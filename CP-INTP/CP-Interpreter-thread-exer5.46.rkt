(module CP-Interpreter-thread-exer5.46
(lib "eopl.ss" "eopl")
(require racket/vector)
(require "../cha1.rkt")
(provide run)
;;;;;;;;;;;;;lang;;;;;;;;;;;;;;;;;;;;;;
  (define the-lexical-spec
    '((whitespace (whitespace) skip)
      (comment ("%" (arbno (not #\newline))) skip)
      (identifier
       (letter (arbno (or letter digit "_" "-" "?")))
       symbol)
      (number (digit (arbno digit)) number)
      (number ("-" digit (arbno digit)) number)
      ))
  
  (define the-grammar
    '((program (expression) num-program)
      (program (Bool-exp) bool-program)
      
      (Bool-exp
       ("zero?" "(" expression ")")
       zero?-exp)
      
      (expression (number) const-exp)
      
      (expression
        ("-" "(" expression "," expression ")")
       diff-exp)

      (expression
       ("*" "(" expression "," expression ")")
       mult-exp)
      
      (expression
       ("if" Bool-exp "then" expression "else" expression)
       if-exp)

      (expression (identifier) var-exp)

      (expression
       ("let" (arbno identifier "=" expression) "in" expression)
       let-exp)
      
       (expression
       ("car" "(" expression ")")
       car-exp)

      (expression
       ("cdr" "(" expression ")")
       cdr-exp)

      (Bool-exp
       ("null?" "(" expression ")")
       null?-exp)

      (expression
       ("list" "(" (separated-list expression ",") ")")
       list-exp)
      
      (expression
       ("proc" "(" (arbno identifier) ")" expression)
       proc-exp)

      (expression
       ("(" expression (arbno expression) ")")
       call-exp)

      (expression
       ("letrec" (arbno identifier "(" (arbno identifier) ")" "=" expression) "in" expression)
      letrec-exp)

      (expression
       ("set" identifier "=" expression)
       assign-exp)

      (expression
       ("begin" (separated-list expression ";") "end")
       begin-exp)

      (expression
       ("spawn" "(" expression ")")
       spawn-exp)

      (expression
       ("mutex" "(" ")")
       mutex-exp)

      (expression
       ("wait" "(" expression ")")
       wait-exp)

      (expression
       ("signal" "(" expression ")")
       signal-exp)

      (expression
       ("yield" "(" ")")
       yield-exp)

      (expression
       ("print" "(" expression ")")
       print-exp)
      ))
  
  ;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;
  (sllgen:make-define-datatypes the-lexical-spec the-grammar)
  (define show-the-datatypes
    (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))
  
  (define scan&parse
    (sllgen:make-string-parser the-lexical-spec the-grammar))
  
  (define just-scan
    (sllgen:make-string-scanner the-lexical-spec the-grammar))
;;;;;;;;;;;;;;;;;;;;;;;;;; store implementation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;helper func;;;;;;;;;;;;
(define exact-integer?
  (lambda (v)
    (and (integer? v) (exact? v))))
(define exact-nonnegative-integer?
  (lambda (v)
    (and (exact-integer? v) (not (negative? v)))))
;;store? : v -> Bool
(define store?
  (lambda (v)
    (vector? v)))
;;empty-store : () -> Sto
(define empty-store
  (lambda ()
    (make-vector 0)))
;;store: A Scheme variable containing the current state of the store. Initially set to a dummy value.
(define the-store 'uninitialized)
;;get-store : () -> Sto
(define get-store
  (lambda ()
    the-store))
;;initialize-store! : () -> Unspecified
(define initialize-store!
  (lambda ()
    (set! the-store (empty-store))))
;;reference? : SchemeVal -> Bool
(define reference?
  (lambda (v)
    (exact-nonnegative-integer? v)))
;;newref : ExpVal -> Ref
(define newref
  (lambda (val)
    (let ((next-ref (vector-length the-store)))
      (set! the-store (vector-append the-store (make-vector 1 val)))
      next-ref)))
;;deref : Ref -> Expval
(define deref
  (lambda (ref)
    (vector-ref the-store ref)))
;;setref! : Ref × ExpVal -> Unspecified
(define setref!
  (lambda (ref val)
    (vector-set! the-store ref val)))
;;;;;;;;;;;;;;;;;;;;;;;;;; environment implementation;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;helper func;;;;;;;;;;;;;
(define member?
  (lambda (s lst)
    (cond
      ((null? lst) #f)
      (else
       (cond
         ((eq? s (car lst)) #t)
         (else (member s (cdr lst))))))))
(define identifier?
  (lambda (s)
   (and (symbol? s) (not (eq? s 'lambda)))))
(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))
(define report-invalid-env
  (lambda (env)
    (eopl:error 'apply-env "Bad environment: ~s" env)))
;;;;;;;;;;;;;;;environment(procedural representation);;;;;;;;;;;;;;;
(define environment?
  (lambda (v)
    (procedure? v)))
(define empty-env
  (lambda ()
    (lambda (search-var)
      (report-no-binding-found search-var))))
(define extend-env
  (lambda (saved-vars saved-vals saved-env)
    (lambda (search-var)
      (let ((i (index search-var saved-vars)))
          (if (not (zero? i))
            (if (vector? saved-vals)
              (pick i (vector-ref saved-vals 0))
              (pick i saved-vals))           
            (apply-env saved-env search-var))))))
(define list-proc
  (lambda (lob-vars lop-body env)
    (cond
      ((and (null? lob-vars) (null? lop-body)) '())
      (else
       (cons (newref (proc-val (procedure (car lob-vars) (car lop-body) env))) (list-proc (cdr lob-vars) (cdr lop-body) env))))))
(define extend-env-rec
  (lambda (lop-name lob-vars lop-body saved-env)
    (let ((vec (make-vector 1)))
      (let ((new-env (extend-env lop-name vec saved-env)))
        (vector-set! vec 0
          (list-proc lob-vars lop-body new-env))
        new-env))))
(define apply-env
  (lambda (env search-var)
    (env search-var)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;mutex implementation;;;;;;;;;;;;;;;;;;;;;;;
(define-datatype mutex mutex?
  (a-mutex
    (ref-to-closed? reference?)
    (ref-to-wait-queue reference?)))
;;new-mutex : () -> Mutex
(define new-mutex
  (lambda ()
    (a-mutex
      (newref #f)
      (newref '()))))
;;wait-for-mutex : Mutex × Thread -> FinalAnswer
(define wait-for-mutex
  (lambda (m th)
    (cases mutex m
      (a-mutex (ref-to-closed? ref-to-wait-queue)
        (cond
          ((deref ref-to-closed?)
           (setref! ref-to-wait-queue
             (enqueue (deref ref-to-wait-queue) th))
           (run-next-thread))
          (else
            (setref! ref-to-closed? #t)
            (th)))))))
(define signal-mutex
  (lambda (m th)
    (cases mutex m
      (a-mutex (ref-to-closed? ref-to-wait-queue)
        (let ((closed? (deref ref-to-closed?))
              (wait-queue (deref ref-to-wait-queue)))
          (when closed?
            (if (empty? wait-queue)
              (setref! ref-to-closed? #f)
              (dequeue wait-queue
                (lambda (first-waiting-th other-waiting-ths)
                  (place-on-ready-queue! first-waiting-th the-max-time-slice)
                  (setref! ref-to-wait-queue other-waiting-ths)))))
          (th))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;scheduler implementation;;;;;;;;;;;;;;;;;;;
;;queue = list
;;empty? : q -> Boolean
(define empty? null?)
;;empty-queue : () -> '()
(define empty-queue
  (lambda ()
    '()))
;;enqueue : queue × val -> new queue
(define enqueue
  (lambda (q val)
    (append q (list val))))
;;dequeue : queue × proc -> expval
(define dequeue
  (lambda (q f)
    (f (car q) (cdr q))))
;;;;;;;;;;;;;;;; the state ;;;;;;;;;;;;;;;;
;; components of the scheduler state:
(define the-ready-queue 'uninitialized)         
(define the-final-answer 'uninitialized)
(define the-max-time-slice 'uninitialized)
(define the-time-remaining 'uninitialized)
;; initialize-scheduler! : Int -> Unspecified
  (define initialize-scheduler!
    (lambda (ticks)
      (set! the-ready-queue (empty-queue))
      (set! the-final-answer 'uninitialized)
      (set! the-max-time-slice ticks)
      (set! the-time-remaining the-max-time-slice)))
;; place-on-ready-queue! : Thread -> Unspecified
  (define place-on-ready-queue!
    (lambda (th ts)
      (set! the-ready-queue
        (enqueue the-ready-queue (list th ts)))))

;; run-next-thread : () -> FinalAnswer   
  (define run-next-thread
    (lambda ()
      (if (empty? the-ready-queue)
        the-final-answer
        (dequeue the-ready-queue
          (lambda (first-ready-thread other-ready-threads)
            (set! the-ready-queue other-ready-threads)            
            (set! the-time-remaining (cadr first-ready-thread))
            (eopl:printf "from run-next-thread, thread ready to run: ~s~%" first-ready-thread)
            ((car first-ready-thread)))))))

;; set-final-answer! : ExpVal -> Unspecified   
  (define set-final-answer!
    (lambda (val)
      (set! the-final-answer val)))

;; time-expired? : () -> Bool
  (define time-expired?
    (lambda ()
      (zero? the-time-remaining)))

;; decrement-timer! : () -> Unspecified  
  (define decrement-timer!
    (lambda ()
      (set! the-time-remaining (- the-time-remaining 1))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;continuation implementation;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;abstract-syntax representation;;;;;;;;;;;;;;;;;;;;
;;Cont = ExpVal -> FinalAnswer
(define-datatype continuation continuation?
  (end-cont)
  (zero-cont
   (saved-cont continuation?))
  (diff1-cont
   (exp2 expression?)
   (saved-env environment?)
   (saved-cont continuation?))
  (diff2-cont
   (val1 expval?)
   (saved-cont continuation?))
  (mult1-cont
   (exp2 expression?)
   (saved-env environment?)
   (saved-cont continuation?))
  (mult2-cont
   (val1 expval?)
   (saved-cont continuation?))
  (first-of-let-cont
   (lovar (list-of identifier?))
   (loexp (list-of expression?))
   (body expression?)
   (saved-env environment?)
   (saved-cont continuation?))
  (rest-of-let-cont
   (lovar (list-of identifier?))
   (loexp (list-of expression?))
   (loval (list-of reference?))
   (body expression?)
   (saved-env environment?)
   (saved-cont continuation?))
  (if-test-cont
   (exp2 expression?)
   (exp3 expression?)
   (saved-env environment?)
   (saved-cont continuation?))
  (car-cont
   (saved-cont continuation?))
  (cdr-cont
   (saved-cont continuation?))
  (null-cont
   (saved-cont continuation?))
  (first-of-list-cont
   (loexp (list-of expression?))
   (saved-env environment?)
   (saved-cont continuation?))
  (rest-of-list-cont
   (loexp (list-of expression?))
   (loval (list-of expval?))
   (saved-env environment?)
   (saved-cont continuation?))
  (rator-cont
   (lorand (list-of expression?))
   (saved-env environment?)
   (saved-cont continuation?))
  (first-of-rand-cont
   (proc proc?)
   (lorand (list-of expression?))
   (saved-env environment?)
   (saved-cont continuation?))
  (rest-of-rand-cont
   (proc proc?)
   (lorand (list-of expression?))
   (loval (list-of reference?))
   (saved-env environment?)
   (saved-cont continuation?))
  (set-rhs-cont
   (var identifier?)
   (saved-env environment?)
   (saved-cont continuation?))
  (rest-of-begin-cont
   (loexp (list-of expression?))
   (saved-env environment?)
   (saved-cont continuation?))
  (spawn-cont
   (saved-cont continuation?))
  (end-main-thread-cont)
  (end-subthread-cont)
  (wait-cont
   (saved-cont continuation?))
  (signal-cont
   (saved-cont continuation?))
  (print-cont
   (saved-cont continuation?)))
(define max-cont-size 0)
(define apply-cont
  (lambda (cont v)
    (if (time-expired?)
      (begin
        (eopl:printf "time-expired~%")
        (place-on-ready-queue!
          (lambda () (apply-cont cont v)) the-max-time-slice)
        (run-next-thread))
      (begin
        (decrement-timer!)
        (eopl:printf "from apply-cont, timer: ~s, cont: ~s, val: ~s~%" the-time-remaining cont v)
        (cases continuation cont
          (end-cont ()
            (begin
              (eopl:printf "End of computation.")
              v))
          (zero-cont (saved-cont)
            (apply-cont saved-cont
              (bool-val
                (zero? (expval->num v)))))
          (diff1-cont (exp2 env saved-cont)
            (value-of/k exp2 env
              (diff2-cont v saved-cont)))
          (diff2-cont (val1 saved-cont)
            (let ((num1 (expval->num val1))
                  (num2 (expval->num v)))
              (apply-cont saved-cont
                (num-val (- num1 num2)))))
          (mult1-cont (exp2 env saved-cont)
            (value-of/k exp2 env
              (mult2-cont v saved-cont)))
          (mult2-cont (val1 saved-cont)
            (let ((num1 (expval->num val1))
                  (num2 (expval->num v)))
              (apply-cont saved-cont
                (num-val (* num1 num2)))))
          (first-of-let-cont (lovar loexp body env saved-cont)
            (let ((loref (list (newref v))))
              (if (null? loexp)
                (value-of/k body (extend-env lovar loref env) saved-cont)
                (value-of/k (car loexp) env
                  (rest-of-let-cont lovar (cdr loexp) loref body env saved-cont)))))
          (rest-of-let-cont (lovar loexp loval body env saved-cont)
            (let ((loref (append loval (list (newref v)))))
              (if (null? loexp)
                (value-of/k body (extend-env lovar loref env) saved-cont)
                (value-of/k (car loexp) env
                  (rest-of-let-cont lovar (cdr loexp) loref body env saved-cont)))))
          (if-test-cont (exp2 exp3 env saved-cont)
            (if (expval->bool v)
              (value-of/k exp2 env saved-cont)
              (value-of/k exp3 env saved-cont)))
          (first-of-list-cont (loexp env saved-cont)
            (if (null? loexp)
              (apply-cont saved-cont (list-val (list v)))
              (value-of/k (car loexp) env
                (rest-of-list-cont (cdr loexp) (list v) env saved-cont))))
          (rest-of-list-cont (loexp loval env saved-cont)
            (if (null? loexp)
              (apply-cont saved-cont (list-val (append loval (list v))))
              (value-of/k (car loexp) env
                (rest-of-list-cont (cdr loexp) (append loval (list v)) env saved-cont))))
          (car-cont (saved-cont)
            (apply-cont saved-cont (car (expval->list v))))
          (cdr-cont (saved-cont)
            (apply-cont saved-cont (list-val (cdr (expval->list v)))))
          (null-cont (saved-cont)
            (apply-cont saved-cont (bool-val (null? (expval->list v)))))
          (rator-cont (lorand env saved-cont)
            (let ((proc (expval->proc v)))
              (if (null? lorand)
                (apply-procedure/k proc '() saved-cont)
                (value-of/k (car lorand) env
                  (first-of-rand-cont proc (cdr lorand) env saved-cont)))))
          (first-of-rand-cont (proc lorand env saved-cont)
            (if (null? lorand)
              (apply-procedure/k proc (list v) saved-cont)
              (value-of/k (car lorand) env
                (rest-of-rand-cont proc (cdr lorand) (list v) env saved-cont))))
          (rest-of-rand-cont (proc lorand loval env saved-cont)
            (if (null? lorand)
              (apply-procedure/k proc (append loval (list v)) saved-cont)
              (value-of/k (car lorand) env
                (rest-of-rand-cont proc (cdr lorand) (append loval (list v)) env saved-cont))))
          (set-rhs-cont (var env saved-cont)
            (let ((ref (apply-env env var)))
              (let ((oldval (deref ref)))
                (begin
                  (setref! ref v)
                  (apply-cont saved-cont oldval)))))
          (rest-of-begin-cont (loexp env saved-cont)
            (if (null? loexp)
              (apply-cont saved-cont v)
              (value-of/k (car loexp) env
                (rest-of-begin-cont (cdr loexp) env saved-cont))))
          (spawn-cont (saved-cont)
            (let ((proc (expval->proc v)))
              (place-on-ready-queue!
                (lambda ()
                  (apply-procedure/k proc
                    (list (num-val 28))
                    (end-subthread-cont)))
                the-max-time-slice)
              (apply-cont saved-cont (num-val 73))));;return to the caller of the spawn
          (end-main-thread-cont ()
            (set-final-answer! v)
            (eopl:printf "from end-main-thread,final answer: ~s~%,current queue: ~s~%" v the-ready-queue)
            (run-next-thread))
          (end-subthread-cont ()
            (eopl:printf "from end-subthread-cont, ignored val:~s~%" v)
            (run-next-thread))
          (wait-cont (saved-cont)
            (wait-for-mutex
              (expval->mutex v)
              (lambda () (apply-cont saved-cont (num-val 52)))));;used to return to the caller to continue the computation
          (signal-cont (saved-cont)
            (signal-mutex
              (expval->mutex v)
              (lambda () (apply-cont saved-cont (num-val 53)))))
          (print-cont (saved-cont)
             (eopl:printf "~s~%" v)
             (apply-cont saved-cont v)))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;run;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;init-env : () -> Env
(define init-env
  (lambda ()
    (extend-env
     (list 'i) (list 0)
     (extend-env
      (list 'v) (list 1)
      (extend-env
       (list 'x) (list 2)
       (empty-env))))))

;;run : String -> ExpVal
(define run
  (lambda (string)
    (value-of-program (scan&parse string))))
;;value-of-program : Program -> ExpVal
(define timeslice 10)
(define value-of-program
  (lambda (pgm)
    (set! max-cont-size 0)
    (initialize-store!)
    (newref 1)
    (newref 5)
    (newref 10)
    (initialize-scheduler! timeslice)
    (cases program pgm
      (num-program (exp)
        (value-of/k exp (init-env) (end-main-thread-cont)))
      (bool-program (exp)
        (value-of-bool-exp/k exp (init-env) (end-main-thread-cont))))))
;;;;;;;;;;;;;;;;;;;;;;value-of-bool-exp/k : Exp × Env × Cont -> ExpVal;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define value-of-bool-exp/k
  (lambda (exp env cont)
    (cases Bool-exp exp
      (zero?-exp (exp)
        (value-of/k exp env (zero-cont cont)))
      (null?-exp (exp)
        (value-of/k exp env
          (null-cont cont))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;value-of implementation;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;helper func;;;;;;;;;;;;;;;
;; applicative-order Y combinator
(define  Y
  (lambda (le)
    ((lambda (f) (f f))
     (lambda (f)
       (le (lambda (x y z) ((f f) x y z)))))))
;;curry2 : Func -> Func
(define curry2
  (lambda (f)
    (lambda (arg1)
      (lambda (arg2)
        (f arg2 arg1)))))
;;;;;;;;;;;;;;;;;value-of/k : Exp × Env × Cont -> ExpVal;;;;;;;;;;;;;;;;;
(define value-of/k
  (lambda (exp env cont)
    (cases expression exp
      (const-exp (num) (apply-cont cont (num-val num)))
      (var-exp (var) (apply-cont cont (deref (apply-env env var))))
      (assign-exp (var exp)
        (value-of/k exp env
          (set-rhs-cont var env cont)))
      (begin-exp (loexp)
        (value-of/k (car loexp) env
          (rest-of-begin-cont (cdr loexp) env cont)))
      (diff-exp (exp1 exp2)
        (value-of/k exp1 env
          (diff1-cont exp2 env cont)))
      (mult-exp (exp1 exp2)
        (value-of/k exp1 env
          (mult1-cont exp2 env cont)))
      (if-exp (exp1 exp2 exp3)
        (value-of-bool-exp/k exp1 env
          (if-test-cont exp2 exp3 env cont)))
      (let-exp (lovar loexp body)
        (if (null? loexp)
          (value-of/k body env cont)
          (value-of/k (car loexp) env
            (first-of-let-cont lovar (cdr loexp) body env cont))))
      (car-exp (exp)
        (value-of/k exp env
          (car-cont cont)))
      (cdr-exp (exp)
        (value-of/k exp env
          (cdr-cont cont)))
      (list-exp (loexp)
         (if (null? loexp)
          (apply-cont cont (list-val '()))
          (value-of/k (car loexp) env
            (first-of-list-cont (cdr loexp) env cont))))
      ;;;;;lexical scoping;;;;;
      (proc-exp (lovar body)
        (apply-cont cont (proc-val (procedure lovar body env))))
      (call-exp (rator lorand)
        (value-of/k rator env
          (rator-cont lorand env cont)))
      (letrec-exp (lop-name lob-vars lop-body letrec-body)
        (value-of/k letrec-body (extend-env-rec lop-name lob-vars lop-body env) cont))
      (spawn-exp (exp)
        (value-of/k exp env
          (spawn-cont cont)))
      (mutex-exp ()
        (apply-cont cont (mutex-val (new-mutex))))
      (wait-exp (exp)
        (value-of/k exp env
          (wait-cont cont)))
      (signal-exp (exp)
        (value-of/k exp env
          (signal-cont cont)))
      (yield-exp ()
        (begin
          (place-on-ready-queue!
            (lambda () (apply-cont cont (num-val 99)))
            the-time-remaining)
          (run-next-thread)))
      (print-exp (exp)
        (value-of/k exp env
          (print-cont cont))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;datatype implementation;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
;;;;;;;;;;;;;;;;;;;;;;;procedure datatype;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;abstract-syntax representation;;;;;;;;;;;;;
(define-datatype proc proc?
  (procedure
    (lovar (list-of identifier?))
    (body expression?)
    (saved-env environment?)))
(define apply-procedure/k
  (lambda (proc1 loval cont)
    (eopl:printf "from apply-procedure/k, cont:~s~%" cont)
    (cases proc proc1
      (procedure (lovar body saved-env)
        (value-of/k body (extend-env lovar (map newref loval) saved-env) cont)))))
;;(define apply-procedure/k
;;  (lambda (proc1 loval cont)             
;;    (begin
;;      (eopl:printf
;;        "~%entering apply-procedure:~%proc1=~s~%loval=~s~%cont=~s~%cont-size=~s~%" 
;;          proc1 loval cont (continuation-size 0 cont))
;;      (cases proc proc1
;;        (procedure (lovar body saved-env)
;;          (value-of/k body (extend-env lovar (map newref loval) saved-env) cont))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;expval datatype;;;;;;;;;;;;;;;;;;;;;;;
(define-datatype expval expval?
  (num-val
    (num number?))
  (bool-val
    (bool boolean?))
  (list-val
    (list list?))
  (proc-val
    (proc proc?))
  (mutex-val
    (mutex mutex?)))
;;expval->mutex : Expval -> mutex
(define expval->mutex
  (lambda (val)
    (cases expval val
      (mutex-val (mutex) mutex)
      (else (report-expval-extractor-error 'mutex val)))))
;;expval->proc : Expval-> proc
(define expval->proc
  (lambda (val)
    (cases expval val
      (proc-val (proc) proc)
      (else (report-expval-extractor-error 'proc val)))))
;;expval->num : ExpVal -> Int
(define expval->num
  (lambda (val)
    (cases expval val
      (num-val (num) num)
      (else (report-expval-extractor-error 'num val)))))
;;expval->bool : ExpVal -> Bool
(define expval->bool
  (lambda (val)
    (cases expval val
      (bool-val (bool) bool)
      (else (report-expval-extractor-error 'bool val)))))
;;expval->list : ExpVal -> List
(define expval->list
  (lambda (val)
    (cases expval val
      (list-val (list) list)
      (else (report-expval-extractor-error 'list val)))))
;;expval->any : ExpVal -> List|Int|Bool|Proc
(define expval->any
  (lambda (val)
    (cases expval val
      (list-val (list) list)
      (num-val (num) num)
      (bool-val (bool) bool)
      (proc-val (proc) proc)
      (mutex-val (mutex) mutex)
      (else (report-expval-extractor-error 'any val)))))
(define report-expval-extractor-error
  (lambda (type val)
    (eopl:error 'expval->any "expect ~s, but reveived ~s" type val)))


;;;;;;;;;;;;;;;;;;;;;;;;;exer3.26;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; unique : lst -> lst of unique elements
(define unique
  (lambda (lst)
    (cond
      ((null? lst) '())
      (else
       (cond
         ((member? (car lst) (cdr lst)) (unique (cdr lst)))
         (else (cons (car lst) (unique (cdr lst)))))))))
;; removelist : Lst × Lst -> Lst
(define removelist
  (lambda (lst1 lst2)
    (cond
      ((null? lst1) lst2)
      (else
       (removelist (cdr lst1) (remove (car lst1) lst2))))))
;; var-in-exp : exp -> lst of var
)

;;add
;;"let add = proc (x) proc (y) +(x,y) in ((add 1) 3)"

;;(run "letrec fact(n) = if zero? (n) then 1 else *(n,(fact -(n,1))) in (fact 4)")
;;(run "letrec fact-iter (n) = (fact-iter-acc n 1) fact-iter-acc (n a) = if zero?(n) then a else (fact-iter-acc -(n,1) *(n,a)) in (fact-iter 4)")
;;(run "let minus = proc (x) proc (y) print(-(x,y)) in begin spawn(proc (d) ((minus 1) 3)); print(1) end")
;;exercise5.51(run "let buffer = 0 mut = mutex()
;;in let producer = proc (n)
;;letrec
;;waitloop(k) = if zero?(k)
;;then begin
;;set buffer = n;
;;signal(mut)
;;end
;;else begin
;;print(-(k,-200));
;;(waitloop -(k,1))
;;end
;;in (waitloop 5)
;;in let consumer = proc (d)
;;begin
;;wait(mut);
;;buffer
;;end
;;in begin
;;wait(mut);
;;spawn(proc (d) (producer 44));
;;print(300);
;;(consumer 86)
;;end")
