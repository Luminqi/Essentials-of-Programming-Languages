(module CP-Interpreter-data-structure
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
       ("begin" expression (arbno ";" expression) "end")
       begin-exp)
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
   (loval (list-of expval?))
   (body expression?)
   (saved-env environment?)
   (saved-cont continuation?))
  (if-test-cont
   (exp2 expression?)
   (exp3 expression?)
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
   (loval (list-of expval?))
   (saved-env environment?)
   (saved-cont continuation?))
  (set-rhs-cont
   (var identifier?)
   (saved-env environment?)
   (saved-cont continuation?))
  (rest-of-begin-cont
   (loexp (list-of expression?))
   (saved-env environment?)
   (saved-cont continuation?)))
(define max-cont-size 0)
(define apply-cont
  (lambda (cont v)
    (begin
      (let ((size (continuation-size 0 cont)))
        (when (> size max-cont-size)
          (set! max-cont-size size)))
    (cases continuation cont
      (end-cont ()
        (begin
          (eopl:printf "End of computation.~%max-cont-size: ~s~%" max-cont-size)
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
            (rest-of-begin-cont (cdr loexp) env saved-cont))))))))
(define continuation-size
  (lambda (saved-size cont)
    (cases continuation cont
      (end-cont ()
        (+ saved-size 1))
      (zero-cont (saved-cont)
        (continuation-size (+ saved-size 1) saved-cont))
      (diff1-cont (exp2 env saved-cont)
        (continuation-size (+ saved-size 1) saved-cont))
      (diff2-cont (val1 saved-cont)
        (continuation-size (+ saved-size 1) saved-cont))
      (mult1-cont (exp2 env saved-cont)
        (continuation-size (+ saved-size 1) saved-cont))
      (mult2-cont (val1 saved-cont)
        (continuation-size (+ saved-size 1) saved-cont))
      (first-of-let-cont (lovar loexp body env saved-cont)
        (continuation-size (+ saved-size 1) saved-cont))
      (rest-of-let-cont (lovar loexp loval body env saved-cont)
        (continuation-size (+ saved-size 1) saved-cont))
      (if-test-cont (exp2 exp3 env saved-cont)
        (continuation-size (+ saved-size 1) saved-cont))
      (rator-cont (lorand env saved-cont)
        (continuation-size (+ saved-size 1) saved-cont))
      (first-of-rand-cont (proc lorand env saved-cont)
        (continuation-size (+ saved-size 1) saved-cont))
      (rest-of-rand-cont (proc lorand loval env saved-cont)
        (continuation-size (+ saved-size 1) saved-cont))
      (set-rhs-cont (var env saved-cont)
        (continuation-size (+ saved-size 1) saved-cont))
      (rest-of-begin-cont (loexp env saved-cont)
        (continuation-size (+ saved-size 1) saved-cont)))))
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
(define value-of-program
  (lambda (pgm)
    (set! max-cont-size 0)
    (initialize-store!)
    (newref 1)
    (newref 5)
    (newref 10)
    (cases program pgm
      (num-program (exp)
        (value-of/k exp (init-env) (end-cont)))
      (bool-program (exp)
        (value-of-bool-exp/k exp (init-env) (end-cont))))))
;;;;;;;;;;;;;;;;;;;;;;value-of-bool-exp/k : Exp × Env × Cont -> ExpVal;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define value-of-bool-exp/k
  (lambda (exp env cont)
    (cases Bool-exp exp
      (zero?-exp (exp)
        (value-of/k exp env (zero-cont cont))))))
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
      (begin-exp (exp loexp)
        (if (null? loexp)
          (value-of/k exp env cont)
          (begin
            (value-of/k exp env cont)
            (value-of/k (car loexp) env
              (rest-of-begin-cont (cdr loexp) env cont)))))
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
      ;;;;;lexical scoping;;;;;
      (proc-exp (lovar body)
        (apply-cont cont (proc-val (procedure lovar body env))))
      (call-exp (rator lorand)
        (value-of/k rator env
          (rator-cont lorand env cont)))
      (letrec-exp (lop-name lob-vars lop-body letrec-body)
        (value-of/k letrec-body (extend-env-rec lop-name lob-vars lop-body env) cont)))))
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
    (proc proc?)))
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
      (else (report-expval-extractor-error 'any val)))))
(define report-expval-extractor-error
  (lambda (type val)
    (eopl:error 'expval->num "expect ~s, but reveived ~s" type val)))


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

