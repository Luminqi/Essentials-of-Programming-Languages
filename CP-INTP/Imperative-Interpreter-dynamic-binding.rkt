(module Imperative-Interpreter-dynamic-binding
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
;;;;;;;;;;;;;;environment(abstract-syntax representation);;;;;;;;;;;;;;;;;;;;
(define-datatype environment environment?
  (empty-env)
  (extend-env
    (vars (list-of identifier?))
    (vals (list-of number?))
    (env environment?))
  (extend-env-rec
    (lop-name (list-of identifier?))
    (lob-vars (list-of (list-of identifier?)))
    (lobody (list-of expression?))
    (env environment?)))
(define apply-env
  (lambda (env search-var)
    (cases environment env
      (empty-env ()
        (report-no-binding-found search-var))
      (extend-env (saved-vars saved-vals saved-env)
        (let ((i (index search-var saved-vars)))
          (if (not (zero? i))
            (pick i saved-vals)
            (apply-env saved-env search-var))))
      (extend-env-rec (lop-name lob-vars lop-body saved-env)
        (let ((i (index search-var lop-name)))
          (if (not (zero? i))
            (newref (proc-val (procedure (pick i lob-vars) (pick i lop-body) env)))
            (apply-env saved-env search-var)))))))

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
   (loval (list-of number?))
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
  (lambda ()
    (begin
      ;;(eopl:printf "~%entering apply-cont:~%cont=~s~%val=~s~%" cont* val*)
      (eopl:printf "~%entering apply-cont:~%cont=~s~%env=~s~%" cont* env*)
      (let ((size (continuation-size 0 cont*)))
        (when (> size max-cont-size)
          (set! max-cont-size size)))
    (cases continuation cont*
      (end-cont ()
        (begin
          (eopl:printf "End of computation.~%max-cont-size: ~s~%" max-cont-size)
          val*))
      (zero-cont (saved-cont)
        (set! cont* saved-cont)
        (set! val* (bool-val (zero? (expval->num val*))))
        (apply-cont))
      (diff1-cont (exp2 env saved-cont)
        (set! cont* (diff2-cont val* saved-cont))
        (set! exp* exp2)
        (set! env* env)
        (value-of/k))
      (diff2-cont (val1 saved-cont)
        (let ((num1 (expval->num val1))
              (num2 (expval->num val*)))
          (set! cont* saved-cont)
          (set! val* (num-val (- num1 num2)))
          (apply-cont)))
      (mult1-cont (exp2 env saved-cont)
        (set! cont* (mult2-cont val* saved-cont))
        (set! exp* exp2)
        (set! env* env)
        (value-of/k))
      (mult2-cont (val1 saved-cont)
        (let ((num1 (expval->num val1))
              (num2 (expval->num val*)))
          (set! cont* saved-cont)
          (set! val* (num-val (* num1 num2)))
          (apply-cont)))
      (first-of-let-cont (lovar loexp body env saved-cont)
        (let ((loref (list (newref val*))))
          (if (null? loexp)
            (begin
              (set! cont* saved-cont)
              (set! exp* body)
              (set! env* (extend-env lovar loref env))
              (value-of/k))
            (begin
              (set! cont* (rest-of-let-cont lovar (cdr loexp) loref body env saved-cont))
              (set! exp* (car loexp))
              (set! env* env)
              (value-of/k)))))
      (rest-of-let-cont (lovar loexp loval body env saved-cont)
        (let ((loref (append loval (list (newref val*)))))
          (if (null? loexp)
            (begin
              (set! cont* saved-cont)
              (set! exp* body)
              (set! env* (extend-env lovar loref env))
              (value-of/k))
            (begin
              (set! cont* (rest-of-let-cont lovar (cdr loexp) loref body env saved-cont))
              (set! exp* (car loexp))
              (set! env* env)
              (value-of/k)))))
      (if-test-cont (exp2 exp3 env saved-cont)
        (set! cont* saved-cont)
        (if (expval->bool val*)            
          (set! exp* exp2)
          (set! exp* exp3))
        (set! env* env)
        (value-of/k))
      (rator-cont (lorand env saved-cont)
        (let ((proc (expval->proc val*)))
          (if (null? lorand)
            (begin
              (set! cont* saved-cont)
              (set! proc* proc)
              (set! val* '())
              (set! env* env)
              (set! pc apply-procedure/k))
            (begin
              (set! cont* (first-of-rand-cont proc (cdr lorand) env saved-cont))
              (set! exp* (car lorand))
              (set! env* env)
              (value-of/k)))))
      (first-of-rand-cont (proc lorand env saved-cont)
        (if (null? lorand)
          (begin
            (set! cont* saved-cont)
            (set! proc* proc)
            (set! val* (list val*))
            (set! env* env)
            (set! pc apply-procedure/k))
          (begin
            (set! cont* (rest-of-rand-cont proc (cdr lorand) (list val*) env saved-cont))
            (set! exp* (car lorand))
            (set! env* env)
            (value-of/k))))
      (rest-of-rand-cont (proc lorand loval env saved-cont)
        (if (null? lorand)
          (begin
            (set! cont* saved-cont)
            (set! proc* proc)
            (set! val* (append loval (list val*)))
            (set! env* env)
            (set! pc apply-procedure/k))
         (begin
            (set! cont* (rest-of-rand-cont proc (cdr lorand) (append loval (list val*)) env saved-cont))
            (set! exp* (car lorand))
            (set! env* env)
            (value-of/k))))
      (set-rhs-cont (var env saved-cont)
        (let ((ref (apply-env env var)))
          (let ((oldval (deref ref)))
            (begin
              (setref! ref val*)
              (set! cont* saved-cont)
              (set! val* oldval)
              (apply-cont)))))
      (rest-of-begin-cont (loexp env saved-cont)
        (if (null? loexp)
          (begin
            (set! cont* saved-cont)
            (apply-cont))
          (begin
            (set! cont* (rest-of-begin-cont (cdr loexp) env saved-cont))
            (set! exp* (car loexp))
            (set! env* env)
            (value-of/k))))))))
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
;;global registers
(define exp* 'uninitialized)
(define env* 'uninitialized)
(define cont* 'uninitialized)
(define val* 'uninitialized)
(define proc* 'uninitialized)
(define pc 'uninitialized)
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
        (set! cont* (end-cont))
        (set! exp* exp)
        (set! env* (init-env))
        (trampoline (value-of/k)))
      (bool-program (exp)
        (set! cont* (end-cont))
        (set! exp* exp)
        (set! env* (init-env))
        (trampoline (value-of-bool-exp/k))))))
;;bounce = expval ∪ (the result of set!, of course nothing)
;;trampoline : bounce -> expval
(define trampoline
  (lambda (bounce)
    (if (expval? bounce)
      bounce
      (trampoline (pc)))))
;;;;;;;;;;;;;;;;;;;;;;value-of-bool-exp/k : Exp × Env × Cont -> ExpVal;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define value-of-bool-exp/k
  (lambda ()
    (cases Bool-exp exp*
      (zero?-exp (exp)
        (set! cont* (zero-cont cont*))
        (set! exp* exp)
        (value-of/k)))))
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
  (lambda ()
    ;;(eopl:printf "~%entering value-of/k:~%exp=~s~%env=~s~%cont=~s~%" exp* env* cont*)
    (cases expression exp*
      (const-exp (num)
        (set! val* (num-val num))
        (apply-cont))
      (var-exp (var)
        (set! val* (deref (apply-env env* var)))
        (apply-cont))
      (assign-exp (var exp)
        (set! cont* (set-rhs-cont var env* cont*))
        (set! exp* exp)
        (value-of/k))
      (begin-exp (exp loexp)
        (if (null? loexp)
          (begin
            (set! exp* exp)
            (value-of/k))
          (begin
            (set! exp* exp)
            (value-of/k)
            (set! cont* (rest-of-begin-cont (cdr loexp) env* cont*))
            (set! exp* (car loexp))
            (value-of/k))))
      (diff-exp (exp1 exp2)
        (set! cont* (diff1-cont exp2 env* cont*))
        (set! exp* exp1)
        (value-of/k))
      (mult-exp (exp1 exp2)
        (set! cont* (mult1-cont exp2 env* cont*))
        (set! exp* exp1)
        (value-of/k))
      (if-exp (exp1 exp2 exp3)
        (set! cont* (if-test-cont exp2 exp3 env* cont*))
        (set! exp* exp1)
        (value-of-bool-exp/k))
      (let-exp (lovar loexp body)
        (set! cont* (first-of-let-cont lovar (cdr loexp) body env* cont*))
        (set! exp* (car loexp))
        (value-of/k))
      ;;;;;lexical scoping;;;;;
      ;;(proc-exp (lovar body)
      ;;  (set! val* (proc-val (procedure lovar body env*)))
      ;;  (apply-cont))
      ;;(call-exp (rator lorand)
      ;;  (set! cont* (rator-cont lorand env* cont*))
      ;;  (set! exp* rator)
      ;;  (value-of/k))
      ;;;;;dynamic scoping;;;;;
      (proc-exp (lovar body)
        (set! val* (proc-val (procedure lovar body)))
        (apply-cont))
      (call-exp (rator lorand)
        (set! cont* (rator-cont lorand env* cont*))
        (set! exp* rator)
        (value-of/k))
      (letrec-exp (lop-name lob-vars lop-body letrec-body)
        (set! exp* letrec-body)
        (set! env* (extend-env-rec lop-name lob-vars lop-body env*))
        (value-of/k)))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;datatype implementation;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
;;;;;;;;;;;;;;;;;;;;;;;procedure datatype;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;abstract-syntax representation(dynamic binding);;;;;;;;;;;;;;;;;;;;;;;;;;
(define-datatype proc proc?
  (procedure
    (lovar (list-of identifier?))
    (body expression?)))
(define apply-procedure/k
  (lambda ()
    ;;(eopl:printf  "~%entering apply-procedure:~%proc=~s~%loval=~s~%env=~s~%cont=~s~%" proc* val* env* cont*)
    (cases proc proc*
      (procedure (lovar body)
        (set! exp* body)
        (set! env* (extend-env lovar (map newref val*) env*))
        (value-of/k)))))
;;;;;;;;abstract-syntax representation;;;;;;;;;;;;;
;;(define-datatype proc proc?
;;  (procedure
;;    (lovar (list-of identifier?))
;;    (body expression?)
;;    (saved-env environment?)))
;;(define apply-procedure/k
;;  (lambda ()
;;    (eopl:printf  "~%entering apply-procedure:~%proc=~s~%loval=~s~%cont=~s~%" proc* val* cont*)
;;    (cases proc proc*
;;      (procedure (lovar body saved-env)
;;        (set! exp* body)
;;        (set! env* (extend-env lovar (map newref val*) saved-env))
;;        (value-of/k)))))
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


