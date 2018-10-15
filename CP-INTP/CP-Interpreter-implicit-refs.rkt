(module CP-Interpreter-implicit-refs
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
      
      (Bool-exp
       ("equal?" "(" expression "," expression ")")
       equal?-exp)

      (Bool-exp
       ("greater?" "(" expression "," expression ")")
       greater?-exp)

      (Bool-exp
       ("less?" "(" expression "," expression ")")
       less?-exp)
      
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
       ("emptylist")
       emptylist-exp)

      (expression
       ("cons" "(" expression "," expression ")")
       cons-exp)

      (expression
       ("car" "(" expression ")")
       car-exp)

      (expression
       ("cdr" "(" expression ")")
       cdr-exp)

      (expression
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
;;;;;;;;;;;;;;environment(abstract-syntax representation);;;;;;;;;;;;;;;;;;;;
;;(define-datatype environment environment?
;;  (empty-env)
;;  (extend-env
;;    (vars (list-of identifier?))
;;    (vals (list-of expval?))
;;    (env environment?))
;;  (extend-env-rec
;;    (lop-name (list-of identifier?))
;;    (lob-vars (list-of (list-of identifier?)))
;;    (lobody (list-of expression?))
;;    (env environment?)))
;;(define apply-env
;;  (lambda (env search-var)
;;    (cases environment env
;;      (empty-env ()
;;        (report-no-binding-found search-var))
;;      (extend-env (saved-vars saved-vals saved-env)
;;        (let ((i (index search-var saved-vars)))
;;          (if (not (zero? i))
;;            (pick i saved-vals)
;;            (apply-env saved-env search-var))))
;;      (extend-env-rec (lop-name lob-vars lop-body saved-env)
;;        (let ((i (index search-var lop-name)))
;;          (if (not (zero? i))
;;            (proc-val (procedure (pick i lob-vars) (pick i lop-body) env))
;;            (apply-env saved-env search-var)))))))
;;;;;;;;;;;;;;;;;;;;;;environment(data structure representation);;;;;;;;;;;;;;;;;;;;;;;;;;;
;;(define environment?
;;  (lambda (env)
;;    ((list-of list?) env)))
;;(define empty-env
;;  (lambda ()
;;    '()))
;;(define extend-env
;;  (lambda (vars vals env)
;;    (cond
;;      ((and (atom? vars) (atom? vals)) (list (list (cons vars '()) (cons vals '())) env))
;;      (else (list (list vars vals) env)))))
;;(define apply-env
;;  (lambda (env ;;search-var)
;;    (cond
;;      ((null? env)
;;       (report-no-binding-found search-var))
;;      (else
;;       (let ((saved-vars (caar env))
;;             (saved-vals (cadar env))
;;             (saved-env (cadr env)))
;;           (let ((i (index search-var saved-vars)))
;;             (if (not (eq? i 0))
;;               (pick i saved-vals)
;;               (apply-env saved-env search-var))))))))
;;(define empty-env?
;;  (lambda (env)
;;    (null? env)))
;;(define has-binding*?
;;  (lambda (env s)
;;    (cond
;;      ((null? env) #f)
;;      (else
;;       (let ((saved-vars (caar env))
;;             (saved-vals (cadar env))
;;             (saved-env (cadr env)))
;;         (cond
;;           ((member? s saved-vars) #t)
;;           (else (has-binding*? saved-env s))))))))
  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;continuation implementation;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;procedural representation;;;;;;;;;;;;;;;;;;;;
;;Cont = ExpVal -> FinalAnswer
;;end-cont : () -> Cont
(define end-cont
  (lambda ()
    (lambda (val)
      (begin
        (eopl:printf "End of computation.~%")
        val))))
;;zero-cont : Cont -> Cont
(define zero-cont
  (lambda (cont)
    (lambda (val)
      (apply-cont cont
        (bool-val
          (zero? (expval->num val)))))))
;;equal-exp1-cont : Exp × Env × Cont -> Cont
(define equal-exp1-cont
  (lambda (exp2 env cont)
    (lambda (val1)
      (value-of/k exp2 env
        (equal-exp2-cont val1 cont)))))
;;equal-exp2-cont : Expval × Cont -> Cont
(define equal-exp2-cont
  (lambda (val1 cont)
    (lambda (val2)
      (let ((num1 (expval->num val1))
            (num2 (expval->num val2)))
        (apply-cont cont
          (bool-val (eq? num1 num2)))))))
;;greater-exp1-cont : Exp × Env × Cont -> Cont
(define greater-exp1-cont
  (lambda (exp2 env cont)
    (lambda (val1)
      (value-of/k exp2 env
        (greater-exp2-cont val1 cont)))))
;;greater-exp2-cont : Expval × Cont -> Cont
(define greater-exp2-cont
  (lambda (val1 cont)
    (lambda (val2)
      (let ((num1 (expval->num val1))
            (num2 (expval->num val2)))
        (apply-cont cont
          (bool-val (> num1 num2)))))))
;;less-exp1-cont : Exp × Env × Cont -> Cont
(define less-exp1-cont
  (lambda (exp2 env cont)
    (lambda (val1)
      (value-of/k exp2 env
        (less-exp2-cont val1 cont)))))
;;less-exp2-cont : Expval × Cont -> Cont
(define less-exp2-cont
  (lambda (val1 cont)
    (lambda (val2)
      (let ((num1 (expval->num val1))
            (num2 (expval->num val2)))
        (apply-cont cont
          (bool-val (< num1 num2)))))))
;;let-exp-cont : Var × Exp × Env × Cont -> Cont
(define let-exp-cont
  (lambda (var body env cont)
    (lambda (val)
      (value-of/k body (extend-env var val env) cont))))
;;if-test-cont : Exp × Exp × Env × Cont -> Cont
(define if-test-cont
  (lambda (exp2 exp3 env cont)
    (lambda (val)
      (if (expval->bool val)
        (value-of/k exp2 env cont)
        (value-of/k exp3 env cont)))))
;;diff1-cont :  Exp × Env × Cont -> Cont
(define diff1-cont
  (lambda (exp2 env cont)
    (lambda (val1)
      (value-of/k exp2 env
        (diff2-cont val1 cont)))))
;;diff2-cont : Expval × Cont -> Cont
(define diff2-cont
  (lambda (val1 cont)
    (lambda (val2)
      (let ((num1 (expval->num val1))
            (num2 (expval->num val2)))
        (apply-cont cont
          (num-val (- num1 num2)))))))
;;mult1-cont :  Exp × Env × Cont -> Cont
(define mult1-cont
  (lambda (exp2 env cont)
    (lambda (val1)
      (value-of/k exp2 env
        (mult2-cont val1 cont)))))
;;mult2-cont : Expval × Cont -> Cont
(define mult2-cont
  (lambda (val1 cont)
    (lambda (val2)
      (let ((num1 (expval->num val1))
            (num2 (expval->num val2)))
        (apply-cont cont
          (num-val (* num1 num2)))))))
;;first-of-let-cont : loVar × loExp × Exp × Env × Cont -> Cont
(define first-of-let-cont
  (lambda (lovar loexp body env cont)
    (lambda (val)
      (let ((loref (list (newref val))))
        (if (null? loexp)
          (value-of/k body (extend-env lovar loref env) cont)
          (value-of/k (car loexp) env
            (rest-of-let-cont lovar (cdr loexp) loref body env cont)))))))
;;rest-of-let-cont : loVar × loExp × loExpval × Exp × Env × Cont -> Cont
(define rest-of-let-cont
  (lambda (lovar loexp loval body env cont)
    (lambda (val)
      (let ((loref (append loval (list (newref val)))))
        (if (null? loexp)
          (value-of/k body (extend-env lovar loref env) cont)
          (value-of/k (car loexp) env
            (rest-of-let-cont lovar (cdr loexp) loref body env cont)))))))
;;cons-exp1-cont : Exp × Env × Cont -> Cont
(define cons-exp1-cont
  (lambda (exp2 env cont)
    (lambda (val1)
      (value-of/k exp2 env
        (cons-exp2-cont val1 cont)))))
;;cons-exp2-cont : Expval × Cont -> Cont
(define cons-exp2-cont
  (lambda (val1 cont)
    (lambda (val2)
      (let ((v1 (expval->any val1))
            (v2 (expval->list val2)))
        (apply-cont cont
          (list-val (cons v1 v2)))))))
;;car-exp-cont : Cont -> Cont
(define car-exp-cont
  (lambda (cont)
    (lambda (val)
      (let ((v (car (expval->list val))))
        (cond
          ((number? v) (apply-cont cont (num-val v)))
          ((boolean? v) (apply-cont cont (bool-val v)))
          ((list? v) (apply-cont cont (list-val v)))
          (else (apply-cont cont (proc-val v))))))))
;;cdr-exp-cont : Cont -> Cont
(define cdr-exp-cont
  (lambda (cont)
    (lambda (val)
      (let ((v (cdr (expval->list val))))
        (apply-cont cont
          (list-val v))))))
;;null-exp-cont : Cont -> Cont
(define null-exp-cont
  (lambda (cont)
    (lambda (val)
      (let ((v (expval->list val)))
        (apply-cont cont
          (bool-val (null? v)))))))
;;first-of-list-cont : loExp × Env × Cont -> Cont
(define first-of-list-cont
  (lambda (loexp env cont)
    (lambda (val)
      (if (null? loexp)
        (apply-cont cont (list-val (list val)))
        (value-of/k (car loexp) env
          (rest-of-list-cont (cdr loexp) (list val) env cont))))))
;;rest-of-list-cont: loExp × loVal × Env × Cont -> Cont
(define rest-of-list-cont
  (lambda (loexp loval env cont)
    (lambda (val)
      (if (null? loexp)
        (apply-cont cont (list-val (append loval (list val))))
        (value-of/k (car loexp) env
          (rest-of-list-cont (cdr loexp) (append loval (list val)) env cont))))))
;;rator-cont : loRand × Env × Cont -> Cont
(define rator-cont
  (lambda (lorand env cont)
    (lambda (val)
      (let ((proc (expval->proc val)))
        (if (null? lorand)
          (apply-procedure/k proc '() cont)
          (value-of/k (car lorand) env
            (first-of-rand-cont proc (cdr lorand) env cont)))))))
;;first-of-rand-cont : Proc × loExp × Env × Cont
(define first-of-rand-cont
  (lambda (proc lorand env cont)
    (lambda (val)
      (if (null? lorand)
        (apply-procedure/k proc (list val) cont)
        (value-of/k (car lorand) env
          (rest-of-rand-cont proc (cdr lorand) (list val) env cont))))))
;;rest-of-rand-cont : Proc × loExp × loExpval × Env × Cont -> Cont
(define rest-of-rand-cont
  (lambda (proc lorand loval env cont)
    (lambda (val)
      (if (null? lorand)
        (apply-procedure/k proc (append loval (list val)) cont)
        (value-of/k (car lorand) env
          (rest-of-rand-cont proc (cdr lorand) (append loval (list val)) env cont))))))
;;set-rhs-cont : Var × Env × Cont -> Cont
(define set-rhs-cont
  (lambda (var env cont)
    (lambda (val)
      (let ((ref (apply-env env var)))
          (let ((oldval (deref ref)))
            (begin
              (setref! ref val)
              (apply-cont cont oldval)))))))
;;rest-of-begin-cont : loExp × Env × Cont -> Cont
(define rest-of-begin-cont
  (lambda (loexp env cont)
    (lambda (val)
      (if (null? loexp)
        (apply-cont cont val)
        (value-of/k (car loexp) env
          (rest-of-begin-cont (cdr loexp) env cont))))))
;;apply-cont : Cont × ExpVal -> FinalAnswer
(define apply-cont
  (lambda (cont v)
    (cont v)))

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
        (value-of/k exp env (zero-cont cont)))
      (equal?-exp (exp1 exp2)
        (value-of/k exp1 env
          (equal-exp1-cont exp2 env cont)))
      (greater?-exp (exp1 exp2)
        (value-of/k exp1 env
          (greater-exp1-cont exp2 env cont)))
      (less?-exp (exp1 exp2)
        (value-of/k exp1 env
          (less-exp1-cont exp2 env cont))))))
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
;;      (let*-exp (lovar loexp body)
;;        (let ((loval (value* lovar loexp env)))
;;          (value-of body
;;            (extend-env lovar loval env))))
;;      (minus-exp (exp) (num-val (- 0 (expval->num (value-of exp env)))))
;;      (add-exp (loexp)
;;        (num-val (addition loexp env)))
;;      (mul-exp (loexp)
;;        (num-val (multiply loexp env)))
;;      (intq-exp (num exp) (num-val (* num (expval->num (value-of exp env)))))
      (emptylist-exp () (apply-cont cont (list-val '())))
      (cons-exp (exp1 exp2)
        (value-of/k exp1 env
          (cons-exp1-cont exp2 env cont)))
      (car-exp (exp)
        (value-of/k exp env (car-exp-cont cont)))
      (cdr-exp (exp)
        (value-of/k exp env (cdr-exp-cont cont)))
      (null?-exp (exp)
        (value-of/k exp env (null-exp-cont cont)))
      (list-exp (loexp)
        (if (null? loexp)
          (apply-cont cont (list-val '()))
          (value-of/k (car loexp) env
            (first-of-list-cont (cdr loexp) env cont))))
;;      (cond-exp (loexp1 loexp2)
;;        (value-of (pick (findIndex loexp1 env) loexp2) env))
;;      (unpack-exp (lovar lst-exp exp)
;;        (let ((lst (expval->list (value-of lst-exp env))))
;;          (if (not (eq? (length lovar) (length lst)))
;;            (report-unpack-args-mismatch)
;;            (value-of exp (extend-env lovar (map num-val lst) env)))))
      ;;;;;lexical scoping;;;;;
      (proc-exp (lovar body)
        (apply-cont cont (proc-val (procedure lovar body env))))
      (call-exp (rator lorand)
        (value-of/k rator env
          (rator-cont lorand env cont)))
      ;;;;;dynamic scoping;;;;;
      ;;(proc-exp (lovar body)
      ;;  (proc-val (procedure lovar body)))
      ;;(call-exp (rator lorand)
      ;;  (let ((proc (expval->proc (value-of rator env)))
      ;;        (loarg (map ((curry2 value-of) env) lorand)))
      ;;    (apply-procedure proc loarg env)))
      (letrec-exp (lop-name lob-vars lop-body letrec-body)
        (value-of/k letrec-body (extend-env-rec lop-name lob-vars lop-body env) cont)))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;datatype implementation;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;(define-datatype program program?
;;  (a-program
;;    (exp1 expression?)))
;;(define identifier?
;;  (lambda (s)
;;    (and (symbol? s) (not (eq? s 'lambda)))))
;;(define-datatype expression expression?
;;  (const-exp
;;    (num number?))
;;  (diff-exp
;;    (exp1 expression?)
;;    (exp2 expression?))
;;  (zero?-exp
;;    (exp1 expression?))
;;  (if-exp
;;    (exp1 expression?)
;;    (exp2 expression?)
;;    (exp3 expression?))
;;  (var-exp
;;    (var identifier?))
;;  (let-exp
;;    (var identifier?)
;;    (exp1 expression?)
;;    (body expression?))
;;  (minus-exp
;;   (exp expression?))
;;  (add-exp
;;   (loexp (list-of expression?)))
;;  (mul-exp
;;   (loexp (list-of expression?)))
;;  (intq-exp
;;   (num number?)
;;   (exp expression?)))
  
;;;;;;;;;;;;;;;;;;;;;;;procedure datatype;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;procedural representation;;;;;;;;;;
;;(define proc?
;;  (lambda (val)
;;    (procedure? val)))
;;(define procedure
;;  (lambda (lovar body env)
;;    (lambda (loval)
;;      (value-of body (extend-env lovar loval env)))))
;;(define apply-procedure
;;  (lambda (proc1 loval)
;;    (proc1 loval)))
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
;;;;;;;;;;;;;;;;;;;;abstract-syntax representation(dynamic binding);;;;;;;;;;;;;;;;;;;;;;;;;;;be sure to modify the value-of as well
;;(define-datatype proc proc?
;;  (procedure
;;    (lovar (list-of identifier?))
;;    (body expression?)))
;;(define apply-procedure
;;  (lambda (proc1 loval env)
;;    (cases proc proc1
;;      (procedure (lovar body)
;;        (value-of body (extend-env lovar loval env))))))

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

