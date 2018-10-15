(module LET-2
(lib "eopl.ss" "eopl")
(require "../cha1.rkt")
(provide run value-of-program value-of)
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
       ("if" Bool-exp "then" expression "else" expression)
       if-exp)

      (expression (identifier) var-exp)

      (expression
       ("let" (arbno identifier "=" expression) "in" expression)
       let-exp)

      (expression
       ("let*" (arbno identifier "=" expression) "in" expression)
       let*-exp)

      (expression
       ("minus" "(" expression ")")
       minus-exp)

      (expression
       ("+" "(" (separated-list expression ",") ")")
       add-exp)

      (expression
       ("*" "(" (separated-list expression ",") ")")
       mul-exp)

      (expression
       ("(" number ")" "(" expression ")")
       intq-exp)

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
       ("cond" (arbno Bool-exp "==>" expression) "end")
       cond-exp)
    
      (expression
       ("unpack" (arbno identifier) "=" expression "in" expression)
       unpack-exp)
      ))
  
  ;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;
  (sllgen:make-define-datatypes the-lexical-spec the-grammar)
  (define show-the-datatypes
    (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))
  
  (define scan&parse
    (sllgen:make-string-parser the-lexical-spec the-grammar))
  
  (define just-scan
    (sllgen:make-string-scanner the-lexical-spec the-grammar))

;; environment
(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))
(define report-invalid-env
  (lambda (env)
    (eopl:error 'apply-env "Bad environment: ~s" env)))
(define empty-env
  (lambda ()
    '()))
(define extend-env
  (lambda (vars vals env)
    (cond
      ((and (atom? vars) (atom? vals)) (list (list (cons vars '()) (cons vals '())) env))
      (else (list (list vars vals) env)))))
(define apply-env
  (lambda (env search-var)
    (cond
      ((null? env)
       (report-no-binding-found search-var))
      (else
       (let ((saved-vars (caar env))
             (saved-vals (cadar env))
             (saved-env (cadr env)))
           (let ((i (index search-var saved-vars)))
             (if (not (eq? i 0))
               (pick i saved-vals)
               (apply-env saved-env search-var))))))))
(define empty-env?
  (lambda (env)
    (null? env)))
(define has-binding*?
  (lambda (env s)
    (cond
      ((null? env) #f)
      (else
       (let ((saved-vars (caar env))
             (saved-vals (cadar env))
             (saved-env (cadr env)))
         (cond
           ((member? s saved-vars) #t)
           (else (has-binding*? saved-env s))))))))
(define member?
  (lambda (s lst)
    (cond
      ((null? lst) #f)
      (else
       (cond
         ((eq? s (car lst)) #t)
         (else (member s (cdr lst))))))))
;;datatype
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

;;expval datatype
(define-datatype expval expval?
  (num-val
    (num number?))
  (bool-val
    (bool boolean?))
  (list-val
    (list list?)))
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
;;expval->val : ExpVal -> List|Int|Bool
(define expval->val
  (lambda (val)
    (cases expval val
      (list-val (list) list)
      (num-val (num) num)
      (bool-val (bool) bool)
      (else (report-expval-extractor-error 'listornumorbool val)))))
(define report-expval-extractor-error
  (lambda (type val)
    (cond
      ((eq? type 'num) (eopl:error 'expval->num "expect num, but reveived ~s" val))
      ((eq? type 'bool) (eopl:error 'expval->bool "expect bool, but reveived ~s" val))
      ((eq? type 'list) (eopl:error 'expval->list "expect list, but reveived ~s" val))
      (else (eopl:error 'expval->val "expect list or num or bool, but reveived ~s" val)))))

;;init-env : () -> Env
(define init-env
  (lambda ()
    (extend-env
     'i (num-val 1)
     (extend-env
      'v (num-val 5)
      (extend-env
       'x (num-val 10)
       (empty-env))))))

;;run : String -> ExpVal
(define run
  (lambda (string)
    (value-of-program (scan&parse string))))
;;value-of-program : Program -> ExpVal
(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (num-program (exp)
        (value-of exp (init-env)))
      (bool-program (exp)
        (value-of-bool-exp exp (init-env))))))
;;value-of-bool-exp : Exp × Env -> ExpVal
(define value-of-bool-exp
  (lambda (exp env)
    (cases Bool-exp exp
      (zero?-exp (exp)
       (let ((num (expval->num (value-of exp env))))
         (if (zero? num)
           (bool-val #t)
           (bool-val #f))))
       (equal?-exp (exp1 exp2)
         (let ((val1 (value-of exp1 env))
              (val2 (value-of exp2 env)))
          (let ((num1 (expval->num val1))
                (num2 (expval->num val2)))
            (bool-val (eq? num1 num2)))))
       (greater?-exp (exp1 exp2)
         (let ((val1 (value-of exp1 env))
              (val2 (value-of exp2 env)))
          (let ((num1 (expval->num val1))
                (num2 (expval->num val2)))
            (bool-val (> num1 num2)))))
       (less?-exp (exp1 exp2)
         (let ((val1 (value-of exp1 env))
              (val2 (value-of exp2 env)))
          (let ((num1 (expval->num val1))
                (num2 (expval->num val2)))
            (bool-val (< num1 num2))))))))
;;curry2 : Func -> Func
(define curry2
  (lambda (f)
    (lambda (arg1)
      (lambda (arg2)
        (f arg2 arg1)))))
;;value* : ({Symbol}*) × ({Exp}*) × Env -> ({Int}*)
(define value*
  (lambda (lovar loexp env)
    (cond
      ((and (null? lovar) (null? loexp) '()))
      (else
       (let ((val (value-of (car loexp) env)))
         (cons val (value* (cdr lovar) (cdr loexp) (extend-env (car lovar) val env))))))))
;;value-of : Exp × Env -> ExpVal
(define value-of
  (lambda (exp env)
    (cases expression exp
      (const-exp (num) (num-val num))
      (var-exp (var) (apply-env env var))
      (diff-exp (exp1 exp2)
        (let ((val1 (value-of exp1 env))
              (val2 (value-of exp2 env)))
          (let ((num1 (expval->num val1))
                (num2 (expval->num val2)))
            (num-val (- num1 num2)))))
      (if-exp (exp1 exp2 exp3)
        (let ((val1 (value-of-bool-exp exp1 env)))
          (if (expval->bool val1)
            (value-of exp2 env)
            (value-of exp3 env))))
      (let-exp (lovar loexp body)
        (let ((loval (map ((curry2 value-of) env) loexp)))
          (value-of body
            (extend-env lovar loval env))))
      (let*-exp (lovar loexp body)
        (let ((loval (value* lovar loexp env)))
          (value-of body
            (extend-env lovar loval env))))
      (minus-exp (exp) (num-val (- 0 (expval->num (value-of exp env)))))
      (add-exp (loexp)
        (num-val (addition loexp env)))
      (mul-exp (loexp)
        (num-val (multiply loexp env)))
      (intq-exp (num exp) (num-val (* num (expval->num (value-of exp env)))))
      (emptylist-exp () (list-val '()))
      (cons-exp (exp1 exp2)
        (let ((val1 (value-of exp1 env))
              (val2 (value-of exp2 env)))
          (let ((v1 (expval->val val1))
                (v2 (expval->list val2)))
            (list-val (cons v1 v2)))))
      (car-exp (exp)
        (let ((val (car (expval->list (value-of exp env)))))
          (cond
            ((number? val) (num-val val))
            ((boolean? val) (bool-val val))
            (else (list-val val)))))
      (cdr-exp (exp)
        (let ((list (cdr (expval->list (value-of exp env)))))
          (list-val list)))
      (null?-exp (exp)
        (let ((list (expval->list (value-of exp env))))
            (bool-val (null? list))))
      (list-exp (loexp)
        (list-val (maplist loexp env)))
      (cond-exp (loexp1 loexp2)
        (value-of (pick (findIndex loexp1 env) loexp2) env))
      (unpack-exp (lovar lst-exp exp)
        (let ((lst (expval->list (value-of lst-exp env))))
          (if (not (eq? (length lovar) (length lst)))
            (report-unpack-args-mismatch)
            (value-of exp (extend-env lovar (map num-val lst) env))))))))
  
(define report-unpack-args-mismatch
  (lambda ()
    (eopl:error 'unpack-exp "the number of vars is not equal to the length of lst")))
;; applicative-order Y combinator
(define  Y
  (lambda (le)
    ((lambda (f) (f f))
     (lambda (f)
       (le (lambda (x y z) ((f f) x y z)))))))
;; findIndex: ({Exp}*) × Env -> Int
(define findIndex
  (lambda (loexp env)
    ((Y (lambda (index)
         (lambda (loexp env n)
           (cond
             ((null? loexp) (report-cond-fail-error))
             ((expval->bool (value-of-bool-exp (car loexp) env)) n)
             (else (index (cdr loexp) env (+ n 1))))))) loexp env 1)))
(define report-cond-fail-error
  (lambda ()
    (eopl:error 'findIndex "no condition succeed")))
;; maplist: ({Exp}*) × Env -> list
(define maplist
  (lambda (loexp env)
    (cond
      ((null? loexp) '())
      (else
       (let ((val (expval->val (value-of (car loexp) env))))
         (cons val (maplist (cdr loexp) env)))))))
;; addition: ({Exp}*) × Ent -> num
(define addition
  (lambda (loexp env)
    (cond
      ((null? loexp) 0)
      (else
       (let ((num (expval->num (value-of (car loexp) env))))
         (+ num (addition (cdr loexp) env)))))))
;; multiply: ({Exp}*) × Env -> num
(define multiply
  (lambda (loexp env)
    (cond
      ((null? loexp) 1)
      (else
       (let ((num (expval->num (value-of (car loexp) env))))
         (* num (multiply (cdr loexp) env)))))))
)
