(module LEXICAL-ADDR
  (lib "eopl.ss" "eopl")
  (require "../cha1.rkt")
  (provide run)
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
       ("[" number "]" "(" expression ")")
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
       ("%lexref" number number)
       nameless-var-exp)

      (expression
       ("%let" (arbno expression) "in" expression)
       nameless-let-exp)

      (expression
       ("%lexproc" expression)
       nameless-proc-exp)

      (expression
       ("%unpack" expression "in" expression number)
       nameless-unpack-exp)

      (expression
       ("%letrec-lexref" number number)
       nameless-letrec-var-exp)
      ))
  
  ;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;
  (sllgen:make-define-datatypes the-lexical-spec the-grammar)
  (define show-the-datatypes
    (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))
  
  (define scan&parse
    (sllgen:make-string-parser the-lexical-spec the-grammar))
  
  (define just-scan
    (sllgen:make-string-scanner the-lexical-spec the-grammar))
;;;;;;;;;;;;;;;;;;;;;;;;;;static environment implementation;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;helper func;;;;;;;;;;;;;;;;;
(define report-unbound-var
  (lambda (var)
    (eopl:error 'apply-senv "no binding for ~s" var)))
;;add1-on-car : List -> List
(define add1-on-car
  (lambda (lst)
    (cons (+ (car lst) 1) (cdr lst))))
;;Senv = Listof(Sym)
;;Lexaddr = N
;;empty-senv : () -> Senv
(define empty-senv
  (lambda ()
    '()))
;;extend-senv : Vars × Senv -> Senv
(define extend-senv
  (lambda (vars senv)
    (cons vars senv)))
;;apply-senv : Senv × Var -> Lexaddr
(define apply-senv
  (lambda (senv var)
    (cond
      ((null? senv)
       (report-unbound-var var))
      ((member? var (car senv))
        (let ((i (index var (car senv))))
          (list 0 i)))
      (else
        (add1-on-car (apply-senv (cdr senv) var))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;environment implementation;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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
;;;;;;;;;;;;;;;nameless-environment implementation;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;data structure representation;;;;;;;;
(define nameless-environment?
  (lambda (env)
    ((list-of (list-of expval?)) env)))
(define empty-nameless-env
  (lambda ()
    '()))
(define extend-nameless-env
  (lambda (vals nameless-env)
    (cons vals nameless-env)))
(define apply-nameless-env
  (lambda (nameless-env depth position)
    (pick position (list-ref nameless-env depth))))
;;;;;;;;;;;;;;;environment(procedural representation);;;;;;;;;;;;;;;
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
       (cons (proc-val (procedure (car lob-vars) (car lop-body) env)) (list-proc (cdr lob-vars) (cdr lop-body) env))))))
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
;;  (lambda (env search-var)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;run;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;init-senv : ()-> Senv
(define init-senv
  (lambda ()
    (extend-senv (list 'i)
      (extend-senv (list 'v)
        (extend-senv (list 'x)
          (empty-senv))))))
;;init-nameless-env : () -> Env
(define init-nameless-env
  (lambda ()
    (extend-nameless-env
      (list (num-val 1))
      (extend-nameless-env
        (list (num-val 5))
        (extend-nameless-env
          (list (num-val 10))
          (empty-nameless-env))))))

;;run : String -> ExpVal
(define run
  (lambda (string)
    (value-of-program
      (translation-of-program
        (scan&parse string)))))
;;translation-of-program :  Program -> Nameless-program
(define translation-of-program
  (lambda (pgm)
    (cases program pgm
      (num-program (exp)
        (num-program
          (translation-of exp (init-senv))))
      (bool-program (exp)
        (bool-program
          (translation-of-bool-exp exp (init-senv)))))))
;;translation-of-bool-exp : Exp × Senv -> Nameless-exp
(define translation-of-bool-exp
  (lambda (exp senv)
    (cases Bool-exp exp
      (zero?-exp (exp)
        (zero?-exp (translation-of exp senv)))
      (equal?-exp (exp1 exp2)
        (equal?-exp
          (translation-of exp1 senv)
          (translation-of exp2 senv)))
      (greater?-exp (exp1 exp2)
        (greater?-exp
          (translation-of exp1 senv)
          (translation-of exp2 senv)))
      (less?-exp (exp1 exp2)
        (less?-exp
          (translation-of exp1 senv)
          (translation-of exp2 senv))))))
;;translation-of : Exp × Senv -> Nameless-exp
;;;why only var-exp, let-exp, proc-exp need the new nameless version constructor: because the declaration of the varaibles occurs in these expressions, and we do not
;;;need these variables explicitly existing in the expression, so we need to discard the variable part of the expression which makes old constructor not suitable
(define report-invalid-source-expression
  (lambda (exp)
   (eopl:error 'translation-of "invalid source expression ~s" exp)))
(define translation-of
  (lambda (exp senv)
    (cases expression exp
      (const-exp (num) (const-exp num))
      (var-exp (var)
        (let ((addr (apply-senv senv var)))
          (nameless-var-exp (car addr) (cadr addr))))
      (diff-exp (exp1 exp2)
        (diff-exp
          (translation-of exp1 senv)
          (translation-of exp2 senv)))
      (if-exp (exp1 exp2 exp3)
        (if-exp
          (translation-of-bool-exp exp1 senv)
          (translation-of exp2 senv)
          (translation-of exp3 senv)))
      (let-exp (lovar loexp body)
        (let ((lotexp (map ((curry2 translation-of) senv) loexp))
              (tbody (translation-of body (extend-senv lovar senv))))
          (nameless-let-exp lotexp tbody)))
      (proc-exp (lovar body)
        (nameless-proc-exp
          (translation-of body (extend-senv lovar senv))))
      (call-exp (rator lorand)
        (call-exp
         (translation-of rator senv)
         (map ((curry2 translation-of) senv) lorand)))
      (cond-exp (loexp1 loexp2)
        (cond-exp
         (map ((curry2 translation-of-bool-exp) senv) loexp1)
         (map ((curry2 translation-of) senv) loexp2)))
      (emptylist-exp ()
        (emptylist-exp))
      (cons-exp (exp1 exp2)
        (cons-exp
          (translation-of exp1 senv)
          (translation-of exp2 senv)))
      (car-exp (exp)
        (car-exp
          (translation-of exp senv)))
      (cdr-exp (exp)
        (cdr-exp
          (translation-of exp senv)))
      (null?-exp (exp)
        (null?-exp
          (translation-of exp senv)))
      (list-exp (loexp)
        (list-exp
         (map ((curry2 translation-of) senv) loexp)))
      (unpack-exp (lovar lst-exp exp)
        (nameless-unpack-exp
          (translation-of lst-exp senv)
          (translation-of exp (extend-senv lovar senv))
          (length lovar)))
      (else
        (report-invalid-source-expression exp)))))

;;value-of-program : Program -> ExpVal
(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (num-program (exp)
        (value-of exp (init-nameless-env)))
      (bool-program (exp)
        (value-of-bool-exp exp (init-nameless-env))))))
;;;;;;;;;;;;;;;;;;;;;;value-of-bool-exp : Exp × Env -> ExpVal;;;;;;;;;;;;;;;;;;;;;;;;;;;
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
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;value-of implementation;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;helper func;;;;;;;;;;;;;;;
(define report-unpack-args-mismatch
  (lambda ()
    (eopl:error 'unpack-exp "the number of vars is not equal to the length of lst")))
(define report-invalid-translated-expression
  (lambda (exp)
    (eopl:error 'value-of "invalid translated expression ~s" exp)))
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

;;;;;;;;;;;;;;;;;value-of : Exp × Env -> ExpVal;;;;;;;;;;;;;;;;;
;;value-of : Exp × Env -> ExpVal
(define value-of
  (lambda (exp nameless-env)
    (cases expression exp
      (const-exp (num) (num-val num))
      (nameless-var-exp (depth position) (apply-nameless-env nameless-env depth position))
      (diff-exp (exp1 exp2)
        (let ((val1 (value-of exp1 nameless-env))
              (val2 (value-of exp2 nameless-env)))
          (let ((num1 (expval->num val1))
                (num2 (expval->num val2)))
            (num-val (- num1 num2)))))
      (if-exp (exp1 exp2 exp3)
        (let ((val1 (value-of-bool-exp exp1 nameless-env)))
          (if (expval->bool val1)
            (value-of exp2 nameless-env)
            (value-of exp3 nameless-env))))
      (nameless-let-exp (loexp body)
        (let ((loval (map ((curry2 value-of) nameless-env) loexp)))
          (value-of body
            (extend-nameless-env loval nameless-env))))
      (let*-exp (lovar loexp body)
        (let ((loval (value* lovar loexp nameless-env)))
          (value-of body
            (extend-env lovar loval nameless-env))))
      (minus-exp (exp) (num-val (- 0 (expval->num (value-of exp nameless-env)))))
      (add-exp (loexp)
        (num-val (addition loexp nameless-env)))
      (mul-exp (loexp)
        (num-val (multiply loexp nameless-env)))
      (intq-exp (num exp) (num-val (* num (expval->num (value-of exp nameless-env)))))
      (emptylist-exp () (list-val '()))
      (cons-exp (exp1 exp2)
        (let ((val1 (value-of exp1 nameless-env))
              (val2 (value-of exp2 nameless-env)))
          (let ((v1 (expval->val val1))
                (v2 (expval->list val2)))
            (list-val (cons v1 v2)))))
      (car-exp (exp)
        (let ((val (car (expval->list (value-of exp nameless-env)))))
          (cond
            ((number? val) (num-val val))
            ((boolean? val) (bool-val val))
            ((list? val) (list-val val))
            (else (proc-val val)))))
      (cdr-exp (exp)
        (let ((list (cdr (expval->list (value-of exp nameless-env)))))
          (list-val list)))
      (null?-exp (exp)
        (let ((list (expval->list (value-of exp nameless-env))))
            (bool-val (null? list))))
      (list-exp (loexp)
        (list-val (maplist loexp nameless-env)))
      (cond-exp (loexp1 loexp2)
        (value-of (pick (findIndex loexp1 nameless-env) loexp2) nameless-env))
      (nameless-unpack-exp (lst-exp exp num)
        (let ((lst (expval->list (value-of lst-exp nameless-env))))
          (if (not (eq? num (length lst)))
            (report-unpack-args-mismatch)
            (value-of exp (extend-nameless-env (map num-val lst) nameless-env)))))
      (nameless-proc-exp (body)
        (proc-val (procedure body nameless-env)))
      (call-exp (rator lorand)
        (let ((proc (expval->proc (value-of rator nameless-env)))
              (loarg (map ((curry2 value-of) nameless-env) lorand)))
          (apply-procedure proc loarg)))
      (letrec-exp (lop-name lob-vars lop-body letrec-body)
        (value-of letrec-body (extend-env-rec lop-name lob-vars lop-body nameless-env)))
      (else
        (report-invalid-translated-expression exp)))))
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
;;;;;;;;;;;nameless version abstract-syntax representation;;;;;;;;;;;;;;;
(define-datatype proc proc?
  (procedure
    (body expression?)
    (saved-nameless-env nameless-environment?)))
(define apply-procedure
  (lambda (proc1 loval)
    (cases proc proc1
      (procedure (body saved-nameless-env)
        (value-of body (extend-nameless-env loval saved-nameless-env))))))
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
;;(define-datatype proc proc?
;;  (procedure
;;    (lovar (list-of identifier?))
;;    (body expression?)
;;    (saved-env environment?)))
;;(define apply-procedure
;;  (lambda (proc1 loval)
;;    (cases proc proc1
;;      (procedure (lovar body saved-env)
;;        (value-of body (extend-env lovar loval saved-env))))))

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
;;expval->val : ExpVal -> List|Int|Bool|Proc
(define expval->val
  (lambda (val)
    (cases expval val
      (list-val (list) list)
      (num-val (num) num)
      (bool-val (bool) bool)
      (proc-val (proc) proc)
      (else (report-expval-extractor-error 'any val)))))
(define report-expval-extractor-error
  (lambda (type val)
    (cond
      ((eq? type 'num) (eopl:error 'expval->num "expect num, but reveived ~s" val))
      ((eq? type 'bool) (eopl:error 'expval->bool "expect bool, but reveived ~s" val))
      ((eq? type 'list) (eopl:error 'expval->list "expect list, but reveived ~s" val))
      ((eq? type 'proc) (eopl:error 'expval->proc "expect procedure, but reveived ~s" val))
      (else (eopl:error 'expval->val "expect list or num or bool or proc, but reveived ~s" val)))))


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

