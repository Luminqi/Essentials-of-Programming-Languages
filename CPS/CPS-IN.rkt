(module CPS-IN
(lib "eopl.ss" "eopl")
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
    '((program (InpExp) a-program)
      
      (InpExp
       ("emptylist")
       emptylist-exp)
      
      (InpExp
       ("cons" "(" InpExp "," InpExp ")")
       cons-exp)

      (InpExp
       ("list" "(" (arbno InpExp) ")")
       list-exp)
      
      (InpExp
       ("car" "(" InpExp ")")
       car-exp)
      
      (InpExp
       ("cdr" "(" InpExp ")")
       cdr-exp)
      
      (InpExp
       ("zero?" "(" InpExp ")")
       zero?-exp)
      
      (InpExp
       ("null?" "(" InpExp ")")
       null?-exp)

      (InpExp
       ("number?" "(" InpExp ")")
       number?-exp)

      (InpExp
       ("equal?" "(" InpExp "," InpExp ")")
       equal?-exp)
      
      (InpExp (number) const-exp)
      
      (InpExp
       ("-" "(" InpExp "," InpExp ")")
       diff-exp)
      
      (InpExp
       ("*" "(" InpExp "," InpExp ")")
       mult-exp)

      (InpExp
       ("+" "(" (separated-list InpExp ",") ")")
       sum-exp)
      
      (InpExp
       ("if" InpExp "then" InpExp "else" InpExp)
       if-exp)

      (InpExp (identifier) var-exp)

      (InpExp
       ("let" (arbno identifier "=" InpExp) "in" InpExp)
       let-exp)

      (InpExp
       ("proc" "(" (arbno identifier) ")" InpExp)
       proc-exp)

      (InpExp
       ("(" InpExp (arbno InpExp) ")")
       call-exp)

      (InpExp
       ("letrec" (arbno identifier "(" (arbno identifier) ")" "=" InpExp) "in" InpExp)
      letrec-exp)
      ))
  
  ;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;
  (sllgen:make-define-datatypes the-lexical-spec the-grammar)
  (define show-the-datatypes
    (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))
  
  (define scan&parse
    (sllgen:make-string-parser the-lexical-spec the-grammar))
  
  (define just-scan
    (sllgen:make-string-scanner the-lexical-spec the-grammar))

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
(define environment? procedure?)
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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;run;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;init-env : () -> Env
(define init-env
  (lambda ()
    (extend-env
     (list 'i) (list (num-val 1))
     (extend-env
      (list 'v) (list (num-val 5))
      (extend-env
       (list 'x) (list (num-val 10))
       (empty-env))))))

;;run : String -> ExpVal
(define run
  (lambda (string)
    (value-of-program (scan&parse string))))
;;value-of-program : Program -> ExpVal
(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp)
        (value-of exp (init-env))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;value-of implementation;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;curry2 : Func -> Func
(define curry2
  (lambda (f)
    (lambda (arg1)
      (lambda (arg2)
        (f arg2 arg1)))))
;;sum : listof(num) -> num
(define sum*
  (lambda (lst cont)
    (cond
      ((null? lst) cont)
      (else
       (sum* (cdr lst) (+ cont (car lst)))))))
(define sum
  (lambda (lst)
    (sum* lst 0)))

;;;;;;;;;;;;;;;;;value-of : Exp × Env -> ExpVal;;;;;;;;;;;;;;;;;
;;value-of : Exp × Env -> ExpVal
(define value-of
  (lambda (exp env)
    (cases InpExp exp
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
      (number?-exp (exp)
        (bool-val (number? (expval->any (value-of exp env)))))
      (null?-exp (exp)
        (bool-val (null? (expval->list (value-of exp env)))))
      (emptylist-exp () (list-val '()))
      (car-exp (exp)
        (car (expval->list (value-of exp env))))
      (cdr-exp (exp)
        (list-val (cdr (expval->list (value-of exp env)))))
      (cons-exp (exp1 exp2)
        (let ((val1 (value-of exp1 env))
              (val2 (value-of exp2 env)))
          (let ((list (expval->list val2)))
            (list-val (cons val1 list)))))
      (list-exp (loexp)
        (list-val (map ((curry2 value-of) env) loexp)))
      (const-exp (num) (num-val num))
      (var-exp (var) (apply-env env var))
      (diff-exp (exp1 exp2)
        (let ((val1 (value-of exp1 env))
              (val2 (value-of exp2 env)))
          (let ((num1 (expval->num val1))
                (num2 (expval->num val2)))
            (num-val (- num1 num2)))))
      (mult-exp (exp1 exp2)
        (let ((val1 (value-of exp1 env))
              (val2 (value-of exp2 env)))
          (let ((num1 (expval->num val1))
                (num2 (expval->num val2)))
            (num-val (* num1 num2)))))
      (sum-exp (loexp)
        (let ((loval (map ((curry2 value-of) env) loexp)))
          (num-val (sum (map expval->num loval)))))
      (if-exp (exp1 exp2 exp3)
        (let ((val1 (value-of exp1 env)))
          (if (expval->bool val1)
            (value-of exp2 env)
            (value-of exp3 env))))
      (let-exp (lovar loexp body)
        (let ((loval (map ((curry2 value-of) env) loexp)))
          (value-of body
            (extend-env lovar loval env))))
      (proc-exp (lovar body)
        (proc-val (procedure lovar body env)))
      (call-exp (rator lorand)
        (let ((proc (expval->proc (value-of rator env)))
              (loarg (map ((curry2 value-of) env) lorand)))
          (apply-procedure proc loarg)))
      (letrec-exp (lop-name lob-vars lop-body letrec-body)
        (value-of letrec-body (extend-env-rec lop-name lob-vars lop-body env))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;datatype implementation;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
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
    (body InpExp?)
    (saved-env environment?)))
(define apply-procedure
  (lambda (proc1 loval)
    (cases proc proc1
      (procedure (lovar body saved-env)
        (value-of body (extend-env lovar loval saved-env))))))
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
;;expval->list : ExpVal -> List
(define expval->list
  (lambda (val)
    (cases expval val
      (list-val (list) list)
      (else (report-expval-extractor-error 'list val)))))
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
)

