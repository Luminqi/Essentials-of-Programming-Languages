(module CPS-OUT
(lib "eopl.ss" "eopl")
(require "../cha1.rkt")
(provide run)
;;;;;;;;;;;;;lang;;;;;;;;;;;;;;;;;;;;;;
  (define cps-the-lexical-spec
    '((whitespace (whitespace) skip)
      (comment ("%" (arbno (not #\newline))) skip)
      (identifier
       (letter (arbno (or letter digit "_" "-" "?")))
       symbol)
      (number (digit (arbno digit)) number)
      (number ("-" digit (arbno digit)) number)
      ))
  
  (define cps-the-grammar
    '((program (TfExp) cps-a-program)
      
      (SimpleExp (number) cps-const-exp)

      (SimpleExp (identifier) cps-var-exp)
      
      (SimpleExp
       ("-" "(" SimpleExp "," SimpleExp ")")
       cps-diff-exp)
      
      (SimpleExp
       ("*" "(" SimpleExp "," SimpleExp ")")
       cps-mult-exp)
      
      (SimpleExp
       ("+" "(" (separated-list SimpleExp ",") ")")
       cps-sum-exp)
      
      (SimpleExp
       ("zero?" "(" SimpleExp ")")
       cps-zero?-exp)

      (SimpleExp
       ("null?" "(" SimpleExp ")")
       cps-null?-exp)

      (SimpleExp
       ("number?" "(" SimpleExp ")")
       cps-number?-exp)

      (SimpleExp
       ("equal?" "(" SimpleExp "," SimpleExp ")")
       cps-equal?-exp)
   
      (SimpleExp
       ("proc" "(" (arbno identifier) ")" TfExp)
       cps-proc-exp)

      (SimpleExp
       ("emptylist")
       cps-emptylist-exp)
      
      (SimpleExp
       ("cons" "(" SimpleExp "," SimpleExp ")")
       cps-cons-exp)

      (SimpleExp
       ("list" "(" (arbno SimpleExp) ")")
       cps-list-exp)
      
      (SimpleExp
       ("car" "(" SimpleExp ")")
       cps-car-exp)
      
      (SimpleExp
       ("cdr" "(" SimpleExp ")")
       cps-cdr-exp)      

      (TfExp (SimpleExp) simple-exp->exp)
      
      (TfExp
       ("let" (arbno identifier "=" SimpleExp) "in" TfExp)
       cps-let-exp)

      (TfExp
       ("letrec" (arbno identifier "(" (arbno identifier) ")" "=" TfExp) "in" TfExp)
       cps-letrec-exp)
       
      (TfExp
       ("if" SimpleExp "then" TfExp "else" TfExp)
       cps-if-exp)

      (TfExp
       ("(" SimpleExp (arbno SimpleExp) ")")
       cps-call-exp)
      ))
  
  ;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;
  (sllgen:make-define-datatypes cps-the-lexical-spec cps-the-grammar)
  (define show-the-datatypes
    (lambda () (sllgen:list-define-datatypes cps-the-lexical-spec cps-the-grammar)))
  
  (define scan&parse
    (sllgen:make-string-parser cps-the-lexical-spec cps-the-grammar))
  
  (define just-scan
    (sllgen:make-string-scanner cps-the-lexical-spec cps-the-grammar))

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
      (cps-a-program (exp)
        (value-of/k exp (init-env))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;value-of implementation;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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
;;value-of-simple-exp : Exp × Env -> ExpVal
(define value-of-simple-exp
  (lambda (exp env)
    (cases SimpleExp exp
      (cps-const-exp (num) (num-val num))
      (cps-var-exp (var) (apply-env env var))
      (cps-diff-exp (simple1 simple2)
        (let ((val1 (value-of-simple-exp simple1 env))
              (val2 (value-of-simple-exp simple2 env)))
          (let ((num1 (expval->num val1))
                (num2 (expval->num val2)))
            (num-val (- num1 num2)))))
      (cps-mult-exp (simple1 simple2)
        (let ((val1 (value-of-simple-exp simple1 env))
              (val2 (value-of-simple-exp simple2 env)))
          (let ((num1 (expval->num val1))
                (num2 (expval->num val2)))
            (num-val (* num1 num2)))))
      (cps-sum-exp (losimple)
        (let ((loval (map (lambda (simple) (value-of-simple-exp simple env)) losimple)))
          (num-val (sum (map expval->num loval)))))
      (cps-zero?-exp (simple)
        (bool-val (zero? (expval->num (value-of-simple-exp simple env)))))
      (cps-equal?-exp (simple1 simple2)
        (let ((val1 (value-of-simple-exp simple1 env))
              (val2 (value-of-simple-exp simple2 env)))
          (let ((num1 (expval->num val1))
                (num2 (expval->num val2)))
            (bool-val (eq? num1 num2)))))
      (cps-number?-exp (simple)
        (bool-val (number? (expval->any (value-of-simple-exp simple env)))))
      (cps-null?-exp (simple)
        (bool-val (null? (expval->list (value-of-simple-exp simple env)))))
      (cps-emptylist-exp () (list-val '()))
      (cps-car-exp (simple)
        (car (expval->list (value-of-simple-exp simple env))))
      (cps-cdr-exp (simple)
        (list-val (cdr (expval->list (value-of-simple-exp simple env)))))
      (cps-cons-exp (simple1 simple2)
        (let ((val1 (value-of-simple-exp simple1 env))
              (val2 (value-of-simple-exp simple2 env)))
          (let ((list (expval->list val2)))
            (list-val (cons val1 list)))))
      (cps-list-exp (losimple)
        (list-val (map (lambda (simple) (value-of-simple-exp simple env)) losimple)))
      (cps-proc-exp (lovar body)
        (proc-val (procedure lovar body env))))))
;;value-of/k : Exp × Env -> ExpVal
(define value-of/k
  (lambda (exp env)
    (cases TfExp exp
      (simple-exp->exp (simple)
        (apply-cont (end-cont)
          (value-of-simple-exp simple env)))
      (cps-let-exp (lovar losimple body)
        (let ((loval (map (lambda (simple) (value-of-simple-exp simple env)) losimple)))
          (value-of/k body
            (extend-env lovar loval env))))
      (cps-letrec-exp (lop-name lob-vars lop-body letrec-body)
        (value-of/k letrec-body (extend-env-rec lop-name lob-vars lop-body env)))
      (cps-if-exp (simple body1 body2)
        (if (expval->bool (value-of-simple-exp simple env))
          (value-of/k body1 env)
          (value-of/k body2 env)))
      (cps-call-exp (rator lorand)
        (let ((proc (expval->proc (value-of-simple-exp rator env)))
              (loarg (map (lambda (simple) (value-of-simple-exp simple env)) lorand)))
          (apply-procedure proc loarg))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;continuation implementation;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define end-cont
  (lambda ()
    (lambda (val)
      (eopl:printf "End of computation.~%")
      val)))
(define apply-cont
  (lambda (cont val)
    (cont val)))
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
    (body TfExp?)
    (saved-env environment?)))
(define apply-procedure
  (lambda (proc1 loval)
    (cases proc proc1
      (procedure (lovar body saved-env)
        (value-of/k body (extend-env lovar loval saved-env))))))
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

