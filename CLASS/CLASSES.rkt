(module CLASSES
(lib "eopl.ss" "eopl")
(require racket/vector)
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
    '((program
       ((arbno class-decl) expression)
       a-program)

      (class-decl
       ("class" identifier "extends" identifier (arbno "field" identifier) (arbno method-decl))
       a-class-decl)

      (method-decl
       ("method" identifier "(" (separated-list identifier ",") ")" expression)
       a-method-decl)

      (expression
       ("new" identifier "(" (separated-list expression ",") ")")
       new-object-exp)

      (expression
       ("send" expression identifier "(" (separated-list expression ",") ")")
       method-call-exp)

      (expression
       ("super" identifier "(" (separated-list expression ",") ")")
       super-call-exp)

      (expression
       ("self")
       self-exp)
      
      (expression
       ("zero?" "(" expression ")")
       zero?-exp)
      
      (expression
       ("equal?" "(" expression "," expression ")")
       equal?-exp)

      (expression
       ("greater?" "(" expression "," expression ")")
       greater?-exp)

      (expression
       ("less?" "(" expression "," expression ")")
       less?-exp)
      
      (expression (number) const-exp)
      
      (expression
        ("-" "(" expression "," expression ")")
        diff-exp)
      
      (expression
       ("if" expression "then" expression "else" expression)
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
       ("cond" (arbno expression "==>" expression) "end")
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
       ("begin" expression (arbno ";" expression) "end")
       begin-exp)

      (expression
       ("set" identifier "=" expression)
       assign-exp)

      (expression
       ("letmutable" (arbno identifier "=" expression) "in" expression)
       letmutable-exp)

      (expression
       ("setdynamic" identifier "=" expression "during" expression)
       setdynamic-exp)
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
;;;;;;;;;;;;;;;;;;;;;;;;;; environment implementation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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
;;(define environment?
;;  (lambda (v)
;;    ((list-of
;;       (list-of identifier?)
;;       (list-of number?)) v)))
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
(define extend-env-with-self-and-super
  (lambda (self s-name saved-env)
    (extend-env (list '%self '%super) (list self s-name) saved-env)))
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
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;object implementation;;;;;;;;;;;;;;;;;;;;;;
(define-datatype object object?
  (an-object
    (class-name identifier?)
    (fields (list-of reference?))))
;;object->class-name : Object -> ClassName
(define object->class-name
  (lambda (o)
    (cases object o
      (an-object (c-name fields)
        c-name))))
;;object->fields : Object -> Fields
(define object->fields
  (lambda (o)
    (cases object o
      (an-object (c-name fields)
        fields))))
;;new-object : ClassName -> Obj
(define new-object
  (lambda (class-name)
    (an-object
      class-name
      (map
        (lambda (field-name) (newref (list 'uninitialized-field field-name)))
        (class->field-names (lookup-class class-name))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;method implementation;;;;;;;;;;;;;;;;;;;;;;
(define-datatype method method?
  (a-method
    (vars (list-of identifier?))
    (body expression?)
    (super-name identifier?)
    (field-names (list-of identifier?))))
;;apply-method : Method × Obj × Listof(ExpVal) -> ExpVal
(define apply-method
  (lambda (m self args)
    (cases method m
      (a-method (vars body super-name field-names)
        (value-of body
          (extend-env vars (map newref args)
            (extend-env-with-self-and-super self super-name
              (extend-env field-names (object->fields self)
                (empty-env)))))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;class-env implementation;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;class;;;;;;;;;;;;;;;;;;;;;;
(define-datatype class class?
  (a-class
    (super-name (maybe identifier?))
    (field-names (list-of identifier?))
    (method-env method-environment?)))
(define method-environment? (list-of list?))
;;class->field-names : Class -> FieldNames
(define class->field-names
  (lambda (c)
    (cases class c
      (a-class (s-name f-names m-env)
        f-names))))
;;class->method-env : Class -> MethodEnv
(define class->method-env
  (lambda (c)
    (cases class c
      (a-class (s-name f-names m-env)
        m-env))))
;;ClassEnv = Listof(List(ClassName , Class))
;;the-class-env : ClassEnv
(define the-class-env '())
;;add-to-class-env! : ClassName × Class -> Unspecified
(define add-to-class-env!
  (lambda (class-name class)
    (set! the-class-env
      (cons
        (list class-name class)
        the-class-env))))
;;lookup-class : ClassName -> Class
(define lookup-class
  (lambda (name)
    (let ((maybe-pair (assq name the-class-env)))
      (if maybe-pair
        (cadr maybe-pair)
        (report-unknown-class name)))))
;;report-unknown-class : ClassName -> Unspecified
(define report-unknown-class
  (lambda (c-name)
    (eopl:error 'lookup-class "can not find class ~s" c-name)))
;;initialize-class-env! : Listof(ClassDecl) -> Unspecified
(define initialize-class-env!
  (lambda (c-decls)
    (set! the-class-env
      (list
        (list 'object (a-class #f '() '()))))
    (for-each initialize-class-decl! c-decls)))
;;initialize-class-decl! : ClassDecl -> Unspecified
(define initialize-class-decl!
  (lambda (c-decl)
    (cases class-decl c-decl
      (a-class-decl (c-name s-name f-names m-decls)
        (let ((f-names
                (append-field-names
                  (class->field-names (lookup-class s-name))
                  f-names)))
          (add-to-class-env!
            c-name
            (a-class s-name f-names
              (merge-method-envs
                (class->method-env (lookup-class s-name))
                (method-decls->method-env m-decls s-name f-names)))))))))
;;append-field-names : Listof(FieldName) × Listof(FieldName) -> Listof(FieldName)
(define append-field-names
  (lambda (super-fields new-fields)
    (cond
      ((null? super-fields) new-fields)
      (else
       (cons
         (if (memq (car super-fields) new-fields)
           (fresh-identifier (car super-fields))
           (car super-fields))
         (append-field-names (cdr super-fields) new-fields))))))
;;fresh-identifier : symbol -> symbol
  (define fresh-identifier
    (let ((sn 0))
      (lambda (identifier)  
        (set! sn (+ sn 1))
        (string->symbol
          (string-append
            (symbol->string identifier)
            "%"             ; this can't appear in an input identifier
            (number->string sn))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;method-env implementation;;;;;;;;;;;;;;;;;;;;;;
;;MethodEnv = Listof(List(MethodName , Method))
;;find-method : Sym × Sym -> Method
(define find-method
  (lambda (c-name name)
    (let ((m-env (class->method-env (lookup-class c-name))))
      (let ((maybe-pair (assq name m-env)))
        (if (pair? maybe-pair)
          (cadr maybe-pair)
          (report-method-not-found name))))))
;;report-method-not-found : MethodName -> Unspecified
(define report-method-not-found
  (lambda (m-name)
    (eopl:error 'find-method "can not fint the method ~s" m-name)))
;;method-decls->method-env : Listof(MethodDecl) × ClassName × Listof(FieldName) -> MethodEnv
(define method-decls->method-env
  (lambda (m-decls super-name field-names)
    (map
      (lambda (m-decl)
        (cases method-decl m-decl
          (a-method-decl (method-name vars body)
            (list method-name (a-method vars body super-name field-names)))))
      m-decls)))
;;merge-method-envs : MethodEnv × MethodEnv -> MethodEnv
(define  merge-method-envs
  (lambda (super-m-env new-m-env)
    (append new-m-env super-m-env)))
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
    (newref (num-val 1))
    (newref (num-val 5))
    (newref (num-val 10))
    (cases program pgm
      (a-program (class-decls body)
        (initialize-class-env! class-decls)
        (value-of body (init-env))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;value-of implementation;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;helper func;;;;;;;;;;;;;;;
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
             ((expval->bool (value-of (car loexp) env)) n)
             (else (index (cdr loexp) env (+ n 1))))))) loexp env 1)))
(define report-cond-fail-error
  (lambda ()
    (eopl:error 'findIndex "no condition succeed")))
;; addition: ({Exp}*) × Env -> num
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
      ((and (null? lovar) (null? loexp)) '())
      (else
       (let ((val (value-of (car loexp) env)))
         (cons val (value* (cdr lovar) (cdr loexp) (extend-env (car lovar) val env))))))))

;;;;;;;;;;;;;;;;;value-of : Exp × Env -> ExpVal;;;;;;;;;;;;;;;;;
;;value-of : Exp × Env -> ExpVal
(define value-of
  (lambda (exp env)
    (cases expression exp
      (self-exp () (apply-env env '%self))
      (method-call-exp (obj-exp method-name rands)
        (let ((args (map (lambda (exp) (value-of exp env)) rands))
              (obj (value-of obj-exp env)))
          (apply-method
            (find-method
              (object->class-name obj)
              method-name)
            obj
            args)))
      (super-call-exp (method-name rands)
        (let ((args (map (lambda (exp) (value-of exp env)) rands))
              (obj (apply-env env '%self)))
          (apply-method
            (find-method (apply-env env '%super) method-name)
            obj
            args)))
      (new-object-exp (class-name rands)
        (let ((args (map (lambda (exp) (value-of exp env)) rands))
              (obj (new-object class-name)))
          (apply-method
            (find-method class-name 'initialize)
            obj
            args)
          obj))
      (zero?-exp (exp)
        (let ((num (expval->num (value-of exp env))))
          (bool-val (zero? num))))
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
            (bool-val (< num1 num2)))))
      (const-exp (num) (num-val num))
      (var-exp (var)
        (let ((val (apply-env env var)))
          (if (reference? val)
            (deref val)
            val)))
      (assign-exp (var exp)
        (let ((ref (apply-env env var)))
          (let ((oldval (deref ref)))
            (begin
              (setref! ref (value-of exp env))
              oldval))))
      (setdynamic-exp (var exp body)
        (let ((ref (apply-env env var)))
          (let ((oldval (deref ref)))
            (setref! ref (value-of exp env))
            (let ((result (value-of body env)))
              (begin
                (setref! ref oldval)
                result)))))
      (diff-exp (exp1 exp2)
        (let ((val1 (value-of exp1 env))
              (val2 (value-of exp2 env)))
          (let ((num1 (expval->num val1))
                (num2 (expval->num val2)))
            (num-val (- num1 num2)))))
      (if-exp (exp1 exp2 exp3)
        (let ((val1 (value-of exp1 env)))
          (if (expval->bool val1)
            (value-of exp2 env)
            (value-of exp3 env))))
      (let-exp (lovar loexp body)
        (let ((loval (map ((curry2 value-of) env) loexp)))
          (value-of body
            (extend-env lovar loval env))))
      (letmutable-exp (lovar loexp body)
        (let ((loval (map ((curry2 value-of) env) loexp)))
          (value-of body
            (extend-env lovar (map newref loval) env))))
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
          (let ((lst (expval->list val2)))
            (list-val (cons val1 lst)))))
      (car-exp (exp)
        (car (expval->list (value-of exp env))))
      (cdr-exp (exp)
        (let ((list (cdr (expval->list (value-of exp env)))))
          (list-val list)))
      (null?-exp (exp)
        (let ((list (expval->list (value-of exp env))))
          (bool-val (null? list))))
      (list-exp (loexp)
        (list-val (map (lambda (exp) (value-of exp env)) loexp)))
      (cond-exp (loexp1 loexp2)
        (value-of (pick (findIndex loexp1 env) loexp2) env))
      (unpack-exp (lovar lst-exp exp)
        (let ((lst (expval->list (value-of lst-exp env))))
          (if (not (eq? (length lovar) (length lst)))
            (report-unpack-args-mismatch)
            (value-of exp (extend-env lovar (map num-val lst) env)))))
      ;;;;;lexical scoping;;;;;
      (proc-exp (lovar body)
        (proc-val (procedure lovar body env)))
      (call-exp (rator lorand)
        (let ((proc (expval->proc (value-of rator env)))
              (loarg (map ((curry2 value-of) env) lorand)))
          (apply-procedure proc loarg)))
      ;;;;;dynamic scoping;;;;;
      ;;(proc-exp (lovar body)
      ;;  (proc-val (procedure lovar body)))
      ;;(call-exp (rator lorand)
      ;;  (let ((proc (expval->proc (value-of rator env)))
      ;;        (loarg (map ((curry2 value-of) env) lorand)))
      ;;    (apply-procedure proc loarg env)))
      (letrec-exp (lop-name lob-vars lop-body letrec-body)
        (value-of letrec-body (extend-env-rec lop-name lob-vars lop-body env)))
      (begin-exp (exp loexp)
        (let ((loval (map ((curry2 value-of) env) (cons exp loexp))))
          (list-ref loval (- (length loval) 1)))))))
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
    (body expression?)
    (saved-env environment?)))
(define apply-procedure
  (lambda (proc1 loval)
    (cases proc proc1
      (procedure (lovar body saved-env)
        (value-of body (extend-env lovar (map newref loval) saved-env))))))
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
    (eopl:error 'report-expval-extractor-error "expect ~s, but reveived ~s" type val)))
)
;;exer9.1
;;(run "class queue extends object
;;field q
;;field count
;;method initialize () begin set q = emptylist; set count = 1 end
;;method empty? () begin set count = +(count,1); null?(q) end
;;method enqueue (v) let result = letrec loop (lst v) = if null?(lst) then list(v) else cons(car(lst), (loop cdr(lst) v)) in (loop q v) in begin set count = ;;+(count,1);set q = result end
;;method dequeue (f) begin set count = +(count,1); (f car(q) cdr(q)) end
;;method get-queue () begin set count = +(count,1); q end
;;method get-count () count
;;let q1 = new queue()
;;in begin
;;send q1 enqueue(1);
;;send q1 enqueue(2);
;;let f = proc (a lst) +(a,car(lst)) in send q1 dequeue(f);
;;send q1 get-count()
;;end")

