(module TYPED-OO
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
       ("class" identifier "extends" identifier (arbno "implements" identifier) (arbno "field" type identifier) (arbno method-decl))
       a-class-decl)

      (class-decl
       ("interface" identifier (arbno abstract-method-decl))
       an-interface-decl)

      (method-decl
       ("method" type identifier "(" (separated-list identifier ":" type ",") ")" expression)
       a-method-decl)

      (abstract-method-decl
       ("method" type identifier "(" (separated-list identifier ":" type ",") ")")
       an-abstract-method-decl)

      (expression
       ("cast" expression identifier)
       cast-exp)

      (expression
       ("instanceof" expression identifier)
       instanceof-exp)

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
       ("+" "(" (separated-list expression ",") ")")
       add-exp)

      (expression
       ("*" "(" (separated-list expression ",") ")")
       mul-exp)

      (expression
       ("emptylist_" type)
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
       ("list" "(" expression (arbno "," expression) ")")
       list-exp)
      
      (expression
       ("proc" "(" (arbno identifier ":" type) ")" expression)
       proc-exp)

      (expression
       ("(" expression (arbno expression) ")")
       call-exp)

      (expression
       ("letrec" (arbno type identifier "(" (arbno identifier ":" type) ")" "=" expression) "in" expression)
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

      (type
       ("int")
       int-type)

      (type
       ("bool")
       bool-type)

      (type
       ("(" (separated-list type "*") "->" type ")")
       proc-type)

      (type
       ("void")
       void-type)

      (type
       (identifier)
       class-type)

      (type
       ("listof" type)
       list-type)
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
    (eopl:error 'apply-env "No binding for ~s~%" search-var)))
(define report-invalid-env
  (lambda (env)
    (eopl:error 'apply-env "Bad environment: ~s~%" env)))
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
;;class->super-name : Class -> SuperName
(define class->super-name
  (lambda (c)
    (cases class c
      (a-class (s-name f-names m-env)
        s-name))))
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
;;is-subclass? : ClassName × ClassName -> Bool
(define is-subclass?
  (lambda (c-name1 c-name2)
    (cond
      ((eqv? c-name1 c-name2) #t)
      (else
       (let ((s-name (class->super-name (lookup-class c-name1))))
       (if s-name
         (is-subclass? s-name c-name2)
         #f))))))
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
    (eopl:error 'lookup-class "can not find class ~s~%" c-name)))
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
      (a-class-decl (c-name s-name i-names f-types f-names m-decls)
        (let ((f-names
                (append-field-names
                  (class->field-names (lookup-class s-name))
                  f-names)))
          (add-to-class-env!
            c-name
            (a-class s-name f-names
              (merge-method-envs
                (class->method-env (lookup-class s-name))
                (method-decls->method-env m-decls s-name f-names))))))
      (an-interface-decl (i-name abs-m-decls)
        (eopl:printf "don't need to init interface ~s for value-of~%" i-name)))))
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
    (eopl:error 'find-method "can not fint the method ~s~%" m-name)))
;;method-decls->method-env : Listof(MethodDecl) × ClassName × Listof(FieldName) -> MethodEnv
(define method-decls->method-env
  (lambda (m-decls super-name field-names)
    (map
      (lambda (m-decl)
        (cases method-decl m-decl
          (a-method-decl (res-type method-name vars var-types body)
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
    (begin
      (eopl:printf "type: ~s~%" (type-of-program (scan&parse string)))
      (value-of-program (scan&parse string)))))
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
    (eopl:error 'unpack-exp "the number of vars is not equal to the length of lst~%")))
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
    (eopl:error 'findIndex "no condition succeed~%")))
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
      (cast-exp (exp c-name)
        (let ((obj (value-of exp env)))
          (if (is-subclass? (object->class-name obj) c-name)
            obj
            (report-cast-error c-name obj))))
      (instanceof-exp (exp c-name)
        (let ((obj (value-of exp env)))
         (if (is-subclass? (object->class-name obj) c-name)
           (bool-val #t)
           (bool-val #f))))
      (zero?-exp (exp)
        (let ((num (expval->num (value-of exp env))))
          (bool-val (zero? num))))
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
      (add-exp (loexp)
        (num-val (addition loexp env)))
      (mul-exp (loexp)
        (num-val (multiply loexp env)))
      (emptylist-exp (ty1) (list-val '()))
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
      (list-exp (exp1 loexp)
        (list-val (map (lambda (exp) (value-of exp env)) (cons exp1 loexp))))
      ;;;;;lexical scoping;;;;;
      (proc-exp (lovar lovar-type body )
        (proc-val (procedure lovar body env)))
      (call-exp (rator lorand)
        (let ((proc (expval->proc (value-of rator env)))
              (loarg (map ((curry2 value-of) env) lorand)))
          (apply-procedure proc loarg)))
      (letrec-exp (lop-result-type lop-name lob-vars lob-var-types lop-body letrec-body) 
        (value-of letrec-body (extend-env-rec lop-name lob-vars lop-body env)))
      (begin-exp (exp loexp)
        (let ((loval (map ((curry2 value-of) env) (cons exp loexp))))
          (list-ref loval (- (length loval) 1)))))))
  ;;report-cast-error : ClassName × Object -> Unspecified
  (define report-cast-error
    (lambda (c-name obj)
      (eopl:error 'report-cast-error "cast exp fail: object ~s is not an instance of the class ~s or of one of its descendants~%" obj c-name)))
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
    (eopl:error 'report-expval-extractor-error "expect ~s, but reveived ~s~%" type val)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;type-environment(abstract-syntax representation);;;;;;;;;;;;;;;;;;;;
  (define-datatype type-environment type-environment?
    (empty-tenv)
    (extend-tenv
     (vars (list-of identifier?))
     (types (list-of type?))
     (env type-environment?))
    (extend-tenv-with-self-and-super
     (self type?)
     (super identifier?)
     (env type-environment?)))
  (define apply-tenv
    (lambda (env search-var)
      (cases type-environment env
        (empty-tenv ()
          (eopl:error 'apply-tenv "Unbound variable ~s in tenv~%" search-var))
        (extend-tenv (saved-vars saved-types saved-tenv)
          (let ((i (index search-var saved-vars)))
            (if (not (zero? i))
              (pick i saved-types)
              (apply-tenv saved-tenv search-var))))
        (extend-tenv-with-self-and-super (self super saved-tenv)
          (cond
            ((equal? search-var '%self) self)
            ((equal? search-var '%super) super)
            (else (apply-tenv saved-tenv search-var)))))))
  ;;init-tenv : () -> tenv
  (define init-tenv
    (lambda ()
      (extend-tenv
       (list 'i) (list (int-type))
       (extend-tenv
        (list 'v) (list (int-type))
        (extend-tenv
         (list 'x) (list (int-type))
         (empty-tenv))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;checker;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;check-all : Listof(Type) × Listof(Type) × Listof(Exp) -> Unspecified
  (define check-all
    (lambda (loty1 loty2 loexp)
      (cond
        ((eq? (length loty1) 1) (check-equal-type! (car loty1) (car loty2) (car loexp)))
        (else
         (begin
           (check-equal-type! (car loty1) (car loty2) (car loexp))
           (check-all (cdr loty1) (cdr loty2) (cdr loexp)))))))
  ;;check-equal-type! : Type × Type × Exp -> Unspecified
  (define check-equal-type!
    (lambda (ty1 ty2 exp)
      (when (not (equal? ty1 ty2))
        (report-unequal-types ty1 ty2 exp))))
  ;;report-unequal-types : Type × Type × Exp -> Unspecified
  (define report-unequal-types
    (lambda (ty1 ty2 exp)
      (eopl:error 'check-equal-type!
                  "Types didn’t match: ~s != ~s in ~s~%"
                  (type-to-external-form ty1)
                  (type-to-external-form ty2)
                  exp)))
  ;;type-to-external-form : Type -> List
  (define type-to-external-form
    (lambda (ty)
      (cases type ty
        (int-type () 'int)
        (bool-type () 'bool)
        (proc-type (loarg-type result-type)
          (up
            (list
              (insertSym '* (map type-to-external-form loarg-type))
              '->
              (type-to-external-form result-type))))
        (list-type (ty1)
          (list 'listof (type-to-external-form ty1)))
        (void-type ()
          (list 'void))
        (class-type (sym)
          (list 'class sym)))))
  ;;insertSym : Sym × List -> List
  (define insertSym
    (lambda (sym lst)
      (cond
        ((or (null? lst) (eq? (length lst) 1)) lst)
        (else (cons (car lst) (cons sym (insertSym sym (cdr lst))))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;static-class env;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  
  (define-datatype static-class static-class?
    (a-static-class
      (super-name (maybe identifier?))
      (interface-names (list-of identifier?))
      (field-names (list-of identifier?))
      (field-types (list-of type?))
      (method-tenv method-tenv?))
    (an-interface
      (method-tenv method-tenv?)))
  ;;;;find-method -type: Sym × Sym -> Method
  (define find-method-type
    (lambda (c-name m-name)
      (let ((m-tenv (static-class->method-tenv (lookup-static-class c-name))))
        (let ((maybe-pair (assq m-name m-tenv)))
          (if (pair? maybe-pair)
            (cadr maybe-pair)
            (report-method-not-found m-name))))))
  ;;static-class->super-name : StaticClass -> SuperName
  (define static-class->super-name
    (lambda (sc)
      (cases static-class sc
        (a-static-class (s-name i-names f-names f-types m-tenv)
          s-name)
        (an-interface (m-tenv)
          (report-interface-extrator-error 'super-name sc)))))
  ;;static-class->interface-names : StaticClass -> InterfaceNames
  (define static-class->interface-names
    (lambda (sc)
      (cases static-class sc
        (a-static-class (s-name i-names f-names f-types m-tenv)
          i-names)
        (an-interface (m-tenv)
          (report-interface-extrator-error 'interface-names sc)))))
   ;;static-class->field-names : StaticClass -> FieldNames
  (define static-class->field-names
    (lambda (sc)
      (cases static-class sc
        (a-static-class (s-name i-names f-names f-types m-tenv)
          f-names)
        (an-interface (m-tenv)
          (report-interface-extrator-error 'field-names sc)))))
  ;;static-class->field-types : StaticClass -> FieldTypes
  (define static-class->field-types
    (lambda (sc)
      (cases static-class sc
        (a-static-class (s-name i-names f-names f-types m-tenv)
          f-types)
        (an-interface (m-tenv)
          (report-interface-extrator-error 'field-types sc)))))
  ;;static-class->method-tenv : StaticClass -> MethodTenv
  (define static-class->method-tenv
    (lambda (sc)
      (cases static-class sc
        (a-static-class (s-name i-names f-names f-types m-tenv)
          m-tenv)
        (an-interface (m-tenv)
          m-tenv))))
  ;;report-interface-extrator-error : Sym × Sym -> Unspecified 
  (define report-interface-extrator-error
    (lambda (field sc)
      (eopl:error 'report-interface-extrator-error "unable to find ~s in an interface ~s~%" field sc)))
  ;;method-tenv  = List(MethodName,Type)
  ;;method-tenv? : Val -> Bool
  (define method-tenv? (list-of list?))
  ;;StaticClassEnv = Listof(List(ClassName , StaticClass))
  ;;the-static-class-env : StaticClassEnv
  (define the-static-class-env '())
  ;;empty-the-static-class-env! : () -> Unspecified
  (define empty-the-static-class-env!
    (lambda ()
      (set! the-static-class-env '())))
  ;;add-static-class-binding! : ClassName × StaticClass -> Unspecified
  (define add-static-class-binding!
    (lambda (class-name static-class)
      (set! the-static-class-env
        (cons
          (list class-name static-class)
          the-static-class-env))))
  ;;lookup-static-class : ClassName -> StaticClass
  (define lookup-static-class
    (lambda (name)
      (let ((maybe-pair (assq name the-static-class-env)))
        (if maybe-pair
          (cadr maybe-pair)
          (report-unknown-static-class name)))))
  ;;report-unknown-static-class : ClassName -> Unspecified
  (define report-unknown-static-class
    (lambda (c-name)
      (eopl:error 'lookup-static-class "can not find static class ~s~%" c-name)))
  ;;initialize-static-class-env! : Listof(ClassDecl) -> Unspecified
  (define initialize-static-class-env!
    (lambda (c-decls)
      (empty-the-static-class-env!)
      (add-static-class-binding!
        'object (a-static-class #f '() '() '() '()))
      (for-each add-class-decl-to-static-class-env! c-decls)))
  ;;add-class-decl-to-static-class-env! : ClassDecl -> Unspecified
  (define add-class-decl-to-static-class-env!
    (lambda (c-decl)
      (cases class-decl c-decl
        (an-interface-decl (i-name abs-m-decls)
          (let ((m-tenv (abs-method-decls->method-tenv abs-m-decls)))
            (check-no-dups! (map car m-tenv) i-name)
            (add-static-class-binding! i-name (an-interface m-tenv))))
        (a-class-decl (c-name s-name i-names f-types f-names m-decls)
          (let ((i-names
                  (append
                    (static-class->interface-names (lookup-static-class s-name))
                    i-names))
                (f-names
                  (append-field-names
                    (static-class->field-names (lookup-static-class s-name))
                    f-names))
                (f-types
                  (append
                    (static-class->field-types (lookup-static-class s-name))
                    f-types))
                (method-tenv
                  (let ((local-method-tenv (method-decls->method-tenv m-decls)))
                    (check-no-dups! (map car local-method-tenv) c-name)
                    (merge-method-tenvs
                      (static-class->method-tenv (lookup-static-class s-name))
                      local-method-tenv))))
            (check-no-dups! i-names c-name)
            (check-no-dups! f-names c-name)
            (check-for-initialize! method-tenv c-name)
            (add-static-class-binding! c-name (a-static-class
                                                s-name i-names f-names f-types method-tenv)))))))
  ;;abs-method-decls->method-tenv : Listof(AbstractMethodDecl) ->  MethodTenv
  (define abs-method-decls->method-tenv
    (lambda (abs-m-decls)
      (if (null? abs-m-decls)
        '()
        (cases abstract-method-decl (car abs-m-decls)
          (an-abstract-method-decl (res-type m-name vars var-types)
            (cons
              (list m-name (proc-type var-types res-type))
              (abs-method-decls->method-tenv (cdr abs-m-decls))))))))
  ;;method-decls->method-tenv : Listof(MethodDecl) ->  MethodTenv
  (define method-decls->method-tenv
    (lambda (m-decls)
      (if (null? m-decls)
        '()
        (cases method-decl (car m-decls)
          (a-method-decl (res-type m-name vars var-types body)
            (cons
              (list m-name (proc-type var-types res-type))
              (method-decls->method-tenv (cdr m-decls))))))))
  ;;check-no-dups! : Listof(Name) × ClassName || InterfaceName -> Unspecified
  (define check-no-dups!
    (lambda (names c-name)
      (let ((d-name (no-repeat? names)))
        (when (symbol? d-name)
          (report-duplicated-name d-name c-name)))))
   ;;report-duplicated-names : Sym × Sym -> Unspecified
  (define report-duplicated-name
    (lambda (d-name c-name)
      (eopl:error 'check-no-dups! "duplicated name ~s in ~s~%" d-name c-name)))
  ;;no-repeat? : List -> True || Sym
  (define no-repeat?
    (lambda (lst)
      (if (<= (length lst) 1)
        #t
        (let ((maybe-sym (mem? (car lst) (cdr lst))))
          (if maybe-sym
            maybe-sym
            (no-repeat? (cdr lst)))))))
  ;;mem? : Sym × List -> False || Sym
  (define mem?
    (lambda (sym lst)
      (cond
        ((null? lst) #f)
        ((equal? sym (car lst)) sym)
        (else
         (mem? sym (cdr lst))))))
  ;;merge-method-tenvs : MethodTenv × MethodTenv -> MethodTenv
  (define merge-method-tenvs
    (lambda (s-m-tenv l-m-tenv)
      (append l-m-tenv s-m-tenv)))
  ;;check-for-initialize! method-tenv c-name
  (define check-for-initialize!
    (lambda (m-tenv c-name)
      (unless (assq 'initialize m-tenv)
        (report-no-initialize-in-declaration c-name))))
  ;;report-no-initialize-in-declaration : ClassName -> Unspecified
  (define report-no-initialize-in-declaration
    (lambda (c-name)
      (eopl:error 'check-for-initialize! "no method initialize in class ~s~%" c-name)))
  ;;check-class-decl! : ClassDecl -> Unspecified
  (define check-class-decl!
    (lambda (c-decl)
      (cases class-decl c-decl
        (an-interface-decl (i-name abs-method-decls)
          #t)
        (a-class-decl (class-name super-name i-names field-types field-names method-decls)
          (let ((sc (lookup-static-class class-name)))
            (for-each
              (lambda (method-decl)
                (check-method-decl! method-decl class-name super-name
                  (static-class->field-names sc)
                  (static-class->field-types sc)))
              method-decls))
          (for-each
            (lambda (i-name) (check-if-implements! class-name i-name))
            i-names)))))
  ;;check-method-decl! : MethodDecl × ClassName × ClassName × Listof(FieldName) × Listof(Type) -> Bool
  (define check-method-decl!
    (lambda (m-decl self-name s-name f-names f-types)
      (cases method-decl m-decl
        (a-method-decl (res-type m-name vars var-types body)
          (let ((tenv (extend-tenv vars var-types
                        (extend-tenv-with-self-and-super (class-type self-name) s-name
                          (extend-tenv f-names f-types
                            (init-tenv))))))
            (let ((body-type (type-of body tenv)))
              (check-is-subtype! body-type res-type m-decl)
              (if (eqv? m-name 'initialize)
                #t
                (let ((maybe-super-type
                        (maybe-find-method-type
                          (static-class->method-tenv (lookup-static-class s-name))
                          m-name)))
                  (if maybe-super-type
                    (check-is-subtype! (proc-type var-types res-type) maybe-super-type body)
                    #t)))))))))
  ;;maybe-find-method-type : MethodTenv × MethodName -> Maybe(Type)
  (define maybe-find-method-type
    (lambda (m-tenv m-name)
      (let ((maybe-pair (assq m-name m-tenv)))
        (if (pair? maybe-pair)
          (cadr maybe-pair)
          #f))))
  ;;check-if-implements! : ClassName × InterfaceName -> Bool
  (define check-if-implements!
    (lambda (c-name i-name)
      (cases static-class (lookup-static-class i-name)
        (a-static-class (s-name i-names f-names f-types m-tenv)
          (report-cant-implement-non-interface c-name i-name))
        (an-interface (method-tenv)
          (let ((class-method-tenv (static-class->method-tenv (lookup-static-class c-name))))
            (for-each
              (lambda (method-binding)
                (let ((m-name (car method-binding))
                      (m-type (cadr method-binding)))
                  (let ((c-method-type
                          (maybe-find-method-type
                            class-method-tenv
                            m-name)))
                    (if c-method-type
                      (check-is-subtype! c-method-type m-type c-name)
                      (report-missing-method c-name i-name m-name)))))
               method-tenv))))))
  ;;report-cant-implement-non-interface : Sym × Sym -> Unspecified
  (define report-cant-implement-non-interface
    (lambda (c-name i-name)
      (eopl:error 'check-if-implements! "can't implement ~s which is not an interface in ~s~%" i-name c-name)))
  ;;report-missing-method : Sym × Sym × Sym -> Unspecified
  (define report-missing-method
    (lambda (c-name i-name m-name)
      (eopl:error 'check-if-implements! "missing method ~s in class ~s which implements interface ~s~%" m-name c-name i-name)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;type-of-program;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;type-of-program : Program -> Type
  (define type-of-program
    (lambda (pgm)
      (cases program pgm
        (a-program (class-decls exp1)
          (initialize-static-class-env! class-decls)
          (for-each check-class-decl! class-decls)
          (type-of exp1 (init-tenv))))))
  ;;type-of-call : Type × Listof(Type) × Listof(Exp) -> Type
  (define type-of-call
    (lambda (rator-type rand-types rands exp)
      (cases type rator-type
        (proc-type (arg-types result-type)
          (when (not (= (length arg-types) (length rand-types)))
            (report-wrong-number-of-arguments
              (map type-to-external-form arg-types)
              (map type-to-external-form rand-types)
              exp))
          (for-each check-is-subtype! rand-types arg-types rands)
          result-type)
        (else
          (report-rator-not-a-proc-type rator-type exp)))))
  ;;report-wrong-number-of-arguments
  (define report-wrong-number-of-arguments
    (lambda (et1 et2 exp)
      (eopl:error 'report-wrong-number-of-arguments "exp ~s has argument types ~s and has been provided wrong number of arguments ~s~%" exp et1 et2)))
  ;;check-is-subtype! : Type × Type × Exp -> Unspecified
  (define check-is-subtype!
    (lambda (ty1 ty2 exp)
      (if (is-subtype? ty1 ty2)
        #t
        (report-subtype-failure
          (type-to-external-form ty1)
          (type-to-external-form ty2)
          exp))))
  ;;report-subtype-failure
  (define report-subtype-failure
    (lambda (et1 et2 exp)
      (eopl:error 'check-is-subtype! "type ~s is not a subtype of type ~s in exp ~s~%" et1 et2 exp)))
  ;;is-subtype? : Type × Type -> Bool
  (define is-subtype?
    (lambda (ty1 ty2)
      (cases type ty1
        (class-type (name1)
          (cases type ty2
            (class-type (name2)
              (statically-is-subclass? name1 name2))
            (else #f)))
        (proc-type (args1 res1)
          (cases type ty2
            (proc-type (args2 res2)
              (and
                (every2? is-subtype? args2 args1)
                (is-subtype? res1 res2)))
            (else #f)))
        (else (equal? ty1 ty2)))))
  ;;every2? : Pred × List × List -> Bool
  (define every2?
    (lambda (pred lst1 lst2)
      (cond
        ((not (equal? (length lst1) (length lst2))) #f)
        ((null? lst1) #t)
        ((not (pred (car lst1) (car lst2))) #f)
        (else
         (every2? pred (cdr lst1) (cdr lst2))))))
  ;;statically-is-subclass? : ClassName × ClassName -> Bool
  (define statically-is-subclass?
    (lambda (name1 name2)
      (or
       (eqv? name1 name2)
       (let ((super-name (static-class->super-name (lookup-static-class name1))))
         (if super-name
           (statically-is-subclass? super-name name2)
           #f))
       (let ((interface-names (static-class->interface-names (lookup-static-class name1))))
         (memv name2 interface-names)))))
  ;;type-of : Exp × Tenv -> Type
  (define type-of
    (lambda (exp tenv)
      (cases expression exp
        (self-exp () (apply-tenv tenv '%self))
        (instanceof-exp (obj-exp class-name)
          (let ((obj-type (type-of obj-exp tenv))
                (sc (assq class-name the-static-class-env)))
            (if sc
              (if (class-type? obj-type)
                (bool-type)
                (report-bad-type-to-instanceof obj-type obj-exp))
              (report-bad-class-to-instanceof class-name))))
        (cast-exp (obj-exp class-name)
          (let ((obj-type (type-of obj-exp tenv))
                (sc (assq class-name the-static-class-env)))
            (if sc
              (if (class-type? obj-type)
                (class-type class-name)
                (report-bad-type-to-cast obj-type obj-exp))
              (report-bad-class-to-cast class-name))))
        (method-call-exp (obj-exp method-name rands)
          (let ((arg-types (map (lambda (exp) (type-of exp tenv)) rands))
                (obj-type (type-of obj-exp tenv)))
           (type-of-call
             (find-method-type
               (type->class-name obj-type)
               method-name)
             arg-types
             rands
             exp)))
        (super-call-exp (method-name rands)
          (let ((arg-types (map (lambda (exp) (type-of exp tenv)) rands))
                (obj-type (apply-tenv tenv '%self)))
            (type-of-call
              (find-method-type
                (apply-tenv tenv '%super)
                method-name)
              arg-types
              rands
              exp)))
        (new-object-exp (class-name rands)
          (let ((arg-types (map (lambda (exp) (type-of exp tenv)) rands))
                (c (lookup-static-class class-name)))
            (cases static-class c
              (an-interface (method-tenv)
                (report-cant-instantiate-interface class-name))
              (a-static-class (super-name i-names field-names field-types method-tenv)
                (type-of-call
                  (find-method-type
                    class-name
                    'initialize)
                  arg-types
                  rands
                  exp)
                (class-type class-name)))))
        (const-exp (num) (int-type))
        (var-exp (var) (apply-tenv tenv var))
        (diff-exp (exp1 exp2)
          (let ((ty1 (type-of exp1 tenv))
                (ty2 (type-of exp2 tenv)))
            (check-equal-type! ty1 (int-type) exp1)
            (check-equal-type! ty2 (int-type) exp2)
            (int-type)))
        (add-exp (loexp)
          (let ((lotype (map (lambda (exp) (type-of exp tenv)) loexp)))
            (for-each (lambda (ty) (check-equal-type! ty (int-type) exp)) lotype)
            (int-type)))
        (mul-exp (loexp)
          (let ((lotype (map (lambda (exp) (type-of exp tenv)) loexp)))
            (for-each (lambda (ty) (check-equal-type! ty (int-type) exp)) lotype)
            (int-type)))
        (begin-exp (exp1 loexp)
          (let loop ((loexp (cons exp1 loexp)))
            (if (eq? (length loexp) 1)
              (type-of (car loexp) tenv)
              (begin
                (type-of (car loexp) tenv)
                (loop (cdr loexp))))))
        (zero?-exp (exp1)
          (let ((ty1 (type-of exp1 tenv)))
            (check-equal-type! ty1 (int-type) exp1)
            (bool-type)))
        (if-exp (exp1 exp2 exp3)
          (let ((ty1 (type-of exp1 tenv)))
            (check-equal-type! ty1 (bool-type) exp1)
            (let ((ty2 (type-of exp2 tenv))
                  (ty3 (type-of exp3 tenv)))
              (check-equal-type! ty2 ty3 exp)
              ty2)))
        (let-exp (lovar loexp body)
          (let ((lotype (map (lambda (exp1) (type-of exp1 tenv)) loexp)))
            (type-of body (extend-tenv lovar lotype tenv))))
        (letmutable-exp (lovar loexp body)
          (let ((lotype (map (lambda (exp1) (type-of exp1 tenv)) loexp)))
            (type-of body (extend-tenv lovar lotype tenv))))
        (proc-exp (lovar lovar-type body)
          (let ((result-type
                  (type-of body
                    (extend-tenv lovar lovar-type tenv))))
            (proc-type lovar-type result-type)))
        (call-exp (rator lorand)
          (let ((rator-type (type-of rator tenv))
                (lorand-type (map (lambda (exp1) (type-of exp1 tenv)) lorand)))
            (cases type rator-type
              (proc-type (loarg-type result-type)
                (if (not (equal? (length loarg-type) (length lorand-type)))
                  (report-wrong-number-of-arguments
                    (map type-to-external-form loarg-type)
                    (map type-to-external-form lorand-type)
                    exp)
                  (begin
                    (for-each check-equal-type! loarg-type lorand-type lorand)
                    result-type)))
              (else
                (report-rator-not-a-proc-type rator-type exp)))))
        (letrec-exp (lop-result-type lop-name lob-vars lob-var-types lop-body letrec-body)
          (let ((tenv-for-letrec-body
                  (extend-tenv lop-name
                    (conjugate2 (lambda (loarg-type result-type) (proc-type loarg-type result-type)) lob-var-types lop-result-type)
                    tenv)))
            (let ((lop-body-type
                    (conjugate3
                      (lambda (p-body lob-var lob-var-type)
                        (type-of p-body
                           (extend-tenv lob-var lob-var-type
                             tenv-for-letrec-body)))
                      lop-body lob-vars lob-var-types)))
              (check-all lop-body-type lop-result-type lop-body)
              (type-of letrec-body tenv-for-letrec-body))))
        (assign-exp (var exp1)
          (let ((ty1 (type-of exp1 tenv)))
            (check-equal-type! ty1 (apply-tenv tenv var) exp)
            (void-type)))
        (list-exp (exp1 loexp)
          (let type-of-rest ((ty1 (type-of exp1 tenv)) (loexp loexp))
            (if (null? loexp)
              (list-type ty1)
              (begin
                (check-equal-type! (type-of (car loexp) tenv) ty1 (car loexp))
                (type-of-rest ty1 (cdr loexp))))))
        (cons-exp (exp1 exp2)
          (let ((ty1 (type-of exp1 tenv))
                (ty2 (type-of exp2 tenv)))
            (cases type ty2
              (list-type (l-type)
                (begin
                  (check-equal-type! ty1 l-type exp1)
                  (list-type l-type)))
              (else
                (report-exp-not-a-list-type ty2 exp2)))))
        (null?-exp (exp1)
          (let ((ty1 (type-of exp1 tenv)))
            (cases type ty1
              (list-type (l-type)
                (bool-type))
              (else
                (report-exp-not-a-list-type ty1 exp1)))))
        (emptylist-exp (ty1)
          (list-type ty1))
        (car-exp (exp1)
          (let ((ty1 (type-of exp1 tenv)))
            (cases type ty1
              (list-type (l-type)
                l-type)
              (else
                (report-exp-not-a-list-type ty1 exp1)))))
        (cdr-exp (exp1)
          (let ((ty1 (type-of exp1 tenv)))
            (cases type ty1
              (list-type (l-type)
                ty1)
              (else
                (report-exp-not-a-list-type ty1 exp1))))))))
  ;;class-type? : Type -> Bool
  (define class-type?
    (lambda (ty)
      (cases type ty
        (class-type (c-name) #t)
        (else #f))))
  ;;type->class-name : Type -> ClassName
  (define type->class-name
    (lambda (obj-type)
      (cases type obj-type
        (class-type (c-name) c-name)
        (else (report-not-a-class-type obj-type)))))
  ;;report-not-a-class-type
  (define report-not-a-class-type
    (lambda (ty)
      (eopl:error 'report-not-a-class-type "type ~s is not a class type~%" ty)))
  ;;report-bad-type-to-instanceof: Type × Exp -> Unspecified
  (define report-bad-type-to-instanceof
    (lambda (obj-type obj-exp)
      (eopl:error 'report-bad-type-to-instanceof "exp ~s has type ~s which is a bad type to instanceof~%" obj-exp obj-type)))
  ;;report-bad-class-to-instanceof
  (define report-bad-class-to-instanceof
    (lambda (c-name)
      (eopl:error 'report-bad-class-to-instanceof "can't find class name ~s in the-static-class-env for instanceof exp" c-name)))
  ;;report-cant-instantiate-interface
  (define report-cant-instantiate-interface
    (lambda (c-name)
      (eopl:error 'report-cant-instantiate-interface "can't initialize an interface ~s~%" c-name)))
  ;;report-bad-type-to-cast: Type × Exp -> Unspecified
  (define report-bad-type-to-cast
    (lambda (obj-type obj-exp)
      (eopl:error 'report-bad-type-to-cast "exp ~s has type ~s which is a bad type to cast~%" obj-exp obj-type)))
  ;;report-bad-class-to-cast
  (define report-bad-class-to-cast
    (lambda (c-name)
      (eopl:error 'report-bad-class-to-cast "can't find class name ~s in the-static-class-env for cast exp" c-name)))
  ;;report-exp-not-a-list-type : type × exp -> undefined
  (define report-exp-not-a-list-type
    (lambda (type exp)
      (eopl:error 'report-exp-not-a-list-type "exp ~s has type: ~s which should be list-type~%" exp (type-to-external-form type))))  
  ;;report-exp-not-a-pair-type : type × exp -> undefined
  (define report-exp-not-a-pair-type
    (lambda (type exp)
      (eopl:error 'report-exp-not-a-pair-type "exp ~s has type: ~s which should be pair-type~%" exp (type-to-external-form type))))
  ;;report-rator-not-a-proc-type : type × exp -> undefined
  (define report-rator-not-a-proc-type
    (lambda (type exp)
      (eopl:error 'report-rator-not-a-proc-type "expression ~s rator type: ~s which should be proc-type~% " exp (type-to-external-form type))))
  ;;conjugate2 : Proc × List × List -> List
  (define conjugate2
    (lambda (proc lst1 lst2)
      (cond
        ((and (null? lst1) (null? lst2)) '())
        (else
         (cons (proc (car lst1) (car lst2)) (conjugate2 proc (cdr lst1) (cdr lst2)))))))
   ;;conjugate3 : Proc × List × List × List-> List
  (define conjugate3
    (lambda (proc lst1 lst2 lst3)
      (cond
        ((and (null? lst1) (null? lst2) (null? lst3)) '())
        (else
         (cons (proc (car lst1) (car lst2) (car lst3)) (conjugate3 proc (cdr lst1) (cdr lst2) (cdr lst3)))))))
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

