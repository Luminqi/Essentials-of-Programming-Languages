(module SIMPLE-MODULE
(lib "eopl.ss" "eopl")
(require "../cha1.rkt")
;;;;;;;;;;;;;lang;;;;;;;;;;;;;;;;;;;;;;
  (define the-lexical-spec
    '((whitespace (whitespace) skip)
      (comment ("%" (arbno (not #\newline))) skip)
      (module-ref
       (letter (arbno (or letter digit "_" "-" "?")) "." letter (arbno (or letter digit "_" "-" "?" ".")))
       symbol)
      (identifier
       (letter (arbno (or letter digit "_" "-" "?")))
       symbol)
      (number (digit (arbno digit)) number)
      (number ("-" digit (arbno digit)) number)
      ))
  
  (define the-grammar
    '((program
       ((arbno module-definition) expression)
       a-program)
      
      (module-definition
       ("module" identifier "interface" interface "body" (arbno module-definition) module-body)
       a-module-definition)

      (interface
       ("[" (arbno declaration) "]")
       simple-iface)
      
      (declaration
       (identifier ":" type)
       val-decl)

      (module-body
       ("["(arbno definition) "]")
       defns-module-body)

      (module-body
       ("let" (arbno identifier "=" expression) "in" module-body)
       let-module-body)

      (module-body
       ("letrec" (arbno type identifier "(" (arbno identifier ":" type) ")" "=" expression) "in" module-body)
       letrec-module-body)

      (definition
       (identifier "=" expression)
       val-defn)
      
      (expression (module-ref) qualified-var-exp)
      
      (expression (number) const-exp)
      
      (expression
        ("-" "(" expression "," expression ")")
        diff-exp)
            
      (expression
       ("zero?" "(" expression ")")
       zero?-exp)
      
      (expression
       ("if" expression "then" expression "else" expression)
       if-exp)

      (expression (identifier) var-exp)

      (expression
       ("let" (arbno identifier "=" expression) "in" expression)
       let-exp)

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
       ("newpair" "(" expression "," expression ")")
       pair-exp)
      
      (expression
       ("unpair" identifier identifier "=" expression "in" expression)
       unpair-exp)

      (expression
       ("list" "(" expression (arbno "," expression) ")")
       list-exp)

      (expression
       ("cons" "(" expression "," expression ")")
       cons-exp)

      (expression
       ("null?" "(" expression ")")
       null?-exp)

      (expression
       ("emptylist_" type)
       emptylist-exp)

      (expression
       ("car" "(" expression ")")
       car-exp)
      
      (expression
       ("cdr" "(" expression ")")
       cdr-exp)
      
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
       ("pairof" type "*" type)
       pair-type)

      (type
       ("listof" type)
       list-type)

      (type
       ("[" (arbno identifier ":" type) "]")
       iface-type)
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
  (define identifier?
    (lambda (s)
      (and (symbol? s) (not (eq? s 'lambda)))))
;;;;;;;;;;;;;;;;type-environment(abstract-syntax representation);;;;;;;;;;;;;;;;;;;;
  (define-datatype type-environment type-environment?
    (empty-tenv)
    (extend-tenv
     (vars (list-of identifier?))
     (types (list-of type?))
     (env type-environment?))
    (extend-tenv-with-module
     (name identifier?)
     (interface interface?)
     (saved-tenv type-environment?)))
  (define apply-tenv
    (lambda (env search-var)
      (cases type-environment env
        (empty-tenv ()
          (eopl:error 'apply-tenv "Unbound variable ~s in Tenv" search-var))
        (extend-tenv (saved-vars saved-types saved-env)
          (let ((i (index search-var saved-vars)))
            (if (not (zero? i))
              (pick i saved-types)
              (apply-tenv saved-env search-var))))
        (extend-tenv-with-module (m-name iface saved-env)
          (if (equal? search-var m-name)
            (cases interface iface
              (simple-iface (decls)
                (let ((lovar (map decl->name decls))
                      (loty (map decl->type decls)))
                  (iface-type lovar loty))))
            (apply-tenv saved-env search-var))))))
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
  ;;lookup-qualified-var-in-tenv : Sym × Sym × Tenv -> Type
  (define lookup-qualified-var-in-tenv
    (lambda (m-name var-name tenv)
      (let ((iface (lookup-module-name-in-tenv tenv m-name)))
        (cases interface iface
          (simple-iface (decls)
            (lookup-variable-name-in-decls var-name decls))))))
  ;;lookup-module-name-in-tenv : Tenv × Sym -> Interface
  (define lookup-module-name-in-tenv
    (lambda (tenv m-name)
      (cases type-environment tenv
        (empty-tenv ()
          (eopl:error 'lookup-module-name-in-tenv "can't find module ~s in tenv ~s" m-name tenv))
        (extend-tenv (vars types saved-tenv)
          (lookup-module-name-in-tenv saved-tenv m-name))
        (extend-tenv-with-module (name iface saved-tenv)
          (if (equal? name m-name)
            iface
            (lookup-module-name-in-tenv saved-tenv m-name))))))
  ;;lookup-variable-name-in-decls : Sym × Listof(Declaration) -> Type
  (define lookup-variable-name-in-decls
    (lambda (var-name decls)
      (if (null? decls)
        (eopl:error 'lookup-variable-name-in-decls "cant't find var ~s in decls ~s" var-name decls)
        (cases declaration (car decls)
          (val-decl (var type)
            (if (equal? var var-name)
              type
              (lookup-variable-name-in-decls var-name (cdr decls))))))))
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
        "Types didn’t match: ~s != ~a in~%~a"
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
              (list (type-to-external-form result-type)))))
        (pair-type (ty1 ty2)
          (list 'pairof
            (type-to-external-form ty1)
            (type-to-external-form ty2)))
        (list-type (ty1)
          (list 'listof (type-to-external-form ty1)))
        (iface-type (lovar loty)          
          (up
            (list
              'interface
              (insertSym '* lovar)
              ':
              (insertSym '* (map type-to-external-form loty))))))))
  ;;insertSym : Sym × List -> List
  (define insertSym
    (lambda (sym lst)
      (cond
        ((or (null? lst) (eq? (length lst) 1)) lst)
        (else (cons (car lst) (cons sym (insertSym sym (cdr lst))))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;type-of-program;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;type-of-program : Program -> Type
  (define type-of-program
    (lambda (pgm)
      (cases program pgm
        (a-program (module-defns body)
          (type-of body (add-module-defns-to-tenv module-defns (init-tenv)))))))
  ;;add-module-defns-to-tenv : Listof(ModuleDefn) × Tenv -> Tenv
  (define add-module-defns-to-tenv
    (lambda (defns tenv)
      (if (null? defns)
        tenv
        (cases module-definition (car defns)
          (a-module-definition (m-name expected-iface m-defns m-body)
            (if (m-name-not-include-in-tenv tenv m-name)
              (let ((actual-iface (interface-of m-body (add-module-defns-to-tenv m-defns tenv))))
                (if (<:-iface actual-iface expected-iface tenv)
                  (let ((new-tenv (extend-tenv-with-module m-name expected-iface tenv)))
                    (add-module-defns-to-tenv (cdr defns) new-tenv))
                  (report-module-doesnt-satisfy-iface m-name expected-iface actual-iface)))
              (report-duplicated-module-name m-name)))))))
  ;;m-name-not-include-in-tenv : Sym × Tenv -> Bool
  (define m-name-not-include-in-tenv
    (lambda (tenv m-name)
      (cases type-environment tenv
        (empty-tenv () #t)
        (extend-tenv (vars types saved-tenv)
          (m-name-not-include-in-tenv saved-tenv m-name))
        (extend-tenv-with-module (name iface saved-tenv)
          (if (equal? name m-name)
            #f
            (m-name-not-include-in-tenv saved-tenv m-name))))))
  ;;report-module-doesnt-satisfy-iface : Sym × Interface × Interface -> Unspecified
  (define report-module-doesnt-satisfy-iface
    (lambda (m-name expected-iface actual-iface)
      (eopl:error 'm-name expected-iface actual-iface "module ~s has interface ~s which not satisfy the expected interface ~s" m-name actual-iface expected-iface)))
  ;;report-duplicated-module-name : Sym -> Unspecified
  (define report-duplicated-module-name
    (lambda (m-name)
      (eopl:error 'report-duplicated-module-name "duplicated module name ~s" m-name)))
  ;;interface-of : ModuleBody × Tenv -> Iface
  (define interface-of
    (lambda (m-body tenv)
      (cases module-body m-body
        (defns-module-body (defns)
          (simple-iface (defns-to-decls defns tenv)))
        (let-module-body (lovar loexp new-m-body)
          (let ((lotype (map (lambda (exp1) (type-of exp1 tenv)) loexp)))
            (interface-of new-m-body (extend-tenv lovar lotype tenv))))
        (letrec-module-body (lop-result-type lop-name lob-vars lob-var-types lop-body new-m-body)
           (let ((tenv-for-new-m-body
                  (extend-tenv lop-name
                    (conjugate2 (lambda (loarg-type result-type) (proc-type loarg-type result-type)) lob-var-types lop-result-type)
                    tenv)))
            (let ((lop-body-type
                    (conjugate3
                      (lambda (p-body lob-var lob-var-type)
                        (type-of p-body
                           (extend-tenv lob-var lob-var-type
                             tenv-for-new-m-body)))
                      lop-body lob-vars lob-var-types)))
              (check-all lop-body-type lop-result-type lop-body)
              (interface-of new-m-body tenv-for-new-m-body)))))))
  ;;defns-to-decls :  Listof(Defn) × Tenv -> Listof(Decl)
  (define defns-to-decls
    (lambda (defns tenv)
      (if (null? defns)
        '()
        (cases definition (car defns)
          (val-defn (var-name exp)
            (let ((ty (type-of exp tenv)))
              (cons
                (val-decl var-name ty)
                (defns-to-decls (cdr defns) (extend-tenv (list var-name) (list ty) tenv)))))))))
  ;;<:-iface : Iface × Iface × Tenv -> Bool
  (define <:-iface
    (lambda (iface1 iface2 tenv)
      (cases interface iface1
        (simple-iface (decls1)
          (cases interface iface2
            (simple-iface (decls2)
              (<:-decls decls1 decls2 tenv)))))))
  ;;<:-decls : Listof(Decl) × Listof(Decl) × Tenv -> Bool
  (define <:-decls
    (lambda (decls1 decls2 tenv)
      (let loop ((decls1 decls1) (decls2 decls2) (tenv tenv) (cont '()))
        (cond
          ((null? decls2) #t)
          ((null? decls1) #f)
          (else
            (let ((name1 (decl->name (car decls1)))
                  (name2 (decl->name (car decls2))))
              (if (equal? name1 name2)
                (and
                  (equal? (decl->type (car decls1)) (decl->type (car decls2)))
                  (loop (append cont (cdr decls1)) (cdr decls2) tenv '()))
                (loop (cdr decls1) decls2 tenv (append cont (list (car decls1)))))))))))
  ;;decl->name : Decl -> Sym
  (define decl->name
    (lambda (decl)
      (cases declaration decl
        (val-decl (var type)
          var))))
   ;;decl->type : Decl -> Type
  (define decl->type
    (lambda (decl)
      (cases declaration decl
        (val-decl (var type)
          type))))
  ;;type-of : Exp × Tenv -> Type
  (define type-of
    (lambda (exp tenv)
      (cases expression exp
        (const-exp (num) (int-type))
        (var-exp (var) (apply-tenv tenv var))
        (diff-exp (exp1 exp2)
          (let ((ty1 (type-of exp1 tenv))
                (ty2 (type-of exp2 tenv)))
            (check-equal-type! ty1 (int-type) exp1)
            (check-equal-type! ty2 (int-type) exp2)
            (int-type)))
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
                (begin
                  (check-all loarg-type lorand-type lorand)
                  result-type))
              (else
                (report-rator-not-a-proc-type rator-type rator)))))
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
        (pair-exp (exp1 exp2)
          (let ((ty1 (type-of exp1 tenv))
                (ty2 (type-of exp2 tenv)))
            (pair-type ty1 ty2)))
        (unpair-exp (var1 var2 p-exp body)
          (let ((p-type (type-of p-exp tenv)))
            (cases type p-type
              (pair-type (ty1 ty2)
                (type-of body
                  (extend-tenv (list var1 var2) (list ty1 ty2) tenv)))
              (else
                (report-exp-not-a-pair-type p-type p-exp)))))
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
                (report-exp-not-a-list-type ty1 exp1)))))
        (qualified-var-exp (m-ref)
          (let ((m-strs (split "." (symbol->string m-ref))))
            (let ((m-name (string->symbol (car m-strs)))
                  (var-names (map string->symbol (cdr m-strs))))
              (let ((ty (lookup-qualified-var-in-tenv m-name (car var-names) tenv)))
                (let loop ((var-names (cdr var-names))
                           (ty ty))
                  (if (null? var-names)
                    ty
                    (cases type ty
                      (iface-type (lovar lotype)
                        (let ((i (index (car var-names) lovar)))
                          (if (not (zero? i))
                            (loop (cdr var-names) (pick i lotype))
                            (report-variable-not-in-export-module ty (car var-names)))))
                      (else report-not-a-iface-type ty)))))))))))
  ;;split : String * String -> Listof(String)
  (define split
    (lambda (str1 str2)
      (let loop ((separator (car (string->list str1)))
                 (lst (string->list str2))
                 (cont '()))
        (if (null? lst)
          (if (null? cont)
            '()
            (list (list->string cont)))
          (if (equal? (car lst) separator)
            (if (null? cont)
              (loop separator (cdr lst) '())
              (cons (list->string cont) (loop separator (cdr lst) '())))
            (loop separator (cdr lst) (append cont (list (car lst)))))))))
  ;;report-variable-not-in-export-module : Type × Sym -> Unspecified
  (define report-variable-not-in-export-module
    (lambda (type var)
      (eopl:error 'report-variable-not-in-export-module "variable ~s not in export-iface-type ~s" var (type-to-external-form type))))
  ;;report-not-a-iface-type : Type -> Unspecified
  (define report-not-a-iface-type
    (lambda (type)
      (eopl:error 'report-not-a-iface-type "~s is not a iface-type" (type-to-external-form type))))
  ;;report-exp-not-a-list-type : type × exp -> undefined
  (define report-exp-not-a-list-type
    (lambda (type exp)
      (eopl:error 'report-exp-not-a-list-type "exp ~s has type: ~s~% which should be list-type" exp (type-to-external-form type))))  
  ;;report-exp-not-a-pair-type : type × exp -> undefined
  (define report-exp-not-a-pair-type
    (lambda (type exp)
      (eopl:error 'report-exp-not-a-pair-type "exp ~s has type: ~s~% which should be pair-type" exp (type-to-external-form type))))
  ;;report-rator-not-a-proc-type : type × exp -> undefined
  (define report-rator-not-a-proc-type
    (lambda (type exp)
      (eopl:error 'report-rator-not-a-proc-type "rator ~s has type: ~s~% which should be proc-type" exp (type-to-external-form type))))
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
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;value-of section;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;;;;;;;;;;;;;;;;;;;;;;;;;;environment(abstract-syntax representation);;;;;;;;;;;;;;
  ;;;;;;;;;;;;;;;;;typed-module;;;;;;;;;;;;;;;;;;;;;;;;;
  (define-datatype typed-module typed-module?
    (simple-module
      (bindings environment?)))
  (define-datatype environment environment?
    (empty-env)
    (extend-env
     (vars (list-of identifier?))
     (vals (list-of expval?))
     (env environment?))
    (extend-env-rec
     (lop-name (list-of identifier?))
     (lob-vars (list-of (list-of identifier?)))
     (lobody (list-of expression?))
     (env environment?))
    (extend-env-with-module
     (m-name symbol?)
     (m-val typed-module?)
     (saved-env environment?)))
  (define apply-env
    (lambda (env search-var)
      (cases environment env
        (empty-env ()
          (eopl:error 'apply-env "Unbound variable ~s in env" search-var))
        (extend-env (saved-vars saved-vals saved-env)
          (let ((i (index search-var saved-vars)))
            (if (not (zero? i))
              (pick i saved-vals)
              (apply-env saved-env search-var))))
        (extend-env-rec (lop-name lob-vars lop-body saved-env)
          (let ((i (index search-var lop-name)))
            (if (not (zero? i))
              (proc-val (procedure (pick i lob-vars) (pick i lop-body) env))
              (apply-env saved-env search-var))))
        (extend-env-with-module (m-name m-val saved-env)
          (if (equal? search-var m-name)
            (module-val m-val)
            (apply-env saved-env search-var))))))
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
  ;;lookup-qualified-var-in-env : Sym × Sym × Env -> ExpVal
  (define lookup-qualified-var-in-env
    (lambda (m-name var-name env)
      (let ((m-val (lookup-module-name-in-env m-name env)))
        (cases typed-module m-val
          (simple-module (bindings)
            (apply-env bindings var-name))))))
  ;;lookup-module-name-in-env : Sym × Env -> TypedModule
  (define lookup-module-name-in-env
    (lambda (m-name env)
      (cases environment env
        (empty-env ()
          (eopl:error 'lookup-module-name-in-env "can't find module ~s in env ~s" m-name env))
        (extend-env-with-module (name m-val saved-env)
          (if (equal? name m-name)
            m-val
            (lookup-module-name-in-env m-name saved-env)))
        (extend-env (saved-vars saved-vals saved-env)
          (lookup-module-name-in-env m-name saved-env))
        (extend-env-rec (lop-name lob-vars lop-body saved-env)
          (lookup-module-name-in-env m-name saved-env)))))
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;value-of;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;curry2 : Func -> Func
  (define curry2
    (lambda (f)
      (lambda (arg1)
        (lambda (arg2)
          (f arg2 arg1)))))
  ;; value-of : Exp × Env -> Expval
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
        (zero?-exp (exp1)
          (let ((num (expval->num (value-of exp1 env))))
            (bool-val (zero? num))))
        (if-exp (exp1 exp2 exp3)
          (let ((val1 (value-of exp1 env)))
            (if (expval->bool val1)
              (value-of exp2 env)
              (value-of exp3 env))))
        (let-exp (lovar loexp body)
          (let ((loval (map ((curry2 value-of) env) loexp)))
            (value-of body (extend-env lovar loval env))))
        (proc-exp (lovar lovar-type body)
          (proc-val (procedure lovar body env)))
        (call-exp (rator lorand)
          (let ((proc (expval->proc (value-of rator env)))
                (loarg (map ((curry2 value-of) env) lorand)))
            (apply-procedure proc loarg)))
        (letrec-exp (lop-result-type lop-name lob-vars lob-var-types lop-body letrec-body)
          (value-of letrec-body (extend-env-rec lop-name lob-vars lop-body env)))
        (pair-exp (exp1 exp2)
          (let ((val1 (value-of exp1 env))
                (val2 (value-of exp2 env)))
            (pair-val (cons val1 val2))))
        (unpair-exp (var1 var2 p-exp body)
          (let ((pair (expval->pair (value-of p-exp env))))
            (value-of body
              (extend-env (list var1 var2) (list (car pair) (cdr pair)) env))))
        (list-exp (exp1 loexp)
          (list-val (map ((curry2 value-of) env) (cons exp1 loexp))))
        (cons-exp (exp1 exp2)
          (let ((val1 (value-of exp1 env))
                (val2 (value-of exp2 env)))
            (let ((list (expval->list val2)))
              (list-val (cons val1 list)))))
        (null?-exp (exp1)
          (let ((list (expval->list (value-of exp1 env))))
            (bool-val (null? list))))
        (car-exp (exp1)
          (car (expval->list (value-of exp1 env))))
        (cdr-exp (exp1)
          (let ((list (cdr (expval->list (value-of exp1 env)))))
            (list-val list)))
        (emptylist-exp (ty1) (list-val '()))
        (qualified-var-exp (m-ref)
          (let ((m-strs (split "." (symbol->string m-ref))))
            (let ((m-name (string->symbol (car m-strs)))
                  (var-names (map string->symbol (cdr m-strs))))
              (let ((val (lookup-qualified-var-in-env m-name (car var-names) env)))
                (let loop ((var-names (cdr var-names))
                           (val val))
                  (if (null? var-names)
                    val
                    (cases expval val
                      (module-val (module)
                        (cases typed-module module
                          (simple-module (bindings)
                            (loop (cdr var-names) (apply-env bindings (car var-names))))))
                      (else (report-val-not-a-module-val val))))))))))))
  ;;report-val-not-a-module-val : Expval -> Unspecified
  (define report-val-not-a-module-val
    (lambda (val)
      (eopl:error 'report-val-not-a-module-val "~s is not a module-val" val)))
  ;;value-of-program : Program -> ExpVal
  (define value-of-program
    (lambda (pgm)
      (cases program pgm
        (a-program (m-defns body)
          (value-of body
            (add-module-defns-to-env m-defns (init-env)))))))
  ;;add-module-defns-to-env : Listof(Defn) × Env -> Env
  (define add-module-defns-to-env
    (lambda (defns env)
      (if (null? defns)
        env
        (cases module-definition (car defns)
          (a-module-definition (m-name iface m-defns m-body)
            (add-module-defns-to-env
              (cdr defns)
              (extend-env-with-module m-name (value-of-module-body iface m-body (add-module-defns-to-env m-defns env)) env)))))))
  ;;value-of-module-body : ModuleBody × Env -> TypedModule
  (define value-of-module-body
    (lambda (iface m-body env)
      (cases module-body m-body
        (defns-module-body (defns)
          (simple-module
            (defns-to-env iface defns env)))
        (let-module-body (lovar loexp new-m-body)
          (let ((loval (map ((curry2 value-of) env) loexp)))
            (value-of-module-body iface new-m-body (extend-env lovar loval env))))
        (letrec-module-body (lop-result-type lop-name lob-vars lob-var-types lop-body new-m-body)
          (value-of-module-body iface new-m-body (extend-env-rec lop-name lob-vars lop-body env))))))
  ;;defns-to-env : Listof(Defn) × Env -> Env (let* scoping)
  (define defns-to-env
    (lambda (iface defns env)
      (if (null? defns)
        (empty-env)
        (cases definition (car defns)
          (val-defn (var exp)
            (let ((val (value-of exp env)))
              (let ((new-env (extend-env (list var) (list val) env)))
                (if (var-declared-in-interface iface var)
                  (extend-env (list var) (list val) (defns-to-env iface (cdr defns) new-env))
                  (defns-to-env iface (cdr defns) new-env)))))))))
  ;;var-declared-in-interface : Interface × Sym -> Bool
  (define var-declared-in-interface
    (lambda (iface var)
      (cases interface iface
        (simple-iface (decls)
          (let loop ((decls decls))
            (if (null? decls)
              #f
              (cases declaration (car decls)
                (val-decl (var-name type)
                  (if (equal? var var-name)
                    #t
                    (loop (cdr decls)))))))))))
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;data structures;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;;;;;;;;;;;;;;;;;;;;procedure datatype;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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
          (value-of body (extend-env lovar loval saved-env))))))
 ;;;;;;;;;;;;;;;;;;;;;;;expval datatype;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-datatype expval expval?
  (num-val
    (num number?))
  (bool-val
    (bool boolean?))
  (pair-val
    (pair pair?))
  (list-val
    (list list?))
  (proc-val
    (proc proc?))
  (module-val
    (module typed-module?)))
;;expval->module : Expval -> TypedModule
(define expval->module
  (lambda (val)
    (cases expval val
      (module-val (module) module)
      (else (report-expval-extractor-error 'module val)))))
;;expval->proc : Expval -> proc
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
;;expval->pair : ExpVal -> pair
(define expval->pair
  (lambda (val)
    (cases expval val
      (pair-val (pair) pair)
      (else (report-expval-extractor-error 'pair val)))))
;;expval->any : ExpVal -> List|Int|Bool|Proc
(define expval->any
  (lambda (val)
    (cases expval val
      (list-val (list) list)
      (num-val (num) num)
      (bool-val (bool) bool)
      (proc-val (proc) proc)
      (pair-val (pair) pair)
      (module-val (module) module)
      (else (report-expval-extractor-error 'any val)))))
(define report-expval-extractor-error
  (lambda (type val)
    (eopl:error 'report-expval-extractor-error "expect ~s, but reveived ~s" type val)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;run;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;run : String -> Type
  (define run
    (lambda (string)
      (begin
        (eopl:printf "Type: ~s~%" (type-to-external-form (type-of-program (scan&parse string))))
        (value-of-program (scan&parse string)))))
)



