(module INFERRED
(lib "eopl.ss" "eopl")
(require "../cha1.rkt")
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
    '((program (expression) a-program)
      
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
       ("proc" "(" (arbno identifier optional-type-2) ")" expression)
       proc-exp)

      (expression
       ("(" expression (arbno expression) ")")
       call-exp)

      (expression
       ("letrec" (arbno optional-type identifier "(" (arbno identifier optional-type-2) ")" "=" expression) "in" expression)
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
       ("emptylist" optional-type-3)
       emptylist-exp)

      (expression
       ("car" "(" expression ")")
       car-exp)
      
      (expression
       ("cdr" "(" expression ")")
       cdr-exp)

      (optional-type
       ()
       no-type)

      (optional-type
       (type)
       a-type)

      (optional-type-2
       ()
       no-type-2)
      
      (optional-type-2
       (":" type)
       a-type-2)
      
      (optional-type-3
       ()
       no-type-3)
      
      (optional-type-3
       ("_" type)
       a-type-3)
      
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
       ("%tvar-type" number)
       tvar-type)
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
     (env type-environment?)))
  (define apply-tenv
    (lambda (env search-var)
      (cases type-environment env
        (empty-tenv ()
          (eopl:error 'apply-tenv "Unbound variable ~s" search-var))
        (extend-tenv (saved-vars saved-types saved-env)
          (let ((i (index search-var saved-vars)))
            (if (not (zero? i))
              (pick i saved-types)
                (apply-tenv saved-env search-var)))))))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;substitution implementation;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;apply-one-subst : Type × Tvar × Type -> Type
  (define apply-one-subst
    (lambda (ty0 tvar ty1)
      (cases type ty0
        (int-type () (int-type))
        (bool-type () (bool-type))
        (proc-type (loarg-type result-type)
          (proc-type
            (map (lambda (arg-type) (apply-one-subst arg-type tvar ty1)) loarg-type)
            (apply-one-subst result-type tvar ty1)))
        (pair-type (ty2 ty3)
          (pair-type
             (apply-one-subst ty2 tvar ty1)
             (apply-one-subst ty3 tvar ty1)))
        (list-type (ty)
          (list-type (apply-one-subst ty tvar ty1)))
        (tvar-type (num)
          (if (equal? ty0 tvar) ty1 ty0)))))
  ;;;;;;;;;;;;;;;;substitution obserber;;;;;;;;;;;;;;;;;;;
  ;;apply-subst-to-type :  Type × Subst → Type
  ;;(define apply-subst-to-type
  ;;  (lambda (ty subst)
  ;;    (cases type ty
  ;;      (int-type () (int-type))
  ;;      (bool-type () (bool-type))
  ;;      (proc-type (loarg-type result-type)
  ;;        (proc-type
  ;;          (map (lambda (arg-type) (apply-subst-to-type arg-type subst)) loarg-type)
  ;;          (apply-subst-to-type result-type subst)))
  ;;      (pair-type (ty1 ty2)
  ;;        (pair-type
  ;;          (apply-subst-to-type ty1 subst)
  ;;          (apply-subst-to-type ty2 subst)))
  ;;      (list-type (ty1)
  ;;        (list-type (apply-subst-to-type ty1 subst)))
  ;;      (tvar-type (num)
  ;;        (let ((tmp (assoc ty subst)))
  ;;          (if tmp
  ;;            ;;(cdr tmp)
  ;;            (apply-subst-to-type (cdr tmp) subst)  ;;exercise 7.17
  ;;            ty))))))
  (define apply-subst-to-type
    (lambda (ty subst)
      (let ((col '()))
        (let apply-subst ((ty ty) (subst subst))
          (cases type ty
            (int-type () (int-type))
            (bool-type () (bool-type))
            (proc-type (loarg-type result-type)
              (proc-type
                (map (lambda (arg-type) (apply-subst arg-type subst)) loarg-type)
                (apply-subst result-type subst)))
            (pair-type (ty1 ty2)
              (pair-type
                (apply-subst ty1 subst)
                (apply-subst ty2 subst)))
            (list-type (ty1)
              (list-type (apply-subst ty1 subst)))
            (tvar-type (num)
              (let ((saved-type (assoc num col)))
                (if saved-type
                  (cdr saved-type)
                  (let ((tmp (assoc ty subst)))
                    (let ((result (if tmp (apply-subst (cdr tmp) subst) ty)))
                      (cons (cons num result) col)
                      result))))))))))
  ;;substitution? : Val -> Bool
  (define substitution?
    (lambda (v)
      ((list-of pair?) v)))
  ;;;;;;;;;;;;;;;;substitution constructor;;;;;;;;;;;;;;;;;;;
  ;;empty-subst : () -> Subst
  (define empty-subst
    (lambda () '()))
  ;;extend-subst : Subst × Tvar × Type -> Subst
  ;;(define extend-subst
  ;;  (lambda (subst tvar ty)
  ;;    (cons
  ;;      (cons tvar ty)
  ;;      (map
  ;;        (lambda (p)
  ;;          (let ((oldlhs (car p))
  ;;                (oldrhs (cdr p)))
  ;;            (cons
  ;;              oldlhs
  ;;              (apply-one-subst oldrhs tvar ty))))
  ;;        subst))))
  (define extend-subst
    (lambda (subst tvar ty)
      (cons (cons tvar ty) subst))) ;; be careful that (cons tvar ty) returns a pair not a list!!!
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;unifier;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;unifier : Type × Type × Subst × Exp -> Subst
  (define unifier
    (lambda (ty1 ty2 subst exp)
      (let ((ty1 (apply-subst-to-type ty1 subst))
            (ty2 (apply-subst-to-type ty2 subst)))
        (cond
          ((equal? ty1 ty2) subst)  ;;deep-equal?
          ((tvar-type? ty1)
           (if (no-occurrence? ty1 ty2)
             (extend-subst subst ty1 ty2)
             (report-no-occurrence-violation ty1 ty2 exp)))
          ((tvar-type? ty2)
           (if (no-occurrence? ty2 ty1)
             (extend-subst subst ty2 ty1)
             (report-no-occurrence-violation ty2 ty1 exp)))
          ((and (proc-type? ty1) (proc-type? ty2))
           (let unifier-for-proc
            ((loty1 (cons (proc-type->result-type ty1) (proc-type->loarg-type ty1)))
             (loty2 (cons (proc-type->result-type ty2) (proc-type->loarg-type ty2)))
             (subst subst)
             (exp exp))
             (if (and (null? loty1) (null? loty2))
               subst
               (let ((new-subst (unifier (car loty1) (car loty2) subst exp)))
                 (unifier-for-proc (cdr loty1) (cdr loty2) new-subst exp)))))
          ((and (pair-type? ty1) (pair-type? ty2))
           (let ((subst (unifier
                          (pair-type->first-type ty1)
                          (pair-type->first-type ty2)
                          subst exp)))
             (let ((subst (unifier
                           (pair-type->second-type ty1)
                           (pair-type->second-type ty2)
                           subst exp)))
               subst)))
          ((and (list-type? ty1) (list-type? ty2))
           (unifier (list-type->type ty1) (list-type->type ty2) subst exp))
          (else (report-unification-failure ty1 ty2 exp))))))
  ;;no-occurrence? : Tvar × Type -> Bool
  (define no-occurrence?
    (lambda (tvar ty)
      (cases type ty
        (int-type () #t)
        (bool-type () #t)
        (proc-type (loarg-type result-type)
          (and
            (no-occurrence-for-all? tvar loarg-type)
            (no-occurrence? tvar result-type)))
        (pair-type (ty1 ty2)
          (and
            (no-occurrence? tvar ty1)
            (no-occurrence? tvar ty2)))
        (list-type (ty)
          (no-occurrence? tvar ty))
        (tvar-type (serial-number) (not (equal? tvar ty))))))
  ;;no-occurrence-for-all? : Tvar × Listof(Type) -> Bool
  (define no-occurrence-for-all?
    (lambda (tvar loty)
      (cond
        ((eq? (length loty) 1) (no-occurrence? tvar (car loty)))
        ((no-occurrence? tvar (car loty)) (no-occurrence-for-all? tvar (cdr loty)))
        (else #f))))
  ;;tvar-type? : Type -> Bool
  (define tvar-type?
    (lambda (ty)
      (cases type ty
        (tvar-type (sn) #t)
        (else #f))))
  ;;proc-type? : Type -> Bool
  (define proc-type?
    (lambda (ty)
      (cases type ty
        (proc-type (loarg-type result-type) #t)
        (else #f))))
  ;;proc-type->loarg-type : Type -> Type
  (define proc-type->loarg-type
    (lambda (ty)
      (cases type ty
        (proc-type (loarg-type result-type) loarg-type)
        (else (eopl:error 'proc-type->loarg-type "~s is not a proc-type" ty)))))
  ;;proc-type->result-type : Type -> Type
  (define proc-type->result-type
    (lambda (ty)
      (cases type ty
        (proc-type (loarg-type result-type) result-type)
        (else (eopl:error 'proc-type->result-type "~s is not a proc-type" ty)))))
  ;;pair-type? : Type -> Bool
  (define pair-type?
    (lambda (ty)
      (cases type ty
        (pair-type (ty1 ty2) #t)
        (else #f))))
  ;;pair-type->first-type : Type -> Type
  (define pair-type->first-type
    (lambda (ty)
      (cases type ty
        (pair-type (ty1 ty2) ty1)
        (else (eopl:error 'pair-type->first-type "~s is not a pair-type" ty)))))
  ;;pair-type->second-type : Type -> Type
  (define pair-type->second-type
    (lambda (ty)
      (cases type ty
        (pair-type (ty1 ty2) ty2)
        (else (eopl:error 'pair-type->first-type "~s is not a pair-type" ty)))))
  ;;list-type? : Type -> Bool
  (define list-type?
    (lambda (ty)
      (cases type ty
        (list-type (ty1) #t)
        (else #f))))
  ;;list-type->type : Type -> Type
  (define list-type->type
    (lambda (ty)
      (cases type ty
        (list-type (ty1) ty1)
        (else (eopl:printf 'list-type->type "~s is not a list-type" ty)))))
  ;;report-no-occurrence-violation : Type × Type × Exp -> Unspecified
  (define report-no-occurrence-violation
    (lambda (ty1 ty2 exp)
      (eopl:error 'report-no-occurrence-violation "adding ~s = ~s which arises from ~s vioates the no-occurrence invariant" ty1 ty2 exp)))
  ;;report-unification-failure : Type × Type × Exp -> Unspecified
  (define report-unification-failure
    (lambda (ty1 ty2 exp)
      (eopl:error 'report-unification-failure "adding ~s = ~s which arises from ~s failure" ty1 ty2 exp)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;type-of;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;optype->type : OptionalType -> Type
  (define optype->type
    (lambda (otype)
      (cases optional-type otype
        (no-type () (fresh-tvar-type))
        (a-type (ty) ty))))
  ;;optype2->type : OptionalType2 -> Type
  (define optype2->type
    (lambda (otype)
      (cases optional-type-2 otype
        (no-type-2 () (fresh-tvar-type))
        (a-type-2 (ty) ty))))
  ;;optype3->type : OptionalType3 -> Type
  (define optype3->type
    (lambda (otype)
      (cases optional-type-3 otype
        (no-type-3 () (fresh-tvar-type))
        (a-type-3 (ty) ty))))
  ;;fresh-tvar-type : () → Type
(define fresh-tvar-type
  (let ((sn 0))
    (lambda ()
      (set! sn (+ sn 1))
      (tvar-type sn))))
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
        (tvar-type (sn)
          (string->symbol
            (string-append
              "ty"
              (number->string sn)))))))
  ;;insertSym : Sym × List -> List
  (define insertSym
    (lambda (sym lst)
      (cond
        ((or (null? lst) (eq? (length lst) 1)) lst)
        (else (cons (car lst) (cons sym (insertSym sym (cdr lst))))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;type-of-program;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;Answer = Type × Subst
  (define-datatype answer answer?
    (an-answer
      (ty type?)
      (subst substitution?)))
  ;;run : String -> Type
  (define run
    (lambda (string)
      (type-of-program (scan&parse string))))
  ;;type-of-program : Program -> Type
  (define type-of-program
    (lambda (pgm)
      (cases program pgm
        (a-program (exp1)
          (cases answer (type-of exp1 (init-tenv) (empty-subst))
            (an-answer (ty subst)
              (eopl:printf "answer:~%type:~s~%subst:~s~%" ty subst)
              (type-to-external-form (apply-subst-to-type ty subst))))))))
  ;;type-of :  Exp × Tenv × Subst -> Answer
  (define type-of
    (lambda (exp tenv subst)
      (cases expression exp
        (const-exp (num) (an-answer (int-type) subst))
        (var-exp (var) (an-answer (apply-tenv tenv var) subst))
        (diff-exp (exp1 exp2)
          (cases answer (type-of exp1 tenv subst)
            (an-answer (ty1 subst1)
              (let ((subst1 (unifier ty1 (int-type) subst1 exp1)))
                (cases answer (type-of exp2 tenv subst1)
                  (an-answer (ty2 subst2)
                    (let ((subst2 (unifier ty2 (int-type) subst2 exp2)))
                      (an-answer (int-type) subst2))))))))
        (zero?-exp (exp1)
          (cases answer (type-of exp1 tenv subst)
            (an-answer (ty1 subst1)
              (let ((subst2
                (unifier ty1 (int-type) subst1 exp)))
                  (an-answer (bool-type) subst2)))))
        (if-exp (exp1 exp2 exp3)
          (cases answer (type-of exp1 tenv subst)
            (an-answer (ty1 subst)
              (let ((subst (unifier ty1 (bool-type) subst exp1)))
                (cases answer (type-of exp2 tenv subst)
                  (an-answer (ty2 subst)
                    (cases answer (type-of exp3 tenv subst)
                      (an-answer (ty3 subst)
                        (let ((subst (unifier ty2 ty3 subst exp)))
                          (an-answer ty2 subst))))))))))
        (let-exp (lovar loexp body)
          (let type-of-let-exp ((loexp loexp) (subst subst) (lotype '()))
            (if (null? loexp)
              (type-of body (extend-tenv lovar (reverse lotype) tenv) subst)
              (cases answer (type-of (car loexp) tenv subst)
                (an-answer (exp-type new-subst)
                  (type-of-let-exp (cdr loexp) new-subst (cons exp-type lotype)))))))       
        (proc-exp (lovar lootype2 body)
          (let ((lovar-type (map optype2->type lootype2)))
            (cases answer (type-of body (extend-tenv lovar lovar-type tenv) subst)
              (an-answer (body-type subst)
                (an-answer
                  (proc-type lovar-type body-type)
                  subst)))))
        (call-exp (rator lorand)
          (let ((result-type (fresh-tvar-type)))
            (cases answer (type-of rator tenv subst)
              (an-answer (rator-type subst)
                (let type-of-lorand ((lorand lorand) (subst subst) (lorand-type '()))
                  (if (null? lorand)
                    (let ((subst (unifier rator-type (proc-type (reverse lorand-type) result-type) subst exp)))
                      (an-answer result-type subst))
                    (cases answer (type-of (car lorand) tenv subst)
                      (an-answer (rand-type new-subst)
                        (type-of-lorand (cdr lorand) new-subst (cons rand-type lorand-type))))))))))
        (letrec-exp (lop-result-otype lop-name lob-vars lob-var-otypes lop-body letrec-body)
          (let ((lop-result-type (map optype->type lop-result-otype))
                (lob-var-types (map (lambda (b-var-otypes) (map optype2->type b-var-otypes)) lob-var-otypes)))
            (let ((tenv-for-letrec-body
                   (extend-tenv lop-name
                      (conjugate2 (lambda (arg-types result-type) (proc-type arg-types result-type)) lob-var-types lop-result-type)
                      tenv)))
              (let type-of-lop-body ((lop-body lop-body) (lob-vars lob-vars) (lob-var-types lob-var-types) (lop-result-type lop-result-type) (subst subst))
                (if (null? lop-body)
                  (type-of letrec-body tenv-for-letrec-body subst)
                  (cases answer (type-of (car lop-body) (extend-tenv (car lob-vars) (car lob-var-types) tenv-for-letrec-body) subst)
                    (an-answer (p-body-type subst)
                      (let ((subst (unifier p-body-type (car lop-result-type) subst (car lop-body))))
                        (type-of-lop-body (cdr lop-body) (cdr lob-vars) (cdr lob-var-types) (cdr lop-result-type) subst)))))))))
        (pair-exp (exp1 exp2)
          (cases answer (type-of exp1 tenv subst)
            (an-answer (ty1 subst)
              (cases answer (type-of exp2 tenv subst)
                (an-answer (ty2 subst)
                  (an-answer (pair-type ty1 ty2) subst))))))
        (unpair-exp (var1 var2 p-exp body)
          (let ((first-type (fresh-tvar-type))
                (second-type (fresh-tvar-type)))
            (cases answer (type-of p-exp tenv subst)
              (an-answer (p-type subst)
                (let ((subst (unifier p-type (pair-type first-type second-type) subst p-exp)))
                  (type-of body (extend-tenv (list var1 var2) (list first-type second-type) tenv) subst))))))
        (list-exp (exp1 loexp)
          (cases answer (type-of exp1 tenv subst)
            (an-answer (ty1 subst)
              (let type-of-list-exp ((loexp loexp) (subst subst))
                (if (null? loexp)
                  (an-answer (list-type ty1) subst)
                  (cases answer (type-of (car loexp) tenv subst)
                    (an-answer (ty2 subst)
                      (let ((new-subst (unifier ty2 ty1 subst (car loexp))))
                        (type-of-list-exp (cdr loexp) new-subst)))))))))
        (cons-exp (exp1 exp2)
          (cases answer (type-of exp1 tenv subst)
            (an-answer (ty1 subst)
              (cases answer (type-of exp2 tenv subst)
                (an-answer (ty2 subst)
                  (let ((subst (unifier ty2 (list-type ty1) subst exp1)))
                    (an-answer ty2 subst)))))))
        (null?-exp (exp1)
          (let ((l-type (fresh-tvar-type)))
            (cases answer (type-of exp1 tenv subst)
              (an-answer (ty1 subst)
                (let ((subst (unifier ty1 (list-type l-type) subst exp1)))
                  (an-answer (bool-type) subst))))))
        (emptylist-exp (otype)
          (an-answer (list-type (optype3->type otype)) subst))
        (car-exp (exp1)
          (let ((l-type (fresh-tvar-type)))
            (cases answer (type-of exp1 tenv subst)
              (an-answer (ty1 subst)
                (let ((subst (unifier ty1 (list-type l-type) subst exp1)))
                  (an-answer l-type subst))))))
        (cdr-exp (exp1)
          (let ((l-type (fresh-tvar-type)))
            (cases answer (type-of exp1 tenv subst)
              (an-answer (ty1 subst)
                (let ((subst (unifier ty1 (list-type l-type) subst exp1)))
                  (an-answer (list-type l-type) subst)))))))))
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



