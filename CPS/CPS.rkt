(module CPS
  (lib "eopl.ss" "eopl")
;;remove-first : Sym × Listof(Sym) -> Listof(Sym)
  (define remove-first
    (lambda (s los)
      (if (null? los)
        '()
        (if (eqv? (car los) s)
          (cdr los)
          (cons (car los) (remove-first s (cdr los)))))))
;;occurs-free? : Sym × LcExp -> Bool
  (define occurs-free?
    (lambda (var exp)
      (cond
        ((symbol? exp) (eqv? var exp))
        ((eqv? (car exp) 'lambda)
         (and
           (not (eqv? var (car (cadr exp))))
           (occurs-free? var (caddr exp))))
        (else
         (or
           (occurs-free? var (car exp))
           (occurs-free? var (cadr exp)))))))
;;list-sum : Listof(Int) -> Int
  (define list-sum
    (lambda (loi)
      (if (null? loi)
        0
        (+ (car loi)
           (list-sum (cdr loi))))))
;;subst : Sym × Sym × S-list -> S-list
  (define subst
    (lambda (new old slist)
      (if (null? slist)
        '()
        (cons
          (subst-in-s-exp new old (car slist))
          (subst new old (cdr slist))))))
;;subst-in-s-exp : Sym × Sym × S-exp -> S-exp
  (define subst-in-s-exp
    (lambda (new old sexp)
      (if (symbol? sexp)
        (if (eqv? sexp old) new sexp)
        (subst new old sexp))))

;;;;;;;;;;;;;;;;;;;;;CPS;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (define listorsym?
    (lambda (v)
      (or
        (symbol? v)
        (list? v))))
  (define-datatype continuation continuation?
    (end-cont)
    (remove-first-cont
     (s symbol?)
     (cont continuation?))
    (occurs-free1-cont
     (var symbol?)
     (arg symbol?)
     (cont continuation?))
    (occurs-free2-cont
     (var symbol?)
     (exp listorsym?)
     (cont continuation?))
    (occurs-free3-cont
     (val1 boolean?)
     (cont continuation?))
    (list-sum-cont
     (n number?)
     (cont continuation?))
    (subst1-cont
     (new symbol?)
     (old symbol?)
     (slist list?)
     (cont continuation?))
    (subst2-cont
     (val listorsym?)
     (cont continuation?)))
  (define apply-cont
    (lambda (cont val)
      (cases continuation cont
        (end-cont ()
          (begin
            (eopl:printf "End of computation.~%")
            (eopl:printf "This sentence should appear only once.~%")
            val))
        (remove-first-cont (s saved-cont)
          (apply-cont saved-cont (cons s val)))
        (occurs-free1-cont (var arg saved-cont)
          (apply-cont saved-cont
            (and
              (not (eqv? var arg))
               val)))
        (occurs-free2-cont (var exp saved-cont)
          (occurs-free?/k var exp (occurs-free3-cont val saved-cont)))
        (occurs-free3-cont (val1 saved-cont)
          (apply-cont saved-cont (or val1 val)))
        (list-sum-cont (n saved-cont)
          (apply-cont saved-cont (+ n val)))
        (subst1-cont (new old slist saved-cont)
          (subst/k new old slist (subst2-cont val saved-cont)))
        (subst2-cont (val1 saved-cont)
          (apply-cont saved-cont (cons val1 val))))))
  
  (define remove-first/k
    (lambda (s los cont)
      (if (null? los)
        (apply-cont cont '())
        (if (eqv? (car los) s)
          (apply-cont cont (cdr los))
          (remove-first/k s (cdr los) (remove-first-cont (car los) cont))))))
  (define remove-first*
    (lambda (s los)
      (remove-first/k s los (end-cont))))
  
  (define occurs-free?/k
    (lambda (var exp cont)
      (cond
        ((symbol? exp) (apply-cont cont (eqv? var exp)))
        ((eqv? (car exp) 'lambda)
         (occurs-free?/k var (caddr exp) (occurs-free1-cont var (caadr exp) cont)))
        (else
         (occurs-free?/k var (car exp) (occurs-free2-cont var (cadr exp) cont))))))
  (define occurs-free?*
    (lambda (var exp)
      (occurs-free?/k var exp (end-cont))))

  (define list-sum/k
    (lambda (loi cont)
      (if (null? loi)
        (apply-cont cont 0)
        (list-sum/k (cdr loi) (list-sum-cont (car loi) cont)))))
  (define list-sum*
    (lambda (loi)
      (list-sum/k loi (end-cont))))

  (define subst/k
    (lambda (new old slist cont)
      (if (null? slist)
        (apply-cont cont '())
        (subst-in-s-exp/k new old (car slist) (subst1-cont new old (cdr slist) cont)))))
  (define subst-in-s-exp/k
    (lambda (new old sexp cont)
      (if (symbol? sexp)
        (if (eqv? sexp old)
          (apply-cont cont new)
          (apply-cont cont sexp))
        (subst/k new old sexp cont))))
  (define subst*
    (lambda (new old slist)
      (subst/k new old slist (end-cont))))

;;;;succinct representation of the continuation
  (define apply-cont*
    (lambda (cont val)
      (+ cont val)))
  (define end-cont*
    (lambda ()
      0))
  (define list-sum-cont*
    (lambda (n cont)
      (+ cont n)))
  (define list-sum/k*
    (lambda (loi cont)
      (if (null? loi)
        (apply-cont* cont 0)
        (list-sum/k* (cdr loi) (list-sum-cont* (car loi) cont)))))
  (define list-sum**
    (lambda (loi)
      (list-sum/k* loi (end-cont*))))
)