#lang eopl
(require "cha1.rkt")
(define eqlist?
  (lambda (l1 l2)
    (cond
      ((and (null? l1) (null? l2)) #t)
      ((or (null? l1) (null? l2)) #f)
      ((and (atom? (car l1)) (atom? (car l2)))
       (and (eq? (car l1) (car l2)) (eqlist? (cdr l1) (cdr l2))))
      ((or (atom? (car l1)) (atom? (car l2)))
       #f)
      (else
       (and (eqlist? (car l1) (car l2)) (eqlist? (cdr l1) (cdr l2)))))))
(define zero
  (lambda ()
    '()))
(define is-zero?
  (lambda (n)
    (null? n)))
(define base 64)
(define report-negative-values
  (lambda (n)
    (eopl:error 'predecessor "negative values ~s" n)))
(define successor
  (lambda (n)
    (cond
      ((< (car n) (- base 1)) (cons (+ (car n) 1) (cdr n)))
      (else
       (cond
         ((null? (cdr n)) '(0 1))
         (else (cons 0 (successor (cdr n)))))))))
(define predecessor
    (lambda (n)
      (cond
        ((eqlist? n '(1)) '())
        ((> (car n) 0) (cons (- (car n) 1) (cdr n)))
        (else (cons (- base 1) (predecessor (cdr n)))))))
(define plus
  (lambda (x y)
    (cond
      ((is-zero? x) y)
      (else (successor (plus (predecessor x) y))))))
(define multiply
  (lambda (x y)
    (cond
      ((or (is-zero? x) (is-zero? y)) '())
      (else (plus (multiply (predecessor x) y) y)))))
(define rev-car
  (lambda (lst)
    (car (reverse lst))))
(define rev-cdr
  (lambda (lst)
    (reverse (cdr (reverse lst)))))
(define greater-than
  (lambda (x y)
    (cond
      ((eqlist? x y) #f)
      ((is-zero? x) #f)
      ((is-zero? y) #t)
      ((not(eq? (length x) (length y))) (> (length x) (length y)))
      ((not(eq? (rev-car x) (rev-car y))) (> (rev-car x) (rev-car y)))
      (else (greater-than (rev-cdr x) (rev-cdr y))))))
(define factorial
  (lambda (n)
    (cond
      ((eqlist? n '(1)) '(1))
      (else (multiply n (factorial (predecessor n)))))))
(define (fact-iter product counter max-count)
  (if (greater-than counter max-count)
      product
     (fact-iter (multiply counter product) (successor counter) max-count)))
(define (new-factorial n)(fact-iter '(1) '(1) n))

;;exercise 2.5
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
  (lambda (var val env)
    (list (list var val) env)))
(define apply-env
  (lambda (env search-var)
    (cond
      ((null? env)
       (report-no-binding-found search-var))
      (else
       (let ((saved-var (caar env))
             (saved-val (cadar env))
             (saved-env (cadr env)))
         (cond
           ((eq? search-var saved-var) saved-val)
           (else (apply-env saved-env search-var))))))))
(define empty-env?
  (lambda (env)
    (null? env)))
(define has-binding?
  (lambda (env s)
    (cond
      ((null? env) #f)
      (else
       (let ((saved-var (caar env))
             (saved-val (cadar env))
             (saved-env (cadr env)))
         (cond
           ((eq? s saved-var) #t)
           (else (has-binding? saved-env s))))))))

;;exercise 2.11
(define extend-env*
  (lambda (vars vals env)
    (cond
      ((and (atom? vars) (atom? vals)) (list (list (cons vars '()) (cons vals '())) env))
      (else (list (list vars vals) env)))))
(define empty-env* empty-env)
(define empty-env*? empty-env?)
;; member?: Symbol * list -> Boolean
(define member?
  (lambda (s lst)
    (cond
      ((null? lst) #f)
      (else
       (cond
         ((eq? s (car lst)) #t)
         (else (member s (cdr lst))))))))
(define index-from
  (lambda (s lst n)
    (cond
      ((null? lst) 0)
      (else
       (cond
         ((eq? s (car lst)) n)
         (else (index-from s (cdr lst) (+ n 1))))))))
(define index
  (lambda (s lst)
    (index-from s lst 1)))
(define pick
  (lambda (n lst)
    (cond
      ((zero? (- n 1)) (car lst))
      (else (pick (- n 1) (cdr lst))))))
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
(define report-no-binding-found*
  (lambda (search-var)
    (eopl:error 'apply-env* "No binding for ~s" search-var)))
(define apply-env*
  (lambda (env s)
    (cond
      ((null? env)
       (report-no-binding-found* s))
      (else
       (let ((saved-vars (caar env))
             (saved-vals (cadar env))
             (saved-env (cadr env)))
         (cond
           ((member? s saved-vars) (pick (index s saved-vars) saved-vals))
           (else (apply-env* saved-env s))))))))

;;exercise 2.13
(define empty-env-p
  (lambda ()
    (list
     (lambda (search-var)
       (report-no-binding-found search-var))
     (lambda ()
       #t)
     (lambda (search-var)
       #f))))
(define extend-env-p
  (lambda (saved-var saved-val saved-env)
    (list
     (lambda (search-var)
       (if (eqv? search-var saved-var)
         saved-val
         (apply-env-p saved-env search-var)))
     (lambda ()
       #f)
     (lambda (search-var)
       (if (eqv? search-var saved-var)
         #t
         (has-binding-p? saved-env search-var))))))
(define apply-env-p
  (lambda (env search-var)
    ((pick 1 env) search-var)))
(define empty-env-p?
  (lambda (env)
    ((pick 2 env))))
(define has-binding-p?
  (lambda (env search-var)
    ((pick 3 env) search-var)))

;;exercise 2.15
(define var-exp
  (lambda (var)
    var))
(define lambda-exp
  (lambda (var exp)
    (list 'lambda (list var) exp)))
(define app-exp
  (lambda (exp1 exp2)
    (list exp1 exp2)))
(define var-exp?
  (lambda (exp)
    (atom? exp)))
(define lambda-exp?
  (lambda (exp)
    (cond
      ((var-exp? exp) #f)
      (else
       (eq? (car exp) 'lambda)))))
(define app-exp?
  (lambda (exp)
    (cond
      ((var-exp? exp) #f)
      ((lambda-exp? exp) #f)
      (else #t))))
(define var-exp->var
  (lambda (exp)
    exp))
(define lambda-exp->bound-var
  (lambda (exp)
    (caadr exp)))
(define lambda-exp->body
  (lambda (exp)
    (caddr exp)))
(define app-exp->rator
  (lambda (exp)
    (car exp)))
(define app-exp->rand
  (lambda (exp)
    (cadr exp)))
(define occurs-free?
  (lambda (search-var exp)
    (cond
      ((var-exp? exp) (eqv? search-var (var-exp->var exp)))
      ((lambda-exp? exp)
       (and
         (not (eqv? search-var (lambda-exp->bound-var exp)))
         (occurs-free? search-var (lambda-exp->body exp))))
    (else
      (or
        (occurs-free? search-var (app-exp->rator exp))
        (occurs-free? search-var (app-exp->rand exp)))))))

;;exercise 2.18
(define make-seq
  (lambda (n loi1 loi2)
    (list n loi1 loi2)))
(define current-node
  (lambda (seq)
    (car seq)))
(define before-loi
  (lambda (seq)
    (cadr seq)))
(define after-loi
  (lambda (seq)
    (caddr seq)))
(define number->sequence
  (lambda (n)
    (make-seq n '() '())))
(define current-number current-node)
(define report-current-number-is-at-left-end
  (lambda (n)
    (eopl:error 'move-to-left "current num ~s is at left end of the sequence" n)))
(define report-current-number-is-at-right-end
  (lambda (n)
    (eopl:error 'move-to-right "current num ~s is at right end of the sequence" n)))
(define move-to-left
  (lambda(seq)
    (cond
      ((null? (before-loi seq)) (report-current-number-is-at-left-end (current-number seq)))
      (else
       (let ((n (car (before-loi seq)))
             (bloi (cdr (before-loi seq)))
             (aloi (cons (current-number seq) (after-loi seq))))
         (make-seq n bloi aloi))))))
(define move-to-right
  (lambda(seq)
    (cond
      ((null? (after-loi seq)) (report-current-number-is-at-right-end (current-number seq)))
      (else
       (let ((n (car (after-loi seq)))
             (bloi (cons (current-number seq) (before-loi seq)))
             (aloi (cdr (after-loi seq))))
         (make-seq n bloi aloi))))))
(define insert-to-left
  (lambda (n seq)
    (make-seq (current-number seq) (cons n (before-loi seq)) (after-loi seq))))
(define insert-to-right
  (lambda (n seq)
    (make-seq (current-number seq) (before-loi seq) (cons n (after-loi seq)))))

(provide (all-defined-out))

