#lang eopl
(require "cha1.rkt")
(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))
(define-datatype environment env?
  (empty-env)
  (extend-env
    (var symbol?)
    (val number?)
    (env env?)))
(define apply-env
  (lambda (env search-var)
    (cases environment env
      (empty-env () (report-no-binding-found search-var))
      (extend-env (saved-var saved-val saved-env)
        (if (eq? search-var saved-var) saved-val
          (apply-env saved-env search-var))))))
(define has-binding?
  (lambda (env search-var)
    (cases environment env
      (empty-env () #f)
      (extend-env (saved-var saved-val saved-env)
        (if (eq? search-var saved-var) #t
          (has-binding? saved-env search-var))))))

;;exercise 2.23
(define identifier?
  (lambda (s)
    (and (symbol? s) (not (eq? s 'lambda)))))
(define-datatype lc-exp lc-exp?
  (var-exp
    (var identifier?))
  (lambda-exp
    (bound-var identifier?)
    (body lc-exp?))
  (app-exp
    (rator lc-exp?)
    (rand lc-exp?)))

;;exercise 2.24
(define-datatype bintree bintree?
  (leaf-node
    (num integer?))
  (interior-node
    (key symbol?)
    (left bintree?)
    (right bintree?)))
(define bintree-to-list
  (lambda (bt)
    (cases bintree bt
      (leaf-node (n) (list 'leaf-node n))
      (interior-node (key left right) (list 'interior-node key (bintree-to-list left) (bintree-to-list right))))))

;;exercise 2.25
(define add-leaves
  (lambda (bt)
    (cases bintree bt
      (leaf-node (n) n)
      (interior-node (key left right) (+ (add-leaves left) (add-leaves right))))))
(define interior-with-sum
  (lambda (bt)
    (cases bintree bt
      (leaf-node (n) '())
      (interior-node (key left right) (list (list key (+ (add-leaves left) (add-leaves right))) (interior-with-sum left) (interior-with-sum right))))))
(define max-num
  (lambda (loi)
    (cond
       ((eq? (length loi) 1) (car loi))
       (else
        (cond
          ((< (car loi) (cadr loi)) (max-num (cons (cadr loi) (cddr loi))))
          (else (max-num (cons (car loi) (cddr loi)))))))))
(define max-interior
  (lambda (bt)
    (let ((node-with-sum (flatten (interior-with-sum bt))))
      (pick (- (index (max-num (filter-in number? node-with-sum)) node-with-sum) 1) node-with-sum))))

;;exercise 2.29
(define-datatype lc-exp* lc-exp*?
  (var-exp*
    (var identifier?))
  (lambda-exp*
    (bound-vars (list-of identifier?))
    (body lc-exp*?))
  (app-exp*
    (rator lc-exp*?)
    (rands (list-of lc-exp*?))))
(define report-invalid-concrete-syntax
  (lambda (exp)
    (eopl:error 'parse-expression* "invalid concrete syntax ~s" exp)))
(define report-invalid-identifier
  (lambda (exp)
    (eopl:error 'parse-expression* "invalid identifier ~s" exp)))
(define parse-expression*
  (lambda (datum)
    (cond
      ((eq? datum 'lambda) (report-invalid-identifier datum))
      ((identifier? datum) (var-exp* datum))
      ((pair? datum)
       (if (eqv? (car datum) 'lambda)
         (lambda-exp*
           (cadr datum)
           (parse-expression* (caddr datum)))
         (app-exp*
           (parse-expression* (car datum))
           (map parse-expression* (cadr datum)))))
      (else (report-invalid-concrete-syntax datum)))))

;;exercise 2.31
(define-datatype prefix-exp prefix-exp?
  (const-exp
    (num integer?))
  (diff-exp
    (operand1 prefix-exp?)
    (operand2 prefix-exp?)))
(define parse
  (lambda (plst)
    (cond
      ((integer? (car plst)) (const-exp (car plst)))
      (else ()))))