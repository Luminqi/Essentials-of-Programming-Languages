(module LET
(lib "eopl.ss" "eopl")
(provide (all-defined-out))
(define atom?
  (lambda (l)
    (and (not (pair? l)) (not (null? l)))))
(define length*
  (lambda (l)
    (cond
      ((null? l) 0)
      ((atom? (car l))
       (+ 1 (length* (cdr l))))
      (else
       (+ (length* (car l)) (length* (cdr l)))))))
(define remove
  (lambda (s los)
    (cond
      ((null? los) '())
      ((eq? (car los) s)
       (remove s (cdr los)))
      (else
       (cons (car los) (remove s (cdr los)))))))
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
(define duple
  (lambda (n x)
    (cond
      ((zero? n) '())
      (else
       (cons x (duple (- n 1) x))))))
(define invert-pair
  (lambda (p)
    (cond
      ((null? p) '())
      (else
       (cons (cadr p) (cons (car p) '()))))))
(define invert
  (lambda (lst)
    (cond
      ((null? lst) '())
      (else
       (cons (invert-pair (car lst))
             (invert (cdr lst)))))))
(define down
  (lambda (lst)
    (cond
      ((null? lst) '())
      (else
       (cons (cons (car lst) '()) (down (cdr lst)))))))
(define subst*
  (lambda (new old l)
    (cond
      ((null? l) '())
      ((atom? (car l))
       (cond
         ((eq? old (car l))
          (cons new (subst* new old (cdr l))))
         (else
          (cons (car l) (subst* new old (cdr l))))))
      (else
       (cons
        (subst* new old (car l))
        (subst* new old (cdr l)))))))
(define swapper
  (lambda (s1 s2 slist)
    (cond
      ((null? slist) '())
      ((atom? (car slist))
       (cond
         ((eq? s1 (car slist))
          (cons s2 (swapper s1 s2 (cdr slist))))
         ((eq? s2 (car slist))
          (cons s1 (swapper s1 s2 (cdr slist))))
         (else
          (cons (car slist) (swapper s1 s2 (cdr slist))))))
      (else
       (cons
        (swapper s1 s2 (car slist))
        (swapper s1 s2 (cdr slist)))))))
(define list-set
  (lambda (lst n x)
    (cond
      ((< (length lst) (- n 1)) '())
      ((= n 0) (cons x (cdr lst)))
      (else
       (cons (car lst) (list-set (cdr lst) (- n 1) x))))))
(define count-occurrences
  (lambda (s slist)
    (cond
      ((null? slist) 0)
      ((atom? (car slist))
       (cond
         ((eq? s (car slist)) (+ 1 (count-occurrences s (cdr slist))))
         (else (count-occurrences s (cdr slist)))))
      (else (+ (count-occurrences s (car slist)) (count-occurrences s (cdr slist)))))))
(define product-by-symbol
  (lambda (sos s)
    (cond
      ((null? sos) '())
      (else (cons(list s (car sos)) (product-by-symbol (cdr sos) s))))))
(define product
  (lambda (sos1 sos2)
    (cond
      ((or (null? sos1) (null? sos2)) '())
      (else (cons (product-by-symbol sos2 (car sos1)) (product (cdr sos1) sos2))))))
(define add-list
  (lambda (lst1 lst2)
    (cond
      ((null? lst1) lst2)
      ((atom? lst1) (cons lst1 lst2))
      (else (cons (car lst1) (add-list (cdr lst1) lst2))))))
(define up
  (lambda (lst)
    (cond
      ((null? lst) '())
      (else (add-list (car lst) (up (cdr lst)))))))
(define new-product
  (lambda (sos1 sos2)
    (up (product sos1 sos2))))
(define filter-in
  (lambda (pred lst)
    (cond
      ((null? lst) '())
      (else
       (cond
         ((pred (car lst)) (cons (car lst) (filter-in pred (cdr lst))))
         (else (filter-in pred (cdr lst))))))))
(define filter-in*
  (lambda (pred lst)
    (cond
      ((null? lst) '())
      ((atom? (car lst))
       (cond
         ((pred (car lst)) (cons (car lst) (filter-in* pred (cdr lst))))
         (else (filter-in* pred (cdr lst)))))
      (else
       (cons (filter-in* pred (car lst)) (filter-in* pred (cdr lst)))))))
(define new-filter-in*
  (lambda (pred lst)
    (flatten (filter-in* pred lst))))
(define list-index-from
  (lambda (pred lst n)
    (cond
      ((null? lst) #f)
      (else
       (cond
         ((pred (car lst)) n)
         (else (list-index-from pred (cdr lst) (+ n 1))))))))
(define list-index
  (lambda (pred lst)
    (list-index-from pred lst 0)))
(define every?
  (lambda (pred lst)
    (cond
      ((null? lst) #f)
      ((= (length lst) 1) (pred (car lst)))
      (else (and (pred (car lst)) (every? pred (cdr lst)))))))
(define exists?
  (lambda (pred lst)
    (cond
      ((null? lst) #f)
      ((= (length lst) 1) (pred (car lst)))
      (else (or (pred (car lst)) (exists? pred (cdr lst)))))))
(define flatten
  (lambda (slist)
    (cond
      ((null? slist) '())
      ((atom? (car slist)) (cons (car slist) (flatten (cdr slist))))
      (else
       (up (cons (flatten (car slist)) (up (flatten (cdr slist)))))))))
(define insert
  (lambda (i loi)
    (cond
      ((null? loi) (cons i loi))
      (else
       (cond
         ((<= i (car loi)) (cons i loi))
         (else (cons (car loi) (insert i (cdr loi)))))))))
(define merge
  (lambda (loi1 loi2)
    (cond
      ((null? loi1) loi2)
      (else
       (insert (car loi1) (merge (cdr loi1) loi2))))))
(define merge2
  (lambda (loi1 loi2)
    (cond
      ((null? loi1) loi2)
      ((null? loi2) loi1)
      ((<= (car loi1) (car loi2)) (cons (car loi1) (merge2 (cdr loi1) loi2)))
      (else (cons (car loi2) (merge2 loi1 (cdr loi2)))))))
(define merge-sort
  (lambda (loi)
    (if (null? loi)
      '()
      (let ((mid-pos  (floor (/ (length loi) 2))))
        (let ((loi1 (take loi mid-pos))
              (loi2 (list-tail loi mid-pos)))
          (merge (merge-sort loi1) (merge-sort loi2)))))))
(define sort
  (lambda (loi)
    (cond
      ((null? loi) '())
      (else
       (insert (car loi) (sort (cdr loi)))))))
(define insert/predicate
  (lambda (pred i loi)
    (cond
      ((null? loi) (cons i loi))
      (else
       (cond
         ((pred i (car loi)) (cons i loi))
         (else (cons (car loi) (insert/predicate pred i (cdr loi)))))))))
(define sort/predicate
  (lambda (pred loi)
    (cond
      ((null? loi) '())
      (else
       (insert/predicate pred (car loi) (sort/predicate pred (cdr loi)))))))
(define report-arg-not-number
  (lambda (arg)
    (eopl:error 'leaf
      "Argument ~s is not a number.~%" arg)))

;;Bintree :: = Int | (Symbol Bintree Bintree)
(define leaf
  (lambda (Int)
    (cond
      ((number? Int) Int)
      (else
       (report-arg-not-number Int)))))
(define interior-node list)
(define leaf?
  (lambda (bt)
    (number? bt)))
(define lson
  (lambda (bt)
    (cond
      ((leaf? bt) '())
      (else (cadr bt)))))
(define rson
  (lambda (bt)
    (cond
      ((leaf? bt) '())
      (else (caddr bt)))))
(define contents-of
  (lambda (bt)
    (cond
      ((leaf? bt) bt)
      (else (car bt)))))
(define map-leaves
  (lambda (pred bt)
    (cond
      ((leaf? bt) (leaf (pred bt)))
      (else
       (interior-node (contents-of bt) (map-leaves pred (lson bt)) (map-leaves pred (rson bt)))))))
(define double
  (lambda (int)
    (* int 2)))
(define double-tree
  (lambda (bt)
    (map-leaves double bt)))
(define mark-leaves-with-red-depth-from
  (lambda (n bt)
    (cond
      ((leaf? bt) (leaf n))
      (else
       (cond
         ((eq? (contents-of bt) 'red)
          (interior-node (contents-of bt) (mark-leaves-with-red-depth-from (+ n 1) (lson bt)) (mark-leaves-with-red-depth-from (+ n 1) (rson bt))))
         (else
          (interior-node (contents-of bt) (mark-leaves-with-red-depth-from n (lson bt)) (mark-leaves-with-red-depth-from n (rson bt)))))))))
(define mark-leaves-with-red-depth
  (lambda (bt)
    (mark-leaves-with-red-depth-from 0 bt)))

;;Binary-search-tree :: = () | (Int Binary-search-tree Binary-search-tree)
(define report-arg-not-null
  (lambda (arg)
    (eopl:error 'leaf
      "Argument ~s is not ().~%" arg)))
(define bst-leaf
  (lambda (l)
    (cond
      ((null? l) l)
      (else
       (report-arg-not-null l)))))
(define bst-leaf?
  (lambda (l)
    (null? l)))
(define bst-interior-node interior-node)
(define bst-lson lson)
(define bst-rson rson)
(define bst-contents-of contents-of)
(define revcons
  (lambda (s lst)
    (up (list lst (cons s '())))))
(define path-helper
  (lambda (n bst lst)
    (cond
      ((bst-leaf? bst) '())
      (else
       (cond
         ((eq? (bst-contents-of bst) n) lst)
         ((> (bst-contents-of bst) n) (path-helper n (bst-lson bst) (revcons 'left lst)))
         (else (path-helper n (bst-rson bst) (revcons 'right lst))))))))
(define path
  (lambda (n bst)
    (path-helper n bst '())))
(define numbers-in-lst
  (lambda (lst)
    (filter-in number? (flatten lst))))
(define add1
  (lambda (n)
    (+ n 1)))
(define interior-node-with-add1
  (lambda (s bt1 bt2)
    (list s bt1 (map-leaves add1 bt2))))
(define make-zero
  (lambda (n)
    0))
(define make-newbt
  (lambda (pred bt)
    (map-leaves pred bt)))
(define number-leaves-with-newbt
  (lambda (bt)
    (cond
      ((leaf? bt) bt)
      (else
       (interior-node-with-add1 (contents-of bt) (number-leaves-with-newbt (lson bt)) (number-leaves-with-newbt (rson bt)))))))
(define number-leaves
  (lambda (bt)
    ((lambda (newbt)
       (number-leaves-with-newbt newbt)) (make-newbt make-zero bt))))
(define number-car-from
  (lambda (n lop)
    (cond
      ((null? lop) '())
      (else
       (cons (cons n (cdar lop)) (number-car-from (+ 1 n) (cdr lop)))))))
(define add1-to-car
  (lambda (lop)
    (cond
      ((null? lop) '())
      (else
       (cons (cons (+ (caar lop) 1) (cdar lop)) (add1-to-car (cdr lop)))))))
(define g
  (lambda (p lop)
    (cons p (add1-to-car lop))))
(define number-elements
  (lambda (lst)
    (cond
      ((null? lst) '())
      (else
       (g (list 0 (car lst)) (number-elements (cdr lst)))))))
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
(provide (all-defined-out))
)