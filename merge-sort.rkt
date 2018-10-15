#lang racket
(define merge
  (lambda (loi1 loi2)
    (cond
      ((null? loi1) loi2)
      ((null? loi2) loi1)
      ((<= (car loi1) (car loi2)) (cons (car loi1) (merge (cdr loi1) loi2)))
      (else (cons (car loi2) (merge loi1 (cdr loi2)))))))
(define merge-sort
  (lambda (loi)
    (let ((length (length loi)))
      (if (<= length 1)
        loi
        (let ((mid-pos  (exact-floor (/ length 2))))
          (let ((loi1 (take loi mid-pos))
                (loi2 (list-tail loi mid-pos)))
            (merge (merge-sort loi1) (merge-sort loi2))))))))
(define merge/k
  (lambda (loi1 loi2 cont)
    (cond
      ((null? loi1) (cont loi2))
      ((null? loi2) (cont loi1))
      ((<= (car loi1) (car loi2)) (merge/k (cdr loi1) loi2 (lambda (val) (cont (cons (car loi1) val)))))
      (else (merge/k loi1 (cdr loi2) (lambda (val) (cont (cons (car loi2) val))))))))
(define merge-sort/k
  (lambda (loi cont)
    (let ((length (length loi)))
      (if (<= length 1)
        (cont loi)
        (let ((mid-pos  (exact-floor (/ length 2))))
          (let ((loi1 (take loi mid-pos))
                (loi2 (list-tail loi mid-pos)))
            (merge-sort/k loi1
              (lambda (val1)
                (merge-sort/k loi2
                  (lambda (val2)
                    (merge/k val1 val2 cont)))))))))))