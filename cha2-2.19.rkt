#lang eopl
(require "cha1.rkt")
;;exercise 2.19
(define number->bintree
  (lambda (n)
    (list n '() '())))
(define current-element contents-of)
(define move-to-left lson)
(define move-to-right rson)
(define at-leaf? null?)
(define insert-to-left
  (lambda (n bt)
    (let ((cur-node (current-element bt))
          (left-son (move-to-left bt))
          (right-son (move-to-right bt)))
      (cond
        ((at-leaf? left-son)
         (list cur-node (number->bintree n) right-son))
        (else
         (list cur-node (list n left-son '()) right-son))))))
(define insert-to-right
  (lambda (n bt)
    (let ((cur-node (current-element bt))
          (left-son (move-to-left bt))
          (right-son (move-to-right bt)))
      (cond
        ((at-leaf? right-son)
         (list cur-node left-son (number->bintree n)))
        (else
         (list cur-node left-son (list n right-son '())))))))