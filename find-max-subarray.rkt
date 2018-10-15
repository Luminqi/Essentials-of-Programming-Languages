#lang racket
;;find-max-crossing-subarray : List × Num × Num × Num -> List(Num Num Num)
(define find-max-crossing-subarray
  (lambda (lst low mid high)
    (let ((left-result (find-max-left-result lst low mid))
          (right-result (find-max-right-result lst (+ mid 1) high)))
      (let ((max-left (car left-result))
            (left-sum (cadr left-result))
            (max-right (car right-result))
            (right-sum (cadr right-result)))
        (list max-left max-right (+ left-sum right-sum))))))
(define find-max-left-result
  (lambda (lst low mid)
    (let loop ((i mid) (left-sum -inf.0) (sum 0) (max-left mid))
      (cond
        ((< i low) (list max-left left-sum))
        (else
         (let ((sum (+ sum (list-ref lst i))))
           (cond
             ((> sum left-sum) (loop (- i 1) sum sum i))
             (else
              (loop (- i 1) left-sum sum max-left)))))))))
(define find-max-right-result
  (lambda (lst mid high)
    (let loop ((i mid) (right-sum -inf.0) (sum 0) (max-right mid))
      (cond
        ((> i high) (list max-right right-sum))
        (else
         (let ((sum (+ sum (list-ref lst i))))
           (cond
             ((> sum right-sum) (loop (+ i 1) sum sum i))
             (else
              (loop (+ i 1) right-sum sum max-right)))))))))
;;find-max-subarray : List × Num × Num -> List(Num Num Num)
(define find-max-subarray
  (lambda (lst low high)
    (cond
      ((equal? low high) (list low high (list-ref lst low)))
      (else
       (let ((mid (exact-floor (/ (+ low high) 2))))
         (let ((left-result (find-max-subarray lst low mid))
               (right-result (find-max-subarray lst (+ mid 1) high))
               (cross-result (find-max-crossing-subarray lst low mid high)))
           (let ((left-low (car left-result))
                 (left-high (cadr left-result))
                 (left-sum (caddr left-result))
                 (right-low (car right-result))
                 (right-high (cadr right-result))
                 (right-sum (caddr right-result))
                 (cross-low (car cross-result))
                 (cross-high (cadr cross-result))
                 (cross-sum (caddr cross-result)))
             (cond
               ((and (>= left-sum right-sum) (>= left-sum cross-sum)) (list left-low left-high left-sum))
               ((and (>= right-sum left-sum) (>= right-sum cross-sum)) (list right-low right-high right-sum))
               (else (list cross-low cross-high cross-sum))))))))))