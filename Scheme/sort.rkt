#lang racket

(define (swap vec a b)
    (define tmp (vector-ref vec a))
    (begin
        (vector-set! vec a (vector-ref vec b))
        (vector-set! vec b tmp)))

(define (qsort xs)
    (if (null? xs)
        '()
        (let ((left (filter (lambda (x) (< x (car xs))) (cdr xs)))
              (right (filter (lambda (x) (>= x (car xs))) (cdr xs))))
            (append (qsort left) (list (car xs)) (qsort right)))))
