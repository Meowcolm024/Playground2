#lang racket

(define (fix f) (
    (λ (x) (f (λ (y) ((x x) y))))
    (λ (x) (f (λ (y) ((x x) y))))
    ))

(define fact0
    (λ (f) (λ (x)
        (if (= x 0) 1 (* x (f (- x 1))))
    )))

(define fact (fix fact0))
