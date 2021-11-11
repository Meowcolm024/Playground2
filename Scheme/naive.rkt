#lang racket

;; (type-constructor base-type arg-types)

(define option '(option 1))
(define none '(none (option 1) ()))
(define some '(some (option 1) (1)))

(define (none-constr) '(none (option 1) ()))
(define (some-constr v) (list 'some '(option 1) (list v)))

(define (type n)
    (cond 
        ((number? n) 'int)
        ((string? n) 'string)
        ((boolean? n) 'bool)
        (else (get-type n))))

(define (get-type n) (cadr n))
