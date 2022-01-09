#lang racket

(define (int)
    (define val 0)
    (define (dispatch msg)
        (cond
            [(eq? msg 'inc) (set! val (+ val 1))]
            [(eq? msg 'dec) (set! val (- val 1))]
            [(eq? msg 'get) val]
            [(eq? msg 'reset) (lambda (x) (set! val x))]
            [else (error 'unknown)]
        )
    )
    dispatch)

(define (inc x) (x 'inc))
(define (dec x) (x 'dec))
(define (get x) (x 'get))
(define (reset val) (lambda (x) ((x 'reset) val)))

(define (inc-ret x)
    (define ret (get x))
    (begin
        (inc x)
        ret))

(define (object obj) (lambda (msg) (msg obj)))

(define a (object (int)))
(define b (object (int)))
