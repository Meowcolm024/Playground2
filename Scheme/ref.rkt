#lang racket

;; reference cell
(define (ref v)
    (define val v)
    (define (dispatch msg)
        (match msg
            ['deref   (force val)]
            ['update  (lambda (n) (set! val n))]
            [else     (error 'wrong-msg)]))
    dispatch)

;; dereference
(define (! k) (k 'deref))
;; update
(define (<- k v) ((k 'update) v))
;; null ref
(define (null-ref) (ref (delay (error 'null-ref))))
;; list of refs
(define (mut-arr l)
    (define (mk ln)
        (if (= ln 0)
            '()
            (cons (null-ref) (mk (- ln 1)))))
    (ref (mk l)))


(define a (ref 10))

(define arr (mut-arr 3))
(<- (list-ref (! arr) 0) 1)
(<- (list-ref (! arr) 1) 2)
(<- (list-ref (! arr) 2) 4)

(define a1 (list-ref (! arr) 1))
