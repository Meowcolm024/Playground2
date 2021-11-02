#lang racket

(define (assign v t) (cons v t))
(define (val v) (car v))
(define (type v) (cdr v))
(define (has-type v ty) (if (pair? v) (eq? (type v) ty) #f))
(define (eq-type? x y) (if (and (pair? x) (pair? y)) (eq? (type x) (type y)) #f))

;; typed functions (construction only)

(define (add x y) 
    (if (and (has-type x 'int) (has-type y 'int))
        (assign (list 'add x y) 'int)
        'error))

(define (mul x y)
    (if (and (has-type x 'int) (has-type y 'int))
        (assign (list 'mul x y) 'int)
        'error))

(define (not-bool x) 
    (if (eq? (type x) 'bool)
        (assign (list 'not-bool x) 'bool)
        'error))

(define (eq-int x y)
    (if (and (has-type x 'int) (has-type y 'int))
        (assign (list 'eq-int x y) 'bool)
        'error))

(define (eq-bool x y)
    (if (and (has-type x 'bool) (has-type y 'bool))
        (assign (list 'eq-bool x y) 'bool)
        'error))

(define (if-else b t1 t2)
    (if (and (has-type b 'bool) (eq-type? t1 t2))
        (assign (list 'if-else b t1 t2) (type t1))
        'error))

;; eval function

;; eval typed expr
(define (eval-expr expr)
    (if (eq? expr 'error)
        'not-well-typed
        (eval-raw expr)))

;; helper function
(define (eval-raw e)
    (let ((expr (car e)) (ty (cdr e)))
        (if (list? expr)
            (cond
                ((eq? (val expr) 'add) 
                    (assign (+ (val (eval-raw (cadr expr))) (val (eval-raw (caddr expr)))) ty))
                ((eq? (val expr) 'mul) 
                    (assign (* (val (eval-raw (cadr expr))) (val (eval-raw (caddr expr)))) ty))
                ((eq? (val expr) 'not-bool)
                    (assign (not (val (eval-raw (cadr expr)))) ty))
                ((eq? (val expr) 'eq-int)
                    (assign (= (val (eval-raw (cadr expr))) (val (eval-raw (caddr expr)))) ty))
                ((eq? (val expr) 'eq-bool)
                    (assign (eq? (val (eval-raw (cadr expr))) (val (eval-raw (caddr expr)))) ty))
                ((eq? (val expr) 'if-else)
                    (let ((c (eval-raw (cadr expr))))
                        (cond 
                            ((eq? (car c) #t) (eval-raw (caddr expr)))
                            ((eq? (car c) #f) (eval-raw (cadddr expr)))
                            (else 'eval-error))))
                (else 'eval-error))
            e   ;; primitive
    )))

;; def

(define t (assign #t 'bool))    ;; primitive
(define f (assign #f 'bool))    ;; primitive

(define a (assign 1 'int))
(define b (assign 2 'int))
(define e1 (if-else 
    (eq-int a b) (add a b)
    (if-else (not-bool (eq-bool t f)) (mul (add b a) b) (mul b b))))
