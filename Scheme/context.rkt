#lang racket

(define (lit ty) (lambda (ctx) (list 'lit ty ctx)))
(define (var n) (lambda (ctx) (list 'var n ctx)))
(define (type x) (lambda (ctx) (cadr (x ctx))))
(define (has-type? x t)
    (lambda (ctx)
        (if (pair? (x ctx))
            (eq? (type (x ctx)) t)
            'error)))

(define (add x y)
    (lambda (ctx)
        (list 'add 'int ctx (cons x y))))

(define (eq-int x y)
    (lambda (ctx)
        (list 'eq-int 'bool ctx (cons x y))))

(define (not-bool x)
    (lambda (ctx)
        (list 'not 'bool ctx x)))

(define (let-in n t r)
    (lambda (ctx)
        (list 'let (type r) (cons (cons n t) ctx) r)))

(define (type-check expr ctx)
    (let ((ex (expr ctx)))
    (cond
        ((eq? ex 'type-error) 'type-error)
        ((eq? (car ex) 'lit) (list 'lit (cadr ex)))
        ((eq? (car ex) 'add) 
            (let ((x (type-check (car (cadddr ex)) ctx)) (y (type-check (cdr (cadddr ex)) ctx)))
                (if (and (eq? (cadr x) 'int) (eq? (cadr y) 'int))
                    (list 'add 'int (cons x y))
                    'type-error)))
        ((eq? (car ex) 'eq-int) 
            (let ((x (type-check (car (cadddr ex)) ctx)) (y (type-check (cdr (cadddr ex)) ctx)))
                (if (and (eq? (cadr x) 'int) (eq? (cadr y) 'int))
                    (list 'eq-int 'bool (cons x y))
                    'type-error)))
        ((eq? (car ex) 'not)
            (let ((x (type-check (cadddr ex) ctx)))
                (if (eq? (cadr x) 'bool)
                    (list 'not 'bool x)
                    'type-error)))
        ((eq? (car ex) 'let)
            (list )
        )
    )))


;; def

(define (view x ctx) (x ctx))

(define a (lit 'int))
(define b (lit 'int))
(define t (lit 'bool))
(define f (lit 'bool))

(define e1 (not-bool (eq-int b (add a b))))
