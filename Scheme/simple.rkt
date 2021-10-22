#lang racket

(define (assign var type) (list 'type var type))
(define (get-type var) (caddr var))
(define (typed? var)
    (and (pair? var) (eq? (car var) 'type)))

(define (infer-type var)
    (cond 
        ((typed? var) (get-type var))
        ((number? var) 'Int)
        ((string? var) 'String)
        ((func? var)   (infer-func-type var))
        ((pair? var)   (make-pair-type (car var) (cdr var)))
        ((eq? var '()) 'Nil)
        (else 'type-error)))

(define (func? f) 
    (if (typed? f) 
        (eq? (car (get-type f)) '->) 
        (and (pair? f) (eq? (car f) '=>))))

(define (make-pair-type a b)
    (let ((p (infer-type a)) 
          (q (infer-type b)))
        (if (or (eq? p 'type-error) (eq? q 'type-error))
           'type-error
           (list 'pair p q))))

(define (infer-func-type f) 
    (infer-body (caddr f) (cadr f)))

; (define (infer-body body x)
;     (if (app? body)
;         (if (primitive-func? (car body))
;             (if (eq? (cadr body) x)
;                 (caddr (get-type (car body)))
;                 'type-error)
;             (infer-type body))
;     "infer error"))

(define (func-type? f) (and (pair? f) (eq? (car f) '->)))
(define (arg-type f) (if (func-type? f) (cadr f) 'type-error))
(define (ret-type f) (if (func-type? f) (caddr f) 'type-error))

(define (app-val f x) (app (infer-type f) (infer-type x)))

(define (app f x)
    (if (and (func-type? f) (eq? (arg-type f) x))
        (ret-type f)
        'type-error))

(define (app? expr)
    (and (pair? expr) (func? (car expr))))

(define (primitive-func? f) (and (pair? f) (eq? (cadr f) '<primitive>)))

(define succ (assign '<primitive> '(-> Int Int)))
(define add  (assign '<primitive> '(-> Int (-> Int Int))))

(define primitves '(succ add))

(define (process expr)
    (define (helper x)
        (cond 
            ((list? x) (map helper x))
            (else (if (member x primitves) (eval x) x))))
    (map helper expr))

(define (reload) (load "simple.scm"))
