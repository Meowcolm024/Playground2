#lang racket

(define (stuck p) (list 'stuck p))
(define (run prog)
    (match prog
        ['true 'true]
        ['false 'false]
        ['zero 'zero]
        [(list 'succ r) (list 'succ (run r))]
        [(list 'pred (list 'succ r)) (run r)]
        [(list 'iszero 'zero) 'true]
        [(list 'iszero (list 'succ _)) 'false]
        [(list 'if p 'then t 'else a) 
         (match (run p) 
            ['true (run t)] 
            ['false (run a)]
            [result (stuck result)])]
        [else (stuck prog)]))

(define a '(succ (succ zero)))
(define p 
    '(if (iszero (succ zero))
      then (succ zero)
      else true
    )
)

(displayln (run p))
