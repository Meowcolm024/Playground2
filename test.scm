(define (hello)
    (begin
        (display "hello")
        (newline)
        (display (map (lambda (x) (* x 2)) '(1 2 3)))
        (newline)))

(hello)
