; #lang typed/racket

(struct pt ([x : Real] [y : Real]))
(struct sg ([x : Real]))

(define-type ut (U pt sg))
(define-type it (I pt sg))
