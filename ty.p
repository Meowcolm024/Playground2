type(bool).
type(int).

add1(int, int).
ifelse(bool, X, Y) :- type(X), type(Y), X = Y.
not1(bool).