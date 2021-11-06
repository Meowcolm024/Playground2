type(unit).
type(bool).
type(nat).
type(arr(_, _)).    % function type
type(star(_, _)).   % tuple (product) type

arr(A, B) :- type(A), type(B).
star(A, B) :- type(A), type(B).

value(u).
value(t).
value(f).
value(zero).
value(succ(_)).
value(ifelse(_, _, _)).
value(add(_, _)).
value(equal(_, _)).
value(nott(_)).
value(fun(_)).
value(funApp(_, _)).
value(pair(_, _)).

succ(T) :- value(T).
add(X, Y) :- value(X), value(Y).
iszero(T) :- value(T).
nott(X) :- value(X).

ifelse(P, T, E) :- value(P), value(T), value(E).
equal(X, Y) :- value(X), value(Y).

fun(arr(_, _)).
funApp(fun(_), X) :- value(X).

pair(A, B) :- value(A), value(B).

welltyped(u, unit).
welltyped(t, bool).
welltyped(f, bool).
welltyped(zero, nat).
welltyped(succ(T), nat) :- welltyped(T, nat).
welltyped(ifelse(P, T, E), X) :- type(X), welltyped(P, bool), welltyped(T, X), welltyped(E, X).
welltyped(add(X, Y), nat) :- welltyped(X, nat), welltyped(Y, nat).
welltyped(equal(X, Y), bool) :- welltyped(X, T), welltyped(Y, T).
welltyped(iszero(X), bool) :- welltyped(X, nat).
welltyped(nott(X), bool) :- welltyped(X, bool).
welltyped(fun(T), X) :- type(X), X = T.
welltyped(funApp(fun(arr(P, R)), V), X) :- type(X), welltyped(V, P), X = R.
welltyped(funApp(F, V), X) :- type(X), welltyped(F, arr(P, R)), welltyped(V, P), R = X.
welltyped(pair(A, B), star(P, Q)) :- welltyped(A, P), welltyped(B, Q).

% welltyped(funApp(fun(arr(nat, bool)), zero), T).
% welltyped(pair(t, pair(u, zero)), T).
% welltyped(funApp(funApp(fun(arr(nat, arr(nat, star(nat, nat)))), succ(zero)), succ(succ(zero))), T).
% funApp(funApp(funApp(fun(arr(nat, arr(bool, arr(star(nat, bool), unit)))), zero), t), pair(succ(zero), f)).
