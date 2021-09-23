person(cyz).
person(jyc).
person(yky).

crime(X) :-
    person(X),
    kitchen(X),
    knife(X),
    \+ white(X).

kitchen(cyz).
kitchen(jyc).
kitchen(yky).

knife(jyc).
knife(yky).

white(jyc).
white(cyz).
