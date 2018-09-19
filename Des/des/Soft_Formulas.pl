c(X) :- domain(X), s(X).
s(Y) :- domain(Y), domain(X), s(X), f(X,Y).
not f(X,Y) :- domain(Y), domain(X), s(X).
