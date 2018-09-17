s(X) :- domain(X).
c(X) :- domain(X).
f(X,Y) :- domain(Y), domain(X).
s(Y) :- domain(Y), domain(X), s(X), f(X,Y).
c(X) :- domain(X), s(X).
