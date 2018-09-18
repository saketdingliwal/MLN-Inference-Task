f(X,Z) :- domain(Y), domain(X), domain(Z), f(X,Y), f(Y,Z).
f(Y,X) :- domain(Y), domain(X), f(X,Y).
