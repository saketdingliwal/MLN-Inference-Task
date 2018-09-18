e(a0,a1).
e(a0,a2).
e(a1,a3).
e(a1,a4).
e(a2,a5).
e(a2,a6).
p(X,X) :- domain(X).
p(X,Z) :- domain(Y), domain(X), domain(Z), p(X,Y), e(Y,Z).
