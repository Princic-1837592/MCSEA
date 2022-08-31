% simple
d(X, X, 1).

d(Y, X, 0) :-
    atomic(Y),
    Y \= X.
    
d(X^N, X, N * X^(N-1)) :-
    d(N, X, DN),
    DN =:= 0.

d(1/X, X, -1/X^2).

d(sqrt(X), X, 1/(2 * sqrt(X))).

d(abs(X), X, abs(X)/X).

d(log(e, X), X, 1/X).

d(log(A, X), X, 1/X * log(A, e)) :-
    d(A, X, DA),
    DA =:= 0.

d(ln(X), X, 1/X).

d(e^X, X, e^X).

d(A^X, X, A^X * ln(A)) :-
    d(A, X, DA),
    DA =:= 0.

% trigonometric
d(abs(X), X, X / abs(X)).
d(ln(X), X, 1 / X).
d(sin(X), X, cos(X)).
d(cos(X), X, -sin(X)).
d(tan(X), X, 1 / cos(X)^2).
d(tan(X), X, 1 + tan(X)^2).
d(cot(X), X, -1 / sin(X)^2).
d(cot(X), X, -(1 + cot(X)^2)).
d(arcsin(X), X, 1 / root(2, 1 - X^2)).
d(arccos(X), X, -1 / root(2, 1 - X^2)).
d(arctan(X), X, 1 / (1 + X^2)).
d(arccot(X), X, -1 / (1 + X^2)).


% rules
d(F + G, X, DF + DG) :-
    d(F, X, DF),
    d(G, X, DG).
    
d(F - G, X, DF - DG) :-
    d(F, X, DF),
    d(G, X, DG).








simp(X*1, X).
simp(1*X, X).

simp(X*(-1), -X).
simp(-1*X, -X).

simp(X+0, X).
simp(0+X, X).

simp(0*_, 0).
simp(_*0, 0).

simp(_^0, 1).
simp(X^1, X).

simp(0^_, 0).
simp(1^_, 1).

simp(X-X, 0).

simp(FAB, E) :-
    FAB =.. [_, A, B],
    number(A),
    number(B),
    E is FAB,
    !.

simplify(X, Z) :-
   simp(X, Y),
   !,
   simplify(Y, Z).
   
simplify(A+B, C+D) :-
    simplify(A, C),
    simplify(B, D).

simplify(A-B, C-D) :-
    simplify(A, C),
    simplify(B, D).

simplify(A*B, C*D) :-
    simplify(A, C),
    simplify(B, D).

simplify(A/B, C/D) :-
    simplify(A, C),
    simplify(B, D).
    
simplify(X, X).

simpder(F, X, SDSF) :-
    d(SF, X, DSF),
    simplify(DSF, SDSF).
