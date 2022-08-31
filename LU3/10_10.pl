% X' = 1
d(X, X, 1).


% Y' = 0 if Y is number or atom different from X
d(Y, X, 0) :-
    atomic(Y),
    Y \= X.


% alternative way to match a n-root (next rule)
d(root(A, X), X, Z) :-
    d(X^(1 / A), X, Z).

% (X^A)' = AX^(A-1)    if A constant wrt X
d(X^A, X, A * X^(A-1)) :-
    d(A, X, DA),
    DA = 0.


% ln(X)' = 1/X
d(ln(X), X, 1 / X).

% special case of log
d(log(e, X), X, Z) :-
    d(ln(X), X, Z).

% (log_A(X))' = 1/(X * ln(A))
% also matches more complex expressions than just X
d(log(A, F), X, 1 / (F * ln(A)) * DF) :-
    d(A, X, DA),
    DA = 0,
    !,
    d(F, X, DF).


% (e^X)' = e^X
d(e^X, X, e^X).

% also matches more complex expressions than just X
d(e^F, X, e^F * DF):-
    d(F, X, DF).

% (A^X)' = A^X ln(A)
% also matches more complex expressions than just X
d(A^F, X, A^F * ln(A) * DF) :-
    d(A, X, DA),
    DA = 0,
    !,
    d(F, X, DF).

    
% composition rule. Matches functions applied to functions like f(g(x))
% rules for this kind of recursive application must be declared in d1
d(FG, X, DF * DG) :-
    FG =.. [_, G],
    d(G, X, DG),
    d1(FG, DF).


% (F * G)' = FG' + GF'
d(F * G, X, F * DG + G * DF) :-
    d(F, X, DF),
    d(G, X, DG).


% (A * Y)' = A * Y' if A is constant w.r.t. X
d(A * F, X, A * DF) :-
    d(A, X, DA),
    DA = 0,
    !,
    d(F, X, DF).


% (F + G)' = F' + G'
d(F + G, X, DF + DG) :-
    d(F, X, DF),
    d(G, X, DG).


% (F - G)' = F' - G'
d(F - G, X, DF - DG) :-
    d(F, X, DF),
    d(G, X, DG).


%(F/G)' = (F' * G - F * G') / G^2
d(F / G, X, (DF * G - F * DG) / G^2) :-
    d(F, X, DF),
    d(G, X, DG).


d1(abs(X), X / abs(X)).
d1(ln(X), 1 / X).
d1(sin(X), cos(X)).
d1(cos(X), -sin(X)).
d1(tan(X), 1 / cos(X)^2).
d1(tan(X), 1 + tan(X)^2).
d1(cot(X), -1 / sin(X)^2).
d1(cot(X), -(1 + cot(X)^2)).
d1(arcsin(X), 1 / root(2, 1 - X^2)).
d1(arccos(X), -1 / root(2, 1 - X^2)).
d1(arctan(X), 1 / (1 + X^2)).
d1(arccot(X), -1 / (1 + X^2)).




% X * 1 = X
% 1 * X = X
simp(X * 1, X).
simp(1 * X, X).

% X * (-1) = -X
% -1 * X = -X
simp(X * (-1), -X).
simp(-1 * X, -X).

% 0 + X = X
% X + 0 = X
simp(X + 0, X).
simp(0 + X, X).

% 0 * X = 0
% X * 0 = 0
simp(0 * _, 0).
simp(_ * 0, 0).

% X^0 = 1
% X^1 = X
simp(_^0, 1).
simp(X^1, X).

% 0^ANYTHING = 0
% 1^ANYTHING = 1
simp(0^_, 0).
simp(1^_, 1).

% X - X = 0
simp(X - X, 0).

% simplifies any constant binary operation
simp(FAB, E) :-
    FAB =.. [_, A, B],
    number(A),
    number(B),
    E is FAB,
    !.


% tries to simplify in one step, then simplifies again
simplify(X, Z) :-
   simp(X, Y),
   !,
   simplify(Y, Z).
   

% applies the association rule trying to order the operands (only on + and *)
simplify(FFABC, Z) :-
    FFABC =.. [F, FAB, C],
    FAB =.. [F, A, B],
    assoc(F),
    sort([A, B, C], [A1, B1, C1]),
    [A, B, C] \= [A1, B1, C1],
    FA1B1 =.. [F, A1, B1],
    FFA1B1C1 =.. [F, FA1B1, C1],
    simplify(FFA1B1C1, Z),
    !.

% applies the association rule on - and /
simplify(FFABC, Z) :-
    FFABC =.. [F, FAB, C],
    FAB =.. [F, A, B],
    assoc2(F, G),
    sort([B, C], [B1, C1]),
    GB1C1 =.. [G, B1, C1],
    FAGB1C1 =.. [F, A, GB1C1],
    simplify(FAGB1C1, Z),
    !.
    

% tries to simplify a binary operation by applying simplification on both operands iff at least one can be simplified
simplify(FAB, Z) :-
    FAB =.. [F, A, B],
    simplify(A, C),
    simplify(B, D),
    (A \= C ; B \= D),
    FCD =.. [F, C, D],
    simplify(FCD, Z).


% tries to simplify the composition of functions: in f(x) simplifies x to x' and then simplifies f(x') (iff x != x')
simplify(FA, Z) :-
    FA =.. [F, A],
    simplify(A, A1),
    A \= A1,
    FA1 =.. [F, A1],
    simplify(FA1, Z),
    !.
    

% if no rule can be applied then X can only be simplified to itself
simplify(X, X).


comm('+').
comm('*').

assoc('+').
assoc('*').

assoc2('-', '+').
assoc2('/', '*').


% tries to first simplify the original function, then applies the derivative and then simplifies again
simpder(F, X, SDSF) :-
    simplify(F, SF),
    d(SF, X, DSF),
    simplify(DSF, SDSF).
