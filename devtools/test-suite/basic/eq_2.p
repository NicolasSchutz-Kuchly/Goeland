% checks whether the transitivity rule is validated by our equality reasoning
% result: VALID

fof(eq_a_a, axiom,
   b = c).

fof(eq_a_b, axiom,
   p(g(g(a)),b)).

fof(eq_a_c, conjecture,
   p(a,c)).

fof(eq, axiom,
    ! [X] :
    g(X) = f(X)).

fof(eq, axiom,
    ! [Y] :
    g(f(Y)) = f(Y)).
