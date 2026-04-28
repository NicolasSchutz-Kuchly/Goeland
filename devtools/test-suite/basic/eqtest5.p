%NOT VALID

%VALID


fof(eq_a_bd, axiom,
    (! [Y] :
        g(f(Y)) = Y)).

fof(eq_a_bb, axiom,
   b = c).

fof(eq_a_bb, axiom,
    (! [X] :
        g(X)=f(X))).

fof(eq_a_bb, axiom,
   p(g(g(a)),b)).


fof(test_eq, conjecture,
    p(a,c)).
