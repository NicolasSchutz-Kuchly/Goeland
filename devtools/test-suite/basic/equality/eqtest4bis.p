
%VALID

fof(eq_a_ba, axiom,
    (! [X] :
        X = a)).

fof(eq_a_bb, axiom,
   g(a) = c).

fof(test_eq, conjecture,
    (! [X] :
        g(X) = c)).
