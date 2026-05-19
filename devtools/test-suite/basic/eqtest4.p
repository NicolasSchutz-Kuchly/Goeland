%NOT VALID


fof(eq_a_bb, axiom,
   f(a) = a).

fof(eq_a_bb, axiom,
   g(a) = c).

fof(test_eq, conjecture,
    (! [X] :
        g(f(X)) = c)).
