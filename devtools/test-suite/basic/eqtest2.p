%VALID

fof(f_is_constant_b, axiom,
    f(a) = b).

fof(eq_a_bb, axiom,
   g(b) = c).

fof(test_eq, conjecture,
    (? [X] :
        g(f(X)) = c)).
