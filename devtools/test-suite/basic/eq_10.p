% result: VALID

fof(eq, axiom,
        (! [X,Y] :
        X = f(X,Y))).


fof(eq_a_b, axiom,
   p(a)).

fof(eq_a_b, axiom,
   f(a,b) = c).

fof(test_eq, conjecture,
    p(c)).
