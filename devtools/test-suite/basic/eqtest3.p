%VALID

fof(eq_a_ba, axiom,
    (! [X] :
        X = a)).

fof(eq_a_bd, axiom,
    (! [X] :
        f(X) = b)).

fof(test_eq, conjecture,
    f(a)=b).
