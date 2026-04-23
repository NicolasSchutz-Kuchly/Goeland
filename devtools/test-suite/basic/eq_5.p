% checks whether the transitivity rule is validated by our equality reasoning
% result: VALID

fof(eq, axiom,
        (! [X] :
        X = a)).


fof(eq_a_b, axiom,
   p(a)).


fof(test_eq, conjecture, 
    (! [X] : p(X))).
