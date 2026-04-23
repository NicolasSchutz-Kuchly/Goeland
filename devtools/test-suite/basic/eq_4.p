% checks whether the transitivity rule is validated by our equality reasoning
% result: VALID


fof(eq, axiom,
                   (! [X] :
                   X = f(X))).

fof(eq_a_b, axiom,
   p(a)).


fof(eq_a_b, axiom,
   a=b).

fof(test_eq, conjecture, 
    p(f(b))).
