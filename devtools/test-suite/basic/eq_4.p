% checks whether the transitivity rule is validated by our equality reasoning
% result: VALID


fof(eq_a_ba, axiom,
   a = f(a)).

fof(eq_a_b, axiom,
   p(a)).


fof(test_eq, conjecture, 
    p(f(a))).
