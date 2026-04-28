% checks whether the transitivity rule is validated by our equality reasoning
% result: VALID

fof(eq_a_b, axiom,
   p(a)).

fof(eq_a_b, axiom,
     p(b)).



fof(eq_a_b, axiom,
   f(a) = f(b)).


