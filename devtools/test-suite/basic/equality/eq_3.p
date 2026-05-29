% checks whether the transitivity rule is validated by our equality reasoning
% result: VALID


fof(eq_a_ba, axiom,
   a = b).

fof(eq_a_b, axiom,
   c = d).

fof(eq_a_ac, axiom,
   g(g(g(g(a,d),b),c),d) = b).

 fof(eq_a_ac, axiom,
     g(a,a) = b).



fof(test_eq, conjecture, 
    a = g(a,b)).
