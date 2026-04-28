%VALID

fof(eq_a_ba, axiom,
   f(a)=b).

fof(eq_a_ba, axiom,
   g(b) = c).

fof(test_eq, conjecture, 
    g(f(a)) = c).
