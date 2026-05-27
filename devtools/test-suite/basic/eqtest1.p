%VALID

fof(eq_a_ba, axiom,
   f(a)=b | g(f(a))=e).

fof(eq_a_ba, axiom,
   g(b) = c).

fof(eq_a_ba, axiom,
   e = c).

fof(test_eq, conjecture, 
    g(f(a)) = c).
