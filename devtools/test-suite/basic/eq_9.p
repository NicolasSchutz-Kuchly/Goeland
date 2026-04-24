

fof(eq_a_b, axiom,
   g(a)).

fof(eq_a_b, axiom,
  (! [X] :  (~g(f(X))))).


fof(test_eq, conjecture,
            (! [Y] : (f(g(b)) = Y))).
