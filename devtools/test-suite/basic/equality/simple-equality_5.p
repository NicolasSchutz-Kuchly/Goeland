% Trivial equality test to check that we don't loop-rewrite
% result: VALID

fof(eq, axiom, a = b).

fof(eq, axiom, p(f(a, c, d))).

fof(eq, axiom, p(a)).

fof(eq, axiom, c = d).

fof(eq, axiom, (e = d )).



fof(test, conjecture, 
    p(f(b, d , c))).


