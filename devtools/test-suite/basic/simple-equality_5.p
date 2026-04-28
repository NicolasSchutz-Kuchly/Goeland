% Trivial equality test to check that we don't loop-rewrite
% result: VALID

fof(eq, axiom, a = b).

fof(eq, axiom, c = d).

fof(eq, axiom, e = g).

fof(eq, axiom, p(f(a, c, d))).

fof(eq, axiom, p(f(d, b , e))).

fof(test, conjecture, 
    p(f(b, d , c))).


