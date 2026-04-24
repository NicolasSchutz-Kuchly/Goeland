% Trivial equality test to check that we don't loop-rewrite
% result: VALID

fof(eq, axiom, a = b).

fof(eq, axiom, c = d).

fof(eq, axiom, e = f).

fof(eq, axiom, p(a, c, d)).

fof(eq, axiom, p(d, b , f)).

fof(test, conjecture, 
    p(b, d , c)).


