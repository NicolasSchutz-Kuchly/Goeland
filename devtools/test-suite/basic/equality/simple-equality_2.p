% Trivial equality test to check if the congruence can go deep
% result: VALID

fof(eq, axiom, a = f(a)).
fof(eq, axiom, b = a).
fof(eq, axiom, p(a)).

fof(test, conjecture, 
    p(f(f(f(f(b)))))).


