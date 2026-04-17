% Trivial equality test to check that we don't loop-rewrite
% result: VALID

fof(eq, axiom, a = f(a,b)).


fof(test, conjecture, 
    f(f(a,b),b)=a).
