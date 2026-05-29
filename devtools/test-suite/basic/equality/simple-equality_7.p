% Trivial equality test to check that we don't loop-rewrite
% result: VALID

fof(eq, axiom, 
    (! [X,Y] :
    f(X,Y) = X)).


fof(eq, axiom,
    a = b).

fof(test_quant_1, conjecture, 
    f(a,a) = f(b,c)).


