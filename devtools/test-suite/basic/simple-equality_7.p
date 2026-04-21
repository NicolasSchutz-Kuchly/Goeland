% Trivial equality test to check that we don't loop-rewrite
% result: VALID

fof(eq, axiom, 
    (! [X,Y] :
    p(X,Y) = X)).


fof(eq, axiom,
    a = b).

fof(test_quant_1, conjecture, 
    p(a,a) = p(b,b)).


