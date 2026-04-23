% Trivial equality test to check that we don't loop-rewrite
% result: VALID

fof(eq, axiom, 
    (! [X] :
    X = a)).


fof(eq, axiom,
    p(a) ).

fof(test_quant_1, conjecture, 
    p(b)).


