%valid
fof(eq, axiom,
    (! [X] :
        X = f(X,b))).


fof(eq, axiom,
    (! [X] :
        f(X,a) = f(X,b))).


fof(eq, conjecture,
    (! [X] :
        (X = f(X,a)))).
