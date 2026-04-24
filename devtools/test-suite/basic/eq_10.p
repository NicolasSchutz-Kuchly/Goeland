% result: VALID

fof(eq, axiom,
        (! [X,Y] :
        X = f(X,Y))).
fof(eq, axiom,
        (! [Z,Y] :
        f(Z,Y) = f(Y,Z))).

fof(eq_a_b, axiom,
   p(a)).

fof(eq_a_b, axiom,
   f(a,b) = c | f(b,a)=c | p(f(c,c))).

fof(test_eq, conjecture,
    p(c)).
