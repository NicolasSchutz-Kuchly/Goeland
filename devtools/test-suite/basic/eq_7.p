
fof(eq, axiom,
        (! [X,Y,Z] :
        f(X,Y,Z)=f(Y,X,Z))).


fof(eq_a_b, axiom,
   p(f(a,b,c))).


fof(test_eq, conjecture,
    p(f(b,a,c))).
