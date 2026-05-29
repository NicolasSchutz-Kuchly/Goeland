%test pour check si on gere plusieurs arguments
%valid

fof(ax1, axiom,
    ! [X1,X2,X3,X4] : f(X1,X2,X3,X4) = f(a,X2,c,X3)).

fof(ax1, axiom,
    ! [X1,X2,X3,X4] : f(X1,X2,X3,X4) = f(X3,b,X1,d)).


fof(axa, conjecture,
   f(a,b,c,d) = f(c,b,a,d)).
