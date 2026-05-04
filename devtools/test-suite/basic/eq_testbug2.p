fof(ax1, axiom,
    ! [X] : f(X) = g(X)).

fof(ax2, axiom,
    ! [X] : g(X) = f(f(X))).

fof(goal, axiom,
    p(f(f(a)))).

fof(goal, conjecture,
    p(a)).
