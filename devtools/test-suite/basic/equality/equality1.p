%test pour voir si on arrive a utiliser plusieurs axiomes en meme temps

%valid l=4

fof(ax1, axiom,
    ! [X] : f(X) = g(X)).

fof(ax2, axiom,
    ! [Y] : g(g(Y)) = Y).

fof(ax3, axiom,
    ! [X] : h(X) = X).


fof(goal, conjecture,
    h(f(f(a))) = a).
