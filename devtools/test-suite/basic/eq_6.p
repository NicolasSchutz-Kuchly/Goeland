% checks whether the transitivity rule is validated by our equality reasoning


fof(pel55_3,axiom,
     a = b).

fof(pel55_3,axiom,
     p(a)).

fof(pel55_3,axiom,
    ( a = e
        | a = f ) ).


fof(test_eq, conjecture,
    p(e)).
