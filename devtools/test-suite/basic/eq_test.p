% not valid

fof(pel55_2_1,axiom,
    p(b) ).


fof(pel55_3,axiom,
    ! [X] :
      ( p(X)
     => ( X = a
        | X = b )) ).


fof(test_eq, conjecture,
    a = b).
