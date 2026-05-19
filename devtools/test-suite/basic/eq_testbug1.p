%not valid

fof(ax16,axiom,
     a != b).

fof(coaa1,axiom,
      ? [W] :
        ( left(W)) ).


fof(co1zz,axiom,
      ? [X] :
        ( right(X)) ).


fof(ax12,axiom,
    ! [U] :
      ( left(U)
     => ~ goal(U) ) ).


fof(ax14,axiom,
    ! [U] :
      ( right(U)
     => rightbis(U) ) ).


fof(ax16,axiom,
    ! [U] :
      ( rightbis(U)
     => rightbisbis(U) ) ).

fof(ax16,axiom,
    ! [U] :
      ( rightbisbis(U)
     => goal(U) ) ).



fof(co1,conjecture,
     ~ ? [W,X] :
        ( left(W)
        & right(X)) ).
