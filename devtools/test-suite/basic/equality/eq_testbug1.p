%not valid

fof(eq,axiom,
    a != b).

fof(coaa1,axiom,
( left(a)) ).

fof(co1zz,axiom,
( right(b)) ).

fof(ax12,axiom,
    ! [X] :
      ( left(X)
     => ~ goal(X) ) ).

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

fof(ax2, conjecture,
    $false).
