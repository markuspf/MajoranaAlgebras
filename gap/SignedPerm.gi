BindGlobal( "TrimSignedPerm",
function(p)
    local ls;
    ls := Length(p![2]);
    while ls > 0 and IsZero(p![2][ls]) do ls := ls - 1; od;
    p![3] := Maximum(LargestMovedPoint(p![1]), ls);
    p![2] := (p![2]){[1..p![3]]} + ListWithIdenticalEntries(p![3], Z(2) * 0);
    return p;
end);


BindGlobal( "SignedPermList",
function(l)
    local sp, s, ts;

    sp := [];

    # Signs
    s := PositionsProperty(l, x -> x < 0);
    l{s} := -l{s};

    sp![1] := PermList(l);
    if sp![1] = fail then
        ErrorNoReturn("l does not define a permutation");
    fi;

    sp![2] := ListWithIdenticalEntries(Length(l), Z(2) * 0);
    sp![2]{s} := List(s, x -> Z(2)^0);

    TrimSignedPerm(sp);
    ConvertToVectorRep(sp![2]);

    return Objectify( SignedPermType, sp );
end);

BindGlobal( "ListSignedPerm",
function( arg )
    local sp, len, p, s, l, i;

    sp := arg[1]; p := sp![1]; s := sp![2];

    if Length(arg) = 2 then
        len := arg[2];
    else
        len := Length(s);
    fi;

    l := ListPerm(p, len);

    for i in [ 1 .. len ] do
        if IsBound(s[i]) and IsOne(s[i]) then
            l[i] := -l[i];
        fi;
    od;

    return l;

end );

BindGlobal( "SignedPerm",
function(p, s)
    return Objectify( SignedPermType, TrimSignedPerm([ p, s ]));
end);

InstallMethod(ViewObj, "for signed permutations",
  [ IsSignedPermRep ],
function(sp)
    Print("<signed permutation ", sp![1], ", ", sp![2], ">");
end);

InstallMethod(PrintObj, "for signed permutations",
[ IsSignedPermRep ],
function(sp)
    Print("<signed permutation ", sp![1], ", ", sp![2], ">");
end);

InstallMethod(\*, "for signed permutations",
  [ IsSignedPermRep, IsSignedPermRep ],
function(l, r)
    local sp;
    return Objectify(SignedPermType, TrimSignedPerm( [ l![1] * r![1]
                                     , Permuted(Zero(r![2]) + l![2], r![1]) + r![2] ] ) );
end);

InstallMethod(InverseOp, "for signed permutations",
  [ IsSignedPermRep ],
function(sp)
    return Objectify(SignedPermType, TrimSignedPerm([ sp![1]^-1, Permuted(sp![2], sp![1]^-1) ]) );
end);

InstallMethod(OneImmutable, "for signed permutations",
              [ IsSignedPermRep ],
function(sp)
    return Objectify(SignedPermType, [ (), [] ]);
end);

InstallMethod(OneMutable, "for signed permutations",
              [ IsSignedPermRep ],
function(sp)
    return Objectify(SignedPermType, [ (), [] ]);
end);

InstallMethod(IsOne, "for signed permutations",
  [ IsSignedPermRep ],
function(sp)
    return IsOne(sp![1]) and IsZero(sp![2]);
end);

InstallMethod(\^, "for an integer and a signed permutation",
  [ IsInt, IsSignedPermRep ],
function(pt, sp)
    local spt, sign;

    if pt < 0 then
        spt := -pt;
        sign := -1;
    else
        spt := pt;
        sign := 1;
    fi;

    if IsBound(sp![2][spt]) and IsOne(sp![2][spt]) then
        sign := -sign;
    fi;
    return sign * (spt^sp![1]);
end);

InstallMethod( \=, "for a signed permutation and a signed permutation",
               [ IsSignedPermRep, IsSignedPermRep ],
function(l,r)
    # Trim?
    if l![1] = r![1] then
        return l![2] = r![2];
    fi;
    return false;
end);

InstallMethod( \<, "for a signed permutation and a signed permutation",
               [ IsSignedPermRep, IsSignedPermRep ],
function(l,r)
    # Trim?
    if l![1] < r![1] then
        return true;
    elif l![1] = r![1] then
        return l![2] < r![2];
    fi;
    return false;
end);

# for an int and a signed perm
InstallGlobalFunction(OnPosPoints,
    { pnt, elm } -> pnt ^ elm![1]);

InstallTrueMethod( IsGeneratorsOfMagmaWithInverses
                 , IsSignedPermCollection );



#### bla

BindGlobal( "SignedPermL",
function(list)
    return Objectify( SignedPermListType, [ p ]));
end);

InstallMethod(ViewObj, "for signed permutations (list rep)",
  [ IsSignedPermListRep ],
function(sp)
    Print("<signed permutation in list rep>");
end);

InstallMethod(PrintObj, "for signed permutations",
[ IsSignedPermListRep ],
function(sp)
    Print("<signed permutation ", sp![1], ", ", sp![2], ">");
end);

InstallMethod(\*, "for signed permutations",
  [ IsSignedPermListRep, IsSignedPermListRep ],
function(l, r)
    local sp;
    return Objectify(SignedPermType, TrimSignedPerm( [ l![1] * r![1]
                                     , Permuted(Zero(r![2]) + l![2], r![1]) + r![2] ] ) );
end);

InstallMethod(InverseOp, "for signed permutations",
  [ IsSignedPermListRep ],
function(sp)
    return Objectify(SignedPermType, TrimSignedPerm([ sp![1]^-1, Permuted(sp![2], sp![1]^-1) ]) );
end);

InstallMethod(OneImmutable, "for signed permutations",
              [ IsSignedPermListRep ],
function(sp)
    return Objectify(SignedPermListType, [ [] ]);
end);

InstallMethod(OneMutable, "for signed permutations",
              [ IsSignedPermListRep ],
function(sp)
    return Objectify(SignedPermListType, [ [] ]);
end);

InstallMethod(IsOne, "for signed permutations",
  [ IsSignedPermListRep ],
function(sp)
    return IsEmpty(sp![1]);
end);

InstallMethod(\^, "for an integer and a signed permutation",
  [ IsInt, IsSignedPermListRep ],
function(pt, sp)
    local spt, sign;

    if pt < 0 then
        spt := -pt;
        sign := -1;
    else
        spt := pt;
        sign := 1;
    fi;

    return sign * (sp![1][spt]);
end);

InstallMethod( \=, "for a signed permutation and a signed permutation",
               [ IsSignedPermListRep, IsSignedPermListRep ],
function(l,r)
    # Trim?
    return l![1] = r![1];
end);

InstallMethod( \<, "for a signed permutation and a signed permutation",
               [ IsSignedPermListRep, IsSignedPermListRep ],
function(l,r)
    return l![1] < r![1];
end);
