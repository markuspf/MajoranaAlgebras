InstallGlobalFunction(MAJORANA_Orbits,

    function(gens, t, setup)

    local   conjelts,
            orbitreps,
            i, j,
            orb,
            gen,
            elts,
            count,
            dim,
            p,
            q,
            h,
            g;

    conjelts := [1..t]*0;
    orbitreps := [];

    dim := Size(setup.coords);

    for i in [1..t] do
        if conjelts[i] = 0 then

            Add(orbitreps, i);
            conjelts[i] := [1..dim];

            orb := [i];
            elts := [[1..dim]];

            count := 0;

            for p in orb do

                count := count + 1;
                h := elts[count];

                for gen in gens do
                    q := gen[p];

                    g := [];

                    for j in h do
                        if j > 0 then
                            Add(g, gen[j]);
                        else
                            Add(g, -gen[-j]);
                        fi;
                    od;

                    if q < 0 then q := -q; fi;

                    if conjelts[q] = 0 then
                        Add(orb, q);
                        Add(elts, g);
                        conjelts[q] := g;
                    fi;
                od;
            od;
        fi;
    od;

    conjelts := DuplicateFreeList(conjelts);

    return rec( conjelts := conjelts,
                orbitreps := orbitreps  );

    end );

InstallGlobalFunction(MAJORANA_Orbitals,

    function(gens,t,setup)

    local   dim, i, j, orb;

    dim := Size(setup.coords);

    for i in [1..dim] do
        for j in [Maximum(i,t + 1)..dim] do

            if setup.pairorbit[i][j] = 0 then

                orb := MAJORANA_NewOrbital([i,j], gens, setup);

                if IsBound(setup.orbitals) then
                    Add(setup.orbitals, Immutable(orb));
                fi;
            fi;
        od;
    od;

    end );


InstallGlobalFunction( MAJORANA_NewOrbital,

    function( pnt, gens, setup)

    local orb, elts, count, y, p, h, q, z, g, i, j, k, pos, im, new, old, dim, sign, gen;

    # New Orbital, record as a new representative
    Add(setup.pairreps, pnt);

    # Number of points we're acting on
    dim := Size(setup.coords);

    # Orbit contains the point we're starting with
    orb := [ pnt ];
    # What does elts do?
    elts := [ [1..dim] ];

    count := 0;

    # The number of the orbit we're enumerating
    y := Size(setup.pairreps);

    setup.pairorbit[pnt[1]][pnt[2]] := y;
    setup.pairorbit[pnt[2]][pnt[1]] := y;

    # The element that's conguating is the identity
    setup.pairconj[pnt[1]][pnt[2]] := 1;
    setup.pairconj[pnt[2]][pnt[1]] := 1;

    # Orbit enumeration?
    for p in orb do

        count := count + 1;
        h := elts[count];

        # Orbit enumeration, every generator
        for gen in gens do

            # Generator applied to p?
            q := gen{p};

            # Make a permutation out of a signed permutation
            if q[1] < 0 then q[1] := -q[1]; fi;
            if q[2] < 0 then q[2] := -q[2]; fi;


            # the orbit in which this point lies
            z := setup.pairorbit[q[1]][q[2]];

            # Not detected yet
            if z = 0 then

                g := [];

                for i in h do
                    if i > 0 then
                        Add(g, gen[i]);
                    else
                        Add(g, -gen[-i]);
                    fi;
                od;

                Add( orb, q );
                Add( elts, g);

                if Product(g{orb[1]}) < 0 then
                    sign := -1;
                else
                    sign := 1;
                fi;

                setup.pairorbit[q[1]][q[2]] := sign*y;
                setup.pairorbit[q[2]][q[1]] := sign*y;

                pos := Position(setup.pairconjelts, g);

                if pos = fail then
                    Add(setup.pairconjelts, g);
                    pos := Size(setup.pairconjelts);
                fi;

                # The element that takes this pair to
                # the representative
                setup.pairconj[q[1]][q[2]] := pos;
                setup.pairconj[q[2]][q[1]] := pos;
            fi;
        od;
    od;

    return orb;

    end );

InstallGlobalFunction( MAJORANA_FindOrbitals,

    function(rep, gens, Omega)

    local new_pairreps, k, x;

    gens := List(gens, SignedPermList);

    # Construct the orbital structure

    rep.setup.orbitalstruct := MAJORANA_OrbitalStructure(gens, Omega, OnPosPoints);

    # Store representatives of the orbitals and add them to a corresponding hashmap

    new_pairreps := MAJORANA_UnorderedOrbitalReps(rep.setup.orbitalstruct);

    for x in new_pairreps do
        if not x in rep.setup.pairreps then
            # Only add new reps to preserve the ordering of the old reps
            Add(rep.setup.pairreps, x);
            # Record the position of the new rep in the hashmap
            k := Size(rep.setup.pairreps);
            rep.setup.pairrepsmap[ x ] := k;
            rep.setup.pairrepsmap[ Reversed(x) ] := k;
        fi;
    od;

end );

# Compute an orbital structure which has the
# following properties
#
# Input: G acting on Omega via Act

# Output: Orbital Structure
#         - A set of representatives of orbitals
#         - For any pair (i,j) efficiently
#           determine which orbital it belongs to
#         - For any pair (i,j) efficiently
#           compute an element g in G that takes (i,j)
#           to a representative in the set of
#           representatives
#         - iterate over orbit given a rep
#         - iterate over a transversal for
#           a stabilizer of a pair

InstallGlobalFunction(MAJORANA_OrbitalStructure,
# gens  - generators of a group acting on Omega
# Omega - the domain
# Act   - action of Group(gens) on Omega
function(gens, Omega, Act)
    local o, so, i, res;

    # Result will be an orbital structure that allows
    # some stuff to be done with orbitals
    res := rec( gens := gens, group := Group(gens), act := Act );

    # Orbits. Currently we'll just choose the
    # first element in each orbit as orbit rep
    res.orbits := Orbits( res.group, Omega, Act );

    # This is so we're able to determine which orbit the
    # first point of a pair is in, and then get an element
    # of G that maps said point to the orbit rep
    # Really what we want is a schreier trees/vectors here
    res.orbreps := [];
    res.orbnums := HashMap(Size(Omega));
    res.orbstabs := [];
    for o in [1..Length(res.orbits)] do
        Add(res.orbreps, res.orbits[o][1]);
        res.orbstabs[o] := rec( );
        res.orbstabs[o].stab := Stabilizer(res.group, res.orbits[o][1], Act);
        res.orbstabs[o].orbs := Orbits(res.orbstabs[o].stab, Omega, Act);
        res.orbstabs[o].orbnums := HashMap(Size(Omega));
        res.orbstabs[o].orbreps := [];
        for so in [1..Length(res.orbstabs[o].orbs)] do
            Add(res.orbstabs[o].orbreps, res.orbstabs[o].orbs[so][1]);
            for i in res.orbstabs[o].orbs[so] do
                res.orbstabs[o].orbnums[i] := so;
            od;
        od;

        for i in res.orbits[o] do
            res.orbnums[i] := o;
        od;
    od;

    return res;
end);

InstallGlobalFunction(MAJORANA_OrbitalRep,
function(os, pair)

    # Returns a representative (as a pair of elements of the G set) for the
    # orbital that contains <pair>.

    local fo, so, p;
    fo := os.orbnums[pair[1]];
    p := RepresentativeAction(os.group, pair[1], os.orbreps[fo] );
    so := os.orbstabs[fo].orbnums[os.act(pair[2], p)];
    return [ os.orbreps[fo], os.orbstabs[fo].orbreps[so] ];
end);

# TODO: fix this.
InstallGlobalFunction(MAJORANA_OrbitalCanonizingElement,
function(os, pair)

    # Returns a group elements that maps <pair> to its orbital representative
    # (as given by MAJORANA_OrbitalRep).

    local fo, so, p1, p2;

    fo := os.orbnums[pair[1]];
    p1 := RepresentativeAction(os.group, pair[1], os.orbreps[fo]);
    so := os.orbstabs[fo].orbnums[os.act(pair[2], p1)];
    p2 := RepresentativeAction( os.orbstabs[fo].stab, os.act(pair[2], p1)
                               , os.orbstabs[fo].orbreps[so]);

    return p1 * p2;
end);

InstallGlobalFunction(MAJORANA_OrbitalCanonizingElementInverse,
function(os, pair)

    # Returns a group elements that maps the orbital representative of <pair>
    # to <pair> itself. This will be the inverse of the output of
    # MAJORANA_OrbitalCanonizingElement( os, pair )

    local fo, so, p1, p2;

    fo := os.orbnums[pair[1]];
    p1 := RepresentativeAction(os.group, os.orbreps[fo], pair[1]);
    so := os.orbstabs[fo].orbnums[os.act(pair[2], p1)];
    p2 := RepresentativeAction(os.orbstabs[fo].stab, os.orbstabs[fo].orbreps[so], os.act(pair[2], p1));

    return p1 * p2;
end);

# Acting on sets of size 2
InstallGlobalFunction(MAJORANA_UnorderedOrbitalRep,
function(os, p)
    local a, b, oa, ob, r1, r2, p1;

    a := p[1];
    b := p[2];

    oa := os.orbnums[a];
    ob := os.orbnums[b];

    r1 := os.orbreps[oa];
    r2 := os.orbreps[ob];

    if r1 < r2 then
        p1 := RepresentativeAction(os.group, a, r1);
        ob := os.orbstabs[oa].orbnums[os.act(b, p1)];
        return [ r1, os.orbstabs[oa].orbreps[ob]];
    else
        p1 := RepresentativeAction(os.group, b, r2);
        oa := os.orbstabs[ob].orbnums[os.act(a, p1)];
        return [ r2, os.orbstabs[ob].orbreps[oa] ];
    fi;
end);

InstallGlobalFunction(MAJORANA_UnorderedOrbitalCanonizingElement,
function(os, pair)

    # Returns a group elements that maps <pair> to its orbital representative
    # (as given by MAJORANA_OrbitalRep).

    local a, b, oa, ob, r1, r2, p1, p2;

    a := pair[1];
    b := pair[2];

    oa := os.orbnums[a];
    ob := os.orbnums[b];

    r1 := os.orbreps[oa];
    r2 := os.orbreps[ob];

    if r1 < r2 then
        p1 := RepresentativeAction(os.group, a, r1);
        ob := os.orbstabs[oa].orbnums[os.act(b, p1)];
        p2 := RepresentativeAction(os.orbstabs[oa].stab, os.act(b, p1)
                                   , os.orbstabs[oa].orbreps[ob]);
    else
        p1 := RepresentativeAction(os.group, b, r2);
        oa := os.orbstabs[ob].orbnums[os.act(a, p1)];
        p2 := RepresentativeAction(os.orbstabs[ob].stab, os.act(a, p1)
                                   , os.orbstabs[oa].orbreps[ob]);
    fi;

    return p1 * p2;
end);

InstallGlobalFunction(MAJORANA_UnorderedOrbitalCanonizingElementInverse,
     {os, pair} -> MAJORANA_UnorderedOrbitalCanonizingElement(os, pair) ^ -1);

InstallGlobalFunction(MAJORANA_UnorderedOrbitalReps,
function(os)
    local reps, reps2, p, q;

    reps := Set(Union( List( [1..Length(os.orbreps)]
                       , k -> ListX(os.orbreps, os.orbstabs[k].orbreps
                                    , {x,y} -> MAJORANA_UnorderedOrbitalRep(os, [x,y]) ) ) ) );
    return reps;
end);

InstallGlobalFunction(MAJORANA_OrbitalTransversalIterator,
function( os, rep )
    local r, fo, so;

    fo := os.orbnums[rep[1]];
    so := os.orbstabs[fo].orbnums[rep[2]];

    r := rec( lorb := ShallowCopy(os.orbits[fo])
            , rorb := ShallowCopy(os.orbstabs[fo].orbs[so])
            , NextIterator := function(iter)
                local lrep, rrep, fact;

                lrep := RepresentativeAction(os.group, rep[1], iter!.lorb[1]);
                rrep := RepresentativeAction(os.orbstabs[fo].stab, rep[2], iter!.rorb[1]);
                Remove(iter!.rorb, 1);
                if IsEmpty(iter!.rorb) then
                    iter!.rorb := ShallowCopy(os.orbstabs[fo].orbs[so]);
                    Remove(iter!.lorb, 1);
                fi;

                fact := Factorization(os.group, rrep * lrep);
                return MappedWord(fact, GeneratorsOfGroup(FamilyObj(fact)!.freeGroup), os.gens);
            end
            , IsDoneIterator := iter -> iter!.lorb = []
            , ShallowCopy := iter -> rec( lorb := ShallowCopy(iter!.lorb)
                                        , rorb := ShallowCopy(iter!.rorb) )
            );
    return IteratorByFunctions(r);
end);

# For now, a disguised orbit algorithm which is probably better
# than computing RepresentativeAction all the time!
InstallGlobalFunction(MAJORANA_UnorderedOrbitalTransversalIterator,
function( os, rep )
    local r, fo, so;

    # Make sure we have *the* rep, not *a* rep
    rep := MAJORANA_UnorderedOrbitalRep(os, rep);



    r := rec( orb := HashMap()
            , new := [ [ rep, [] ] ]
            , NextIterator := function(iter)
                local i, pntp, pnt, npntp, npnt;

                pntp := Remove(iter!.new, 1);
                pnt := pntp[1];

                for i in [1..Length(os.gens)] do
                    npnt := Set(pnt, x -> os.act(x, os.gens[i]));
                    if not npnt in iter!.orb then
                        npntp := [ npnt, Concatenation(pntp[2], [i]) ];
                        iter!.orb[npnt] := npntp[2];
                        Add(iter!.new, npntp);
                    fi;
                od;
                if Length(pntp[2]) = 0 then
                    return One(os.group);
                else
                    return Product(List(pntp[2], i -> os.gens[i]));
                fi;
            end
            , IsDoneIterator := iter -> iter!.new = []
            , ShallowCopy := iter -> rec( orb := StructuralCopy(iter!.orb)
                                        , new := ShallowCopy(iter!.new) )
            );
    r.orb[rep] := [];
    return IteratorByFunctions(r);
end);

MAJORANA_SomeOrbTest :=
function()
    local ex, rep, gens, orbs, t, ra, fact, maresult;

    t := NanosecondsSinceEpoch();
    ex := A7();;
    t := NanosecondsSinceEpoch() - t;
    Print("ex  setup: ", t/1000000., "\n");

    t := NanosecondsSinceEpoch();
    rep := MAJORANA_SetUp(ex, 1, "AllAxioms");
    t := NanosecondsSinceEpoch() - t;
    Print("rep setup: ", t/1000000., "\n");

    t := NanosecondsSinceEpoch();
    gens := GeneratorsOfGroup(rep.group);
    gens := List(gens, x -> MAJORANA_FindPerm(x, rep, rep));
    gens := List(gens, SignedPermList);

    orbs := MAJORANA_OrbitalStructure( gens
                                     , [1..Length(rep.setup.coords)]
                                     , OnPosPoints );
    t := NanosecondsSinceEpoch() - t;
    Print("orb setup: ", t/1000000., "\n");

    t := NanosecondsSinceEpoch();
    ra := MAJORANA_OrbitalCanonizingElement(orbs, [216, 106]);
    t := NanosecondsSinceEpoch() - t;
    Print("repr calc: ", t/1000000., "\n");

    return [ra, rep, orbs];
end;

