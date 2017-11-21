# Solving linear equations over the integers/rationals by Dixon/Hensel lifting
#
# This is a GAP prototype which already works quite a bit faster than any code
# inside GAP, for reasonably large systems (thousands of equations)
#
# If you find any bugs, email markus.pfeiffer@morphism.de
#
# TODO:
# * actually only solve the solvable variables.
# * Make a better implementation of the padics code. Its currently pretty brittle
#   and hacky
# * More tests
# * look at flint that has some of this functionality
# * Implement in C or Rust (or Julia)?
# * Parallelisation strategies
# * use meataxe64
#
PadicList := function(padic)
    local result, n, p, r, i;

    result := [];
    n := padic![2];
    p := FamilyObj(padic)!.prime;

    for i in [1..padic![1]] do
        Add(result, 0);
    od;

    while n <> 0 do
        r := n mod p;
        Add(result, r);
        n := (n - r) / p;
    od;

    for i in [Length(result)+1..FamilyObj(padic)!.precision] do
        Add(result, 0);
    od;
    return result{[1..FamilyObj(padic)!.precision]};
end;

PadicDenominator := function(number, p, precision)
    local big
        , little
        , bigf
        , littlef
        , tmp, i
        , sig
        , ecnt
        , oldequot
        , tmpl
        , retv
        , n
        , PadicList, PadicLess, PadicAdd, PadicAssert;
    PadicAssert := function(number)
        if ForAny(number{[1..precision-1]}, x -> x >= p) then
            Error("invalid p-adic rep");
        fi;
    end;

    PadicAssert(number);
    PadicLess := function(a,b)
        local i;

        PadicAssert(a);
        PadicAssert(b);

        # Should be precision
        for i in [precision-1, precision-2..1] do
            if a[i] < b[i] then
                return true;
            elif a[i] > b[i] then
                return false;
            fi;
        od;
        return true;
    end;
    PadicAdd := function(a,b)
        local r, i;

        PadicAssert(a);
        PadicAssert(b);

        r := ShallowCopy(a + b);

        # Process carry
        for i in [1..Length(r) - 1] do
            while r[i] >= p do
                r[i+1] := r[i+1] + 1;
                r[i] := r[i] - p;
            od;
        od;
        return r;
    end;

    if Length(PositionsProperty(number, x -> (x=0) or x = (p-1)))/Length(number) > 3/4 then
        return 1;
    fi;

    little := number;
    littlef := 1;
    big := number;
    bigf := 1;

    n := 0;
    while true do
        n := n + 1;

        tmp := PadicAdd(little, big);

        Info(InfoMajoranaPadics, 10,
             STRINGIFY(Float(Length(PositionsProperty(tmp, x -> (x=0)))/Length(tmp)), " ",
                       Float(Length(PositionsProperty(tmp, x -> (x=(p-1))))/Length(tmp)), "\n"));

        # TODO better check that this is *Exact*
        #      by looking at the p-adic norm and deciding whether number has converged
        if Length(PositionsProperty(tmp, x -> (x=0) or x = (p-1)))/Length(tmp) > 3/4 then
            if bigf + littlef = 2 then
                # Error("gcd is 2");
            fi;
            return bigf + littlef;
        fi;

        if PadicLess(tmp, little) then
            little := tmp;
            littlef := bigf + littlef;
        elif PadicLess(big, tmp) then
            big := tmp;
            bigf := bigf + littlef;
        else
            Info(InfoMajoranaLinearEq, 1, "little <= tmp <= big: "
                 , little, " "
                 , tmp, " "
                 , big);
            Error("This shouldn't happen");
        fi;
    od;
end;

# This is slightly prettier than before, and still reasonably fast
_Fold := function(init, func, iterable)
    local result, i;
    result := init;
    for i in iterable do
        result := func(result, i);
    od;
    return result;
end;

_FoldMat := function(init, func, matrix)
    return _Fold( init
                , {v, row} -> _Fold(init, {v, entry} -> func(v, entry), row)
                , matrix);
end;
# FIXME: This does not work correctly...
# function(mat, vecs)
#    local matlcm, row, e, lcm;
#
#    return LcmInt( _FoldMat(1, {v, e} -> LcmInt(v, DenominatorRat(e)), mat)
#                 , _FoldMat(1, {v, e} -> LcmInt(v, DenominatorRat(e)), vecs));
#end;


FindLCM := function(mat, vecs)
    local r, c, res;
    res := 1;

    for r in mat do
        for c in r do
            res := LcmInt(res, DenominatorRat(c));
        od;
    od;
    for r in vecs do
        for c in r do
            res := LcmInt(res, DenominatorRat(c));
        od;
    od;

    return res;
end;

MakeIntSystem := function(mat, vecs)
    local lcm, intmat, intvec;

    lcm := FindLCM(mat,vecs);
    Info(InfoMajoranaLinearEq, 5,
         "found lcm ", lcm);

    return [lcm * mat, lcm * vecs];
end;

# Just to make sure we're not shooting ourselves
# in the foot with inconsistent entries.
TestIntSystem := function(intsys)
    local r, c;

    Info(InfoMajoranaLinearEq, 5,
         " testing integer system for integerness");
    for r in intsys[1] do
        for c in r do
            if DenominatorRat(c) <> 1 then
                Error(" /!\\ DENOMINATOR STILL NOT 1");
            fi;
        od;
    od;
    for r in intsys[2] do
        for c in r do
            if DenominatorRat(c) <> 1 then
                Error(" /!\\ DENOMINATOR STILL NOT 1");
            fi;
        od;
    od;
    Info( InfoMajoranaLinearEq, 5,
          " success.");
end;

SelectS := function(coeffs)
    local i, n, vars, c;

    vars := [];

    n := Length(coeffs[1]);
    for c in coeffs do
        i := n;
        while IsZero(c[i]) and i >= 0 do i := i - 1; od;
        if i > 0 then
            Add(vars, i);
        else
            # This shouldn't happen
        fi;
    od;
    return vars;
end;



# This puts the integer matrix imat into
# semiechelon form modulo the integer p
# TODO: This step could be done using meataxe64
Presolve :=
function(imat, p)
    local n, pmat, semiech, uniqvars, zeroablerhs;

    Info(InfoMajoranaLinearEq, 5,
         "presolving...");

    n := Length(imat);
    Info(InfoMajoranaLinearEq, 5,
         "number of variables: ", n);

    Info(InfoMajoranaLinearEq, 5,
         "number of equations: ", Length(imat[1]));

    Info(InfoMajoranaLinearEq, 5,
         "reducing mod ", p);
    pmat := Z(p)^0 * imat;

    Info(InfoMajoranaLinearEq, 5,
         "finding semiechelon form");
    semiech := SemiEchelonMatTransformation(pmat);

    uniqvars    := SelectS(semiech.coeffs);
    # Difference([1..n], AsSet(Concatenation(List(semiech.relations, x -> PositionsProperty(x, y -> not IsZero(y))))));
    zeroablerhs := PositionsProperty(semiech.heads, x -> not IsZero(x));

    Info(InfoMajoranaLinearEq, 5,
         "number of solvable variables: ", Length(uniqvars));
    Info(InfoMajoranaLinearEq, 5,
         "number of zeroable rhs:       ", Length(zeroablerhs));

    return rec( semiech := semiech
              , uniqvars := uniqvars
              , zeroablerhs := zeroablerhs );
end;


# FIXME: Why is "selection" unused?
#        The selection is a mask of variables that we hope
#        to be solving for, so in principle (if that selection
#        is small we could only add the selected entries)
#        not entirely sure whether its worth it
SelectedSolutionWithEchelonForm :=
function(semiech, vec, selection)
    local i, ncols, vno, x, z, residue, soln;

    ncols := Length(vec);
    residue := MutableCopyMat(vec);
    ConvertToVectorRepNC(residue);
    # FIXME: If there are no coefficients then something
    #        is wrong anyway
    soln := ZeroMutable(semiech.coeffs[1]);
    ConvertToVectorRepNC(soln);

    # "speed up" zero test
    z := Zero(vec[1]);

    for i in [1..ncols] do
        vno := semiech.heads[i];
        if vno <> 0 then
            x := residue[i];
            if x <> z then
                AddRowVector(residue, semiech.vectors[vno], -x);
                AddRowVector(soln, semiech.coeffs[vno], x);
            fi;
        fi;
    od;
    return rec( residue := residue
              , solution := soln );
end;


#
# This function tries to solve the systems xA = b_i for i in [1..k],
# where A is an n x m matrix over the rational numbers, and b_i are
# vectors of length m over the rationals.
#
# We refer to b_i as "right-hand-side"
#
# We first convert the system into an integer system by
# finding the LCM l of all denominators of all entries in A
# and all b_i.
# It is then true that any (integer or rational) solution of x(lA) = lb is also
# a solution of xA = b.
#
# In a "presolving" step, the matrix lA is reduced modulo the prime
# p, put into semiechelon form and the variables for which a unique
# solution exists are selected. (FIXME: Describe how these are selected)
#
# We then iterate solving  x(lA) = lb mod p, computing a p-adic expansion
# of a solution to the system x(lA) = lb.
#
# If we find an integer solution, we return it, if we hit a pre-determined
# number of digits, (currently max_iter) we try to compute the denominator
# of that fraction. (FIXME: Describe how the denominator is computed)
# If we computed a denominator d, we solve x(lA) = d(lb) for x
# (which now has an integer solution), and return x/d as the result.
#
# We refer to
#
# FIXME: Find out why we have to drag around symmetric/non-symmetric variants
#
# TODO: Add a "guess"/prevalue for the denominator (eases solving for multiple b)
#
# FIXME: The parameter "mat" is probably not needed
#
# FIXME: Can we not just extract the solvable part of the equations and solve that?
#
# TODO:  Can we use the fact we found integer solutions for some variables
#
InstallGlobalFunction(MAJORANA_SolutionIntMatVec_Padic,
function(pre, mat, b, p, max_iter)
    local
        # hack
        nzh,

          # These are *integer* vectors
          soln, soln_sym,
          residue, residue_sym,

          # These are vectors in GF(p)
          vec_p, vec_p_sym,
          soln_p, soln_p_sym,

          done, iterations, coeffs, ppower, sol, x, y, i,
          k, denom, vecd;

    # Accumulator for integer solution
    soln := ListWithIdenticalEntries(Length(mat), 0);
    soln_sym := ListWithIdenticalEntries(Length(mat), 0);

    # These are the *integer* residuals of the RHS
    # initially this is the RHS we're solving for
    residue := MutableCopyMat(b);
    residue_sym := MutableCopyMat(b);

    done := false;
    iterations := 0;
    ppower := 1; # this is p^iterations;

    # digits in the p-adic expansion of the approximation to the solution
    # to xA = b
    coeffs := [];
    vec_p := residue * Z(p)^0;
    vec_p_sym := residue_sym * Z(p)^0;

    #T just solve for the selected ones?
    while true do
        iterations := iterations + 1;

        if iterations mod 100 = 0 then
            Info(InfoMajoranaLinearEq, 5, STRINGIFY(iterations, " iterations"));
        fi;

        # solve the system mod p
        vec_p := Z(p)^0 * residue;
        vec_p_sym := Z(p)^0 * residue_sym;

        # Note that SelectedSolutionWithEchelonForm converts to vector rep
        soln_p := SelectedSolutionWithEchelonForm(pre.semiech, vec_p, pre.uniqvars);
        soln_p_sym := SelectedSolutionWithEchelonForm(pre.semiech, vec_p_sym, pre.uniqvars);

        if IsZero( soln_p.residue{ pre.zeroablerhs } ) then

            # Convert the solution from GF(p) to integers 0..p-1 and -p/2..p/2-1
            x := List(soln_p.solution, IntFFE);
            y := List(soln_p_sym.solution, IntFFESymm);

            # they are the coefficients of the p-adic expansion of the denominator
            Add(coeffs, x);

            # FIXME: better way?
            AddRowVector(soln, x, ppower);
            AddRowVector(soln_sym, y, ppower);

            for i in [1..Length(mat)] do
                AddRowVector(residue, mat[i], -x[i]);
                AddRowVector(residue_sym, mat[i], -y[i]);
            od;

            Info(InfoMajoranaLinearEq, 10, "soln:        ", soln);
            Info(InfoMajoranaLinearEq, 10, "soln_sym:    ", soln_sym);
            Info(InfoMajoranaLinearEq, 10, "x:           ", x);
            Info(InfoMajoranaLinearEq, 10, "y:           ", y);
            Info(InfoMajoranaLinearEq, 10, "residue:     ", residue);
            Info(InfoMajoranaLinearEq, 10, "residue_sym: ", residue_sym);

            # Solution found?
            if IsZero(residue_sym{ pre.zeroablerhs } ) then
                Info(InfoMajoranaLinearEq, 5,
                     "found an integer solution");
                return [pre.uniqvars, soln_sym];
            else
                if iterations > max_iter then
                    Info(InfoMajoranaLinearEq, 5,
                         "reached iteration limit, trying to compute denominator");
                    coeffs := TransposedMat(coeffs);

                    # TODO: do we have to do them all?
                    # FIXME:
                    denom := 1;
                    for k in [1..Length(pre.uniqvars)] do
                        denom := LcmInt(denom, PadicDenominator(coeffs[pre.uniqvars[k]], p, iterations));
                    od;

                    Info(InfoMajoranaLinearEq, 5,
                         "found denominator: ", denom);
                    if denom = 1 then
                        Info(InfoMajoranaLinearEq, 5,
                             "denominator of 1 should not happen, trying to solve using GAP's builtin method");
                        Error("why you little?");
                        return [pre.uniqvars, SolutionIntMat(mat, b), coeffs, residue, soln];
                    else
                        # TODO: This is silly, if we are using the same parameters otherwise, we could just continue
                        #       with all the precomputed data we already have.
                        Info(InfoMajoranaLinearEq, 5,
                             "solving system after multiplying b by denominator.");

                        soln := MAJORANA_SolutionIntMatVec_Padic(pre, mat, b * denom, p, max_iter);
                        return [pre.uniqvars, soln[2]/denom];
                    fi;
                fi;

                # The residue better be divisible by p now.
                residue{ pre.zeroablerhs } := residue{ pre.zeroablerhs } / p;
                residue_sym{ pre.zeroablerhs } := residue_sym{ pre.zeroablerhs } / p;

                ppower := ppower * p;
            fi;
        else
            Error("boop");
            Info(InfoMajoranaLinearEq, 5,
                 "there does not exist a rational solution");
            return fail;
        fi;
    od;
end);

# Solve for one right-hand-side
InstallGlobalFunction( MAJORANA_SolutionMatVec_Padic,
                       { mat, b, p, max_iter } -> MAJORANA_SolutionMatVecs_Padic(mat, [ b ], p, max_iter) );

# Solve for multiple right-hand-sides
InstallGlobalFunction(MAJORANA_SolutionMatVecs_Padic,
function(mat, vecs, p, max_iter)
    local intsys, pre;

    if not IsPrime(p) then
        Error("p has to be a prime");
    fi;

    intsys := MakeIntSystem(mat, vecs);
    TestIntSystem(intsys);

    pre := Presolve(intsys[1], p);

    return List(intsys[2], v -> MAJORANA_SolutionIntMatVec_Padic(pre, intsys[1], v, p, max_iter));
end);
