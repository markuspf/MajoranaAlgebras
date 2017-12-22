
ConvertSparse := function(smat, p)
    local m, r, i, j, m2, maxrow, maxcol;

    maxrow := Maximum(List(smat![5]![5], x -> x[1]));
    maxcol := Maximum(List(smat![5]![5], x -> x[2]));
    Print("nonzero: ", maxrow, ", ", maxcol, "\n");

    Print("creating non-sparse primefield mat\n");
    r := ListWithIdenticalEntries(maxcol, Zero(GF(p)));
    ConvertToVectorRep(r);
    m := [];
    for i in [1..maxrow] do
        m[i] := ShallowCopy(r);
    od;

    Print("copy & convert to prime field mat\n");
    for i in mat![5]![5] do
        m[i[1],i[2]] := mat![5][i] * One(GF(p));
    od;

    return m;
end;



# FIXME: This function does a divide-and-conquer map/reduce
#        over a list. This should go in the GAP library
_FoldList2 := function(list, func, op)
    local k, s, old_s, r, i, len, n, nh, res, r1, r2;

    len := Length(list);
    if len = 0 then
        return 1;
    elif len = 1 then
        return func(list[1]);
    fi;

    res := List(list, func);

    k := len;
    s := 1;
    while k > 1 do
        r := k mod 2;
        old_s := s;
        k := QuoInt(k, 2);
        s := s * 2;
        i := s;
        while i <= k * s do
            if IsBound(res[i-old_s]) then
                r1 := res[i-old_s];
            else
                r1 := 1;
            fi;
            if IsBound(res[i]) then
                r2 := res[i];
            else
                r2 := 1;
            fi;
            res[i] := op(r1, r2);
            res[i-old_s] := 0;
            i := i + s;
        od;
        if r = 1 then
            k := k + 1;
            res[i] := res[i-old_s];
        fi;
    od;
    return res[ k * s ];
end;

# Solving linear equations over the integers/rationals by Dixon/Hensel lifting
#
# This is a GAP prototype which already works quite a bit faster than any code
# inside GAP, for reasonably large systems (thousands of equations)
#
# If you find any bugs, email markus.pfeiffer@morphism.de
#
# TODO:
# * Carry denominator forward
# * actually only solve the solvable variables.
# * Make a better implementation of the padics code. Its currently pretty brittle
#   and hacky
# * More tests
# * look at flint that has some of this functionality
# * Implement in C or Rust (or Julia)?
# * Parallelisation strategies
# * use meataxe64
#

# FIXME:
PadicLess := function(a,b)
    local fam, p, q_a, q_b, r_a, r_b, div;

    fam := FamilyObj(a);
    p := fam!.prime;

    r_a := p^(a![1]) * a![2];
    r_b := p^(b![1]) * b![2];
    div := p ^ (fam!.precision - 1);

    repeat
        q_a := QuoInt(r_a, div);
        q_b := QuoInt(r_b, div);
        if r_a < r_b then
            return true;
        elif r_a > r_b then
            return false;
        fi;
        r_a := QuoInt(r_a, div);
        r_b := QuoInt(r_b, div);
        div := div / p;
    until div = 1;
    return false;
end;


# FIXME: better way of detecting insufficient progress and abort?
PadicDenominator := function(number, max_iter)
    local n, thresh, tmp, big, little, bigf, littlef, biggest, fam,
          is_int;

    # Threshold where we consider something an integer
    # This should probably not be computed every time
    fam := FamilyObj(number);
    thresh := fam!.prime ^ QuoInt(fam!.precision, 2);

    Info(InfoMajoranaPadics, 10, " n: ", number, "\n");

    is_int := function(n)
        return (n![2] < thresh) or
               ((-n)![2] < thresh);
    end;

    if is_int(number) then
        return 1;
    fi;

    little := number;
    littlef := 1;
    big := number;
    bigf := 1;

    n := 0;
    while n < max_iter do
        n := n + 1;

        tmp := little + big;
        Info(InfoMajoranaPadics, 10
             , " lf: ", String(littlef, 16)
             , " bf: ", String(bigf, 16));
        Info(InfoMajoranaPadics, 10
             , " little: ", little
             , " big:    ", big);

        if is_int(tmp) then
            Info(InfoMajoranaPadics, 1, "PadicDenominator iterations: ", n);
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

    Info(InfoMajoranaPadics, 1
         , " failed to compute denominator after ", n, " iterations, giving up");
    return fail;
end;

# Compute LCM of denominators of a list of p-adics
# TODO: do we have to do them all?
PadicDenominatorList := function(list, max_iter)
    local denom, old_denom, k, iter, found;

    found := false;
    old_denom := 1;
    denom := 1;
    k := 1;

    repeat
        denom := PadicDenominator(old_denom * list[k], max_iter);

        if (denom <> fail) and (denom > 1) then
            found := true;
            old_denom := LcmInt(old_denom, denom);
        fi;

        k := k + 1;
        Info(InfoMajoranaLinearEq, 10, "current denominator: ", old_denom);
    until k > Length(list);

    if found then
        Info(InfoMajoranaLinearEq, 10, "found denominator: ", old_denom);
        return old_denom;
    else
        Info(InfoMajoranaLinearEq, 10, "failed to find");
        return fail;
    fi;
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

# This computes the lcm of each row of mat and each row of vecs
# and stores them in a list. It then chooses a prime that does not
# occur in any denominator. We will try to solve the system modulo
# that prime and lift solutions
MakeIntSystem := function(mat, vecs)
    local mult, intsys, mmults, vmults, p, lcm, lcm2;

    Info(InfoMajoranaLinearEq, 5,
         "computing row-wise denominator lcms" );

    mmults := List(mat, x -> _FoldList2(x, DenominatorRat, LcmInt));
    vmults := List(vecs, x -> _FoldList2(x, DenominatorRat, LcmInt));

    Info(InfoMajoranaLinearEq, 5,
         "choosing a prime that does not occur in any denominator");

    lcm := _FoldList2(Concatenation(mmults, vmults), IdFunc, LcmInt);
    Info(InfoMajoranaLinearEq, 5,
         "lcm: ", lcm);
    intsys := [ lcm * mat, lcm * vecs ];
    p := 1;
    repeat
        p := NextPrimeInt(p);
        Info(InfoMajoranaLinearEq, 5,
             "prime: ", p);
    until GcdInt(lcm, p) = 1;

    intsys[7] := p;

    if MAJORANA_LinAlg_Padic_Debug then
        TestIntSystem(intsys);
    fi;

    return intsys;
end;


# FIXME: This is ugly and inefficient
#        and possibly still not quite right
SelectS := function(pre)
    local i, j, n, k, x, r2
          , vars

          , rsel

          , column_select   # The columns in b that we are able to solve with
          , column_to_row   # column_to_row[i] is the row of vectors that has the pivot (leftmost entry = One(Field))
          , row_to_column
          , variable_to_row # which variable (column in x) is linked to row i
          , row_select      # probably better named "variable select"
          , variable_select #
          , nz, v, v2
          , c, r, coeffs, nze, nheads
          , rmask;


    # These are the columns that we can zero in a RHS (i.e. columns that have pivots)
    column_select := PositionsProperty(pre.semiech.heads, x -> not IsZero(x));

    # column_to_row[column] is the row in vectors that has the pivot in column
    column_to_row := ShallowCopy(pre.semiech.heads);
    # row_to_column[row] is the column that this row in vectors has the pivot in
    row_to_column := List(pre.semiech.vectors, v -> PositionProperty(v, x -> not (IsZero(x))));

    # first column in coefficients that is not zero
    # row_to_variable := List(pre.)ListWithIdenticalEntries(Length(pre.semiech.coeffs[1]), 0);

    n := Length(pre.semiech.coeffs[1]);
    variable_to_row := 0 * [1..n];
    for c in column_select do
        j := n;
        while IsZero(pre.semiech.coeffs[column_to_row[c]][j]) and j >= 0 do j := j - 1; od;
        if j > 0 then
            variable_to_row[j] := column_to_row[c];
        fi;
    od;

    variable_select := PositionsProperty(variable_to_row, x -> not IsZero(x));
    for r in pre.semiech.relations do
        for v in variable_select do
            # A relation involves a variable
            if not IsZero(r[v]) then
                nz := PositionsProperty(r, x -> not IsZero(x));

                for x in nz do
                    v2 := variable_to_row[x];
                    variable_to_row[x] := 0;
                    if v2 <> 0 then
                        r2 := row_to_column[v2];
                        row_to_column[v2] := 0;
                        column_to_row[r2] := 0;
                    fi;
                od;
            fi;
        od;
    od;

    pre.variable_to_row := variable_to_row;
    pre.column_to_row := column_to_row;
    pre.variable_select := PositionsProperty(variable_to_row, x -> not IsZero(x));
    pre.column_select := PositionsProperty(column_to_row, x -> not IsZero(x));
end;


# This puts the integer matrix imat into
# semiechelon form modulo the integer p
# TODO: This step could be done using meataxe64
Presolve :=
function(imat, p)
    local n, pmat, semiech, res;

    res := rec();

    Info(InfoMajoranaLinearEq, 5,
         "presolving...");

    n := Length(imat);
    Info(InfoMajoranaLinearEq, 5,
         "  number of variables: ", n);

    Info(InfoMajoranaLinearEq, 5,
         "  number of equations: ", Length(imat[1]));

    Info(InfoMajoranaLinearEq, 5,
         "  reducing mod ", p);
    pmat := Z(p)^0 * imat;
    ConvertToMatrixRep(pmat);

    Info(InfoMajoranaLinearEq, 5,
         "  finding semiechelon form");
    res.semiech := SemiEchelonMatTransformation(pmat);

    SelectS(res);
    Info(InfoMajoranaLinearEq, 5,
         "  number of solvable variables:   ", Length(res.variable_select));
    Info(InfoMajoranaLinearEq, 5,
         "done.");

    return res;
end;


SelectedSolutionWithEchelonForm :=
function(pre, vec)
    local i, ncols, vno, x, z, residue, soln;

    ncols := Length(vec);
    residue := MutableCopyMat(vec);
    ConvertToVectorRepNC(residue);
    # FIXME: If there are no coefficients then something
    #        is wrong anyway
    soln := ZeroMutable(pre.semiech.coeffs[1]);
    ConvertToVectorRepNC(soln);

    # "speed up" zero test
    z := Zero(vec[1]);
    for i in [1..Length(pre.column_select)] do
        vno := pre.column_to_row[pre.column_select[i]];
        x := residue[pre.column_select[i]];
        if x <> z then
            AddRowVector(residue, pre.semiech.vectors[vno], -x);
            AddRowVector(soln, pre.semiech.coeffs[vno], x);
        fi;
    od;
#    for i in [1..ncols] do
#        vno := semiech.heads[i];
#        if vno <> 0 then
#            x := residue[i];
#            if x <> z then
#                AddRowVector(residue, pre.semiech.vectors[vno], -x);
#                AddRowVector(soln, pre.semiech.coeffs[vno], x);
#            fi;
#        fi;
#    od;
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
# TODO:  return relations
#
# FIXME: Find out why we (whether we) have to drag around symmetric/non-symmetric
#        variants
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
function(pre, mat, b, p, iter_step)
    local
          # These are *integer* vectors
          tmp_soln, soln,
          residue,

          # These are vectors in GF(p)
          vec_p,
          soln_p,

          done, iterations, coeffs_padic, fam,
          ppower, sol, x, y, i,
          k, old_denom, denom, vecd, iter;

    # Accumulator for integer solution
    soln := ListWithIdenticalEntries(Length(mat), 0);

    # These are the *integer* residuals of the RHS
    # initially this is the RHS we're solving for
    residue := MutableCopyMat(b);

    done := false;
    iterations := 0;
    ppower := 1; # this is p^iterations;

    # digits in the p-adic expansion of the approximation to the solution
    # to xA = b
    fam := PurePadicNumberFamily(p, iter_step);
    coeffs_padic := List([1..Length(mat)], x -> PadicNumber(fam, 0));

    vec_p := residue * Z(p)^0;

    #T just solve for the selected ones?
    while true do
        iterations := iterations + 1;

        if iterations mod 100 = 0 then
            Info(InfoMajoranaLinearEq, 5, STRINGIFY(iterations, " iterations"));
        fi;

        # solve the system mod p
        vec_p := Z(p)^0 * residue;

        # Note that SelectedSolutionWithEchelonForm converts to vector rep
        soln_p := SelectedSolutionWithEchelonForm(pre, vec_p);

        if IsZero( soln_p.residue{ pre.column_select } ) then
            # Convert the solution from GF(p) to integers -p/2..p/2-1
            y := List(soln_p.solution, IntFFESymm);

            # they are the coefficients of the p-adic expansion of the denominator
            # coeffs_padic := coeffs_padic + List(y, c -> PadicNumber(fam, ppower * -c));
            coeffs_padic := coeffs_padic + List(y, c -> PadicNumber(fam, [iterations, c mod fam!.modulus ] ) );
             # c * ppower));

            AddRowVector(soln, y, ppower);

            for i in [1..Length(mat)] do
#                AddRowVector(residue, mat[i], -y[i]);
                residue{ pre.column_select } := residue{ pre.column_select } - y[i] * mat[i]{pre.column_select};
            od;

            Info(InfoMajoranaLinearEq, 10, "soln:    ", soln);
            Info(InfoMajoranaLinearEq, 10, "y:       ", y);
            Info(InfoMajoranaLinearEq, 10, "residue: ", residue);

            # Solution found?
            if IsZero(residue{ pre.column_select } ) then
                Info(InfoMajoranaLinearEq, 5,
                     "found an integer solution");
                return [soln, 1];
            else
                if iterations > iter_step then
                    Info(InfoMajoranaLinearEq, 5,
                         "reached iteration limit, trying to compute denominator");
                    # Compute the least common denominator of them all
                    denom := PadicDenominatorList( coeffs_padic{ pre.variable_select }, 50 * iter_step );
                    Info(InfoMajoranaLinearEq, 5,
                         "found denominator: ", denom);

                    # FIXME: Hack
                    if denom = fail then
                        denom := PadicDenominatorList( coeffs_padic{ pre.variable_select }, 10 * iter_step);
                    fi;

                    if denom = fail then
                        Info( InfoMajoranaLinearEq, 10
                              , "failed to find denominator trying with more p-adic places");

                        # FIXME: We could just extend the places we have here
                        tmp_soln := MAJORANA_SolutionIntMatVec_Padic(pre, mat, b, p, 3 * iter_step);
                        return tmp_soln;
                    elif denom = 1 then
                        Info(InfoMajoranaLinearEq, 5,
                             "denominator 1 should not happen, trying to solve using GAP's builtin method");
                        return [SolutionIntMat(mat, b), 1];
                    else
                        # TODO: This is silly, if we are using the same parameters otherwise, we could just continue
                        #       with all the precomputed data we already have.
                        Info(InfoMajoranaLinearEq, 5,
                             "solving system after multiplying b by denominator.");

                        tmp_soln := MAJORANA_SolutionIntMatVec_Padic(pre, mat, b * denom, p, iter_step);
                        return [ tmp_soln[1] / denom, tmp_soln[2] * denom ];
                    fi;
                fi;

                # The residue better be divisible by p now.
                residue{ pre.column_select } := residue{ pre.column_select } / p;
                ppower := ppower * p;
            fi;
        else
            Info(InfoMajoranaLinearEq, 5,
                 "there does not exist a rational solution");
            Error("err?");
            return fail;
        fi;
    od;
end);

# Solve for one right-hand-side
InstallGlobalFunction( MAJORANA_SolutionMatVec_Padic,
                       { mat, b, iter_step } -> MAJORANA_SolutionMatVecs_Padic(mat, [ b ], iter_step) );

# Solve for multiple right-hand-sides
InstallGlobalFunction(MAJORANA_SolutionMatVecs_Padic,
function(mat, vecs, max_iter)
    local intsys, pre, v, sol, denom, sols, p;

    intsys := MakeIntSystem(mat, vecs);
    p := intsys[7];

    pre := Presolve(intsys[1], p);

    return List(intsys[2], v -> MAJORANA_SolutionIntMatVec_Padic(pre, intsys[1], v, p, max_iter));
end);

## Plug
InstallGlobalFunction(MAJORANA_SolutionMatVecs_Plugin,
function(mat, vecs)
    local res, tmat, tvecs, tsols, intsys, pre, max_iter, i, v, sl, denom, unsol;

    max_iter := MAJORANA_LinAlg_Padic_Iterations;

    Info(InfoMajoranaLinearEq, 1, "Using p-adic expansion code...");
    Info(InfoMajoranaLinearEq, 1, " ", Length(mat[1]), " variables");
    Info(InfoMajoranaLinearEq, 1, " ", Length(mat), " equations");

    res := rec( );

    tmat := TransposedMat(mat);
    tvecs := TransposedMat(vecs);

    Info(InfoMajoranaLinearEq, 1, " zero rows: ", Length(PositionsProperty(tmat, IsZero)));

    intsys := MakeIntSystem(tmat, tvecs);

    pre := Presolve(intsys[1], intsys[7]);

    if pre.variable_select = [] then
        res.solutions := ListWithIdenticalEntries(Length(tmat), fail);
        res.mat := [];
        res.vec := [];
        return res;
    fi;

    tsols := [];
    # FIXME: This is a bit ugly: we thread the denominator through
    #        the loop to avoid recomputing denominators (because its expensive)
    denom := 1;
    sl := [,1];
    for v in intsys[2] do
        denom := LcmInt(denom,  sl[2]);
        sl := MAJORANA_SolutionIntMatVec_Padic(pre, intsys[1], v * denom, intsys[7], max_iter);
        Add(tsols, sl[1] / denom);
    od;

    res.solutions := TransposedMatMutable(tsols);

    for i in Difference([1..Length(res.solutions)], pre.variable_select) do
        res.solutions[i] := fail;
    od;

    # FIXME: It would be more efficient (in particular for large matrices)
    #        to just return the selector (As RP calls it)
    unsol := Difference([1..Length(mat)], pre.column_select);
    Print("unsolved (", Length(unsol), ") ", unsol, "\n");

    res.mat := mat{ unsol };
    res.vec := vecs{ unsol };
#    res.mat := [[]];
#    res.vec := [[]];

    return res;
end);

## Plug alternative
InstallGlobalFunction(MAJORANA_SolutionMatVecs_Plugin2,
function(mat, vecs)
    local res, tmat, tvecs, tsols, intsys, pre, max_iter, i, v, sl, denom, unsol;

    max_iter := MAJORANA_LinAlg_Padic_Iterations;

    Info(InfoMajoranaLinearEq, 1, "Using p-adic expansion code (inverse variant)...");
    Info(InfoMajoranaLinearEq, 1, " ", Length(mat[1]), " variables");
    Info(InfoMajoranaLinearEq, 1, " ", Length(mat), " equations");

    res := rec( );

    tmat := TransposedMat(mat);
#    tvecs := TransposedMat(vecs);

    Info(InfoMajoranaLinearEq, 1, " zero rows: ", Length(PositionsProperty(tmat, IsZero)));

    intsys := MakeIntSystem(tmat, [[]]);

    pre := Presolve(intsys[1], intsys[7]);

    if pre.variable_select = [] then
        res.solutions := ListWithIdenticalEntries(Length(tmat), fail);
        res.mat := [];
        res.vec := [];
        return res;
    fi;

    intsys[2] := [];
    for i in pre.column_select do
        v := [1..Length(intsys[1][1])] * 0;
        v[i] := 1;
        Add(intsys[2], v);
    od;

    tsols := [];
    # FIXME: This is a bit ugly: we thread the denominator through
    #        the loop to avoid recomputing denominators (because its expensive)
    denom := 1;
    sl := [,1];
    for v in intsys[2] do
        denom := LcmInt(denom,  sl[2]);
        sl := MAJORANA_SolutionIntMatVec_Padic(pre, intsys[1], v * denom, intsys[7], max_iter);
        Add(tsols, sl[1] / denom);
    od;

    res.solutions := TransposedMatMutable(tsols);

    for i in Difference([1..Length(res.solutions)], pre.variable_select) do
        res.solutions[i] := fail;
    od;

    # FIXME: It would be more efficient (in particular for large matrices)
    #        to just return the selector (As RP calls it)
    unsol := Difference([1..Length(mat)], pre.column_select);
    Print("unsolved (", Length(unsol), ") ", unsol, "\n");

    res.mat := mat{ unsol };
    res.vec := vecs{ unsol };
#    res.mat := [[]];
#    res.vec := [[]];

    return res;
end);
