#
# Solving linear equations over the integers/rationals by Dixon/Hensel lifting
#
# This is a GAP prototype which already works quite a bit faster than any code
# inside GAP, for reasonably large systems (thousands of equations)
#
# If you find any bugs, email markus.pfeiffer@morphism.de
#
# TODO:
# * Make a better implementation of the padics code. Its currently pretty brittle
#   and hacky
# * More tests
# * look at flint that has some of this functionality
# * Implement in C or Rust (or Julia)?
# * Parallelisation strategies
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
        n := (n - r)/p;
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
                Error("gcd is 2");
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

A := [[1/2, 1/3], [2,3]];
Ap := [[1/2, 1/3], [2,3], [5/2, 10/3]];

b := [1,1];

Read("pkg/A6Matrix.txt");
Read("pkg/A6Vector.txt");

# I think I want to use row-major, which means variables are in
# rows.

tmat := TransposedMat(mat);
tvec := TransposedMat(vec);
tvec1 := tvec[1];

sample1 := function()
    return MAJORANA_SolutionMatVecs_Padic( [[1,0,1],[0,0,0],[1,0,0]]
                                         , [0,0,1/3]
                                         , 11, 100);
end;

# Select the variables that we can solve for
# They are the ones that have no (possible) contribution 
# from he Nullspace
SelectSolvableVariables := function(semiech)
    if semiech.relations = [] then
        return semiech.heads;
    else
        return PositionsProperty(TransposedMat(semiech.relations), IsZero);
    fi;
end;

# This is ugly but reasonably fast
FindLCM := function(mat, vec)
    local row, e, lcm;

    lcm := 1;
    for row in mat do
        for e in row do
            if not IsZero(e) then
                lcm := LcmInt(lcm, DenominatorRat(e));
            fi;
        od;
    od;
    for e in vec do
        if not IsZero(e) then
            lcm := LcmInt(lcm, DenominatorRat(e));
        fi;
    od;
    return lcm;
end;

MakeIntSystem := function(mat, vec)
    local lcm, intmat, intvec;

    lcm := FindLCM(mat,vec);
    Info(InfoMajoranaLinearEq, 5,
         "found lcm ", lcm);

    return [lcm * mat, lcm * vec];
end;

Presolve :=
function(imat, p)
    local n, pmat, semiech, solvb;

    n := Length(imat);
    Info(InfoMajoranaLinearEq, 5,
         "number of variables: ", n);

    Info(InfoMajoranaLinearEq, 5,
         "reducing mod ", p);
    pmat := Z(p)^0 * imat;

    Info(InfoMajoranaLinearEq, 5,
         "finding semiechelon form");
    semiech := SemiEchelonMatTransformation(pmat);

    Info(InfoMajoranaLinearEq, 5,
         "selecting variables that have solution");
    solvb := SelectSolvableVariables(semiech);

    Info(InfoMajoranaLinearEq, 5,
        "number of solvable variables: ", Length(solvb));

    return rec( semiech := semiech, solvb := solvb );
end;

SelectedSolutionWithEchelonForm :=
function(semiech, vec, selection)
    local i, ncols, vno, x, z, row, lvec, sol;

    lvec := MutableCopyMat(vec);
    ncols := Length(vec);
    z := Zero(semiech.vectors[1][1]);
    sol := ListWithIdenticalEntries(Length(semiech.coeffs[1]), z);
    ConvertToVectorRepNC(lvec);
    ConvertToVectorRepNC(sol);
    if ncols <> Length(semiech.heads) then
        Error("");
    fi;

    for i in [1..ncols] do
        vno := semiech.heads[i];
        if vno <> 0 then
            x := lvec[i];
            if x <> z then
                AddRowVector(lvec, semiech.vectors[vno], -x);
                AddRowVector(sol, semiech.coeffs[vno], x);
            fi;
        fi;
    od;
    return [lvec, sol];
end;



#
# This function tries to solve the system xA = b, where
# A is a n x m matrix over the rational numbers, and b
# is a vector of length m over the rationals.
#
# It first converts the system into an integer system by
# finding the LCM l of all denominators of all entries in A
# and b. It is then true that any solution of x(lA) = lb is also
# a solution of xA = b.
#
# In a "presolving" step, the matrix lA is reduced modulo the prime
# p, put into semiechelon form and the variables for which a unique
# solution exists are selected. (TODO: Describe how these are selected)
#
# We then iterate solving  x(lA) = lb mod p, computing a p-adic expansion
# of a solution to the system x(lA) = lb.
# Once we reach a number of digits (currently max_iter) we try to compute
# the denominator of the solution. Once we have computed a denominator d,
# we solve x(lA) = d(lb) for x, and return x/d as the result.
#

# TODO: Turn the Print("#I ") into proper info-levels
# TODO: Find out why we drag around symmetric/non-symmetric solusitons
InstallGlobalFunction(MAJORANA_SolutionIntMatVecs_Padic,
function(intmat, intvec, p, max_iter)
    local pfam,
          intsol, intsolsym,
          intres, intressym,
          pre, pvec, pvecsym, solsym,
          done, nriter, coeffs, ppower, sol, x, y, i, dd,
          k, denom, vecd;

    pfam := PurePadicNumberFamily(p, max_iter);
    intsol := [1..Length(intmat)] * 0;
    intsolsym := [1..Length(intmat)] * 0;
    intres := MutableCopyMat(intvec);
    intressym := MutableCopyMat(intvec);

    Info(InfoMajoranaLinearEq, 5,
         "presolving...");
    pre := Presolve(intmat, p);
    pvec := Z(p)^0 * intres;
    pvecsym := Z(p)^0 * intressym;
    done := false;
    nriter := 0;
    coeffs := [];
    ppower := 1;

    #T just solve for the selected ones?
    while true do
        nriter := nriter + 1;
        sol := SelectedSolutionWithEchelonForm(pre.semiech, pvec, pre.solvb);
        solsym := SelectedSolutionWithEchelonForm(pre.semiech, pvecsym, pre.solvb);
        # Here we should only be testing the solved variables?
        if IsZero(sol[1]) then
            #  intsol := p * intsol;
            #T Matrix/vector op?
            #T this is also reasonably ugly...

            Add(coeffs, List(sol[2], IntFFE));

            x := List(sol[2], IntFFE);
            y := List(solsym[2], IntFFESymm);

            AddRowVector(intsol, x, ppower);
            AddRowVector(intsolsym, y, ppower);

            for i in [1..Length(sol[2])] do
                AddRowVector(intres, intmat[i], -x[i]);
                AddRowVector(intressym, intmat[i], -y[i]);
            od;

            Info(InfoMajoranaLinearEq, 10, "intsol:    ", intsol);
            Info(InfoMajoranaLinearEq, 10, "x:         ", x, " ", List(sol[2], IntFFESymm));
            Info(InfoMajoranaLinearEq, 10, "y:         ", List(solsym[2], IntFFE), " ", y);
            Info(InfoMajoranaLinearEq, 10, "intres:    ", intres);
            Info(InfoMajoranaLinearEq, 10, "intsol:    ", intsol);
            Info(InfoMajoranaLinearEq, 10, "intressym: ", intressym);
            Info(InfoMajoranaLinearEq, 10, "intsolsym: ", intsolsym);

            # Solution found?
            # TODO: Can we remove the pre.solvb?
            if IsZero(intressym{pre.solvb}) then
                Info(InfoMajoranaLinearEq, 5,
                     "found an integer solution");
                return [pre.solvb, intsolsym];
            else
                if nriter > max_iter then
                    Info(InfoMajoranaLinearEq, 5,
                         "trying to compute denominator");
                    coeffs := TransposedMat(coeffs);

                    # TODO: do we have to do them all?
                    
                    dd := [];
                    for k in [1..Length(pre.solvb)] do
                        Add(dd, PadicDenominator(coeffs[pre.solvb[k]], p, nriter));
                    od;
                    denom := Lcm(dd);

                    Info(InfoMajoranaLinearEq, 5,
                         "found denominator: ", denom);
                    if denom = 1 then
                        Info(InfoMajoranaLinearEq, 5,
                             "denominator of 1 should not happen, trying to solve using GAP's builtin method");
                        return [pre.solvb, SolutionIntMat(intmat, intvec), coeffs, intres, intsol];
                    else
                        vecd := denom * intvec;
                        # TODO: This is silly, if we are using the same parameters otherwise, we could just continue
                        #       with all the precomputed data we already have.
                        sol := MAJORANA_SolutionIntMatVecs_Padic(intmat, vecd, p, max_iter);
                        Info(InfoMajoranaLinearEq, 5,
                             "calling  of 1 should not happen, trying to solve using GAP's builtin method");
                        return [pre.solvb, sol[2]/denom];
                    fi;
                fi;

                intres := intres / p;
                intressym := intressym / p;

                pvec := Z(p)^0 * intres;
                pvecsym := Z(p)^0 * intressym;
                Info(InfoMajoranaLinearEq, 10, "pvec:    ", pvec);
                Info(InfoMajoranaLinearEq, 10, "pvecsym: ", pvecsym);
                ppower := ppower * p;
                if nriter > max_iter then
                    Error("");
                fi;
            fi;
        else
            # No rational solution exists
            Info(InfoMajoranaLinearEq, 5,
                 "there does not exist a rational solution");
            return fail;
        fi;
    od;
end);

InstallGlobalFunction(MAJORANA_SolutionMatVecs_Padic,
function(mat, vec, p, max_iter)
    local intsys;

    if not IsPrime(p) then
        Error("p has to be a prime");
    fi;
    if max_iter < 100 then
        # TODO: Should probably make a better guess about the
        #       number of iterations or not try to restrict the
        #       user.
        Info(InfoMajoranaLinearEq, 1,
             "warning: using less that 100 iterations is not recommended");
    fi;

    Info(InfoMajoranaLinearEq, 5,
         "number of variables: ", Length(mat), "\n");
    intsys := MakeIntSystem(mat, vec);

    return MAJORANA_SolutionIntMatVecs_Padic(intsys[1], intsys[2], p, max_iter);
end);
