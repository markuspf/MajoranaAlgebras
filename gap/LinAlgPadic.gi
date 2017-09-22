

fam := PurePadicNumberFamily(5,100);
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
#    PadicList := function(padic)
#        local result, n, p, r, i;
#
#        result := [];
#        n := padic![2];
#        p := FamilyObj(padic)!.prime;
#
#        for i in [1..padic![1]] do
#            Add(result, 0);
#        od;
#
#        while n <> 0 do
#            r := n mod p;
#            Add(result, r);
#            n := (n - r)/p;
#        od;
#
#        for i in [Length(result)+1..FamilyObj(padic)!.precision] do
#            Add(result, 0);
#        od;
#        return result{[1..FamilyObj(padic)!.precision]};
#    end;
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

        # TODO better check that this is *Exact*
        if Length(PositionsProperty(tmp, x -> (x=0) or x = (p-1)))/Length(tmp) > 3/4 then
            if bigf + littlef = 2 then
                Error("gcd is 2");
            fi;
            return bigf + littlef;
        fi;

        # TODO: There must be a more efficient way to do this
        if PadicLess(tmp, little) then
            little := tmp;
            littlef := bigf + littlef;
        elif PadicLess(big, tmp) then
            big := tmp;
            bigf := bigf + littlef;
        else
            Print("#I little <= tmp <= big: "
                 , little, " "
                 , tmp, " "
                 , big, "\n");
            Error("blerg");
        fi;
    od;
end;

A := [[1/2, 1/3], [2,3]];
b := [1,1];

Read("pkg/A5Matrix.txt");
Read("pkg/A5Vector.txt");

# I think I want to use row-major, which means variables are in
# rows.

mat1 := TransposedMat(mat);
mat2 := mat1{[1..100]};
vec1 := TransposedMat(vec)[1];

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
    Print("#I found lcm ", lcm, "\n");

    return [lcm * mat, lcm * vec];
end;

Presolve :=
function(imat, p)
    local n, pmat, semiech, solvb;

    n := Length(imat);
    Print("#I number of variables: ", n, "\n");

    Print("#I reducing mod ", p, "\n");
    pmat := Z(p)^0 * imat;

    Print("#I finding semiechelon form\n");
    semiech := SemiEchelonMatTransformation(pmat);

    Print("#I selecting variables that have solution\n");
    solvb := SelectSolvableVariables(semiech);

    Print("#I number of solvable variables: ", Length(solvb), "\n");

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
# solution exists are selected. (TODO: Describe how these are selected
# those)
#
# We then iterate solving  x(lA) = lb mod p, computing a p-adic expansion
# of a solution to the system x(lA) = lb.
# Once we reach a number of digits (currently max_iter) we try to compute
# the denominator of the solution. Once we have computed a denominator d,
# we solve x(lA) = d(lb) for x, and return x/d as the result.
#
InstallGlobalFunction(MAJORANA_SolutionIntMatVecs_Padic,
function(intmat, intvec, p, max_iter)
    local pfam,
          intsol,
          intres,
          pre, pvec,
          done, nriter, coeffs, ppower, sol, x, i, dd,
          k, denom, vecd;

    pfam := PurePadicNumberFamily(p, max_iter);
    intsol := [1..Length(intmat)] * 0;
    intres := MutableCopyMat(intvec);

    Print("#I Presolving...\n");
    pre := Presolve(intmat, p);
    pvec := Z(p)^0 * intvec;
    done := false;
    nriter := 0;
    coeffs := [];
    ppower := 1;
    
    #T just solve for the selected ones?
    while true do
        nriter := nriter + 1;
        sol := SelectedSolutionWithEchelonForm(pre.semiech, pvec, pre.solvb);

        # Here we should only be testing the solved variables?
        if IsZero(sol[1]) then
            #  intsol := p * intsol;
            #T Matrix/vector op?
            #T this is also reasonably ugly...
            x := List(sol[2], IntFFE);
            Add(coeffs, List(sol[2], IntFFE));

            AddRowVector(intsol, x, ppower);
            for i in [1..Length(sol[2])] do
                AddRowVector(intres, intmat[i], -x[i]);
            od;

            # Solution found?
            if IsZero(intres{pre.solvb}) then
                Print("#I found an integer solution\n");
                return [pre.solvb, intsol];
            else
                if nriter > max_iter then
                    Print("#I Trying to find denominator\n");
                    coeffs := TransposedMat(coeffs);

                    dd := [];
                    for k in [1..Length(pre.solvb)] do
                        Add(dd, PadicDenominator(coeffs[pre.solvb[k]], p, nriter));
                    od;
                    denom := Lcm(dd);

                    Print("#I Denominator: ", denom, "\n");
                    if denom = 1 then
                        Error("A denominator of 1 should not happen!");
                        return [pre.solvb, SolutionIntMat(intmat, intvec), coeffs];
#                        return [pre.solvb, intsol, coeffs];
                    else
                        vecd := denom * intvec;
                        sol := MAJORANA_SolutionIntMatVecs_Padic(intmat, vecd, p, max_iter);
                        return [pre.solvb, sol[2]/denom];
                    fi;
                fi;

                intres := intres / p;
                pvec := Z(p)^0 * intres;
                ppower := ppower * p;
                if nriter > max_iter then
                    Error("");
                fi;
            fi;
        else
            # No rational solution exists
            Error("I believe there is no solution (which I think is wrong");
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
    if max_iter < 1000 then
        # TODO: Should probably make a better guess about the
        #       number of iterations or not try to restrict the
        #       user.
        Error("using less that 1000 iterations is not recommended");
    fi;

    Print("#I number of variables: ", Length(mat), "\n");
    intsys := MakeIntSystem(mat, vec);

    return MAJORANA_SolutionIntMatVecs_Padic(intsys[1], intsys[2], p, max_iter);
end);
