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

# Just to make sure we're not shooting ourselves
# in the foot with inconsistent entries.
CheckSystem := function(system)
    local b, r, c;

    Info( InfoMajoranaLinearEq, 5,
          " testing system of equation structure" );
    if not IsPrime(system.p) then
        Error("p is not prime");
    fi;

    for r in system.int_mat do
        for c in r do
            if DenominatorRat(c) <> 1 then
                Error("Non-1-denominator in system.int_mat");
            fi;
        od;
    od;

    for r in system.int_vecs do
        for c in r do
            if DenominatorRat(c) <> 1 then
                Error("Non-1-denominator in system.int_vecs");
            fi;
        od;
    od;
    Info( InfoMajoranaLinearEq, 5,
          " success.");
end;

Presolve := function(system)
    system.mat_mod_p := system.int_mat * Z(system.p)^0;
    ConvertToMatrixRep(system.mat_mod_p);

    system.echelon := EchelonMatTransformation(system.mat_mod_p);

    system.solvable_variables := Concatenation( Filtered( List( system.echelon.vectors
                                                              , x -> PositionsProperty(x, y -> not IsZero(y) ) )
                                                        , z -> Length(z) = 1) );
    system.solvable_rows := system.echelon.heads{ system.solvable_variables };
    return system;
end;

# Solve for one right-hand-side
InstallGlobalFunction( MAJORANA_SolutionMatVec_Padic,
                       { mat, b, iter_step } -> MAJORANA_SolutionMatVecs_Padic(mat, [ b ], iter_step) );

# Solve for multiple right-hand-sides
InstallGlobalFunction(MAJORANA_SetupMatVecsSystem_Padic,
function(mat, vecs, p, max_iter)
    local system, mmults, vmults, lcm;
    system := rec( mat := mat
                 , vecs := vecs
                 , number_variables := Length(mat[1])
                 , number_equations := Length(mat) );

    #  MakeIntSystem(system);
    Info(InfoMajoranaLinearEq, 5,
         "MakeIntSystem2: computing denominator lcms" );

    mmults := List(system.mat, x -> _FoldList2(x, DenominatorRat, LcmInt));
    vmults := List(system.vecs, x -> _FoldList2(x, DenominatorRat, LcmInt));
    lcm := _FoldList2(Concatenation(mmults, vmults), IdFunc, LcmInt);

    Info(InfoMajoranaLinearEq, 5,
         "MakeIntSystem2: lcm: ", lcm);

    system.lcm := lcm;
    system.int_mat := system.mat * lcm;
    system.int_vecs := system.vecs * lcm;

    system.p := p;
    system.precision := max_iter;
    system.padic_family := PurePadicNumberFamily(p, max_iter);
    system.padic_iterations := 1000;

    Presolve(system);

    # Transposingpalooza
    system.transposed_int_mat := TransposedMat(system.int_mat);
    system.transposed_int_mat_sliced := system.transposed_int_mat{system.solvable_rows};
    system.transposed_coeffs := TransposedMat(system.echelon.coeffs);
    system.transposed_vecs := TransposedMat(system.int_vecs);
    system.lifted_coeffs := List(system.transposed_coeffs, y -> List(y, IntFFESymm));

    system.solution_denominator := 1;

    return system;
end);

InstallGlobalFunction( MAJORANA_SolutionIntMatVec_Padic,
function(system, vi)
    local
        p,

        # These are *integer* vectors
        tmp_soln, soln,
        residue,

        # These are vectors in GF(p)
        vec_p,
        soln_p, soln_pp,

        done, iterations,
        soln_padic,
        ppower, sol, x, y, i,
        k, old_denom, denom, vecd, iter;

    p := system.p;

    # Accumulator for integer solution
    # FIXME: only solved variables? Should cut down on memory use
    #        and how many p-adic expansions we have to actually turn
    #        into denominators
    soln := ListWithIdenticalEntries(system.number_variables, 0);

    # These are the *integer* residuals of the RHS
    # initially this is the RHS we're solving for
    # FIXME: for testing, only do one RHS right now
    #        this will trivially generalise fortunately
    #        but there might be a point in not solving all
    #        RHS at the same time, in case we discover enough 
    #        of the denominator to not have to approximate?
    residue := MutableCopyMat(system.transposed_vecs[vi])
               * system.solution_denominator;

    done := false;
    iterations := 0;
    ppower := 1; # this is p^iterations, FIXME: can we avoid this?

    # digits in the p-adic approximation to the solution
    soln_padic := List([1..system.number_variables], x -> PadicNumber(system.padic_family, 0));

    while (not done) do
        iterations := iterations + 1;

        if iterations mod 100 = 0 then
            Info(InfoMajoranaLinearEq, 5, STRINGIFY(iterations, " iterations"));
        fi;

        # solve the system mod p
        vec_p := Z(p)^0 * residue;
        soln_p := vec_p * system.transposed_coeffs;
        soln_p := List( system.echelon.heads,
                      function(x)
                          if x > 0 then
                              return soln_p[x];
                          else
                              return Zero(soln_p[1]);
                          fi;
                      end);

        # Convert the solution from GF(p) to integers -p/2..p/2-1
        y := List(soln_p, IntFFESymm);

        # they are the coefficients of the p-adic expansion of the denominator
        # the below is slow, and hence replaced by the hack below that.
        # soln_padic := soln_padic + List(y, c -> PadicNumber(fam, ppower * -c));
        soln_padic := soln_padic + List(y, c -> PadicNumber(system.padic_family, [iterations, c mod system.padic_family!.modulus ] ) );
        AddRowVector(soln, y, ppower);

        residue := (residue - y * system.transposed_int_mat) / p;
        ppower := ppower * p;

        Info(InfoMajoranaLinearEq, 10, "soln:    ", soln);
        Info(InfoMajoranaLinearEq, 10, "y:       ", y);
        Info(InfoMajoranaLinearEq, 10, "residue: ", residue);

        # Solution found?
        if IsZero( residue{ system.solvable_rows } ) then
            Info(InfoMajoranaLinearEq, 5,
                 "found an integer solution");

            # FIXME: I don't like this state struct design at the moment
            system.int_solution := soln;
            return true;
        else
            if iterations > system.precision then
                Info(InfoMajoranaLinearEq, 5,
                     "reached iteration limit, trying to compute denominator");
                # Compute the least common denominator of them all

                denom := PadicDenominatorList( soln_padic{ system.solvable_variables }, system.padic_iterations);
                Info(InfoMajoranaLinearEq, 5,
                     "found denominator: ", denom);

                if denom = fail then
                    Info( InfoMajoranaLinearEq, 10
                          , "failed to find denominator trying to increase p-adic precision");

                    Print("failed to solve rhs ", vi, "\n");
                    system.rhns := Intersection( system.solvable_rows,
                                                 PositionsProperty(residue, x -> not IsZero(x)));
                    Print("rhs not zero: ", system.rhns, " ", residue{ system.rhns },
                          "\n");

                    Error("");
                    # FIXME: adjust system, i.e. we could increase precision?
                    #        no need to recurse, then, just continue...
                    # MAJORANA_SolutionIntMatVec_Padic(system);
                    system.int_solution := soln;
                    return true;
                elif denom = 1 then
                    Info(InfoMajoranaLinearEq, 5,
                         "denominator 1 should not happen, trying to solve using GAP's builtin method");
                    Error("Denominator 1 occurred. This should not happen.");
                    return false;
                else
                    Info(InfoMajoranaLinearEq, 5,
                         "solving system after multiplying b by denominator.");

                    system.solution_denominator := system.solution_denominator * denom;

                    Print("failed to solve rhs ", vi, "\n");
                    system.rhns := Intersection( system.solvable_rows,
                                                 PositionsProperty(residue, x -> not IsZero(x)));
                    Print("rhs not zero: ", system.rhns, " ", residue{ system.rhns },
                          "\n");

                    # try again with new denominator
                    MAJORANA_SolutionIntMatVec_Padic(system, vi);
                    return true;
                fi;
            fi;


        fi;
    od;
end );
