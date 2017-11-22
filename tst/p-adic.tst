# Test the p-adic solver

# Select the p-adic solver
gap> MAJORANA_SetLinearSolver(MAJORANA_SolutionMatVecs_Plugin);;

# A5
gap> a5 := A5();;
gap> rep1 := MajoranaRepresentation(a5,1);;
gap> MajoranaAlgebraTest(rep1);
true
gap> rep2 := MajoranaRepresentation(a5,2);;
gap> MajoranaAlgebraTest(rep2);
true;

# A6
gap> a6 := A6();;
gap> rep1 := MajoranaRepresentation(a6, 1);;
gap> MajoranaAlgebraTest(rep1);
true
gap> rep2 := MajoranaRepresentation(a6, 4);;
gap> MajoranaAlgebraTest(rep2);
true

#
gap> MAJORANA_SetLinearSolver(MAJORANA_SolutionMatVecs);;

#
