# Test A6

# Select the p-adic solver
gap> MAJORANA_SetLinearSolver(MAJORANA_SolutionMatVecs);;

# A6
gap> a6 := A6();;
gap> rep1 := MajoranaRepresentation(a6, 1);;
gap> MajoranaAlgebraTest(rep1);
true
gap> rep2 := MajoranaRepresentation(a6, 2);;
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 1st choice method found for `[]' on 2 arguments
The 2nd argument is 'fail' which might point to an earlier problem
 at ./lib/methsel2.g:250 called from
gap> rep3 := MajoranaRepresentation(a6, 3);;
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 1st choice method found for `[]' on 2 arguments
The 2nd argument is 'fail' which might point to an earlier problem
 at ./lib/methsel2.g:250 called from
gap> rep4 := MajoranaRepresentation(a6, 4);;
gap> MajoranaAlgebraTest(rep4);
true

#
gap> MAJORANA_SetLinearSolver(MAJORANA_SolutionMatVecs);;

#
