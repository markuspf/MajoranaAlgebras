#
# Solving linear equations over the integers/rationals by Dixon/Hensel lifting
#
DeclareGlobalFunction( "MAJORANA_RatNumberFromModular" );
DeclareGlobalFunction( "MAJORANA_IntMat" );
DeclareGlobalFunction( "MAJORANA_SolutionWithEchelonForm" );


# solve for one vector (integer version)
DeclareGlobalFunction( "MAJORANA_SolutionIntMatVec_Padic" );

# solve for a list of vectors (rationals)
DeclareGlobalFunction( "MAJORANA_SolutionMatVecs_Padic" );

# solve for a list of vectors (rationals)
DeclareGlobalFunction( "MAJORANA_SolutionMatVec_Padic" );

DeclareGlobalFunction( "MAJORANA_NullspaceIntMat_Padic" );
DeclareGlobalFunction( "MAJORANA_NullspaceMat_Padic" );


DeclareInfoClass("InfoMajoranaPadics");
DeclareInfoClass("InfoMajoranaLinearEq");

# This is the function that should be "pluggable" into the
# rest of the Majorana algebras stuff
DeclareGlobalFunction( "MAJORANA_SolutionMatVecs_Plugin" );
DeclareGlobalFunction( "MAJORANA_NullspaceMat_Plugin" );

