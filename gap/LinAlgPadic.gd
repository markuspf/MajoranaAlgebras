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
DeclareGlobalFunction( "MAJORANA_SolutionMatVecs_Plugin2" );
DeclareGlobalFunction( "MAJORANA_SolutionMatVecs_Test" );
DeclareGlobalFunction( "MAJORANA_NullspaceMat_Plugin" );

# This activates some sanity checks
# Setting this constant to false will
# probably speed up the code a bit
BindConstant("MAJORANA_LinAlg_Padic_Debug", true);
BindGlobal("MAJORANA_LinAlg_Padic_Iterations", 100);
BindGlobal("MAJORANA_LinAlg_Padic_Prime", 193);


# DeclareCategory( "IsSparseMatrix", IsObject and IsList ); # really IsMatrixObj, but that doen't exist.
# DeclareRepresentation( "IsSparseMatrixRep", IsSparseMatrix and IsPositionalObjectRep, [] );

# BindGlobal("SparseMatrixType", NewType( NewFamily("IsSparseMatrixFamily", IsSparseMatrix)
#                                      , IsSparseMatrix and IsSparseMatrixRep and IsMutable ));

# DeclareGlobalFunction( "NewSparseMatrix" );
# DeclareGlobalFunction( "LcmOfDenominators" );

