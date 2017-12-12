# FIXME: Prototype sparse matrices using hash tables
#        These should really go into the "Gauss" package

#InstallGlobalFunction(NewSparseMatrix,
#function(ring, rowc, colc)
#    return Objectify(SparseMatrixType, [ring, rowc, colc, false, HashMap()]);
#end);
#
#InstallOtherMethod( \[\], "for a sparse matrix, an index, and an index"
#               , [ IsSparseMatrixRep, IsPosInt, IsPosInt ],
#function(m, i, j)
#    local idx;
#    if m![4] then
#        idx := [i, j];
#    else
#        idx := [j, i];
#    fi;
#    if idx in m![5] then
#        return m![5][idx];
#    else
#        return Zero(m![1]);
#    fi;
#end);
#
#InstallOtherMethod( \[\]\:\=, "for a sparse matrix, an index, and an index"
#                    , [ IsSparseMatrixRep, IsPosInt, IsPosInt, IsObject ],
#function(m, i, j, val)
#    local idx;
#    if m![4] then
#        idx := [i, j];
#    else
#        idx := [j, i];
#    fi;
#    m![5][idx] := val;
#end);
#
#InstallGlobalFunction( LcmOfDenominators,
#function(mat)
#    return _FoldList2(mat![5]![6], DenominatorRat, LcmInt);
#end);
#
#InstallMethod( ViewString, "", [IsSparseMatrixRep],
#function(mat)
#    return STRINGIFY( "<a sparse hashtable "
#                    , mat![2], "x", mat![3]
#                    , " matrix over "
#                    , ViewString(mat![1]), ">");
#end);
#
#InstallMethod( ViewObj, "", [IsSparseMatrixRep],
#function(mat)
#    Print(ViewString(mat));
#end);
#

