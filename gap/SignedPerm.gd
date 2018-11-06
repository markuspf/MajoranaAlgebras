# Signed permutations

DeclareCategory("IsSignedPerm",
                IsAssociativeElement and
                IsExtLElement and
                IsExtRElement and
                IsMultiplicativeElement and
                IsMultiplicativeElementWithOne and
                IsMultiplicativeElementWithInverse and
                IsFiniteOrderElement );

DeclareCategoryCollections( "IsSignedPerm" );
DeclareCategoryCollections( "IsSignedPermCollection" );

BindGlobal("SignedPermFamily", NewFamily("SignedPermFamily", IsSignedPerm));
DeclareRepresentation("IsSignedPermRep", IsSignedPerm and IsPositionalObjectRep, []);
BindGlobal("SignedPermType", NewType(SignedPermFamily, IsSignedPermRep));

DeclareGlobalFunction("OnPosPoints");

