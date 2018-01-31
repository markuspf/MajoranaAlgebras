InstallGlobalFunction(MAJORANA_ThreeClosedSetUp,

    function(rep, index)
    
    local   orders, signs, unknowns, dim, new_dim, x, elts, o1, o2, k, i, j, gens, pos;
    
    orders := [[], [1], [1,2], [1,3], [1,2,3,4]];
    signs := [[], [1], [1, 1], [1,1,1], [1,-1,-1,1]];
    
    dim := Size(rep.setup.coords);
    
    unknowns := [];
    
    for i in [1..dim] do 
        for j in [i..dim] do 
            if rep.setup.pairorbit[i][j] = index then 
                Add(unknowns, [i,j]);
            fi;
        od;
    od;

    MAJORANA_ThreeClosedExtendPerm(unknowns, rep.setup);

    for x in unknowns do 
        
        elts := rep.setup.coords{x};
        
        Add(rep.setup.coords, elts);
        
        o1 := Order(elts[1]); o2 := Order(elts[2]);
        
        k := Size(rep.setup.coords);
        
        for i in orders[o1] do 
            for j in orders[o2] do 
                Add(rep.setup.longcoords, [elts[1]^i, elts[2]^j]);
                Add(rep.setup.poslist, signs[o1][i]*signs[o2][j]*k);
                Add(rep.setup.longcoords, [elts[2]^i, elts[1]^j]);
                Add(rep.setup.poslist, signs[o1][i]*signs[o2][j]*k);
            od;
        od;
    od;
    
    new_dim := Size(rep.setup.coords);
    
    for i in [1..dim] do 
        Append(rep.setup.pairorbit[i], [dim + 1 .. new_dim]*0);
        Append(rep.setup.pairconj[i], [dim + 1 .. new_dim]*0);
    od;
    
    Append(rep.setup.pairorbit, NullMat(new_dim - dim, new_dim));
    Append(rep.setup.pairconj, NullMat(new_dim - dim, new_dim));
    
    gens := GeneratorsOfGroup(rep.group);
    gens := List(gens, x -> MAJORANA_FindVectorPermutation(x, rep.setup));
    
    MAJORANA_Orbitals(gens, dim, rep.setup);
    
    pos := Position(unknowns, rep.setup.pairreps[index]);    
    rep.algebraproducts[index] := SparseMatrix(1, new_dim, [[dim + pos]], [[1]], Rationals);
    
    for i in [1..Size(rep.algebraproducts)] do 
        if rep.algebraproducts[i] <> false then 
            rep.algebraproducts[i]!.ncols := new_dim;
        fi;
    od;
    
    for i in [Size(rep.algebraproducts) + 1 .. Size(rep.setup.pairreps)] do 
        rep.algebraproducts[i] := false;
        rep.innerproducts[i] := false;
    od;
    
    for i in rep.setup.orbitreps do 
        for j in [1..3] do 
            rep.evecs[i][j]!.ncols := new_dim;
        od;
    od;
    
    rep.nullspace!.ncols := new_dim;
    
    end );
    
InstallGlobalFunction( MAJORANA_ThreeClosedExtendPerm,

    function(unknowns, setup)
    
    local x, im, sign, pos, i, j, dim;
    
    dim := Size(setup.coords);
    
    for i in [1..Size(setup.pairconjelts)] do 
        if Size(setup.pairconjelts[i]) <= dim + Size(unknowns) then 
            for x in unknowns do 
                im := setup.pairconjelts[i]{x};
                sign := 1;
                
                if im[1] < 0 then im[1] := -im[1]; sign := -sign; fi;
                if im[2] < 0 then im[2] := -im[2]; sign := -sign; fi;
                
                if im[1] > im[2] then 
                    im := im{[2,1]};
                fi;
                
                pos := Position(unknowns, im);

                Add(setup.pairconjelts[i], sign*(dim + pos));
            od;
        fi;
    od;    
    
    for i in [1..Size(setup.conjelts)] do 
        for x in unknowns do 
            if setup.conjelts[i][1] <> () then 
                im := setup.conjelts[i]{x};
                sign := 1;
                
                if im[1] < 0 then im[1] := -im[1]; sign := -sign; fi;
                if im[2] < 0 then im[2] := -im[2]; sign := -sign; fi;
                
                if im[1] > im[2] then 
                    im := im{[2,1]};
                fi;
                
                pos := Position(unknowns, im);

                Add(setup.conjelts[i], sign*(dim + pos));
            fi;
        od;
    od;
    
    end);
    
InstallGlobalFunction( ThreeClosedMajoranaRepresentation, 

    function(rep)
    
    local falsecount, newfalsecount;
    
    MAJORANA_ThreeClosedSetUp(rep, Position(rep.algebraproducts, false));
    
    falsecount := [0,0];
    
    falsecount[1] := Size(Positions(rep.algebraproducts,false));
    falsecount[2] := Size(Positions(rep.innerproducts,false));
    
    while true do
                                
        MAJORANA_MainLoop(rep);
        
        newfalsecount := [0,0];

        newfalsecount[1] := Size(Positions(rep.algebraproducts,false));
        newfalsecount[2] := Size(Positions(rep.innerproducts,false));

        if newfalsecount[2] < falsecount[2] then 
            rep.nullspace := MAJORANA_CheckNullSpace(rep.innerproducts, rep.setup);
        fi;

        Info(InfoMajorana, 20,
            STRINGIFY( "There are ", newfalsecount[1], " unknown algebra products ") );
        Info(InfoMajorana, 20,
            STRINGIFY( "There are ", newfalsecount[2], " unknown inner products ") );

        if newfalsecount = [0,0] then
            Info( InfoMajorana, 10, "Success" );
            return;
        elif newfalsecount = falsecount then
            Info( InfoMajorana, 10, "Fail" );
            return;
        else
            falsecount := StructuralCopy(newfalsecount);
        fi;
    od;
    
    end );
