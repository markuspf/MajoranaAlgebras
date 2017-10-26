InstallGlobalFunction( MAJORANA_Orbits,

    function(G, D, act)
    
    local       gens,
                orbs,
                elements, 
                orb,
                orb2,
                sort,
                plist,
                pos,
                use,
                o,
                table,
                orders,
                y,
                i,
                j,
                result;
                
    table := [[], [1], [1,2], [1,3], [1,2,3,4]];
  
    gens := GeneratorsOfGroup(G);
    
    sort := Length(D)>0 and CanEasilySortElements(D[1]);
    plist := IsPlistRep(D);
  
    if not plist then
        use := BlistList([1..Length(D)],[]);
    fi;
    
    orbs := [];
    elements := [];
    pos := 1;
    
    while Length(D) > 0 and pos <= Length(D) do
    
        orders := List(D[pos], Order);
        
        if orders[1] > orders[2] then 
            D[pos] := Reversed(D[pos]);
        fi;
    
        orb := MAJORANA_OrbitOp( G, D[pos], gens, act );
        
        for i in table[orders[1]] do 
            for j in table[orders[2]] do 
                if not [D[pos][1]^i,D[pos][2]^j] in orb[1] then 
                    orb2 := MAJORANA_OrbitOp( G, [D[pos][1]^i,D[pos][2]^j], gens, act );
            
                    Append(orb[1], orb2[1]);
                    Append(orb[2], orb2[2]);
                fi;
                
                if not [D[pos][2]^j,D[pos][1]^i] in orb[1] then 
                    orb2 := MAJORANA_OrbitOp( G, [D[pos][1]^i,D[pos][2]^j], gens, act );
            
                    Append(orb[1], orb2[1]);
                    Append(orb[2], orb2[2]);
                fi;
            od;
        od;
                
        
        Add( orbs, Immutable(orb[1]) );
        Add( elements, Immutable(orb[2]) );
            
        if plist then
            if sort then
                D:=Difference(D,orb[1]);
                MakeImmutable(D); # to remember sortedness
            else
                D:=Filtered(D,i-> not i in orb[1]);
            fi;
        else
            for o in orb[1] do
                use[PositionCanonical(D,o)]:=true;
            od;
            
            # not plist -- do not take difference as there may be special
            # `PositionCanonical' method.
            
            while pos <= Length(D) and use[pos] do 
                pos := pos + 1;
            od;
        fi;
    od;
    
    result := rec(  orbits := orbs,
                    elts := elements );
    
    return result;
    
    end );
    
InstallGlobalFunction( MAJORANA_OrbitOp, 

    function( G, pnt, gens, act )
    
    local   D,
            orb,
            orb_elts,
            d,
            gen,
            i,
            g,
            h,
            p,
            count,
            result;
    
    D := DomainForAction(pnt,gens,act);
    
    pnt := Immutable(pnt);
    
    d := NewDictionary(pnt, false, D);
    
    orb := [ pnt ];
    orb_elts := [ Identity(G) ];
    
    AddDictionary(d,pnt);
    
    g := Identity(G);
    
    count := 0;
    
    for p in orb do
        
        count := count + 1;
        h := orb_elts[count];
        
        for gen in gens do
    
            i := act(p,gen);
            g := h*gen;
            
            MakeImmutable(i);
            
            if not KnowsDictionary(d,i) then
                Add( orb, i );
                AddDictionary(d,i);
                Add( orb_elts, g);
            fi;
        od;
    od;
    
    result := [orb,orb_elts];
    
    return result;
    
    end );
    
InstallGlobalFunction(MAJORANA_Orbitals,

    function(ProductList)
    
    local   G,
            dim,
            gens,
            i,j,k,l,
            pnt,
            d,
            orb,
            elts,
            count,
            p,
            h,
            g,
            q,
            x,
            y,
            table,
            gen,
            pos_1,
            pos_2,
            sign;
            
    
    G := ProductList[8];
    dim := Size(ProductList[1]);
    
    table := [[], [1], [1,2], [1,3], [1,2,3,4]];

    gens := GeneratorsOfGroup(G);
    
    ProductList[3] := NullMat(dim,dim);
    ProductList[4] := NullMat(dim,dim);
    ProductList[7] := [];

    for i in [1..dim] do 
        for j in [i..dim] do 

            if ProductList[3][i][j] = 0 then 
                
                Add(ProductList[7], [i,j]);
                
                pnt := Immutable(ProductList[1]{[i,j]});
                
                d := NewDictionary(pnt, false);
                
                orb := [pnt];
                elts := [()];
                
                AddDictionary(d,pnt);
                
                count := 0;
                
                x := List(pnt, Order);
                y := Size(ProductList[7]);
                
                ProductList[3][i][j] := y;
                ProductList[3][j][i] := y;
        
                ProductList[4][i][j] := ();
                ProductList[4][j][i] := ();
                
                for p in orb do 
                    
                    count := count + 1;
                    h := elts[count];
                    
                    for gen in gens do 
                    
                        q := OnPairs(p,gen);
                        g := h*gen;
                        
                        MakeImmutable(i);
                        
                        if not KnowsDictionary(d,q) then 
                        
                            Add( orb, q );
                            AddDictionary(d,q);
                            Add( elts, g);
                            
                            for k in table[x[1]] do 
                            
                                sign := 1;
                            
                                pos_1 := Position(ProductList[2], q[1]^k);
                                pos_1 := ProductList[5][pos_1];
                                
                                if pos_1 < 0 then 
                                    pos_1 := -pos_1;
                                    sign := - sign;
                                fi;
                            
                                for l in table[x[2]] do 

                                    pos_2 := Position(ProductList[2], q[2]^l);
                                    pos_2 := ProductList[5][pos_2];
                                    
                                    if pos_2 < 0 then 
                                        pos_2 := -pos_2;
                                        sign := - sign;
                                    fi;
                         
                                    if x = [5,5] then
                                        if [k,l] in [[1,2],[2,1],[1,3],[3,1],[2,4],[4,2],[3,4],[4,3]] then 
                                            sign := -sign;
                                        fi;
                                    elif x[2] = 5 and k in [2,3] then 
                                        sign := -sign;
                                    fi;
                                    
                                    ProductList[3][pos_1][pos_2] := sign*y;
                                    ProductList[3][pos_2][pos_1] := sign*y;
                            
                                    ProductList[4][pos_1][pos_2] := g;
                                    ProductList[4][pos_2][pos_1] := g;
                                
                                od;
                            od;
                        fi;
                    od;
                od;
            fi;
        od;
    od;
    
    end );
