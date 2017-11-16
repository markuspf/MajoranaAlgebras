 
InstallGlobalFunction(MAJORANA_Orbits,

    function(G, t, SetUp)
    
    local   gens,
            i,
            pnt,
            d,
            orb,
            gen,
            elts,
            count,
            p,
            q,
            h,
            g,
            pos;
    
    gens := GeneratorsOfGroup(G);
    SetUp.conjelts := [1..t]*0;
    SetUp.orbitreps := [];
    
    for i in [1..t] do 
        if SetUp.conjelts[i] = 0 then 
            
            Add(SetUp.orbitreps, i);
            SetUp.conjelts[i] := ();
        
            pnt := Immutable(SetUp.coords[i]);
            
            d := NewDictionary(pnt, false);
            
            orb := [pnt];
            elts := [()];
            
            count := 0;
            
            AddDictionary(d, pnt);
            
            for p in orb do 
            
                count := count + 1;
                h := elts[count];
                
                for gen in gens do 
                
                    q := OnPoints(p, gen);
                    g := h*gen;
                    
                    MakeImmutable(q);
                    
                    if not KnowsDictionary(d,q) then 
                        Add(orb, q);
                        AddDictionary(d,q);
                        Add(elts, g);
                        
                        pos := Position(SetUp.longcoords, q);
                        pos := SetUp.poslist[pos];
                        
                        if pos < 0 then pos := -pos; fi;
                        
                        SetUp.conjelts[pos] := g;
                    fi;
                od;
            od;
        fi;
    od;
    
    SetUp.conjelts := DuplicateFreeList(SetUp.conjelts);
                        
    end ); 
   
InstallGlobalFunction(MAJORANA_Orbitals,

    function(G,t,SetUp)
    
    local   dim,
            gens,
            i,j,k,l,
            pnt,
            d,
            orb,
            elts,
            count,
            o,
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
    
    dim := Size(SetUp.coords);
    
    table := [[], [1], [1,2], [1,3], [1,2,3,4]];

    gens := GeneratorsOfGroup(G);

    for i in [1..dim] do 
        for j in [Maximum(i,t + 1)..dim] do 

            if SetUp.pairorbit[i][j] = 0 then 
                
                Add(SetUp.pairreps, [i,j]);
                
                pnt := Immutable(SetUp.coords{[i,j]});
                
                d := NewDictionary(pnt, false);
                
                orb := [pnt];
                elts := [()];
                
                count := 0;
                
                x := List(pnt, Order);
                y := Size(SetUp.pairreps);
                
                SetUp.pairorbit[i][j] := y;
                SetUp.pairorbit[j][i] := y;
                
                SetUp.pairconj[i][j] := ();
                SetUp.pairconj[j][i] := ();
                
                for p in orb do 
                    
                    count := count + 1;
                    h := elts[count];
                    
                    for gen in gens do 
                    
                        q := OnPairs(p,gen);
                        g := h*gen;
                        
                        pos_1 := Position(SetUp.longcoords,q[1]);
                        pos_2 := Position(SetUp.longcoords,q[2]);
                        
                        pos_1 := SetUp.poslist[pos_1];
                        pos_2 := SetUp.poslist[pos_2];
                        
                        if pos_1 < 0 then pos_1 := -pos_1; fi;
                        if pos_2 < 0 then pos_2 := -pos_2; fi;
                        
                        q := SetUp.coords{[pos_1,pos_2]};
                        
                        if not KnowsDictionary(d,q) then 
                        
                            Add( orb, q );
                            Add( elts, g);
                            AddDictionary( d, q);
                            
                            SetUp.pairorbit[pos_1][pos_2] := y;
                            SetUp.pairorbit[pos_2][pos_1] := y;
                            
                            SetUp.pairconj[pos_1][pos_2] := g;
                            SetUp.pairconj[pos_2][pos_1] := g;
                            
                        fi;
                    od;
                od;                
            fi;
        od;
    od;
    
    for i in [1 .. dim] do 
    
        o := Order(SetUp.coords[i]);
        
        for j in [Maximum(t, i) + 1 .. dim] do 
            if Order(SetUp.coords[j]) = 5 then 
            
                sign := 1;
                
                g := SetUp.pairconj[i][j];
                x := SetUp.pairorbit[i][j];
                
                p := SetUp.coords{SetUp.pairreps[x]};
                q := OnPairs(p, g);

                if SetUp.coords[j] in [q[2]^2,q[2]^3,q[1]^2,q[1]^3] then 
                    sign := -sign;
                elif not SetUp.coords[j] in [q[2],q[2]^4,q[1],q[1]^4] then 
                    Error("setup 2");
                fi;
                
                if o = 5 then 
                    if SetUp.coords[i] in [q[2]^2,q[2]^3,q[1]^2,q[1]^3] then 
                        sign := -sign;
                    elif not SetUp.coords[i] in [q[2],q[2]^4,q[1],q[1]^4] then 
                        Error("setup 1");
                    fi;
                fi; 
            
                SetUp.pairorbit[i][j] := sign*SetUp.pairorbit[i][j];
                SetUp.pairorbit[j][i] := sign*SetUp.pairorbit[j][i];
                              
            fi;
            
        od;
    od;
    
    end );
    
InstallGlobalFunction( MAJORANA_OrbitalsT,

    function(G, T)
    
    local   gens,
            t, 
            i,
            j,
            k,
            pairorbit,
            pairconj,
            pairreps,
            pnt,
            d,
            gen,
            orb,
            orbs,
            elts,
            count,
            p,
            q,
            h,
            g,
            res,
            pos_1,
            pos_2;
            
    gens := GeneratorsOfGroup(G);
    t := Size(T);
    
    pairorbit := NullMat(t,t);
    pairconj  := NullMat(t,t);
    pairreps  := [];
    orbs      := [];
    
    
    for i in [1..t] do 
        for j in [i..t] do 
            if pairorbit[i][j] = 0 then 
                
                Add(pairreps, [i,j]);
                
                k := Size(pairreps);
                
                pairorbit[i][j] := k;
                pairorbit[j][i] := k;
                
                pairconj[i][j] := ();
                pairconj[j][i] := ();
                
                pnt := Immutable(T{[i,j]});
                
                d := NewDictionary(pnt, false);
                
                orb := [pnt];
                elts := [()];
                
                AddDictionary(d,pnt);
                AddDictionary(d,Reversed(pnt));
                
                count := 0;
                
                for p in orb do 
                    
                    count := count + 1;
                    h := elts[count];
                    
                    for gen in gens do 
                    
                        q := OnPairs(p,gen);
                        g := h*gen;
                        
                        MakeImmutable(q);
                        
                        if not KnowsDictionary(d,q) then 
                        
                            Add( orb, q );
                            AddDictionary(d,q);
                            AddDictionary(d,Reversed(q));
                            Add( elts, g);
                
                            pos_1 := Position(T,q[1]);
                            pos_2 := Position(T,q[2]);
                                
                            pairorbit[pos_1][pos_2] := k;
                            pairorbit[pos_2][pos_1] := k;
                            
                            pairconj[pos_1][pos_2] := g;
                            pairconj[pos_2][pos_1] := g;
                            
                        fi;
                    od;
                od;
                
                Add(orbs, Immutable(orb));
                
            fi;
        od;
    od;
    
    res := rec( pairorbit := pairorbit,
                pairconj  := pairconj,
                pairreps  := pairreps,
                orbitals  := orbs   );
                
    return res;
    
    end );
