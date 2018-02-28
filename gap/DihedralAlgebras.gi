BindGlobal( "MAJORANA_DihedralAlgebras", rec());

MAJORANA_DihedralAlgebras.2A := 

rec(    algebraproducts := [    SparseMatrix( 1, 3, [ [ 1 ] ], [ [ 1 ] ], Rationals ), 
                                SparseMatrix( 1, 3, [ [ 1, 2, 3 ] ], [ [ 1/8, 1/8, -1/8 ] ], Rationals ), 
                                SparseMatrix( 1, 3, [ [ 1, 2, 3 ] ], [ [ 1/8, -1/8, 1/8 ] ], Rationals ), 
                                SparseMatrix( 1, 3, [ [ 2 ] ], [ [ 1 ] ], Rationals ), 
                                SparseMatrix( 1, 3, [ [ 1, 2, 3 ] ], [ [ -1/8, 1/8, 1/8 ] ], Rationals ), 
                                SparseMatrix( 1, 3, [ [ 3 ] ], [ [ 1 ] ], Rationals ) ],
        evecs := [  [   SparseMatrix( 1, 3, [ [ 1, 2, 3 ] ], [ [ -1/4, 1, 1 ] ], Rationals ), 
                        SparseMatrix( 1, 3, [ [ 2, 3 ] ], [ [ -1, 1 ] ], Rationals ), 
                        SparseMatrix( 0, 3, [  ], [  ], Rationals ) ], 
                    [   SparseMatrix( 1, 3, [ [ 1, 2, 3 ] ], [ [ 1, -1/4, 1 ] ], Rationals ), 
                        SparseMatrix( 1, 3, [ [ 1, 3 ] ], [ [ -1, 1 ] ], Rationals ), 
                        SparseMatrix( 0, 3, [  ], [  ], Rationals ) ], 
                    [   SparseMatrix( 1, 3, [ [ 1, 2, 3 ] ], [ [ -4, -4, 1 ] ], Rationals ), 
                        SparseMatrix( 1, 3, [ [ 1, 2 ] ], [ [ -1, 1 ] ], Rationals ), 
                        SparseMatrix( 0, 3, [  ], [  ], Rationals ) ] ],
        group := Group( [ (1,2), (3,4) ] ),
        innerproducts := [ 1, 1/8, 1/8, 1, 1/8, 1 ],
        involutions := [ (1,2), (3,4), (1,2)(3,4) ],
        nullspace := SparseMatrix( 0, 3, [  ], [  ], Rationals ),
        setup := rec(   conjelts := [ [ 1 .. 3 ] ],
                        coords := [ (1,2), (3,4), (1,2)(3,4) ],
                        longcoords := [ (1,2), (3,4), (1,2)(3,4) ],
                        orbitreps := [ 1, 2, 3 ],
                        pairconj := [ [ 1, 1, 1 ], [ 1, 1, 1 ], [ 1, 1, 1 ] ],
                        pairconjelts := [ [ 1, 2, 3 ], [ 1, 2, 3 ], [ 1, 2, 3 ], [ 1, 2, 3 ] ],
                        pairorbit := [ [ 1, 2, 3 ], [ 2, 4, 5 ], [ 3, 5, 6 ] ],
                        pairreps := [ [ 1, 1 ], [ 1, 2 ], [ 1, 3 ], [ 2, 2 ], [ 2, 3 ], [ 3, 3 ] ],
                        poslist := [ 1 .. 3 ] ),
        shape := [ "1A", "2A", "2A", "1A", "2A", "1A" ] ); 

MAJORANA_DihedralAlgebras.2B := 

rec(     algebraproducts := [   SparseMatrix( 1, 2, [ [ 1 ] ], [ [ 1 ] ], Rationals ), 
                                SparseMatrix( 1, 2, [ [  ] ], [ [  ] ], Rationals ), 
                                SparseMatrix( 1, 2, [ [ 2 ] ], [ [ 1 ] ], Rationals ) ],
        evecs := [  [   SparseMatrix( 1, 2, [ [ 2 ] ], [ [ 1 ] ], Rationals ), 
                        SparseMatrix( 0, 2, [  ], [  ], Rationals ), 
                        SparseMatrix( 0, 2, [  ], [  ], Rationals ) ], 
                    [   SparseMatrix( 1, 2, [ [ 1 ] ], [ [ 1 ] ], Rationals ), 
                        SparseMatrix( 0, 2, [  ], [  ], Rationals ), 
                        SparseMatrix( 0, 2, [  ], [  ], Rationals ) ] ],
        group := Group( [ (1,2), (3,4) ] ),
        innerproducts := [ 1, 0, 1 ],
        involutions := [ (1,2), (3,4) ],
        nullspace := SparseMatrix( 0, 2, [  ], [  ], Rationals ),
        setup := rec(   conjelts := [ [ 1 .. 2 ] ],
                        coords := [ (1,2), (3,4) ],
                        longcoords := [ (1,2), (3,4) ],
                        orbitreps := [ 1, 2 ],
                        pairconj := [ [ 1, 1 ], [ 1, 1 ] ],
                        pairconjelts := [ [ 1, 2 ], [ 1, 2 ], [ 1, 2 ], [ 1, 2 ] ],
                        pairorbit := [ [ 1, 2 ], [ 2, 3 ] ],
                        pairreps := [ [ 1, 1 ], [ 1, 2 ], [ 2, 2 ] ],
                        poslist := [ 1 .. 2 ] ),
        shape := [ "1A", "2B", "1A" ] );

MAJORANA_DihedralAlgebras.3A := 
                
rec(    algebraproducts := [    SparseMatrix( 1, 4, [ [ 1 ] ], [ [ 1 ] ], Rationals ), 
                                SparseMatrix( 1, 4, [ [ 1, 2, 3, 4 ] ], [ [ 1/16, 1/16, 1/32, -135/2048 ] ], Rationals ), 
                                SparseMatrix( 1, 4, [ [ 1, 2, 3, 4 ] ], [ [ 2/9, -1/9, -1/9, 5/32 ] ], Rationals ),
                                SparseMatrix( 1, 4, [ [ 4 ] ], [ [ 1 ] ], Rationals ) ],
        evecs := [  [   SparseMatrix( 1, 4, [ [ 1, 2, 3, 4 ] ], [ [ -10/27, 32/27, 32/27, 1 ] ], Rationals ), 
                        SparseMatrix( 1, 4, [ [ 1, 2, 3, 4 ] ], [ [ -8/45, -32/45, -32/45, 1 ] ], Rationals ), 
                        SparseMatrix( 1, 4, [ [ 2, 3 ] ], [ [ -1, 1 ] ], Rationals ) ], 
                    [ false, false, false ], 
                    [ false, false, false ] ],
        group := Group( [ (1,2), (1,3) ] ),
        innerproducts := [ 1, 13/256, 1/4, 8/5 ],
        involutions := [ (1,2), (1,3), (2,3) ],
        nullspace := SparseMatrix( 0, 4, [  ], [  ], Rationals ),
        setup := rec(   conjelts := [ [ 1 .. 4 ], [ 2, 3, 1, 4 ], [ 3, 2, 1, 4 ] ],
                        coords := [ (1,2), (1,3), (2,3), (1,2,3) ],
                        longcoords := [ (1,2), (1,3), (2,3), (1,2,3), (1,3,2) ],
                        orbitreps := [ 1 ],
                        pairconj := [ [ 1, 1, 3, 1 ], [ 1, 5, 6, 5 ], [ 3, 6, 6, 6 ], [ 1, 5, 6, 1 ] ],
                        pairconjelts := [ [ 1, 2, 3, 4 ], [ 2, 1, 3, 4 ], [ 1, 3, 2, 4 ], [ 3, 1, 2, 4 ], [ 2, 3, 1, 4 ], [ 3, 2, 1, 4 ] ],
                        pairorbit := [ [ 1, 2, 2, 3 ], [ 2, 1, 2, 3 ], [ 2, 2, 1, 3 ], [ 3, 3, 3, 4 ] ],
                        pairreps := [ [ 1, 1 ], [ 1, 2 ], [ 1, 4 ], [ 4, 4 ] ],
                        poslist := [ 1, 2, 3, 4, 4 ] ),
        shape := [ "1A", "3A" ] );
                
MAJORANA_DihedralAlgebras.3C := 

rec (   algebraproducts := [    SparseMatrix( 1, 3, [ [ 1 ] ], [ [ 1 ] ], Rationals ), 
                                SparseMatrix( 1, 3, [ [ 1, 2, 3 ] ], [ [ 1/64, 1/64, -1/64 ] ], Rationals ) ],
        evecs := [  [   SparseMatrix( 1, 3, [ [ 1, 2, 3 ] ], [ [ -1/32, 1, 1 ] ], Rationals ), 
                        SparseMatrix( 0, 3, [  ], [  ], Rationals ), 
                        SparseMatrix( 1, 3, [ [ 2, 3 ] ], [ [ -1, 1 ] ], Rationals ) ], 
                    [ false, false, false ], [ false, false, false ] ],
        group := Group( [ (1,2), (1,3) ] ),
        innerproducts := [ 1, 1/64 ],
        involutions := [ (1,2), (1,3), (2,3) ],
        nullspace := SparseMatrix( 0, 3, [  ], [  ], Rationals ),
        setup := rec(   conjelts := [ [ 1 .. 3 ], [ 2, 3, 1 ], [ 3, 2, 1 ] ],
                          coords := [ (1,2), (1,3), (2,3) ],
                          longcoords := [ (1,2), (1,3), (2,3) ],
                          orbitreps := [ 1 ],
                          pairconj := [ [ 1, 1, 3 ], [ 1, 5, 6 ], [ 3, 6, 6 ] ],
                          pairconjelts := [ [ 1, 2, 3 ], [ 2, 1, 3 ], [ 1, 3, 2 ], [ 3, 1, 2 ], [ 2, 3, 1 ], [ 3, 2, 1 ] ],
                          pairorbit := [ [ 1, 2, 2 ], [ 2, 1, 2 ], [ 2, 2, 1 ] ],
                          pairreps := [ [ 1, 1 ], [ 1, 2 ] ],
                          poslist := [ 1 .. 3 ] ),
        shape := [ "1A", "3C" ] ) ;

MAJORANA_DihedralAlgebras.4A := 

rec (   algebraproducts := [    SparseMatrix( 1, 5, [ [ 1 ] ], [ [ 1 ] ], Rationals ), 
                                SparseMatrix( 1, 5, [ [ 1, 2, 3, 4, 5 ] ], [ [ 3/64, 3/64, 1/64, 1/64, -3/64 ] ], Rationals ), 
                                SparseMatrix( 1, 5, [ [  ] ], [ [  ] ], Rationals ), 
                                SparseMatrix( 1, 5, [ [ 2 ] ], [ [ 1 ] ], Rationals ), 
                                SparseMatrix( 1, 5, [ [  ] ], [ [  ] ], Rationals ), 
                                SparseMatrix( 1, 5, [ [ 1, 2, 3, 4, 5 ] ], [ [ 5/16, -1/8, -1/16, -1/8, 3/16 ] ], Rationals ), 
                                SparseMatrix( 1, 5, [ [ 1, 2, 3, 4, 5 ] ], [ [ -1/8, 5/16, -1/8, -1/16, 3/16 ] ], Rationals ), 
                                SparseMatrix( 1, 5, [ [ 5 ] ], [ [ 1 ] ], Rationals ) ],
        evecs := [  [   SparseMatrix( 2, 5, [ [ 1, 2, 4, 5 ], [ 3 ] ], [ [ -1/2, 2, 2, 1 ], [ 1 ] ], Rationals ), 
                        SparseMatrix( 1, 5, [ [ 1, 2, 3, 4, 5 ] ], [ [ -1/3, -2/3, -1/3, -2/3, 1 ] ], Rationals ), 
                        SparseMatrix( 1, 5, [ [ 2, 4 ] ], [ [ -1, 1 ] ], Rationals ) ], 
                    [   SparseMatrix( 2, 5, [ [ 1, 2, 3, 5 ], [ 4 ] ], [ [ 2, -1/2, 2, 1 ], [ 1 ] ], Rationals ), 
                        SparseMatrix( 1, 5, [ [ 1, 2, 3, 4, 5 ] ], [ [ -2/3, -1/3, -2/3, -1/3, 1 ] ], Rationals ), 
                        SparseMatrix( 1, 5, [ [ 1, 3 ] ], [ [ -1, 1 ] ], Rationals ) ], 
                    [ false, false, false ], [ false, false, false ] ],
        group := Group( [ (1,2), (1,3)(2,4) ] ),
        innerproducts := [ 1, 1/32, 0, 1, 0, 3/8, 3/8, 2 ],
        involutions := [ (1,2), (1,3)(2,4), (3,4), (1,4)(2,3) ],
        nullspace := SparseMatrix( 0, 5, [  ], [  ], Rationals ),
        setup := rec(   conjelts := [ [ 1 .. 5 ], [ 3, 2, 1, 4, 5 ], [ 1, 4, 3, 2, 5 ] ],
                        coords := [ (1,2), (1,3)(2,4), (3,4), (1,4)(2,3), (1,4,2,3) ],
                        longcoords := [ (1,2), (1,3)(2,4), (3,4), (1,4)(2,3), (1,4,2,3), (1,3,2,4) ],
                        orbitreps := [ 1, 2 ],
                        pairconj := [ [ 1, 1, 1, 3, 1 ], [ 1, 1, 5, 1, 1 ], [ 1, 5, 5, 7, 5 ], [ 3, 1, 7, 3, 2 ], [ 1, 1, 5, 2, 1 ] ],
                        pairconjelts := [ [ 1, 2, 3, 4, 5 ], [ 1, 4, 3, 2, 5 ], [ 1, 4, 3, 2, 5 ], [ 1, 2, 3, 4, 5 ], [ 3, 2, 1, 4, 5 ], [ 3, 4, 1, 2, 5 ], [ 3, 4, 1, 2, 5 ], [ 3, 2, 1, 4, 5 ] ],
                        pairorbit := [ [ 1, 2, 3, 2, 6 ], [ 2, 4, 2, 5, 7 ], [ 3, 2, 1, 2, 6 ], [ 2, 5, 2, 4, 7 ], [ 6, 7, 6, 7, 8 ] ],
                        pairreps := [ [ 1, 1 ], [ 1, 2 ], [ 1, 3 ], [ 2, 2 ], [ 2, 4 ], [ 1, 5 ], [ 2, 5 ], [ 5, 5 ] ],
                        poslist := [ 1, 2, 3, 4, 5, 5 ] ),
        shape := [ "1A", "4A", "2B", "1A", "2B" ] ) ;

MAJORANA_DihedralAlgebras.4B := 

rec (   algebraproducts := [    SparseMatrix( 1, 5, [ [ 1 ] ], [ [ 1 ] ], Rationals ), 
                                SparseMatrix( 1, 5, [ [ 1, 2, 3, 4, 5 ] ], [ [ 1/64, 1/64, -1/64, -1/64, 1/64 ] ], Rationals ), 
                                SparseMatrix( 1, 5, [ [ 1, 3, 5 ] ], [ [ 1/8, 1/8, -1/8 ] ], Rationals ), 
                                SparseMatrix( 1, 5, [ [ 1, 3, 5 ] ], [ [ 1/8, -1/8, 1/8 ] ], Rationals ), 
                                SparseMatrix( 1, 5, [ [ 2 ] ], [ [ 1 ] ], Rationals ), 
                                SparseMatrix( 1, 5, [ [ 2, 4, 5 ] ], [ [ 1/8, 1/8, -1/8 ] ], Rationals ), 
                                SparseMatrix( 1, 5, [ [ 2, 4, 5 ] ], [ [ 1/8, -1/8, 1/8 ] ], Rationals ), 
                                SparseMatrix( 1, 5, [ [ 5 ] ], [ [ 1 ] ], Rationals ) ],
        evecs :=  [ [   SparseMatrix( 2, 5, [ [ 1, 3, 5 ], [ 1, 2, 3, 4 ] ], [ [ -1/4, 1, 1 ], [ -1/16, 1, 1/4, 1 ] ], Rationals ), 
                        SparseMatrix( 1, 5, [ [ 3, 5 ] ], [ [ -1, 1 ] ], Rationals ), 
                        SparseMatrix( 1, 5, [ [ 2, 4 ] ], [ [ -1, 1 ] ], Rationals ) ], 
                    [   SparseMatrix( 2, 5, [ [ 1, 3, 5 ], [ 1, 2, 3, 4 ] ], [ [ -4, -4, 1 ], [ 4, -1/4, 4, 1 ] ], Rationals ), 
                        SparseMatrix( 1, 5, [ [ 4, 5 ] ], [ [ -1, 1 ] ], Rationals ), 
                        SparseMatrix( 1, 5, [ [ 1, 3 ] ], [ [ -1, 1 ] ], Rationals ) ], 
                    [ false, false, false ], [ false, false, false ], 
                    [   SparseMatrix( 2, 5, [ [ 1, 3, 5 ], [ 1, 2, 3, 4 ] ], [ [ -4, -4, 1 ], [ -1, 1, -1, 1 ] ], Rationals ), 
                        SparseMatrix( 2, 5, [ [ 2, 4 ], [ 1, 3 ] ], [ [ -1, 1 ], [ -1, 1 ] ], Rationals ), SparseMatrix( 0, 5, [  ], [  ], Rationals ) ] ],
        group := Group( [ (1,2), (1,3)(2,4) ] ),
        innerproducts := [ 1, 1/64, 1/8, 1/8, 1, 1/8, 1/8, 1 ],
        involutions := [ (1,2), (1,3)(2,4), (3,4), (1,4)(2,3), (1,2)(3,4) ],
        nullspace := SparseMatrix( 0, 5, [  ], [  ], Rationals ),
        setup := rec(   conjelts := [ [ 1 .. 5 ], [ 3, 2, 1, 4, 5 ], [ 1, 4, 3, 2, 5 ] ],
                        coords := [ (1,2), (1,3)(2,4), (3,4), (1,4)(2,3), (1,2)(3,4) ],
                      longcoords := [ (1,2), (1,3)(2,4), (3,4), (1,4)(2,3), (1,2)(3,4) ],
                      orbitreps := [ 1, 2, 5 ],
                      pairconj := [ [ 1, 1, 1, 3, 1 ], [ 1, 1, 5, 1, 1 ], [ 1, 5, 5, 7, 5 ], [ 3, 1, 7, 3, 3 ], [ 1, 1, 5, 3, 1 ] ],
                      pairconjelts := [ [ 1, 2, 3, 4, 5 ], [ 1, 4, 3, 2, 5 ], [ 1, 4, 3, 2, 5 ], [ 1, 2, 3, 4, 5 ], [ 3, 2, 1, 4, 5 ], [ 3, 4, 1, 2, 5 ], [ 3, 4, 1, 2, 5 ], [ 3, 2, 1, 4, 5 ] ],
                      pairorbit := [ [ 1, 2, 3, 2, 4 ], [ 2, 5, 2, 6, 7 ], [ 3, 2, 1, 2, 4 ], [ 2, 6, 2, 5, 7 ], [ 4, 7, 4, 7, 8 ] ],
                      pairreps := [ [ 1, 1 ], [ 1, 2 ], [ 1, 3 ], [ 1, 5 ], [ 2, 2 ], [ 2, 4 ], [ 2, 5 ], [ 5, 5 ] ],
                      poslist := [ 1 .. 5 ] ),
          shape := [ "1A", "4B", "2A", "2A", "1A", "2A", "2A", "1A" ] );

MAJORANA_DihedralAlgebras.5A := 

rec(    algebraproducts := [    SparseMatrix( 1, 6, [ [ 1 ] ], [ [ 1 ] ], Rationals ), 
                                SparseMatrix( 1, 6, [ [ 1, 2, 3, 4, 5, 6 ] ], [ [ 3/128, 3/128, -1/128, -1/128, -1/128, 1 ] ], Rationals ), 
                                SparseMatrix( 1, 6, [ [ 1, 2, 3, 4, 5, 6 ] ], [ [ 3/128, -1/128, -1/128, 3/128, -1/128, -1 ] ], Rationals ), 
                                SparseMatrix( 1, 6, [ [ 2, 3, 4, 5, 6 ] ], [ [ 7/4096, 7/4096, -7/4096, -7/4096, 7/32 ] ], Rationals ), 
                                SparseMatrix( 1, 6, [ [ 1, 2, 3, 4, 5 ] ], [ [ 175/524288, 175/524288, 175/524288, 175/524288, 175/524288 ] ], Rationals ) ],
        evecs := [  [   SparseMatrix( 2, 6, [ [ 1, 2, 3, 6 ], [ 1, 2, 3, 4, 5 ] ], [ [ 21/4096, -7/64, -7/64, 1 ], [ -3/32, 1, 1, 1, 1 ] ], Rationals ), 
                        SparseMatrix( 1, 6, [ [ 2, 3, 4, 5, 6 ] ], [ [ 1/128, 1/128, -1/128, -1/128, 1 ] ], Rationals ), 
                        SparseMatrix( 2, 6, [ [ 4, 5 ], [ 2, 3 ] ], [ [ -1, 1 ], [ -1, 1 ] ], Rationals ) ], 
                        [ false, false, false ], [ false, false, false ], [ false, false, false ], [ false, false, false ] ],
        group := Group( [ (1,2)(3,5), (1,3)(4,5) ] ),
        innerproducts := [ 1, 3/128, 3/128, 0, 875/524288 ],
        involutions := [ (1,2)(3,5), (1,3)(4,5), (2,5)(3,4), (1,5)(2,4), (1,4)(2,3) ],
        nullspace := SparseMatrix( 0, 6, [  ], [  ], Rationals ),
        setup := rec(   conjelts := [ [ 1 .. 6 ], [ 2, 5, 1, 3, 4, 6 ], [ 3, 4, 1, 2, 5, 6 ], [ 4, 3, 5, 2, 1, 6 ], [ 5, 2, 4, 3, 1, 6 ] ],
                        coords := [ (1,2)(3,5), (1,3)(4,5), (2,5)(3,4), (1,5)(2,4), (1,4)(2,3), (1,2,3,4,5) ],
                        longcoords := [ (1,2)(3,5), (1,3)(4,5), (2,5)(3,4), (1,5)(2,4), (1,4)(2,3), (1,2,3,4,5), (1,3,5,2,4), (1,4,2,5,3), (1,5,4,3,2) ],
                        orbitreps := [ 1 ],
                        pairconj := [ [ 1, 1, 3, 1, 3, 1 ], [ 1, 8, 7, 9, 5, 8 ], [ 3, 7, 7, 9, 5, 7 ], [ 1, 9, 9, 9, 4, 9 ], [ 3, 5, 5, 4, 5, 5 ], [ 1, 8, 7, 9, 5, 1 ] ],
                        pairconjelts := [ [ 1, 2, 3, 4, 5, 6 ], [ 4, 5, 3, 1, 2, 6 ], [ 1, 3, 2, 5, 4, 6 ], [ 5, 4, 2, 1, 3, 6 ], [ 5, 2, 4, 3, 1, 6 ], [ 3, 1, 4, 5, 2, 6 ], [ 3, 4, 1, 2, 5, 6 ], [ 2, 5, 1, 3, 4, 6 ], [ 4, 3, 5, 2, 1, 6 ], [ 2, 1, 5, 4, 3, 6 ] ],
                        pairorbit := [ [ 1, 2, 2, 3, 3, 4 ], [ 2, 1, 3, 3, 2, 4 ], [ 2, 3, 1, 2, 3, 4 ], [ 3, 3, 2, 1, 2, 4 ], [ 3, 2, 3, 2, 1, 4 ], [ 4, 4, 4, 4, 4, 5 ] ],
                        pairreps := [ [ 1, 1 ], [ 1, 2 ], [ 1, 4 ], [ 1, 6 ], [ 6, 6 ] ],
                        poslist := [ 1, 2, 3, 4, 5, 6, -6, -6, 6 ] ),
        shape := [ "1A", "5A", "5A" ] ) ;
        
MAJORANA_DihedralAlgebras.6A := 

rec(    algebraproducts := [    SparseMatrix( 1, 8, [ [ 1 ] ], [ [ 1 ] ], Rationals ), 
                                SparseMatrix( 1, 8, [ [ 1, 2, 3, 4, 5, 6, 7, 8 ] ], [ [ 1/64, 1/64, -1/64, -1/64, -1/64, 1/64, -1/64, 45/2048 ] ], Rationals ), 
                                SparseMatrix( 1, 8, [ [ 1, 4, 6 ] ], [ [ 1/8, 1/8, -1/8 ] ], Rationals ), 
                                SparseMatrix( 1, 8, [ [ 1, 5, 7, 8 ] ], [ [ 1/16, 1/16, 1/32, -135/2048 ] ], Rationals ), 
                                SparseMatrix( 1, 8, [ [ 1, 4, 6 ] ], [ [ 1/8, -1/8, 1/8 ] ], Rationals ), 
                                SparseMatrix( 1, 8, [ [ 2 ] ], [ [ 1 ] ], Rationals ), 
                                SparseMatrix( 1, 8, [ [ 2, 3, 4, 8 ] ], [ [ 1/16, 1/16, 1/32, -135/2048 ] ], Rationals ), 
                                SparseMatrix( 1, 8, [ [ 2, 6, 7 ] ], [ [ 1/8, 1/8, -1/8 ] ], Rationals ), 
                                SparseMatrix( 1, 8, [ [ 6 ] ], [ [ 1 ] ], Rationals ), 
                                SparseMatrix( 1, 8, [ [ 1, 5, 7, 8 ] ], [ [ 2/9, -1/9, -1/9, 5/32 ] ], Rationals ), 
                                SparseMatrix( 1, 8, [ [ 2, 3, 4, 8 ] ], [ [ 2/9, -1/9, -1/9, 5/32 ] ], Rationals ), 
                                SparseMatrix( 1, 8, [ [  ] ], [ [  ] ], Rationals ), 
                                SparseMatrix( 1, 8, [ [ 8 ] ], [ [ 1 ] ], Rationals ) ],
        evecs := [  [   SparseMatrix( 3, 8, [ [ 2, 3, 4, 8 ], [ 1, 2, 3, 4, 5, 7 ], [ 1, 4, 6 ] ], [ [ -32/9, -32/9, -8/9, 1 ], [ -5/16, 3, 3, 3/4, 1, 1 ], [ -1/4, 1, 1 ] ], Rationals ), 
                        SparseMatrix( 2, 8, [ [ 1, 5, 7, 8 ], [ 4, 6 ] ], [ [ -8/45, -32/45, -32/45, 1 ], [ -1, 1 ] ], Rationals ), 
                        SparseMatrix( 2, 8, [ [ 5, 7 ], [ 2, 3 ] ], [ [ -1, 1 ], [ -1, 1 ] ], Rationals ) ], 
                    [   SparseMatrix( 3, 8, [ [ 2, 3, 4, 8 ], [ 1, 2, 3, 4, 5, 7 ], [ 1, 2, 3, 4, 5, 6 ] ], [ [ -10/27, 32/27, 32/27, 1 ], [ 4, -5/12, 4/3, 4/3, 4, 1 ], [ -4, 1/6, -4/3, -4/3, -4, 1 ] ], Rationals ), 
                        SparseMatrix( 2, 8, [ [ 2, 3, 4, 8 ], [ 6, 7 ] ], [ [ -8/45, -32/45, -32/45, 1 ], [ -1, 1 ] ], Rationals ), 
                        SparseMatrix( 2, 8, [ [ 1, 5 ], [ 3, 4 ] ], [ [ -1, 1 ], [ -1, 1 ] ], Rationals ) ], 
                        [ false, false, false ], [ false, false, false ], [ false, false, false ], 
                    [   SparseMatrix( 4, 8, [ [ 8 ], [ 1, 2, 4, 7 ], [ 1, 4, 6 ], [ 1, 3, 4, 5 ] ], [ [ 1 ], [ -1, 1, -1, 1 ], [ -4, -4, 1 ], [ -1, 1, -1, 1 ] ], Rationals ), 
                        SparseMatrix( 3, 8, [ [ 2, 7 ], [ 3, 5 ], [ 1, 4 ] ], [ [ -1, 1 ], [ -1, 1 ], [ -1, 1 ] ], Rationals ), 
                        SparseMatrix( 0, 8, [  ], [  ], Rationals ) ], [ false, false, false ] ],
        group := Group( [ (1,2)(3,6)(4,5), (1,3)(4,6) ] ),
        innerproducts := [ 1, 5/256, 1/8, 13/256, 1/8, 1, 13/256, 1/8, 1, 1/4, 1/4, 0, 8/5 ],
        involutions := [ (1,2)(3,6)(4,5), (1,3)(4,6), (2,6)(3,5), (1,5)(2,4), (1,4)(2,3)(5,6), (1,4)(2,5)(3,6), (1,6)(2,5)(3,4) ],
        nullspace := SparseMatrix( 0, 8, [  ], [  ], Rationals ),
        setup := rec(   conjelts := [ [ 1 .. 8 ], [ 1, 3, 2, 4, 7, 6, 5, 8 ], [ 5, 4, 2, 3, 7, 6, 1, 8 ], [ 5, 2, 4, 3, 1, 6, 7, 8 ], [ 7, 3, 4, 2, 1, 6, 5, 8 ] ],
                        coords := [ (1,2)(3,6)(4,5), (1,3)(4,6), (2,6)(3,5), (1,5)(2,4), (1,4)(2,3)(5,6), (1,4)(2,5)(3,6), (1,6)(2,5)(3,4), (1,3,5)(2,4,6) ],
                        longcoords := [ (1,2)(3,6)(4,5), (1,3)(4,6), (2,6)(3,5), (1,5)(2,4), (1,4)(2,3)(5,6), (1,4)(2,5)(3,6), (1,6)(2,5)(3,4), (1,3,5)(2,4,6), (1,5,3)(2,6,4) ],
                        orbitreps := [ 1, 2, 6 ],
                        pairconj := [ [ 1, 1, 3, 1, 1, 1, 3, 1 ], [ 1, 1, 1, 5, 5, 1, 11, 1 ], [ 3, 1, 3, 11, 5, 3, 11, 3 ], [ 1, 5, 11, 4, 4, 4, 2, 4 ], 
                          [ 1, 5, 5, 4, 5, 5, 4, 5 ], [ 1, 1, 3, 4, 5, 1, 11, 1 ], [ 3, 11, 11, 2, 4, 11, 11, 6 ], [ 1, 1, 3, 4, 5, 1, 6, 1 ] ],
                        pairconjelts := [ [ 1, 2, 3, 4, 5, 6, 7, 8 ], [ 7, 4, 3, 2, 5, 6, 1, 8 ], [ 1, 3, 2, 4, 7, 6, 5, 8 ], [ 5, 4, 2, 3, 7, 6, 1, 8 ], 
                          [ 5, 2, 4, 3, 1, 6, 7, 8 ], [ 7, 3, 4, 2, 1, 6, 5, 8 ], [ 7, 4, 3, 2, 5, 6, 1, 8 ], [ 1, 2, 3, 4, 5, 6, 7, 8 ], [ 1, 3, 2, 4, 7, 6, 5, 8 ], 
                          [ 5, 4, 2, 3, 7, 6, 1, 8 ], [ 7, 3, 4, 2, 1, 6, 5, 8 ], [ 5, 2, 4, 3, 1, 6, 7, 8 ] ],
                        pairorbit := [ [ 1, 2, 2, 3, 4, 5, 4, 10 ], [ 2, 6, 7, 7, 2, 8, 3, 11 ], [ 2, 7, 6, 7, 3, 8, 2, 11 ], [ 3, 7, 7, 6, 2, 8, 2, 11 ], 
                          [ 4, 2, 3, 2, 1, 5, 4, 10 ], [ 5, 8, 8, 8, 5, 9, 5, 12 ], [ 4, 3, 2, 2, 4, 5, 1, 10 ], [ 10, 11, 11, 11, 10, 12, 10, 13 ] ],
                        pairreps := [ [ 1, 1 ], [ 1, 2 ], [ 1, 4 ], [ 1, 5 ], [ 1, 6 ], [ 2, 2 ], [ 2, 3 ], [ 2, 6 ], [ 6, 6 ], [ 1, 8 ], [ 2, 8 ], [ 6, 8 ], [ 8, 8 ] ],
                        poslist := [ 1, 2, 3, 4, 5, 6, 7, 8, 8 ] ),
        shape := [ "1A", "6A", "2A", "3A", "2A", "1A", "3A", "2A", "1A" ] );
