gap> a:=(1,2)(3,4)(5,6);; b:=(1,4)(2,3);; c:=(2,4);;
gap> G:=Group(a,b,c);;
gap> T1:=[a,b,c,a*b,(1,4)(2,3)(5,6),(1,2)(4,3),(1,3)];;
gap> MajoranaRepresentation(G,T1);
[ [ [ "1A", "4A", "4A", "2B", "2B", "1A", "2B", "2A", "2B", "2A", "1A", "2A", 
          "2B", "1A" ], "Error", "Fusion of 0,0 eigenvectors does not hold", 
      1, [ 1, -4, 0, -4, 0, 0, 0, 0, 0 ], [ 0, 0, 0, 0, 1, 0, 0, 0, 0 ], 
      [ [ 0, 0, 1, 0, 0, 0, 0, 0, 0 ], 
          [ 0, 1/64, 3/64, 0, 0, 3/64, 1/64, -3/64, 0 ], 
          [ 3/64, 0, 3/64, 0, 1/64, 0, 1/64, 0, -3/64 ], 
          [ 0, 0, 0, 0, 0, 0, 0, 0, 0 ], [ 0, 0, 0, 0, 0, 0, 0, 0, 0 ], 
          [ 0, 0, 0, 0, 0, 1, 0, 0, 0 ], [ 0, 0, 0, 0, 0, 0, 0, 0, 0 ], 
          [ 0, 0, 0, 1/8, -1/8, 1/8, 0, 0, 0 ], [ 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
          [ 0, 0, 0, -1/8, 1/8, 1/8, 0, 0, 0 ], [ 1, 0, 0, 0, 0, 0, 0, 0, 0 ],
          [ 1/8, -1/8, 0, 1/8, 0, 0, 0, 0, 0 ], [ 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
          [ 0, 0, 0, 1, 0, 0, 0, 0, 0 ], 
          [ 0, -1/8, 5/16, 0, 0, -1/8, -1/16, 3/16, 0 ], 
          [ -1/8, 0, 5/16, 0, -1/8, 0, -1/16, 0, 3/16 ], 
          [ 0, -1/16, -1/8, 0, 0, 5/16, -1/8, 3/16, 0 ], false, false, 
          [ 5/16, 0, -1/8, 0, -1/16, 0, -1/8, 0, 3/16 ], 
          [ 0, 0, 0, 0, 0, 0, 0, 1, 0 ], false, [ 0, 0, 0, 0, 0, 0, 0, 0, 1 ],
          false, false ], 
      [ 
          [ (1,2)(3,4)(5,6), (1,4)(2,3), (2,4), (1,3)(2,4)(5,6), (1,4)(2,3)(5,6),
              (1,2)(3,4), (1,3), (1,2,3,4), (1,2,3,4)(5,6) ], 
          [ (1,2)(3,4)(5,6), (1,4)(2,3), (2,4), (1,3)(2,4)(5,6), 
              (1,4)(2,3)(5,6), (1,2)(3,4), (1,3), (1,2,3,4), (1,4,3,2), 
              (1,2,3,4)(5,6), (1,4,3,2)(5,6) ], 
          [ [ 11, 10, 3, 12, 13, 7, 3, 19, 20 ], 
              [ 10, 6, 2, 8, 7, 9, 2, 17, 18 ], 
              [ 3, 2, 1, 5, 3, 2, 4, 15, 16 ], 
              [ 12, 8, 5, 14, 12, 8, 5, 24, 25 ], 
              [ 13, 7, 3, 12, 11, 10, 3, 19, 20 ], 
              [ 7, 9, 2, 8, 10, 6, 2, 17, 18 ], 
              [ 3, 2, 4, 5, 3, 2, 1, 15, 16 ], 
              [ 19, 17, 15, 24, 19, 17, 15, 21, 22 ], 
              [ 20, 18, 16, 25, 20, 18, 16, 22, 23 ] ], 
          [ [ (), (2,4), (), (), (), (), (1,2)(3,4), (), () ], 
              [ (2,4), (2,4), (2,4), (2,4), (2,4), (2,4), (1,2,3,4), 
                  (1,2,3,4), (1,2,3,4) ], 
              [ (), (2,4), (), (), (2,4), (), (), (), () ], 
              [ (), (2,4), (), (), (2,4), (), (1,2)(3,4), (), () ], 
              [ (2,4), (2,4), (2,4), (2,4), (2,4), (), (1,2,3,4), (1,2,3,4), 
                  (1,2,3,4) ], [ (), (), (), (), (), (), (1,2)(3,4), (), () ],
              [ (1,2)(3,4), (1,2,3,4), (1,2)(3,4), (1,2)(3,4), (1,2,3,4), 
                  (1,2)(3,4), (1,2)(3,4), (1,2,3,4), (1,2,3,4) ], 
              [ (), (1,2,3,4), (), (), (1,2,3,4), (), (1,2,3,4), (), () ], 
              [ (), (1,2,3,4), (), (), (1,2,3,4), (), (1,2,3,4), (), () ] ], 
          [ 1, 2, 3, 4, 5, 6, 7, 8, 8, 9, 9 ], [  ] ] ] ]
gap> T2:=[a,b,c,a*b,(1,4)(2,3)(5,6),(1,2)(4,3),(1,3),(1,3)(5,6),(2,4)(5,6)];;
gap> MajoranaRepresentation(G,T2);
[ [ [ "1A", "2B", "4A", "4A", "2B", "2A", "2A", "1A", "4A", "4A", "2B", "2A", 
          "1A", "2B", "2A", "2B", "2A", "1A", "2A", "2B", "1A" ], "Error", 
      "Fusion of 0,0 eigenvectors does not hold", 1, 
      [ 1, -4, 0, -4, 0, 0, 0, 0, 0, 0, 0 ], 
      [ 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0 ], 
      [ [ 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0 ], 
          [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ], 
          [ 0, 1/64, 3/64, 0, 0, 3/64, 1/64, 0, 0, -3/64, 0 ], 
          [ 3/64, 0, 3/64, 0, 1/64, 0, 1/64, 0, 0, 0, -3/64 ], 
          [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ], 
          [ 0, 0, 1/8, -1/8, 0, 0, 0, 1/8, 0, 0, 0 ], 
          [ 0, 0, 1/8, 1/8, 0, 0, 0, -1/8, 0, 0, 0 ], 
          [ 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0 ], 
          [ 0, 1/64, 0, 0, 0, 3/64, 0, 1/64, 3/64, 0, -3/64 ], 
          [ 3/64, 0, 0, 0, 1/64, 0, 0, 1/64, 3/64, -3/64, 0 ], 
          [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ], 
          [ 0, 0, 0, 1/8, 0, 0, -1/8, 0, 1/8, 0, 0 ], 
          [ 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0 ], 
          [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ], 
          [ 0, 0, 0, 1/8, -1/8, 1/8, 0, 0, 0, 0, 0 ], 
          [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ], 
          [ 0, 0, 0, -1/8, 1/8, 1/8, 0, 0, 0, 0, 0 ], 
          [ 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ], 
          [ 1/8, -1/8, 0, 1/8, 0, 0, 0, 0, 0, 0, 0 ], 
          [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ], 
          [ 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0 ], 
          [ 0, -1/8, 5/16, 0, 0, -1/8, -1/16, 0, 0, 3/16, 0 ], 
          [ -1/8, 0, 5/16, 0, -1/8, 0, -1/16, 0, 0, 0, 3/16 ], 
          [ -1/8, 0, 0, 0, -1/8, 0, 0, -1/16, 5/16, 3/16, 0 ], 
          [ 0, -1/8, 0, 0, 0, -1/8, 0, -1/16, 5/16, 0, 3/16 ], 
          [ 0, -1/16, -1/8, 0, 0, 5/16, -1/8, 0, 0, 3/16, 0 ], 
          [ 0, -1/16, 0, 0, 0, 5/16, 0, -1/8, -1/8, 0, 3/16 ], 
          [ 5/16, 0, 0, 0, -1/16, 0, 0, -1/8, -1/8, 3/16, 0 ], 
          [ 5/16, 0, -1/8, 0, -1/16, 0, -1/8, 0, 0, 0, 3/16 ], 
          [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0 ], false, 
          [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 ], false, false ], 
      [ 
          [ (1,2)(3,4)(5,6), (1,4)(2,3), (2,4), (1,3)(2,4)(5,6), (1,4)(2,3)(5,6),
              (1,2)(3,4), (1,3), (1,3)(5,6), (2,4)(5,6), (1,2,3,4), 
              (1,2,3,4)(5,6) ], 
          [ (1,2)(3,4)(5,6), (1,4)(2,3), (2,4), (1,3)(2,4)(5,6), 
              (1,4)(2,3)(5,6), (1,2)(3,4), (1,3), (1,3)(5,6), (2,4)(5,6), 
              (1,2,3,4), (1,4,3,2), (1,2,3,4)(5,6), (1,4,3,2)(5,6) ], 
          [ [ 18, 17, 4, 19, 20, 14, 4, 10, 10, 28, 29 ], 
              [ 17, 13, 3, 15, 14, 16, 3, 9, 9, 26, 27 ], 
              [ 4, 3, 1, 7, 4, 3, 5, 6, 2, 22, 23 ], 
              [ 19, 15, 7, 21, 19, 15, 7, 12, 12, 33, 34 ], 
              [ 20, 14, 4, 19, 18, 17, 4, 10, 10, 28, 29 ], 
              [ 14, 16, 3, 15, 17, 13, 3, 9, 9, 26, 27 ], 
              [ 4, 3, 5, 7, 4, 3, 1, 2, 6, 22, 23 ], 
              [ 10, 9, 6, 12, 10, 9, 2, 8, 11, 24, 25 ], 
              [ 10, 9, 2, 12, 10, 9, 6, 11, 8, 24, 25 ], 
              [ 28, 26, 22, 33, 28, 26, 22, 24, 24, 30, 31 ], 
              [ 29, 27, 23, 34, 29, 27, 23, 25, 25, 31, 32 ] ], 
          [ [ (), (2,4), (), (), (), (), (1,2)(3,4), (1,2)(3,4), (), (), () ],
              [ (2,4), (2,4), (2,4), (2,4), (2,4), (2,4), (1,2,3,4), 
                  (1,2,3,4), (2,4), (1,2,3,4), (1,2,3,4) ], 
              [ (), (2,4), (), (), (2,4), (), (), (), (), (), () ], 
              [ (), (2,4), (), (), (2,4), (), (1,2)(3,4), (1,2)(3,4), (), (), 
                  () ], 
              [ (2,4), (2,4), (2,4), (2,4), (2,4), (), (1,2,3,4), (1,2,3,4), 
                  (2,4), (1,2,3,4), (1,2,3,4) ], 
              [ (), (), (), (), (), (), (1,2)(3,4), (1,2)(3,4), (), (), () ], 
              [ (1,2)(3,4), (1,2,3,4), (1,2)(3,4), (1,2)(3,4), (1,2,3,4), 
                  (1,2)(3,4), (1,2)(3,4), (1,2)(3,4), (1,2)(3,4), (1,2,3,4), 
                  (1,2,3,4) ], 
              [ (1,2)(3,4), (1,2,3,4), (), (1,2)(3,4), (1,2,3,4), (1,2)(3,4), 
                  (1,2)(3,4), (1,2)(3,4), (1,2)(3,4), (1,2,3,4), (1,2,3,4) ], 
              [ (), (2,4), (), (), (2,4), (), (1,2)(3,4), (), (), (), () ], 
              [ (), (1,2,3,4), (), (), (1,2,3,4), (), (1,2,3,4), (1,2,3,4), 
                  (), (), () ], 
              [ (), (1,2,3,4), (), (), (1,2,3,4), (), (1,2,3,4), (1,2,3,4), 
                  (), (), () ] ], 
          [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 10, 11, 11 ], [  ] ] ] ]
gap> T := [ (1,2), (1,3), (1,4), (2,3), (2,4), (3,4), (1,2)(3,4), (1,3)(2,4), (1,4)(2,3) ];;
gap> G := Group(T);;
gap> MajoranaRepresentation(G,T);
[ [ [ "1A", "3A", "2A", "2A", "4B", "1A", "2A" ], "Success", 
      [ (2,3,4), (1,3,4), (1,2,4), (1,2,3) ], [  ], [  ], 
      [ 
          [ [ (3,4), (3,4) ], [ (1,4), (1,4) ], [ (1,3), (1,3) ], 
              [ (2,4), (2,4) ], [ (2,3), (2,3) ], [ (1,2), (1,2) ] ], 
          [ [ (3,4), (2,3) ], [ (3,4), (1,3) ], [ (1,4), (1,2) ], 
              [ (1,3), (2,3) ], [ (2,4), (2,3) ], [ (2,3), (3,4) ], 
              [ (3,4), (2,4) ], [ (3,4), (1,4) ], [ (1,2), (1,4) ], 
              [ (1,2), (2,3) ], [ (1,4), (1,3) ], [ (1,3), (3,4) ], 
              [ (2,4), (1,2) ], [ (2,3), (1,3) ], [ (1,2), (1,3) ], 
              [ (1,2), (2,4) ], [ (1,4), (2,4) ], [ (1,3), (1,2) ], 
              [ (2,3), (1,2) ], [ (1,4), (3,4) ], [ (2,4), (1,4) ], 
              [ (1,3), (1,4) ], [ (2,4), (3,4) ], [ (2,3), (2,4) ] ], 
          [ [ (3,4), (1,2) ], [ (1,4), (2,3) ], [ (1,3), (2,4) ], 
              [ (2,4), (1,3) ], [ (2,3), (1,4) ], [ (1,2), (3,4) ] ], 
          [ [ (3,4), (1,2)(3,4) ], [ (1,4), (1,4)(2,3) ], 
              [ (1,3), (1,3)(2,4) ], [ (2,4), (1,3)(2,4) ], 
              [ (2,3), (1,4)(2,3) ], [ (1,2), (1,2)(3,4) ], 
              [ (1,2)(3,4), (3,4) ], [ (1,4)(2,3), (1,4) ], 
              [ (1,3)(2,4), (1,3) ], [ (1,3)(2,4), (2,4) ], 
              [ (1,4)(2,3), (2,3) ], [ (1,2)(3,4), (1,2) ] ], 
          [ [ (3,4), (1,3)(2,4) ], [ (3,4), (1,4)(2,3) ], 
              [ (1,4), (1,3)(2,4) ], [ (1,3), (1,2)(3,4) ], 
              [ (2,4), (1,2)(3,4) ], [ (2,3), (1,3)(2,4) ], 
              [ (1,2), (1,3)(2,4) ], [ (1,4), (1,2)(3,4) ], 
              [ (1,3), (1,4)(2,3) ], [ (2,4), (1,4)(2,3) ], 
              [ (2,3), (1,2)(3,4) ], [ (1,2), (1,4)(2,3) ], 
              [ (1,2)(3,4), (2,3) ], [ (1,2)(3,4), (1,3) ], 
              [ (1,4)(2,3), (1,2) ], [ (1,3)(2,4), (2,3) ], 
              [ (1,4)(2,3), (3,4) ], [ (1,2)(3,4), (2,4) ], 
              [ (1,2)(3,4), (1,4) ], [ (1,4)(2,3), (1,3) ], 
              [ (1,3)(2,4), (3,4) ], [ (1,3)(2,4), (1,2) ], 
              [ (1,4)(2,3), (2,4) ], [ (1,3)(2,4), (1,4) ] ], 
          [ [ (1,2)(3,4), (1,2)(3,4) ], [ (1,4)(2,3), (1,4)(2,3) ], 
              [ (1,3)(2,4), (1,3)(2,4) ] ], 
          [ [ (1,2)(3,4), (1,3)(2,4) ], [ (1,2)(3,4), (1,4)(2,3) ], 
              [ (1,4)(2,3), (1,3)(2,4) ], [ (1,3)(2,4), (1,2)(3,4) ], 
              [ (1,4)(2,3), (1,2)(3,4) ], [ (1,3)(2,4), (1,4)(2,3) ] ], 
          [ [ (3,4), (2,3,4) ], [ (3,4), (1,3,4) ], [ (1,4), (1,4,2) ], 
              [ (1,3), (1,2,3) ], [ (2,4), (2,4,3) ], [ (2,3), (2,4,3) ], 
              [ (3,4), (2,4,3) ], [ (3,4), (1,4,3) ], [ (1,2), (1,2,4) ], 
              [ (1,2), (1,3,2) ], [ (1,4), (1,4,3) ], [ (1,3), (1,4,3) ], 
              [ (2,4), (1,2,4) ], [ (2,3), (1,3,2) ], [ (1,2), (1,2,3) ], 
              [ (1,2), (1,4,2) ], [ (1,4), (1,2,4) ], [ (1,3), (1,3,2) ], 
              [ (2,3), (1,2,3) ], [ (1,4), (1,3,4) ], [ (2,4), (1,4,2) ], 
              [ (1,3), (1,3,4) ], [ (2,4), (2,3,4) ], [ (2,3), (2,3,4) ], 
              [ (2,3,4), (3,4) ], [ (1,3,4), (3,4) ], [ (1,4,2), (1,4) ], 
              [ (1,2,3), (1,3) ], [ (2,4,3), (2,4) ], [ (2,4,3), (2,3) ], 
              [ (2,4,3), (3,4) ], [ (1,4,3), (3,4) ], [ (1,2,4), (1,2) ], 
              [ (1,3,2), (1,2) ], [ (1,4,3), (1,4) ], [ (1,4,3), (1,3) ], 
              [ (1,2,4), (2,4) ], [ (1,3,2), (2,3) ], [ (1,2,3), (1,2) ], 
              [ (1,4,2), (1,2) ], [ (1,2,4), (1,4) ], [ (1,3,2), (1,3) ], 
              [ (1,2,3), (2,3) ], [ (1,3,4), (1,4) ], [ (1,4,2), (2,4) ], 
              [ (1,3,4), (1,3) ], [ (2,3,4), (2,4) ], [ (2,3,4), (2,3) ] ], 
          [ [ (3,4), (1,2,3) ], [ (3,4), (1,3,2) ], [ (1,4), (1,3,2) ], 
              [ (1,3), (2,3,4) ], [ (2,4), (1,3,2) ], [ (2,3), (1,4,3) ], 
              [ (3,4), (1,2,4) ], [ (3,4), (1,4,2) ], [ (1,2), (1,3,4) ], 
              [ (1,2), (2,4,3) ], [ (1,4), (1,2,3) ], [ (1,3), (2,4,3) ], 
              [ (2,4), (1,2,3) ], [ (2,3), (1,3,4) ], [ (1,2), (1,4,3) ], 
              [ (1,2), (2,3,4) ], [ (1,4), (2,4,3) ], [ (1,3), (1,4,2) ], 
              [ (2,3), (1,2,4) ], [ (1,4), (2,3,4) ], [ (2,4), (1,4,3) ], 
              [ (1,3), (1,2,4) ], [ (2,4), (1,3,4) ], [ (2,3), (1,4,2) ], 
              [ (2,3,4), (1,2) ], [ (1,3,4), (1,2) ], [ (1,4,2), (2,3) ], 
              [ (1,2,3), (2,4) ], [ (2,4,3), (1,3) ], [ (2,4,3), (1,4) ], 
              [ (2,4,3), (1,2) ], [ (1,4,3), (1,2) ], [ (1,2,4), (3,4) ], 
              [ (1,3,2), (3,4) ], [ (1,4,3), (2,3) ], [ (1,4,3), (2,4) ], 
              [ (1,2,4), (1,3) ], [ (1,3,2), (1,4) ], [ (1,2,3), (3,4) ], 
              [ (1,4,2), (3,4) ], [ (1,2,4), (2,3) ], [ (1,3,2), (2,4) ], 
              [ (1,2,3), (1,4) ], [ (1,3,4), (2,3) ], [ (1,4,2), (1,3) ], 
              [ (1,3,4), (2,4) ], [ (2,3,4), (1,3) ], [ (2,3,4), (1,4) ] ], 
          [ [ (2,3,4), (2,3,4) ], [ (1,3,4), (1,3,4) ], [ (1,4,2), (1,4,2) ], 
              [ (1,2,3), (1,2,3) ], [ (2,4,3), (2,4,3) ], 
              [ (1,4,3), (1,4,3) ], [ (1,2,4), (1,2,4) ], 
              [ (1,3,2), (1,3,2) ] ], 
          [ [ (2,3,4), (1,2,3) ], [ (1,3,4), (1,3,2) ], [ (1,4,2), (1,3,2) ], 
              [ (1,2,3), (2,3,4) ], [ (2,4,3), (1,3,2) ], 
              [ (2,4,3), (1,4,3) ], [ (2,4,3), (1,2,4) ], 
              [ (1,4,3), (1,4,2) ], [ (1,2,4), (1,3,4) ], 
              [ (1,3,2), (2,4,3) ], [ (1,4,3), (1,2,3) ], 
              [ (1,4,3), (2,4,3) ], [ (1,2,4), (1,2,3) ], 
              [ (1,3,2), (1,3,4) ], [ (1,2,3), (1,4,3) ], 
              [ (1,4,2), (2,3,4) ], [ (1,2,4), (2,4,3) ], 
              [ (1,3,2), (1,4,2) ], [ (1,2,3), (1,2,4) ], 
              [ (1,3,4), (2,3,4) ], [ (1,4,2), (1,4,3) ], 
              [ (1,3,4), (1,2,4) ], [ (2,3,4), (1,3,4) ], 
              [ (2,3,4), (1,4,2) ] ], 
          [ [ (2,3,4), (1,2,4) ], [ (1,3,4), (1,4,2) ], [ (1,4,2), (2,4,3) ], 
              [ (1,2,3), (1,4,2) ], [ (2,4,3), (1,3,4) ], 
              [ (2,4,3), (1,4,2) ], [ (2,4,3), (1,2,3) ], 
              [ (1,4,3), (1,3,2) ], [ (1,2,4), (2,3,4) ], 
              [ (1,3,2), (1,4,3) ], [ (1,4,3), (2,3,4) ], 
              [ (1,4,3), (1,2,4) ], [ (1,2,4), (1,4,3) ], 
              [ (1,3,2), (1,2,4) ], [ (1,2,3), (2,4,3) ], 
              [ (1,4,2), (1,3,4) ], [ (1,2,4), (1,3,2) ], 
              [ (1,3,2), (2,3,4) ], [ (1,2,3), (1,3,4) ], 
              [ (1,3,4), (1,2,3) ], [ (1,4,2), (1,2,3) ], 
              [ (1,3,4), (2,4,3) ], [ (2,3,4), (1,3,2) ], 
              [ (2,3,4), (1,4,3) ] ], 
          [ [ (1,2)(3,4), (2,3,4) ], [ (1,2)(3,4), (1,3,4) ], 
              [ (1,4)(2,3), (1,4,2) ], [ (1,3)(2,4), (1,2,3) ], 
              [ (1,3)(2,4), (2,4,3) ], [ (1,4)(2,3), (2,4,3) ], 
              [ (1,2)(3,4), (2,4,3) ], [ (1,2)(3,4), (1,4,3) ], 
              [ (1,2)(3,4), (1,2,4) ], [ (1,2)(3,4), (1,3,2) ], 
              [ (1,4)(2,3), (1,4,3) ], [ (1,3)(2,4), (1,4,3) ], 
              [ (1,3)(2,4), (1,2,4) ], [ (1,4)(2,3), (1,3,2) ], 
              [ (1,2)(3,4), (1,2,3) ], [ (1,2)(3,4), (1,4,2) ], 
              [ (1,4)(2,3), (1,2,4) ], [ (1,3)(2,4), (1,3,2) ], 
              [ (1,4)(2,3), (1,2,3) ], [ (1,4)(2,3), (1,3,4) ], 
              [ (1,3)(2,4), (1,4,2) ], [ (1,3)(2,4), (1,3,4) ], 
              [ (1,3)(2,4), (2,3,4) ], [ (1,4)(2,3), (2,3,4) ], 
              [ (2,3,4), (1,2)(3,4) ], [ (1,3,4), (1,2)(3,4) ], 
              [ (1,4,2), (1,4)(2,3) ], [ (1,2,3), (1,3)(2,4) ], 
              [ (2,4,3), (1,3)(2,4) ], [ (2,4,3), (1,4)(2,3) ], 
              [ (2,4,3), (1,2)(3,4) ], [ (1,4,3), (1,2)(3,4) ], 
              [ (1,2,4), (1,2)(3,4) ], [ (1,3,2), (1,2)(3,4) ], 
              [ (1,4,3), (1,4)(2,3) ], [ (1,4,3), (1,3)(2,4) ], 
              [ (1,2,4), (1,3)(2,4) ], [ (1,3,2), (1,4)(2,3) ], 
              [ (1,2,3), (1,2)(3,4) ], [ (1,4,2), (1,2)(3,4) ], 
              [ (1,2,4), (1,4)(2,3) ], [ (1,3,2), (1,3)(2,4) ], 
              [ (1,2,3), (1,4)(2,3) ], [ (1,3,4), (1,4)(2,3) ], 
              [ (1,4,2), (1,3)(2,4) ], [ (1,3,4), (1,3)(2,4) ], 
              [ (2,3,4), (1,3)(2,4) ], [ (2,3,4), (1,4)(2,3) ] ] ], 
      [ 1, 13/256, 1/8, 1/8, 1/64, 1, 1/8, 1/4, 1/36, 8/5, 136/405, 136/405, 
          1/9 ], 
      [ [ 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0 ], 
          [ 0, 0, 0, 1/16, 1/32, 1/16, 0, 0, 0, -135/2048, 0, 0, 0 ], 
          [ 1/8, 0, 0, 0, 0, 1/8, -1/8, 0, 0, 0, 0, 0, 0 ], 
          [ -1/8, 0, 0, 0, 0, 1/8, 1/8, 0, 0, 0, 0, 0, 0 ], 
          [ -1/64, 0, 0, 0, 0, 1/64, 1/64, 1/64, -1/64, 0, 0, 0, 0 ], 
          [ 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0 ], 
          [ 0, 0, 0, 0, 0, 0, 1/8, 1/8, -1/8, 0, 0, 0, 0 ], 
          [ 0, 0, 0, -1/9, -1/9, 2/9, 0, 0, 0, 5/32, 0, 0, 0 ], 
          [ 1/45, -1/90, -1/90, -1/90, -1/90, 1/45, -1/45, 0, 0, 1/64, 1/64, 
              -1/64, 1/64 ], [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0 ], 
          [ 0, 0, 0, 0, 0, 0, -64/675, -64/675, 128/2025, 1/5, -1/18, -1/18, 
              1/5 ], 
          [ 0, 0, 0, 0, 0, 0, -64/675, 128/2025, -64/675, 1/5, -1/18, 1/5, 
              -1/18 ], 
          [ 0, 0, 0, 0, 0, 0, 1/9, 0, 0, 5/64, 3/64, -1/16, -1/16 ] ], 
      [ 
          [ 
              [ [ -10/27, 32/27, 0, 32/27, 0, 0, 0, 0, 0, 0, 0, 0, 1 ], 
                  [ 0, 0, 32/27, 0, 32/27, -40/27, -40/27, 0, 0, 0, 0, 1, 0 ],
                  [ -167/432, 32/135, 32/135, 32/135, 32/135, 103/108, 
                      707/540, 0, 0, 1, 1, 0, 0 ], 
                  [ 5/16, 0, 0, 0, 0, -5/4, -5/4, 0, 0, 0, 0, 0, 0 ], 
                  [ 0, 0, 0, 0, 0, 0, -1/4, 1, 1, 0, 0, 0, 0 ] ], 
              [ [ -8/45, -32/45, 0, -32/45, 0, 0, 0, 0, 0, 0, 0, 0, 1 ], 
                  [ -8/45, 0, -32/45, 0, -32/45, 0, 0, 0, 0, 0, 0, 1, 0 ], 
                  [ 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0 ] ], 
              [ [ 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0 ], 
                  [ 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0 ], 
                  [ 0, 0, 1, 0, -1, 0, 0, 0, 0, -1, 1, 0, 0 ], 
                  [ 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0 ] ] ], 
          [ 
              [ [ 32/27, -10/27, 0, 32/27, 0, 0, 0, 0, 0, 0, 0, 0, 1 ], 
                  [ 32/135, -29/27, 32/135, 32/135, 100/27, 32/135, 0, 
                      548/135, 0, 1, 0, 1, 0 ], 
                  [ 0, 0, 32/27, 0, -40/27, 32/27, 0, -40/27, 0, 0, 1, 0, 0 ],
                  [ 0, 1, 0, 0, -4, 0, 0, -4, 0, 0, 0, 0, 0 ], 
                  [ 0, 0, 0, 0, 0, 0, 1, -1/4, 1, 0, 0, 0, 0 ] ], 
              [ [ -32/45, -8/45, 0, -32/45, 0, 0, 0, 0, 0, 0, 0, 0, 1 ], 
                  [ 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0 ], 
                  [ 0, -8/45, -32/45, 0, 0, -32/45, 0, 0, 0, 0, 1, 0, 0 ] ], 
              [ [ 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0 ], 
                  [ 0, 0, 1, 0, 0, -1, 0, 0, 0, -1, 0, 1, 0 ], 
                  [ 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0 ], 
                  [ 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0 ] ] ], 
          [ 
              [ 
                  [ 32/135, 32/135, 7/2160, -109/180, 32/135, 32/135, -1, -1, 0, 1, 
                      0, 0, 1 ], 
                  [ 32/27, 0, -10/27, 0, 32/27, 0, 0, 0, 0, 0, 0, 1, 0 ], 
                  [ 0, 32/27, -10/27, 0, 0, 32/27, 0, 0, 0, 0, 1, 0, 0 ], 
                  [ 0, 0, -1/16, 1/4, 0, 0, 1, 1, 0, 0, 0, 0, 0 ], 
                  [ 0, 0, -1/4, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0 ] ], 
              [ [ 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0 ], 
                  [ -32/45, 0, -8/45, 0, -32/45, 0, 0, 0, 0, 0, 0, 1, 0 ], 
                  [ 0, -32/45, -8/45, 0, 0, -32/45, 0, 0, 0, 0, 1, 0, 0 ] ], 
              [ [ 0, 1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 1 ], 
                  [ 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0 ], 
                  [ 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0 ], 
                  [ 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0 ] ] ], 
          [ 
              [ [ 32/27, 32/27, 0, -10/27, 0, 0, 0, 0, 0, 0, 0, 0, 1 ], 
                  [ 32/135, 32/135, -109/180, 7/2160, 32/135, 32/135, -1, -1, 
                      0, 0, 1, 1, 0 ], 
                  [ 0, 0, 1/4, -1/16, 0, 0, 1, 1, 0, 0, 0, 0, 0 ], 
                  [ 0, 0, 0, -10/27, 32/27, 32/27, 0, 0, 0, 1, 0, 0, 0 ], 
                  [ 0, 0, 1, -1/4, 0, 0, 0, 0, 1, 0, 0, 0, 0 ] ], 
              [ [ -32/45, -32/45, 0, -8/45, 0, 0, 0, 0, 0, 0, 0, 0, 1 ], 
                  [ 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0 ], 
                  [ 0, 0, 0, 1, 4, 4, 0, 0, 0, -45/8, 0, 0, 0 ] ], 
              [ [ 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ], 
                  [ 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, -1, 1, 0 ], 
                  [ 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0 ], 
                  [ 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0 ] ] ], 
          [ 
              [ 
                  [ 32/135, -1, 32/135, 32/135, 11/108, 32/135, 0, -29/45, 0, 0, 1, 
                      0, 1 ], 
                  [ 32/27, 0, 32/27, 0, -10/27, 0, 0, 0, 0, 0, 0, 1, 0 ], 
                  [ 0, 1, 0, 0, -1/4, 0, 0, 1, 0, 0, 0, 0, 0 ], 
                  [ 0, 0, 0, 32/27, -10/27, 32/27, 0, 0, 0, 1, 0, 0, 0 ], 
                  [ 0, 0, 0, 0, 0, 0, 1, -1/4, 1, 0, 0, 0, 0 ] ], 
              [ [ 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0 ], 
                  [ -32/45, 0, -32/45, 0, -8/45, 0, 0, 0, 0, 0, 0, 1, 0 ], 
                  [ 0, 0, 0, 1, 1/4, 1, 0, 0, 0, -45/32, 0, 0, 0 ] ], 
              [ [ 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1 ], 
                  [ 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0 ], 
                  [ 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ], 
                  [ 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0 ] ] ], 
          [ 
              [ 
                  [ -1, 32/135, 32/135, 32/135, 32/135, 11/108, -29/45, 0, 0, 0, 0, 
                      1, 1 ], [ 1, 0, 0, 0, 0, -1/4, 1, 0, 0, 0, 0, 0, 0 ], 
                  [ 0, 32/27, 32/27, 0, 0, -10/27, 0, 0, 0, 0, 1, 0, 0 ], 
                  [ 0, 0, 0, 32/27, 32/27, -10/27, 0, 0, 0, 1, 0, 0, 0 ], 
                  [ 0, 0, 0, 0, 0, 0, -1/4, 1, 1, 0, 0, 0, 0 ] ], 
              [ [ 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0 ], 
                  [ 0, 0, 0, 1, 1, 1/4, 0, 0, 0, -45/32, 0, 0, 0 ], 
                  [ 0, -32/45, -32/45, 0, 0, -8/45, 0, 0, 0, 0, 1, 0, 0 ] ], 
              [ [ 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, -1, 1 ], 
                  [ 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0 ], 
                  [ 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ], 
                  [ 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0 ] ] ], 
          [ 
              [ [ -1, -178/9, -1, -1, -178/9, -1, -19/144, 169/36, 0, 1, 1, 1, 1 
                     ], [ 1, 0, 0, 0, 0, 1, -1/4, 0, 0, 0, 0, 0, 0 ], 
                  [ 0, 32, 0, 0, 32, 0, 0, -8, 0, 0, 0, 0, 0 ], 
                  [ 0, 2, 1, 1, 2, 0, -1/16, -1/4, 0, 0, 0, 0, 0 ], 
                  [ 0, 8, 0, 0, 8, 0, -1/4, -1, 1, 0, 0, 0, 0 ] ], 
              [ [ 1, 0, 0, 0, 0, -1, 0, -1, 1, -1, -1, 1, 1 ], 
                  [ 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0 ], 
                  [ 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0 ] ], 
              [ [ 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 1 ], 
                  [ 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0 ], 
                  [ 0, 0, 1, -1, 0, 0, 0, 0, 0, -1, 1, 0, 0 ], 
                  [ 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0 ] ] ], 
          [ 
              [ [ 6, -1, -1, -1, -1, 6, -7/4, -19/144, 0, 1, 1, 1, 1 ], 
                  [ 0, 1, 0, 0, 1, 0, 0, -1/4, 0, 0, 0, 0, 0 ], 
                  [ -8, 0, 0, 0, 0, -8, 2, 0, 0, 0, 0, 0, 0 ], 
                  [ 2, 0, 1, 1, 0, 2, -1/4, -1/16, 0, 0, 0, 0, 0 ], 
                  [ 8, 0, 0, 0, 0, 8, -1, -1/4, 1, 0, 0, 0, 0 ] ], 
              [ [ 0, -1, 0, 0, 1, 0, 1, 0, -1, -1, 1, -1, 1 ], 
                  [ 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0 ], 
                  [ 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0 ] ], 
              [ [ 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 1 ], 
                  [ 0, 0, 1, -1, 0, 0, 0, 0, 0, -1, 0, 1, 0 ], 
                  [ 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0 ], 
                  [ 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0 ] ] ], 
          [ [ [ 16/9, -1, -1, -1, -1, 16/9, -11/9, -19/36, 0, 1, 1, 1, 1 ], 
                  [ -8, 0, 1, 1, 0, -8, 1, -1, 0, 0, 0, 0, 0 ], 
                  [ -8, 0, 0, 0, 0, -8, 2, 0, 0, 0, 0, 0, 0 ], 
                  [ 0, 1, 0, 0, 1, 0, 0, -1/4, 0, 0, 0, 0, 0 ], 
                  [ -32, 0, 0, 0, 0, -32, 4, -4, 1, 0, 0, 0, 0 ] ], 
              [ [ 0, 0, 1, -1, 0, 0, 1, -1, 0, 1, -1, -1, 1 ], 
                  [ 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0 ], 
                  [ 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0 ] ], 
              [ [ 0, 1, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 1 ], 
                  [ 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 1, 0 ], 
                  [ 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0 ], 
                  [ 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0 ] ] ] ], [  ], 
      [ [ (1,2), (1,3), (1,4), (2,3), (2,4), (3,4), (1,2)(3,4), (1,3)(2,4), 
              (1,4)(2,3), (2,3,4), (1,3,4), (1,2,4), (1,2,3) ], 
          [ (1,2), (1,3), (1,4), (2,3), (2,4), (3,4), (1,2)(3,4), (1,3)(2,4), 
              (1,4)(2,3), (2,3,4), (2,4,3), (1,3,4), (1,4,3), (1,2,4), 
              (1,4,2), (1,2,3), (1,3,2) ], 
          [ [ 1, 2, 2, 2, 2, 3, 4, 5, 5, 9, 9, 8, 8 ], 
              [ 2, 1, 2, 2, 3, 2, 5, 4, 5, 9, 8, 9, 8 ], 
              [ 2, 2, 1, 3, 2, 2, 5, 5, 4, 9, 8, 8, 9 ], 
              [ 2, 2, 3, 1, 2, 2, 5, 5, 4, 8, 9, 9, 8 ], 
              [ 2, 3, 2, 2, 1, 2, 5, 4, 5, 8, 9, 8, 9 ], 
              [ 3, 2, 2, 2, 2, 1, 4, 5, 5, 8, 8, 9, 9 ], 
              [ 4, 5, 5, 5, 5, 4, 6, 7, 7, 13, 13, 13, 13 ], 
              [ 5, 4, 5, 5, 4, 5, 7, 6, 7, 13, 13, 13, 13 ], 
              [ 5, 5, 4, 4, 5, 5, 7, 7, 6, 13, 13, 13, 13 ], 
              [ 9, 9, 9, 8, 8, 8, 13, 13, 13, 10, 11, 12, 11 ], 
              [ 9, 8, 8, 9, 9, 8, 13, 13, 13, 11, 10, 11, 12 ], 
              [ 8, 9, 8, 9, 8, 9, 13, 13, 13, 12, 11, 10, 11 ], 
              [ 8, 8, 9, 8, 9, 9, 13, 13, 13, 11, 12, 11, 10 ] ], 
          [ 
              [ (1,3)(2,4), (1,4,2,3), (1,3)(2,4), (1,4)(2,3), (1,3,2,4), 
                  (1,3)(2,4), (1,3)(2,4), (1,3)(2,4), (1,3,2,4), (1,3,2,4), 
                  (1,3)(2,4), (1,3)(2,4), (1,4,2,3) ], 
              [ (1,4,3), (1,2,4,3), (1,2,4,3), (1,4), (1,2,4,3), (1,2,4), 
                  (1,2,4,3), (1,2,4,3), (1,2,4), (1,4), (1,2,4,3), (1,2,4,3), 
                  (1,4) ], 
              [ (1,3), (1,2,3), (1,2,3), (1,2,3), (1,3,4), (1,2,3,4), 
                  (1,2,3), (1,2,3,4), (1,2,3), (1,2,3,4), (1,2,3,4), (1,3,4), 
                  (1,2,3) ], 
              [ (1,4,3,2), (1,4,2), (2,4,3), (2,4,3), (2,4,3), (2,4), 
                  (2,4,3), (2,4), (2,4,3), (2,4,3), (1,4,2), (1,4,3,2), 
                  (1,4,3,2) ], 
              [ (1,3,2), (2,3), (1,3,4,2), (2,3), (2,3), (2,3,4), (2,3), 
                  (2,3), (2,3,4), (2,3,4), (2,3,4), (1,3,2), (1,3,2) ], 
              [ (), (1,2), (1,2)(3,4), (), (3,4), (), (), (), (3,4), (), 
                  (1,2), (3,4), () ], 
              [ (1,3)(2,4), (1,2,4,3), (1,2,3), (2,4,3), (2,3), (), (), (), 
                  (3,4), (), (1,2), (1,3)(2,4), (1,4,2,3) ], 
              [ (1,3)(2,4), (1,2,4,3), (1,2,3,4), (2,4), (2,3), (), (2,3), 
                  (2,3), (2,3,4), (2,3,4), (1,2,4,3), (1,3,2), (1,4) ], 
              [ (1,3,2,4), (1,2,4), (1,2,3), (2,4,3), (2,3,4), (3,4), 
                  (2,4,3), (2,4), (2,4,3), (2,4,3), (1,2,3,4), (1,3,4), 
                  (1,4,3,2) ], 
              [ (1,3,2,4), (1,4), (1,2,3,4), (2,4,3), (2,3,4), (), (), 
                  (2,3,4), (2,4,3), (), (2,3,4), (), () ], 
              [ (1,3)(2,4), (1,2,4,3), (1,2,3,4), (1,4,2), (2,3,4), (1,2), 
                  (1,2), (1,2,4,3), (1,2,3,4), (1,2,3,4), (1,2), (1,2,4,3), 
                  (1,2,3,4) ], 
              [ (1,3)(2,4), (1,2,4,3), (1,3,4), (1,4,3,2), (1,3,2), (3,4), 
                  (1,3)(2,4), (1,3,2), (1,3,4), (1,3)(2,4), (1,3)(2,4), 
                  (1,3,2), (1,3,2) ], 
              [ (1,4,2,3), (1,4), (1,2,3), (1,4,3,2), (1,3,2), (), (1,4,2,3), 
                  (1,4), (1,4,3,2), (1,4), (1,4,3,2), (1,4,3,2), (1,4,3,2) ] ]
            , [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 10, 11, 11, 12, 12, 13, 13 ], 
          [  ] ], 
      [ [ 6, 6 ], [ 6, 4 ], [ 6, 1 ], [ 6, 7 ], [ 6, 8 ], [ 7, 7 ], [ 7, 8 ], 
          [ 6, 10 ], [ 6, 13 ], [ 10, 10 ], [ 10, 13 ], [ 10, 12 ], [ 7, 10 ] 
         ] ], 
  [ [ "1A", "3C", "2A", "2A", "4B", "1A", "2A" ], "Success", [  ], [  ], 
      [  ], 
      [ 
          [ [ (3,4), (3,4) ], [ (1,4), (1,4) ], [ (1,3), (1,3) ], 
              [ (2,4), (2,4) ], [ (2,3), (2,3) ], [ (1,2), (1,2) ] ], 
          [ [ (3,4), (2,3) ], [ (3,4), (1,3) ], [ (1,4), (1,2) ], 
              [ (1,3), (2,3) ], [ (2,4), (2,3) ], [ (2,3), (3,4) ], 
              [ (3,4), (2,4) ], [ (3,4), (1,4) ], [ (1,2), (1,4) ], 
              [ (1,2), (2,3) ], [ (1,4), (1,3) ], [ (1,3), (3,4) ], 
              [ (2,4), (1,2) ], [ (2,3), (1,3) ], [ (1,2), (1,3) ], 
              [ (1,2), (2,4) ], [ (1,4), (2,4) ], [ (1,3), (1,2) ], 
              [ (2,3), (1,2) ], [ (1,4), (3,4) ], [ (2,4), (1,4) ], 
              [ (1,3), (1,4) ], [ (2,4), (3,4) ], [ (2,3), (2,4) ] ], 
          [ [ (3,4), (1,2) ], [ (1,4), (2,3) ], [ (1,3), (2,4) ], 
              [ (2,4), (1,3) ], [ (2,3), (1,4) ], [ (1,2), (3,4) ] ], 
          [ [ (3,4), (1,2)(3,4) ], [ (1,4), (1,4)(2,3) ], 
              [ (1,3), (1,3)(2,4) ], [ (2,4), (1,3)(2,4) ], 
              [ (2,3), (1,4)(2,3) ], [ (1,2), (1,2)(3,4) ], 
              [ (1,2)(3,4), (3,4) ], [ (1,4)(2,3), (1,4) ], 
              [ (1,3)(2,4), (1,3) ], [ (1,3)(2,4), (2,4) ], 
              [ (1,4)(2,3), (2,3) ], [ (1,2)(3,4), (1,2) ] ], 
          [ [ (3,4), (1,3)(2,4) ], [ (3,4), (1,4)(2,3) ], 
              [ (1,4), (1,3)(2,4) ], [ (1,3), (1,2)(3,4) ], 
              [ (2,4), (1,2)(3,4) ], [ (2,3), (1,3)(2,4) ], 
              [ (1,2), (1,3)(2,4) ], [ (1,4), (1,2)(3,4) ], 
              [ (1,3), (1,4)(2,3) ], [ (2,4), (1,4)(2,3) ], 
              [ (2,3), (1,2)(3,4) ], [ (1,2), (1,4)(2,3) ], 
              [ (1,2)(3,4), (2,3) ], [ (1,2)(3,4), (1,3) ], 
              [ (1,4)(2,3), (1,2) ], [ (1,3)(2,4), (2,3) ], 
              [ (1,4)(2,3), (3,4) ], [ (1,2)(3,4), (2,4) ], 
              [ (1,2)(3,4), (1,4) ], [ (1,4)(2,3), (1,3) ], 
              [ (1,3)(2,4), (3,4) ], [ (1,3)(2,4), (1,2) ], 
              [ (1,4)(2,3), (2,4) ], [ (1,3)(2,4), (1,4) ] ], 
          [ [ (1,2)(3,4), (1,2)(3,4) ], [ (1,4)(2,3), (1,4)(2,3) ], 
              [ (1,3)(2,4), (1,3)(2,4) ] ], 
          [ [ (1,2)(3,4), (1,3)(2,4) ], [ (1,2)(3,4), (1,4)(2,3) ], 
              [ (1,4)(2,3), (1,3)(2,4) ], [ (1,3)(2,4), (1,2)(3,4) ], 
              [ (1,4)(2,3), (1,2)(3,4) ], [ (1,3)(2,4), (1,4)(2,3) ] ] ], 
      [ 1, 1/64, 1/8, 1/8, 1/64, 1, 1/8 ], 
      [ [ 0, 0, 0, 0, 0, 1, 0, 0, 0 ], [ 0, 0, 0, 1/64, -1/64, 1/64, 0, 0, 0 ]
            , [ 1/8, 0, 0, 0, 0, 1/8, -1/8, 0, 0 ], 
          [ -1/8, 0, 0, 0, 0, 1/8, 1/8, 0, 0 ], 
          [ -1/64, 0, 0, 0, 0, 1/64, 1/64, 1/64, -1/64 ], 
          [ 0, 0, 0, 0, 0, 0, 1, 0, 0 ], [ 0, 0, 0, 0, 0, 0, 1/8, 1/8, -1/8 ] 
         ], 
      [ 
          [ 
              [ [ -1, 121/4, -1/4, 121/4, -1/4, 1/4, 0, 1, 1 ], 
                  [ 1, -32, 0, -32, 0, 0, 0, 0, 0 ], 
                  [ 0, -7, -1, -7, -1, 1, 1, 0, 0 ], 
                  [ 0, -1, 1, -1, 1, 0, 0, 0, 0 ] ], 
              [ [ 0, 0, 0, 0, 0, 1, -1, 0, 0 ] ], 
              [ [ 0, 1, 0, -1, 0, 0, 0, -1, 1 ], 
                  [ 0, 1, 0, -1, 0, 0, 0, 0, 0 ], 
                  [ 0, 0, 1, 0, -1, 0, 0, 0, 0 ] ] ], 
          [ 
              [ [ -1, -1/32, 0, -1, 1/4, 0, 1, 0, 1 ], 
                  [ 0, -1/4, 0, 0, 1, 0, 0, 1, 0 ], 
                  [ 1, -1/32, 0, 1, 0, 0, 0, 0, 0 ], 
                  [ 0, -1/32, 1, 0, 0, 1, 0, 0, 0 ] ], 
              [ [ 0, 0, 0, 0, 1, 0, 0, -1, 0 ] ], 
              [ [ 0, 0, 1, 0, 0, -1, -1, 0, 1 ], 
                  [ 1, 0, 0, -1, 0, 0, 0, 0, 0 ], 
                  [ 0, 0, 1, 0, 0, -1, 0, 0, 0 ] ] ], 
          [ 
              [ [ 0, 0, -1/4, 1, 0, 0, 0, 0, 1 ], 
                  [ -1, 0, -1/32, 1/4, -1, 0, 1, 1, 0 ], 
                  [ 1, 0, -1/32, 0, 1, 0, 0, 0, 0 ], 
                  [ 0, 1, -1/32, 0, 0, 1, 0, 0, 0 ] ], 
              [ [ 0, 0, 0, -1, 0, 0, 0, 0, 1 ] ], 
              [ [ 1, 0, 0, 0, -1, 0, 0, 0, 0 ], 
                  [ 0, 1, 0, 0, 0, -1, -1, 1, 0 ], 
                  [ 0, 1, 0, 0, 0, -1, 0, 0, 0 ] ] ], 
          [ 
              [ [ 0, 0, 1, -1/4, 0, 0, 0, 0, 1 ], 
                  [ -1, -1, 1/4, -1/32, 0, 0, 1, 1, 0 ], 
                  [ 1, 1, 0, -1/32, 0, 0, 0, 0, 0 ], 
                  [ 0, 0, 0, -1/32, 1, 1, 0, 0, 0 ] ], 
              [ [ 0, 0, -1, 0, 0, 0, 0, 0, 1 ] ], 
              [ [ 1, -1, 0, 0, 0, 0, 0, 0, 0 ], 
                  [ 0, 0, 0, 0, 1, -1, -1, 1, 0 ], 
                  [ 0, 0, 0, 0, 1, -1, 0, 0, 0 ] ] ], 
          [ 
              [ [ -1, 1/4, -1, 0, -1/32, 0, 1, 0, 1 ], 
                  [ 0, 1, 0, 0, -1/4, 0, 0, 1, 0 ], 
                  [ 1, 0, 1, 0, -1/32, 0, 0, 0, 0 ], 
                  [ 0, 0, 0, 1, -1/32, 1, 0, 0, 0 ] ], 
              [ [ 0, 1, 0, 0, 0, 0, 0, -1, 0 ] ], 
              [ [ 0, 0, 0, 1, 0, -1, -1, 0, 1 ], 
                  [ 1, 0, -1, 0, 0, 0, 0, 0, 0 ], 
                  [ 0, 0, 0, 1, 0, -1, 0, 0, 0 ] ] ], 
          [ 
              [ [ 1/4, -1, -1, -1, -1, 0, 0, 1, 1 ], 
                  [ 0, -1, -1, 1, 1, 0, 0, 0, 0 ], 
                  [ 1, -8, -8, 0, 0, 0, 1, 0, 0 ], 
                  [ 0, -32, -32, 0, 0, 1, 0, 0, 0 ] ], 
              [ [ 1, 0, 0, 0, 0, 0, -1, 0, 0 ] ], 
              [ [ 0, 1, -1, 0, 0, 0, 0, -1, 1 ], 
                  [ 0, 1, -1, 0, 0, 0, 0, 0, 0 ], 
                  [ 0, 0, 0, 1, -1, 0, 0, 0, 0 ] ] ], 
          [ 
              [ [ 0, 0, -4, -4, 0, 0, 0, 0, 1 ], [ 0, -4, 0, 0, -4, 0, 0, 1, 0 ],
                  [ 0, -16, -16, -16, -16, 0, 1, 0, 0 ], 
                  [ 1, -4, -4, -4, -4, 1, 0, 0, 0 ] ], 
              [ [ 1, 0, 0, 0, 0, -1, 0, -1, 1 ], 
                  [ 1, 0, 0, 0, 0, -1, 0, 0, 0 ] ], 
              [ [ 0, 1, 0, 0, -1, 0, 0, 0, 0 ], 
                  [ 0, 0, 1, -1, 0, 0, 0, 0, 0 ] ] ], 
          [ 
              [ [ 0, 0, -4, -4, 0, 0, 0, 0, 1 ], [ 0, -4, 0, 0, -4, 0, 0, 1, 0 ],
                  [ 0, -1, 4, 4, -1, 0, 1, 0, 0 ], 
                  [ 1, -1/4, 1, 1, -1/4, 1, 0, 0, 0 ] ], 
              [ [ 0, 0, 0, 0, 0, 0, -1, 0, 1 ], 
                  [ 0, 1, 0, 0, -1, 0, 0, 0, 0 ] ], 
              [ [ 1, 0, 0, 0, 0, -1, 0, 0, 0 ], 
                  [ 0, 0, 1, -1, 0, 0, 0, 0, 0 ] ] ], 
          [ 
              [ [ 0, 0, -4, -4, 0, 0, 0, 0, 1 ], [ 0, -4, 0, 0, -4, 0, 0, 1, 0 ],
                  [ 0, 4, -1, -1, 4, 0, 1, 0, 0 ], 
                  [ 1, 1, -1/4, -1/4, 1, 1, 0, 0, 0 ] ], 
              [ [ 0, 0, 1, -1, 0, 0, 0, 0, 0 ], 
                  [ 0, 0, 0, 0, 0, 0, -1, 1, 0 ] ], 
              [ [ 1, 0, 0, 0, 0, -1, 0, 0, 0 ], 
                  [ 0, 1, 0, 0, -1, 0, 0, 0, 0 ] ] ] ], [  ], 
      [ [ (1,2), (1,3), (1,4), (2,3), (2,4), (3,4), (1,2)(3,4), (1,3)(2,4), 
              (1,4)(2,3) ], 
          [ (1,2), (1,3), (1,4), (2,3), (2,4), (3,4), (1,2)(3,4), (1,3)(2,4), 
              (1,4)(2,3) ], 
          [ [ 1, 2, 2, 2, 2, 3, 4, 5, 5 ], [ 2, 1, 2, 2, 3, 2, 5, 4, 5 ], 
              [ 2, 2, 1, 3, 2, 2, 5, 5, 4 ], [ 2, 2, 3, 1, 2, 2, 5, 5, 4 ], 
              [ 2, 3, 2, 2, 1, 2, 5, 4, 5 ], [ 3, 2, 2, 2, 2, 1, 4, 5, 5 ], 
              [ 4, 5, 5, 5, 5, 4, 6, 7, 7 ], [ 5, 4, 5, 5, 4, 5, 7, 6, 7 ], 
              [ 5, 5, 4, 4, 5, 5, 7, 7, 6 ] ], 
          [ 
              [ (1,3)(2,4), (1,4,2,3), (1,3)(2,4), (1,4)(2,3), (1,3,2,4), 
                  (1,3)(2,4), (1,3)(2,4), (1,3)(2,4), (1,3,2,4) ], 
              [ (1,4,3), (1,2,4,3), (1,2,4,3), (1,4), (1,2,4,3), (1,2,4), 
                  (1,2,4,3), (1,2,4,3), (1,2,4) ], 
              [ (1,3), (1,2,3), (1,2,3), (1,2,3), (1,3,4), (1,2,3,4), 
                  (1,2,3), (1,2,3,4), (1,2,3) ], 
              [ (1,4,3,2), (1,4,2), (2,4,3), (2,4,3), (2,4,3), (2,4), 
                  (2,4,3), (2,4), (2,4,3) ], 
              [ (1,3,2), (2,3), (1,3,4,2), (2,3), (2,3), (2,3,4), (2,3), 
                  (2,3), (2,3,4) ], 
              [ (), (1,2), (1,2)(3,4), (), (3,4), (), (), (), (3,4) ], 
              [ (1,3)(2,4), (1,2,4,3), (1,2,3), (2,4,3), (2,3), (), (), (), 
                  (3,4) ], 
              [ (1,3)(2,4), (1,2,4,3), (1,2,3,4), (2,4), (2,3), (), (2,3), 
                  (2,3), (2,3,4) ], 
              [ (1,3,2,4), (1,2,4), (1,2,3), (2,4,3), (2,3,4), (3,4), 
                  (2,4,3), (2,4), (2,4,3) ] ], [ 1, 2, 3, 4, 5, 6, 7, 8, 9 ], 
          [  ] ], 
      [ [ 6, 6 ], [ 6, 4 ], [ 6, 1 ], [ 6, 7 ], [ 6, 8 ], [ 7, 7 ], [ 7, 8 ] 
         ] ] ]
