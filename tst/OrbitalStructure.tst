gap> os := MAJORANA_OrbitalStructure([(1,2), (1,2,3,4,5)], [1..5], OnPoints);;
gap> MAJORANA_OrbitalRep(os, [5,2]);
[ 1, 2 ]
gap> ForAll(Tuples([1..5], 2), t -> OnTuples(t, MAJORANA_OrbitalCanonizingElement(os, t)) = MAJORANA_OrbitalRep(os, t));
true
gap> ForAll(Tuples([1..5], 2), t -> OnTuples(t, MAJORANA_OrbitalCanonizingElementInverse(os, t)^-1) = MAJORANA_OrbitalRep(os, t));
true
gap> os := MAJORANA_OrbitalStructure([(1,2,3)(4,5,6), (1,10)(2,20)], [1..20], OnPoints);;
gap> ForAll(Tuples([1..20], 2), t -> OnTuples(t, MAJORANA_OrbitalCanonizingElement(os, t)) = MAJORANA_OrbitalRep(os, t));
true
gap> ForAll(Arrangements([1..20], 2), t -> OnSets(Set(t), MAJORANA_UnorderedOrbitalCanonizingElement(os, t)) = MAJORANA_UnorderedOrbitalRep(os, t));
true
gap> OrbitalTest(os, [1..20]);
true
gap> OrbitalCanonizingTest(os, [1..20]);
true
gap> OrbitalTransversalTest(os, [1..20]);
true
gap> UnorderedOrbitalTest(os, [1..20]);
true
gap> UnorderedOrbitalCanonizingTest(os, [1..20]);
true
gap> UnorderedOrbitalTransversalTest(os, [1..20]);
true
gap> s := SignedPermL([3,-2,1,4,6,-5]);; t := SignedPermL([-1,-2,-3,5,4,10,7,8,-9,6]);;
gap> dom := Union([-10..-1],[1..10]);;
gap> os := MAJORANA_OrbitalStructure([s, t], dom, OnPoints);;
gap> OrbitalTest(os, dom);
true
gap> OrbitalCanonizingTest(os, dom);
true
gap> OrbitalTransversalTest(os, dom);
true
gap> UnorderedOrbitalTest(os, dom);
true
gap> UnorderedOrbitalCanonizingTest(os, dom);
true
gap> UnorderedOrbitalTransversalTest(os, dom);
true
