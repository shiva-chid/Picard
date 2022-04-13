177,0
S,GSpSize,The order of the group of symplectic similitudes of degree d over Z/NZ,0,2,0,0,0,0,0,0,0,148,,0,0,148,,178,-38,-38,-38,-38,-38
S,Symp,The group of symplectic similitudes of degree d over Z/NZ,0,2,0,0,0,0,0,0,0,148,,0,0,148,,178,-38,-38,-38,-38,-38
S,GSp,The group of symplectic similitudes of degree d over Z/NZ,0,2,0,0,0,0,0,0,0,148,,0,0,148,,178,-38,-38,-38,-38,-38
S,GSpLevel,The least integer N such that H is the full inverse image of its reduction modulo N,0,1,0,0,0,0,0,0,0,178,,148,178,-38,-38,-38,-38
S,GLLift,"The full preimage in GL(n,Z/MZ) of H in GL(n,Z/NZ) for a multiple M of N",0,2,0,0,0,0,0,0,0,148,,0,0,178,,178,-38,-38,-38,-38,-38
S,GLProject,"The projection of the preimage of H in GL(n,Zhat) to GL(n,Z/MZ)",0,2,0,0,0,0,0,0,0,148,,0,0,178,,178,-38,-38,-38,-38,-38
S,GSpLift,"The full preimage in GSp(n,Z/MZ) of H in GSp(n,Z/NZ) for a multiple M of N",0,2,0,0,0,0,0,0,0,148,,0,0,178,,178,-38,-38,-38,-38,-38
S,GSpProject,The index of H in GSp,0,2,0,0,0,0,0,0,0,148,,0,0,178,,148,-38,-38,-38,-38,-38
S,GSpIndex,The index of H in GSp,0,1,0,0,0,0,0,0,0,178,,148,-38,-38,-38,-38,-38
S,GLDeterminantImage,det(H) as a subgroup of GL1,0,1,0,0,0,0,0,0,0,178,,178,-38,-38,-38,-38,-38
S,GLDeterminantIndex,The index of det(H) in GL1,0,1,0,0,0,0,0,0,0,178,,148,-38,-38,-38,-38,-38
S,GLTranspose,"Given a subgroup H of GL(n,R) for some ring R returns the transposed subgroup",0,1,0,0,0,0,0,0,0,178,,178,-38,-38,-38,-38,-38
S,GLOrbitSignature,"The orbit signature of H (the ordered list of triples [e,s,m] where m is the number of non-trivial right H-orbits of V of size s and exponent e)",0,1,0,0,0,0,0,0,0,178,,82,-38,-38,-38,-38,-38
S,GSpSimilitudeCharacter,"Given a matrix A in GSp(2g,Z/NZ) returns a such that A*J*Transpose(A) = a*J, where J is the symplectic form on Sp(2g,Z/NZ)",0,1,0,0,0,0,0,0,0,180,,321,-38,-38,-38,-38,-38
S,GSpSimilitudeImage,Similitude of H as a subgroup of GL1,0,1,0,0,0,0,0,0,0,178,,178,-38,-38,-38,-38,-38
S,GSpSimilitudeIndex,The index of similitude of H in GL1,0,1,0,0,0,0,0,0,0,178,,148,-38,-38,-38,-38,-38
S,GSpClassSignature,"The class signature of H (the ordered list of 5-tuples (o,a,d,s,m) where m is the number of conjugacy classes of elements of H of size s, order o, similitude d, and coefficients of characteristic polynomial a)",0,1,0,0,0,0,0,0,0,178,,82,-38,-38,-38,-38,-38
S,GSpCanonicalize,"Computes a canonical set of generators for a conjugate of a subgroup H of GSp (the returned list generates a conjugate of H and depends only on the conjugacy class of H, not H itself)",0,2,0,0,0,0,0,0,0,178,,0,0,178,,82,-38,-38,-38,-38,-38
S,GSpCompareLabels,"Lexicographically compares subgroup labels of the form N.i.n (N=level, i=index, n=ordinal) as lists of integers. Returns -1,0,1",0,2,0,0,0,0,0,0,0,298,,0,0,298,,148,-38,-38,-38,-38,-38
S,GSpSortLabels,"Sorts the specified list of labels of subgroups of GSp(d,Zhat)",1,0,1,82,0,298,1,0,0,0,0,0,0,0,82,,82,-38,-38,-38,-38,-38
S,GSpCompareLabelLists,Lexicographically compares two lists of subgroup labels,2,0,1,82,0,298,1,1,82,0,298,2,0,0,0,0,0,0,0,82,,0,0,82,,148,-38,-38,-38,-38,-38
S,GLMinimizeGenerators,"Attempts to minimize the number of generators of a finite group by sampling random elements. Result is not guaranteed to be optimal unless G is abelian (but it very likely will be optimal or very close to it, see https://doi.org/10.1016/S0021-8693(02)00528-8)",0,1,0,0,0,0,0,0,0,-27,,-27,-38,-38,-38,-38,-38
S,GSpLattice,"Lattice of subgroups of GSp(d,N) of index bounded by IndexLimit. Returns a list of records with attributes label, level, index, orbits, children, parents, subgroup, where children and parents are indices into this list that identify maximal subgroups and minimal supergroups",0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,148,,457,-38,-38,-38,-38,-38
S,GSpLookupLabel,"The label of the specified subgroup of GSp(d,Z/NZ) if it is present in the specified subgroup lattice (up to conjugacy)",0,2,0,0,0,0,0,0,0,178,,0,0,457,,298,-38,-38,-38,-38,-38
