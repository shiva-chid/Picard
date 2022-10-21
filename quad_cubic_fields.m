function quad_fields(ramprimes);
    if 2 in ramprimes then
        Ds := [-1] cat ramprimes;
    else
        Ds := [(p mod 4 eq 1) select p else -p : p in ramprimes];
    end if;
    V := VectorSpace(GF(2),#Ds);
    quad_flds := [];
    for v in V do
        if v eq V ! 0 then continue; end if;
        a := &*[(v[i] eq 1) select Ds[i] else 1 : i in [1..Dimension(V)]];
        assert IsSquarefree(a);
        Append(~quad_flds,a);
    end for;
    return quad_flds;
end function;


function cubic_fields(ramprimes);
    Z := Integers();
    K := RationalField();
    ramprimes := [p : p in ramprimes | p mod 3 eq 1];
    if #ramprimes eq 0 then
        return [];
    end if;
    full_cond := &*ramprimes;
    G3 := DirichletGroup(full_cond,CyclotomicField(3));
    assert #G3 eq 6^#ramprimes;
    assert NumberOfGenerators(G3) eq #ramprimes;
    cubic_dirichletchars := [];
/*
    cubic_flds := [];
*/
    PV := ProjectiveSpace(GF(3),#ramprimes-1);
    ratpts_PV := SetToSequence(RationalPoints(PV));
    assert #ratpts_PV eq (3^#ramprimes - 1)/2;
    for v in ratpts_PV do
        chi := &*[(G3.i)^(2*(Z ! v[i])): i in [1..#ramprimes]];
        Append(~cubic_dirichletchars,chi);
/*
        Append(~cubic_flds,DefiningPolynomial(NumberField(AbelianExtension(chi))));
*/
    end for;
    return cubic_dirichletchars;
/*
    return cubic_flds;
*/
end function;


