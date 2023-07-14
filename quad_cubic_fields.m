function quad_fields(radical_cond);
    F := CyclotomicField(3);
    OF := RingOfIntegers(F);
    G := HeckeCharacterGroup(4*3*radical_cond*OF : Target := CyclotomicField(1));
//    G := TargetRestriction(G,CyclotomicField(1));
//    EG := [x : x in Elements(G) | Order(x) eq 2];
//    return EG;
    return Exclude(Elements(G),G!1);
end function;

function cubic_fields(radical_cond);
    Z := Integers();
    F := CyclotomicField(3);
    OF := RingOfIntegers(F);
    G := HeckeCharacterGroup(4*3*radical_cond*OF : Target := F);
//    G := TargetRestriction(G,F);
//    EG := {{x,x^-1} : x in Elements(G) | Order(x) eq 3};
//    return [Random(x) : x in EG];
    n := #Generators(G);
    H := sub<G|[G.i^ExactQuotient(Order(G.i),3) : i in [1..n] | Order(G.i) mod 3 eq 0]>;
    n := #Generators(H);
    assert #H eq 3^n;
    PV := ProjectiveSpace(GF(3),n-1);
    PVPoints := RationalPoints(PV);
    cubicflds := [];
    for v in PVPoints do
        Append(~cubicflds,&*[(v[i] ne 0) select H.i^(Z!v[i]) else H!1 : i in [1..n]]);
    end for;
    return cubicflds;
/*
    EH := Exclude(Elements(H),H!1);
    for i := 1 to ExactQuotient(3^n-1,2) do
        Exclude(~EH,EH[i]^-1);
    end for;
    return EH;
*/
end function;

/*
function quad_fields1(cond);
    ramprimes := PrimeFactors(cond);
    F := CyclotomicField(3);
    OF := RingOfIntegers(F);
    gens := [F ! -1];
    for p in ramprimes do
        if p mod 3 eq 1 then
            Facp := PrimeIdealsOverPrime(F,p);
            boo, p1 := IsPrincipal(Facp[1]);
            boo, p2 := IsPrincipal(Facp[2]);
            gens := gens cat [p1, p2];
        elif p eq 3 then
            Facp := PrimeIdealsOverPrime(F,3);
            boo, p1 := IsPrincipal(Facp[1]);
            gens := gens cat [p1];
        else
            gens := gens cat [p];
        end if;
    end for;

    V := VectorSpace(GF(2),#gens);
    quad_flds := [];
    for v in V do
        if v eq V ! 0 then continue; end if;
        a := &*[(v[i] eq 1) select gens[i] else 1 : i in [1..#gens]];
        Append(~quad_flds,a);
    end for;
    return quad_flds;
end function;

function cubic_fields1(cond);
    ramprimes := PrimeFactors(cond);
    Z := Integers();
    F<zeta3> := CyclotomicField(3);
    OF := RingOfIntegers(F);
    gens := [zeta3];
    for p in ramprimes do
        if p mod 3 eq 1 then
            Facp := PrimeIdealsOverPrime(F,p);
            boo, p1 := IsPrincipal(Facp[1]);
            boo, p2 := IsPrincipal(Facp[2]);
            gens := gens cat [p1, p2];
        elif p eq 3 then
            Facp := PrimeIdealsOverPrime(F,3);
            boo, p1 := IsPrincipal(Facp[1]);
            gens := gens cat [p1];
        else
            gens := gens cat [p];
        end if;
    end for;

    cubic_flds := [];
    PV := ProjectiveSpace(GF(3),#gens-1);
    ratpts_PV := SetToSequence(RationalPoints(PV));
    assert #ratpts_PV eq (3^#gens - 1)/2;
    for v in ratpts_PV do
        a := &*[(v[i] ne 0) select gens[i]^(Z!v[i]) else 1 : i in [1..#gens]];
        Append(~cubic_flds,a);
    end for;
    return cubic_flds;
end function;

function check_quad_quad1(cond);
    time out1 := quad_fields1(cond);
    time out2 := quad_fields(cond);
    F := Parent(out1[1]);
    assert #out1 eq #out2;
    Ks1 := [RadicalExtension(F,2,out1[i]) : i in [1..#out1]];
    Ks2 := [NumberField(AbelianExtension(psi)) : psi in out2];
    defpols1 := {Polredabs(DefiningPolynomial(AbsoluteField(K))) : K in Ks1};        
    defpols2 := {Polredabs(DefiningPolynomial(AbsoluteField(K))) : K in Ks2};
    return defpols1 eq defpols2;
end function;

function check_cubic_cubic1(cond);
    time out1 := cubic_fields1(cond);
    time out2 := cubic_fields(cond);
    F := Parent(out1[1]);
    assert #out1 eq #out2;
    Ks1 := [RadicalExtension(F,3,out1[i]) : i in [1..#out1]];
    Ks2 := [NumberField(AbelianExtension(psi)) : psi in out2];
    defpols1 := {Polredabs(DefiningPolynomial(AbsoluteField(K))) : K in Ks1};        
    defpols2 := {Polredabs(DefiningPolynomial(AbsoluteField(K))) : K in Ks2};
    return defpols1 eq defpols2;
end function;

Whenever cond is a multiple of 3, the two functions agree and the checks are satisfied.
*/