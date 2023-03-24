function quad_fields(radical_cond : cond := 1);
    F := CyclotomicField(3);
    OF := RingOfIntegers(F);
    if cond ne 1 then
        G := HeckeCharacterGroup(4*cond*OF);
    else
        G := HeckeCharacterGroup(4*3*radical_cond*OF);
    end if;
    G := TargetRestriction(G,CyclotomicField(1));
    EG := [x : x in Elements(G) | Order(x) eq 2];
    return EG;
end function;

function cubic_fields(radical_cond : cond := 1);
    F := CyclotomicField(3);
    OF := RingOfIntegers(F);
    if cond ne 1 then
        G := HeckeCharacterGroup(3*cond*OF);
    else
        G := HeckeCharacterGroup(4*3*radical_cond*OF);
    end if;
    G := TargetRestriction(G,F);
    EG := [x : x in Elements(G) | Order(x) eq 3];
    EG_prune := {};
    for x in EG do
        Include(~EG_prune,{x,x^-1});
    end for;
    return [Random(x) : x in EG_prune];
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