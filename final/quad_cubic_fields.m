intrinsic quad_fields(radical_cond :: RngIntElt : all := true) -> SeqEnum
{returns a sequence of order-2 Hecke characters of Q(zeta_3), generating quadratic extensions of Q(zeta_3) unramified outside the given number}
    F := CyclotomicField(3);
    OF := RingOfIntegers(F);
    G := HeckeCharacterGroup(4*3*radical_cond*OF : Target := CyclotomicField(1));
    if all then
        return G;
    end if;
    return Exclude(Elements(G),G!1);
end intrinsic;

intrinsic cubic_fields(radical_cond :: RngIntElt : all := true) -> SeqEnum
{returns a sequence of order-3 Hecke characters of Q(zeta_3), generating cubic extensions of Q(zeta_3) unramified outside the given number}
    Z := Integers();
    F := CyclotomicField(3);
    OF := RingOfIntegers(F);
    G := HeckeCharacterGroup(4*3*radical_cond*OF : Target := F);
    n := #Generators(G);
    H := sub<G|[G.i^ExactQuotient(Order(G.i),3) : i in [1..n] | Order(G.i) mod 3 eq 0]>;
    n := #Generators(H);
    assert #H eq 3^n;
    if all then
        return H;
    end if;
    PV := ProjectiveSpace(GF(3),n-1);
    PVPoints := RationalPoints(PV);
    cubicflds := [];
    for v in PVPoints do
        Append(~cubicflds,&*[(v[i] ne 0) select H.i^(Z!v[i]) else H!1 : i in [1..n]]);
    end for;
    return cubicflds;
end intrinsic;
