intrinsic quad_fields(radical_cond :: RngIntElt, F :: Fld : all := true) -> SeqEnum
{returns a sequence of order-2 Hecke characters of the given imaginary quadratic field F,
generating quadratic extensions of F unramified outside the given number}
    OF := RingOfIntegers(F);
    discF := Discriminant(F);
    if discF eq -3 then
        G := HeckeCharacterGroup(4*3*radical_cond*OF : Target := CyclotomicField(1));
    elif discF eq -4 then
        G := HeckeCharacterGroup(8*3*radical_cond*OF : Target := CyclotomicField(1));
// other small imaginary quadratic fields should be considered too.
    end if;
    if all then return G; end if;
    return Exclude(Elements(G),G!1);
end intrinsic;

intrinsic cubic_fields(radical_cond :: RngIntElt, F :: Fld : all := true) -> SeqEnum
{returns a sequence of order-3 Hecke characters of the given imaginary quadratic field F,
generating cubic extensions of F unramified outside the given number}
    Z := Integers();
    OF := RingOfIntegers(F);
    discF := Discriminant(F);
    K := CyclotomicField(3);
    if discF eq -3 then
        G := HeckeCharacterGroup(4*3*radical_cond*OF : Target := K);
    elif discF eq -4 then
        G := HeckeCharacterGroup(9*radical_cond*OF : Target := K);
// other small imaginary quadratic fields should be considered too.
    end if;
    n := #Generators(G);
    H := sub<G|[G.i^ExactQuotient(Order(G.i),3) : i in [1..n] | Order(G.i) mod 3 eq 0]>;
    n := #Generators(H);
    assert #H eq 3^n;
    if all then return H; end if;
    PV := ProjectiveSpace(GF(3),n-1);
    PVPoints := RationalPoints(PV);
    cubicflds := [];
    for v in PVPoints do
        Append(~cubicflds,&*[(v[i] ne 0) select H.i^(Z!v[i]) else H!1 : i in [1..n]]);
    end for;
    return cubicflds;
end intrinsic;
