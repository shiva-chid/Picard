intrinsic possibly_nonsurj_primes(f :: RngUPolElt : radical_cond := 1, primes_bound := 500) -> SeqEnum, SeqEnum
{Given a quartic polynomial f, returns two lists.
1. The first is the list of primes of bad reduction for the Jacobian J of the curve C: y^3 = f(x).
2. The second contains four lists of primes. Put together, they contain all primes ell at which the mod-ell Galois
representation associated to J, is strictly smaller than GL(3,F_ell) or GU(3,F_ell) over Q(zeta_3ell). The first of these lists
is the list of small primes, i.e., primes upto 7. The second one captures primes at which the Galois image is possibly
contained in the reducible type maximal subgroup. The third one corresponds to the field-extension type maximal subgroup 
and the fourth one corresponds to the imprimitive type maximal subgroup.}
    f := suppressed_integer_quartic(f);
    if radical_cond eq 1 then radical_cond := RadCond(f); end if;
    badprimes := PrimeFactors(radical_cond);

    charpols := getcharpols(f : primesend := primes_bound);
    possibly_C1image := C1test(f : radical_cond := radical_cond, primes_bound := primes_bound, charpols := charpols);
    possibly_C3image, possibly_C2image := C2andC3test2(f : radical_cond := radical_cond, primes_bound := primes_bound, charpols := charpols);

    all_possibly_nonsurjprimes := Sort(Setseq(Seqset(badprimes cat [2,3,5,7] cat possibly_C1image cat possibly_C3image cat possibly_C2image)));
//    printf "Primes of bad reduction: %o\n\nReducible image possibly at: %o\n\"Field-extension\" image possibly at: %o\nImprimitive image possibly at: %o\n\nAll possibly non-surjective primes: %o\n", badprimes, possibly_C1image, possibly_C3image, possibly_C2image, all_possibly_nonsurjprimes;
    return badprimes, [[2,3,5,7], possibly_C1image, possibly_C3image, possibly_C2image];
//    return badprimes, all_possibly_nonsurjprimes;
end intrinsic;

intrinsic possibly_nonsurj_primes(f :: RngUPolElt, h :: RngUPolElt : radical_cond := 1, primes_bound := 50) -> SeqEnum, SeqEnum
{Given two polynomials f and h of degrees 4 and 1 respectively, returns two lists.
1. The first is the list of primes of bad reduction for the Jacobian J of the curve C: h(x)y^3 = f(x).
2. The second contains four lists of primes. Put together, they contain all primes ell at which the mod-ell Galois
representation associated to J, is strictly smaller than GL(3,F_ell) or GU(3,F_ell) over Q(zeta_3ell). The first of these lists
is the list of small primes, i.e., primes upto 7. The second one captures primes at which the Galois image is possibly
contained in the reducible type maximal subgroup. The third one corresponds to the field-extension type maximal subgroup 
and the fourth one corresponds to the imprimitive type maximal subgroup.}
    f1,h1 := suppressed_integer_quartic(f,h);
    if radical_cond eq 1 then radical_cond := RadCond(f1,h1); end if;
    badprimes := PrimeFactors(radical_cond);

    charpols := getcharpols(f1,h1 : primesend := primes_bound);
    possibly_C1image := C1test(f1,h1 : radical_cond := radical_cond, primes_bound := primes_bound, charpols := charpols);
    possibly_C3image, possibly_C2image := C2andC3test2(f1,h1 : radical_cond := radical_cond, primes_bound := primes_bound, charpols := charpols);

    all_possibly_nonsurjprimes := Sort(Setseq(Seqset(badprimes cat [2,3,5,7] cat possibly_C1image cat possibly_C3image cat possibly_C2image)));
//    printf "Primes of bad reduction: %o\n\nReducible image possibly at: %o\n\"Field-extension\" image possibly at: %o\nImprimitive image possibly at: %o\n\nAll possibly non-surjective primes: %o\n", badprimes, possibly_C1image, possibly_C3image, possibly_C2image, all_possibly_nonsurjprimes;
    return badprimes, [[2,3,5,7], possibly_C1image, possibly_C3image, possibly_C2image];
//    return badprimes, all_possibly_nonsurjprimes;
end intrinsic;

intrinsic possibly_nonsurj_primes(C :: CrvHyp : radical_cond := 1, primes_bound := 500, F := Rationals()) -> SeqEnum, SeqEnum
{Given a hyperelliptic curve C of genus 3 having an imaginary quadratic field F as its geometric
endomorphism algebra, returns two lists.
1. The first is the list of primes of bad reduction for the Jacobian J of C.
2. The second contains four lists of primes. Put together, they contain all primes ell at which the
mod-ell Galois image associated to J, is strictly smaller than GL(3,F_ell) or GU(3,F_ell) over F(zeta_ell):
The first of these lists is the list of small primes, i.e., primes upto 7 along with primes ramified in F.
The second one captures primes at which the Galois image is possibly contained in the reducible type
maximal subgroup.
The third one corresponds to the field-extension type maximal subgroup 
and the fourth one corresponds to the imprimitive type maximal subgroup.}
    if F eq Rationals() then
        out1, out2, out3 := HeuristicEndomorphismAlgebra(C : Geometric := true);
        assert Dimension(out2) eq 2;
        F := NumberField(MinimalPolynomial(out2.2)); F := Polredabs(F);
        assert Discriminant(F) lt 0; printf "The given curve has endomorphism algebra = \n%o\n", F;
    end if;
    if radical_cond eq 1 then radical_cond := &*BadPrimes(C); end if;
    charpols := getcharpols(C : primesend := primes_bound);
    badprimes := PrimeFactors(radical_cond);
    smallprimes := Sort(Setseq({2,3,5,7} join {p : p in PrimeFactors(Discriminant(F))}));

    possibly_C1image := C1test(C : radical_cond := radical_cond, primes_bound := primes_bound, charpols := charpols, F := F);
    possibly_C3image, possibly_C2image := C2andC3test2(C : radical_cond := radical_cond, primes_bound := primes_bound, charpols := charpols, F := F);

    all_possibly_nonsurjprimes := Sort(Setseq(Seqset(badprimes cat smallprimes cat possibly_C1image cat possibly_C3image cat possibly_C2image)));
//    printf "Primes of bad reduction: %o\nReducible image possibly at: %o\n\"Field-extension\" image possibly at: %o\nImprimitive image possibly at: %o\nAll possibly non-surjective primes: %o\n============================================\n\n", badprimes, possibly_C1image, possibly_C3image, possibly_C2image, all_possibly_nonsurjprimes;
    return badprimes, [smallprimes, possibly_C1image, possibly_C3image, possibly_C2image];
//    return badprimes, all_possibly_nonsurjprimes;
end intrinsic;

