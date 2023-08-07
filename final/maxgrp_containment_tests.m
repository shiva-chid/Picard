intrinsic suppressed_integer_quartic(f :: RngUPolElt) -> RngUPolElt
{Given a quartic polynomial f over the rationals, returns an integral polynomial g of the 
form x^4+a*x^2+b*x+c, such that the curve y^3=f is isomorphic to the curve y^3=g.}
    P<x> := PolynomialRing(Rationals());
    a4 := Coefficient(f,4);
    if a4 ne 1 then
        f := a4^3*Evaluate(f,x/a4);
    end if;

    a3 := Coefficient(f,3);
    if a3 ne 0 then
        f := Evaluate(f,x-a3/4);
    end if;

    coeffs := Coefficients(f)[1..3];
    coeffs_dens := [Denominator(x) : x in coeffs];
    pfacs_dens := &join[Set(PrimeFactors(x)) : x in coeffs_dens];
    m := (pfacs_dens eq {}) select 1 else &*[p^n where n is Maximum([Ceiling(Valuation(coeffs_dens[i],p)/(15-3*i)) : i in [1..3]]) : p in pfacs_dens];

    P<x> := PolynomialRing(Integers());
    return P!([m^(15-3*i)*coeffs[i] : i in [1..3]] cat [0,1]);
end intrinsic;

intrinsic RadCond(f :: RngUPolElt) -> RngIntElt
{Given a quartic polynomial f over the rationals, returns the product of the bad primes 
of the suppressed integral model of the curve y^3=f. Some prime factors could be repeated.}
    f := suppressed_integer_quartic(f);
    radical_disc := &*([1] cat [p : p in PrimeFactors(Discriminant(f))]);
    radical_leadcoeff := &*([1] cat [p : p in PrimeFactors(Coefficient(f,4))]);
    radical_cond := radical_leadcoeff*radical_disc;
    if radical_cond mod 3 ne 0 then
        radical_cond := 3*radical_cond;
    end if;
    return radical_cond;
end intrinsic;

/*
intrinsic getcharpol(f :: RngUPolElt, p :: RngIntElt : radical_cond := 1) -> RngUPolElt
{returns the characteristic polynomial of Frobenius at p on the Tate module of the 
Jacobian of the curve y^3=f, if p is a good prime}
    f := suppressed_integer_quartic(f);
    P<x> := Parent(f);
    if radical_cond eq 1 then radical_cond := RadCond(f); end if;
    require radical_cond mod p ne 0 : "Bad Prime";
    pstr := IntegerToString(p);
    fstr := &cat(Split(Sprint(f)," "));
    C := Coefficients(f)[1..3];
    cartmanmat := Pipe("hwlpoly y^3=" cat fstr cat " " cat pstr cat " 1","");
    Lpol := liftLpoly(cartmanmat,C);
    require #Lpol eq 1 : "Error in computing L-polynomial";
    return P ! Reverse(Lpol[1,2]);
end intrinsic;
*/

intrinsic getcharpols(f :: RngUPolElt : radical_cond := 1, primesstart := 3, primesend := 500) -> SeqEnum
{returns a sequence of tuples <p,charpol_p> where charpol_p is the characteristic polynomial 
of Frobenius at p on the Tate module of the Jacobian of the curve y^3=f, and p ranges over 
the good primes NthPrime(N) for all N within the given bounds. The optional parameter radical_cond
should be some integer divisible by all the bad primes of the curve.}
    f := suppressed_integer_quartic(f);
    P<x> := Parent(f);
    if radical_cond eq 1 then radical_cond := RadCond(f); end if;
    Lpols := [];
    N := Ceiling(Log(2,NthPrime(primesend)));
    Nstr := IntegerToString(N);
    fstr := &cat(Split(Sprint(f)," "));
    C := Coefficients(f)[1..3];
    hwlpolys_standard_message := Pipe("hwlpolys y^3=" cat fstr cat " " cat Nstr cat " 1 0 -1 0 " cat fstr cat ".txt","");
    fil := Open(fstr cat ".txt", "r");
    Lpols := liftLpolys(fil,C);
    delete_file := Pipe("rm " cat fstr cat ".txt","");
    charpols := [<x[1],P!Reverse(x[2])> : x in Lpols];
    return charpols;
end intrinsic;


////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////


intrinsic Bracket(r :: RngIntElt, f :: RngUPolElt) -> RngUPolElt
{Given a positive integer r, and a polynomial f, returns the polynomial whose roots are the r-th powers
of the roots of f.}
    P<x> := Parent(f);
    P2<y> := PolynomialRing(P);
    return Resultant(P2 ! Coefficients(f), x-y^r);
end intrinsic;

intrinsic Bound(pandcharpol :: Tup, alpha :: RngCycElt) -> RngCycElt
{Given a tuple consisting of a rational prime p congruent to 1 mod 3 and the characteristic polynomial of 
Frobenius at p, and a generator alpha of a prime ideal of Z[zeta_3] above p, returns the the Billerey Bound, 
i.e., the analogue to the B_p bound given in Billerey paper.}
    p := pandcharpol[1];
    charpol := pandcharpol[2];
//    newpol := Bracket(72,charpol);
    newpol := WeilPolynomialOverFieldExtension(charpol,72);
    return &*[Evaluate(newpol,r^72): r in {1,alpha,p,alpha*p,p^2,alpha^2}];
end intrinsic;

intrinsic C1test(f :: RngUPolElt : radical_cond := 1, primes_bound := 500, charpols := []) -> SeqEnum
{Given a monic suppressed integral quartic polynomial f = x^4 + a x^2 + b x + c, returns a list of
primes which contains all primes ell at which the mod-ell Galois image associated to the Jacobian of
the curve y^3 = f, is contained in the C1-type maximal subgroup of GL(3,F_ell), i.e., the reducible
type maximal subgroup. These primes are the ones that divide the Billerey Bounds associated to all good 
primes congruent to 1 mod 3 that are considered. The optional parameters are
1. some integer divisible by all the bad primes of the curve.
2. a bound for how many primes to consider.
3. a precomputed list of tuples consisting of a prime p and the characteristic polynomial of Frobenius at p,
for various primes.}
    Z := Integers();
    F := CyclotomicField(3);
    OF := RingOfIntegers(F);
    if radical_cond eq 1 then radical_cond := RadCond(f); end if;
    if charpols eq [] then charpols := getcharpols(f : radical_cond := radical_cond, primesend := primes_bound); end if;
    Bignum := 0;
    for pandcharpol in charpols do
        p := pandcharpol[1];
        charpol := pandcharpol[2];
        if (p mod 3 ne 1) or (radical_cond mod p eq 0) then continue; end if;
        pFacs := PrimeIdealsOverPrime(F,p);
        for pfac in pFacs do
            tf, a := IsPrincipal(pfac);
            B := Bound(pandcharpol,a);
            Bignum := GCD(Bignum,p*Norm(B)); // The bound associated to B_p doesn't give us any information on p.
            if Bignum eq 2^Valuation(Bignum,2)*3^Valuation(Bignum,3) then
                return PrimeFactors(Bignum);
            end if;
        end for;
    end for;
    require Bignum ne 0 : "C1test fails.";
    return PrimeFactors(Bignum);
end intrinsic;


////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////


intrinsic C3test(f :: RngUPolElt : radical_cond := 1, primes_bound := 500, charpols := []) -> SeqEnum
{Given a monic suppressed integral quartic polynomial f = x^4 + a x^2 + b x + c, returns a list of
primes which contains all primes ell at which the mod-ell Galois image associated to the Jacobian of
the curve y^3 = f, is contained in the C3-type maximal subgroup of GL(3,F_ell), i.e., the field-extension
type maximal subgroup. The optional parameters are
1. some integer divisible by all the bad primes of the curve.
2. a bound for how many primes to consider.
3. a precomputed list of tuples consisting of a prime p and the characteristic polynomial of Frobenius at p,
for various primes.}
    Z := Integers();
    F := CyclotomicField(3);
    OF := RingOfIntegers(F);
    C3primes := [];
    if radical_cond eq 1 then radical_cond := RadCond(f); end if;
    if charpols eq [] then charpols := getcharpols(f : radical_cond := radical_cond, primesend := primes_bound); end if;
    charpols := [x : x in charpols | x[1] gt 3];
    factored_charpols := [(x[1] mod 3 eq 1) select <x[1],Factorisation(ChangeRing(x[2],F))> else <x[1],[]> : x in charpols];
    primes_F := [(x[1] mod 3 eq 1) select PrimeIdealsOverPrime(F,x[1]) else [x[1]*OF] : x in charpols];

    CubicHeckeG := cubic_fields(radical_cond : noduplicates := false);
//    print #CubicHeckeG;
    gens_CHG := [CubicHeckeG.i : i in [1..#Generators(CubicHeckeG)]];
    RCl, pi := RayClassGroup(Modulus(CubicHeckeG));
    matrix_of_vals := [[gens_CHG[j](pi(RCl.i)) : i in [1..#Generators(RCl)]] : j in [1..#gens_CHG]];
    genvals := [[[&*[(v[i] ne 0) select matrix_of_vals[j,i]^v[i] else 1 : i in [1..#v]] where v is Eltseq(x @@ pi) : x in p] : p in primes_F] : j in [1..#gens_CHG]];
    n := #gens_CHG;
    PV := ProjectiveSpace(GF(3),n-1);
    PVPoints := RationalPoints(PV);
    for v in PVPoints do
        bignum := 0;
        for i := 1 to #charpols do
            p := primes_F[i];
            charpol := charpols[i,2];
            facs := factored_charpols[i,2];
            if #p eq 1 then
                chivalatp := &*[(v[j] ne 0) select genvals[j,i,1]^(Z!v[j]) else 1 : j in [1..n]];
                if chivalatp ne 1 then
//                    printf "Using an inert prime in C3test.\n";
                    newnum := Coefficient(charpol,5);
//                    if newnum ne 0 then printf "Inert prime works.\n"; end if;
                    bignum := GCD(bignum,newnum);
                    if bignum eq 1 then break; end if;
                end if;
            elif #p eq 2 then
                chivalatp1 := &*[(v[j] ne 0) select genvals[j,i,1]^(Z!v[j]) else 1 : j in [1..n]];
                chivalatp2 := &*[(v[j] ne 0) select genvals[j,i,2]^(Z!v[j]) else 1 : j in [1..n]];
                if chivalatp1 ne 1 and chivalatp2 ne 1 then
                    if #facs eq 2 and Degree(facs[1,1]) eq 3 and Degree(facs[2,1]) eq 3 and facs[1,2] eq 1 and facs[2,2] eq 1 then
//                        printf "Using a split prime in C3test.\n";
                        fac1 := facs[1,1];
                        fac2 := facs[2,1];
                        newnum := Z ! (Coefficient(fac1,2)*Coefficient(fac2,2));
//                        if newnum ne 0 then printf "Split prime works.\n"; end if;
                        bignum := GCD(bignum,newnum);
                        if bignum eq 1 then break; end if;
                    end if;
                end if;
            end if;
        end for;
        require bignum ne 0 : "C3test fails.";
        C3primes := Sort(SetToSequence(Set(C3primes cat PrimeFactors(bignum))));
    end for;
    return Exclude(C3primes,3);
end intrinsic;


////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////


intrinsic C2andC3test(f :: RngUPolElt : radical_cond := 1, primes_bound := 500, charpols := []) -> SeqEnum, SeqEnum
{Given a monic suppressed integral quartic polynomial f = x^4 + a x^2 + b x + c, returns two lists of primes.
1. The first list contains all primes ell at which the mod-ell Galois image associated to the Jacobian of
the curve y^3 = f, is contained in the C3-type maximal subgroup of GL(3,F_ell), i.e., the field-extension
type maximal subgroup.
2. The second list contains all primes ell at which the mod-ell Galois image is contained in the C2-type maximal 
subgroup of GL(3,F_ell), i.e., the imprimitive type maximal subgroup.
The optional parameters are
1. some integer divisible by all the bad primes of the curve.
2. a bound for how many primes to consider.
3. a precomputed list of tuples consisting of a prime p and the characteristic polynomial of Frobenius at p,
for various primes.}
    Z := Integers();
    F := CyclotomicField(3);
    OF := RingOfIntegers(F);
    if radical_cond eq 1 then radical_cond := RadCond(f); end if;
    if charpols eq [] then charpols := getcharpols(f : radical_cond := radical_cond, primesend := primes_bound); end if;
    try
        C3primes := C3test(f : radical_cond := radical_cond, primes_bound := primes_bound, charpols := charpols);
    catch e;
        C3primes := [];
        require C3primes ne [] : "C3test fails.";
    end try;

    C2primes := C3primes;
    factored_charpols := [<x[1],Factorisation(ChangeRing(x[2],F))> : x in charpols | x[1] mod 3 eq 1];
    primes_F := [PrimeIdealsOverPrime(F,x[1]) : x in factored_charpols];
    quaddirichletchars := quad_fields(radical_cond);
    for chi in quaddirichletchars do
        bignum := 0;
        for i := 1 to #factored_charpols do
            p := factored_charpols[i,1];
            facs := factored_charpols[i,2];
            pfacs := primes_F[i];
            if chi(pfacs[1]) ne 1 and chi(pfacs[2]) ne 1 then
                if #facs eq 2 and Degree(facs[1,1]) eq 3 and Degree(facs[2,1]) eq 3 and facs[1,2] eq 1 and facs[2,2] eq 1 then
//                    printf "Using a split prime in C2test. ";
                    fac1 := facs[1,1];
                    fac2 := facs[2,1];
                    newnum := Z ! ((Coefficient(fac1,2)*Coefficient(fac1,1)-Coefficient(fac1,0))*(Coefficient(fac2,2)*Coefficient(fac2,1)-Coefficient(fac2,0)));
//                    if newnum ne 0 then printf "It has worked.\n"; end if;
                    bignum := GCD(bignum,newnum);
                    if bignum eq 1 then break; end if;
                end if;
            end if;
        end for;
        require bignum ne 0 : "C2test fails.";
        C2primes := Sort(SetToSequence(Set(C2primes cat PrimeFactors(bignum))));
    end for;
    return C3primes, Exclude(C2primes,3);
end intrinsic;

