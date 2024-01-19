intrinsic suppressed_integer_quartic(f :: RngUPolElt) -> RngUPolElt
{Given a quartic polynomial f over the rationals, returns an integral polynomial g of the 
form x^4+a*x^2+b*x+c, such that the curve y^3=f is isomorphic to the curve y^3=g.}
    require Degree(f) eq 4 : "f must have degree 4";
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

intrinsic suppressed_integer_quartic(f :: RngUPolElt, h :: RngUPolElt) -> RngUPolElt, RngUPolElt
{Given two polynomials f and h of degrees 4 and 1 respectively over the rationals, 
returns integral polynomials f1 and h1 of the same degrees such that f1 has the
form x^4+a*x^2+b*x+c, and the curves h1(x)y^3=f1(x) and h(x)y^3=f(x) are isomorphic.
If f and h are integral, we do not do anything, i.e., we do not try to suppress the cubic term of f or make it monic.}
    if Degree(h) eq 0 then return suppressed_integer_quartic(f/Coefficient(h,0)), 1; end if;
    require Degree(f) eq 4 : "f must have degree 4";
    require Degree(h) eq 1 : "h must have degree 1";
    P<x> := PolynomialRing(Integers());
    try
        f1 := P ! f;
        h1 := P ! h;
        return f1, h1;
    catch e;
    end try;

    P<x> := PolynomialRing(Rationals());
    a4 := Coefficient(f,4);
    f1 := f/a4;
    h1 := h/a4;
    a3 := Coefficient(f1,3);
    if a3 ne 0 then
        f1 := Evaluate(f1,x-a3/4);
        h1 := Evaluate(h1,x-a3/4);
    end if;

    coeffs := Coefficients(f1)[1..3];
    coeffs_dens := [Denominator(x) : x in coeffs];
    pfacs_dens := &join[Set(PrimeFactors(x)) : x in coeffs_dens];
    m := (pfacs_dens eq {}) select 1 else &*[p^n where n is Maximum([Ceiling(Valuation(coeffs_dens[i],p)/(15-3*i)) : i in [1..3]]) : p in pfacs_dens];

    P<x> := PolynomialRing(Integers());
    f1 := P!([m^(15-3*i)*coeffs[i] : i in [1..3]] cat [0,1]);
    h1 := Coefficient(h1,0)*m^3+Coefficient(h1,1)*x;
    coeffs := Coefficients(h1);
    coeffs_dens := [Denominator(x) : x in coeffs];
    pfacs_dens := &join[Set(PrimeFactors(x)) : x in coeffs_dens];
    m := (pfacs_dens eq {}) select 1 else &*[p^n where n is Maximum([Ceiling(Valuation(x,p)/3) : x in coeffs_dens]) : p in pfacs_dens];
    h1 := P![m^3*x : x in coeffs];
    
    return f1, h1;
end intrinsic;


intrinsic RadCond(f :: RngUPolElt) -> RngIntElt
{Given a quartic polynomial f over the rationals, returns the product of the bad primes 
of the suppressed integral model of the curve y^3=f.}
    f := suppressed_integer_quartic(f);
    radical_disc := &*([1] cat [p : p in PrimeFactors(Discriminant(f))]);
    radical_leadcoeff := &*([1] cat [p : p in PrimeFactors(Coefficient(f,4))]);
    radical_cond := LCM(radical_leadcoeff,radical_disc);
    if radical_cond mod 3 ne 0 then
        radical_cond := 3*radical_cond;
    end if;
    return radical_cond;
end intrinsic;

intrinsic RadCond(f :: RngUPolElt, h :: RngUPolElt) -> RngIntElt
{Given two polynomials f and h of degrees 4 and 1 respectively over the rationals, 
returns the product of bad primes of the suppressed integral model of the curve h(x)y^3=f(x).
Some prime factors could be repeated.}
    f1, h1 := suppressed_integer_quartic(f,h);
    a := Coefficient(h1,1);
    b := Coefficient(h1,0);
    require Evaluate(f1,-b/a) ne 0 : "Curve is reducible";
    radical_disc := &*([1] cat [p : p in PrimeFactors(Discriminant(f1))]);
    radical_leadcoeff := &*([1] cat [p : p in PrimeFactors(Coefficient(f,4))]);
    radical_cond := LCM(radical_leadcoeff,radical_disc);
    radical_cond := LCM(radical_cond,GCD(a,b));
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

intrinsic getcharpols(f :: RngUPolElt : primesend := 500) -> SeqEnum
{returns a sequence of tuples <p,charpol_p> where charpol_p is the characteristic polynomial 
of Frobenius at p on the Tate module of the Jacobian of the curve y^3=f, and p ranges over 
the good primes NthPrime(N) for all N within the given bounds.}
    f := suppressed_integer_quartic(f);
    P<x> := Parent(f);
    Lpols := [];
    N := Ceiling(Log(2,NthPrime(primesend)));
    Nstr := IntegerToString(N);
    fstr := &cat(Split(Sprint(f)," *"));
    filename := Sprintf("temp_%o", Getpid());
    System("hwlpolys y^3=" cat fstr cat " " cat Nstr cat " 1 0 -1 0 " cat filename);
    fil := Open(filename, "r");
    C := Coefficients(f)[1..3];
    Lpols := liftLpolys(fil,C);
    delete(fil);
    System("rm " cat filename);
    charpols := [<x[1],P!Reverse(x[2])> : x in Lpols];
    return charpols;
end intrinsic;

intrinsic getcharpols(f :: RngUPolElt, h :: RngUPolElt : primesend := 50) -> SeqEnum
{returns a sequence of tuples <p,charpol_p> where charpol_p is the characteristic polynomial 
of Frobenius at p on the Tate module of the Jacobian of the curve h(x)y^3=f(x),
and p ranges over the good primes NthPrime(N) for all N within the given bounds.}
    f1, h1 := suppressed_integer_quartic(f,h);
    radical_cond := RadCond(f1,h1);
    P<x> := Parent(f1);
    Lpols := [];
    N := NthPrime(primesend);

    P3<x,y,z> := PolynomialRing(Integers(),3);
    F := y^3*Homogenization(Evaluate(h1,x),z)-Homogenization(Evaluate(f1,x),z);
    p := 5;
    charpols := [];
    while p le N do
        if radical_cond mod p ne 0 then
            cmd := Sprintf("\"from pycontrolledreduction import controlledreduction; R.<x,y,z> = ZZ[]; print(controlledreduction(%o, %o, False))\"", F, p);
            val := Pipe("sage -c " cat cmd, "");
            val := Split(val,"T");
            val := &cat[val[i] cat "x" : i in [1..#val-1]] cat val[#val];
            charpol := <p, P ! Reverse(Coefficients(UnivariatePolynomial(eval val)))>;
            Append(~charpols, charpol);
        end if;
        p := NextPrime(p);
    end while;
    return charpols;
end intrinsic;

intrinsic get_faccharpols_overQzeta3(f :: RngUPolElt : primesend := 500) -> SeqEnum
{returns a sequence of tuples <p,faccharpol_p> where faccharpol_p is the factorisation over Q(zeta_3) 
of the characteristic polynomial of Frobenius at p on the Tate module of the Jacobian of the curve y^3=f, 
and p ranges over the good primes NthPrime(N) for all N within the given bounds.}
    f := suppressed_integer_quartic(f);
    P<x> := Parent(f);
    Lpols := [];
    N := Ceiling(Log(2,NthPrime(primesend)));
    Nstr := IntegerToString(N);
    fstr := &cat(Split(Sprint(f)," *"));
    C := Coefficients(f)[1..3];
    hwlpolys_standard_message := Pipe("hwlpolys y^3=" cat fstr cat " " cat Nstr cat " 1 0 -1 0 " cat fstr cat ".txt","");
    fil := Open(fstr cat ".txt", "r");
    Lpols := liftLpolys(fil,C);
    delete_file := Pipe("rm " cat fstr cat ".txt","");
    charpols := [<x[1],P!Reverse(x[2])> : x in Lpols];

    F := CyclotomicField(3);
    OF := RingOfIntegers(F);
    fac_charpols := [<x[1],(x[1] mod 3 eq 1) select Factorisation(ChangeRing(x[2],OF)) else Factorisation(ChangeRing(Bracket(2,x[2]),OF))> : x in charpols];
    return fac_charpols;
end intrinsic;

intrinsic get_faccharpols_overQzeta3(f :: RngUPolElt, h :: RngUPolElt : primesend := 50) -> SeqEnum
{returns a sequence of tuples <p,faccharpol_p> where faccharpol_p is the factorisation over Q(zeta_3) 
of the characteristic polynomial of Frobenius at p on the Tate module of the Jacobian of the curve h(x)y^3=f(x), 
and p ranges over the good primes NthPrime(N) for all N within the given bounds.}
    charpols := getcharpols(f,h : primesend := primesend);
    F := CyclotomicField(3);
    OF := RingOfIntegers(F);
    fac_charpols := [<x[1],(x[1] mod 3 eq 1) select Factorisation(ChangeRing(x[2],OF)) else Factorisation(ChangeRing(Bracket(2,x[2]),OF))> : x in charpols];
    return fac_charpols;
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
    if charpols eq [] then charpols := getcharpols(f : primesend := primes_bound); end if;
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

intrinsic C1test(f :: RngUPolElt, h :: RngUPolElt : radical_cond := 1, primes_bound := 50, charpols := []) -> SeqEnum
{Given two polynomials f and h of degrees 4 and 1 respectively, returns a list of
primes which contains all primes ell at which the mod-ell Galois image associated to the Jacobian of
the curve h(x)y^3 = f(x), is contained in the C1-type maximal subgroup of GL(3,F_ell), i.e., the reducible
type maximal subgroup. These primes are the ones that divide the Billerey Bounds associated to all good 
primes congruent to 1 mod 3 that are considered. The optional parameters are
1. some integer divisible by all the bad primes of the curve.
2. a bound for how many primes to consider.
3. a precomputed list of tuples consisting of a prime p and the characteristic polynomial of Frobenius at p,
for various primes.}
    Z := Integers();
    F := CyclotomicField(3);
    OF := RingOfIntegers(F);
    if radical_cond eq 1 then radical_cond := RadCond(f,h); end if;
    if charpols eq [] then charpols := getcharpols(f,h : primesend := primes_bound); end if;
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
    if charpols eq [] then charpols := getcharpols(f : primesend := primes_bound); end if;
    charpols := [x : x in charpols | x[1] gt 3];
    factored_charpols := [(x[1] mod 3 eq 1) select <x[1],Factorisation(ChangeRing(x[2],F))> else <x[1],[]> : x in charpols];
    primes_F := [(x[1] mod 3 eq 1) select PrimeIdealsOverPrime(F,x[1]) else [x[1]*OF] : x in charpols];

    CubicHeckeG := cubic_fields(radical_cond);
//    print #CubicHeckeG;
    gens_CHG := [CubicHeckeG.i : i in [1..#Generators(CubicHeckeG)]];
    RCl, pi := RayClassGroup(Modulus(CubicHeckeG));
    matrix_of_vals := [[gens_CHG[j](pi(RCl.i)) : i in [1..#Generators(RCl)]] : j in [1..#gens_CHG]];
    assert {x^3 : x in &cat(matrix_of_vals)} eq {1};
    genvals := [[[&*[(v[i] ne 0) select matrix_of_vals[j,i]^(v[i] mod 3) else 1 : i in [1..#v]] where v is Eltseq(x @@ pi) : x in p] : p in primes_F] : j in [1..#gens_CHG]];
    n := #gens_CHG;
    PV := ProjectiveSpace(GF(3),n-1);
    PVPoints := RationalPoints(PV);
    possiblecubicchars := [];
    for v in PVPoints do
        bignum := 0;
        chi := &*[(v[j] ne 0) select gens_CHG[j]^(Z!v[j]) else CubicHeckeG!1 : j in [1..n]];
        boo := true;
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
                    if bignum eq 1 then boo := false; break; end if;
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
                        if bignum eq 1 then boo := false; break; end if;
                    end if;
                end if;
            end if;
        end for;
        require bignum ne 0 : "C3test fails.";
        if boo then
            pfacsbignum := PrimeFactors(bignum);
            Append(~possiblecubicchars,<pfacsbignum,chi>);
            C3primes := Sort(SetToSequence(Set(C3primes cat pfacsbignum)));
        end if;
    end for;
    n := Nresults();
    if n eq 2 then
        return Exclude(C3primes,3), possiblecubicchars;
    end if;
    return Exclude(C3primes,3);
end intrinsic;


intrinsic C3test2(f :: RngUPolElt : radical_cond := 1, primes_bound := 500, charpols := []) -> SeqEnum
{Given a monic suppressed integral quartic polynomial f = x^4 + a x^2 + b x + c, returns a list of
primes which contains all primes ell at which the mod-ell Galois image associated to the Jacobian of
the curve y^3 = f, is contained in the C3-type maximal subgroup of GL(3,F_ell), i.e., the field-extension
type maximal subgroup. The optional parameters are
1. some integer divisible by all the bad primes of the curve.
2. a bound for how many primes to consider.
3. a precomputed list of tuples consisting of a prime p and the characteristic polynomial of Frobenius at p,
for various primes.}
    Z := Integers();
    P<x> := PolynomialRing(Z);
    F<zeta3> := CyclotomicField(3);
    OF := RingOfIntegers(F);
    C3primes := [];
    if radical_cond eq 1 then radical_cond := RadCond(f); end if;
    if charpols eq [] then charpols := getcharpols(f : primesend := primes_bound); end if;
    charpols := [x : x in charpols | x[1] gt 3];

    CubicHeckeG := cubic_fields(radical_cond);
    n := #Generators(CubicHeckeG);
    gens_CHG := [CubicHeckeG.i : i in [1..n]];
    RCl, pi := RayClassGroup(Modulus(CubicHeckeG));
    matrix_of_vals := [[gens_CHG[j](pi(RCl.i)) : i in [1..#Generators(RCl)]] : j in [1..#gens_CHG]];
    assert {x^3 : x in &cat(matrix_of_vals)} eq {1};

    function mu3toZmod3(zeta);
        if zeta eq 1 then
            return 0;
        elif zeta eq zeta3 then
            return 1;
        else
            assert zeta eq zeta3^2;
            return 2;
        end if;
    end function;

/*
    factored_charpols := [(x[1] mod 3 eq 1) select <x[1],Factorisation(ChangeRing(x[2],F))> else <x[1],Factorisation(ChangeRing(Bracket(2,x[2]),F))> : x in charpols];
    primes_F := [(x[1] mod 3 eq 1) select PrimeIdealsOverPrime(F,x[1]) else [x[1]*OF] : x in charpols];
    genvals := [[[mu3toZmod3(&*[(v[i] ne 0) select matrix_of_vals[j,i]^(v[i] mod 3) else 1 : i in [1..#v]]) : j in [1..n]] where v is Eltseq(x @@ pi) : x in p] : p in primes_F];
*/
    aps := [];
    mat := Matrix(GF(3),n,1,[0 : i in [1..n]]);
    possible_ells_found := false;
    for i := 1 to #charpols do
        p := charpols[i,1];
        ap := Coefficient(charpols[i,2],5);
        bp := Coefficient(charpols[i,2],4);
        if p mod 3 eq 1 then
            if ap eq 0 then continue; end if;
            fac_charpol := Factorisation(ChangeRing(charpols[i,2],F));
            pabove := PrimeIdealsOverPrime(F,p);
        elif p mod 3 eq 2 then
            if ap^2-2*bp eq 0 then continue; end if;
//            fac_charpol := Factorisation(ChangeRing(Bracket(2,charpols[i,2]),F));
            charpol_in_xsq := P![Coefficient(charpols[i,2],2*j) : j in [0..3]];
            assert Evaluate(charpol_in_xsq,x^2) eq charpols[i,2];
            fac_charpol := [<charpol_in_xsq,1>,<charpol_in_xsq,1>];
            pabove := [p*OF];
        end if;
//        printf "Prime = %o, Lpol Factorisation type = %o\n", p, [<Degree(x[1]),x[2]> : x in fac_charpol];
        if #fac_charpol eq 2 and Degree(fac_charpol[1,1]) eq 3 and Degree(fac_charpol[2,1]) eq 3 then
            ap1 := Coefficient(fac_charpol[1,1],2);
            if ap1 eq 0 then continue; end if;
            if p mod 3 eq 1 then
                Append(~aps,ap);
            elif p mod 3 eq 2 then
                Append(~aps,ap^2-2*bp);
            end if;
            nm_ap1 := Z!Norm(ap1);
            Append(~aps,nm_ap1);
            cols := [[mu3toZmod3(&*[(v[i] mod 3 ne 0) select matrix_of_vals[j,i]^(v[i] mod 3) else 1 : i in [1..#v]]) : j in [1..n]] where v is Eltseq(x @@ pi) : x in pabove];
            for col in cols do
                mat := HorizontalJoin(mat,Matrix(GF(3),n,1,col));
            end for;
            kermat := Kernel(mat);
            dimkermat := Dimension(kermat);
//            printf "Size of the matrix is %ox%o and row kernel has dimension %o\n", NumberOfRows(mat), NumberOfColumns(mat), dimkermat;
            if dimkermat eq 0 then
                lcm_aps := LCM(aps);
                require lcm_aps ne 0 : "C3test fails.";
                possible_ells := Exclude(PrimeFactors(lcm_aps),3);
//                printf "Possible ells after first level in C3test2: %o\n", possible_ells;
//                return possible_ells;
                break;
            end if;
        end if;
    end for;

// weeding out extraneous primes
    for i := 1 to #charpols do
        p := charpols[i,1];
        if p mod 3 eq 1 then
            fac_charpol := Factorisation(ChangeRing(charpols[i,2],F));
        elif p mod 3 eq 2 then
//            fac_charpol := Factorisation(ChangeRing(Bracket(2,charpols[i,2]),F));
            charpol_in_xsq := P![Coefficient(charpols[i,2],2*j) : j in [0..3]];
            assert Evaluate(charpol_in_xsq,x^2) eq charpols[i,2];
            fac_charpol := [<charpol_in_xsq,1>,<charpol_in_xsq,1>];
            pabove := [p*OF];
        end if;
        if #fac_charpol eq 2 and Degree(fac_charpol[1,1]) eq 3 and Degree(fac_charpol[2,1]) eq 3 then
//            ap := Coefficient(fac_charpol[1,1],2);
//            ap := Z!Norm(ap);
//            disc_charpolp := Discriminant(fac_charpol[1,1]);
            for ell in possible_ells do
                if ell mod 3 eq 1 then
                    ellabove := PrimeIdealsOverPrime(F,ell);
                    OFmodell1, resmodell1 := ResidueClassField(OF,ellabove[1]);
//                    OFmodell2, resmodell2 := ResidueClassField(OF,ellabove[2]);
//                    if ap mod ell ne 0 and not IsSquare(resmodell1(disc_charpolp)) and not IsSquare(resmodell2(disc_charpolp)) then
                    P_ell1<T> := PolynomialRing(OFmodell1);
                    fp1 := P_ell1![resmodell1(Coefficient(fac_charpol[1,1],i)) : i in [0..3]];
                    if ([fac[2] : fac in Factorisation(fp1)] ne [3]) and (not IsIrreducible(fp1)) and (Coefficient(fp1,1) ne 0 or Coefficient(fp1,2) ne 0) then
                        Exclude(~possible_ells,ell);
                    end if;
                elif ell mod 3 eq 2 then
                    ellabove := ell*OF;
                    OFmodell, resmodell := ResidueClassField(OF,ellabove);
//                    if ap mod ell ne 0 and not IsSquare(resmodell(disc_charpolp)) then
                    P_ell<T> := PolynomialRing(OFmodell);
                    fp := P_ell![resmodell(Coefficient(fac_charpol[1,1],i)) : i in [0..3]];
                    if ([fac[2] : fac in Factorisation(fp)] ne [3]) and (not IsIrreducible(fp)) and (Coefficient(fp,1) ne 0 or Coefficient(fp,2) ne 0) then
                        Exclude(~possible_ells,ell);
                    end if;
                end if;
            end for;
            if possible_ells eq [] then
                break;
            end if;
        end if;
    end for;
    return possible_ells;
end intrinsic;


intrinsic C3test2(f :: RngUPolElt, h :: RngUPolElt : radical_cond := 1, primes_bound := 50, charpols := []) -> SeqEnum
{Given two polynomials f and h of degrees 4 and 1 respectively, returns a list of
primes which contains all primes ell at which the mod-ell Galois image associated to the Jacobian of
the curve h(x)y^3 = f(x), is contained in the C3-type maximal subgroup of GL(3,F_ell), i.e., the field-extension
type maximal subgroup. The optional parameters are
1. some integer divisible by all the bad primes of the curve.
2. a bound for how many primes to consider.
3. a precomputed list of tuples consisting of a prime p and the characteristic polynomial of Frobenius at p,
for various primes.}
    Z := Integers();
    P<x> := PolynomialRing(Z);
    F<zeta3> := CyclotomicField(3);
    OF := RingOfIntegers(F);
    C3primes := [];
    if radical_cond eq 1 then radical_cond := RadCond(f,h); end if;
    if charpols eq [] then charpols := getcharpols(f,h : primesend := primes_bound); end if;
    charpols := [x : x in charpols | x[1] gt 3];

    CubicHeckeG := cubic_fields(radical_cond);
    n := #Generators(CubicHeckeG);
    gens_CHG := [CubicHeckeG.i : i in [1..n]];
    RCl, pi := RayClassGroup(Modulus(CubicHeckeG));
    matrix_of_vals := [[gens_CHG[j](pi(RCl.i)) : i in [1..#Generators(RCl)]] : j in [1..#gens_CHG]];
    assert {x^3 : x in &cat(matrix_of_vals)} eq {1};

    function mu3toZmod3(zeta);
        if zeta eq 1 then
            return 0;
        elif zeta eq zeta3 then
            return 1;
        else
            assert zeta eq zeta3^2;
            return 2;
        end if;
    end function;

/*
    factored_charpols := [(x[1] mod 3 eq 1) select <x[1],Factorisation(ChangeRing(x[2],F))> else <x[1],Factorisation(ChangeRing(Bracket(2,x[2]),F))> : x in charpols];
    primes_F := [(x[1] mod 3 eq 1) select PrimeIdealsOverPrime(F,x[1]) else [x[1]*OF] : x in charpols];
    genvals := [[[mu3toZmod3(&*[(v[i] ne 0) select matrix_of_vals[j,i]^(v[i] mod 3) else 1 : i in [1..#v]]) : j in [1..n]] where v is Eltseq(x @@ pi) : x in p] : p in primes_F];
*/
    aps := [];
    mat := Matrix(GF(3),n,1,[0 : i in [1..n]]);
    possible_ells_found := false;
    for i := 1 to #charpols do
        p := charpols[i,1];
        ap := Coefficient(charpols[i,2],5);
        bp := Coefficient(charpols[i,2],4);
        if p mod 3 eq 1 then
            if ap eq 0 then continue; end if;
            fac_charpol := Factorisation(ChangeRing(charpols[i,2],F));
            pabove := PrimeIdealsOverPrime(F,p);
        elif p mod 3 eq 2 then
            if ap^2-2*bp eq 0 then continue; end if;
//            fac_charpol := Factorisation(ChangeRing(Bracket(2,charpols[i,2]),F));
            charpol_in_xsq := P![Coefficient(charpols[i,2],2*j) : j in [0..3]];
            assert Evaluate(charpol_in_xsq,x^2) eq charpols[i,2];
            fac_charpol := [<charpol_in_xsq,1>,<charpol_in_xsq,1>];
            pabove := [p*OF];
        end if;
//        printf "Prime = %o, Lpol Factorisation type = %o\n", p, [<Degree(x[1]),x[2]> : x in fac_charpol];
        if #fac_charpol eq 2 and Degree(fac_charpol[1,1]) eq 3 and Degree(fac_charpol[2,1]) eq 3 then
            ap1 := Coefficient(fac_charpol[1,1],2);
            if ap1 eq 0 then continue; end if;
            if p mod 3 eq 1 then
                Append(~aps,ap);
            elif p mod 3 eq 2 then
                Append(~aps,ap^2-2*bp);
            end if;
            nm_ap1 := Z!Norm(ap1);
            Append(~aps,nm_ap1);
            cols := [[mu3toZmod3(&*[(v[i] mod 3 ne 0) select matrix_of_vals[j,i]^(v[i] mod 3) else 1 : i in [1..#v]]) : j in [1..n]] where v is Eltseq(x @@ pi) : x in pabove];
            for col in cols do
                mat := HorizontalJoin(mat,Matrix(GF(3),n,1,col));
            end for;
            kermat := Kernel(mat);
            dimkermat := Dimension(kermat);
//            printf "Size of the matrix is %ox%o and row kernel has dimension %o\n", NumberOfRows(mat), NumberOfColumns(mat), dimkermat;
            if dimkermat eq 0 then
                lcm_aps := LCM(aps);
                require lcm_aps ne 0 : "C3test fails.";
                possible_ells := Exclude(PrimeFactors(lcm_aps),3);
//                printf "Possible ells after first level in C3test2: %o\n", possible_ells;
//                return possible_ells;
                break;
            end if;
        end if;
    end for;

// weeding out extraneous primes
    for i := 1 to #charpols do
        p := charpols[i,1];
        if p mod 3 eq 1 then
            fac_charpol := Factorisation(ChangeRing(charpols[i,2],F));
        elif p mod 3 eq 2 then
//            fac_charpol := Factorisation(ChangeRing(Bracket(2,charpols[i,2]),F));
            charpol_in_xsq := P![Coefficient(charpols[i,2],2*j) : j in [0..3]];
            assert Evaluate(charpol_in_xsq,x^2) eq charpols[i,2];
            fac_charpol := [<charpol_in_xsq,1>,<charpol_in_xsq,1>];
            pabove := [p*OF];
        end if;
        if #fac_charpol eq 2 and Degree(fac_charpol[1,1]) eq 3 and Degree(fac_charpol[2,1]) eq 3 then
//            ap := Coefficient(fac_charpol[1,1],2);
//            ap := Z!Norm(ap);
//            disc_charpolp := Discriminant(fac_charpol[1,1]);
            for ell in possible_ells do
                if ell mod 3 eq 1 then
                    ellabove := PrimeIdealsOverPrime(F,ell);
                    OFmodell1, resmodell1 := ResidueClassField(OF,ellabove[1]);
//                    OFmodell2, resmodell2 := ResidueClassField(OF,ellabove[2]);
//                    if ap mod ell ne 0 and not IsSquare(resmodell1(disc_charpolp)) and not IsSquare(resmodell2(disc_charpolp)) then
                    P_ell1<T> := PolynomialRing(OFmodell1);
                    fp1 := P_ell1![resmodell1(Coefficient(fac_charpol[1,1],i)) : i in [0..3]];
                    if ([fac[2] : fac in Factorisation(fp1)] ne [3]) and (not IsIrreducible(fp1)) and (Coefficient(fp1,1) ne 0 or Coefficient(fp1,2) ne 0) then
                        Exclude(~possible_ells,ell);
                    end if;
                elif ell mod 3 eq 2 then
                    ellabove := ell*OF;
                    OFmodell, resmodell := ResidueClassField(OF,ellabove);
//                    if ap mod ell ne 0 and not IsSquare(resmodell(disc_charpolp)) then
                    P_ell<T> := PolynomialRing(OFmodell);
                    fp := P_ell![resmodell(Coefficient(fac_charpol[1,1],i)) : i in [0..3]];
                    if ([fac[2] : fac in Factorisation(fp)] ne [3]) and (not IsIrreducible(fp)) and (Coefficient(fp,1) ne 0 or Coefficient(fp,2) ne 0) then
                        Exclude(~possible_ells,ell);
                    end if;
                end if;
            end for;
            if possible_ells eq [] then
                break;
            end if;
        end if;
    end for;
    return possible_ells;
end intrinsic;

////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////


intrinsic C2andC3test(f :: RngUPolElt : radical_cond := 1, primes_bound := 500, charpols := []) -> SeqEnum, SeqEnum
{Given a monic suppressed integral quartic polynomial f = x^4 + a x^2 + b x + c, returns two lists of primes.
1. The first list contains all primes ell at which the mod-ell Galois image associated to the Jacobian of
the curve y^3 = f, is contained in the C3-type maximal subgroup of GL(3,F_ell) or GU(3,F_ell), i.e., the field-extension
type maximal subgroup.
2. The second list contains all primes ell at which the mod-ell Galois image is contained in the C2-type maximal 
subgroup of GL(3,F_ell) or GU(3,F_ell), i.e., the imprimitive type maximal subgroup.
The optional parameters are
1. some integer divisible by all the bad primes of the curve.
2. a bound for how many primes to consider.
3. a precomputed list of tuples consisting of a prime p and the characteristic polynomial of Frobenius at p,
for various primes.}
    Z := Integers();
    F := CyclotomicField(3);
    OF := RingOfIntegers(F);
    if radical_cond eq 1 then radical_cond := RadCond(f); end if;
    if charpols eq [] then charpols := getcharpols(f : primesend := primes_bound); end if;
    try
        C3primes, possiblecubicchars := C3test(f : radical_cond := radical_cond, primes_bound := primes_bound, charpols := charpols);
    catch e;
        C3primes := [];
        require C3primes ne [] : "C3test fails.";
    end try;

    C2primes := C3primes;
    factored_charpols := [<x[1],Factorisation(ChangeRing(x[2],F))> : x in charpols | x[1] mod 3 eq 1];
    primes_F := [PrimeIdealsOverPrime(F,x[1]) : x in factored_charpols];
    quaddirichletchars := quad_fields(radical_cond : all := false);
    possiblequadchars := [];
    for chi in quaddirichletchars do
        bignum := 0;
        boo := true;
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
                    if bignum eq 1 then boo := false; break; end if;
                end if;
            end if;
        end for;
        require bignum ne 0 : "C2test fails.";
        if boo then
            pfacsbignum := PrimeFactors(bignum);
            Append(~possiblequadchars,<pfacsbignum,chi>);
            C2primes := Sort(SetToSequence(Set(C2primes cat pfacsbignum)));
        end if;
    end for;
    n := Nresults();
    if n eq 4 then
        return C3primes, Exclude(C2primes,3), possiblecubicchars, possiblequadchars;
    end if;
    return C3primes, Exclude(C2primes,3);
end intrinsic;


intrinsic C2andC3test2(f :: RngUPolElt : radical_cond := 1, primes_bound := 500, charpols := []) -> SeqEnum, SeqEnum
{Given a monic suppressed integral quartic polynomial f = x^4 + a x^2 + b x + c, returns two lists of primes.
1. The first list contains all primes ell at which the mod-ell Galois image associated to the Jacobian of
the curve y^3 = f, is contained in the C3-type maximal subgroup of GL(3,F_ell) or GU(3,F_ell), i.e., the field-extension
type maximal subgroup.
2. The second list contains all primes ell at which the mod-ell Galois image is contained in the C2-type maximal 
subgroup of GL(3,F_ell) or GU(3,F_ell), i.e., the imprimitive type maximal subgroup.
The optional parameters are
1. some integer divisible by all the bad primes of the curve.
2. a bound for how many primes to consider.
3. a precomputed list of tuples consisting of a prime p and the characteristic polynomial of Frobenius at p,
for various primes.}
    Z := Integers();
    P<x> := PolynomialRing(Z);
    F<zeta3> := CyclotomicField(3);
    OF := RingOfIntegers(F);
    if radical_cond eq 1 then radical_cond := RadCond(f); end if;
    if charpols eq [] then charpols := getcharpols(f : primesend := primes_bound); end if;
    charpols := [x : x in charpols | x[1] gt 3];
    try
        C3primes := C3test2(f : radical_cond := radical_cond, primes_bound := primes_bound, charpols := charpols);
    catch e;
        C3primes := [];
        require C3primes ne [] : "C3test fails.";
    end try;


    QuadHeckeG := quad_fields(radical_cond);
    n := #Generators(QuadHeckeG);
    gens_QHG := [QuadHeckeG.i : i in [1..n]];
    RCl, pi := RayClassGroup(Modulus(QuadHeckeG));
    matrix_of_vals := [[gens_QHG[j](pi(RCl.i)) : i in [1..#Generators(RCl)]] : j in [1..#gens_QHG]];
    assert {x^2 : x in &cat(matrix_of_vals)} eq {1};

    function mu2toZmod2(zeta);
        if zeta eq 1 then
            return 0;
        elif zeta eq -1 then
            return 1;
        end if;
    end function;


    list_of_vals := [];
    mat := Matrix(GF(2),n,1,[0 : i in [1..n]]);
    possible_ells_found := false;
    for i := 1 to #charpols do
        p := charpols[i,1];
        if p mod 3 eq 1 then
            fac_charpol := Factorisation(ChangeRing(charpols[i,2],F));
            pabove := PrimeIdealsOverPrime(F,p);
        elif p mod 3 eq 2 then
//            fac_charpol := Factorisation(ChangeRing(Bracket(2,charpols[i,2]),F));
            charpol_in_xsq := P![Coefficient(charpols[i,2],2*j) : j in [0..3]];
            assert Evaluate(charpol_in_xsq,x^2) eq charpols[i,2];
            fac_charpol := [<charpol_in_xsq,1>,<charpol_in_xsq,1>];
            pabove := [p*OF];
        end if;
//        printf "Prime = %o, Lpol Factorisation type = %o\n", p, [<Degree(x[1]),x[2]> : x in fac_charpol];
        if #fac_charpol eq 2 and Degree(fac_charpol[1,1]) eq 3 and Degree(fac_charpol[2,1]) eq 3 then
            ap := Coefficient(fac_charpol[1,1],2);
            bp := Coefficient(fac_charpol[1,1],1);
            cp := Coefficient(fac_charpol[1,1],0);
            valp := ap*bp-cp;
            if valp eq 0 then continue; end if;
            valp := Z!Norm(valp);
            Append(~list_of_vals,valp);
            cols := [[mu2toZmod2(&*[(v[i] mod 2 ne 0) select matrix_of_vals[j,i]^(v[i] mod 2) else 1 : i in [1..#v]]) : j in [1..n]] where v is Eltseq(x @@ pi) : x in pabove];
            for col in cols do
                mat := HorizontalJoin(mat,Matrix(GF(2),n,1,col));
            end for;
            kermat := Kernel(mat);
            dimkermat := Dimension(kermat);
//            printf "Size of the matrix is %ox%o and row kernel has dimension %o\n", NumberOfRows(mat), NumberOfColumns(mat), dimkermat;
            if dimkermat eq 0 then
                lcm_vals := LCM(list_of_vals);
                require lcm_vals ne 0 : "C2test fails.";
                possible_ells := Exclude(PrimeFactors(lcm_vals),3);
//                printf "Possible ells after first level in C2test2: %o\n", possible_ells;
//                return possible_ells;
                break;
            end if;
        end if;
    end for;

// weeding out extraneous primes
    for i := 1 to #charpols do
        p := charpols[i,1];
        if p mod 3 eq 1 then
            fac_charpol := Factorisation(ChangeRing(charpols[i,2],OF));
        elif p mod 3 eq 2 then
//            fac_charpol := Factorisation(ChangeRing(Bracket(2,charpols[i,2]),OF));
            charpol_in_xsq := P![Coefficient(charpols[i,2],2*j) : j in [0..3]];
            assert Evaluate(charpol_in_xsq,x^2) eq charpols[i,2];
            fac_charpol := [<charpol_in_xsq,1>,<charpol_in_xsq,1>];
            pabove := [p*OF];
        end if;
        if #fac_charpol eq 2 and Degree(fac_charpol[1,1]) eq 3 and Degree(fac_charpol[2,1]) eq 3 then
            ap := Coefficient(fac_charpol[1,1],2);
            bp := Coefficient(fac_charpol[1,1],1);
            cp := Coefficient(fac_charpol[1,1],0);
            valp := ap*bp-cp;
//            valp := Z!Norm(valp);
//            ap := Z!Norm(ap);
            for ell in possible_ells do
                if ell mod 3 eq 1 then
                    ellabove := PrimeIdealsOverPrime(F,ell);
                    OFmodell1, resmodell1 := ResidueClassField(OF,ellabove[1]);
                    OFmodell2, resmodell2 := ResidueClassField(OF,ellabove[2]);
//                    if valp mod ell ne 0 and ap mod ell ne 0 and #Factorisation(Polynomial([resmodell1(c) : c in Coefficients(fac_charpol[1,1])])) ne 3 and #Factorisation(Polynomial([resmodell2(c) : c in Coefficients(fac_charpol[1,1])])) ne 3 then
                    P_ell1<T> := PolynomialRing(OFmodell1);
                    fp1 := P_ell1![resmodell1(Coefficient(fac_charpol[1,1],i)) : i in [0..3]];
                    if (resmodell1(valp) ne 0 and resmodell2(valp) ne 0) and (Coefficient(fp1,1) ne 0 or Coefficient(fp1,2) ne 0) and ({Degree(fac[1]) : fac in Factorisation(fp1)} ne {1}) then
                        Exclude(~possible_ells,ell);
                    end if;
                elif ell mod 3 eq 2 then
                    ellabove := ell*OF;
                    OFmodell, resmodell := ResidueClassField(OF,ellabove);
//                    if valp mod ell ne 0 and ap mod ell ne 0 and #Factorisation(Polynomial([resmodell(c) : c in Coefficients(fac_charpol[1,1])])) ne 3 then
                    P_ell<T> := PolynomialRing(OFmodell);
                    fp := P_ell![resmodell(Coefficient(fac_charpol[1,1],i)) : i in [0..3]];
                    if (resmodell(valp) ne 0) and (Coefficient(fp,1) ne 0 or Coefficient(fp,2) ne 0) and ({Degree(fac[1]) : fac in Factorisation(fp)} ne {1}) then
                        Exclude(~possible_ells,ell);
                    end if;
                end if;
            end for;
            if possible_ells eq [] then
                return C3primes, C3primes;
            end if;
        end if;
    end for;
    return C3primes, Sort(SetToSequence(Set(C3primes cat possible_ells)));
end intrinsic;

intrinsic C2andC3test2(f :: RngUPolElt, h :: RngUPolElt : radical_cond := 1, primes_bound := 50, charpols := []) -> SeqEnum, SeqEnum
{Given two polynomials f and h of degrees 4 and 1 respectively, returns two lists of primes.
1. The first list contains all primes ell at which the mod-ell Galois image associated to the Jacobian of
the curve h(x)y^3 = f(x), is contained in the C3-type maximal subgroup of GL(3,F_ell) or GU(3,F_ell), i.e., the field-extension
type maximal subgroup.
2. The second list contains all primes ell at which the mod-ell Galois image is contained in the C2-type maximal 
subgroup of GL(3,F_ell) or GU(3,F_ell), i.e., the imprimitive type maximal subgroup.
The optional parameters are
1. some integer divisible by all the bad primes of the curve.
2. a bound for how many primes to consider.
3. a precomputed list of tuples consisting of a prime p and the characteristic polynomial of Frobenius at p,
for various primes.}
    Z := Integers();
    P<x> := PolynomialRing(Z);
    F<zeta3> := CyclotomicField(3);
    OF := RingOfIntegers(F);
    if radical_cond eq 1 then radical_cond := RadCond(f,h); end if;
    if charpols eq [] then charpols := getcharpols(f,h : primesend := primes_bound); end if;
    charpols := [x : x in charpols | x[1] gt 3];
    try
        C3primes := C3test2(f,h : radical_cond := radical_cond, primes_bound := primes_bound, charpols := charpols);
    catch e;
        C3primes := [];
        require C3primes ne [] : "C3test fails.";
    end try;


    QuadHeckeG := quad_fields(radical_cond);
    n := #Generators(QuadHeckeG);
    gens_QHG := [QuadHeckeG.i : i in [1..n]];
    RCl, pi := RayClassGroup(Modulus(QuadHeckeG));
    matrix_of_vals := [[gens_QHG[j](pi(RCl.i)) : i in [1..#Generators(RCl)]] : j in [1..#gens_QHG]];
    assert {x^2 : x in &cat(matrix_of_vals)} eq {1};

    function mu2toZmod2(zeta);
        if zeta eq 1 then
            return 0;
        elif zeta eq -1 then
            return 1;
        end if;
    end function;


    list_of_vals := [];
    mat := Matrix(GF(2),n,1,[0 : i in [1..n]]);
    possible_ells_found := false;
    for i := 1 to #charpols do
        p := charpols[i,1];
        if p mod 3 eq 1 then
            fac_charpol := Factorisation(ChangeRing(charpols[i,2],F));
            pabove := PrimeIdealsOverPrime(F,p);
        elif p mod 3 eq 2 then
//            fac_charpol := Factorisation(ChangeRing(Bracket(2,charpols[i,2]),F));
            charpol_in_xsq := P![Coefficient(charpols[i,2],2*j) : j in [0..3]];
            assert Evaluate(charpol_in_xsq,x^2) eq charpols[i,2];
            fac_charpol := [<charpol_in_xsq,1>,<charpol_in_xsq,1>];
            pabove := [p*OF];
        end if;
//        printf "Prime = %o, Lpol Factorisation type = %o\n", p, [<Degree(x[1]),x[2]> : x in fac_charpol];
        if #fac_charpol eq 2 and Degree(fac_charpol[1,1]) eq 3 and Degree(fac_charpol[2,1]) eq 3 then
            ap := Coefficient(fac_charpol[1,1],2);
            bp := Coefficient(fac_charpol[1,1],1);
            cp := Coefficient(fac_charpol[1,1],0);
            valp := ap*bp-cp;
            if valp eq 0 then continue; end if;
            valp := Z!Norm(valp);
            Append(~list_of_vals,valp);
            cols := [[mu2toZmod2(&*[(v[i] mod 2 ne 0) select matrix_of_vals[j,i]^(v[i] mod 2) else 1 : i in [1..#v]]) : j in [1..n]] where v is Eltseq(x @@ pi) : x in pabove];
            for col in cols do
                mat := HorizontalJoin(mat,Matrix(GF(2),n,1,col));
            end for;
            kermat := Kernel(mat);
            dimkermat := Dimension(kermat);
//            printf "Size of the matrix is %ox%o and row kernel has dimension %o\n", NumberOfRows(mat), NumberOfColumns(mat), dimkermat;
            if dimkermat eq 0 then
                lcm_vals := LCM(list_of_vals);
                require lcm_vals ne 0 : "C2test fails.";
                possible_ells := Exclude(PrimeFactors(lcm_vals),3);
//                printf "Possible ells after first level in C2test2: %o\n", possible_ells;
//                return possible_ells;
                break;
            end if;
        end if;
    end for;

// weeding out extraneous primes
    for i := 1 to #charpols do
        p := charpols[i,1];
        if p mod 3 eq 1 then
            fac_charpol := Factorisation(ChangeRing(charpols[i,2],OF));
        elif p mod 3 eq 2 then
//            fac_charpol := Factorisation(ChangeRing(Bracket(2,charpols[i,2]),OF));
            charpol_in_xsq := P![Coefficient(charpols[i,2],2*j) : j in [0..3]];
            assert Evaluate(charpol_in_xsq,x^2) eq charpols[i,2];
            fac_charpol := [<charpol_in_xsq,1>,<charpol_in_xsq,1>];
            pabove := [p*OF];
        end if;
        if #fac_charpol eq 2 and Degree(fac_charpol[1,1]) eq 3 and Degree(fac_charpol[2,1]) eq 3 then
            ap := Coefficient(fac_charpol[1,1],2);
            bp := Coefficient(fac_charpol[1,1],1);
            cp := Coefficient(fac_charpol[1,1],0);
            valp := ap*bp-cp;
//            valp := Z!Norm(valp);
//            ap := Z!Norm(ap);
            for ell in possible_ells do
                if ell mod 3 eq 1 then
                    ellabove := PrimeIdealsOverPrime(F,ell);
                    OFmodell1, resmodell1 := ResidueClassField(OF,ellabove[1]);
                    OFmodell2, resmodell2 := ResidueClassField(OF,ellabove[2]);
//                    if valp mod ell ne 0 and ap mod ell ne 0 and #Factorisation(Polynomial([resmodell1(c) : c in Coefficients(fac_charpol[1,1])])) ne 3 and #Factorisation(Polynomial([resmodell2(c) : c in Coefficients(fac_charpol[1,1])])) ne 3 then
                    P_ell1<T> := PolynomialRing(OFmodell1);
                    fp1 := P_ell1![resmodell1(Coefficient(fac_charpol[1,1],i)) : i in [0..3]];
                    if (resmodell1(valp) ne 0 and resmodell2(valp) ne 0) and (Coefficient(fp1,1) ne 0 or Coefficient(fp1,2) ne 0) and ({Degree(fac[1]) : fac in Factorisation(fp1)} ne {1}) then
                        Exclude(~possible_ells,ell);
                    end if;
                elif ell mod 3 eq 2 then
                    ellabove := ell*OF;
                    OFmodell, resmodell := ResidueClassField(OF,ellabove);
//                    if valp mod ell ne 0 and ap mod ell ne 0 and #Factorisation(Polynomial([resmodell(c) : c in Coefficients(fac_charpol[1,1])])) ne 3 then
                    P_ell<T> := PolynomialRing(OFmodell);
                    fp := P_ell![resmodell(Coefficient(fac_charpol[1,1],i)) : i in [0..3]];
                    if (resmodell(valp) ne 0) and (Coefficient(fp,1) ne 0 or Coefficient(fp,2) ne 0) and ({Degree(fac[1]) : fac in Factorisation(fp)} ne {1}) then
                        Exclude(~possible_ells,ell);
                    end if;
                end if;
            end for;
            if possible_ells eq [] then
                return C3primes, C3primes;
            end if;
        end if;
    end for;
    return C3primes, Sort(SetToSequence(Set(C3primes cat possible_ells)));
end intrinsic;
