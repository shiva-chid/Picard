load "Lpolys.m";
load "quad_cubic_fields.m";
load "update_CMforms.m";

function suppressed_integer_quartic(f);
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
end function;

function getLpol(f,radical_cond,p);
    f := suppressed_integer_quartic(f);
    P<x> := Parent(f);
/*
    if BaseRing(P) ne Integers() then
        P<x> := PolynomialRing(Integers());
        f := P ! f;
    end if;
*/
    if radical_cond mod p eq 0 then
        return "Bad Prime";
    end if;
/*
    require radical_cond mod p ne 0 : "Bad Prime";
*/
    pstr := IntegerToString(p);
    fstr := Sprint(f);
    fstr := &cat(Split(fstr," "));
/*
    System("hwlpoly y^3=" cat fstr cat " " cat pstr cat " 1 > CartManmat_for_p.txt");
    fil := Open("CartManmat_for_p.txt", "r");
    C := Coefficients(f)[1..3];
    Lpol := liftLpolys(fil,C);
*/
    C := Coefficients(f)[1..3];
    cartmanmat := Pipe("hwlpoly y^3=" cat fstr cat " " cat pstr cat " 1","");
    Lpol := liftLpoly(cartmanmat,C);

/*
    print Lpol;
*/
    if #Lpol ne 1 then
        return "Error in computing L-polynomial";
    end if;
/*
    require #Lpol eq 1 : "Error in computing L-polynomial";
*/
    return P ! Reverse(Lpol[1,2]);
end function;


////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////


function Star(f,g);
    P<x> := Parent(f); 
    P2<z> := PolynomialRing(P);
    g_xz := &+[Coefficient(g,i)*z^(Degree(g)-i)*x^i : i in [0..Degree(g)]];
    return Resultant(P2!Coefficients(f), g_xz);
end function;

function Bracket(r,f);
    P<x> := Parent(f);
    frXr := Star(f, x^r-1);
    return &+[Coefficient(frXr,r*i)*x^i : i in [0..Degree(f)]];
end function;

function RadCond(f);
    radical_disc := &*([1] cat [p : p in PrimeFactors(Discriminant(f))]);
    radical_leadcoeff := &*([1] cat [p : p in PrimeFactors(Coefficient(f,4))]);
    radical_cond := radical_leadcoeff*radical_disc;
    if radical_cond mod 3 ne 0 then
        radical_cond := 3*radical_cond;
    end if;
    return radical_cond;
end function;

//Input: f is the defining polynomial, i.e., y^3=f and "a" should generate a prime ideal of Z[zeta_3] above a rational prime congruent to 1 mod 3.
//Output: This outputs the "Billerey Bound",i.e., the analogue to the B_p bound given in Billerey's paper.
function Bound(f,radical_cond,a);
    p :=Integers()!Norm(a);
    assert p mod 3 eq 1 and radical_cond mod p ne 0 and p ge 53;
    Lpol := getLpol(f,radical_cond,p);
    if Type(Lpol) eq MonStgElt then return Lpol; end if;
    Testpol := Bracket(72,Lpol);
    return &*[Evaluate(Testpol,r^72): r in {1,a,p,a*p,p^2,a^2}];
end function;


////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////


// Given the defining f, we compute the divisors of the associated "Billerey Bounds" for all primes
// 1 mod 3 of good reduction in the interval (53,N).
function C1test(f : radical_cond := 1, primes_bound := 1000);
    Z := Integers();
    F := CyclotomicField(3);
    OF := RingOfIntegers(F);
    if radical_cond eq 1 then
        radical_cond := RadCond(f);
    end if;
    As := [];
    for p in PrimesInInterval(53, primes_bound) do
        if (p mod 3 ne 1) or (radical_cond mod p eq 0) then continue; end if;
        Fac := Factorisation(p*OF);
        for pfac in Fac do
            tf, a := IsPrincipal(pfac[1]);
            Append(~As,a);
        end for;
    end for;
    Bignum := 0;
    for a in As do
        B := Bound(f,radical_cond,a);
        if Type(B) eq MonStgElt then continue; end if;
        Bignum := GCD(Bignum,Norm(a*B)); // The bound associated to B_p doesn't give us any information on p.
        if Bignum eq 2^Valuation(Bignum,2)*3^Valuation(Bignum,3) then
            return PrimeFactors(Bignum);
        end if;
    end for;
    if Bignum eq 0 then
        printf "C1test fails.\n";
        return 0;
    end if;
    return PrimeFactors(Bignum);
end function;




// This is C1test using the Hecke Polynomials computed (and stored) from Grossencharacters
function C1test_CMforms(f,radical_cond : cond := 1, primes_bound := 500, fromCMformsdb := false);
    Z := Integers();
    P<t> := PolynomialRing(Rationals());
    if cond eq 1 then
        cmformsheckepols_alllevels := update_CMforms1(radical_cond : primes_bound := primes_bound, fromCMformsdb := fromCMformsdb);
    else
        cmformsheckepols_alllevels := update_CMforms(cond : primes_bound := primes_bound, fromCMformsdb := fromCMformsdb);
    end if;

    bignum := 0;
    for p in PrimesUpTo(primes_bound) do
        if p ge 53 and p mod 3 eq 1 and radical_cond mod p ne 0 then
            Lpol := getLpol(f,radical_cond,p);
            if Type(Lpol) eq MonStgElt then
                continue p;
            end if;
            prod_heckepols := &*[P!x[3] : x in cmformsheckepols_alllevels | x[2] eq p];
            bignum := GCD(bignum,Z!Resultant(Lpol,prod_heckepols));
//            printf "The latest number bignum, after computing resultants upto primes %o, is %o.\n", p, bignum;
            if bignum ne 0 and bignum eq 3^(Valuation(bignum,3)) then
                return [];
            end if;
        end if;
    end for;

    if bignum eq 0 then
        printf "The resultant of charpol(rho_ell(Frob_p)) and the Hecke polynomials of CM cusp forms is 0 for all split primes up to %o.\n", primes_bound;
        return 0;
    end if;
/*
    require bignum ne 0 : "The resultant of charpol(rho_ell(Frob_p)) and the Hecke polynomials of CM cusp forms is 0 for all split primes up to %o.\n", primes_bound;
*/
    return Exclude(PrimeFactors(bignum),3);
end function;


////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////


function C3test(f : radical_cond := 1, primes_bound := 1000);
    Z := Integers();
    F := CyclotomicField(3);
    possibly_nonsurj_primes := [];
    if radical_cond eq 1 then
        radical_cond := RadCond(f);
    end if;
    cubicdirichletchars := cubic_fields(radical_cond);
//    print cubicdirichletchars;
    for chi in cubicdirichletchars do
        bignum := 0;
        for p in PrimesUpTo(primes_bound) do
            if radical_cond mod p eq 0 then continue; end if;
            if p ne 2 and p mod 3 eq 2 then
                if chi(p) ne 1 then
                    Lpol := getLpol(f,radical_cond,p);
                    if Type(Lpol) ne MonStgElt then
//                        printf "Using an inert prime in C3test.\n";
                        newnum := Coefficient(Lpol,5);
//                        if newnum ne 0 then printf "Inert prime works.\n"; end if;
                        bignum := GCD(bignum,newnum);
                    end if;
                end if;
            elif p mod 3 eq 1 then
                pfacs := PrimeIdealsOverPrime(F,p);
                if chi(pfacs[1]) ne 1 and chi(pfacs[2]) ne 1 then
                    Lpol := getLpol(f,radical_cond,p);
                    if Type(Lpol) ne MonStgElt then
                        facs := Factorisation(ChangeRing(Lpol,F));
                        if #facs eq 2 and Degree(facs[1,1]) eq 3 and Degree(facs[2,1]) eq 3 and facs[1,2] eq 1 and facs[2,2] eq 1 then
//                            printf "Using a split prime in C3test.\n";
                            fac1 := facs[1,1];
                            fac2 := facs[2,1];
                            newnum := Z ! (Coefficient(fac1,2)*Coefficient(fac2,2));
//                            if newnum ne 0 then printf "Split prime works.\n"; end if;
                            bignum := GCD(bignum,newnum);
                        end if;
                    end if;
                end if;
            end if;
        end for;
        if bignum eq 0 then
            printf "C3test fails.\n";
            return 0;
//            return chi;
        end if;
        possibly_nonsurj_primes := Sort(SetToSequence(Set(possibly_nonsurj_primes cat PrimeFactors(bignum))));
    end for;
    return Exclude(possibly_nonsurj_primes,3);
end function;


////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////


function C2andC3test(f : radical_cond := 1, primes_bound := 1000);
    Z := Integers();
    F := CyclotomicField(3);
    if radical_cond eq 1 then
        radical_cond := RadCond(f);
    end if;
    C3primes := C3test(f : radical_cond := radical_cond, primes_bound := primes_bound);
    if Type(C3primes) eq RngIntElt then
        C3primes := [];
    end if;
    C2primes := C3primes;
    quaddirichletchars := quad_fields(radical_cond);
    for chi in quaddirichletchars do
        bignum := 0;
        for p in PrimesUpTo(primes_bound) do
            if radical_cond mod p eq 0 then continue; end if;
            if p mod 3 eq 1 then
                pfacs := PrimeIdealsOverPrime(F,p);
                if chi(pfacs[1]) ne 1 and chi(pfacs[2]) ne 1 then
                    Lpol := getLpol(f,radical_cond,p);
                    if Type(Lpol) ne MonStgElt then
                        facs := Factorisation(ChangeRing(Lpol,F));
                        if #facs eq 2 and Degree(facs[1,1]) eq 3 and Degree(facs[2,1]) eq 3 and facs[1,2] eq 1 and facs[2,2] eq 1 then
//                            printf "Using a split prime in C2test. ";
                            fac1 := facs[1,1];
                            fac2 := facs[2,1];
                            newnum := Z ! ((Coefficient(fac1,2)*Coefficient(fac1,1)-Coefficient(fac1,0))*(Coefficient(fac2,2)*Coefficient(fac2,1)-Coefficient(fac2,0)));
//                            if newnum ne 0 then printf "It has worked.\n"; end if;
                            bignum := GCD(bignum,newnum);
                        end if;
                    end if;
                end if;
            end if;
        end for;
        if bignum eq 0 then
            printf "C2test fails.\n";
            return 0;
        end if;
        C2primes := Sort(SetToSequence(Set(C2primes cat PrimeFactors(bignum))));
    end for;
    return C3primes, Exclude(C2primes,3);
end function;


////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////
/*
P<x> := PolynomialRing(Integers());

f := x^4-x^2-x+1;
C1test(f);
C3test(f);
C2test(f);

f := x^4 - 4*x^3 + 2*x^2 + x + 13;
C1test(f);
C3test(f);
C2test(f);
*/

////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////


