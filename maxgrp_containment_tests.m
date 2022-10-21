load "Lpolys.m";
load "quad_cubic_fields.m";

function getLpol(f,p);
    P<x> := Parent(f);
    disc := Discriminant(f);
    disc := Numerator(disc)*Denominator(disc);
    if disc mod p eq 0 then
        return "Bad Prime";
    end if;
/*
    require disc mod p ne 0 : "Bad Prime";
*/
    pstr := IntegerToString(p);
    fcoeffs := [IntegerToString(c) : c in Coefficients(f)];
    fstr := "x^4+" cat fcoeffs[3] cat "x^2+" cat fcoeffs[2] cat "x+" cat fcoeffs[1];
    System("hwlpoly y^3=" cat fstr cat " " cat pstr cat " 1 > CartManmat_for_p.txt");
    fil := Open("CartManmat_for_p.txt", "r");
    C := Coefficients(f)[1..3];
    Lpol := liftLpolys(fil,C);
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


function C1test(f,cond);
    E := EllipticCurve([0,1]);
    good_ps := [];
    k := 1;
    while #good_ps lt 5 do
        p := 1+k*3*cond;
        if IsPrime(p) then
            a_p := TraceOfFrobenius(E,p);
            if a_p mod cond eq 2 then
/*
The checks p = 1 mod N and a_p = 2 mod N imply that Frob_p on E[N] is unipotent.
The further condition p = 1 mod 3 is enought to guarantee that Frob_p on E[N] is the identity.
*/
                Append(~good_ps,p);
            end if;
        end if;
        k := k+1;
    end while;

    charpols_frobp := [getLpol(f,p) : p in good_ps];
    print good_ps, charpols_frobp;
    assert &and[good_ps[i]^3 eq Coefficient(charpols_frobp[i],0) : i in [1..#charpols_frobp]];
/*
    require &and[good_ps[i]^3 eq Coefficient(charpols_frobp[i],0) : i in [1..#charpols_frobp]] : "Something went wrong in computation of L-polynomial";
*/
    bignum := GCD([Evaluate(charpol,1) : charpol in charpols_frobp]);
    if bignum eq 0 then
        return "The charpol(rho_ell(Frob_p)) evaluated at 1 equals 0, for the five chosen primes p.";
    end if;
/*
    require bignum ne 0 : "The charpol(rho_ell(Frob_p)) evaluated at 1 equals 0, for the five chosen primes p.";
*/
    return [ell : ell in PrimeFactors(bignum) | ell mod 3 eq 1];
end function;

function C1test_v2(f,cond : primes_bound := 100);
    F := CyclotomicField(3);
    OF := RingOfIntegers(F);
/*
    RCl := RayClassGroup(cond*OF);
    e := Exponent(RCl);
*/
/*
    RCl_fact := quo<OF|cond*OF>;
    e := Exponent(UnitGroup(RCl_fact));
*/

    Facs := Factorisation(cond);
    e := 1;
    for fac in Facs do
        p := fac[1];
        m := fac[2];
        if p mod 3 eq 1 then
            e := LCM(e,p^(m-1)*(p-1));
        elif p mod 3 eq 2 then
            e := LCM(e,p^(2*m-2)*(p^2-1));
        else
            e := LCM(e,p^(2*m-1)*(p-1));
        end if;
    end for;

    P<x> := Parent(f);
    disc := Discriminant(f);
    disc := Numerator(disc)*Denominator(disc);
    bignum := 0;
    for p in PrimesUpTo(primes_bound) do
        if p ge 53 and p mod 3 eq 1 and disc mod p ne 0 then
            Lpol := getLpol(f,p);
            bignum := GCD(bignum,Resultant(Lpol,x^e-1));
        end if;
    end for;

    if bignum eq 0 then
        return "The resultant of charpol(rho_ell(Frob_p)) and the equation x^e-1 is 0 for all primes up to the given bound (default 100).";
    end if;
/*
    require bignum ne 0 : "The resultant of charpol(rho_ell(Frob_p)) and the equation x^e-1 is 0 for all primes up to the given bound (default 100).";
*/
    return [ell : ell in PrimeFactors(bignum) | ell mod 3 eq 1];
end function;


////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////


function C3test(f,cond : primes_bound := 100);
    possibly_nonsurj_primes := [];
    ramprimes := PrimeFactors(cond);
    cubicdirichletchars := cubic_fields(ramprimes);
    for chi in cubicdirichletchars do
        bignum := 0;
        for p in PrimesUpTo(primes_bound) do
            if p ne 2 and chi(p) ne 1 then
                Lpol := getLpol(f,p);
                if Type(Lpol) ne MonStgElt then
                    bignum := GCD(bignum,Coefficient(Lpol,5));
                end if;
            end if;
        end for;
        possibly_nonsurj_primes := Sort(SetToSequence(Set(possibly_nonsurj_primes cat PrimeFactors(bignum))));
    end for;
    return [p : p in possibly_nonsurj_primes | p mod 3 eq 1];
end function;


////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////


function C2test(f,cond : primes_bound := 100);
    possibly_nonsurj_primes := C3test(f,cond) cat [3]; // TODO: why include 3 here, when we are anyway only looking for non-surjective primes that are 1 mod 3?
    ramprimes := PrimeFactors(cond);
    quadfields := quad_fields(ramprimes);
    for d in quadfields do
        bignum := 0;
        for p in PrimesUpTo(primes_bound) do
            if p ne 2 and LegendreSymbol(d,p) eq -1 then
                Lpol := getLpol(f,p);
                if Type(Lpol) ne MonStgElt then
                    facs := Factorisation(Lpol);
                    if #facs eq 2 and facs[1,2] eq 1 and facs[2,2] eq 1 then
                        fac1 := facs[1,1];
                        fac2 := facs[2,1];
                        newnum := (Coefficient(fac1,2)*Coefficient(fac1,1)-Coefficient(fac1,0))*(Coefficient(fac2,2)*Coefficient(fac2,1)-Coefficient(fac2,0));
                        bignum := GCD(bignum,newnum);
                    end if;
                end if;
            end if;
        end for;
        possibly_nonsurj_primes := Sort(SetToSequence(Set(possibly_nonsurj_primes cat PrimeFactors(bignum))));
    end for;
    return [p : p in possibly_nonsurj_primes | p mod 3 eq 1];
end function;


P<x> := PolynomialRing(Integers());
AttachSpec("magma/spec");

f := x^4+x^2+1;
discf := Discriminant(f);
f_Q := ChangeRing(f,Rationals());
cond_multiple := AbsoluteValue(QuarticDiscriminant(LongWeierstrassEquation(f_Q)));
// cond_multiple := AbsoluteValue(QuarticDiscriminant(ShortWeierstrassEquation(f_Q)));
// cond_multiple := AbsoluteValue(QuarticDiscriminant(PicardForm(ReducedWeierstrassEquation(f_Q))));
print cond_multiple, discf;
print cond_multiple mod discf eq 0;

C1test(f,cond_multiple);
// C1test_v2(f,cond_multiple);
C3test(f,cond_multiple);
C2test(f,cond_multiple);

f := x^4 - 4*x^3 + 2*x^2 + x + 13;
discf := Discriminant(f);
f_Q := ChangeRing(f,Rationals());
cond_multiple := AbsoluteValue(QuarticDiscriminant(LongWeierstrassEquation(f_Q)));
// cond_multiple := AbsoluteValue(QuarticDiscriminant(ShortWeierstrassEquation(f_Q)));
// cond_multiple := AbsoluteValue(QuarticDiscriminant(PicardForm(ReducedWeierstrassEquation(f_Q))));
print cond_multiple, discf;
print cond_multiple mod discf eq 0;

C1test(f,cond_multiple);
// C1test_v2(f,cond_multiple);
C3test(f,cond_multiple);
C2test(f,cond_multiple);


////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////


