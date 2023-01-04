load "Lpolys.m";
load "quad_cubic_fields.m";
load "update_CMforms.m";

function getLpol(f,cond,p);
    P<x> := Parent(f);
    if cond mod p eq 0 then
        return "Bad Prime";
    end if;
/*
    require cond mod p ne 0 : "Bad Prime";
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


// This is C1test using the Hecke Polynomials computed (and stored) from Grossencharacters
function C1test(f,cond : primes_bound := 500);
    Z := Integers();
    P<t> := PolynomialRing(Rationals());
    cmformsheckepols_alllevels := update_CMforms(cond : primes_bound := primes_bound);

    bignum := 0;
    for p in PrimesUpTo(primes_bound) do
        if p ge 53 and p mod 3 eq 1 and cond mod p ne 0 then
            Lpol := getLpol(f,cond,p);
            if Type(Lpol) eq MonStgElt then
                continue p;
            end if;
            prod_heckepols := &*[P!x[3] : x in cmformsheckepols_alllevels | x[2] eq p];
            bignum := GCD(bignum,Z!Resultant(Lpol,prod_heckepols));
        end if;
    end for;

    if bignum eq 0 then
        printf "The resultant of charpol(rho_ell(Frob_p)) and the Hecke polynomials of CM cusp forms is 0 for all split primes up to %o.\n", primes_bound;
        return 0;
    end if;
/*
    require bignum ne 0 : "The resultant of charpol(rho_ell(Frob_p)) and the Hecke polynomials of CM cusp forms is 0 for all split primes up to %o.\n", primes_bound;
*/
    return PrimeFactors(bignum);
end function;


////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////


function C3test(f,cond : primes_bound := 500);
    Z := Integers();
    F := CyclotomicField(3);
    possibly_nonsurj_primes := [];
    cubicdirichletchars := cubic_fields(cond);
    for chi in cubicdirichletchars do
        bignum := 0;
        for p in PrimesUpTo(primes_bound) do
            if cond mod p eq 0 then continue; end if;
            if p ne 2 and p mod 3 eq 2 then
                if chi(p) ne 1 then
                    Lpol := getLpol(f,cond,p);
                    if Type(Lpol) ne MonStgElt then
//                        printf "Using an inert prime in C3test. ";
                        newnum := Coefficient(Lpol,5);
//                        if newnum ne 0 then printf "It has worked.\n"; end if;
                        bignum := GCD(bignum,newnum);
                    end if;
                end if;
            elif p mod 3 eq 1 then
                pfacs := PrimeIdealsOverPrime(F,p);
                if chi(pfacs[1]) ne 1 and chi(pfacs[2]) ne 1 then
                    Lpol := getLpol(f,cond,p);
                    if Type(Lpol) ne MonStgElt then
                        facs := Factorisation(ChangeRing(Lpol,F));
                        if #facs eq 2 and Degree(facs[1,1]) eq 3 and Degree(facs[2,1]) eq 3 and facs[1,2] eq 1 and facs[2,2] eq 1 then
//                            printf "Using a split prime in C3test. ";
                            fac1 := facs[1,1];
                            fac2 := facs[2,1];
                            newnum := Z ! (Coefficient(fac1,2)*Coefficient(fac2,2));
//                            if newnum ne 0 then printf "It has worked.\n"; end if;
                            bignum := GCD(bignum,newnum);
                        end if;
                    end if;
                end if;
            end if;
        end for;
        if bignum eq 0 then
            printf "C3test fails.\n";
            return 0;
        end if;
        possibly_nonsurj_primes := Sort(SetToSequence(Set(possibly_nonsurj_primes cat PrimeFactors(bignum))));
    end for;
    return possibly_nonsurj_primes;
end function;


////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////


function C2test(f,cond : primes_bound := 500);
    Z := Integers();
    F := CyclotomicField(3);
    possibly_nonsurj_primes := C3test(f,cond);
    if Type(possibly_nonsurj_primes) eq RngIntElt then
        possibly_nonsurj_primes := [];
    end if;
    quaddirichletchars := quad_fields(cond);
    for chi in quaddirichletchars do
        bignum := 0;
        for p in PrimesUpTo(primes_bound) do
            if cond mod p eq 0 then continue; end if;
            if p mod 3 eq 1 then
                pfacs := PrimeIdealsOverPrime(F,p);
                if chi(pfacs[1]) ne 1 and chi(pfacs[2]) ne 1 then
                    Lpol := getLpol(f,cond,p);
                    if Type(Lpol) ne MonStgElt then
                        facs := Factorisation(ChangeRing(Lpol,F));
                        if #facs eq 2 and Degree(facs[1,1]) eq 3 and Degree(facs[2,1]) eq 3 and facs[1,2] eq 1 and facs[2,2] eq 1 then
                            printf "Using a split prime in C2test. ";
                            fac1 := facs[1,1];
                            fac2 := facs[2,1];
                            newnum := Z ! ((Coefficient(fac1,2)*Coefficient(fac1,1)-Coefficient(fac1,0))*(Coefficient(fac2,2)*Coefficient(fac2,1)-Coefficient(fac2,0)));
                            if newnum ne 0 then printf "It has worked.\n"; end if;
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
        possibly_nonsurj_primes := Sort(SetToSequence(Set(possibly_nonsurj_primes cat PrimeFactors(bignum))));
    end for;
    return possibly_nonsurj_primes;
end function;


////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////
/*
load "PicardConductor.m";

P<x> := PolynomialRing(Integers());

f := x^4-x^2-x+1;
cond := PicardConductor(f);
print cond, Factorisation(cond);
C1test(f,cond);
C3test(f,cond);
C2test(f,cond);

f := x^4 - 4*x^3 + 2*x^2 + x + 13;
cond := PicardConductor(f);
print cond, Factorisation(cond);
C1test(f,cond);
C3test(f,cond);
C2test(f,cond);
*/

////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////


