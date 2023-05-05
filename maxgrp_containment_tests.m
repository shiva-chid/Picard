load "Lpolys.m";
load "quad_cubic_fields.m";
load "update_CMforms.m";

function getLpol(f,radical_cond,p);
    P<x> := Parent(f);
    if BaseRing(P) ne Integers() then
        P<x> := PolynomialRing(Integers());
        f := P ! f;
    end if;
    if radical_cond mod p eq 0 then
        return "Bad Prime";
    end if;
/*
    require radical_cond mod p ne 0 : "Bad Prime";
*/
    pstr := IntegerToString(p);
    fcoeffs := [IntegerToString(c) : c in Coefficients(f)];
    fstr := "x^4+" cat fcoeffs[3] cat "x^2+" cat fcoeffs[2] cat "x+" cat fcoeffs[1];
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


// Given the defining f, we compute the divisors of the associated "Billerey Bounds" for all primes 1 mod 3 of good reduction in the interval (53,N).
function C1test(f : radical_cond := 1, primes_bound := 500);
    Z := Integers();
    F := CyclotomicField(3);
    O := RingOfIntegers(F);
    if radical_cond eq 1 then
        radical_cond := RadCond(f);
    end if;
    As := [];
    for p in PrimesInInterval(53, primes_bound) do
        if (p mod 3 ne 1) or (radical_cond mod p eq 0) then continue; end if;
        Fac := Factorisation(p*O);
        for pfac in Fac do
            tf, a := IsPrincipal(pfac[1]);
            Append(~As,a);
        end for;
    end for;
    Bs := [];
    for a in As do
        B := Bound(f,radical_cond,a);
        if Type(B) eq MonStgElt then continue; end if;
        Append(~Bs,Z!Norm(a)*B); // The bound associated to B_p doesn't give us any information on p.
    end for;
/*
    return Sort(Setseq(Seqset(PrimeFactors(Norm(GCD(Bs))) cat PrimeFactors(radical_cond)))); //to catch any primes which may not have semistable reduction. In particular, note that 3 is included here.
*/
    return PrimeFactors(Norm(GCD(Bs)));
end function;


////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////


function C3test(f : radical_cond := 1, primes_bound := 500);
    Z := Integers();
    F := CyclotomicField(3);
    possibly_nonsurj_primes := [];
    if radical_cond eq 1 then
        radical_cond := RadCond(f);
    end if;
    cubicdirichletchars := cubic_fields(radical_cond);
    for chi in cubicdirichletchars do
        bignum := 0;
        for p in PrimesUpTo(primes_bound) do
            if radical_cond mod p eq 0 then continue; end if;
            if p ne 2 and p mod 3 eq 2 then
                if chi(p) ne 1 then
                    Lpol := getLpol(f,radical_cond,p);
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
                    Lpol := getLpol(f,radical_cond,p);
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
    return Exclude(possibly_nonsurj_primes,3);
end function;


////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////


function C2test(f : radical_cond := 1, primes_bound := 500);
    Z := Integers();
    F := CyclotomicField(3);
    if radical_cond eq 1 then
        radical_cond := RadCond(f);
    end if;
    possibly_nonsurj_primes := C3test(f : radical_cond := radical_cond, primes_bound := primes_bound);
    if Type(possibly_nonsurj_primes) eq RngIntElt then
        possibly_nonsurj_primes := [];
    end if;
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
        possibly_nonsurj_primes := Sort(SetToSequence(Set(possibly_nonsurj_primes cat PrimeFactors(bignum))));
    end for;
    return Exclude(possibly_nonsurj_primes,3);
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


