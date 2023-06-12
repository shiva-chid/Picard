load "Lpolys.m";



function RadCond(f);
    radical_disc := &*([1] cat [p : p in PrimeFactors(Discriminant(f))]);
    radical_leadcoeff := &*([1] cat [p : p in PrimeFactors(Coefficient(f,4))]);
    radical_cond := radical_leadcoeff*radical_disc;
    if radical_cond mod 3 ne 0 then
        radical_cond := 3*radical_cond;
    end if;
    return radical_cond;
end function;

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



function cubic_fields(radical_cond);
    F := CyclotomicField(3);
    OF := RingOfIntegers(F);
    G := HeckeCharacterGroup(3 * radical_cond*OF); // Bound for cond at 3 is 3^2.
    G := TargetRestriction(G,F);
    EG := [x : x in Elements(G) | Order(x) eq 3];
    EG_prune := {};
    for x in EG do
        Include(~EG_prune,{x,x^-1});
     end for;
     return [Random(x) : x in EG_prune];
end function;

function C3FieldCheck(f : radical_cond := 1, primes_bound := 1000);
    Z := Integers();
    K := CyclotomicField(3);
    l := PrimeIdealsOverPrime(K,7)[1];
    F, phi := ResidueClassField(l);
    FF , psi := ext<F|6>;
    inert_primes := [];
    if radical_cond eq 1 then
        radical_cond := RadCond(f);
    end if;
        for p in PrimesUpTo(primes_bound) do
            if radical_cond mod p eq 0 then continue; end if;
            if  p mod 3 eq 2 then continue; end if;
            pfacs := PrimeIdealsOverPrime(K,p);
            Lpol := getLpol(f,radical_cond,p);
            if Type(Lpol) eq MonStgElt then continue; end if;
            facs := Factorisation(ChangeRing(Lpol,K));
            if #facs eq 2 and Degree(facs[1,1]) eq 3 and Degree(facs[2,1]) eq 3 and facs[1,2] eq 1 and facs[2,2] eq 1 then
               fac1 := Eltseq(facs[1,1]);
               fac2 := Eltseq(facs[2,1]);
            else continue;
            end if;
            p;
            for s in [fac1,fac2] do
            pol := Polynomial([phi(c): c in s]); pol;
            if #Factorisation(pol) ne 1 then Append(~inert_primes,p); end if;
/*
            s;
            Polynomial(s);
            pol := Polynomial([psi(phi(c)): c in s]); pol;
            Factorisation(pol);
            Roots(Polynomial([psi(phi(c)): c in s]),FF);
            Rs := [r[1]: r in Roots(Polynomial([psi(phi(c)): c in s]), FF )];
            Rs;
            Rs[1]^7;
               for r in Rs do
                if not(r^7 in Rs) then Append(~inert_primes,p); end if;
               end for;
*/
            end for;
        end for;
return Sort(Setseq(Seqset(inert_primes)));
end function;
function C3InertPrimes(f : radical_cond := 1, primes_bound := 1000);
    Z := Integers();
    K := CyclotomicField(3);
    l := PrimeIdealsOverPrime(K,7)[1];
    F, phi := ResidueClassField(l);
    inert_primes := [];
    if radical_cond eq 1 then
        radical_cond := RadCond(f);
    end if;
        for p in PrimesUpTo(primes_bound) do
            if radical_cond mod p eq 0 then continue; end if;
            if  p mod 3 eq 2 then continue; end if;
            Lpol := getLpol(f,radical_cond,p);
            if Type(Lpol) eq MonStgElt then continue; end if;
            facs := Factorisation(ChangeRing(Lpol,K));
            if #facs eq 2 and Degree(facs[1,1]) eq 3 and Degree(facs[2,1]) eq 3 and facs[1,2] eq 1 and facs[2,2] eq 1 then
               fac1 := Eltseq(facs[1,1]);
               fac2 := Eltseq(facs[2,1]);
            else continue;
            end if;
            for s in [fac1,fac2] do
            pol := Polynomial([phi(c): c in s]);
            if #Factorisation(pol) ne 1 then Append(~inert_primes,p); else continue; end if; // Note that here we unfortunately have to loose some of our inert primes, as the corresponding elements are GL_3 conjugate to elements in the n>
            p;
            Factorisation(pol);
            pol;
            end for;
        end for;
return Sort(Setseq(Seqset(inert_primes)));
end function;

C3Fields := function(f);
radical_cond := RadCond(f);
ourprimes := C3InertPrimes(f : radical_cond := radical_cond);
chars := cubic_fields(radical_cond);
ourchars := [];
K := CyclotomicField(3);
for chi in chars do
possible := true;
  for p in ourprimes do
    pps := PrimeIdealsOverPrime(K,p);
    if chi(pps[1]) eq 1 and chi(pps[2]) eq 1 then possible := false; break; end if;
  end for;
if not possible then continue;
else Append(~ourchars,chi);
end if;
end for;
return ourchars;
end function;

function C3test(f : radical_cond := 1, primes_bound := 1000);
    Z := Integers();
    F := CyclotomicField(3);
    possibly_nonsurj_primes := [];
    if radical_cond eq 1 then
        radical_cond := RadCond(f);
    end if;
    cubicdirichletchars := cubic_fields(radical_cond);
    for chi in cubicdirichletchars do
chi;
        bignum := 0;
        for p in PrimesUpTo(primes_bound) do
            if radical_cond mod p eq 0 then continue; end if;
            if p ne 2 and p mod 3 eq 2 then
                if chi(p) eq 1 then continue; end if;
                Lpol := getLpol(f,radical_cond,p);
                if Type(Lpol) eq MonStgElt then continue; end if;
//                        printf "Using an inert prime in C3test. ";
                        newnum := Coefficient(Lpol,5); //won't this always be 0?
//                        if newnum ne 0 then printf "It has worked.\n"; end if;
                        bignum := GCD(bignum,newnum);
            elif p mod 3 eq 1 then
                pfacs := PrimeIdealsOverPrime(F,p);
                if chi(pfacs[1]) eq 1 or chi(pfacs[2]) eq 1 then continue; end if;
                Lpol := getLpol(f,radical_cond,p);
                    if Type(Lpol) eq MonStgElt then continue; end if;
                    facs := Factorisation(ChangeRing(Lpol,F));
                    if #facs eq 2 and Degree(facs[1,1]) eq 3 and Degree(facs[2,1]) eq 3 and facs[1,2] eq 1 and facs[2,2] eq 1 then
//                            printf "Using a split prime in C3test. ";
                            fac1 := facs[1,1];
                            fac2 := facs[2,1];
                            newnum := Z ! (Coefficient(fac1,2)*Coefficient(fac2,2));
//                            if newnum ne 0 then printf "It has worked.\n"; end if;
                            bignum := GCD(bignum,newnum);bignum;
                        if bignum eq 1 then break; end if;
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

