load "Lpolys.m";
load "PicardConductor.m";
/*
function getLpols(f, cond, primesstart, primesend);
    P<x> := Parent(f);

//    Attach("../picard_curves/picard_curves/magma/spec");
//    f_Q := ChangeRing(f,Rationals());
//    disc := AbsoluteValue(QuarticDiscriminant(PicardForm(ReducedWeierstrassEquation(f_Q))));
//    disc := Numerator(disc)*Denominator(disc);

    firstrun := true;
    for N := primesstart to primesend do
        p := NthPrime(N);

//        if disc mod p ne 0 then
        if cond mod p ne 0 then
            pstr := IntegerToString(p);
            fcoeffs := [IntegerToString(c) : c in Coefficients(f)];
            fstr := "x^4+" cat fcoeffs[3] cat "x^2+" cat fcoeffs[2] cat "x+" cat fcoeffs[1];
            if firstrun then
                System("hwlpoly y^3=" cat fstr cat " " cat pstr cat " 1 > CartManmats.txt");
                firstrun := false;
            else
                System("hwlpoly y^3=" cat fstr cat " " cat pstr cat " 1 >> CartManmats.txt");
            end if;
        end if;
    end for;

    fil := Open("CartManmats.txt", "r");
    C := Coefficients(f)[1..3];
    Lpols := liftLpolys(fil,C);
    return Lpols;
end function;
*/

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

function RadCond(f);
    f := suppressed_integer_quartic(f);
    radical_disc := &*([1] cat [p : p in PrimeFactors(Discriminant(f))]);
    radical_leadcoeff := &*([1] cat [p : p in PrimeFactors(Coefficient(f,4))]);
    radical_cond := radical_leadcoeff*radical_disc;
    if radical_cond mod 3 ne 0 then
        radical_cond := 3*radical_cond;
    end if;
    return radical_cond;
end function;

function getLpol(f,radical_cond,p);
    f := suppressed_integer_quartic(f);
    P<x> := Parent(f);
    if radical_cond eq 1 then radical_cond := RadCond(f); end if;
    if radical_cond mod p eq 0 then return "Bad Prime"; end if;
/*
    require radical_cond mod p ne 0 : "Bad Prime";
*/
    pstr := IntegerToString(p);
    fstr := &cat(Split(Sprint(f)," "));
/*
    System("hwlpoly y^3=" cat fstr cat " " cat pstr cat " 1 > CartManmat_for_p.txt");
    fil := Open("CartManmat_for_p.txt", "r");
    C := Coefficients(f)[1..3];
    Lpol := liftLpolys(fil,C);
*/
    C := Coefficients(f)[1..3];
    cartmanmat := Pipe("hwlpoly y^3=" cat fstr cat " " cat pstr cat " 1","");
    Lpol := liftLpoly(cartmanmat,C);
//    print Lpol;
    if #Lpol ne 1 then return "Error in computing L-polynomial"; end if;
/*
    require #Lpol eq 1 : "Error in computing L-polynomial";
*/
    return P ! Reverse(Lpol[1,2]);
end function;

function getLpols(f,radical_cond,primesstart,primesend);
    f := suppressed_integer_quartic(f);
    P<x> := Parent(f);
    if radical_cond eq 1 then radical_cond := RadCond(f); end if;
    Lpols := [];
    for N := primesstart to primesend do
        p := NthPrime(N);
        if radical_cond mod p eq 0 then continue; end if;
        Lpolatp := getLpol(f,radical_cond,p);
        if Type(Lpolatp) eq MonStgElt then continue; end if;
        Lpols := Lpols cat [<p,Lpolatp>];
    end for;
    return Lpols;
end function;


function find_onedimchar(f, cond, ell : primes_bound := 100);
    Z := Integers();
    P_ell<T> := PolynomialRing(GF(ell));

    cond := ell*cond;
    print Factorisation(cond);

    F<zeta3> := CyclotomicField(3);
    OF := RingOfIntegers(F);
    G := HeckeCharacterGroup(cond*OF);
    Q_zeta_lminus1 := CyclotomicField(ell-1);
    G := TargetRestriction(G,Q_zeta_lminus1);

// If SetTargetRing(~chi,GF(ell).1) works, the following code could be simplified.
    omegaF, incl1 := TorsionUnitGroup(Q_zeta_lminus1);
    F_ell := GF(ell);
    F_ellcross, incl2 := MultiplicativeGroup(F_ell);
    assert #omegaF eq #F_ellcross;
    alp := incl2(F_ellcross.1);
    isom := hom<omegaF -> F_ellcross | F_ellcross.1>;
    assert #Kernel(isom) eq 1;


    Lpols := getLpols(f, cond, 1, primes_bound);
    charpols := [<x[1],P_ell ! Reverse(x[2])> : x in Lpols];
//    print charpols;

    gens_G := SetToSequence(Generators(G));
    n := #gens_G;
    exps_G := [Order(chi) : chi in gens_G];

    print exps_G;
    print [Conductor(chi) : chi in gens_G];

    X := Set(CartesianProduct([[0..e-1] : e in exps_G]));
    ind := 1;
    charpols := [x : x in charpols | x[1] mod 3 eq 1];
    primes := [x[1] : x in charpols];
    printf "Using L-polynomials at the (ordinary) primes\n%o\n", primes;
    prime_ideals := [];
    numb_of_chars_to_expect := 6;
    all_roots_charpols := [];
    while #X gt 0 do
        p := charpols[ind,1];
        charpol := charpols[ind,2];
        
        p_idealfacs := Factorisation(p*OF);
        p1 := p_idealfacs[1,1];
        p2 := p_idealfacs[2,1];
        Append(~prime_ideals,p1);
        if cond mod p ne 0 then
            roots_charpol := Roots(charpol);
            Append(~all_roots_charpols, &join[{*r[1] : i in [1..r[2]]*} : r in roots_charpol]);
            eigvals_rhoell_frobp := [r[1] : r in roots_charpol];
            numb_of_chars_to_expect := Minimum(numb_of_chars_to_expect,(roots_charpol eq []) select 0 else &+[r[2] : r in roots_charpol]);
            X := [x : x in X | incl2(isom((&*[(gens_G[i])^(x[i]) : i in [1..n]])(p1)@@incl1)) in eigvals_rhoell_frobp];
        end if;
        print p, #X;
        ind := ind+1;
        if ind gt #charpols then
            printf "Checked %o primes, up to %o\n", #charpols, p;
            break;
        end if;
    end while;

    X_chars := <&*[(gens_G[i])^x[i] : i in [1..n]] : x in X>;
    RF := recformat<char : GrpHeckeElt, values_modell : Assoc>;
    X_chars_values := [];
    for chi in X_chars do
        chi_values_modell := AssociativeArray();
        for i := 1 to #primes do
            p := primes[i];
            p1 := prime_ideals[i];
            chi_values_modell[p] := incl2(isom((chi)(p1)@@incl1));
        end for;
        Append(~X_chars_values,rec<RF | char := chi, values_modell := chi_values_modell>);
    end for;
/*
    if #X_chars gt numb_of_chars_to_expect then
        ps := [x[1] : x in charpols];
        roots_charpols := [&join[{*r[1] : i in [1..r[2]]*} : r in Roots(charpol[2])] : charpol in charpols];

        V := VectorSpace(GF(2),#X_chars);
        count := 0;
        good_vs := [];
        for v in V do
            if &+v eq numb_of_chars_to_expect then
                count := count + 1;



            end if;
        end for;

        for i := 1 to #charpols do
            print ps[i], roots_charpols[i];
        end for;
*/
    printf "Based on the L-polynomials at ORDINARY primes, only the following characters COULD appear as subquotients of rhobar_%o:\n", ell, ell;
    if numb_of_chars_to_expect ne #X_chars then
        printf "Found %o potential characters, but only %o characters are expected.\n", #X_chars, numb_of_chars_to_expect;
        if numb_of_chars_to_expect eq 2 and #X_chars eq 4 then
            prod_all_chars := X_chars[1]*X_chars[2]*X_chars[3]*X_chars[4];
            X_chars_values_new := [];
            for j := 2 to 4 do
                testpair := X_chars[1]*X_chars[j];
                otherinds := Exclude([2..4],j);
                if testpair^2 eq prod_all_chars and Conductor(testpair) eq ell*OF then
                    Append(~X_chars_values_new, [X_chars_values[1], X_chars_values[j]]);
                    Append(~X_chars_values_new, [X_chars_values[k] : k in otherinds]);
                end if;
            end for;
        end if;
        printf "The product of a dual-pair of characters appearing in rhobar_%o is the mod-%o cyclotomic character. Pairing up the characters that could appear, using this fact.\n", ell, ell;
        X_chars_values := X_chars_values_new;
    end if;
    return numb_of_chars_to_expect, X_chars_values, all_roots_charpols;
end function;

/////////////////////////////////////////////////////////////////////////////////////////////////////////////
//     Example: Finding the 1-dim subquotient reps of \ell-torsion representation of a genus 2 Jacobian    //
/////////////////////////////////////////////////////////////////////////////////////////////////////////////

P<x> := PolynomialRing(IntegerRing());
f := x^4 + x^2 + 1;
cond := PicardConductor(f);
n, onedim_subreps_of7tors, all_roots_charpols := find_onedimchar(f,cond,7);

[<Conductor(chi`char), Order(chi`char)> : chi in onedim_subreps_of7tors];
[Factorisation(Norm(Conductor(AssociatedPrimitiveCharacter(chi`char)))) : chi in onedim_subreps_of7tors];

fields_cutout_over_Qzeta3 := [NumberField(AbelianExtension(chi`char)) : chi in onedim_subreps_of7tors];


/*
Why are there 4 characters found for y^3 = x^4-1? It should be 0, 2 or 6, isn't it?
*/



