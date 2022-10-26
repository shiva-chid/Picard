load "Lpolys.m";
load "PicardConductor.m";

function getLpols(f, cond, primesstart, primesend);
    P<x> := Parent(f);
/*
Attach("../picard_curves/picard_curves/magma/spec");
    f_Q := ChangeRing(f,Rationals());
    disc := AbsoluteValue(QuarticDiscriminant(PicardForm(ReducedWeierstrassEquation(f_Q))));
    disc := Numerator(disc)*Denominator(disc);
*/
    firstrun := true;
    for N := primesstart to primesend do
        p := NthPrime(N);
/*
        if disc mod p ne 0 then
*/
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

    omegaF, incl1 := TorsionUnitGroup(Q_zeta_lminus1);
    F_ell := GF(ell);
    F_ellcross, incl2 := MultiplicativeGroup(F_ell);
    assert #omegaF eq #F_ellcross;
    alp := incl2(F_ellcross.1);
    isom := hom<omegaF -> F_ellcross | F_ellcross.1>;
    assert #Kernel(isom) eq 1;


    Lpols := getLpols(f, cond, 1, primes_bound);
    charpols := [<x[1],P_ell ! Reverse(x[2])> : x in Lpols];
/*
    print charpols;
*/

    gens_G := SetToSequence(Generators(G));
    n := #gens_G;
    exps_G := [Order(chi) : chi in gens_G];

    print exps_G;
    print [Conductor(chi) : chi in gens_G];

    X := Set(CartesianProduct([[0..e-1] : e in exps_G]));
    ind := 1;
    charpols := [x : x in charpols | x[1] mod 3 eq 1];
    while #X gt 0 do
        p := charpols[ind,1];
        charpol := charpols[ind,2];
        
        p_idealfacs := Factorisation(p*OF);
        p1 := p_idealfacs[1,1];
        p2 := p_idealfacs[2,1];

        if cond mod p ne 0 then
            eigvals_rhoell_frobp := [r[1] : r in Roots(charpol)];
/*
            if #eigvals_rhoell_frobp lt 2 then
                print p, charpol;
                ind := ind+1;
                if ind gt #charpols then
                    printf "Checked %o primes, up to %o\n", #charpols, p;
                    break;
                end if;
                continue;
            end if;
*/
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
    return X_chars;
end function;

/////////////////////////////////////////////////////////////////////////////////////////////////////////////
//     Example: Finding the 1-dim subquotient reps of \ell-torsion representation of a genus 2 Jacobian    //
/////////////////////////////////////////////////////////////////////////////////////////////////////////////

P<x> := PolynomialRing(IntegerRing());
f := x^4 + x^2 + 1;
cond := PicardConductor(f);
onedim_subreps_of7tors := find_onedimchar(f,cond,7);

[<Conductor(chi), Order(chi)> : chi in onedim_subreps_of7tors];
[Factorisation(Norm(Conductor(AssociatedPrimitiveCharacter(chi)))) : chi in onedim_subreps_of7tors];

fields_cutout_over_Qzeta3 := [NumberField(AbelianExtension(chi)) : chi in onedim_subreps_of7tors];
