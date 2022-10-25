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
/*
We need to replace G by a DirichletGroup over Q(zeta_3).
The ell-torsion representation rho_ell is reducible only when restricted to G_{Q(zeta_3)}.
So the desired one-dimensional subquotient characters are characters of G_{Q(zeta_3)}.
*/
    G := DirichletGroup(cond,GF(ell));

    Lpols := getLpols(f, cond, 1, primes_bound);
    charpols := [<x[1],P_ell ! Reverse(x[2])> : x in Lpols];
/*
    print charpols;
*/

    gens_G := Generators(G);
    n := #gens_G;
    exps_G := [Order(G.i) : i in [1..n]];

    print exps_G;
    print [Conductor(chi) : chi in gens_G];

    X := Set(CartesianProduct([[0..e-1] : e in exps_G]));
    ind := 1;
    charpols := [x : x in charpols | x[1] mod 3 eq 1];
    while #X gt 2 do
        p := charpols[ind,1];
        charpol := charpols[ind,2];

        print p, #X;

        if cond mod p ne 0 then
            eigvals_rhoell_frobp := [r[1] : r in Roots(charpol)];
            X := [x : x in X | Evaluate(&*[(G.i)^(x[i]) : i in [1..n]],p) in eigvals_rhoell_frobp];
        end if;
        ind := ind+1;
        if ind gt #charpols then
            printf "Exceeded the bound for primes";
            break;
        end if;
    end while;
    X_chars := [&*[(G.i)^x[i] : i in [1..n]] : x in X];
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
[ValueList(AssociatedPrimitiveCharacter(chi)) : chi in onedim_subreps_of7tors];


