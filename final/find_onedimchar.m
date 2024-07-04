intrinsic find_onedimchar(f :: RngUPolElt, ell :: RngIntElt : radical_cond := 1, primes_bound := 500, ramified := false, uselambdacharpols := false, noskip := true, Hecke_stricteval := true) -> SeqEnum, SeqEnum
{returns list of possible characters of the Galois group of K=Q(zeta_3) that can
possibly occur in the mod-ell Galois representation of the Jacobian of the curve y^3 = f(x).}
    SetColumns(0);
    Z := Integers();
    P_ell<T> := PolynomialRing(GF(ell));
    f := suppressed_integer_quartic(f);
    if radical_cond eq 1 then radical_cond := RadCond(f); end if;
    if ramified then
        radical_cond := (radical_cond mod ell eq 0) select radical_cond else ell*radical_cond;
    end if;
    cond := radical_cond^4;
    F<zeta3> := CyclotomicField(3);
    OF := RingOfIntegers(F);
    P_F<xF> := PolynomialRing(OF);
    ellaboveF := PrimeIdealsOverPrime(F,ell);
    OFmodell1, resF1 := ResidueClassField(OF,ellaboveF[1]);
    OFmodell2, resF2 := ResidueClassField(OF,ellaboveF[2]);
    G := HeckeCharacterGroup(cond*OF);
    K_targ := (ell mod 3 eq 1) select CyclotomicField(ell-1) else CyclotomicField(ell^2-1);
    G := TargetRestriction(G,K_targ);
    OK_targ := RingOfIntegers(K_targ);
    ellabove := PrimeIdealsOverPrime(K_targ,ell);
    OK_targ_modell, resmodell := ResidueClassField(OK_targ,ellabove[1]);
/*
// If SetTargetRing(~chi,GF(ell).1) works,
// ResidueClassField and resmodell could also be replaced.
// The following code could also be simplified.
    omegaF, incl1 := TorsionUnitGroup(K_targ);
    F_ell := GF(ell);
    F_ellcross, incl2 := MultiplicativeGroup(F_ell);
    assert #omegaF eq #F_ellcross;
    alp := incl2(F_ellcross.1);
    isom := hom<omegaF -> F_ellcross | F_ellcross.1>;
    assert #Kernel(isom) eq 1;
*/

    charpols := getcharpols(f : primesend := primes_bound);
// TODO: can possibly use Bracket-2 of charpols at inert primes.
    if ramified then
        charpols := [x : x in charpols | x[1] mod 3 eq 1 and x[1] ne ell];
    else
        charpols := [x : x in charpols | x[1] mod (3*ell) eq 1];
    end if;
    if uselambdacharpols cmpne false then
        resF1_pol := hom<P_F->P_ell|resF1,T>;
        charpolsfacs := [<x[1],Factorisation(ChangeRing(x[2],OF))> : x in charpols];
        charpolsmodell := [];
        for x in charpolsfacs do
            pi1 := PrimeIdealsOverPrime(F,x[1])[1]; // there is a choice here for each p
            if #x[2] ne 2 or {Degree(y[1]) : y in x[2]} ne {3} then continue; end if;
            charpol_rightsplitfacs := [g[1] : g in x[2] | Coefficient(g[1],0)*OF eq x[1]*pi1];
// TODO: there is no reason this is a consistent pick for charpoly at p for a
// chosen 3-dim piece (\lambda-adic part) of the ell-adic Tate module T_ell(A).
            if #charpol_rightsplitfacs ne 1 then continue; end if;
            Append(~charpolsmodell,<x[1],resF1_pol(charpol_rightsplitfacs[1])>);
        end for;
    else
        charpolsmodell := [<x[1],P_ell ! x[2]> : x in charpols];
    end if;
    primes := [x[1] : x in charpolsmodell];
//    printf "\nUsing L-polynomials at the (ordinary) primes\n%o\n\n", primes;
//    print charpolsmodell;

    gens_G := SetToSequence(Generators(G));
    n := #gens_G;
    exps_G := [Order(chi) : chi in gens_G];
    conds_G := [Conductor(chi) : chi in gens_G];
    printf "Orders of the characters generating the Hecke character group:\n%o\n", exps_G;
//    printf "Orders and conductors of the characters generating the Hecke character group:\n%o\n%o\n", exps_G, conds_G;

    X := Set(CartesianProduct([[0..e-1] : e in exps_G]));
/*
it's enough to test only chi or chi^-1.
    X := Set(CartesianProduct([[0..((exps_G[1]-1) div 2)]] cat [[0..e-1] : e in exps_G[2..#exps_G]])); // could be improved
*/
    ind := 1;
    prime_ideals := [];
    number_linearfacs := 6;
    all_roots_charpolsmodell := [];
    while #X gt 0 do
        p := charpolsmodell[ind,1];
        charpol := charpolsmodell[ind,2];
        p_idealfacs := Factorisation(p*OF);
        p1 := p_idealfacs[1,1];
        p2 := p_idealfacs[2,1];
        Append(~prime_ideals,<p1,p2>);
        if cond mod p ne 0 then
            roots_charpol := Roots(charpol);
            if #roots_charpol eq 0 then
                printf "Witness: p = %o, Frob_p charpol mod %o = %o\n", p, ell, charpol;
                return [], [];
            end if;
            Append(~all_roots_charpolsmodell, <p,&join[{*r[1] : i in [1..r[2]]*} : r in roots_charpol]>);
            eigvals_rhoell_frobp := [r[1] : r in roots_charpol];
//            printf "Charpol at p=%o has roots %o over F_%o\n", p, roots_charpol, ell;
            gens_evalsatp1 := [resmodell((gens_G[i])(p1)) : i in [1..n]];
            gens_evalsatp2 := [resmodell((gens_G[i])(p2)) : i in [1..n]];
// Inefficient earlier attempts
//            Xnew := [x : x in X | incl2(isom((&*[(gens_G[i])^(x[i]) : i in [1..n]])(p1)@@incl1)) in eigvals_rhoell_frobp];
//            Xnew := [x : x in X | resmodell((&*[(gens_G[i])^(x[i]) : i in [1..n]])(p1)) in eigvals_rhoell_frobp];
//            Xnew := [x : x in X | resmodell((&*[(gens_G[i])^(x[i]) : i in [1..n]])(p1)) in eigvals_rhoell_frobp or resmodell((&*[(gens_G[i])^(x[i]) : i in [1..n]])(p2)) in eigvals_rhoell_frobp];
            if Hecke_stricteval then
                Xnew := [x : x in X | &*[gens_evalsatp1[i]^(x[i]) : i in [1..n]] in eigvals_rhoell_frobp];
            else
                Xnew := [x : x in X | &*[gens_evalsatp1[i]^(x[i]) : i in [1..n]] in eigvals_rhoell_frobp or &*[gens_evalsatp2[i]^(x[i]) : i in [1..n]] in eigvals_rhoell_frobp];
            end if;
            if noskip or Xnew ne [] then
                X := Xnew;
                number_linearfacs := Minimum(number_linearfacs,&+([] cat [r[2] : r in roots_charpol]));
            end if;
        end if;
//        print p, #X;
        ind := ind+1;
        if ind gt #charpolsmodell then
            printf "Checked %o primes, up to %o\n", #charpolsmodell, p;
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
            p1 := prime_ideals[i][1];
            p2 := prime_ideals[i][2];
            chi_values_modell[p] := <resmodell((chi)(p1)),resmodell((chi)(p2))>;
//            chi_values_modell[p] := incl2(isom((chi)(p1)@@incl1));
        end for;
        Append(~X_chars_values,rec<RF | char := chi, values_modell := chi_values_modell>);
    end for;
/*
    if #X_chars gt number_linearfacs then
        ps := [x[1] : x in charpolsmodell];
        roots_charpolsmodell := [&join[{*r[1] : i in [1..r[2]]*} : r in Roots(charpol[2])] : charpol in charpolsmodell];

        V := VectorSpace(GF(2),#X_chars);
        count := 0;
        good_vs := [];
        for v in V do
            if &+v eq number_linearfacs then
                count := count + 1;



            end if;
        end for;

        for i := 1 to #charpolsmodell do
            print ps[i], roots_charpolsmodell[i];
        end for;
*/
    printf "Based on the L-polynomials at ORDINARY primes, only the following characters COULD appear as subquotients of rhobar_%o:\n", ell;
    printf "Found %o potential characters. Every Lpoly (factor) used has at least %o linear factors over F_%o.\n", #X_chars, number_linearfacs, ell;
/*
    if number_linearfacs eq 2 and #X_chars eq 4 then
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
        printf "The product of a dual-pair of characters appearing in rhobar_%o is the mod-%o cyclotomic character. Pairing up the characters that could appear, using this fact.\n", ell, ell;
        X_chars_values := X_chars_values_new;
    end if;
*/
    return X_chars_values, all_roots_charpolsmodell;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////////////////////////////
//     Example: Finding the 1-dim subquotient reps of \ell-torsion representation of a genus 2 Jacobian    //
/////////////////////////////////////////////////////////////////////////////////////////////////////////////

/*
P<x> := PolynomialRing(IntegerRing());
f := x^4 + x^2 + 1;
cond := PicardConductor(f);
n, onedim_subreps_of7tors, all_roots_charpols := find_onedimchar(f,cond,7);

[<Conductor(chi`char), Order(chi`char)> : chi in onedim_subreps_of7tors];
[Factorisation(Norm(Conductor(AssociatedPrimitiveCharacter(chi`char)))) : chi in onedim_subreps_of7tors];

fields_cutout_over_Qzeta3 := [NumberField(AbelianExtension(chi`char)) : chi in onedim_subreps_of7tors];
*/

/*
Why are there 4 characters found for y^3 = x^4-1? It should be 0, 2 or 6, isn't it?
*/



/*
AttachSpec("spec");
P<x> := PolynomialRing(Rationals());

///////////////
// Example 1 //
///////////////
f := P ! [ -142, -387, -147, 338, 243 ]; RadCond(f);
chars1, allroots := find_onedimchar(f,13);
chars2, allroots := find_onedimchar(f,13 : noskip := false);
chars3, allroots := find_onedimchar(f,13 : Hecke_stricteval := false);
chars4, allroots := find_onedimchar(f,13 : Hecke_stricteval := false, noskip := false);
chars5, allroots := find_onedimchar(f,13 : uselambdacharpols := true);
#chars1, #chars2, #chars3, #chars4, #chars5;
// 0 2 0 200 0


///////////////
// Example 2 //
///////////////

f := x^4 + 2*x^3 + 4*x^2 + 2*x + 1; RadCond(f);
chars1, allroots := find_onedimchar(f,7);
chars2, allroots := find_onedimchar(f,7 : noskip := false);
chars3, allroots := find_onedimchar(f,7 : Hecke_stricteval := false);
chars4, allroots := find_onedimchar(f,7 : Hecke_stricteval := false, noskip := false);
chars5, allroots := find_onedimchar(f,7 : uselambdacharpols := true);
#chars1, #chars2, #chars3, #chars4, #chars5;
// 4 4 4 4 2

G := Parent(chars1[1]`char);
L1 := [G!x`char : x in chars1];
L2 := [G!x`char : x in chars2];
L3 := [G!x`char : x in chars3];
L4 := [G!x`char : x in chars4];
L5 := [G!x`char : x in chars5];
L1 eq L2, L1 eq L3, L1 eq L4, Set(L5) subset Set(L1);
// true true true true


ramchars1, allroots := find_onedimchar(f,7 : ramified := true);
ramchars2, allroots := find_onedimchar(f,7 : ramified := true, noskip := false);
ramchars3, allroots := find_onedimchar(f,7 : ramified := true, Hecke_stricteval := false);
ramchars4, allroots := find_onedimchar(f,7 : ramified := true, Hecke_stricteval := false, noskip := false);
ramchars5, allroots := find_onedimchar(f,7 : ramified := true, uselambdacharpols := true);
#ramchars1, #ramchars2, #ramchars3, #ramchars4, #ramchars5;
// 6 6 6 6 3

GG := Parent(ramchars1[1]`char);
LL1 := [GG!x`char : x in ramchars1];
LL2 := [GG!x`char : x in ramchars2];
LL3 := [GG!x`char : x in ramchars3];
LL4 := [GG!x`char : x in ramchars4];
LL5 := [GG!x`char : x in ramchars5];
LL1 eq LL2, LL1 eq LL3, LL1 eq LL4, Set(LL5) subset Set(LL1);
// true true true true


[[Norm(Conductor(ramchi/chi)) : chi in L1] : ramchi in LL1];
//
[
[ 144, 16, 36, 1 ],
[ 1, 36, 16, 144 ],
[ 784, 7056, 49, 1764 ],
[ 2800, 25200, 2800, 25200 ],
[ 1764, 49, 7056, 784 ],
[ 25200, 2800, 25200, 2800 ]
]
//

// We want to say that the right pairs <unramified,ramified character>
// correspond to the entries 49=Norm(7) in the above table,
// since the conductor of the mod-7 cyclotomic character is 7.
// But it's unclear. See below.

eps := L1[3];
epschi7 := LL1[3];
// chi7 := epschi7/eps;
chi7 := AssociatedPrimitiveCharacter(epschi7/eps);

K_chi7 := AbsoluteField(NumberField(AbelianExtension(chi7)));
assert IsNormal(K_chi7) and #Roots(CyclotomicPolynomial(7),K_chi7) eq 6;
// true

assert eps^-1 eq L1[2]; assert exists(chipow){i : i in [1..6] | LL1[5]/(eps^-1) eq Extend(chi7,GG)^i};
// false false

eps2 := L1[2]; assert exists(chipow){i : i in [1..6] | LL1[5]/eps2 eq Extend(chi7,GG)^i}; chipow;
// 1
assert AssociatedPrimitiveCharacter(LL1[5]/eps2) eq chi7;
eps12 := eps*eps2;
Order(eps12);
// 2
Norm(Conductor(eps12));
// 16
assert Conductor(eps*eps2) eq 4*RingOfIntegers(CyclotomicField(3));

[Polredabs(DefiningPolynomial(AbsoluteField(NumberField(AbelianExtension(chi))))) : chi in [eps, eps2]];
//
[
x^12 - 3*x^10 + 9*x^6 + 12*x^4 + 9*x^2 + 3,
x^12 - 3*x^10 + 9*x^6 + 12*x^4 + 9*x^2 + 3
]
//
[IsNormal(AbsoluteField(NumberField(AbelianExtension(chi)))) : chi in [eps, eps2]];
// [ false, false ]
IsIsomorphic(NumberField(AbelianExtension(eps)),NumberField(AbelianExtension(eps2)));
// true
K_eps := NumberField(AbelianExtension(eps)); K_eps;
// Number Field with defining polynomial [ $.1^2 - zeta_3 - 2, $.1^3 + 2 ] over its ground field
K_eps2 := NumberField(AbelianExtension(eps2)); K_eps2;
// Number Field with defining polynomial [ $.1^2 + zeta_3 - 1, $.1^3 + 2 ] over its ground field
defpols_Keps := DefiningPolynomial(K_eps);
[#Roots(g,K_eps2) : g in defpols_Keps];
// [ 0, 3 ]
// So K_eps and K_eps2 are not isomorphic as extensions of F = Q(zeta_3).
// But there seems to be NO SIMPLE WAY in magma to check for isomorphism of two relative extensions! See below.
// Calling "NumberField" to create K_eps and K_eps2 seems to be the problem. See below.


K_epsrel := RelativeField(BaseField(K_eps),K_eps);
K_eps2rel := RelativeField(BaseField(K_eps2),K_eps2);
boo, phi := IsIsomorphic(K_epsrel,K_eps2rel);
BaseField(K_epsrel).1 eq phi(BaseField(K_epsrel).1);
// false

F := Domain(DirichletRestriction(G!1));
K_epsrel := RelativeField(F,K_eps);                  
K_eps2rel := RelativeField(F,K_eps2);
boo, phi := IsIsomorphic(K_epsrel,K_eps2rel);
F.1 eq phi(F.1);
// false

printf "%m\n%m\n", K_eps, K_eps2;                                
//
NumberField([ Polynomial(K, [ -K0.1 - 2, 0, 1]), Polynomial(K, [ 2, 0, 0, 1])]:Abs) where K is CyclotomicField(3)
NumberField([ Polynomial(K, [ K0.1 - 1, 0, 1]), Polynomial(K, [ 2, 0, 0, 1])]:Abs) where K is CyclotomicField(3)
//
Looks like if I remove the word Abs in the above commands, then magma does infact say the two fields are not isomorphic.
So I guess when I construct the fields from the Hecke characters I should not call "NumberField", rather something else
to retain the base field info.


*/
