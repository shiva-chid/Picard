intrinsic find_onedimchar(f :: RngUPolElt, ell :: RngIntElt : radical_cond := 1, primes_bound := 400, charpols := [], unramified := true, useinertFrobsq := true, Hecke_stricteval := false, uselambdacharpols := false) -> SeqEnum, SeqEnum
{returns list of characters of the Galois group of K=Q(zeta_3) that can
possibly occur in the mod-ell Galois representation of the Jacobian of the curve y^3 = f(x).}
    SetColumns(0);
    Z := Integers();
    P_ell<T> := PolynomialRing(GF(ell));
    f := suppressed_integer_quartic(f);
    if radical_cond eq 1 then radical_cond := RadCond(f); end if;
    if not unramified then
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
    if charpols eq [] then
        charpols := getcharpols(f : primesend := primes_bound);
    end if;
    printf "Charpols found at primes:\n%o\n", [x[1] : x in charpols];
    if useinertFrobsq then
        // using Bracket-2 of charpols at inert primes.
        charpols := [(x[1] mod 3 eq 1) select x else <x[1],Bracket(2,x[2])> : x in charpols | x[1] ne 3 and x[1] ne ell];
    else
        charpols := [x : x in charpols | x[1] mod 3 eq 1 and x[1] ne ell];
    end if;
    printf "Throwing away ell, and possibly inert primes. Retained:\n%o\n", [x[1] : x in charpols];
/*
    if unramified then
        charpols := [x : x in charpols | x[1] mod ell eq 1];
    end if;
    printf "if looking for the unramified-at-ell character, only retaining primes = 1 mod ell\n%o\n", [x[1] : x in charpols];
*/
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
    printf "\nUsing L-polynomials at the (ordinary) primes\n%o\n\n", primes;
//    print charpolsmodell;

    gens_G := Setseq(Generators(G));
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
        if ind gt #charpolsmodell then
            printf "Checked %o primes, up to %o\n", #charpolsmodell, charpolsmodell[#charpolsmodell];
            break;
        end if;
        p := charpolsmodell[ind,1];
        charpol := charpolsmodell[ind,2];
        pabove := PrimeIdealsOverPrime(F,p);
        Append(~prime_ideals,pabove);
        if cond mod p eq 0 then ind := ind+1; continue; end if;
        roots_charpol := Roots(charpol);
        if #roots_charpol eq 0 then
            printf "Witness: p = %o, Frob_p charpol mod %o = %o has no roots\n", p, ell, charpol;
            return [], [];
        end if;
        Append(~all_roots_charpolsmodell, <p,&join[{*r[1] : i in [1..r[2]]*} : r in roots_charpol]>);
        eigvals_rhoell_frobp := [r[1] : r in roots_charpol];
        printf "Charpol at p=%o has roots %o over F_%o\n", p, roots_charpol, ell;
        gens_evalsatpabove := [[resmodell((gens_G[i])(frakp)) : i in [1..n]] : frakp in pabove];
// Inefficient earlier attempts
//        Xnew := [x : x in X | incl2(isom((&*[(gens_G[i])^(x[i]) : i in [1..n]])(pabove[1])@@incl1)) in eigvals_rhoell_frobp];
//        Xnew := [x : x in X | resmodell((&*[(gens_G[i])^(x[i]) : i in [1..n]])(pabove[1])) in eigvals_rhoell_frobp];
//        Xnew := [x : x in X | resmodell((&*[(gens_G[i])^(x[i]) : i in [1..n]])(pabove[1])) in eigvals_rhoell_frobp or resmodell((&*[(gens_G[i])^(x[i]) : i in [1..n]])(pabove[2])) in eigvals_rhoell_frobp];
        if Hecke_stricteval then
            X := [x : x in X | &*[gens_evalsatpabove[1][i]^(x[i]) : i in [1..n]] in eigvals_rhoell_frobp];
        else
            X := [x : x in X | &or[&*[gens_evalsatfrakp[i]^(x[i]) : i in [1..n]] in eigvals_rhoell_frobp : gens_evalsatfrakp in gens_evalsatpabove]];
        end if;
        number_linearfacs := Minimum(number_linearfacs,&+([] cat [r[2] : r in roots_charpol]));
        print p, #X;
        ind := ind+1;
    end while;

    X_chars := <&*[(gens_G[i])^x[i] : i in [1..n]] : x in X>;
    RF := recformat<char : GrpHeckeElt, values_modell : Assoc>;
    X_chars_values := [];
    for chi in X_chars do
        chi_values_modell := AssociativeArray();
        for i := 1 to #prime_ideals do
            p := Norm(prime_ideals[i][1] meet Z);
            chi_values_modell[p] := <resmodell((chi)(frakp)) : frakp in prime_ideals[i]>;
//            chi_values_modell[p] := incl2(isom((chi)(prime_ideals[i][1])@@incl1));
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

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//  Example: Finding the 1-dim subquotient reps of \ell-torsion representation of the Jacobian of a Picard curve   //
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/*
AttachSpec("spec");
P<x> := PolynomialRing(IntegerRing());
f := x^4 + x^2 + 1;
chars, allroots := find_onedimchar(f,7 : ramified := true);
//
Orders of the characters generating the Hecke character group:
[ 6, 6, 6, 6, 6 ]
Checked 276 primes, up to <4093, t^6 + 6*t^5 + 2*t^4 + 3*t^2 + 3*t + 6>
Based on the L-polynomials at ORDINARY primes, only the following characters COULD appear as subquotients of rhobar_7:
Found 2 potential characters. Every Lpoly (factor) used has at least 2 linear factors over F_7.
//
G := Parent(chars[1]`char);
OF := Order(Modulus(G));
chars := [G!x`char : x in chars]; chars;
//
[
$.1*$.3^3*$.4*$.5^2,
$.1^4*$.2^5*$.3^2*$.4^4*$.5^4
]
//

chi7 := AssociatedPrimitiveCharacter(&*chars);
assert Conductor(chi7) eq 7*OF;
K_chi7 := AbsoluteField(NumberField(AbelianExtension(chi7)));
assert IsNormal(K_chi7) and #Roots(CyclotomicPolynomial(7),K_chi7) eq 6;

conds := [Conductor(chi) : chi in chars];
[Norm(cond) : cond in conds];
// [ 567, 567 ]
gcdofconds := GCD(conds[1],conds[2]);
conds := [cond/gcdofconds : cond in conds];
[Norm(cond) : cond in conds];
// [ 7, 7 ]
assert conds[1] ne conds[2];
assert conds[1]*conds[2] eq 7*OF;


orders_chars := [Order(chi) : chi in chars]; orders_chars;
// [ 6, 6 ]
fields_chars := [NumberField(AbelianExtension(chi)) : chi in chars]; fields_chars;
//
[
Number Field with defining polynomial [ $.1^2 - 4*zeta_3 - 5, $.1^3 - zeta_3 + 4 ] over its ground field,
Number Field with defining polynomial [ $.1^2 + zeta_3 + 5, $.1^3 - zeta_3 - 5 ] over its ground field
]
//
absolutefields_chars := [AbsoluteField(K) : K in fields_chars]; absolutefields_chars;
//
[
Number Field with defining polynomial x^12 - 18*x^10 + 18*x^9 + 171*x^8 + 72*x^7 - 849*x^6 - 3780*x^5 + 4914*x^4 + 9954*x^3 + 6615*x^2 + 10584*x + 13671 over the Rational Field,
Number Field with defining polynomial x^12 + 27*x^10 - 18*x^9 + 306*x^8 - 18*x^7 + 1986*x^6 + 2268*x^5 + 4725*x^4 + 13860*x^3 + 30429*x^2 + 29106*x + 13671 over the Rational Field
]
//
*/

