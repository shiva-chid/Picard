function read_heckepolsdb();
    fil := Open("cmforms_heckepols.txt","r");
    s := Gets(fil);
    hpols := [];
    while not IsEof(s) do
        while true do
            if s[#s] eq "]" then
                break;
            end if;
            s := Prune(s) cat Gets(fil);
        end while;
        s_split := Split(s,": [,]");
        N := StringToInteger(s_split[1]);
        p := StringToInteger(s_split[2]);
        Append(~hpols,<N,p,[StringToInteger(s_split[i]) : i in [3..#s_split]]>);
        s := Gets(fil);
        if #s eq 0 then
            s := Gets(fil);
        end if;
    end while;
    return hpols;
end function;

function write_heckepolsdb(hpols);
//    fil := Open("cmforms_heckepols.txt","w");
    s := "";
    for x in hpols do
        s := s cat IntegerToString(x[1]) cat ":" cat IntegerToString(x[2]) cat ":[";
        for i := 1 to #x[3]-1 do
            s := s cat IntegerToString(x[3][i]) cat ",";
        end for;
        s := s cat IntegerToString(x[3][#x[3]]) cat "]\n";
    end for;
    if #s ne 0 then
        Write("cmforms_heckepols.txt",s);
    end if;
    return true;
end function;

function heckepols(grosschars, primes_bound);
    // we assume that the grossen characters are primitive, i.e., their conductor is equal to the modulus
    F<zeta3> := CyclotomicField(3);
    levs := Sort(SetToSequence({3*Norm(Modulus(grosschar)) : grosschar in grosschars}));
    grosschars_partitioned := [[grosschar : grosschar in grosschars | 3*Norm(Modulus(grosschar)) eq N] : N in levs];
    printf "There are \n%o\n Grossencharacters of levels \n%o\n respectively\n", [#x : x in grosschars_partitioned], levs;
    heckepolslist := [];
    primes := [p : p in PrimesUpTo(primes_bound) | p mod 3 eq 1];
    for i := 1 to #levs do
        N := levs[i];
        X := grosschars_partitioned[i];
// Replacing the following rounding business and the calculation of EulerFactor over complex numbers, because
// it gives non-rational results for large N. For example, N = 1728 and p = 19.
//        heckepolslist := heckepolslist cat [<N,p,Reverse([Round(c) : c in Coefficients(&*[EulerFactor(X[j],p) : j in [1..#X]])])> : p in primes];
// The following is precise.
        for p in primes do
            roots := [**];
            pabove := PrimeIdealsOverPrime(F,p);
            for j := 1 to #X do
                a1,b1,c1 := RawEval(pabove[1],X[j]);
                a2,b2,c2 := RawEval(pabove[2],X[j]);
                roots := roots cat [* a1*b1*c1, a2*b2*c2 *];
            end for;
            minpols := {ChangeRing(MinimalPolynomial(r),Integers()) : r in roots}; // Not keeping track of repeated factors. So our hecke polynomials for different primes will have different degrees.
            Append(~heckepolslist,<N,p,Coefficients(&*minpols)>);
        end for;
        printf "Done with level %o\n", N;
    end for;
    return heckepolslist;
end function;


function update_CMforms(level : primes_bound := 500);
//    if level mod 3 ne 0 then return []; end if;
    if level mod 27 ne 0 then return []; end if;
    existing_hpols := read_heckepolsdb();
    existing_levels := Sort(SetToSequence({x[1] : x in existing_hpols}));
    relevant_existing_hpols := [x : x in existing_hpols | level mod x[1] eq 0];

    F<zeta3> := CyclotomicField(3);
    zeta6 := zeta3+1;
    OF := RingOfIntegers(F);

    leveldiv3 := ExactQuotient(level,3);
    Facs_leveldiv3 := Factorisation(leveldiv3);
    max_cond := 1*OF;
    for fac in Facs_leveldiv3 do
        if fac[1] eq 2 then
            max_cond := max_cond*(2^(Minimum(fac[2] div 2,4))*OF);
        elif fac[1] eq 3 then
            p3 := Factorisation(3*OF)[1,1];
            max_cond := max_cond*(p3^(Minimum(fac[2]-2,4)));
//            max_cond := max_cond*(p3^(Minimum(Maximum(fac[2]-2,0),4)));  // we have already divided level by 3.
        elif fac[1] mod 3 eq 2 then
            max_cond := max_cond*(fac[1]^(Minimum(fac[2] div 2,1))*OF);
        else
            max_cond := max_cond*(fac[1]^(Minimum(fac[2] div 2,1))*OF);
        end if;
    end for;
    extrasplitfacs := [fac[1] : fac in Facs_leveldiv3 | fac[1] mod 3 eq 1 and fac[2] eq 1];

    normfrakm := Norm(max_cond)*(&*(extrasplitfacs cat [1]));
    remaininglevels := Sort(SetToSequence(Set([27*d : d in Divisors(normfrakm) | &and[Valuation(d,pd) mod 2 eq 0 : pd in PrimeFactors(d) | pd mod 3 eq 2]]) diff Set(existing_levels)));
    printf "The database already has data of hecke polynomials for CM forms of levels \n%o\n", Sort(SetToSequence({x[1] : x in relevant_existing_hpols}));
    printf "Now computing this data for the remaining possible levels out of\n%o\n", remaininglevels;
    if remaininglevels eq [] then
        return relevant_existing_hpols;
    end if;

    newlevel := LCM(remaininglevels);
    if newlevel lt level then
        printf "New level is %o\n", newlevel;
        newpols := update_CMforms(newlevel : primes_bound := primes_bound);
        newpols := [x : x in newpols | not x[1] in existing_levels];
        return relevant_existing_hpols cat newpols;
    end if;

    DG := DirichletGroup(3*OF);
    assert #DG eq 6;
    EDG := Elements(DG);
    _ := exists(chi){x : x in EDG | x(zeta6) eq zeta6};

    if extrasplitfacs eq [] then
        printf "Working with the maximum modulus\n%o\n", max_cond;
        G := HeckeCharacterGroup(max_cond);
        printf "The Hecke Character Group of this modulus has %o elements\n", #G;
        good_grosschars := [];
//        cond_norms_comparison := {};
        for x in Elements(G) do
//            norm_cond_x := Norm(Conductor(x));
            grosschar := Grossencharacter(x,Extend(chi,Modulus(x)),[[1,0]]);
//            norm_cond_grosschar := Norm(Conductor(grosschar));
//            Include(~cond_norms_comparison,norm_cond_x/norm_cond_grosschar);
            grosschar := AssociatedPrimitiveGrossencharacter(grosschar);
            if 3*Norm(Modulus(grosschar)) in existing_levels then
                continue;
            end if;
            Append(~good_grosschars,grosschar);
        end for;
        printf "Grossencharacters computed. Found %o of them.\n", #good_grosschars;
//        return good_grosschars, cond_norms_comparison;
//        return good_grosschars;
        hpols := heckepols(good_grosschars,primes_bound);
        boo := write_heckepolsdb(hpols);
        return hpols cat relevant_existing_hpols;
    end if;

    good_grosschars := [];
//    cond_norms_comparison := {};
    V := CartesianPower([1,2],#extrasplitfacs);
    splitprimes := [PrimeIdealsOverPrime(F,p) : p in extrasplitfacs];
    count := 0;
    for v in V do
        count := count+1;
        frakm := max_cond*(&*([splitprimes[i,v[i]] : i in [1..#extrasplitfacs]]));
        printf "Working with the %oth of %o possible modulus\n", count, 2^#extrasplitfacs;
        G := HeckeCharacterGroup(frakm);
        printf "The Hecke Character Group of this modulus has %o elements\n", #G;
        for x in Elements(G) do
//            norm_cond_x := Norm(Conductor(x));
            grosschar := Grossencharacter(x,Extend(chi,Modulus(x)),[[1,0]]);
//            norm_cond_grosschar := Norm(Conductor(grosschar));
//            Include(~cond_norms_comparison,norm_cond_x/norm_cond_grosschar);
            grosschar := AssociatedPrimitiveGrossencharacter(grosschar);
            if 3*Norm(Modulus(grosschar)) in existing_levels then
                continue;
            end if;
            if not grosschar in good_grosschars then
                Append(~good_grosschars,grosschar);
            end if;
        end for;
        printf "Found %o Grossencharacters in total.\n", #good_grosschars;
    end for;
//    return good_grosschars, cond_norms_comparison;
//    return good_grosschars;
    hpols := heckepols(good_grosschars,primes_bound);
    boo := write_heckepolsdb(hpols);
    return hpols cat relevant_existing_hpols;
end function;


function update_CMforms1(radical_level : primes_bound := 500);
    existing_hpols := read_heckepolsdb();
    existing_levels := Sort(SetToSequence({x[1] : x in existing_hpols}));
    relevant_existing_hpols := [x : x in existing_hpols | radical_level mod Squarefree(x[1]) eq 0];

    radical_level_ge5 := radical_level/(2^Valuation(radical_level,2)*3^Valuation(radical_level,3));
    normfrakm := 2^8*3^4*radical_level_ge5^2;
    remaininglevels := Sort(SetToSequence({27*d : d in Divisors(normfrakm) | &and[Valuation(d,pd) mod 2 eq 0 : pd in PrimeFactors(d) | pd mod 3 eq 2]} diff Set(existing_levels)));
    printf "The database already has data of hecke polynomials for CM forms of levels \n%o\n", Sort(SetToSequence({x[1] : x in relevant_existing_hpols}));
    printf "Now computing this data for the remaining possible levels out of\n%o\n", remaininglevels;

    if remaininglevels eq [] then
        return relevant_existing_hpols;
    end if;

    newlevel := LCM(remaininglevels);
    if newlevel lt level then
        printf "New level is %o\n", newlevel;
        newpols := update_CMforms1(newlevel : primes_bound := primes_bound);
        newpols := [x : x in newpols | not x[1] in existing_levels];
        return relevant_existing_hpols cat newpols;
    end if;

    F<zeta3> := CyclotomicField(3);
    zeta6 := zeta3+1;
    OF := RingOfIntegers(F);
    DG := DirichletGroup(3*OF);
    assert #DG eq 6;
    EDG := Elements(DG);
    _ := exists(chi){x : x in EDG | x(zeta6) eq zeta6};

    max_cond := 2^4*3^2*radical_level_ge5*OF;
    printf "Working with the maximum modulus\n%o\n", max_cond;
    G := HeckeCharacterGroup(max_cond);
    printf "The Hecke Character Group of this modulus has %o elements\n", #G;
    good_grosschars := [];
    for x in Elements(G) do
        grosschar := Grossencharacter(x,Extend(chi,Modulus(x)),[[1,0]]);
        grosschar := AssociatedPrimitiveGrossencharacter(grosschar);
        if 3*Norm(Modulus(grosschar)) in existing_levels then
            continue;
        end if;
        Append(~good_grosschars,grosschar);
    end for;
    printf "Grossencharacters computed. Found %o of them.\n", #good_grosschars;
    hpols := heckepols(good_grosschars,primes_bound);
    boo := write_heckepolsdb(hpols);
    return hpols cat relevant_existing_hpols;
end function;

