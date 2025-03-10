load "Lpolys.m";

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
    System(GetEnv("HOME") cat "/hwlpoly y^3=" cat fstr cat " " cat pstr cat " 1 > CartManmat_for_p.txt");
    fil := Open("CartManmat_for_p.txt", "r");
    C := Coefficients(f)[1..3];
    Lpol := liftLpolys(fil,C);
*/
    C := Coefficients(f)[1..3];
    cartmanmat := Pipe(GetEnv("HOME") cat "/hwlpoly y^3=" cat fstr cat " " cat pstr cat " 1","");
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


function charpol_dist(H,G : CCs := [], charpols := []);
    if charpols ne [] then
        if H eq G then
            return [charpols[i,2]/#G : i in [1..#charpols]];
        end if;
        newdist := [0 : j in [1..#charpols]];
        CCH := ConjugacyClasses(H);
        charpolys := [x[1] : x in charpols];
        for x in CCH do
            n := Index(charpolys,CharacteristicPolynomial(x[3]));
            newdist[n] +:= x[2];
        end for;
        newdist := [x/#H : x in newdist];
        return newdist;
    end if;

    if CCs eq [] then
        CCs := ConjugacyClasses(G);
    end if;

    charpols := [];
    charpolnumbers := [];
    for i := 1 to #CCs do
        x := CCs[i,3];
        f := CharacteristicPolynomial(x);
        if not f in charpols then
            Append(~charpols,f);
            Append(~charpolnumbers,CCs[i,2]);
        else
            n := Index(charpols,f);
            charpolnumbers[n] +:= CCs[i,2];
        end if;
    end for;

    if H eq G then
        return [x/#G : x in charpolnumbers];
    end if;
/*    
    if #H gt 2000 then
        return [#(Set(H) meet Orbit(G,CCs[i][3]))/#H : i in [1..#CCs]];
    end if;
*/
    newdist := [0 : j in [1..#charpols]];
    CCH := ConjugacyClasses(H);
    for x in CCH do
        n := Index(charpols,CharacteristicPolynomial(x[3]));
        newdist[n] +:= x[2];
    end for;
    newdist := [x/#H : x in newdist];
    return newdist;
end function;

function allvalidcharpols(sig);
    return [i : i in [1..#sig] | sig[i] ne 0];
end function;

function distinguish(f, poss);
    return poss;
end function;

Attach("GSp.m");
// G := GSp(6,7);
G := CSp(6,7);
load "new_data_7.txt";

function find_image(f, radical_cond, possibs, possible_charpolstats : primesstart := 3, primesend := 10000, list_of_counts := [0/1 : i in [1..#charpols]]);
    f := suppressed_integer_quartic(f);
    if radical_cond eq 1 then radical_cond := RadCond(f); end if;
    Z := Integers();
    Z7 := Integers(7);
    P7<T> := PolynomialRing(Z7);
    charpolys := [x[1] : x in charpols];
    charpolsshowingup := [];
    skipfrobdistcalc := false;
    for N := primesstart to primesend do
        p := NthPrime(N);
        if p mod 3 ne 1 or p mod 7 ne 1 or radical_cond mod p eq 0 then continue; end if;
        Lpolatp := getLpol(f,radical_cond,p);
        if Type(Lpolatp) eq MonStgElt then continue; end if;
	    charpol := P7 ! Lpolatp;
	    iii := Index(charpolys,charpol);
//        print iii;
	    list_of_counts[iii] := list_of_counts[iii]+1;

        if not iii in charpolsshowingup then
            Append(~charpolsshowingup,iii);
            remainingones := [j : j in [1..#possibs] | possible_charpolstats[j,iii] ne 0];
            possibs := possibs[remainingones];
            possible_charpolstats := possible_charpolstats[remainingones];
/*
            if #possibs eq 1 then
                skipfrobdistcalc := true;
                possibilities := possibs;
                break;
            end if;
*/
            if #possibs eq 0 then
                skipfrobdistcalc := true;
                possibilities := [];
                break;
            end if;
	    end if;
    end for;
//    print list_of_counts;

    if not skipfrobdistcalc then
        totalprimes := &+list_of_counts;
//        print totalprimes;
        freqstat := [x/totalprimes : x in list_of_counts];

        V := VectorSpace(RealField(),#charpols);
        localmindists := [];
        for i := 1 to #possible_charpolstats do
            mindist := 1;
            for j := 1 to #possible_charpolstats do
                if j ne i then
                    mindist := Minimum(mindist,Norm(V ! possible_charpolstats[j] - V ! possible_charpolstats[i]));
                end if;
            end for;
            Append(~localmindists,mindist/4);
        end for;
//        print localmindists;

        possibilities := [];
        errors := [];
        for i := 1 to #possible_charpolstats do
            charpolstatH := possible_charpolstats[i];
            err := V ! charpolstatH - V ! freqstat;
//            print i, Norm(err), localmindists[i];
            if Norm(err) lt localmindists[i] then
                Append(~possibilities,possibs[i]);
                Append(~errors,Norm(err));
            end if;
        end for;

//        print #possibilities, #errors;
//        print errors;
    end if;
    if #possibilities eq 0 then
        print "No subgroups found";
        return [];
    end if;
    if #possibilities ne 1 then
        print "More primes need to be sampled. Sampling more primes...";
        newprimesstart := primesend + 1;
        newprimesend := primesend + 1000;
        return find_image(f, radical_cond, possibs, possible_charpolstats : primesstart := newprimesstart, primesend := newprimesend, list_of_counts := list_of_counts);
    elif #possibilities[1] gt 1 then
//        print "Sampled data about frobenius cannot distinguish the image upto GL conjugacy uniquely.";
        printf "The image could be one of the following %o subgroups:\n", #possibilities[1];
    //	print possibilities[1];
    //	print "Looking at global data to distinguish between the", #possibilities[1], "possible images...";
        return distinguish(f,possibilities[1]);
    else
        return possibilities[1][1];
    end if;
end function;

function lifttoQzeta3(f, radical_cond, K, H, G, CCs, charpols, l : possibs := [], possible_charpolstats := [], primesstart := 3, primesend := 10000, list_of_counts := [0/1 : i in [1..#charpols]]);
    f := suppressed_integer_quartic(f);
    if radical_cond eq 1 then radical_cond := RadCond(f); end if;
    charpolys := [x[1] : x in charpols];
    Fl := GF(l);
    Ul, il := UnitGroup(Fl);

    if possibs eq [] then
        zeromat := ZeroMatrix(Fl,3);
        idmat := IdentityMatrix(Fl,3);
        mat := BlockMatrix(2,2,[il(Ul.1)*idmat, zeromat, zeromat, idmat]);
        Hbig := sub<G|H, mat>;
        NK := Normalizer(Hbig,K);
        if #NK eq (l-1)*#K then
            return NK;
        end if;
        subs := Complements(NK,NK meet H,K);

        charpolstats := [charpol_dist(K,G : CCs := CCs, charpols := charpols) : K in subs];

        all_charpolstats := [];
        subs_with_charpolstat := [];
        for i := 1 to #charpolstats do
            if not charpolstats[i] in all_charpolstats then
                Append(~all_charpolstats,charpolstats[i]);
                Append(~subs_with_charpolstat,[subs[i]]);
            else
                n := Index(all_charpolstats,charpolstats[i]);
                Append(~subs_with_charpolstat[n],subs[i]);
            end if;
        end for;

        subs_with_charpolstat_GLconjinfo := [];
        for i := 1 to #all_charpolstats do
            temp := [];
            tempsubs := subs_with_charpolstat[i];
            for k := 1 to #tempsubs do
                KK := tempsubs[k];
                bool := true;
                for ll := 1 to #temp do
                    if IsConjugate(GL(6,Fl),KK,temp[ll,1]) then
                        temp[ll] := temp[ll] cat [KK];
                        bool := false;
                        break;
                    end if;
                end for;
                if bool then
                    Append(~temp,[KK]);
                end if;
            end for;
            Append(~subs_with_charpolstat_GLconjinfo,temp);
        end for;
        possibs := subs_with_charpolstat_GLconjinfo;
        possible_charpolstats := all_charpolstats;
    end if;


    f := suppressed_integer_quartic(f);
    if radical_cond eq 1 then radical_cond := RadCond(f); end if;
    Z := Integers();
    P7<T> := PolynomialRing(Fl);
    charpolsshowingup := [];
    skipcharpoldistcalc := false;

    for N := primesstart to primesend do
        p := NthPrime(N);
        if p mod 3 ne 1 or p mod 7 eq 1 or radical_cond mod p eq 0 then continue; end if;
        Lpolatp := getLpol(f,radical_cond,p);
        if Type(Lpolatp) eq MonStgElt then continue; end if;
	    charpol := P7 ! Lpolatp;
	    iii := Index(charpolys,charpol);
//        print iii;
	    list_of_counts[iii] := list_of_counts[iii]+1;

        if not iii in charpolsshowingup then
            Append(~charpolsshowingup,iii);
            remainingones := [j : j in [1..#possibs] | possible_charpolstats[j,iii] ne 0];
            possibs := possibs[remainingones];
            possible_charpolstats := possible_charpolstats[remainingones];
/*
            if #possibs eq 1 then
                skipcharpoldistcalc := true;
                possibilities := possibs;
                break;
            end if;
*/
            if #possibs eq 0 then
                skipcharpoldistcalc := true;
                possibilities := [];
                break;
            end if;
	    end if;
    end for;
//    print list_of_counts;

    if not skipcharpoldistcalc then
        totalprimes := &+list_of_counts;
//        print totalprimes;
        freqstat := [x/totalprimes : x in list_of_counts];

        V := VectorSpace(RealField(),#charpols);
        localmindists := [];
        for i := 1 to #possible_charpolstats do
            mindist := 1;
            for j := 1 to #possible_charpolstats do
                if j ne i then
                    mindist := Minimum(mindist,Norm(V ! possible_charpolstats[j] - V ! possible_charpolstats[i]));
                end if;
            end for;
            Append(~localmindists,mindist/4);
        end for;
//        print localmindists;

        possibilities := [];
        errors := [];
        for i := 1 to #possible_charpolstats do
            charpolstatH := possible_charpolstats[i];
            err := V ! charpolstatH - V ! freqstat;
//            print i, Norm(err), localmindists[i];
            if Norm(err) lt localmindists[i] then
                Append(~possibilities,possibs[i]);
                Append(~errors,Norm(err));
            end if;
        end for;

//        print #possibilities, #errors;
//        print errors;
    end if;
    if #possibilities eq 0 then
        print "No subgroups found";
        return [];
    end if;
    if #possibilities ne 1 then
        print "More primes need to be sampled. Sampling more primes...";
        newprimesstart := primesend + 1;
        newprimesend := primesend + 1000;
        return lifttoQzeta3(f, K, H, G, CCs, charpols, l : possibs := possibs, possible_charpolstats := possible_charpolstats, primesstart := newprimesstart, primesend := newprimesend, list_of_counts := list_of_counts);
    elif #possibilities[1] gt 1 then
//        print "Sampled data about frobenius charpols cannot distinguish the image upto GL conjugacy uniquely.";
        printf "The image could be one of the following %o subgroups:\n", #possibilities[1];
    //	print possibilities[1];
    //	print "Looking at global data to distinguish between the", #possibilities[1], "possible images...";
        return distinguish(K,possibilities[1]);
    else
        return possibilities[1][1];
    end if;
end function;

function mod_ell_image(f,ell : radical_cond := 1, type := "all");
    // i = 4 for reducible, 1 for field-extension, 3 for imprimitive, 2 for exceptional

    f := suppressed_integer_quartic(f);
    if radical_cond eq 1 then radical_cond := RadCond(f); end if;

    if type eq "reducible" then
        return find_image(f,radical_cond,subs_with_charpolstat_GLconjinfo[4],all_charpolstats[4]);
    elif type eq "field_extension" then
        return find_image(f,radical_cond,subs_with_charpolstat_GLconjinfo[1],all_charpolstats[1]);
    elif type eq "imprimitive" then
        return find_image(f,radical_cond,subs_with_charpolstat_GLconjinfo[3],all_charpolstats[3]);
    elif type eq "exceptional" then
        return find_image(f,radical_cond,subs_with_charpolstat_GLconjinfo[2],all_charpolstats[2]);
    end if;
    for i := 1 to 4 do
        image := find_image(f,radical_cond,subs_with_charpolstat_GLconjinfo[i],all_charpolstats[i]);
        if image ne [] then
            return image;
        end if;
    end for;
end function;

Z := Integers();
P<x> := PolynomialRing(Z);


