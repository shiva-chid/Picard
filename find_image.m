load "Lpolys.m";

function getLpols(f, primesstart, primesend);
    P<x> := Parent(f);
    disc := Discriminant(f);
    disc := Numerator(disc)*Denominator(disc);
    firstrun := true;
    for N := primesstart to primesend do
        p := NthPrime(N);
        if disc mod p ne 0 then
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
            charpolnumbers[n] := charpolnumbers[n]+CCs[i,2];
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
/*
G := GSp(6,7);
*/
G := CSp(6,7);
load "new_data_7.txt";

function find_image(f, possibs, possible_charpolstats : primesstart := 3, primesend := 10000, list_of_counts := [0/1 : i in [1..#charpols]]);
    Z := Integers();
    Z7 := Integers(7);
    P7<T> := PolynomialRing(Z7);
    Lpols := getLpols(f, primesstart, primesend);
    charpolys := [x[1] : x in charpols];
    charpolsshowingup := [];
    skipfrobdistcalc := false;
    for i := 1 to #Lpols do
        if Lpols[i,1] mod 3 ne 1 or Lpols[i,1] mod 7 ne 1 then
            continue;
        end if;
	    charpol := P7 ! Reverse(Lpols[i,2]);
	    iii := Index(charpolys,charpol);
	    list_of_counts[iii] := list_of_counts[iii]+1;
        if not iii in charpolsshowingup then
//		print #possibs, #possible_charpolstats;
            Append(~charpolsshowingup,iii);
            remainingones := [j : j in [1..#possibs] | possible_charpolstats[j,iii] ne 0];
            possibs := possibs[remainingones];
            possible_charpolstats := possible_charpolstats[remainingones];
            if #possibs eq 1 then
                skipfrobdistcalc := true;
                possibilities := possibs;
                break;
            elif #possibs eq 0 then
                skipfrobdistcalc := true;
                possibilities := [];
                break;
            end if;
	    end if;

/*
	if N mod 100 eq 0 then
	    print N;
	end if;
*/
    end for;

    if not skipfrobdistcalc then
        totalprimes := &+list_of_counts;
        print totalprimes;
        freqstat := [list_of_counts[i]/totalprimes : i in [1..#list_of_counts]];

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
        print localmindists;

        possibilities := [];
        errors := [];
        for i := 1 to #possible_charpolstats do
            charpolstatH := possible_charpolstats[i];
            err := V ! charpolstatH - V ! freqstat;
            print i, Norm(err), localmindists[i];
            if Norm(err) lt localmindists[i] then
                Append(~possibilities,possibs[i]);
                Append(~errors,Norm(err));
            end if;
        end for;

        print #possibilities, #errors;
        print errors;
    end if;
    if #possibilities eq 0 then
        print "No subgroups found";
        return [];
    end if;
    if #possibilities ne 1 then
        print "More primes need to be sampled. Sampling more primes...";
        newprimesstart := primesend + 1;
        newprimesend := primesend + 1000;
        return find_image(f, possibs, possible_charpolstats : primesstart := newprimesstart, primesend := newprimesend, list_of_counts := list_of_counts);
    elif #possibilities[1] gt 1 then
        print "Sampled data about frobenius cannot distinguish the image upto GL conjugacy uniquely.";
        print "The image could be one of the following subgroups:";
    //	print possibilities[1];
    //	print "Looking at global data to distinguish between the", #possibilities[1], "possible images...";
        return distinguish(f,possibilities[1]);
    else
        return possibilities[1][1];
    end if;
end function;

function lifttoQzeta3(f, K, H, G, CCs, charpols, l : possibs := [], possible_charpolstats := [], primesstart := 3, primesend := 10000, list_of_counts := [0/1 : i in [1..#charpols]]);
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
                    if IsConjugate(GL(6,Fl),KK,temp[ll,1]`subgroup) then
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



    Z := Integers();
    P7<T> := PolynomialRing(Fl);
    Lpols := getLpols(f, primesstart, primesend);
    charpolsshowingup := [];
    skipcharpoldistcalc := false;
    for i := 1 to #Lpols do
        if Lpols[i,1] mod 3 ne 1 or Lpols[i,1] mod l eq 1 then
            continue;
        end if;
	    charpol := P7 ! Reverse(Lpols[i,2]);
	    iii := Index(charpolys,charpol);
	    list_of_counts[iii] := list_of_counts[iii]+1;
        if not iii in charpolsshowingup then
//		print #possibs, #possible_charpolstats;
            Append(~charpolsshowingup,iii);
            remainingones := [j : j in [1..#possibs] | possible_charpolstats[j,iii] ne 0];
            possibs := possibs[remainingones];
            possible_charpolstats := possible_charpolstats[remainingones];
            if #possibs eq 1 then
                skipcharpoldistcalc := true;
                possibilities := possibs;
                break;
            elif #possibs eq 0 then
                skipcharpoldistcalc := true;
                possibilities := [];
                break;
            end if;
	    end if;
/*
	if N mod 100 eq 0 then
	    print N;
	end if;
*/
    end for;

    if not skipcharpoldistcalc then
        totalprimes := &+list_of_counts;
        print totalprimes;
        freqstat := [list_of_counts[i]/totalprimes : i in [1..#list_of_counts]];

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
        print localmindists;

        possibilities := [];
        errors := [];
        for i := 1 to #possible_charpolstats do
            charpolstatH := possible_charpolstats[i];
            err := V ! charpolstatH - V ! freqstat;
            print i, Norm(err), localmindists[i];
            if Norm(err) lt localmindists[i] then
                Append(~possibilities,possibs[i]);
                Append(~errors,Norm(err));
            end if;
        end for;

        print #possibilities, #errors;
        print errors;
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
        print "Sampled data about frobenius charpols cannot distinguish the image upto GL conjugacy uniquely.";
        print "The image could be one of the following subgroups:";
    //	print possibilities[1];
    //	print "Looking at global data to distinguish between the", #possibilities[1], "possible images...";
        return distinguish(K,possibilities[1]);
    else
        return possibilities[1][1];
    end if;
end function;

Z := Integers();
P<x> := PolynomialRing(Z);
f := x^4+x^2+1;
for i := 1 to 4 do
    mod7img_overQzeta21 := find_image(f,subs_with_charpolstat_GLconjinfo[i],all_charpolstats[i]);
    if mod7img_overQzeta21 ne [] then
        if #mod7img_overQzeta21 eq 1 then
            K := mod7img_overQzeta21[1]`subgroup;
            if BaseRing(K) eq Integers(7) then
                K := ChangeRing(K,GF(7));
            end if;
            mod7img_overQzeta3 := lifttoQzeta3(f,K,H,G,CCs,charpols,7);
            print mod7img_overQzeta3;
        end if;
    end if;
end for;

