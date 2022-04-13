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

function allvalidcharpols(sig);
    return [i : i in [1..#sig] | sig[i] ne 0];
end function;

function distinguish(f, poss);
    return poss;
end function;

Attach("GSp.m");
G := GSp(6,7);
load "all_data_7.txt";

function find_image(f, possibs, possible_charpolstats : primesstart := 3, primesend := 10000, list_of_counts := [0/1 : i in [1..#charpols]]);
    Z := Integers();
    Z7 := Integers(7);
    P7<T> := PolynomialRing(Z7);
    Lpols := getLpols(f, primesstart, primesend);
    charpolsshowingup := [];
    skipfrobdistcalc := false;
    for i := 1 to #Lpols do
        if Lpols[i,1] mod 7 ne 1 then
            continue;
        end if;
	    charpol := P7 ! Reverse(Lpols[i,2]);
	    iii := Index(charpols,charpol);
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


Z := Integers();
P<x> := PolynomialRing(Z);
f := x^4+x+1;
for i := 1 to 6 do
    mod7img := find_image(f,subs_with_charpolstat_GLconjinfo[i],all_charpolstats[i]);
end for;

