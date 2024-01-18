AttachSpec("spec");

cba := [StringToInteger(x) : x in Split(input_string,"[,] ")];
P<x> := PolynomialRing(Integers());
f := P ! (cba cat [0, 1]);
// f := x^4 + a x^2 + b x + c

/*
ff := suppressed_integer_quartic(f);
if Coefficient(ff,1) eq 0 and Coefficient(ff,3) eq 0 then
    exit;
end if;
if Coefficient(ff,0) eq 0 and Coefficient(ff,2) eq 0 and Coefficient(ff,3) eq 0 then
    exit;
end if;
*/

if Discriminant(f) eq 0 then
    exit;
end if;

/*
badprimes := PrimeFactors(RadCond(f));
if #badprimes gt 5 then
    error_for := <cba cat [0,1], badprimes>;
    PrintFile("error_too_many_badprimes.txt", Sprint(error_for));
    exit;
end if;
*/

SetColumns(0);
try
    badprimes, nonsurjprimes := possibly_nonsurj_primes(f);
    result := <cba cat [0,1], badprimes, <nonsurjprimes[2], nonsurjprimes[3], nonsurjprimes[4]>>;
    PrintFile("nonsurjprimes_results_boxsearch2.txt", Sprint(result) cat ",");
catch e;
    badprimes := PrimeFactors(RadCond(f));
    error_for := <cba cat [0,1], badprimes>;
    PrintFile("error_in_possiblynonsurjprimes_boxsearch2.txt", Sprint(error_for));
//    PrintFile("error_in_possiblynonsurjprimes_boxsearch2.txt", e);
end try;

exit;

// cat cba_box.txt | time parallel -j 128 magma input_string:={} parallel_run_boxsearch.m
// ~4 weeks with 64 parallel jobs on lovelace mid Aug to Sep 17.
// Command exited with non-zero status 94
// 135791497.65user 1335972.60system 650:07:44elapsed 5858%CPU (0avgtext+0avgdata 374136048maxresident)k
// 68552inputs+1016202768outputs (222major+474336916565minor)pagefaults 0swaps



/*
for c := -100 to 100 do
    for b := 1 to 100 do
        for a := -100 to 100 do
            if a eq 0 and c eq 0 then continue; end if;
            PrintFile("cba_box.txt", Sprint([c,b,a]));
        end for;
    end for;
end for;
*/


/*
SetColumns(0);
fil := Open("nonsurjprimes_results_boxsearch_unclean.txt","r");
s := Gets(fil);
while not IsEof(s) do
    if s[#s-2..#s] ne ">>," then
        s := s cat Gets(fil);
        assert s[#s-2..#s] eq ">>,";
    end if;
    PrintFile("nonsurjprimes_results_boxsearch.txt",s);
    s := Gets(fil);
end while;

fil := Open("nonsurjprimes_results_boxsearch.txt","r");
s := Gets(fil);
curves := [];
badprimes := [];
results := [];
results_asis := [];
while not IsEof(s) do
    s_split := Split(s,"<>");
    s_split1 := Split(s_split[1],"[,] ");
    s_split2 := Split(s_split[2], "<[,]> ");
    coeffs := [StringToInteger(x) : x in s_split1[1..5]];
    badps := [StringToInteger(x) : x in s_split1[6..#s_split1]];
    nonsurjprimes := Sort(SetToSequence({StringToInteger(x) : x in s_split2}));
    Append(~curves,coeffs);
    Append(~badprimes,badps);
    Append(~results,nonsurjprimes);
    Append(~results_asis,s);
    s := Gets(fil);
end while;

{Maximum(x) : x in results};
Set(results);

{
[ 2, 3 ],
[ 2, 3, 7 ]
}

for i := 1 to #results do
    if results[i] ne [2,3] then
        print results_asis[i];
    end if;
end for;

<[ -3, 8, 30, 0, 1 ], [ 2, 3 ], <[ 2, 3, 7 ], [], []>>,
<[ 13, 8, 10, 0, 1 ], [ 2, 3, 5 ], <[ 2, 3, 7 ], [], [ 2 ]>>,
*/

