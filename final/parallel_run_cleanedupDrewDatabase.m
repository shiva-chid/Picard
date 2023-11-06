AttachSpec("spec");

input_split := Split(input_string,":");
cond := StringToInteger(input_split[1]);
P<x> := PolynomialRing(Integers());
f := eval input_split[2][2..#input_split[2]-1];




ff := suppressed_integer_quartic(f);
if Coefficient(ff,1) eq 0 and Coefficient(ff,3) eq 0 then
    exit;
end if;
if Coefficient(ff,0) eq 0 and Coefficient(ff,2) eq 0 and Coefficient(ff,3) eq 0 then
    exit;
end if;

/*
function endomorphism_algebra(f);
    P2<x,y> := PolynomialRing(Rationals(),2);
    hom_defpol := Homogenize(y^3-Evaluate(f,x));
    PP2<x,y,z> := ProjectiveSpace(Parent(hom_defpol));
    C := Curve(PP2,hom_defpol);
    End_alg_out1, End_alg_out2, End_alg_out3 := HeuristicEndomorphismAlgebra(C : Geometric := true);
    return End_alg_out2;
end function;
if Dimension(endomorphism_algebra(f)) ne 2 then
    exit;
end if;
*/

try
    badprimes, nonsurjprimes := possibly_nonsurj_primes(f);
    assert cond eq &*[p^Valuation(cond,p) : p in badprimes];
    result := <Coefficients(f), <nonsurjprimes[2], nonsurjprimes[3], nonsurjprimes[4]>>;
    PrintFile("nonsurjprimes_results_cleanedupDrewDatabase2.txt", Sprint(result) cat ",");
catch e;
//    badprimes := PrimeFactors(RadCond(f));
    error_for := <Coefficients(f)>;
    PrintFile("error_in_possibly_nonsurj_primes_cleanedupDrewDatabase2.txt", error_for);
end try;

exit;

// cat pic_7smooth_cleanup2.txt | time parallel -j 128 magma input_string:={} parallel_run_cleanedupDrewDatabase.m


/*
fil := Open("nonsurjprimes_results_cleanedupDrewDatabase.txt","r");
s := Gets(fil);
curves := [];
results := [];
results_asis := [];
while not IsEof(s) do
    s_split := Split(s,"<>");
    coeffs := [StringToInteger(x) : x in Split(s_split[1],"[], ")];
    nonsurjprimes := [Sort(SetToSequence({StringToInteger(x) : x in Split(y,"], ")})) : y in Split(s_split[2],"[")];
    Append(~curves,coeffs);
    Append(~results,nonsurjprimes);
    Append(~results_asis,s);
    s := Gets(fil);
end while;

for x in Set(results) do
    n := Multiplicity(results,x);
    printf "%o : Multiplicity %o\n", "[" cat &cat[Sprint(y) : y in x] cat "]", n;
end for;

[[ 2, 3, 5 ][][ 2 ]] : Multiplicity 23
[[ 2, 3, 5 ][][]] : Multiplicity 131
[[ 2, 3, 5 ][][ 5 ]] : Multiplicity 115
[[ 2, 3, 5 ][][ 2, 5 ]] : Multiplicity 10
[[ 2, 3 ][ 2 ][ 2 ]] : Multiplicity 53816
[[ 2, 3, 7 ][][]] : Multiplicity 259
[[ 2, 3, 7 ][][ 7 ]] : Multiplicity 32
[[ 2, 3, 7 ][][ 2 ]] : Multiplicity 90
[[ 2, 3, 13 ][][]] : Multiplicity 5
[[ 2, 3 ][][]] : Multiplicity 1889104
[[ 2, 3 ][][ 2 ]] : Multiplicity 469588

inds := [i : i in [1..#results] | results[i,3] ne [] and results[i,3] ne [2]]; #inds;
// 157
*/

/*
fil := Open("nonsurjprimes_results_cleanedupDrewDatabase.txt","r");
s := Gets(fil);
curves := [];
results := [];
results_asis := [];
while not IsEof(s) do
    s_split := Split(s,"<[,]> ");
    coeffs := [StringToInteger(x) : x in s_split[1..5]];
    nonsurjprimes := Sort(SetToSequence({StringToInteger(x) : x in s_split[6..#s_split]}));
    Append(~curves,coeffs);
    Append(~results,nonsurjprimes);
    Append(~results_asis,s);
    s := Gets(fil);
end while;

{Maximum(x) : x in results};
// { 3, 5, 7, 13 }
setresults := Set(results); setresults;
for x in setresults do
    print x, Multiplicity(results,x);
end for;

[ 2, 3 ]
2412508
[ 2, 3, 13 ]
5
[ 2, 3, 7 ]
381
[ 2, 3, 5 ]
279

for i := 1 to #results do
    if not Set(results[i]) subset {2,3,5,7}  then
        print results_asis[i];
    end if;
end for;

<[ -142, -387, -147, 338, 243 ], <[ 2, 3, 13 ], [], []>>,
<[ -284, -774, -294, 676, 486 ], <[ 2, 3, 13 ], [], []>>,
<[ -71, -387, -294, 1352, 1944 ], <[ 2, 3, 13 ], [], []>>,
<[ -426, -1161, -441, 1014, 729 ], <[ 2, 3, 13 ], [], []>>,
<[ -710, -1935, -735, 1690, 1215 ], <[ 2, 3, 13 ], [], []>>,

for i := 1 to #results do
    if results[i] ne [2,3] then
        print results_asis[i];
    end if;
end for;

setresultsasis7 := {};
count := 0;
for i := 1 to #results do
    if results[i] eq [2,3,7] then
        count +:= 1;
        print results_asis[i];
        s := Split(results_asis[i],"<>")[2];
        Include(~setresultsasis7,s);
    end if;
end for;
count; // 381
#setresultsasis7; // 3
for x in setresultsasis7 do print x; end for;
[ 2, 3, 7 ], [], [ 7 ]
[ 2, 3, 7 ], [], []
[ 2, 3, 7 ], [], [ 2 ]

inds := [i : i in [1..#results] | results[i] eq [2,3,7] and Split(results_asis[i],"<>")[2] eq "[ 2, 3, 7 ], [], [ 7 ]"]; #inds;
// 32
inds;
[ 372957, 492595, 571329, 719940, 755453, 869967, 923038, 1026219, 1152215, 
1208817, 1237947, 1379586, 1424562, 1580423, 1713711, 1753625, 1759762, 1798409,
1872309, 1885282, 1928488, 1963863, 1979386, 1996696, 2137147, 2145128, 2230220,
2241069, 2277342, 2298040, 2315296, 2378814 ]
curvesveryspecialat7 := curves[inds];


setresultsasis5 := {};
count := 0;
for i := 1 to #results do
    if results[i] eq [2,3,5] then
        count +:= 1;
        print results_asis[i];
        s := Split(results_asis[i],"<>")[2];
        Include(~setresultsasis5,s);
    end if;
end for;
count; // 279
#setresultsasis5; // 4
for x in setresultsasis5 do print x; end for;
[ 2, 3, 5 ], [], [ 2 ]
[ 2, 3, 5 ], [], [ 5 ]
[ 2, 3, 5 ], [], []
[ 2, 3, 5 ], [], [ 2, 5 ]


setresultsasis13 := {};
count := 0;
for i := 1 to #results do
    if results[i] eq [2,3,13] then
        count +:= 1;
        print results_asis[i];
        s := Split(results_asis[i],"<>")[2];
        Include(~setresultsasis13,s);
    end if;
end for;
count; // 5
#setresultsasis13; // 1
for x in setresultsasis13 do print x; end for;
[ 2, 3, 13 ], [], []


count := 0;
field_extn_subgrp := {};
for i := 1 to #results_asis do
    s := Split(Split(results_asis[i],"<>")[2],"[")[2];
    Include(~field_extn_subgrp,s);
    count +:= 1;
end for;
count;
field_extn_subgrp := [StringToInteger(Split(s," ],")[1]) : s in field_extn_subgrp | Split(s," ],") ne []];
field_extn_subgrp;
// [ 2 ]









reducible7_curves := [curves[i] : i in [1..#curves] | 7 in results[i]]; #reducible7_curves;
curves := [];
for i := 1 to #reducible7_curves do
    curve := reducible7_curves[i];
    if not [(-1)^(j-1)*curve[j] : j in [1..#curve]] in curves then
        Append(~curves,curve); 
    end if;
end for;
#curves;
// 
#reducible7_curves;
// 
curves;


for i := 1 to #curves do
    C := curves[i];
    f := P ! C;
    mod7img := find_image(f,RadCond(f),subs_with_charpolstat_GLconjinfo[4],all_charpolstats[4]);
    result := <C, mod7img>;
    PrintFile("find_image_7possiblycontainedinC1.txt", result);
    print i;
end for;


*/



/*
to_recheck := [];
for i := 1 to #curves do
    c := curves[i];
    if i mod 1000 eq 0 then print i; end if;
    if not c in curves_old then continue; end if;
    ii := Index(curves_old,c);
    if results[i] ne results_old[ii] or results_asis[i] ne results_asis_old[ii] then
        Append(~to_recheck,<i,ii>);
    end if;
end for;

{results[x[1]] : x in to_recheck};
{
    [ 2, 3 ]
}
{results_old[x[2]] : x in to_recheck};
{
    [ 2, 3 ]
}

{Split(results_asis[x[1]],"<>")[2] : x in to_recheck};
{ [ 2, 3 ], [], [] }
{Split(results_asis_old[x[2]],"<>")[2] : x in to_recheck};
{ [ 2, 3 ], [], [ 2 ] }


distinct_resultsasis := Setseq({Split(x,"<>")[2] : x in results_asis});
for x in distinct_resultsasis do
    print x;
end for;
*/


