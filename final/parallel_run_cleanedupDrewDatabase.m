AttachSpec("spec");

input_split := Split(input_string,":");
cond := StringToInteger(input_split[1]);
P<x> := PolynomialRing(Integers());
f := eval input_split[2][2..#input_split[2]-1];




ff := suppressed_integer_quartic(f);
if Coefficient(ff,1) eq 0 and Coefficient(ff,3) eq 0 then
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
    PrintFile("nonsurjprimes_results_cleanedupDrewDatabase.txt", Sprint(result) cat ",");
catch e;
//    badprimes := PrimeFactors(RadCond(f));
    error_for := <Coefficients(f)>;
    PrintFile("error_in_possibly_nonsurj_primes_cleanedupDrewDatabase.txt", error_for);
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
    s_split := Split(s,"<[,]> ");
    coeffs := [StringToInteger(x) : x in s_split[1..5]];
    nonsurjprimes := Sort(SetToSequence({StringToInteger(x) : x in s_split[6..#s_split]}));
    Append(~curves,coeffs);
    Append(~results,nonsurjprimes);
    Append(~results_asis,s);
    s := Gets(fil);
end while;

{Maximum(x) : x in results};
Set(results);

for i := 1 to #results do
    if results[i] eq [2,3,5] or results[i] eq [2,3,7] or results[i] eq [2,3,5,7] then
        print results_asis[i];
    end if;
end for;

for i := 1 to #results do
    if results[i] ne [2,3] then
        print results_asis[i];
    end if;
end for;

for i := 1 to #results do
    if not Set(results[i]) subset {2,3,5,7}  then
        print results_asis[i];
    end if;
end for;


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
