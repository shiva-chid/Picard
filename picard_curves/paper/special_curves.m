function BinaryQuarticInvariants(q);

R<x> := Parent(q);

a := Coefficient(q, 4);
b := Coefficient(q, 3);
c := Coefficient(q, 2);
d := Coefficient(q, 1);
e := Coefficient(q, 0);

I := 12*a*e - 3*b*d + c^2;
J := 72*a*c*e + 9*b*c*d - 27*a*d^2 - 27*e*b^2 - 2*c^3;
Disc := 4*I^3 - J^2;
j := 6912*I^3/Disc;
return j, Disc, [ I, J ];

end function;


/* Lists with good ramification outside 2, 3 obtained from Jones-Roberts: */
R<x> := PolynomialRing(Rationals());

fs3 := [
x^3 - 3*x - 1,
x^3 - 3,
x^3 - 2,
x^3 - 3*x - 4,
x^3 + 3*x - 2,
x^3 - 12,
x^3 - 6,
x^3 - 3*x - 10,
x^3 - 9*x - 6
];

fs4 := [
x^4 + 1,
x^4 - 4*x^2 + 2,
x^4 + 4*x^2 + 2,
x^4 - 2*x^2 - 1,
x^4 - 2*x^2 + 2,
x^4 - 2,
x^4 + 2,
x^4 - x^2 + 1,
x^4 + 2*x^2 + 4,
x^4 - 2*x^2 + 4,
x^4 - 2*x^3 - 2*x + 1,
x^4 - 3*x^2 + 3,
x^4 - 4*x^2 + 1,
x^4 + 4*x^2 + 1,
x^4 + 9,
x^4 - 3,
x^4 - 6*x^2 + 12,
x^4 - 12*x^2 + 18,
x^4 + 12*x^2 + 18,
x^4 - 2*x^2 - 2,
x^4 + 2*x^2 - 2,
x^4 - 6*x^2 - 9,
x^4 - 4*x^2 - 2,
x^4 + 4*x^2 - 2,
x^4 + 2*x^2 + 3,
x^4 - 2*x^2 + 3,
x^4 - 6*x^2 + 18,
x^4 + 4*x^2 + 6,
x^4 - 4*x^2 + 6,
x^4 - 2*x^3 + 6*x^2 - 4*x + 2,
x^4 - 18,
x^4 + 18,
x^4 - 6*x^2 + 6,
x^4 - 6*x^2 + 3,
x^4 + 6*x^2 + 6,
x^4 + 6*x^2 + 3,
x^4 - 4*x - 6,
x^4 - 2*x^3 - 6*x + 3,
x^4 - 2*x^3 + 3*x^2 + 2*x - 1,
x^4 - 24,
x^4 - 6,
x^4 + 6,
x^4 + 24,
x^4 - 2*x^3 - 4*x + 2,
x^4 - 2*x^3 - 3*x^2 - 2*x + 7,
x^4 - 4*x - 3,
x^4 - 8*x + 6,
x^4 - 12*x^2 - 16*x + 12,
x^4 - 6*x^2 - 8*x + 6,
x^4 - 16*x - 24,
x^4 - 6*x^2 - 8*x + 15,
x^4 - 8*x - 6,
x^4 - 6*x^2 - 4*x + 6,
x^4 + 3*x^2 - 2*x + 6,
x^4 - 6*x^2 - 4*x + 15,
x^4 - 12*x^2 - 8*x + 18,
x^4 - 24*x^2 - 56*x - 30,
x^4 + 12*x^2 - 16*x + 24,
x^4 + 12*x^2 - 4*x + 69,
x^4 + 12*x^2 - 16*x + 6,
x^4 + 12*x^2 - 16*x + 60,
x^4 + 12*x^2 - 8*x + 42
];

/* Thin out by quadratic subfield criterion: */
fs3 := [ f : f in fs3 | (Integers() ! Discriminant(f)) mod 3 eq 0 ];
fs4 := [ f : f in fs4 | (Integers() ! Discriminant(f)) mod 3 eq 0 ];
fs3 := [ f : f in fs3 | IsSquare(-(Integers() ! Discriminant(f)) div 3) ];
fs4 := [ f : f in fs4 | IsSquare(-(Integers() ! Discriminant(f)) div 3) ];

/* We consider only the degree 4 polynomials here */

fs := [
x^4 - 6*x^2 - 3,
x^4 - 12*x^2 - 12,
x^4 + 6*x^2 + 8*x - 3,
x^4 - 24*x^2 + 32*x - 48,
x^4 + 12*x^2 - 8*x - 12,
x^4 - 36*x^2 + 96*x - 108,
x^4 + 12*x^2 + 64*x - 12,
x^4 + 12*x^2 - 16*x - 12
];

/*
Ls4 := [ SplittingField(f) : f in fs4 ];
Ls := [ SplittingField(f) : f in fs ];
print "";
print "Check correct splitting fields:";
print &and[ IsIsomorphic(Ls[i], Ls4[i]) : i in [1..#Ls] ];
*/

/*
function Shadow(f)
R<x> := Parent(f);
f0 := x^3 + 1; g0 := x^4 - 8*x;
L := SplittingField(f);
RL := PolynomialRing(L);
f0 := RL ! f0; g0 := RL ! g0; f := RL ! f;
test, Ts := IsGL2Equivalent(f, f0, 4);
a,b,c,d := Explode(Ts[1]);
T := Matrix([[a, b], [c, d]]); U := T^(-1);
gU := g0^U; gU /:= LeadingCoefficient(gU);
return R ! gU;
end function;

print "";
print "Calculating shadows for degree 4 polynomials:";
shadows := [ ];
for f in fs do
    print "=======";
    print f;
    s := Shadow(f);
    print s;
    Append(~shadows, s);
end for;
*/

fs := [
    x^4 + x,
    x^4 + 2*x, x^3 - 2,
    x^4 + 3*x, x^3 - 3,
    x^4 + 6*x, x^3 - 6,
    x^4 + 12*x, x^3 - 12,
    x^4 - 6*x^2 - 3, x^4 + 6*x^2 - 3,
    x^4 - 12*x^2 - 12, x^4 + 12*x^2 - 12,
    x^4 + 6*x^2 + 8*x - 3, x^4 + 4*x^3 - 6*x^2 - 4*x - 7,
    x^4 - 24*x^2 + 32*x - 48, x^4 - 4*x^3 + 24*x^2 - 16*x - 32,
    x^4 + 12*x^2 - 8*x - 12, x^4 - 2*x^3 - 12*x^2 + 4*x - 14,
    x^4 - 36*x^2 + 96*x - 108, x^4 - 8*x^3 + 36*x^2 - 48*x - 12,
    x^4 + 12*x^2 + 64*x - 12, x^4 + 16*x^3 - 12*x^2 - 32*x - 140,
    x^4 + 12*x^2 - 16*x - 12, x^4 - 4*x^3 - 12*x^2 + 8*x - 20,
    x^4 - 12*x^2 + 32*x - 12
];

print "";
print "List of polynomials:";
print fs;

print "";
print "Check quartic invariants...";
for i:=1 to #fs do
    j := BinaryQuarticInvariants(fs[i]);
    if j ne 0 then
        print "ERROR";
        print fs[i];
    end if;
end for;
print "done";

/*
print "";
print "Inertia calculation:";
for f in fs do
    L := Polredabs(SplittingField(f));
    ZZL := Integers(L);
    pp := Factorization(ideal< ZZL | 3 >)[1][1];
    H := InertiaGroup(pp);
    test := &or[ Order(h) eq 4 : h in H ];
    if test then
        print f;
    end if;
end for;
*/

print "";
print "Check non-equivalence...";
for i:=1 to #fs do
    for j:=i+1 to #fs do
        if IsGL2Equivalent(fs[i], fs[j], 4) then
            print "ERROR";
            print i, j;
        end if;
    end for;
end for;
print "done";

print "";
print "Check completeness naively...";
B := 20;
for b in [-B..B] do
    for c in [0..B] do
        g := x^4 + 6*b*x^2 + c*x - 3*b^2;
        discg := Abs(Integers() ! Discriminant(g));
        if discg ne 0 then
            testg := &or[ IsGL2Equivalent(g, f, 4) : f in fs ];
            if not testg then
                discs := [ Abs(Integers() ! Discriminant(Integers(NumberField(fac[1])))) : fac in Factorization(g) ];
                testdisc := &and[ disc eq 2^Valuation(disc, 2) * 3^Valuation(disc, 3) : disc in discs ];
                if testdisc then
                    print "ERROR, NEW POLYNOMIAL";
                    print g;
                    exit;
                end if;
            end if;
        end if;
    end for;
end for;
print "done";
