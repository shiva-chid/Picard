/***
 *  Special Picard curves
 *
 *  See LICENSE.txt for license details.
 */


intrinsic BinaryQuarticInvariants(q::RngUPolElt) -> .
{Calculates the invariants of the binary quartic q.}

R<x> := Parent(q);

a := Coefficient(q, 4);
b := Coefficient(q, 3);
c := Coefficient(q, 2);
d := Coefficient(q, 1);
e := Coefficient(q, 0);

I := 12*a*e - 3*b*d + c^2;
J := 72*a*c*e + 9*b*c*d - 27*a*d^2 - 27*e*b^2 - 2*c^3;
DiscAlt := 4*I^3 - J^2;
Disc := DiscAlt/(27);
j := 2^8*I^3/Disc;

return j, Disc, [I, J];

end intrinsic;


intrinsic SpecialPicardForm(f::RngUPolElt) -> .
{Returns special ternary form corresponding to f.}

R<t> := Parent(f); K := BaseRing(R);
assert Type(K) eq FldRat;
assert BinaryQuarticInvariants(f) eq 0;

S<x,y,z> := PolynomialRing(K, 3);
F := x^4 - (S ! (z^4*Evaluate(f, y/z)));
return F;

end intrinsic;


intrinsic SpecialPicardIsIsomorphic(f1::., f2::.) -> .
{Returns whether the special Picard curves defined by f1 and f2 are isomorphic.}

R<t> := Parent(f1); K := BaseRing(R);
assert Type(K) eq FldRat;

test, subs := IsGL2Equivalent(f1, f2, 4);
subs0 := [ ];
for sub in subs do;
    a, b, c, d := Explode(sub);
    num := a*t + b;
    den := c*t + d;
    q := R ! ((c*t + d)^4 * Evaluate(f1, num/den));
    if IsPower(K ! (q / f2), 4) then
        Append(~subs0, sub);
    end if;
end for;

return #subs0 ne 0, subs0;

end intrinsic;


intrinsic SpecialLongWeierstrassEquation(f::RngUPolElt) -> .
{Returns a long Weierstrass equation F0 for the special Picard curve defined by f, along with a transformation T such that up to a scalar F^T = F0 for the homogeneous form F corresponding to f.}

S<t> := Parent(f); K := BaseRing(S);
assert Type(K) eq FldRat;

R<x,y,z> := PolynomialRing(K, 3);
F := R ! SpecialPicardForm(f);

F0, T := MinimizeReducePlaneQuartic(F);
F0 := R ! F0;
T := ChangeRing(T, K);

//print F0;
//print F^T;
//print T;

P2 := [ T[2,1], T[2,2], T[2,3] ];
P3 := [ T[3,1], T[3,2], T[3,3] ];
Ps := [ P2, P3 ];
for i in [1..#Ps] do
    P := Ps[i];
    d := LCM([ Denominator(c) : c in P ]);
    P := [ Integers() ! (d*c) : c in P ];
    d := GCD(P);
    P := [ c div d : c in P ];
    Ps[i] := P;
end for;

ZZ3 := RSpace(Integers(), 3);
H := sub< ZZ3 | Ps >;
H := Saturation(H);
Q, proj := quo< ZZ3 | H >;

B := Basis(H);
P1 := Eltseq(Q.1 @@ proj);
P2 := Eltseq(B[1]);
P3 := Eltseq(B[2]);
T1 := Matrix(K, [ P1, P2, P3 ])^(-1);

U := T*T1;
//print F^U;
//print U;

b := Integers() ! U[1,2]; a := Integers() ! U[1,3];
while b ne 0 do
    if (Abs(b) ge Abs(a)) and (Abs(a) ne 0) then
        n := b div a;
        U := U*Matrix(Rationals(), [[1,0,0],[0,1,0],[0,-n,1]]);
    else
        U := U*Matrix(Rationals(), [[1,0,0],[0,0,1],[0,1,0]]);
    end if;
    b := Integers() ! U[1,2]; a := Integers() ! U[1,3];
end while;
//print F^U;
//print U;

G := F^U;
G /:= GCD([ Integers() ! c : c in Coefficients(G) ]);
G /:= Sign(MonomialCoefficient(G, x^4));

//print Factorization(Integers() ! QuarticDiscriminant(F));
//print Factorization(Integers() ! QuarticDiscriminant(G));
return G, U;

end intrinsic;


intrinsic SpecialShortWeierstrassEquation(f::RngUPolElt) -> .
{Returns a short Weierstrass equation for the special Picard curve defined by f.}

F0 := SpecialLongWeierstrassEquation(f);
R<x,y,z> := Parent(F0);

a0 := MonomialCoefficient(F0, x^4);
a1 := MonomialCoefficient(F0, x^3*y)*y + MonomialCoefficient(F0, x^3*z)*z;
G0 := Evaluate(F0, [ x - (a1/(4*a0)), y, z ]);

G0 *:= LCM([ Denominator(c) : c in Coefficients(G0) ]);
Fac := Factorization(Integers() ! MonomialCoefficient(G0, x^4));
for tup in Fac do
    p := tup[1]; e := tup[2];
    G0 := Evaluate(G0, [ p^(-(e div 4))*x, y, z ]);
end for;

G0 /:= Sign(MonomialCoefficient(G0, x^4));
return G0;

end intrinsic;


function Lambda(f, p)

return Minimum([ Valuation(Coefficient(f, i), p)/ (4 - i) : i in [0..3] ]);

end function;


function Step1(g, ps);

S<t> := Parent(g);
lambda := 1;
for p in ps do
    n := Floor(Lambda(g, p));
    g := p^(-4*n) * Evaluate(g, p^n*t);
    lambda *:= p^n;
end for;
return g, lambda;

end function;


function Step2(g, p);

S<t> := Parent(g);
S0 := PolynomialRing(FiniteField(p));
g0 := S0 ! g;
test, h0 := IsPower(g0, 4);
if not test then
    return false, 0;
end if;
a0 := Roots(h0)[1][1];
a := Rationals() ! Integers() ! a0;
return true, a;

end function;


intrinsic SpecialReducedWeierstrassEquation(f::RngUPolElt) -> .
{Returns a reduced short Weierstrass equation for the special Picard curve defined by f.}
/* I do not copy the old stuff after all; it seems silly here because there is no distinguished root at infinity */
S<t> := Parent(f);
K := BaseRing(S);
assert K eq Rationals();

/* Optimize equation and isolate binary part */
F := SpecialShortWeierstrassEquation(f);

R<x,y,z> := Parent(F);
h := hom< R -> S | [ 0, t, 1 ]>;
f := h(F);
c := -MonomialCoefficient(F, x^4);
f := f / c;

psd := [ p : p in Set(&cat[ [ tup[1] : tup in Factorization(Denominator(c)) ] : c in Coefficients(f) ]) ];
psn := [ p : p in Set(&cat[ [ tup[1] : tup in Factorization(Numerator(c)) ] : c in Coefficients(f) | c ne 0 ]) ];
ps := psd cat psn;

for p in ps do
    v := Minimum([ Valuation(c, p) : c in Coefficients(f) ]);
    e := -(v div 4);
    f *:= p^(4*e);
end for;

return f;

/* Old stuff: */
S<t> := Parent(f);
K := BaseRing(S);
assert K eq Rationals();

/* Optimize equation and isolate binary part */
F := SpecialShortWeierstrassEquation(f);

R<x,y,z> := Parent(F);
h := hom< R -> S | [ 0, t, 1 ]>;
f := h(F);
c := -MonomialCoefficient(F, x^4);
f := f / c;

/* Separate monic form and leading coefficient */
c := MonomialCoefficient(f, t^4);
g := f / c;
disc := Discriminant(g);

/* Find relevant primes */
fac_num := Factorization(Numerator(c));
fac_den := Factorization(Denominator(c));
psc := [ tup[1] : tup in fac_num ] cat [ tup[1] : tup in fac_den ];

fac_num := Factorization(Numerator(disc));
fac_den := Factorization(Denominator(disc));
psg := [ tup[1] : tup in fac_num ] cat [ tup[1] : tup in fac_den ];
psl := [ p : p in Set(&cat[ [ tup[1] : tup in Factorization(Denominator(c)) ] : c in Coefficients(g)]) ];

ps := [ p : p in Set(psc cat psl cat psg) ];

subst := t;
repeat
    g, lambda := Step1(g, ps);
    subst *:= lambda;

    stop := true;
    qs := [ p : p in ps | Lambda(g, p) eq 0 ];
    for q in qs do
        notstop, a := Step2(g, q);
        if notstop then
            g := Evaluate(g, t + a);
            subst +:= Evaluate(subst, t + a);
        end if;
        stop := stop and not notstop;
    end for;
until stop;

f := Evaluate(f, subst);
for p in ps do
    v := Minimum([ Valuation(c, p) : c in Coefficients(f) ]);
    e := -(v div 4);
    f *:= p^(4*e);
end for;

return f;

end intrinsic;


intrinsic SpecialMinimalDiscriminant(p::RngUPolElt) -> .
{Returns the minimal discriminant of the Picard curve defined by p.}

F0 := SpecialLongWeierstrassEquation(p);
return QuarticDiscriminant(F0);

end intrinsic;
