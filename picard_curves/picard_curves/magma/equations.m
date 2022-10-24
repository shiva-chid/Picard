/***
 *  Equations for non-special curves
 *
 *  See LICENSE.txt for license details.
 */

import "wps.m" : WPSMultiply, WPSMinimize, WPSMinimizeTwist;


intrinsic LongWeierstrassEquation(f::RngUPolElt) -> .
{Returns a long Weierstrass equation F0 for the Picard curve defined by f, along with a transformation T such that up to a scalar F^T = F0 for the homogeneous form F corresponding to f.}

S<t> := Parent(f);
K := BaseRing(S);
assert Type(K) eq FldRat;

R<y,x,z> := PolynomialRing(K, 3);
f := ReducedWeierstrassEquation(f);
F := R ! PicardForm(f);

F0, T := MinimizeReducePlaneQuartic(F);
F0 := R ! F0;
T := ChangeRing(T, K);
U := T^(-1);

/* At this point F^T = F0, so that T maps X0 to X and U maps X to X0 */
// Image of (1 : 0 : 0)
P := [ U[1,1], U[2,1], U[3,1] ];
d := LCM([ Denominator(c) : c in P ]);
P := [ Integers() ! (d*c) : c in P ];
d := GCD(P);
P := [ c div d : c in P ];

ZZ3 := RSpace(Integers(), 3);
Q, proj := quo< ZZ3 | ZZ3 ! P >;
Q1 := Eltseq(Q.1 @@ proj);
Q2 := Eltseq(Q.2 @@ proj);

T1 := Transpose(Matrix(K, [ P, Q1, Q2 ]));
U1 := T1^(-1);
F1 := F0^T1;

P := [ MonomialCoefficient(F1, y^3*x), MonomialCoefficient(F1, y^3*z) ];
d := LCM([ Denominator(c) : c in P ]);
P := [ Integers() ! (d*c) : c in P ];
d := GCD(P);
P := [ c div d : c in P ];

ZZ2 := RSpace(Integers(), 2);
Q, proj := quo< ZZ2 | ZZ2 ! P >;
Q1 := Eltseq(Q.1 @@ proj);

T2 := DiagonalJoin(Matrix(K, [[1]]), Matrix(K, [ Q1, P ]));
U2 := T2^(-1);
F2 := F1^U2;

T := T*T1*U2;
T11 := (Integers() ! T[1,1]); T12 := (Integers() ! T[1,2]);
if T12 mod T11 eq 0 then
    T := T*Matrix(K, [[ 1, -T12 div T11, 0 ], [ 0, 1, 0 ], [ 0, 0, 1 ]]);
end if;

G := F^T;
G /:= GCD([ Integers() ! c : c in Coefficients(G) ]);
G /:= Sign(MonomialCoefficient(G, y^3*z));
return G, T;

end intrinsic;


intrinsic ShortWeierstrassEquation(f::RngUPolElt) -> .
{Returns a short Weierstrass equation for the Picard curve defined by f.}

F0 := LongWeierstrassEquation(f);
R<y,x,z> := Parent(F0);

a0 := MonomialCoefficient(F0, y^3*z);
a1 := MonomialCoefficient(F0, y^2*x*z)*x + MonomialCoefficient(F0, y^2*z^2)*z;
G0 := Evaluate(F0, [ y - (a1/(3*a0)), x, z ]);

G0 *:= LCM([ Denominator(c) : c in Coefficients(G0) ]);
Fac := Factorization(Integers() ! MonomialCoefficient(G0, y^3*z));
for tup in Fac do
    p := tup[1]; e := tup[2];
    G0 := Evaluate(G0, [ p^(-(e div 3))*y, x, z ]);
end for;

G0 /:= Sign(MonomialCoefficient(G0, y^3*z));
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


intrinsic ReducedWeierstrassEquation(f::RngUPolElt : FromShort := false, OnlyAtTwo := false) -> .
{Returns a reduced short Weierstrass equation for the Picard curve defined by f.}

S<t> := Parent(f); K := BaseRing(S);
assert Type(K) eq FldRat;

if FromShort then
    F := ShortWeierstrassEquation(f);
    R<y,x,z> := Parent(F);
    h := hom< R -> S | [ 0, t, 1 ]>;
    f := h(F);
    c := -MonomialCoefficient(F, y^3*z);
    f := f / c;
else
    cs := ArithmeticInvariants(f);
    cs0 := WPSMinimize([6, 9, 12], cs);
    f := t^4 + cs0[1]*t^2 + cs0[2]*t + cs0[3];
end if;

/* Separate monic form and leading coefficient */
c := MonomialCoefficient(f, t^4);
g := f / c;
goink := g;

if OnlyAtTwo then
    ps := [ 2 ];
else
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
end if;

repeat
    g, lambda := Step1(g, ps);
    f := Evaluate(f, lambda*t);

    stop := true;
    qs := [ p : p in ps | Lambda(g, p) eq 0 ];
    for q in qs do
        notstop, a := Step2(g, q);
        if notstop then
            g := Evaluate(g, t + a);
            f := Evaluate(f, t + a);
        end if;
        stop := stop and not notstop;
    end for;
until stop;

for p in ps do
    v := Minimum([ Valuation(c, p) : c in Coefficients(f) ]);
    e := -(v div 3);
    f *:= p^(3*e);
end for;

/* May remove a minus because of third power */
f *:= Sign(Coefficient(f, 4));
return f;

end intrinsic;


intrinsic MinimalDiscriminant(p::RngUPolElt) -> .
{Returns the minimal discriminant of the Picard curve defined by p.}

F0 := LongWeierstrassEquation(p);
return QuarticDiscriminant(F0);

end intrinsic;
