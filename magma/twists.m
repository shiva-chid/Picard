/***
 *  Twists of Picard curves
 *
 *  See LICENSE.txt for license details.
 */

import "wps.m" : WPSMultiply, WPSMinimize, WPSMinimizeTwist;


function TwistsAtPrime(cs, p);

if cs[2] eq 0 then
    W := [ 1, 0, 2 ];
    lambdas := [ p^i : i in [0..5] ];
elif cs[1] eq 0 and cs[3] eq 0 then
    W := [ 0, 1, 0 ];
    lambdas := [ p^i : i in [0..8] ];
else 
    W := [ 2, 3, 4 ];
    lambdas := [ p^i : i in [0..2] ];
end if;

return [ WPSMultiply(W, cs, lambda) : lambda in lambdas ];

end function;


function TwistsAtSign(cs);

if cs[2] eq 0 then
    return [ cs, [ -cs[1], 0, cs[3] ] ];
else
    return [ cs ];
end if;

end function;


intrinsic SmallPicardTwist(f::RngUPolElt) -> .
{Returns a twist of defining a Picard curve with as few primes of bad reduction as possible.}

assert not IsSpecialPicard(f);
R<t> := Parent(f); K := BaseRing(R);
assert K eq Rationals();

cs := ArithmeticInvariants(f);
cs0 := WPSMinimizeTwist([6, 9, 12], cs);
f0 := t^4 + cs0[1]*t^2 + cs0[2]*t + cs0[3];

f0 := ReducedWeierstrassEquation(f0 : OnlyAtTwo := true);
gcd := GCD([ Integers() ! c : c in Coefficients(f0) ]);
f0 /:= gcd;

ps := [ tup[1] : tup in Factorization(Integers() ! Discriminant(f0)) ];
if not 3 in ps then
    Append(~ps, 3);
    ps := Sort(ps);
end if;

cs0 := ArithmeticInvariants(f0);
f0 := t^4 + cs0[1]*t^2 + cs0[2]*t + cs0[3];
return f0, ps;

end intrinsic;


intrinsic MinimalPicardTwist(f::RngUPolElt) -> .
{Returns a form defining a minimal twist of the Picard curve defined by f.}

assert not IsSpecialPicard(f);
R<t> := Parent(f); K := BaseRing(R);
assert K eq Rationals();

f0 := SmallPicardTwist(f);
cs := ArithmeticInvariants(f0);
test := not ((cs[2] eq 0) or (cs[1] eq 0 and cs[3] eq 0));
if test then
    ps := [ 3 ];
else
    g := t^4 + cs[1]*t^2 + cs[2]*t + cs[3];
    disc := Integers() ! Discriminant(g);
    ps := [ tup[1] : tup in Factorization(disc) ];
    if not 3 in ps then
        Append(~ps, 3);
    end if;
end if;

for p in ps do
    css := TwistsAtPrime(cs, p);
    gs := [ t^4 + cs[1]*t^2 + cs[2]*t + cs[3] : cs in css ];
    discs := [ MinimalDiscriminant(g) : g in gs ];
    vals := [ Valuation(disc, p) : disc in discs ];
    min, i := Minimum(vals);
    cs := css[i];
end for;
if cs[2] eq 0 then
    css := TwistsAtSign(cs);
    gs := [ t^4 + cs[1]*t^2 + cs[2]*t + cs[3] : cs in css ];
    discs := [ MinimalDiscriminant(g) : g in gs ];
    vals := [ Abs(disc) : disc in discs ];
    min, i := Minimum(vals);
    cs := css[i];
end if;

g := t^4 + cs[1]*t^2 + cs[2]*t + cs[3];
return ReducedWeierstrassEquation(g);

end intrinsic;


intrinsic SmallPicardTwists(f::RngUPolElt, ps::SeqEnum) -> .
{Returns all the twists of f that define a Picard curve with good reduction outside the primes in ps.}

assert not IsSpecialPicard(f);
R<t> := Parent(f); K := BaseRing(R);
assert K eq Rationals();

f0, ps0 := SmallPicardTwist(f);
test := &and[ p in ps : p in ps0 ];
if not test then
    return [ ];
end if;

cs0 := ArithmeticInvariants(f0);
css := [ cs0 ];
for p in ps do
    css := &cat[ TwistsAtPrime(cs, p) : cs in css ];
end for;
if cs0[2] eq 0 then
    css := &cat[ TwistsAtSign(cs) : cs in css ];
end if;

/* We have to check at 2 every time; surprisingly, twisting at 3 can change the
 * minimal discriminant at 2 */
if not 2 in ps then
    csschecked := [ ];
    for cs in css do
        f := t^4 + cs[1]*t^2 + cs[2]*t + cs[3];
        f0 := ReducedWeierstrassEquation(f : OnlyAtTwo := true);
        disc0 := Integers() ! Discriminant(f0);
        if (disc0 mod 2 ne 0) then
            Append(~csschecked, cs);
        end if;
    end for;
    css := csschecked;
end if;

css := [ WPSMinimize([6, 9, 12], cs) : cs in css ];
fs := [ t^4 + cs[1]*t^2 + cs[2]*t + cs[3] : cs in css ];
return fs;

end intrinsic;


intrinsic SpecialPicardTwists(f::RngUPolElt, ps::SeqEnum) -> .
{Returns all the twists of f that define a special Picard curve with good reduction outside the primes in ps.}

R<t> := Parent(f); K := BaseRing(R);
assert K eq Rationals();
assert BinaryQuarticInvariants(f) eq 0;

disc := Integers() ! Discriminant(f);
psf := [ tup[1] : tup in Factorization(disc) ];

test := &and[ p in ps : p in psf ];
if not test then
    return [ ];
end if;

test, subs := IsGL2Equivalent(f, f, 4);
exps := [ ];

qs := [ ]; ps := [ -1 ] cat ps; psnew := [ ];
for sub in subs do
    a, b, c, d := Explode(sub);
    num := a*t + b;
    den := c*t + d;
    g := R ! ((c*t + d)^4 * Evaluate(f, num/den));
    q := K ! (g / f);

    den := Denominator(q); facden := Factorization(den);
    num := Numerator(q); facnum := Factorization(num);
    fac := facden cat facnum; psq := [ tup[1] : tup in fac ];
    for p in psq do
        v := Valuation(q, p);
        e := v div 4;
        q *:= p^e;
    end for;

    q := Integers() ! q; Append(~qs, q);
    fac := Factorization(q);
    pnew := [ tup[1] : tup in fac | not tup[1] in ps ];
    psnew := Sort([ p : p in Set(psnew cat pnew) ]);
end for;

psfull := ps cat psnew;
M := RSpace(Integers(), #psfull);
vs := [ 2*M.1 ] cat [ 4*M.i : i in [2..#psfull] ];
ws := [ -((Sign(q) - 1) div 2)*M.1 + &+[ Valuation(q, psfull[i])*M.i : i in [2..#psfull ] ] : q in qs ];
N1 := sub< M | vs cat ws >;
N2 := sub< M | [ M.i : i in [1..#ps] ] >;
N := N1 meet N2;
P := sub< M | [ M.i : i in [(#ps + 1)..#psfull] ] >;
Q, proj := quo< M | N + P >;

vs := [ q @@ proj : q in Q ];
vs := [ Eltseq(v)[1..#ps] : v in vs ];
ds := [ ];
/* Correct for non-optimality */
for i in [1..#ps] do
    Mi := sub< M | M.i >;
    Qi := (N + P) meet Mi;
    Bi := Eltseq(Basis(Qi)[1]);
    Append(~ds, GCD(Bi));
end for;
vs := [ [ v[i] mod ds[i] : i in [1..#v] ] : v in vs ];

cs := [ &*[ ps[i]^v[i] : i in [1..#ps] ] : v in vs ];
return [ c*f : c in cs ];

end intrinsic;
