/***
 *  Non-special Picard curves
 *
 *  See LICENSE.txt for license details.
 */


intrinsic PicardForm(f::RngUPolElt) -> .
{Returns ternary form corresponding to f.}

R<t> := Parent(f); K := BaseRing(R);
S<y,x,z> := PolynomialRing(K, 3);
F := y^3*z - (S ! (z^4*Evaluate(f, x/z)));
return F;

end intrinsic;


intrinsic QuarticDiscriminant(F::RngMPolElt) -> .
{Returns the discriminant of the quartic F.}

I := DixmierOhnoInvariants(F);
DF := I[#I];
if DF in Integers() then
    DF := Integers() ! DF;
end if;
return DF;

end intrinsic;


intrinsic PicardIsIsomorphic(f1::., f2::.) -> .
{Returns whether the Picard curves defined by f1 and f2 are isomorphic.}

R<x> := Parent(f1); K := BaseRing(R);
assert Type(K) eq FldRat;

test, subs := IsGL2Equivalent(f1, f2, 4);
subs0 := [ ];
for sub in subs do;
    a, b, c, d := Explode(sub);
    num := a*x + b;
    den := c*x + d;
    q := R ! ((c*x + d)^4 * Evaluate(f1, num/den));
    if IsPower(K ! (q / f2), 3) then
        Append(~subs0, sub);
    end if;
end for;
return #subs0 ne 0, subs0;

end intrinsic;
