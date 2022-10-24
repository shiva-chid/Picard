/***
 *  Invariants of Picard curves
 *
 *  See LICENSE.txt for license details.
 */

import "wps.m" : WPSMultiply, WPSMinimize, WPSMinimizeTwist;


function CoefficientTriple(f)

S<t> := Parent(f); K := BaseRing(S);
assert K eq Rationals();
assert Degree(f) eq 4;

f := Evaluate(f, t - Coefficient(f, 3)/(4*Coefficient(f, 4)));
c0 := Coefficient(f, 4);
I := [ Coefficient(f, 2), Coefficient(f, 1), Coefficient(f, 0) ];
W := [1, 2, 3];
I := WPSMultiply(W, I, c0);
return I;

end function;


intrinsic GeometricInvariants(f::.) -> .
{Geometric invariants of Picard curve defined by f.}

I := CoefficientTriple(f);
W := [6, 9, 12];
return WPSNormalize(W, I);

end intrinsic;


intrinsic ArithmeticInvariants(f::.) -> .
{Arithmetic invariants of Picard curve defined by f.}

I := CoefficientTriple(f);
W := [6, 9, 12];
return WPSMinimize(W, I);

end intrinsic;
