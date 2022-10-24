/* Relation between Picard discriminant and Demazure discriminant */

K<b,a4,a3,a2,a1,a0> := RationalFunctionField(Rationals(), 6);

R<x> := PolynomialRing(K);
f := a4*x^4 + a3*x^3 + a2*x^2 + a1*x + a0;
Df := Discriminant(f);

S<x,y,z> := PolynomialRing(K, 3);
F := b*y^3*z - (a4*x^4 + a3*x^3*z + a2*x^2*z^2 + a1*x*z^3 + a0*z^4);
I := DixmierOhnoInvariants(F);
DF := I[#I];

print "";
print "DF / Df^2 for nonspecial curves:";
print DF / Df^2;

F := b*y^4 - (a4*x^4 + a3*x^3*z + a2*x^2*z^2 + a1*x*z^3 + a0*z^4);
I, W := DixmierOhnoInvariants(F);
DF := I[#I];

print "";
print "DF / Df^3 for special curves:";
print DF / Df^3;
