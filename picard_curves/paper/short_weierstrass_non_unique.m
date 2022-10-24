R<y,x,z> := PolynomialRing(Rationals(), 3);
p := 17;

w3 := 0; v4 := 5; v2 := 0; v1 := 1; v0 := 0;
F1 := p^w3*y^3*z - (p^v4*x^4 + 2*p^v2*x^2*z^2 + p^v1*x*z^3 - p^v0*z^4);
w3 := 1; v4 := 1; v2 := 0; v1 := 3; v0 := 4;
F2 := p^w3*y^3*z - (p^v4*x^4 + 2*p^v2*x^2*z^2 + p^v1*x*z^3 - p^v0*z^4);
F0 := R ! MinimizeReducePlaneQuartic(F1);

print "";
print "Models:";
print F1;
print F2;

print "";
print "Valuations:";
print Valuation(QuarticDiscriminant(F1), p);
print Valuation(QuarticDiscriminant(F2), p);

print "";
print "Valuation of Elsenhans model:";
print Valuation(QuarticDiscriminant(F0), p);

//print "";
//print "Trying to decrease further...";
//while true do
//  D := [-10..10];
//  T := Matrix(Rationals(), 3,3, [ Random(D) : i in [1..9] ]);
//  F2 := F1^T;
//  F0 := R ! MinimizeReducePlaneQuartic(F2);
//  if Valuation(QuarticDiscriminant(F0), p) lt 25 then
//    print T;
//  end if;
//end while;
