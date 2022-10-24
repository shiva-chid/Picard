R<t> := PolynomialRing(Rationals());
fs := [ t^4 - 12*t^2 - 12, t^4 + t ];

for f in fs do
    print "";
    print "===============================================================================";
    print "Form:";
    print f;

    F0 := SpecialLongWeierstrassEquation(f);
    print "";
    print "Long Weierstrass equation (minimal discriminant as a plane quartic):";
    print F0;
    print "Factorization of corresponding discriminant:";
    print Factorization(QuarticDiscriminant(F0));

    G0 := SpecialShortWeierstrassEquation(f);
    print "";
    print "Minimal short Weierstrass equation (minimal discriminant away from 3):";
    print G0;
    print "Factorization of corresponding discriminant:";
    print Factorization(QuarticDiscriminant(G0));

    g := SpecialReducedWeierstrassEquation(f);
    print "";
    print "Reduced short Weierstrass form (minimized binary quartic times scalar):";
    print g;
    print "Factorization of corresponding discriminant:";
    print Factorization(QuarticDiscriminant(SpecialPicardForm(g)));
end for;
