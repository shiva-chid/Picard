R<t> := PolynomialRing(Rationals());
fs := [ t^4 + t + 1 ];

for f in fs do
    print "";
    print "===============================================================================";
    print "Form:";
    print f;

    F0 := LongWeierstrassEquation(f);
    print "";
    print "Long Weierstrass equation (minimal discriminant as a plane quartic):";
    print F0;
    print "Factorization of corresponding discriminant:";
    print Factorization(QuarticDiscriminant(F0));

    G0 := ShortWeierstrassEquation(f);
    print "";
    print "Minimal short Weierstrass equation (minimal discriminant away from 3):";
    print G0;
    print "Factorization of corresponding discriminant:";
    print Factorization(QuarticDiscriminant(G0));

    g := ReducedWeierstrassEquation(f);
    print "";
    print "Reduced short Weierstrass form (minimized binary quartic times scalar):";
    print g;
    print "Factorization of corresponding discriminant:";
    print Factorization(QuarticDiscriminant(PicardForm(g)));

    I := GeometricInvariants(f);
    print "";
    print "Geometric invariants of f:";
    print I;

    I := ArithmeticInvariants(f);
    print "";
    print "Arithmetic invariants of f:";
    print I;
end for;
