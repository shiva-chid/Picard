/* Example from the paper */

/* Start with equation containing a3 and unlikely to get smaller */
R<x,y,z> := PolynomialRing(Rationals(), 3);
p := 17;

F1 := x^3*z - (p*y^4 + y^3*z + 2*y^2*z^2 + y*z^3 - z^4);
val1 := Valuation(QuarticDiscriminant(F1), p);
print "";
print "Valuation of form with trace:";
print val1;

/* No integral coefficients */
F2 := Evaluate(F1, [x, y - (1/(4*p))*z, z]);
print "";
print "Non-integral model:";
print F2;

w3 := Valuation(MonomialCoefficient(F2, x^3*z^1), p);
v4 := Valuation(MonomialCoefficient(F2, y^4*z^0), p);
v2 := Valuation(MonomialCoefficient(F2, y^2*z^2), p);
v1 := Valuation(MonomialCoefficient(F2, y^1*z^3), p);
v0 := Valuation(MonomialCoefficient(F2, y^0*z^4), p);
print "Coefficient valuations:";
print [ w3, v4, v2, v1, v0 ];

/* These heuristics can be made rigorous with linear programming techniques */
D := [-50..50];
tups := CartesianPower(D, 3);
valmin := Infinity();
for tup in tups do
    la, mu, nu := Explode(tup);
    val := 27*la + 36*mu + 36*nu;
    tests := [ ];
    Append(~tests, (la + 3*nu + w3) ge 0);
    Append(~tests, (la + 4*mu + v4) ge 0);
    Append(~tests, (la + 2*mu + v2) ge 0);
    Append(~tests, (la + 1*mu + v1) ge 0);
    Append(~tests, (la + 0*mu + v0) ge 0);
    if &and(tests) then
        if val lt valmin then
            mins := [ tup ];
            valmin := val;
        elif val eq valmin then
            Append(~mins, tup);
        end if;
    end if;
end for;

/*
print "";
print "Minimal valuations for traceless model:";
print valmin;
print mins;
*/

la, mu, nu := Explode(mins[1]);
F3 := p^la * Evaluate(F2, [ p^nu*x, p^mu*y, z ]);
print "";
print "Traceless model:";
print F3;
print "Discriminant valuation:";
print Valuation(QuarticDiscriminant(F3), p);

w3 := Valuation(MonomialCoefficient(F3, x^3*z^1), p);
v4 := Valuation(MonomialCoefficient(F3, y^4*z^0), p);
v2 := Valuation(MonomialCoefficient(F3, y^2*z^2), p);
v1 := Valuation(MonomialCoefficient(F3, y^1*z^3), p);
v0 := Valuation(MonomialCoefficient(F3, y^0*z^4), p);
print "Coefficient valuations:";
print [ w3, v4, v2, v1, v0 ];
