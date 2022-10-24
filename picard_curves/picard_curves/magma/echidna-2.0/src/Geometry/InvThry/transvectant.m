/////////////////////////////////////////////////////////////////////////////
//                                                                         //
//   Copyright (C) 2006 David Kohel <kohel@maths.usyd.edu.au>              //
//                                                                         //
//   Distributed under the terms of the GNU General Public License (GPL)   //
//   Full text of the GPL is available at: http://www.gnu.org/licenses/    //
//                                                                         //
/////////////////////////////////////////////////////////////////////////////

/*
Mestre "Construction de courbes de genre 2 a partir de leurs modules", p. 315,
"Transvectant" [Uberschiebung (Clebsch) or "Translation" (Faa de Bruno)]
*/

function DerivativeSequence(f,n)
    S := [ Parent(f) | ];
    for k in [0..n] do
        g := f;
        for i in [1..n] do
            if i le k then
                g := Derivative(g,1);
            else
                g := Derivative(g,2);
            end if;
        end for;
        S[k+1] := g; 
    end for;
    return S; 
end function;

intrinsic Transvectant(f::RngMPolElt,g::RngMPolElt,r::RngIntElt) -> RngMPolElt
    {}
    P := Parent(f);
    require P eq Parent(f) : "Arguments 1 and 2 must be have the same parent.";
    require IsHomogeneous(f) and IsHomogeneous(g) : "Arguments 1 and 2 must be homogeneous.";
    if f eq 0 or g eq 0 then return P!0; end if;
    Sf := DerivativeSequence(f,r);
    Sg := DerivativeSequence(g,r);
    Tfg := P!0;
    for k in [0..r] do
         Tfg +:= (-1)^k*Binomial(r,k)*Sf[k+1]*Sg[r-k+1];
    end for;
    n := TotalDegree(f); 
    m := TotalDegree(g);
    cfg := Factorial(n-r)*Factorial(m-r)/(Factorial(n)*Factorial(m));
    return cfg*Tfg;
end intrinsic;

/*
// INVARIANTS OF A SEXTIC GENUS 2 CURVE:

FF<v0,v1,v2,v3,v4,v5,v6> := FunctionField(ZZ,7);
P<X,Z> := PolynomialRing(FF,2);
PF<x> := PolynomialRing(FF);
f := v0*X^6 + v1*X^5*Z + v2*X^4*Z^2 + v3*X^3*Z^3 + v4*X^2*Z^4 + v5*X*Z^5 + v6*Z^6;
Cf := HyperellipticCurve(Evaluate(f,[x,1]));

 i := Transvectant( f, f, 4); // order 4, degree 2
DD := Transvectant( i, i, 2); // order 4, degree 4
y1 := Transvectant( f, i, 4); // order 2, degree 3
y2 := Transvectant( i,y1, 2); // order 2, degree 5
y3 := Transvectant( i,y2, 2); // order 2, degree 7
 A := Transvectant( f, f, 6); // order 0, degree 2
 B := Transvectant( i, i, 4); // order 0, degree 4
 C := Transvectant( i,DD, 4); // order 0, degree 6
 D := Transvectant(y3,y1, 2); // order 0, degree 10

// Here A, B, C, D are the (weighted) Clebsch invariants:

[4^2*A, 4^4*B, 4^6*C, 4^10*D] eq ClebschInvariants(Cf);

// INVARIANTS OF A QUINTIC GENUS 2 CURVE:

FF<v0,v1,v2,v3,v4,v5> := FunctionField(ZZ,6);
P<X,Z> := PolynomialRing(FF,2);
g0 := v0*X^6 + v1*X^5*Z + v2*X^4*Z^2 + v3*X^3*Z^3 + v4*X^2*Z^4 + v5*X*Z^5;
g1 := v5*X^5 + v4*X^4*Z + v3*X^3*Z^2 + v2*X^2*Z^3 + v1*X*Z^4 + v0*Z^5;
PF<x> := PolynomialRing(FF);
// Isomorphic curves with Weierstrass point at (0,0) and oo, respectively.
Cg0 := HyperellipticCurve(Evaluate(g0,[x,1]));
Cg1 := HyperellipticCurve(Evaluate(g1,[x,1]));

f := g0; g := g1;

A1 := Transvectant( f, f,6); // order 0, degree 2 (Clebsch A) 
 i := Transvectant( g, g,4); // order 2, degree 2
x1 := Transvectant( i, g,2); // order 3, degree 3
x2 := Transvectant(x1, i,1); // order 3, degree 5
y1 := Transvectant(x1, g,2); // order 4, degree 4
y2 := Transvectant(x2, g,2); // order 4, degree 6
z1 := Transvectant(x1, i,2); // order 1, degree 5 
z2 := Transvectant(x2, i,2); // order 1, degree 7 
w1 := Transvectant(x1,z2,1); // order 2, degree 10
w2 := Transvectant(y1, i,2); // order 2, degree 6
B1 := Transvectant( i, i,2); // order 0, degree 4
C1 := Transvectant(y1,y1,4); // order 0, degree 6
      C1 eq Transvectant(x1,x2,3); 
S1 := Transvectant(y1,y1,4); // order 0, degree 8 
      S1 eq Transvectant(w2, i,2); 
D1 := Transvectant(z1,z2,1); // order 0, degree 12
      D1 eq Transvectant(w1, i,2);

A1 := Coefficients(A1)[1];
B1 := Coefficients(B1)[1];
C1 := Coefficients(C1)[1];
D1 := Coefficients(D1)[1];
J2, J4, J6, J8, J10 := Explode(IgusaInvariants(Cg0));

// These [A1,B1,C1,D1] are no longer the Clebsch invariants, but should 
// satisfy algebraic relations with them, defining a degree 6 cover of 
// the moduli space.
*/
