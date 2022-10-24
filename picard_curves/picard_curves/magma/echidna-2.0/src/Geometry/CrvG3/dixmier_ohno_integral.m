//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//          Dixmier and Ohno Invariants of Ternary Quartics                 // 
//                                                                          // 
//  Copyright (C) 2004 Martine Girard <girard@maths.usyd.edu>               //
//  Copyright (C) 2006 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

/*
Dixmier invariants -- Martine Girard, 2004.
Discriminant I_27 implemented by Christophe Ritzenthaler, 2004.
Ohno invariants -- David Kohel, 2006.
*/

declare verbose Dixmier, 2;

forward QuarticDiscriminant;

function PowerDerivative(F,exp)
    DF := F;
    for i in [1..#exp] do
        if exp[i] ne 0 then
            DF := Derivative(DF,exp[i],i); // k = exp[i]-th derivative wrt i
        end if;
    end for;
    return DF;
end function;

/*
The operation DifferentialOperation(F,G) takes a pair of covariant
and contravariant in either order, and returns another object of
the type of the second argument G.  The 'degree' of a co/contra-
variant is the homogeneous degree in the coefficients of the
original form and the 'order' is the degree in the variables X,Y,Z
for a covariant or the dual variables u,v,w for a contravariant.
The return value H of DifferentialOperation(F,G) satisfies:

                  deg(H) = deg(F) + deg(G),
and
                  ord(H) = ord(G) - ord(F).
*/

function DifferentialOperation(F,G)
    mons := Monomials(F);
    cffs := Coefficients(F);
    DG := Parent(G)!0;
    for i in [1..#cffs] do
        DG +:= cffs[i]*PowerDerivative(G,Exponents(mons[i]));
    end for;
    return DG;
end function;

function KOperation11(F,G)
    X,Y,Z := Explode([ P.i : i in [1..3] ]) where P := Parent(F);
    ww := [  2,   1,   2,   1,   1,   2  ];
    XX := [ X^2, X*Y, Y^2, Y*Z, X*Z, Z^2 ];
    FF := [ MonomialCoefficient(F,M) : M in XX ];
    GG := [ MonomialCoefficient(G,M) : M in XX ];
    return &+[ ww[i]*FF[i]*GG[i] : i in [1..6] ]; 
end function;

function KOperation22(F,G)
    P := Parent(F);
    K := BaseRing(P);
    X,Y,Z := Explode([ P.i : i in [1..3] ]);
    A := MatrixAlgebra(K,3)!0;
    B := MatrixAlgebra(K,3)!0;
    for i in [1..3] do
        A[i,i] := 2*MonomialCoefficient(F,P.i^2);
        B[i,i] := 2*MonomialCoefficient(G,P.i^2);
        for j in [i+1..3] do
            A[i,j] := MonomialCoefficient(F,P.i*P.j);
            A[j,i] := A[i,j];
            B[i,j] := MonomialCoefficient(G,P.i*P.j);
            B[j,i] := B[i,j];
        end for;
    end for;
    Astar := Eltseq(Adjoint(A));
    Bstar := Eltseq(Adjoint(B));
    return &+[ Astar[i]*Bstar[i] : i in [1..9] ];
end function;

function KOperation30(F)
    P := Parent(F);
    K := BaseRing(P);
    X,Y,Z := Explode([ P.i : i in [1..3] ]);
    A := MatrixAlgebra(K,3)!0;
    for i in [1..3] do
        A[i,i] := 2*MonomialCoefficient(F,P.i^2);
        for j in [i+1..3] do
            A[i,j] := MonomialCoefficient(F,P.i*P.j);
            A[j,i] := A[i,j];
        end for;
    end for;
    return K!Determinant(A);
end function;

function KOperation03(G)
    return KOperation30(G);
end function;

function CovariantIntegralHessian(Phi)
    P := Parent(Phi);
    X := P.1; Y := P.2; Z := P.3;
    a := MonomialCoefficient(Phi,X^4);
    b := MonomialCoefficient(Phi,X^3*Y);
    c := MonomialCoefficient(Phi,X^2*Y^2);
    d := MonomialCoefficient(Phi,Y^3*X);
    e := MonomialCoefficient(Phi,Y^4);
    f := MonomialCoefficient(Phi,X^3*Z);
    g := MonomialCoefficient(Phi,X^2*Y*Z);
    h := MonomialCoefficient(Phi,X*Y^2*Z);
    i := MonomialCoefficient(Phi,Y^3*Z);
    j := MonomialCoefficient(Phi,X^2*Z^2);
    k := MonomialCoefficient(Phi,X*Y*Z^2);
    l := MonomialCoefficient(Phi,Y^2*Z^2);
    m := MonomialCoefficient(Phi,X*Z^3);
    n := MonomialCoefficient(Phi,Z^3*Y);
    p := MonomialCoefficient(Phi,Z^4);
    He := (8*a*c*j - 2*a*g^2 - 3*b^2*j + 3*b*f*g - 3*c*f^2)*X^6
        + (8*a*c*k + 24*a*d*j - 8*a*g*h - 3*b^2*k - 4*b*c*j + 6*b*f*h + b*g^2 - 9*d*f^2)*X^5*Y
        + (24*a*c*m - 8*a*g*k + 8*a*h*j - 9*b^2*m + 6*b*f*k - 4*c*f*j - 3*f^2*h + f*g^2)*X^5*Z
        + (8*a*c*l + 24*a*d*k + 48*a*e*j - 12*a*g*i - 8*a*h^2 - 3*b^2*l - 4*b*c*k + 6*b*d*j
        + 9*b*f*i + b*g*h - 4*c^2*j + 6*c*f*h + c*g^2 - 9*d*f*g - 18*e*f^2)*X^4*Y^2
        + (24*a*c*n + 72*a*d*m - 16*a*g*l - 8*a*h*k + 24*a*i*j - 9*b^2*n - 12*b*c*m + 12*b*f*l
        - 2*b*g*k + 8*b*h*j + 8*c*f*k - 4*c*g*j - 12*d*f*j - 9*f^2*i - 2*f*g*h + g^3)*X^4*Y*Z
        + (48*a*c*p - 12*a*g*n + 24*a*h*m + 8*a*j*l - 8*a*k^2 - 18*b^2*p + 9*b*f*n - 9*b*g*m
        + 6*b*j*k + 6*c*f*m - 4*c*j^2 - 3*f^2*l + f*g*k - 4*f*h*j + g^2*j)*X^4*Z^2
        + (24*a*d*l + 48*a*e*k - 24*a*h*i - 4*b*c*l + 6*b*d*k + 24*b*e*j - 2*b*h^2 - 4*c^2*k
        - 4*c*d*j + 12*c*f*i + 4*c*g*h - 2*d*g^2 - 24*e*f*g)*X^3*Y^3
        + (72*a*d*n + 144*a*e*m - 24*a*h*l - 12*b*c*n + 18*b*d*m - 4*b*g*l - 2*b*h*k + 24*b*i*j
        - 12*c^2*m + 20*c*f*l + 4*c*h*j + 6*d*f*k - 12*d*g*j - 24*e*f*j - 12*f*g*i - 2*f*h^2 + 2*g^2*h)*X^3*Y^2*Z
        + (144*a*d*p + 72*a*i*m - 24*a*k*l - 24*b*c*p - 12*b*g*n + 6*b*h*m + 20*b*j*l
        - 2*b*k^2 + 24*c*f*n - 12*c*g*m + 4*c*j*k + 18*d*f*m - 12*d*j^2 - 4*f*g*l - 2*f*h*k
        - 12*f*i*j + 2*g^2*k)*X^3*Y*Z^2
        + (48*a*h*p - 24*a*k*n + 24*a*l*m - 24*b*g*p + 12*b*j*n + 24*c*f*p - 4*c*j*m
        + 6*f*h*m - 4*f*j*l - 2*f*k^2 - 2*g^2*m + 4*g*j*k - 4*h*j^2)*X^3*Z^3
        + (48*a*e*l - 18*a*i^2 + 6*b*d*l + 24*b*e*k - 9*b*h*i - 4*c^2*l - 4*c*d*k + 8*c*e*j
        + 6*c*g*i + c*h^2 - 3*d^2*j + 9*d*f*i + d*g*h - 12*e*f*h - 8*e*g^2)*X^2*Y^4
        + (144*a*e*n - 24*a*i*l + 18*b*d*n + 72*b*e*m - 12*b*h*l + 6*b*i*k - 12*c^2*n
        - 12*c*d*m + 4*c*g*l + 20*c*i*j + 24*d*f*l - 2*d*g*k - 4*d*h*j - 24*e*g*j
        - 12*f*h*i - 2*g^2*i + 2*g*h^2)*X^2*Y^3*Z
        + (288*a*e*p + 36*a*i*n - 24*a*l^2 + 36*b*d*p - 9*b*h*n + 45*b*i*m - 6*b*k*l
        - 24*c^2*p - 6*c*g*n - 6*c*h*m + 24*c*j*l + 45*d*f*n - 9*d*g*m - 6*d*j*k
        + 36*e*f*m - 24*e*j^2 - 6*f*h*l - 9*f*i*k + 3*g*h*k - 6*g*i*j)*X^2*Y^2*Z^2
        + (144*a*i*p - 24*a*l*n - 12*b*k*n + 24*b*l*m - 24*c*g*p + 20*c*j*n - 4*c*k*m
        + 72*d*f*p - 12*d*j*m + 6*f*h*n + 18*f*i*m - 12*f*k*l - 2*g^2*n - 2*g*h*m
        + 4*g*j*l + 2*g*k^2 - 12*i*j^2)*X^2*Y*Z^3
        + (48*a*l*p - 18*a*n^2 - 12*b*k*p + 9*b*m*n + 8*c*j*p - 3*c*m^2 + 24*f*h*p
	- 9*f*k*n + 6*f*l*m - 8*g^2*p + 6*g*j*n + g*k*m - 4*h*j*m - 4*j^2*l + j*k^2)*X^2*Z^4
	+ (24*b*e*l - 9*b*i^2 - 4*c*d*l + 8*c*e*k - 3*d^2*k + 6*d*g*i + d*h^2 - 8*e*g*h)*X*Y^5
	+ (72*b*e*n - 12*b*i*l - 12*c*d*n + 24*c*e*m - 4*c*h*l + 8*c*i*k - 9*d^2*m
	+ 8*d*g*l - 2*d*h*k + 12*d*i*j + 24*e*f*l - 8*e*g*k - 16*e*h*j - 9*f*i^2
	- 2*g*h*i + h^3)*X*Y^4*Z
	+ (144*b*e*p + 18*b*i*n - 12*b*l^2 - 24*c*d*p - 12*c*h*n + 24*c*i*m + 4*c*k*l
	+ 6*d*g*n - 12*d*h*m + 20*d*j*l - 2*d*k^2 + 72*e*f*n - 24*e*j*k - 12*f*i*l
	- 2*g*i*k + 2*h^2*k - 4*h*i*j)*X*Y^3*Z^2
	+ (72*b*i*p - 12*b*l*n - 24*c*h*p - 4*c*k*n + 20*c*l*m + 24*d*j*n - 12*d*k*m
	+ 144*e*f*p - 24*e*j*m + 18*f*i*n - 12*f*l^2 - 2*g*h*n + 6*g*i*m - 2*h^2*m
	+ 4*h*j*l + 2*h*k^2 - 12*i*j*k)*X*Y^2*Z^3
	+ (24*b*l*p - 9*b*n^2 - 16*c*k*p + 12*c*m*n + 24*d*j*p - 9*d*m^2 + 72*f*i*p
	- 12*f*l*n - 8*g*h*p - 2*g*k*n + 8*g*l*m + 8*h*j*n - 2*h*k*m
	- 12*i*j*m - 4*j*k*l + k^3)*X*Y*Z^4
	+ (24*f*l*p - 9*f*n^2 - 8*g*k*p + 6*g*m*n + 8*h*j*p - 3*h*m^2 - 4*j*l*m + k^2*m)*X*Z^5
	+ (8*c*e*l - 3*c*i^2 - 3*d^2*l + 3*d*h*i - 2*e*h^2)*Y^6
	+ (24*c*e*n - 4*c*i*l - 9*d^2*n + 6*d*i*k + 8*e*g*l - 8*e*h*k - 3*g*i^2 + h^2*i)*Y^5*Z
	+ (48*c*e*p + 6*c*i*n - 4*c*l^2 - 18*d^2*p - 9*d*h*n + 9*d*i*m + 6*d*k*l
	+ 24*e*g*n - 12*e*h*m + 8*e*j*l - 8*e*k^2 - 4*g*i*l + h^2*l + h*i*k - 3*i^2*j)*Y^4*Z^2
	+ (24*c*i*p - 4*c*l*n - 24*d*h*p + 12*d*l*m + 48*e*g*p + 24*e*j*n - 24*e*k*m + 6*g*i*n
	- 4*g*l^2 - 2*h^2*n + 4*h*k*l - 4*i*j*l - 2*i*k^2)*Y^3*Z^3
	+ (8*c*l*p - 3*c*n^2 - 12*d*k*p + 9*d*m*n + 48*e*j*p - 18*e*m^2 + 24*g*i*p - 4*g*l*n
	- 8*h^2*p + h*k*n + 6*h*l*m + 6*i*j*n - 9*i*k*m - 4*j*l^2 + k^2*l)*Y^2*Z^4
	+ (8*g*l*p - 3*g*n^2 - 8*h*k*p + 6*h*m*n + 24*i*j*p - 9*i*m^2 - 4*j*l*n + k^2*n)*Y*Z^5
	+ (8*j*l*p - 3*j*n^2 - 2*k^2*p + 3*k*m*n - 3*l*m^2)*Z^6;
    return He;
end function;

function ContravariantIntegralSigmaAndPsi(Phi)
    // Input: Homogeneous ternary quartic.
    // Output: Contravariants Sigma and Psi of Dixmier & Ohno
    // (Salmon 3rd ed. p. 78). These should really be in the
    // dual ring PUVW, but we return them in PXYZ.
    PXYZ := Parent(Phi);
    XYZ_orig := [ PXYZ.i : i in [1..3] ];
    K := BaseRing(PXYZ);
    PUVW<u,v,w> := PolynomialRing(K,3);
    PXYZUVW<X,Y,Z> := PolynomialRing(PUVW,3);
    L := u*X + v*Y + w*Z;
    Q := Evaluate(Phi,[X,Y,Z]);
    R := Resultant(Q,L,3);
    // This definition of Psi follows Dixmier; there is also
    // the 'symbolic notation' of Salmon, p. 78 & p. 271 as 
    // \psi = (a12)^2(a23)^2(a31)^2.
    A := 12*MonomialCoefficient(R,X^4);
    B :=  3*MonomialCoefficient(R,X^3*Y);
    C :=  2*MonomialCoefficient(R,X^2*Y^2);
    D :=  3*MonomialCoefficient(R,Y^3*X);
    E := 12*MonomialCoefficient(R,Y^4);
    Psi := Determinant(Matrix(3,[A,B,C,B,C,D,C,D,E]));
    Psi := Evaluate(Numerator(Psi/w^Max(TotalDegree(Psi)-6,0)),XYZ_orig);
    // This definition of Sigma follows Salmon's 'symbolic notation' (a12)^4.
    Pxy<x,y> := PolynomialRing(PUVW,2);
    Rxy := Evaluate(R,[x,y,0]);
    Sigma := PUVW!Coefficients(Transvectant(Rxy,Rxy,4))[1]; 
    //Sigma := Evaluate(Sigma/2 div w^(TotalDegree(Sigma)-4),XYZ_orig);
    Sigma := Evaluate(Numerator(Sigma/w^Max(TotalDegree(Sigma)-4,0)),XYZ_orig);
    return Sigma, Psi;
end function;

intrinsic QuarticIntegralCovariantsAndContravariants(Phi::RngMPolElt) -> SeqEnum
    {}
    P := Parent(Phi);
    K := BaseRing(P);
    require Rank(P) eq 3 and IsHomogeneous(Phi) and TotalDegree(Phi) eq 4 : 
        "Argument must be a homogeneous ternary quartic polynomial.";
    X := P.1; Y := P.2; Z := P.3;
    // Phi itself is a contravariant:
    // Phi:   deg = 1, ord = 4
    // 
    // Contravariants:
    Sigma, Psi := ContravariantIntegralSigmaAndPsi(Phi);
    Rho := DifferentialOperation(Phi,Psi);
    // Sigma: deg = 2, ord = 4
    // Psi:   deg = 3, ord = 6
    // Rho:   deg = 4, ord = 2
    // Covariants:
    He := CovariantIntegralHessian(Phi); // deg = 3, ord = 6
    Tau := DifferentialOperation(Rho,Phi);
    Xi := DifferentialOperation(Sigma,He);
    // He:    deg = 3, ord = 6
    // Tau:   deg = 5, ord = 2
    // Xi:    deg = 5, ord = 2
    // More contravariants:
    Eta := DifferentialOperation(Xi,Sigma);
    Chi := DifferentialOperation(Tau,DifferentialOperation(Tau,Psi));
    // Eta:   deg = 7, ord = 2
    // Chi:   deg =13, ord = 2
    // More covariants:
    Nu := DifferentialOperation(Eta,DifferentialOperation(Rho,He));
    // Chi:   deg =14, ord = 2
    return [ Phi, He, Tau, Xi, Nu ], [ Sigma, Psi, Rho, Eta, Chi ]; 
end intrinsic;

intrinsic DixmierOhnoIntegralInvariants(Phi::RngMPolElt) -> SeqEnum
    {Dixmier-Ohno quartic invariants (I3 : I6 : I9 : J9 : I12 : J12 :
    I15 : J15 : I18 : J18 : I21 : J21 : I27); the subset of indices
    [ 1, 2, 3, 5, 7, 9, 13] are the Dixmier invariants.}
    
    P := Parent(Phi);
    K := BaseRing(P);
    require Rank(P) eq 3 and IsHomogeneous(Phi) and TotalDegree(Phi) eq 4 : 
        "Argument must be a homogeneous ternary quartic polynomial.";
    X := P.1; Y := P.2; Z := P.3;
    // Phi itself is a contravariant:
    // Phi:   deg = 1, ord = 4
    // 
    // Contravariants:
    Sigma, Psi := ContravariantIntegralSigmaAndPsi(Phi);
    Rho := DifferentialOperation(Phi,Psi);
    // Sigma: deg = 2, ord = 4
    // Psi:   deg = 3, ord = 6
    // Rho:   deg = 4, ord = 2
    // Covariants:
    He := CovariantIntegralHessian(Phi); // deg = 3, ord = 6
    Tau := DifferentialOperation(Rho,Phi);
    Xi := DifferentialOperation(Sigma,He);
    // He:    deg = 3, ord = 6
    // Tau:   deg = 5, ord = 2
    // Xi:    deg = 5, ord = 2
    // More contravariants:
    Eta := DifferentialOperation(Xi,Sigma);
    Chi := DifferentialOperation(Tau,DifferentialOperation(Tau,Psi));
    // Eta:   deg = 7, ord = 2
    // Chi:   deg =13, ord = 2
    // More covariants:
    Nu := DifferentialOperation(Eta,DifferentialOperation(Rho,He));
    // Chi:   deg =14, ord = 2
    // Covariants: [ Phi, He, Tau, Xi, Nu ],
    // Contravars: [ Sigma, Psi, Rho, Eta, Chi ]; 
    I03 := DixmierIntegralInvariant(Phi,3);
    // assert 72*I03 eq DifferentialOperation(Phi,Sigma);
    // assert 144*I03 eq DifferentialOperation(Phi,Sigma);
    assert 144*I03 eq DifferentialOperation(Sigma,Phi);
    I06 := DixmierIntegralInvariant(Phi,6);
    J06 := DifferentialOperation(Psi,He);
    assert 13824*I03^2 + 7962624*I06 + J06 eq 0;
    I09 := KOperation11(Tau,Rho);
    J09 := KOperation11(Xi,Rho); // Ohno
    I12 := KOperation03(Rho);
    J12 := KOperation11(Tau,Eta); // Ohno
    I15 := KOperation30(Tau);
    J15 := KOperation30(Xi); // Ohno
    I18 := KOperation22(Tau,Rho);
    J18 := KOperation22(Xi,Rho); // Ohno
    I21 := KOperation03(Eta); // Ohno
    J21 := KOperation11(Nu,Eta); // Ohno
    I27 := QuarticDiscriminant(Phi);
    J27 := KOperation11(Nu,Chi);  // Ohno (not given named)
    return [I03,I06,I09,J09,I12,J12,I15,J15,I18,J18,I21,J21,I27,J27];
end intrinsic;

intrinsic DixmierIntegralInvariant(Phi::RngMPolElt,r::RngIntElt) -> RngElt
    {Dixmier quartic invariant I_r where r in [3,6,9,12,15,18,27].}
    
    require r mod 3 eq 0 : "Argument 2 must be 0 mod 3.";
    require r in {3,6,9,12,15,18,27} :
        "Argument 2 must be in 3,6,9,12,15,18,27.";
    P := Parent(Phi);
    K := BaseRing(P);
    require Rank(P) eq 3 and IsHomogeneous(Phi) and TotalDegree(Phi) eq 4 : 
        "Argument must be a homogeneous ternary quartic polynomial.";
    if r eq 27 then return QuarticDiscriminant(Phi); end if;
    X := P.1; Y := P.2; Z := P.3;
    
    a := MonomialCoefficient(Phi,X^4);
    b := MonomialCoefficient(Phi,X^3*Y);
    c := MonomialCoefficient(Phi,X^2*Y^2);
    d := MonomialCoefficient(Phi,Y^3*X);
    e := MonomialCoefficient(Phi,Y^4);
    f := MonomialCoefficient(Phi,X^3*Z);
    g := MonomialCoefficient(Phi,X^2*Y*Z);
    h := MonomialCoefficient(Phi,X*Y^2*Z);
    i := MonomialCoefficient(Phi,Y^3*Z);
    j := MonomialCoefficient(Phi,X^2*Z^2);
    k := MonomialCoefficient(Phi,X*Y*Z^2);
    l := MonomialCoefficient(Phi,Y^2*Z^2);
    m := MonomialCoefficient(Phi,X*Z^3);
    n := MonomialCoefficient(Phi,Z^3*Y);
    p := MonomialCoefficient(Phi,Z^4);

    if r eq 3 then
	I03 := 144*a*e*p - 36*a*i*n + 12*a*l^2 - 36*b*d*p + 9*b*h*n + 9*b*i*m
            - 6*b*k*l + 12*c^2*p - 6*c*g*n - 6*c*h*m + 4*c*j*l + 2*c*k^2
            + 9*d*f*n + 9*d*g*m - 6*d*j*k - 36*e*f*m + 12*e*j^2 - 6*f*h*l
            + 9*f*i*k + 2*g^2*l - g*h*k - 6*g*i*j + 2*h^2*j;
        return I03;
    elif r eq 6 then
        I06 := Determinant(Matrix([
            [12*a,  2*c,  2*j,   g,  3*f,  3*b], 
            [ 2*c, 12*e,  2*l, 3*i,    h,  3*d],
            [ 2*j,  2*l, 12*p, 3*n,  3*m,    k],
            [   g,  3*i,  3*n, 2*l,    k,    h],
            [ 2*f,    h,  3*m,   k,   2*j,   g],
            [ 3*b,  3*d,    k,   h,     g, 2*c] ]));
        return I06;
    end if;
    
    K := BaseRing(Parent(Phi));
    PUVW<u,v,w> := PolynomialRing(K,3);
    PXYZUVW<x,y,z> := PolynomialRing(PUVW,3);
    Q := Evaluate(Phi,[x,y,z]);
    L := u*x+v*y+w*z;
    
    R := Resultant(Q,L,3);
    A0 := 12*MonomialCoefficient(R,x^4);
    B0 :=  3*MonomialCoefficient(R,x^3*y);
    C0 :=  2*MonomialCoefficient(R,x^2*y^2);
    D0 :=  3*MonomialCoefficient(R,y^3*x);
    E0 := 12*MonomialCoefficient(R,y^4);
    
    Psi := Determinant(Matrix([[A0,B0,C0],[B0,C0,D0],[C0,D0,E0]]));
    Psi := PUVW!Numerator(Psi/w^Max(TotalDegree(Psi)-6,0));
    
    Rho := DifferentialOperation(Phi,Psi);
    Tau := DifferentialOperation(Rho,Phi);
    
    A1 := 2*MonomialCoefficient(Tau,X^2);
    B1 := MonomialCoefficient(Tau,X*Y);
    C1 := 2*MonomialCoefficient(Tau,Y^2);
    D1 := MonomialCoefficient(Tau,X*Z);
    E1 := MonomialCoefficient(Tau,Y*Z);
    F1 := 2*MonomialCoefficient(Tau,Z^2);
    
    A2 := 2*MonomialCoefficient(Rho,u^2);
    B2 := MonomialCoefficient(Rho,u*v);
    C2 := 2*MonomialCoefficient(Rho,v^2);
    D2 := MonomialCoefficient(Rho,u*w);
    E2 := MonomialCoefficient(Rho,v*w);
    F2 := 2*MonomialCoefficient(Rho,w^2);
    
    if r eq 9 then
        I9 := A1*A2+2*B1*B2+C1*C2+2*D1*D2+2*E1*E2+F1*F2;
        return K!I9;
    elif r eq 12 then
        I12 := Determinant(Matrix(3,3,[A2,B2,D2,B2,C2,E2,D2,E2,F2]));
        return K!I12;
    elif r eq 15 then
        I15 := Determinant(Matrix(3,3,[A1,B1,D1,B1,C1,E1,D1,E1,F1]));
        return K!I15;
    elif r eq 18 then
        I18 := (E1^2-C1*F1)*(E2^2-C2*F2)+2*(B1*F1-D1*E1)*(B2*F2-D2*E2)
            + (D1^2-A1*F1)*(D2^2-A2*F2) + 2*(C1*D1-B1*E1)*(C2*D2-B2*E2)
            + 2*(A1*E1-B1*D1)*(A2*E2-B2*D2)+(B1^2-A1*C1)*(B2^2-A2*C2);
        return K!I18;
    end if;
end intrinsic;

intrinsic DixmierIntegralInvariants(Phi::RngMPolElt) -> SeqEnum
    {Dixmier quartic invariants (I3 : I6 : I9 : I12 : I15 : I18 : I27).}
    
    P := Parent(Phi);
    K := BaseRing(P);
    require IsUnit(K!12) :
        "Argument must be a polynomial over a ring in which 2 and 3 are units.";
    require Rank(P) eq 3 and IsHomogeneous(Phi) and TotalDegree(Phi) eq 4 : 
        "Argument must be a homogeneous ternary quartic polynomial.";
    X := P.1; Y := P.2; Z := P.3;
    
    a0 := MonomialCoefficient(Phi,X^4);
    b0 := (1/4)*MonomialCoefficient(Phi,X^3*Y);
    c0 := (1/6)*MonomialCoefficient(Phi,X^2*Y^2);
    d0 := (1/4)*MonomialCoefficient(Phi,Y^3*X);
    e0 := MonomialCoefficient(Phi,Y^4);
    f0 := (1/4)*MonomialCoefficient(Phi,X^3*Z);
    g0 := (1/12)*MonomialCoefficient(Phi,X^2*Y*Z);
    h0 := (1/12)*MonomialCoefficient(Phi,X*Y^2*Z);
    i0 := (1/4)*MonomialCoefficient(Phi,Y^3*Z);
    j0 := (1/6)*MonomialCoefficient(Phi,X^2*Z^2);
    k0 := (1/12)*MonomialCoefficient(Phi,X*Y*Z^2);
    l0 := (1/6)*MonomialCoefficient(Phi,Y^2*Z^2);
    m0 := (1/4)*MonomialCoefficient(Phi,X*Z^3);
    n0 := (1/4)*MonomialCoefficient(Phi,Z^3*Y);
    p0 := MonomialCoefficient(Phi,Z^4);
    
    vprint Dixmier : "Computing invariants...";
    I03 := a0*e0*p0
        + 3*(a0*l0^2+e0*j0^2+p0*c0^2)
        + 4*(b0*i0*m0+f0*d0*n0)
        - 4*(a0*i0*n0+e0*f0*m0+p0*b0*d0)
        + 6*c0*j0*l0
        + 12*(c0*k0^2+j0*h0^2+l0*g0^2)
        - 12*g0*h0*k0
        - 12*(b0*k0*l0+f0*h0*l0+d0*k0*j0+i0*g0*j0+m0*h0*c0+n0*g0*c0)
        + 12*(g0*d0*m0+h0*n0*b0+k0*f0*i0);
    // print "I03:"; I03;
    vprint Dixmier : "...I03;";
    
    I06 := Determinant(M) where M :=Matrix(6,6, [
        a0,c0,j0,g0,f0,b0,
        c0,e0,l0,i0,h0,d0,
        j0,l0,p0,n0,m0,k0,
        g0,i0,n0,l0,k0,h0,
        f0,h0,m0,k0,j0,g0,
        b0,d0,k0,h0,g0,c0]);
    // print "I06:"; I06;
    vprint Dixmier : "...I06;";
    
    PXYZ := Parent(Phi);
    XYZ_orig := [ PXYZ.i : i in [1..3] ];
    K := BaseRing(Parent(Phi));
    PUVW<u,v,w> := PolynomialRing(K,3);
    PXYZUVW<X,Y,Z> := PolynomialRing(PUVW,3);
    Phi := Evaluate(Phi,[X,Y,Z]);
    L := u*X+v*Y+w*Z;
    Q := Evaluate(Phi,[X,Y,Z]);
    R := Resultant(Q,L,3);
    
    A := 12*MonomialCoefficient(R,X^4);
    B :=  3*MonomialCoefficient(R,X^3*Y);
    C :=  2*MonomialCoefficient(R,X^2*Y^2);
    D :=  3*MonomialCoefficient(R,Y^3*X);
    E := 12*MonomialCoefficient(R,Y^4);
    Psi := Determinant(Matrix(3,[A,B,C,B,C,D,C,D,E]));
    Psi := Evaluate(Numerator(Psi/w^Max(TotalDegree(Psi)-6,0)),XYZ_orig);
    
    Rho := DifferentialOperation(Phi,Psi);
    Tau := DifferentialOperation(Rho,Phi);
    
    A1 := MonomialCoefficient(Tau,X^2);
    B1 := (1/2)*MonomialCoefficient(Tau,X*Y);
    C1 := MonomialCoefficient(Tau,Y^2);
    D1 := (1/2)*MonomialCoefficient(Tau,X*Z);
    E1 := (1/2)*MonomialCoefficient(Tau,Y*Z);
    F1 := MonomialCoefficient(Tau,Z^2);
    
    A2 := MonomialCoefficient(Rho,u^2);
    B2 := (1/2)*MonomialCoefficient(Rho,u*v);
    C2 := MonomialCoefficient(Rho,v^2);
    D2 := (1/2)*MonomialCoefficient(Rho,u*w);
    E2 := (1/2)*MonomialCoefficient(Rho,v*w);
    F2 := MonomialCoefficient(Rho,w^2);
    
    I09 := A1*A2+2*B1*B2+C1*C2+2*D1*D2+2*E1*E2+F1*F2;
    // print "I09:"; I09; "(=I09)";
    vprint Dixmier : "...I09;";
    
    I12 := Determinant(Matrix(3,3,[A2,B2,D2,B2,C2,E2,D2,E2,F2]));
    // print "I12:"; I12; "(=I12)";
    vprint Dixmier : "...I12;";
    
    I15 := Determinant(Matrix(3,3,[A1,B1,D1,B1,C1,E1,D1,E1,F1]));
    // print "I15:"; I15; "(=I15)";
    vprint Dixmier : "...I15;";
    
    I18 := (E1^2-C1*F1)*(E2^2-C2*F2)+2*(B1*F1-D1*E1)*(B2*F2-D2*E2)
        + (D1^2-A1*F1)*(D2^2-A2*F2) + 2*(C1*D1-B1*E1)*(C2*D2-B2*E2)
        + 2*(A1*E1-B1*D1)*(A2*E2-B2*D2)+(B1^2-A1*C1)*(B2^2-A2*C2);
    // print "I18:"; I18; "(=I18)";
    vprint Dixmier : "...I18;";
    
    D := Derivative;
    
    C1 := Derivative(Phi,X);
    C2 := Derivative(Phi,Y);
    C3 := Derivative(Phi,Z);
    
    Jd := Determinant(Matrix(PXYZUVW,
        [
        [D(C1,X),D(C1,Y),D(C1,Z)],
        [D(C2,X),D(C2,Y),D(C2,Z)],
        [D(C3,X),D(C3,Y),D(C3,Z)]
        ]));
    
    Jd1 := D(Jd,X);
    Jd2 := D(Jd,Y);
    Jd3 := D(Jd,Z);
    
    C1X2 := X^2*C1;
    C2X2 := X^2*C2;
    C3X2 := X^2*C3;
    C1Y2 := Y^2*C1;
    C2Y2 := Y^2*C2;
    C3Y2 := Y^2*C3;
    C1Z2 := Z^2*C1;
    C2Z2 := Z^2*C2;
    C3Z2 := Z^2*C3;
    C1YZ := Y*Z*C1;
    C2YZ := Y*Z*C2;
    C3YZ := Y*Z*C3;
    C1ZX := Z*X*C1;
    C2ZX := Z*X*C2;
    C3ZX := Z*X*C3;
    C1XY := Y*X*C1;
    C2XY := Y*X*C2;
    C3XY := Y*X*C3;
    
    Eqq := [Jd1,Jd2,Jd3,C1X2,C2X2,C3X2,C1Y2,C2Y2,C3Y2,C1Z2,C2Z2,C3Z2,C1YZ,
        C2YZ,C3YZ,C1ZX,C2ZX,C3ZX,C1XY,C2XY,C3XY];
    
    L := [
        X^5,
        X^4*Y,
        X^4*Z,
        X^3*Y^2,
        X^3*Y*Z,
        X^3*Z^2,
        X^2*Y^3,
        X^2*Y^2*Z,
        X^2*Y*Z^2,
        X^2*Z^3,
        X*Y^4,
        X*Y^3*Z,
        X*Y^2*Z^2,
        X*Y*Z^3,
        X*Z^4,
        Y^5,
        Y^4*Z,
        Y^3*Z^2,
        Y^2*Z^3,
        Y*Z^4,
        Z^5
        ];
    
    M := [[MonomialCoefficient(Eqql,Ll): Ll in L]: Eqql in Eqq];
    
    R := Matrix(K,M);
    vprint Dixmier : "...R27 (computing determinant);";
    
    I27 := Determinant(R);
    return [K|I03,I06,I09,I12,I15,I18,I27];
    // PP := ProjectiveSpace(K,[1,2,3,4,5,6,9]);
    // return PP(K)![K|I03,I06,I09,I12,I15,I18,I27];
    return [ K |
        I06/I03^2, I09/I03^3, I12/I03^4, I15/I03^5, I18/I03^6, I27/I03^9 ];
end intrinsic;

function QuarticDiscriminant(Phi)
    P := Parent(Phi);
    K := BaseRing(P);
    X,Y,Z := Explode([ P.i : i in [1..3] ]);
    
    C1 := Derivative(Phi,X);
    C2 := Derivative(Phi,Y);
    C3 := Derivative(Phi,Z);
    
    C1X2 := X^2*C1;
    C2X2 := X^2*C2;
    C3X2 := X^2*C3;
    C1Y2 := Y^2*C1;
    C2Y2 := Y^2*C2;
    C3Y2 := Y^2*C3;
    C1Z2 := Z^2*C1;
    C2Z2 := Z^2*C2;
    C3Z2 := Z^2*C3;
    C1YZ := Y*Z*C1;
    C2YZ := Y*Z*C2;
    C3YZ := Y*Z*C3;
    C1ZX := Z*X*C1;
    C2ZX := Z*X*C2;
    C3ZX := Z*X*C3;
    C1XY := Y*X*C1;
    C2XY := Y*X*C2;
    C3XY := Y*X*C3;
    
    He := CovariantIntegralHessian(Phi);
    DHe1 := Derivative(He,X);
    DHe2 := Derivative(He,Y);
    DHe3 := Derivative(He,Z);
    
    Eqq := [
        DHe1,DHe2,DHe3,
        C1X2,C2X2,C3X2,
        C1Y2,C2Y2,C3Y2,
        C1Z2,C2Z2,C3Z2,
        C1YZ,C2YZ,C3YZ,
        C1ZX,C2ZX,C3ZX,
        C1XY,C2XY,C3XY];
    
    L := [
        X^5,
        X^4*Y,
        X^4*Z,
        X^3*Y^2,
        X^3*Y*Z,
        X^3*Z^2,
        X^2*Y^3,
        X^2*Y^2*Z,
        X^2*Y*Z^2,
        X^2*Z^3,
        X*Y^4,
        X*Y^3*Z,
        X*Y^2*Z^2,
        X*Y*Z^3,
        X*Z^4,
        Y^5,
        Y^4*Z,
        Y^3*Z^2,
        Y^2*Z^3,
        Y*Z^4,
        Z^5
        ];
    return Determinant(
        Matrix(K,[ [ MonomialCoefficient(Ei,Li) : Li in L ] : Ei in Eqq ]));
end function;
