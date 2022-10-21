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


function DifferentialOperation(F,G)
    mons := Monomials(F);
    cffs := Coefficients(F);
    DG := Parent(G)!0;
    for i in [1..#cffs] do
	DG +:= cffs[i]*PowerDerivative(G,Exponents(mons[i]));
    end for;
    return DG;
end function;


function JOperation11(F,G)
    X,Y,Z := Explode([ P.i : i in [1..3] ]) where P := Parent(F);
    ww := [  1,  1/2,  1,  1/2, 1/2,  1  ];
    XX := [ X^2, X*Y, Y^2, Y*Z, X*Z, Z^2 ];
    FF := [ MonomialCoefficient(F,M) : M in XX ];
    GG := [ MonomialCoefficient(G,M) : M in XX ];
    return &+[ ww[i]*FF[i]*GG[i] : i in [1..6] ]; 
end function;


function JOperation22(F,G)
    P := Parent(F);
    K := BaseRing(P);
    X,Y,Z := Explode([ P.i : i in [1..3] ]);
    A := MatrixAlgebra(K,3)!0;
    B := MatrixAlgebra(K,3)!0;
    for i in [1..3] do
	A[i,i] := MonomialCoefficient(F,P.i^2);
	B[i,i] := MonomialCoefficient(G,P.i^2);
	for j in [i+1..3] do
	    A[i,j] := MonomialCoefficient(F,P.i*P.j)/2;
	    A[j,i] := A[i,j];
	    B[i,j] := MonomialCoefficient(G,P.i*P.j)/2;
	    B[j,i] := B[i,j];
	end for;
    end for;
    Astar := Eltseq(Adjoint(A));
    Bstar := Eltseq(Adjoint(B));
    return &+[ Astar[i]*Bstar[i] : i in [1..9] ];
end function;


function JOperation30(F)
    P := Parent(F);
    K := BaseRing(P);
    X,Y,Z := Explode([ P.i : i in [1..3] ]);
    A := MatrixAlgebra(K,3)!0;
    for i in [1..3] do
	A[i,i] := MonomialCoefficient(F,P.i^2);
	for j in [i+1..3] do
	    A[i,j] := MonomialCoefficient(F,P.i*P.j)/2;
	    A[j,i] := A[i,j];
	end for;
    end for;
    return K!Determinant(A);
end function;


function JOperation03(G)
    return JOperation30(G);
end function;


intrinsic CovariantHessian(Phi::RngMPolElt) -> RngMPolElt
    {}
    require Rank(Parent(Phi)) eq 3 and IsHomogeneous(Phi) : 
	"Argument must be a homogeneous ternary forms.";
    DPhi_i := [ Derivative(Phi,i) : i in [1..3] ];
    DPhi_ij := MatrixAlgebra(Parent(Phi),3)!0;
    for i in [1..3] do
	DPhi_ij[i,i] := Derivative(DPhi_i[i],i);
	for j in [i+1..3] do
	    DPhi_ij[i,j] := Derivative(DPhi_i[i],j);
	    DPhi_ij[j,i] := DPhi_ij[i,j];
	end for;
    end for;
    return Determinant(DPhi_ij);
end intrinsic;


intrinsic ContravariantSigmaAndPsi(Phi::RngMPolElt) -> RngMPolElt, RngMPolElt
    {}
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
    R := (-1)^Degree(Q,Z)*Resultant(Q,L,Z);
    // This definition of Psi follows Dixmier; there is also
    // the 'symbolic notation' of Salmon, p. 78 & p. 271 as 
    // \psi = (a12)^2(a23)^2(a31)^2.
    A := MonomialCoefficient(R,X^4);
    B := (1/4)*MonomialCoefficient(R,X^3*Y);
    C := (1/6)*MonomialCoefficient(R,X^2*Y^2);
    D := (1/4)*MonomialCoefficient(R,Y^3*X);
    E := MonomialCoefficient(R,Y^4);
    Psi := Determinant(Matrix(3,[A,B,C,B,C,D,C,D,E]));
    //Psi := Evaluate(Numerator(Psi/w^(TotalDegree(Psi)-6)),XYZ_orig);
    totdeg := TotalDegree(Psi)-6;
    if totdeg ge 0 then
        Psi := Evaluate(PUVW!(Psi/w^totdeg),XYZ_orig);
    else
        Psi := Evaluate(PUVW!(Psi*w^(-totdeg)),XYZ_orig);
    end if;
    // This definition of Sigma follows Salmon's 'symbolic notation' (a12)^4.
    Pxy<x,y> := PolynomialRing(PUVW,2);
    Rxy := Evaluate(R,[x,y,0]);
    Sigma := (1/2)*PUVW!Coefficients(Transvectant(Rxy,Rxy,4))[1]; 
    //Sigma := Evaluate(Numerator(Sigma/w^(TotalDegree(Sigma)-4)),XYZ_orig);
    totdeg := TotalDegree(Sigma)-4;
    if totdeg ge 0 then
        Sigma := Evaluate(PUVW!(Sigma/w^totdeg),XYZ_orig);
    else
        Sigma := Evaluate(PUVW!(Sigma*w^(-totdeg)),XYZ_orig);
    end if;
    return Sigma, Psi;
end intrinsic;


function QuarticDiscriminant(Phi)
    P := Parent(Phi);
    K := BaseRing(P);
    X,Y,Z := Explode([ P.i : i in [1..3] ]);

    CLASSICAL := true;

    if CLASSICAL then
	C1 := (1/4)*Derivative(Phi,X);
	C2 := (1/4)*Derivative(Phi,Y);
	C3 := (1/4)*Derivative(Phi,Z);
    else
	C1 := Derivative(Phi,X);
	C2 := Derivative(Phi,Y);
	C3 := Derivative(Phi,Z);
    end if;
    
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
    C1XY := X*Y*C1;
    C2XY := X*Y*C2;
    C3XY := X*Y*C3;

    if CLASSICAL then
	He := (1/1728)*CovariantHessian(Phi);
    else
	He := (1/54)*CovariantHessian(Phi);
    end if;

    if CLASSICAL then
	DHe1 := (1/2)*Derivative(He,X);
	DHe2 := (1/2)*Derivative(He,Y);
	DHe3 := (1/2)*Derivative(He,Z);
    else
	DHe1 := Derivative(He,X);
	DHe2 := Derivative(He,Y);
	DHe3 := Derivative(He,Z);
    end if;

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
    R27 := Matrix(K,[ [MonomialCoefficient(Eqql,Ll): Ll in L]: Eqql in Eqq ]);
    return Determinant(R27);
end function;


intrinsic QuarticCovariantsAndContravariants(Phi::RngMPolElt) -> SeqEnum
    {}
    P := Parent(Phi);
    K := BaseRing(P);
    require IsUnit(K!12) :
	"Argument must be a polynomial over a ring in which 2 and 3 are units.";
    require Rank(P) eq 3 and IsHomogeneous(Phi) and TotalDegree(Phi) eq 4 : 
	"Argument must be a homogeneous ternary quartic polynomial.";
    X := P.1; Y := P.2; Z := P.3;
    // Phi itself is a contravariant:
    // Phi:   deg = 1, ord = 4
    // 
    // Contravariants:
    Sigma, Psi := ContravariantSigmaAndPsi(Phi);
    Rho := (1/144)*DifferentialOperation(Phi,Psi);
    // Sigma: deg = 2, ord = 4
    // Psi:   deg = 3, ord = 6
    // Rho:   deg = 4, ord = 2
    // Covariants:
    He := (1/1728)*CovariantHessian(Phi); // deg = 3, ord = 6
    Tau := (1/12)*DifferentialOperation(Rho,Phi);
    Xi := (1/72)*DifferentialOperation(Sigma,He);
    // He:    deg = 3, ord = 6
    // Tau:   deg = 5, ord = 2
    // Xi:    deg = 5, ord = 2
    // More contravariants:
    Eta := (1/12)*DifferentialOperation(Xi,Sigma);
    Chi := (1/8)*DifferentialOperation(Tau,DifferentialOperation(Tau,Psi));
    // Eta:   deg = 7, ord = 2
    // Chi:   deg =13, ord = 2
    // More covariants:
    Nu := (1/8)*DifferentialOperation(Eta,DifferentialOperation(Rho,He));
    // Chi:   deg =14, ord = 2
    return [ Phi, He, Tau, Xi, Nu ], [ Sigma, Psi, Rho, Eta, Chi ]; 
end intrinsic;


intrinsic DixmierOhnoInvariants(C::Crv) -> SeqEnum
    {}
    PP := AmbientSpace(C);
    require IsProjective(PP) and Dimension(PP) eq 2 and Degree(C) eq 4 :
	"Argument must be a plane quartic curve.";
    K := BaseRing(C);
    require Characteristic(K) notin {2,3} :
	"Argument must not be defined over a ring of characteristic 2 or 3.";
    return DixmierOhnoInvariants(DefiningPolynomial(C));
end intrinsic;


intrinsic DixmierOhnoInvariants(Phi::RngMPolElt : IntegralNormalization := true) -> SeqEnum
    {Dixmier-Ohno quartic invariants (I3 : I6 : I9 : J9 : I12 : J12 :
    I15 : J15 : I18 : J18 : I21 : J21 : I27); the subset of indices
    [ 1, 2, 3, 5, 7, 9, 13] are the Dixmier invariants.}

    P := Parent(Phi);
    K := BaseRing(P);
    require IsUnit(K!12) :
	"Argument must be a polynomial over a ring in which 2 and 3 are units.";
    require Rank(P) eq 3 and IsHomogeneous(Phi) and TotalDegree(Phi) eq 4 : 
	"Argument must be a homogeneous ternary quartic polynomial.";
    X := P.1; Y := P.2; Z := P.3;
    // Phi itself is a contravariant:
    // Phi:   deg = 1, ord = 4
    // 
    // Contravariants:
    Sigma, Psi := ContravariantSigmaAndPsi(Phi);
    Rho := (1/144)*DifferentialOperation(Phi,Psi);
    // Sigma: deg = 2, ord = 4
    // Psi:   deg = 3, ord = 6
    // Rho:   deg = 4, ord = 2
    // Covariants:
    He := (1/1728)*CovariantHessian(Phi); // deg = 3, ord = 6
    Tau := (1/12)*DifferentialOperation(Rho,Phi);
    Xi := (1/72)*DifferentialOperation(Sigma,He);
    // He:    deg = 3, ord = 6
    // Tau:   deg = 5, ord = 2
    // Xi:    deg = 5, ord = 2
    // More contravariants:
    Eta := (1/12)*DifferentialOperation(Xi,Sigma);
    Chi := (1/8)*DifferentialOperation(Tau,DifferentialOperation(Tau,Psi));
    // Eta:   deg = 7, ord = 2
    // Chi:   deg =13, ord = 2
    // More covariants:
    Nu := (1/8)*DifferentialOperation(Eta,DifferentialOperation(Rho,He));
    // Chi:   deg =14, ord = 2
    // Covariants: [ Phi, He, Tau, Xi, Nu ],
    // Contravars: [ Sigma, Psi, Rho, Eta, Chi ]; 
    I03 := DixmierInvariant(Phi,3 : IntegralNormalization := false);
    // With classical normalization:
    assert 72*I03 eq DifferentialOperation(Phi,Sigma);
    // but D_Sigma(Phi) is classically integral but not integral:
    // assert I03 eq 2*DifferentialOperation(Sigma,Phi);
    I06 := DixmierInvariant(Phi,6 : IntegralNormalization := false);
    J06 := DifferentialOperation(Psi,He);
    // The sign of the Hessian seems NOT to be invariant.
    assert 8*I03^2 + 4608*I06 in {J06,-J06};
    I09 := JOperation11(Tau,Rho);
    J09 := JOperation11(Xi,Rho); // Ohno
    I12 := JOperation03(Rho);
    J12 := JOperation11(Tau,Eta); // Ohno
    I15 := JOperation30(Tau);
    J15 := JOperation30(Xi); // Ohno
    I18 := JOperation22(Tau,Rho);
    J18 := JOperation22(Xi,Rho); // Ohno
    I21 := JOperation03(Eta); // Ohno
    J21 := JOperation11(Nu,Eta); // Ohno
    I27 := QuarticDiscriminant(Phi);
    J27 := JOperation11(Nu,Chi); // Ohno (not given name) not returned
    ww := [1,2,3,3,4,4,5,5,6,6,7,7,9];
    DD := [I03,I06,I09,J09,I12,J12,I15,J15,I18,J18,I21,J21,I27];
    if IntegralNormalization then
	// I03 -> 144*I03, I06 -> 2985984*I06 are already done
	scale := [ 144, 2985984, 26873856, 8957952, 34828517376, 7739670528,
	    120367356051456, 4458050224128, 17332899271409664, 1925877696823296,
	    831979165027663872, 369768517790072832, 1099511627776 ];
	return [ scale[i]*DD[i] : i in [1..13] ], ww;  
    end if;
    return DD, ww;
end intrinsic;


intrinsic DixmierInvariant(Phi::RngMPolElt,i::RngIntElt : 
    IntegralNormalization := true) -> SeqEnum
    {Dixmier quartic invariant I_i where i in [3,6,9,12,15,18,27].}

    require i mod 3 eq 0 : "Argument 2 must be 0 mod 3.";
    require i in {3,6,9,12,15,18,27} :
	"Argument 2 must be in 3,6,9,12,15,18,27.";
    P := Parent(Phi);
    K := BaseRing(P);
    require IsUnit(K!12) :
	"Argument must be a polynomial over a ring in which 2 and 3 are units.";
    require Rank(P) eq 3 and IsHomogeneous(Phi) and TotalDegree(Phi) eq 4 : 
	"Argument must be a homogeneous ternary quartic polynomial.";
    if i eq 27 then
	I27 := QuarticDiscriminant(Phi);
	if IntegralNormalization then
	    I27 *:= 1099511627776;
	end if;
	return I27;
    end if;
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

    if i eq 3 then
	I03 := a0*e0*p0
	    + 3*(a0*l0^2+e0*j0^2+p0*c0^2)
	    + 4*(b0*i0*m0+f0*d0*n0)
	    - 4*(a0*i0*n0+e0*f0*m0+p0*b0*d0)
	    + 6*c0*j0*l0
	    + 12*(c0*k0^2+j0*h0^2+l0*g0^2)
	    - 12*g0*h0*k0
	    - 12*(b0*k0*l0+f0*h0*l0+d0*k0*j0+i0*g0*j0+m0*h0*c0+n0*g0*c0)
	    + 12*(g0*d0*m0+h0*n0*b0+k0*f0*i0);
	if IntegralNormalization then
	    I03 *:= 144;
	end if;
	return I03;
    elif i eq 6 then
	I06 := Determinant(M) where M :=Matrix(6,6, [
	    a0,c0,j0,g0,f0,b0,
	    c0,e0,l0,i0,h0,d0,
	    j0,l0,p0,n0,m0,k0,
	    g0,i0,n0,l0,k0,h0,
	    f0,h0,m0,k0,j0,g0,
	    b0,d0,k0,h0,g0,c0]);
	if IntegralNormalization then
	    I06 *:= 2985984; 
	end if;
	return I06;
    end if;

    PXYZ := Parent(Phi);
    XYZ_orig := [ PXYZ.i : i in [1..3] ];
    K := BaseRing(PXYZ);
    PUVW<u,v,w> := PolynomialRing(K,3);
    PXYZUVW<X,Y,Z> := PolynomialRing(PUVW,3);
    Q := Evaluate(Phi,[X,Y,Z]);
    L := u*X+v*Y+w*Z;
    
    R := Resultant(Q,L,Z);
    R := (-1)^Degree(Q,Z)*Resultant(Q,L,Z);
    
    A0 := MonomialCoefficient(R,X^4);
    B0 := (1/4)*MonomialCoefficient(R,X^3*Y);
    C0 := (1/6)*MonomialCoefficient(R,X^2*Y^2);
    D0 := (1/4)*MonomialCoefficient(R,Y^3*X);
    E0 := MonomialCoefficient(R,Y^4);
    
    Psi := Determinant(Matrix(3,[A0,B0,C0,B0,C0,D0,C0,D0,E0]));
    Psi := Evaluate(PUVW!Numerator(Psi/w^(TotalDegree(Psi)-6)),XYZ_orig);

    Rho := (1/144)*DifferentialOperation(Phi,Psi);
    Tau := (1/12)*DifferentialOperation(Rho,Phi);

    Xo, Yo, Zo := Explode(XYZ_orig);
    A1 := MonomialCoefficient(Tau,Xo^2);
    B1 := (1/2)*MonomialCoefficient(Tau,Xo*Yo);
    C1 := MonomialCoefficient(Tau,Yo^2);
    D1 := (1/2)*MonomialCoefficient(Tau,Xo*Zo);
    E1 := (1/2)*MonomialCoefficient(Tau,Yo*Zo);
    F1 := MonomialCoefficient(Tau,Zo^2);
    
    A2 := MonomialCoefficient(Rho,Xo^2);
    B2 := (1/2)*MonomialCoefficient(Rho,Xo*Yo);
    C2 := MonomialCoefficient(Rho,Yo^2);
    D2 := (1/2)*MonomialCoefficient(Rho,Xo*Zo);
    E2 := (1/2)*MonomialCoefficient(Rho,Yo*Zo);
    F2 := MonomialCoefficient(Rho,Zo^2);

    if i eq 9 then
	I09 := A1*A2+2*B1*B2+C1*C2+2*D1*D2+2*E1*E2+F1*F2;
	if IntegralNormalization then
	    I09 *:= 26873856;
	end if;
	return K!I09;
    elif i eq 12 then
	I12 := Determinant(Matrix(3,3,[A2,B2,D2,B2,C2,E2,D2,E2,F2]));
	if IntegralNormalization then
	    I12 *:= 34828517376; 
	end if;
	return K!I12;
    elif i eq 15 then
	I15 := Determinant(Matrix(3,3,[A1,B1,D1,B1,C1,E1,D1,E1,F1]));
	if IntegralNormalization then
	    I15 *:= 120367356051456;
	end if;
//	return K!MonomialCoefficient(I15,PUVW!1);
	return K!I15;
    elif i eq 18 then
	I18 := (E1^2-C1*F1)*(E2^2-C2*F2)+2*(B1*F1-D1*E1)*(B2*F2-D2*E2)
	    + (D1^2-A1*F1)*(D2^2-A2*F2) + 2*(C1*D1-B1*E1)*(C2*D2-B2*E2)
	    + 2*(A1*E1-B1*D1)*(A2*E2-B2*D2)+(B1^2-A1*C1)*(B2^2-A2*C2);
	if IntegralNormalization then
	    I18 *:= 17332899271409664;
	end if;
//	return K!MonomialCoefficient(I18,PUVW!1);
	return K!I18;
    end if;
end intrinsic;
    

intrinsic DixmierInvariants(C::Crv) -> SeqEnum
    {}
    PP := AmbientSpace(C);
    require IsProjective(PP) and Dimension(PP) eq 2 and Degree(C) eq 4 :
	"Argument must be a plane quartic curve.";
    K := BaseRing(C);
    require Characteristic(K) notin {2,3} :
	"Argument must not be defined over a ring of characteristic 2 or 3.";
    return DixmierInvariants(DefiningPolynomial(C));
end intrinsic;


intrinsic DixmierInvariants(Phi::RngMPolElt : 
    IntegralNormalization := true) -> SeqEnum
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
    vprint Dixmier : "...I03;";
    vprint Dixmier, 2 : "I03:", I03;
    
    I06 := Determinant(M) where M :=Matrix(6,6, [
	a0,c0,j0,g0,f0,b0,
	c0,e0,l0,i0,h0,d0,
	j0,l0,p0,n0,m0,k0,
	g0,i0,n0,l0,k0,h0,
	f0,h0,m0,k0,j0,g0,
	b0,d0,k0,h0,g0,c0]);
    vprint Dixmier : "...I06;";
    vprint Dixmier, 2 : "I06:", I06;
    
    PXYZ := Parent(Phi);
    XYZ_orig := [ PXYZ.i : i in [1..3] ];
    K := BaseRing(Parent(Phi));
    PUVW<u,v,w> := PolynomialRing(K,3);
    PXYZUVW<X,Y,Z> := PolynomialRing(PUVW,3);
    Q := Evaluate(Phi,[X,Y,Z]);
    L := u*X+v*Y+w*Z;
    
    /*
    If the degree of the quartic Q is 3 not 4 in Z, 
    then the sign of the resultant changes.
    */
    R1 := (-1)^Degree(Q,Z)*Resultant(Q,L,Z);
    A0 := MonomialCoefficient(R1,X^4);
    B0 := (1/4)*MonomialCoefficient(R1,X^3*Y);
    C0 := (1/6)*MonomialCoefficient(R1,X^2*Y^2);
    D0 := (1/4)*MonomialCoefficient(R1,Y^3*X);
    E0 := MonomialCoefficient(R1,Y^4);

    Psi := Determinant(Matrix(3,[A0,B0,C0,B0,C0,D0,C0,D0,E0]));
    Psi := Evaluate(PUVW!Numerator(Psi/w^(TotalDegree(Psi)-6)),XYZ_orig);

    Rho := (1/144)*DifferentialOperation(Phi,Psi);
    Tau := (1/12)*DifferentialOperation(Rho,Phi);

    X, Y, Z := Explode(XYZ_orig);
    
    A1 := MonomialCoefficient(Tau,X^2);
    B1 := (1/2)*MonomialCoefficient(Tau,X*Y);
    C1 := MonomialCoefficient(Tau,Y^2);
    D1 := (1/2)*MonomialCoefficient(Tau,X*Z);
    E1 := (1/2)*MonomialCoefficient(Tau,Y*Z);
    F1 := MonomialCoefficient(Tau,Z^2);
    
    A2 := MonomialCoefficient(Rho,X^2);
    B2 := (1/2)*MonomialCoefficient(Rho,X*Y);
    C2 := MonomialCoefficient(Rho,Y^2);
    D2 := (1/2)*MonomialCoefficient(Rho,X*Z);
    E2 := (1/2)*MonomialCoefficient(Rho,Y*Z);
    F2 := MonomialCoefficient(Rho,Z^2);
    
    I09 := A1*A2+2*B1*B2+C1*C2+2*D1*D2+2*E1*E2+F1*F2;
    vprint Dixmier : "...I09;";
    vprint Dixmier, 2 : "I09:", I09;
    
    I12 := Determinant(Matrix(3,[K|A2,B2,D2,B2,C2,E2,D2,E2,F2]));
    vprint Dixmier : "...I12;";
    vprint Dixmier, 2 : "I12:", I12;
    
    I15 := Determinant(Matrix(3,[K|A1,B1,D1,B1,C1,E1,D1,E1,F1]));
    vprint Dixmier : "...I15;";
    vprint Dixmier, 2 : "I15:", I15;
    
    I18 := (E1^2-C1*F1)*(E2^2-C2*F2)+2*(B1*F1-D1*E1)*(B2*F2-D2*E2)
	+ (D1^2-A1*F1)*(D2^2-A2*F2) + 2*(C1*D1-B1*E1)*(C2*D2-B2*E2)
	+ 2*(A1*E1-B1*D1)*(A2*E2-B2*D2)+(B1^2-A1*C1)*(B2^2-A2*C2);
    vprint Dixmier : "...I18;";
    vprint Dixmier, 2 : "I18:", I18;

    I27 := QuarticDiscriminant(Phi);

    ww := [1,2,3,4,5,6,9];
    DD := [I03,I06,I09,I12,I15,I18,I27];
    if IntegralNormalization then
	scale := [ 144, 2985984, 26873856, 34828517376, 
	    120367356051456, 17332899271409664, 1099511627776 ];
	return [ scale[i]*DD[i] : i in [1..7] ], ww;  
    end if;
    return DD, ww;
end intrinsic;

