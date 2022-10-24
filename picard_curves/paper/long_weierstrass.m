/* Shows that we may not be able to get rid of x as well */

R<t> := PolynomialRing(Rationals());
f := t^4 + 3*t^3 - 105*t^2 - 46*t + 2145;
F0, T := LongWeierstrassEquation(f);

print "";
print "Long Weierstrass equation and transformation:";
print F0;
print T;

//print "";
//print "Trying to remove x...";
//D := [-100..100];
//while true do
//    K := Rationals();
//    R<y,x,z> := PolynomialRing(K, 3);
//
//    repeat
//        T := Matrix(K, 3, 3, [ Random(D) : i in [1..9] ]);
//    until Determinant(T) ne 0;
//    F := R ! PicardForm(f)^T;
//
//    F0, T := MinimizeReducePlaneQuartic(F);
//    F0 := R ! F0;
//    T := ChangeRing(T, K);
//    U := T^(-1);
//
//    /* At this point F^T = F0, so that T maps X0 to X and U maps X to X0 */
//    // Image of (1 : 0 : 0)
//    P := [ U[1,1], U[2,1], U[3,1] ];
//    d := LCM([ Denominator(c) : c in P ]);
//    P := [ Integers() ! (d*c) : c in P ];
//    d := GCD(P);
//    P := [ c div d : c in P ];
//
//    ZZ3 := RSpace(Integers(), 3);
//    Q, proj := quo< ZZ3 | ZZ3 ! P >;
//    Q1 := Eltseq(Q.1 @@ proj);
//    Q2 := Eltseq(Q.2 @@ proj);
//
//    T1 := Transpose(Matrix(K, [ P, Q1, Q2 ]));
//    U1 := T1^(-1);
//    F1 := F0^T1;
//
//    P := [ MonomialCoefficient(F1, y^3*x), MonomialCoefficient(F1, y^3*z) ];
//    d := LCM([ Denominator(c) : c in P ]);
//    P := [ Integers() ! (d*c) : c in P ];
//    d := GCD(P);
//    P := [ c div d : c in P ];
//
//    ZZ2 := RSpace(Integers(), 2);
//    Q, proj := quo< ZZ2 | ZZ2 ! P >;
//    Q1 := Eltseq(Q.1 @@ proj);
//
//    T2 := DiagonalJoin(Matrix(K, [[1]]), Matrix(K, [ Q1, P ]));
//    U2 := T2^(-1);
//    F2 := F1^U2;
//
//    T := T*T1*U2;
//    T11 := (Integers() ! T[1,1]); T12 := (Integers() ! T[1,2]);
//    if T12 mod T11 eq 0 then
//        T := T*Matrix(K, [[ 1, -T12 div T11, 0 ], [ 0, 1, 0 ], [ 0, 0, 1 ]]);
//        G := F^T;
//        G /:= GCD([ Integers() ! c : c in Coefficients(G) ]);
//        G /:= Sign(MonomialCoefficient(G, y^3*z));
//        print G;
//    end if;
//end while;
