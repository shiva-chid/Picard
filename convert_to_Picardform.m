function suppressed_integer_quartic(f);
    P<x> := PolynomialRing(Rationals());
    a4 := Coefficient(f,4);
    if a4 ne 1 then
        f := a4^3*Evaluate(f,x/a4);
    end if;

    a3 := Coefficient(f,3);
    if a3 ne 0 then
        f := Evaluate(f,x-a3/4);
    end if;

    coeffs := Coefficients(f)[1..3];
    coeffs_dens := [Denominator(x) : x in coeffs];
    pfacs_dens := &join[Set(PrimeFactors(x)) : x in coeffs_dens];
    m := (pfacs_dens eq {}) select 1 else &*[p^n where n is Maximum([Ceiling(Valuation(coeffs_dens[i],p)/(15-3*i)) : i in [1..3]]) : p in pfacs_dens];

    P<x> := PolynomialRing(Integers());
    return P!([m^(15-3*i)*coeffs[i] : i in [1..3]] cat [0,1]);
end function;

/*
function convert_to_Picardform(f : suppressed_quartic := true);
    F<zeta> := CyclotomicField(3);
    P3<x,y,z> := Parent(ChangeRing(f,F));
    CF := Curve(ProjectiveSpace(P3),f);
    AF := AutomorphismGroup(CF);
    assert #AF eq 3;
    aut_eqns := DefiningEquations(AF.1);
    assert &and[Degree(eqn) eq 1 : eqn in aut_eqns];
    M := Matrix(F,3,3,[[MonomialCoefficient(eqn,P3.i) : i in [1..3]] : eqn in aut_eqns]);
    D := DiagonalMatrix(F,3,[1,zeta,1]);
    eigvals := Eigenvalues(M);
    assert exists(w){t[1] : t in eigvals | t[2] eq 2};
    if w ne 1 then
        M := w^2*M;
    end if;
    assert exists(w){t[1] : t in eigvals | t[2] eq 1};
    if w eq zeta^2 then
        D := D^2;
    end if;
    boo, mat := IsSimilar(M,D);
    invmat := mat^-1;
    assert mat*M*invmat eq D;
    f_new := Evaluate(f,[&+[invmat[i,j]*P3.j : j in [1..3]] : i in [1..3]]);
    a := MonomialCoefficient(f_new,x*y^3);
    b := MonomialCoefficient(f_new,z*y^3);
    if b ne 0 then
        f_new := Evaluate(f_new,[x,y,(z-a*x)/b]);
    else
        f_new := Evaluate(f_new,[z/a,y,x]);
    end if;

    P<t> := PolynomialRing(F);
    g := Evaluate(f_new,[t,0,1]);
    assert IsIsomorphic(CF,Curve(ProjectiveSpace(P3),y^3*z-P3!(Evaluate(g,x/z)*z^4)));
    if suppressed_quartic then
        a4 := Coefficient(g,4);
        if a4 ne 1 then
            g := a4^3*Evaluate(g,t/a4);
        end if;
        a3 := Coefficient(g,3);
        if a3 ne 0 then
            g := Evaluate(g,t-a3/4);
        end if;
    end if;
    P_Q<t> := PolynomialRing(Rationals());
    try g := P_Q ! g; g := suppressed_integer_quartic(g); catch e; end try;
    return g;
end function;

P<x,y,z> := PolynomialRing(Integers(),3);


input_split := Split(input_string,":");
f := eval input_split[2][2..#input_split[2]-1];

try
    if input_split[#input_split] eq "x^2-x+1" then
        g := convert_to_Picardform(f);
        out := input_split[1] cat ":" cat Sprint(g) cat &cat[":" cat input_split[j] : j in [3..#input_split]];
        PrintFile("spq_B_SuppIntQuartic.txt", out);
    else
        PrintFile("spq_B_DiffEndStructure.txt", input_string);
    end if;
catch e;
    PrintFile("spq_B_error.txt", input_string);
end try;

exit;

// cat spq_B.txt | time parallel -j 32 --eta magma input_string:={} convert_to_Picardform.m

// error for x^3*z+x*y^3+y^4+y^3*z+z^4 (which is rectified by convert_to_Picardform3 below)
*/

///////////////////////////////////////////////////////////////////////////////////////////////////////

/*
function convert_to_Picardform2(f : suppressed_quartic := true);
    P9<a,b,c,d,e,f,g,h,i> := PolynomialRing(Rationals(),9);
    P3<x,y,z> := PolynomialRing(P9,3);
    f := P3 ! f;
    g := Evaluate(f,[a*x+b*y+c*z,d*x+e*y+f*z,g*x+h*y+i*z]);
    mons4 := MonomialsOfDegree(P3,4);
    assert #mons4 eq 15;
    vanishing_mons4 := [mon : mon in mons4 | Degree(mon,y) in {1,2,4} or mon in {y^3*x, x^3*z}];
    assert #vanishing_mons4 eq 10;
    coeffs := [MonomialCoefficient(g,mon) : mon in vanishing_mons4];
    I := ideal<P9 | coeffs>;
    Groebner(I);

    g := Evaluate(f,[aa*x+bb*y+cc*z,dd*x+ee*y+ff*z,gg*x+hh*y+ii*z]);
    return g;
end function;
*/

function convert_to_Picardform3(f : suppressed_quartic := true, basefield := Rationals());
    P5<a,b,c,d,e> := PolynomialRing(basefield,5);
    P3<x,y,z> := PolynomialRing(P5,3);
    f := P3 ! f;
    g := Evaluate(f,z,a*x+b*y);
    coeffs := CoefficientsAndMonomials(g);
    assert #coeffs eq 5;
    eqns := [coeffs[1]-e*c^4, coeffs[2]-4*e*c^3*d, coeffs[3]-6*e*c^2*d^2, coeffs[4]-4*e*c*d^3, coeffs[5]-e*d^4];
    I := ideal<P5|eqns>;
    Groebner(I);
    GB_I := GroebnerBasis(I);
    if GB_I ne [1] then
        A4<aa,bb,cc,ee> := AffineSpace(basefield,4);
        PA4 := CoordinateRing(A4);
        coerce := hom<P5->PA4|[aa,bb,cc,1,ee]>;
        relevant_eqns := [coerce(xx) : xx in GB_I];
        V := Scheme(A4,relevant_eqns);
//        assert Dimension(V) eq 0;
        pts_V := Points(V);
//        pts_V := PointsOverSplittingField(V);
//        print #pts_V;
        for pt in pts_V do
            P3<x,y,z> := Parent(f);
            print pt;
            aaa := pt[1];
            bbb := pt[2];
            ccc := pt[3];
            ddd := 1;
            eee := pt[4];
            ff := Evaluate(f,z,z+aaa*x+bbb*y);
            ff := Evaluate(ff,[y,x-ccc*y,z]);
            P3_Q<x,y,z> := PolynomialRing(basefield,3);
            ff := P3_Q ! ff;
//            print ff;
            try
                ppp := MonomialCoefficient(ff,x*y^2*z)/MonomialCoefficient(ff,y^3*z);
                qqq := MonomialCoefficient(ff,y^2*z^2)/MonomialCoefficient(ff,y^3*z);
                ff := Evaluate(ff,y,y-ppp/3*x-qqq/3*z);
                ff := Evaluate(ff,z,z/MonomialCoefficient(ff,y^3*z));
                print ff;

                P_Q<t> := PolynomialRing(basefield);
                g := Evaluate(ff,[t,0,1]);
                assert IsIsomorphic(Curve(ProjectiveSpace(P3_Q),P3_Q!f),Curve(ProjectiveSpace(P3_Q),y^3*z-P3_Q!(Evaluate(g,x/z)*z^4)));
            catch e;
                continue;
            end try;
            if suppressed_quartic then
                try g := P_Q ! g; g := suppressed_integer_quartic(g); catch e; end try;
            end if;
            return g;
        end for;

        A3<aa,bb,ee> := AffineSpace(basefield,3);
        PA3 := CoordinateRing(A3);
        coerce := hom<P5->PA3|[aa,bb,1,0,ee]>;
        relevant_eqns := [coerce(xx) : xx in GB_I];
        V := Scheme(A3,relevant_eqns);
//        assert Dimension(V) eq 0;
        pts_V := Points(V);
//        pts_V := PointsOverSplittingField(V);
//        print #pts_V;
        for pt in pts_V do
            P3<x,y,z> := Parent(f);
            print pt;
            aaa := pt[1];
            bbb := pt[2];
            ccc := 1;
            ddd := 0;
            eee := pt[3];
            ff := Evaluate(f,z,z+aaa*x+bbb*y);
            P3_Q<x,y,z> := PolynomialRing(basefield,3);
            ff := P3_Q ! ff;
//            print ff;
            try
                ppp := MonomialCoefficient(ff,x*y^2*z)/MonomialCoefficient(ff,y^3*z);
                qqq := MonomialCoefficient(ff,y^2*z^2)/MonomialCoefficient(ff,y^3*z);
                ff := Evaluate(ff,y,y-ppp/3*x-qqq/3*z);
                ff := Evaluate(ff,z,z/MonomialCoefficient(ff,y^3*z));
                print ff;

                P_Q<t> := PolynomialRing(basefield);
                g := Evaluate(ff,[t,0,1]);
                assert IsIsomorphic(Curve(ProjectiveSpace(P3_Q),P3_Q!f),Curve(ProjectiveSpace(P3_Q),y^3*z-P3_Q!(Evaluate(g,x/z)*z^4)));
            catch e;
                continue;
            end try;
            if suppressed_quartic then
                try g := P_Q ! g; g := suppressed_integer_quartic(g); catch e; end try;
            end if;
            return g;
        end for;
/*
        A2<aa,bb> := AffineSpace(basefield,2);
        P2 := CoordinateRing(A2);
        coerce1 := hom<P5->P2|[aa,bb,0,0,0]>;
        relevant_eqns1 := [coerce1(xx) : xx in GB_I | Degree(xx,c) eq 0 and Degree(xx,d) eq 0 and Degree(xx,e) eq 0];
        V1 := Scheme(A2,relevant_eqns1);
        assert Dimension(V1) eq 0;

        P1<cc,dd> := ProjectiveSpace(basefield,1);
        P2 := CoordinateRing(P1);
        coerce2 := hom<P5->P2|[0,0,cc,dd,0]>;
        relevant_eqns2 := [coerce2(xx) : xx in GB_I | Degree(xx,a) eq 0 and Degree(xx,b) eq 0 and Degree(xx,e) eq 0];
        V2 := Scheme(P1,relevant_eqns2);
        assert Dimension(V2) eq 0;
 

        pts_V1 := Points(V1);
//        pts_V1 := PointsOverSplittingField(V1);
//        print #pts_V1;
        for ab_pt in pts_V1 do
            aaa := ab_pt[1];
            bbb := ab_pt[2];
            ff := Evaluate(f,z,z+aaa*x+bbb*y);
            pts_V2 := Points(V2);
//            pts_V2 := PointsOverSplittingField(V2);
//            print #pts_V2;
            for cd_pt in pts_V2 do
                ccc := cd_pt[1];
                ddd := cd_pt[2];
                if ccc ne 0 then
                    ff := Evaluate(ff,x,(x-ddd*y)/ccc);
                else
                    ff := Evaluate(ff,[y,x,z]);
                end if;
                P3_Q<x,y,z> := PolynomialRing(basefield,3);
                ff := P3_Q ! ff;
//                print ff;
                ppp := MonomialCoefficient(ff,x*y^2*z)/MonomialCoefficient(ff,y^3*z);
                qqq := MonomialCoefficient(ff,y^2*z^2)/MonomialCoefficient(ff,y^3*z);
                ff := Evaluate(ff,y,y-ppp/3*x-qqq/3*z);
                ff := Evaluate(ff,z,z/MonomialCoefficient(ff,y^3*z));
//                print ff;

                P_Q<t> := PolynomialRing(basefield);
                g := Evaluate(ff,[t,0,1]);
                assert IsIsomorphic(Curve(ProjectiveSpace(P3_Q),P3_Q!f),Curve(ProjectiveSpace(P3_Q),y^3*z-P3_Q!(Evaluate(g,x/z)*z^4)));
                if suppressed_quartic then
                    try g := P_Q ! g; g := suppressed_integer_quartic(g); catch e; end try;
                end if;
                return g;
            end for;
        end for;
*/
    end if;


/*
    P4<a,c,d,e> := PolynomialRing(basefield,4);
    P3<x,y,z> := PolynomialRing(P4,3);
    f := P3 ! f;
    g := Evaluate(f,y,a*x);
    coeffs := CoefficientsAndMonomials(g);
    assert #coeffs eq 5;
    eqns := [coeffs[1]-e*c^4, coeffs[2]-4*e*c^3*d, coeffs[3]-6*e*c^2*d^2, coeffs[4]-4*e*c*d^3, coeffs[5]-e*d^4];
    I := ideal<P4|eqns>;
    Groebner(I);
    GB_I := GroebnerBasis(I);
    if GB_I ne [1] then

    end if;

    g := Evaluate(f,x,0);
    coeffs := CoefficientsAndMonomials(g);
    P<t> := PolynomialRing(basefield);
    g := P ! coeffs;
    gprime := Derivative(g);
    if GCD(g,gprime) eq gprime/LeadingCoefficient(gprime) then

    end if;
*/
    return false;
end function;

/*
No error for x^3*z+x*y^3+y^4+y^3*z+z^4.
It is isomorphic to the Picard curve defined by x^4 - 1944*x^2 - 46656*x + 2671056
*/


/*
(Candidate) example of a non-Picard curve:

> P3<x,y,z> := PolynomialRing(Rationals(),3);
> f := x^3*y + x^3*z + x^2*y^2 - x^2*y*z - 4*x^2*z^2 - 4*x*y^3 + 6*x*y^2*z + 3*x*y*z^2 + 5*x*z^3 + 5*y^4 - 4*y^3*z - y^2*z^2 - 3*y*z^3 - z^4;
> convert_to_Picardform3(f);
false
*/

//////////////////////////////////////////////////////////////////

P<x,y,z> := PolynomialRing(Integers(),3);


input_split := Split(input_string,":");
f := eval input_split[2][2..#input_split[2]-1];

try
    if input_split[#input_split] eq "x^2-x+1" then
        g := convert_to_Picardform3(f);
        if Type(g) eq BoolElt then
            PrintFile("spq_B_likelynotPicard3.txt", input_string);
        else
            out := input_split[1] cat ":" cat Sprint(g) cat &cat[":" cat input_split[j] : j in [3..#input_split]];
            PrintFile("spq_B_SuppIntQuartic3.txt", out);
        end if;
    else
        PrintFile("spq_B_DiffEndStructure3.txt", input_string);
    end if;
catch e;
    PrintFile("spq_B_error3.txt", input_string);
end try;

exit;

// cat spq_B.txt | time parallel -j 64 --eta magma input_string:={} convert_to_Picardform.m
