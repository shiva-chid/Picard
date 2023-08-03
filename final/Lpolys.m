intrinsic lift2mod3(p :: RngIntElt, CartierManin :: SeqEnum, C :: SeqEnum) -> SeqEnum
{Given the coefficients C = [c,b,a] of a curve y^3 = x^4 + ax^2 + bx + c, and a prime p that is 2 modulo 3,
and the entries of the Cartier Manin matrix at the prime p, returns the coefficient sequence of the L-polynomial at p.}
    Z := Integers();
    Fp := GF(p);
    CartierManin := Matrix(Z,3,3,CartierManin);
    A2modp := Z ! (-(CartierManin[3,1]*CartierManin[1,3]+CartierManin[3,2]*CartierManin[2,3]+CartierManin[1,2]*CartierManin[2,1]) mod p);

    P<T> := PolynomialRing(Z);
    P<x> := PolynomialRing(Fp);
    f := x^4 + C[3]*x^2 + C[2]*x + C[1];
    mod3res := IsIrreducible(f) select 1 else 0;

    candidates := 0;
    jacvals := [];
    for i := -1 to 2 do
        A2 := A2modp + i*p;
        if A2 mod 3 eq mod3res then
            candidates +:= 1;
            Append(~jacvals,[1,0,A2,0,p*A2,0,p^3]);
        end if;
    end for;

    if candidates eq 1 then
        return jacvals[1];
    end if;

    f0 := C[1];
    f1 := C[2];
    f2 := C[3];
    psi_f := x^9 + 24*f2*x^7-168*f1*x^6+ (1080*f0-78*f2^2)*x^5+ 336*f1*f2*x^4+ (1728*f0*f2-636*f1^2+ 80*f2^3)*x^3+ (-864*f0*f1-168*f1*f2^2)*x^2+ (-432*f0^2 + 216*f0*f2^2-120*f1^2*f2-27*f2^4)*x-8*f1^3;
    binp := [];
    pred := p;
    while pred ne 0 do
        rem := pred mod 2;
        pred := ExactQuotient(pred - rem,2);
        Append(~binp,rem);
    end while;
    xtothepbar := 1;
    res := x mod psi_f;
    for i := 1 to #binp do
        if binp[i] eq 1 then
            xtothepbar *:= res;
            xtothepbar := xtothepbar mod psi_f;
        end if;
        res := res*res;
        res := res mod psi_f;
    end for;
    assert (x^p - xtothepbar) mod psi_f eq 0;
    psiGCDdeg := Degree(GCD(xtothepbar-x,psi_f));
    parity := (psiGCDdeg gt 0) select 1 else 0;

    for i := 1 to 2 do
        if jacvals[i][3] mod 2 eq parity then
            return jacvals[i];
        end if;
    end for;
end intrinsic;

NF<zzeta> := CyclotomicField(3);
ONF := RingOfIntegers(NF);

intrinsic lift1mod3(p :: RngIntElt, CartierManin :: SeqEnum, f :: RngUPolElt) -> SeqEnum
{Given a prime p that is 1 modulo 3, the entries of the Cartier Manin matrix at the prime p, 
and a quartic polynomial f defining a curve y^3 = f(x), returns the coefficient sequence of 
the Lpolynomial at p.}
    Z := Integers();
    Fp := GF(p);
    P<T> := PolynomialRing(Z);

//    require p ge 53 : "Use naive point counting.";
    if p lt 53 then
        P3<x,y,z> := PolynomialRing(Rationals(),3);
        return Coefficients(LPolynomial(y^3*z-P3!(Evaluate(f,x/z)*z^4),p));
    end if;

    CartierManin := Matrix(Integers(),3,3,CartierManin);

    _, sqrt_3 := IsSquare(Fp ! -3);
    zeta3 := (-1+sqrt_3)/2;
    zeta3bar := zeta3^2;

    M := Matrix(Fp,2,2,[1, zeta3, 1, zeta3bar]);
    r_p := (CartierManin[1,1]+CartierManin[2,2]) mod p;
    r_pbar := CartierManin[3,3] mod p;

    a_p := Solution(Transpose(M), Matrix(Fp,1,2,[r_p, r_pbar]));
    a_p := a_p[1];
    a_p := [((Z!a_p[1]) lt p/2) select Z!a_p[1] else (Z!a_p[1])-p, ((Z!a_p[2]) lt p/2) select Z!a_p[2] else (Z!a_p[2])-p];
    a_pbar := (a_p[1]-a_p[2]) - zzeta*a_p[2];
    a_p := a_p[1] + a_p[2]*zzeta;

    zeta6 := zzeta+1;

    pi_ideal_element := -(Z ! zeta3) + zzeta;
    pi_ideal_1 := pi_ideal_element*ONF;
    pi_ideal_2 := p*ONF;
    pi_ideal := pi_ideal_1 + pi_ideal_2;

    boo, pi_00 := IsPrincipal(pi_ideal);
    pibar_00 := pi_00[1]-pi_00[2]-pi_00[2]*zzeta;

    pi_00_plc := Place(pi_ideal);

    s := CartierManin[1,1]*CartierManin[2,2] - CartierManin[1,2]*CartierManin[2,1];
    s_p := Evaluate(s, pi_00_plc);
    require s_p ne 0 : "Non ordinary prime";
    r_pbar_ffelt := Evaluate(CartierManin[3,3], pi_00_plc);
    sigma_pibar := Evaluate(pibar_00, pi_00_plc);
    sextic_val := s_p/(r_pbar_ffelt*sigma_pibar);
    sigma_zeta6 := Evaluate(zeta6, pi_00_plc);
    assert exists(sextic_power){i : i in [0..5] | sigma_zeta6^i eq sextic_val};
    c_p := (zeta6^sextic_power)*pibar_00*p;
    c_pbar := c_p[1]-c_p[2]-c_p[2]*zzeta;

    b_p := c_p*a_pbar/p;
    b_pbar := b_p[1]-b_p[2]-b_p[2]*zzeta;

    A1 := -2*a_p[1]+a_p[2];
    A2 := a_p*a_pbar + b_p + b_pbar;
    A3 := -(c_p + c_pbar + a_p*b_pbar + a_pbar*b_p);
    return [1,A1,A2,A3,p*A2,p^2*A1,p^3];
end intrinsic;

/*
function liftLpolys(CMlist,TrList,C,i);
    str := CMList[i];
    l := #str;
    ind := Index(str,",");
    p := StringToInteger(str[1..ind-1]);
    CM := Split(str[ind+1..#str],"[],");
    CM := [[StringToInteger(CM[3*i+1]),StringToInteger(CM[3*i+2]),StringToInteger(CM[3*i+3])] : i in [0..2]];
    t := TrList[i];
    if p mod 3 eq 1 then
        return lift1mod3(p,CM,t,true);
    end if;
    if p mod 3 eq 2 then
        return lift2mod3(p,CM,C);
    end if;
end function;

function liftLpolysAlt(CMlist,C,i);
    str := CMList[i];
    l := #str;
    ind := Index(str,",");
    p := StringToInteger(str[1..ind-1]);
    CM := Split(str[ind+1..#str],"[],");
    CM := [[StringToInteger(CM[3*i+1]),StringToInteger(CM[3*i+2]),StringToInteger(CM[3*i+3])] : i in [0..2]];
    if p mod 3 eq 1 then
        return lift1mod3(p,CM,1,false);
    end if;
    if p mod 3 eq 2 then
        return lift2mod3(p,CM,C);
    end if;
end function;
*/

intrinsic liftLpolys(CMlistfile :: IO, C :: SeqEnum) -> SeqEnum
{return a sequence of tuples <p, Lpoly_p> where Lpoly_p is the coefficient sequence 
of the L-polynomial at p for the curve y^3 = x^4 + ax^2 + bx + c. The input consists
of two things:
1. a file containing the entries of the Cartier Manin matrices for primes in some range
in the form
p, [[a11, a12, a13],[a21, a22, a23],[a31, a32, a33]]
2. A sequence containing the coefficients [c,b,a] of the curve.}
    s := Gets(CMlistfile);
    s := Gets(CMlistfile);
    P<x> := PolynomialRing(Rationals());
    f := x^4 + (P ! C);
    Lpolyslist := [];
    while not IsEof(s) do
        s := Split(s,",[]");
        if #s ne 10 then
            s := Gets(CMlistfile);
            continue;
        end if;
        p := StringToInteger(s[1]);
        assert IsPrime(p);
        CMmat := [[StringToInteger(s[3*i+2]),StringToInteger(s[3*i+3]),StringToInteger(s[3*i+4])] : i in [0..2]];
        if p mod 3 eq 1 then
            try
                lpoly := lift1mod3(p,CMmat,f);
                Append(~Lpolyslist,<p,lpoly>);
            catch e;
            end try;
        elif p mod 3 eq 2 then
            try
                lpoly := lift2mod3(p,CMmat,C);
                Append(~Lpolyslist,<p,lpoly>);
            catch e;
            end try;
        end if;
        s := Gets(CMlistfile);
    end while;
    return Lpolyslist;
end intrinsic;

/*
function liftLpoly(CartManMat_string,C);
    s := CartManMat_string;
    Lpolyslist := [];
    s := Split(s,":");
    assert #s eq 9;
    p := StringToInteger(s[4]);
    assert IsPrime(p);
    CMmat := Split(s[9],"[],");
    CMmat := [[StringToInteger(CMmat[3*i+1]),StringToInteger(CMmat[3*i+2]),StringToInteger(CMmat[3*i+3])] : i in [0..2]];
    if p mod 3 eq 1 then
        lpoly := lift1mod3(p,CMmat);
        if Type(lpoly) eq MonStgElt then
            return "Lpolynomial not computed";
        end if;
        return [<p,lpoly>];
    end if;
    if p mod 3 eq 2 then
        lpoly := lift2mod3(p,CMmat,C);
        if Type(lpoly) eq MonStgElt then
            return "Lpolynomial not computed";
        end if;
        return [<p,lpoly>];
    end if;
end function;
*/