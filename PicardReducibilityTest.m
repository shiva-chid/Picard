function Star(P,Q)
PP<x> := Parent(P); 
RR<z> := PolynomialRing(PP);
Qxz := 0;
for i in [0 .. Degree(Q)]  do
Qxz +:= Eltseq(Q)[i+1]*z^(Degree(Q)-i)*x^i;
end for;
return Resultant(RR!Eltseq(P), Qxz);
end function;

function StarPower(r,P)
if r eq 1 then return P; end if;
Pr := P;
for i in [2 .. r] do
Pr := Star(Pr,P);
end for;
return Pr;
end function;

function Bracket(r,P)
_<x> := Parent(P);
PrXr := Star(P, x^r-1);
PrX := 0;
for i in [0 .. Degree(P)] do
PrX +:= Eltseq(PrXr)[r*i + 1] * x^i;
end for;
return PrX;
end function;

load "Lpolys.m";
function getLpol(f,radical_cond,p);
    P<x> := Parent(f);
    if BaseRing(P) ne Integers() then
        P<x> := PolynomialRing(Integers());
        f := P ! f;
    end if;
    if radical_cond mod p eq 0 then
        return "Bad Prime";
    end if;
/*
    require radical_cond mod p ne 0 : "Bad Prime";
*/
    pstr := IntegerToString(p);
    fcoeffs := [IntegerToString(c) : c in Coefficients(f)];
    fstr := "x^4+" cat fcoeffs[3] cat "x^2+" cat fcoeffs[2] cat "x+" cat fcoeffs[1];
    System("hwlpoly y^3=" cat fstr cat " " cat pstr cat " 1 > CartManmat_for_p.txt");
    fil := Open("CartManmat_for_p.txt", "r");
    C := Coefficients(f)[1..3];
    Lpol := liftLpolys(fil,C);
/*
    print Lpol;
*/
    if #Lpol ne 1 then
        return "Error in computing L-polynomial";
    end if;
/*
    require #Lpol eq 1 : "Error in computing L-polynomial";
*/
    return P ! Reverse(Lpol[1,2]);
end function;

K := QuadraticField(-3);
O := Integers(K);
R:= PolynomialRing(O);

function RadCond(f)
radical_disc := &*([1] cat [p : p in PrimeFactors(Discriminant(f))]);
        radical_leadcoeff := &*([1] cat [p : p in PrimeFactors(Coefficient(f,4))]);
        radical_cond := radical_leadcoeff*radical_disc;
        if radical_cond mod 3 ne 0 then
            radical_cond := 3*radical_cond;
        end if;
return radical_cond;
end function;

//Input: f is the defining polynomial, i.e., y^3=f and "a" should generate a prime ideal above a rational prime congruent to 1 mod 3.
//Output: This outputs the "Billerey Bound",i.e., the analogue to the B_p bound given in Billerey's paper.
function Bound(f, radical_cond,a)
p :=Integers()!Norm(a);
assert p mod 3 eq 1 and radical_cond mod p ne 0 and p ge 53;
Lpol := getLpol(f,radical_cond,p);
Testpol := Bracket(72,Lpol);
return &*[Evaluate(Testpol, r^(72)): r in {1,a,p,a*p,p^2,a^2}];
end function;

// Given the defining f, we compute the divisors of the associated "Billerey Bounds" for all primes 1 mod 3 of good reduction in the interval (53,N).
function PosRedPrimes(f,N)
radical_cond := RadCond(f);
As := [];
 for p in PrimesInInterval(53, N) do
 if (p mod 3 ne 1) or (radical_cond mod p eq 0)  then continue; end if;
 Fact := Factorisation(p*O);
 for F in Fact do
 tf, a := IsPrincipal(F[1]);
 Append(~As,a);
 end for;
 end for;
Bs := [Integers()!Norm(a) * Bound(f,radical_cond,a):a in As]; // The bound associated to B_p doesn't give us any any information on p.
return Setseq(Seqset(PrimeFactors(Norm(GCD(Bs))) cat PrimeFactors(radical_cond))); //to catch any primes which may not have semistable reduction. In particular, note that 3 is included here.
end function;

