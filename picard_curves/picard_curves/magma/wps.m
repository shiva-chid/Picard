/***
 *  Required functions
 *
 *  See LICENSE.txt for license details.
 */


function WPSMultiply(W, I, lambda)

assert #W eq #I;
return [ lambda^(W[i]) * I[i] : i in [1..#I] ];

end function;


function WPSMinimize(W, I)

assert #W eq #I;
nums := [ Numerator(inv) : inv in I ];
dens := [ Denominator(inv) : inv in I ];
ps := [ ];
for n in nums cat dens do
    if n ne 0 then
        fac := Factorization(n);
        ps := [ p : p in Set(ps cat [ tup[1] : tup in fac ]) ];
    end if;
end for;

for p in ps do
    e := Minimum([ Valuation(I[k], p) div W[k] : k in [1..3] | I[k] ne 0 ]);
    I := WPSMultiply(W, I, p^(-e));
end for;

/* Sign standardization */
J := WPSMultiply(W, I, -1);
if J gt I then
    I := J;
end if;

return I;

end function;


function WPSMinimizeTwist(W, I)

assert #W eq #I;
for i in [1..#W] do
    if I[i] eq 0 then
        W[i] := 0;
    end if;
end for;
gcd := GCD(W); W := [ w div gcd : w in W ];

nums := [ Numerator(inv) : inv in I ];
dens := [ Denominator(inv) : inv in I ];
ps := [ ];
for n in nums cat dens do
    if n ne 0 then
        fac := Factorization(n);
        ps := [ p : p in Set(ps cat [ tup[1] : tup in fac ]) ];
    end if;
end for;

for p in ps do
    e := Minimum([ Valuation(I[k], p) div W[k] : k in [1..3] | I[k] ne 0 ]);
    I := WPSMultiply(W, I, p^(-e));
end for;

/* Sign standardization */
J := WPSMultiply(W, I, -1);
if J gt I then
    I := J;
end if;

return I;

end function;
