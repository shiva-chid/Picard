load "maxgrp_containment_tests.m";


function possibly_nonsurj_primes(f : radical_cond := 1, primes_bound := 1000);
    if radical_cond eq 1 then
        radical_cond := RadCond(f);
    end if;
    badprimes := PrimeFactors(radical_cond);
    f := suppressed_integer_quartic(f);
    if radical_cond eq 1 then
        radical_cond := RadCond(f);
    end if;
    possibly_C1image := C1test(f : radical_cond := radical_cond, primes_bound := primes_bound);
    possibly_C3image, possibly_C2image := C2andC3test(f : radical_cond := radical_cond, primes_bound := primes_bound);
    return badprimes, [[2,3,5,7], possibly_C1image, possibly_C3image, possibly_C2image];
end function;


P<x> := PolynomialRing(Integers());
/*
f := x^4 - x^2 - x + 1;
possibly_nonsurj_primes(f : radical_cond := 3*23);
possibly_nonsurj_primes(f);
*/


