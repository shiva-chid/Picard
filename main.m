load "maxgrp_containment_tests.m";

function possibly_nonsurj_primes(f : cond := 1, fromCMformsdb := false);
    if cond eq 1 then
        radical_disc := &*([1] cat [p : p in PrimeFactors(Discriminant(f))]);
        radical_leadcoeff := &*([1] cat [p : p in PrimeFactors(Coefficient(f,4))]);
        radical_cond := radical_leadcoeff*radical_disc;
        if radical_cond mod 3 ne 0 then
            radical_cond := 3*radical_cond;
        end if;
        possibly_C1image := C1test(f,radical_cond : fromCMformsdb := fromCMformsdb);
        possibly_C3image := C3test(f,radical_cond);
        possibly_C2image := C2test(f,radical_cond);
//        return [[2,3,5,7], PrimeFactors(radical_cond), possibly_C1image, possibly_C3image, possibly_C2image];
        return [[2,3,5,7], possibly_C1image, possibly_C3image, possibly_C2image];
    else
        possibly_C1image := C1test(f, cond : cond := cond, fromCMformsdb := fromCMformsdb);
        possibly_C3image := C3test(f, cond : cond := cond);
        possibly_C2image := C2test(f, cond : cond := cond);
//        return [[2,3,5,7], PrimeFactors(cond), possibly_C1image, possibly_C3image, possibly_C2image];
        return [[2,3,5,7], possibly_C1image, possibly_C3image, possibly_C2image];
    end if;
end function;


P<x> := PolynomialRing(Integers());
/*
f := x^4 - x^2 - x + 1;
possibly_nonsurj_primes(f : cond := 3^8*23^2);
possibly_nonsurj_primes(f);
*/


