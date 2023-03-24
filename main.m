load "maxgrp_containment_tests.m";

function possibly_nonsurj_primes(f : cond := 1);
    if cond eq 1 then
        radical_cond := Squarefree(Coefficient(f,4))*Squarefree(Discriminant(f));
        if radical_cond mod 2 ne 0 then
            radical_cond := 2*radical_cond;
        end if;
        if radical_cond mod 3 ne 0 then
            radical_cond := 3*radical_cond;
        end if;
        possibly_C1image := C1test(f,radical_cond);
        possibly_C3image := C3test(f,radical_cond);
        possibly_C2image := C2test(f,radical_cond);
//        return [[2,3,5,7], PrimeFactors(radical_cond), possibly_C1image, possibly_C3image, possibly_C2image];
        return [[2,3,5,7], possibly_C1image, possibly_C3image, possibly_C2image];
    else
        possibly_C1image := C1test(f, cond : cond := cond);
        possibly_C3image := C3test(f, cond : cond := cond);
        possibly_C2image := C2test(f, cond : cond := cond);
//        return [[2,3,5,7], PrimeFactors(cond), possibly_C1image, possibly_C3image, possibly_C2image];
        return [[2,3,5,7], possibly_C1image, possibly_C3image, possibly_C2image];
    end if;
end function;


P<x> := PolynomialRing(Integers());
f := x^4 - x^2 - x + 1;
possibly_nonsurj_primes(f : cond := 3^8*23^2);
possibly_nonsurj_primes(f);
