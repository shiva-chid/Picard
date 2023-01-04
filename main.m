load "PicardConductor.m";
load "maxgrp_containment_tests.m";

function possibly_nonsurj_primes(f : cond := 1);
    if cond eq 1 then
        cond := PicardConductor(f);
    end if;
    possibly_C1image := C1test(f,cond);
    possibly_C3image := C3test(f,cond);
    possibly_C2image := C2test(f,cond);
    return [[2,3,5,7], PrimeFactors(cond), possibly_C1image, possibly_C3image, possibly_C2image];
end function;


P<x> := PolynomialRing(Integers());
f := x^4 - x^2 - x + 1;
possibly_nonsurj_primes(f : cond := 3^8*23^2);


