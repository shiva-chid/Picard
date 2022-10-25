load "PicardConductor.m";

function possibly_nonsurj_primes_1mod3(f);
    cond := PicardConductor(f);
    possibly_C1image := C1test(f,cond);
    possibly_C3image := C3test(f,cond);
    possibly_C2image := C2test(f,cond);
    possibly_C6image := [7];
    return [possibly_C1image,possibly_C2image,possibly_C3image,possibly_C6image];
end function;

/*
P<x> := PolynomialRing(Integers());
f := x^4 - 1;
possibly_nonsurj_primes_1mod3(f);
*/
