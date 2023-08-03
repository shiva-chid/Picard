//////////////////////////////
////       Example        ////
//////////////////////////////

AttachSpec("spec");

P<x> := PolynomialRing(Integers());
f := x^4 - x^2 - x + 1;
possibly_nonsurj_primes(f : radical_cond := 3*23, primes_bound := 1000);
possibly_nonsurj_primes(f);



