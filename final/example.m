//////////////////////////////
////       Example        ////
//////////////////////////////

AttachSpec("spec");

P<x> := PolynomialRing(Integers());
f := x^4 - x^2 - x + 1;
possibly_nonsurj_primes(f : radical_cond := 3*23, primes_bound := 1000);
possibly_nonsurj_primes(f); // returns possibly non surjective primes for the Picard curve y^3 = x^4 - x^2 - x + 1


h := x+1;
possibly_nonsurj_primes(f,h); // returns possibly non surjective primes for the Picard curve (x + 1) y^3 = x^4 - x^2 - x + 1
