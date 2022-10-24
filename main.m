function PicardConductor(f);
    cmd := Sprintf("\"from sage.all import QQ, PolynomialRing; from picard_curves import PicardCurve; R = PolynomialRing(QQ,'x'); print(PicardCurve(R(%o)).cond)\"", Coefficients(f));
    val := Pipe("cd picard_curves\n sage -python -c " cat cmd, "");
    val := Split(val,"[(,)] \n");
    val := [StringToInteger(x) : x in val];
    assert #val mod 2 eq 0;
    return &*[val[2*i-1]^val[2*i] : i in [1..ExactQuotient(#val,2)]];
end function;

function possibly_nonsurj_primes_1mod3(f);
    cond := PicardConductor(f);
    possibly_C1image := C1test(f,cond);
    possibly_C3image := C3test(f,cond);
    possibly_C2image := C2test(f,cond);
    possibly_C6image := [7];
    return [possibly_C1image,possibly_C2image,possibly_C3image,possibly_C6image];
end function;

P<x> := PolynomialRing(Integers());
f := x^4 - 1;
possibly_nonsurj_primes_1mod3(f);
