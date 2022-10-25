function PicardConductor(f);
    cmd := Sprintf("\"from sage.all import QQ, PolynomialRing; from picard_curves import PicardCurve; R = PolynomialRing(QQ,'x'); print(PicardCurve(R(%o)).cond)\"", Coefficients(f));
    val := Pipe("cd picard_curves\n sage -python -c " cat cmd, "");
    val := Split(val,"[(,)] \n");
    val := [StringToInteger(x) : x in val];
    assert #val mod 2 eq 0;
    return &*[val[2*i-1]^val[2*i] : i in [1..ExactQuotient(#val,2)]];
end function;
