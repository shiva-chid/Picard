Attach("GSp.m");

function xmat(x,bas);
// Expresses the 2x2 matrix corresponding to multiplication by an element x \in F_{l^2} in terms of the given basis bas of F_{l^2} over F_l.
    topfld := Universe(bas);
    l := Characteristic(topfld);
    degtop := Degree(topfld);
    degbas := ExactQuotient(degtop,#bas);
    basefld := GF(l,degbas);
    V, pi := VectorSpace(topfld, basefld, bas);
    return Matrix(basefld,#bas,#bas,[Eltseq(pi(x*b)) : b in bas]);
end function;

function gassman_dist(H,G : CCs := [], classfunc:=func<x|1>);
// Given a subgroup H in record format, and the overgroup G, return the gassman distribution of H as a subgroup of G
    if CCs eq [] then
        CCs := ConjugacyClasses(G);
        classfunc := ClassMap(G);
    end if;
    ordG := #G;
    ordH := H`order;
    if ordH eq ordG then
        return [CCs[i][2]/ordG : i in [1..#CCs]];
    end if;
    newdist := [0 : j in [1..#CCs]];
    CCH := (assigned H`classes) select H`classes else ConjugacyClasses(H`subgroup);
    for x in CCH do
        n := classfunc(x[3]);
        newdist[n] +:= x[2];
    end for;
    newdist := [x/ordH : x in newdist];
    return newdist;
end function;

function update_gassmandist_change_overgroup(distK_H,classfunc_HtoG,numb_CCG);
// For a subgroup K, given the gassman distribution of K as a subgroup of H, and a map from conjugacy classes of H into conjugacy classes of G
// (thought of as a SeqEnum for fixed sequences of conjugacy classes of H and G), and the number of conjugacy classes in G,
// return the gassman distribution of K as a subgroup of G.
    distK_G := [0/1 : i in [1..numb_CCG]];
    for i := 1 to #classfunc_HtoG do
        n := classfunc_HtoG[i];
        distK_G[n] +:= distK_H[i];
    end for;
    return distK_G;
end function;

/* TODO : Modify charpol_dist. The following is just copied from splitcase file.
function charpol_dist(H,G : CCs := [], charpols := []);
    if charpols ne [] then
        if H eq G then
            return [charpols[i,2]/#G : i in [1..#charpols]];
        end if;
        newdist := [0 : j in [1..#charpols]];
        CCH := ConjugacyClasses(H);
        charpolys := [x[1] : x in charpols];
        for x in CCH do
            n := Index(charpolys,CharacteristicPolynomial(x[3]));
            newdist[n] +:= x[2];
        end for;
        newdist := [x/#H : x in newdist];
        return newdist;
    end if;

    if CCs eq [] then
        CCs := ConjugacyClasses(G);
    end if;

    charpols := [];
    charpolnumbers := [];
    for i := 1 to #CCs do
        x := CCs[i,3];
        f := CharacteristicPolynomial(x);
        if not f in charpols then
            Append(~charpols,f);
            Append(~charpolnumbers,CCs[i,2]);
        else
            n := Index(charpols,f);
            charpolnumbers[n] := charpolnumbers[n]+CCs[i,2];
        end if;
    end for;

    if H eq G then
        return [x/#G : x in charpolnumbers];
    end if;
    newdist := [0 : j in [1..#charpols]];
    CCH := ConjugacyClasses(H);
    for x in CCH do
        n := Index(charpols,CharacteristicPolynomial(x[3]));
        newdist[n] +:= x[2];
    end for;
    newdist := [x/#H : x in newdist];
    return newdist;
end function;
*/

function uptoGconjugacy(G,ZK);
    l := #BaseRing(G);
    ZKtrue := [];
    if Type(ZK[1]) eq Rec then
        for i := 1 to #ZK do
            KK := ZK[i]`subgroup;
            KKord := ZK[i]`order;
            KKgassmandist := ZK[i]`distG;
            boo := false;
            ZKtrue_sub := [x : x in ZKtrue | x`order eq KKord and x`distG eq KKgassmandist];
            for j := 1 to #ZKtrue_sub do
                if IsConjugate(G,KK,ZKtrue_sub[j]`subgroup) then
                    boo := true;
                    break;
                end if;
            end for;
            if not boo then
                Append(~ZKtrue,ZK[i]);
            end if;
            if i mod 100 eq 0 then
                printf "Checked %o out of %o subgroups for conjugacy in G = GSp(6,%o)...\n", i, #ZK, l;
            end if;
        end for;
        printf "%o out of %o subgroups are distinct upto G-conjugacy where G = GSp(6,%o)\n\n", #ZKtrue, #ZK, l;
        return ZKtrue;
    else
        RF := recformat<order : Integers(), subgroup : GrpMat>;
        for i := 1 to #ZK do
            KK := ZK[i];
            KKord := #KK;
            boo := false;
            ZKtrue_sub := [x : x in ZKtrue | x`order eq KKord];
            for j := 1 to #ZKtrue_sub do
                if IsConjugate(G,KK,ZKtrue_sub[j]`subgroup) then
                    boo := true;
                    break;
                end if;
            end for;
            if not boo then
                KK_rec := rec<RF | order := KKord, subgroup := KK>;
                Append(~ZKtrue,KK_rec);
            end if;
            if i mod 100 eq 0 then
                printf "Checked %o out of %o subgroups for conjugacy in G = GSp(6,%o)...\n", i, #ZK, l;
            end if;
        end for;
        printf "%o out of %o subgroups are distinct upto G-conjugacy where G = GSp(6,%o)\n\n", #ZKtrue, #ZK, l;
        return ZKtrue;
    end if;
end function;


function subs_of_maxsub(G,H,K,ZDelU,ZH,maptoDelU,DelUinjG,l,CCDelU,classmapDelU,classfunc_DelUtoG,ordCCG);
    Kord := K`order;
    KinDelU := maptoDelU(K`subgroup);
    M := GModule(KinDelU);
/*
    Ul, il := UnitGroup(GF(l^2));
    det := hom<H -> Ul | [Determinant(maptoDelU(h))@@il : h in Generators(H)]>;
*/
    if not IsIrreducible(M) then
        if #DirectSumDecomposition(M) gt 1 then
            assert Kord eq #CU(1,l)*#CU(2,l)/(l-1);  // This is the maximal subgroup DelU(1) \perp DelU(2) with matching similitudes.
            ZK := [ZH[i] : i in [1..#ZH] | (not IsIrreducible(Mx)) and (#DirectSumDecomposition(Mx) gt 1) where Mx := GModule(ZDelU[i]`subgroup)];
            printf "(Decomposable case:) %o subgroups of DelU(3,%o) are contained in this maximal subgroup\nChecking for conjugacy in G = GSp(6,%o)...\n", #ZK, l, l;
            return uptoGconjugacy(G,ZK);
        end if;
        assert Kord eq l^3*#CU(1,l)*#GL(1,l^2); // This is the maximal subgrp l^(1+2) semidirect (GU(1) x GL(1,l^2))
        ZK := [ZH[i] : i in [1..#ZH] | (not IsIrreducible(Mx)) and (#DirectSumDecomposition(Mx) eq 1) where Mx := GModule(ZDelU[i]`subgroup)]; // TODO: So we are not listing all subgroups of this maximal subgroup here. Only those that are not contained in the other "decomposable" maximal subgroup above.
        printf "(Reducible indecomposable case:) %o subgroups of DelU(3,%o) are contained in this maximal subgroup, but not in the decomposable maximal subgroup\nChecking for conjugacy in G = GSp(6,%o)...\n", #ZK, l, l;
        return uptoGconjugacy(G,ZK);
    elif IsPrime(n) and (l-1)*(l+1) mod n eq 0 where n is ExactQuotient(#CU(3,l),Kord) then // l+1 is the index of SU(3,l) inside GU(3,l). l-1 is the index of GU(3,l) inside DelU(3,l)
        return []; // when the maximal subgroup of DelU(3,l) contains SU(3,l), we do not calculate any subgroups of it.
/*
        detK := det(K`subgroup);
        ZK := [x : x in ZH | det(x`subgroup) subset detK];
        printf "%o subgroups of this maximal subgroup have been found\nChecking for conjugacy in G = GSp(6,%o)...\n", #ZK, l;
        return uptoGconjugacy(G,ZK);
*/
    else
        ZKinDelU := Subgroups(KinDelU);
        DelU := CU(3,l);

        RF := recformat<order : Integers(), subgroup : GrpMat, classes : SeqEnum, distH : SeqEnum, distG : SeqEnum>;
        ZKinDelU_RF := [rec<RF | order := x`order, subgroup := x`subgroup, classes := ConjugacyClasses(x`subgroup)> : x in ZKinDelU];
//        delete(ZKinDelU);
        for i := 1 to #ZKinDelU_RF do
            ZKinDelU_RF[i]`distH := gassman_dist(ZKinDelU_RF[i],DelU : CCs := CCDelU, classfunc := classmapDelU);
            ZKinDelU_RF[i]`distG := update_gassmandist_change_overgroup(ZKinDelU_RF[i]`distH,classfunc_DelUtoG,ordCCG);
        end for;
        ZK := [rec<RF | order := x`order, subgroup := DelUinjG(x`subgroup), classes := [<y[1],y[2],DelUinjG(y[3])> : y in x`classes], distH := x`distH, distG := x`distG> : x in ZKinDelU_RF];
//        delete(ZKinDelU_RF);
        printf "This maximal subgroup has %o subgroups upto conjugacy in it\nChecking for conjugacy in G = GSp(6,%o)...\n", #ZK, l;
        return uptoGconjugacy(G,ZK);
    end if;
end function;


function precomputation_nonsplitcase(l);
/*
    Fl := Integers(l);
    G := GSp(6,l);
    SG := Symp(6,l);
    Gl := GL(3,Fl);
    zeromat := ZeroMatrix(Fl,3);
    idmat := IdentityMatrix(Fl,3);
    antidiagidmat := Matrix(Fl,3,3,[[i+j eq 4 select 1 else 0 : j in [1..3]] : i in [1..3]]);
    permmat := GL(6,Fl) ! DirectSum(idmat,antidiagidmat);
    H := MatrixGroup<6, Fl | [BlockMatrix(2,2,[Matrix(A),zeromat,zeromat,Transpose(A^-1)]) : A in Generators(Gl)]>;
    H := Conjugate(H,permmat^-1);
    H := sub<G | H>;
    assert #H eq #GL(3,Fl);
*/

    Fl := GF(l);
    Flsq := GF(l,2);
    xi := (Flsq.1)^(ExactQuotient(l+1,2));
/*
    G := GSp(6,l);
*/
    G := CSp(6,l);
/*
    SG := Symp(6,l);
*/
    DelU := CU(3,l);
    Gu := GU(3,l);
    Su := SU(3,l);

    permmat := PermutationMatrix(Fl,[1,5,3,4,2,6]);
    bas := [1,1/(2*xi^l)];
    DelUinjG := hom<DelU -> G | [ permmat*BlockMatrix(3,3,[[xmat(g[j,k],bas) : k in [1..3]] : j in [1..3]])*permmat where g is DelU.i : i in [1..#Generators(DelU)]]>;
    assert #Kernel(DelUinjG) eq 1;
    H := DelUinjG(DelU);
    maptoDelU := Inverse(DelUinjG);


    CCG := ConjugacyClasses(G); classmapG := ClassMap(G);
    CCDelU := ConjugacyClasses(DelU); classmapDelU := ClassMap(DelU);
    classfunc_DelUtoG := [classmapG(DelUinjG(CCDelU[i,3])) : i in [1..#CCDelU]];

    MDelU := MaximalSubgroups(DelU);
    RF := recformat<order : Integers(), subgroup : GrpMat, classes : SeqEnum, distH : SeqEnum, distG : SeqEnum>;
    MDelU_RF := [rec<RF | order := x`order, subgroup := x`subgroup, classes := ConjugacyClasses(x`subgroup)> : x in MDelU];
//    delete(MDelU);
    for i := 1 to #MDelU_RF do
        MDelU_RF[i]`distH := gassman_dist(MDelU_RF[i],DelU : CCs := CCDelU, classfunc := classmapDelU);
        MDelU_RF[i]`distG := update_gassmandist_change_overgroup(MDelU_RF[i]`distH,classfunc_DelUtoG,#CCG);
    end for;
    MH := [rec<RF | order := x`order, subgroup := DelUinjG(x`subgroup), classes := [<y[1],y[2],DelUinjG(y[3])> : y in x`classes], distH := x`distH, distG := x`distG> : x in MDelU_RF];
    printf "There are %o maximal subgroups of DelU(3,F_%o) upto conjugacy in it\n", #MH, l;
//    delete(MDelU_RF);
    MHtrue := uptoGconjugacy(G,MH);
//    delete(MH);
    printf "There are %o maximal subgroups of DelU(3,F_%o) upto conjugacy in G = GSp(6,%o)\n", #MHtrue, l, l;
    printf "Their orders and index in DelU(3,F_%o) are:\n", l;
//    printf "%o\n", [<x`order,#H/x`order> : x in MHtrue];
    printf "%o\n", [<x`order,#DelU/x`order> : x in MHtrue];

//    ZH := Subgroups(H);
    ZDelU := Subgroups(DelU);
    ZDelU_RF := [rec<RF | order := x`order, subgroup := x`subgroup, classes := ConjugacyClasses(x`subgroup)> : x in ZDelU];
//    delete(ZDelU);
    for i := 1 to #ZDelU_RF do
        ZDelU_RF[i]`distH := gassman_dist(ZDelU_RF[i],DelU : CCs := CCDelU, classfunc := classmapDelU);
        ZDelU_RF[i]`distG := update_gassmandist_change_overgroup(ZDelU_RF[i]`distH,classfunc_DelUtoG,#CCG);
    end for;
    ZH := [rec<RF | order := x`order, subgroup := DelUinjG(x`subgroup), classes := [<y[1],y[2],DelUinjG(y[3])> : y in x`classes], distH := x`distH, distG := x`distG> : x in ZDelU_RF];
    printf "There are %o subgroups of DelU(3,F_%o) upto conjugacy in it\n", #ZH, l;
/*
    ZHs := uptoGconjugacy(G,ZH);
    printf "There are %o subgroups of DelU(3,%o) upto conjugacy in G = GSp(6,%o)\n", #ZHs, l, l;
*/
    printf "Working using these %o subgroups of DelU(3,%o), which are not necessarily distinct upto G-conjugacy, where G = GSp(6,%o).\n\n", #ZH, l, l;
    ZHtrue := [subs_of_maxsub(G,H,K,ZDelU_RF,ZH,maptoDelU,DelUinjG,l,CCDelU,classmapDelU,classfunc_DelUtoG,#CCG) : K in MHtrue];
//    delete ZH;


    charpolys := [];
    charpolynumbers := [];
    cctocharpol := [];
    for i := 1 to #CCG do
        x := CCG[i,3];
        f := CharacteristicPolynomial(x);
        if not f in charpolys then
            Append(~charpolys,f);
            Append(~charpolynumbers,CCG[i,2]);
            Append(~cctocharpol,#charpolys);
        else
            n := Index(charpolys,f);
            charpolynumbers[n] := charpolynumbers[n] + CCG[i,2];
            Append(~cctocharpol,n);
        end if;
    end for;
    charpols := [<charpolys[i],charpolynumbers[i]> : i in [1..#charpolys]];
    printf "There are %o conjugacy classes in GSp(6,F_%o), which give %o distinct characteristic polynomials\n\n", #CCG, l, #charpols;

    ccstats := [[subK`distG : subK in K] : K in ZHtrue];

    charpolstats := [];
    for i := 1 to #ccstats do
        temp := [];
        printf "Starting computation of charpol distribution stats for each subgroup of the %oth maximal subgroup...\n", i;
        for j := 1 to #ccstats[i] do
            dat := ccstats[i,j];
            charpoldat := [&+[dat[l] : l in [1..#dat] | cctocharpol[l] eq k] : k in [1..#charpols]];
            Append(~temp,charpoldat);
            if j mod 100 eq 0 then
                printf "Computed charpol distribution stats for %o subgroups...\n", j;
            end if;
        end for;
        Append(~charpolstats,temp);
        printf "Done computing charpol distribution stats for all subgroups of the %oth maximal subgroup\n\n", i;
    end for;

    all_ccstats := [];
    subs_with_ccstat := [];
    for i := 1 to #ccstats do
        tempccstats := [];
        tempsubs := [];
        for j := 1 to #ccstats[i] do
            if not ccstats[i,j] in tempccstats then
                Append(~tempccstats,ccstats[i,j]);
                Append(~tempsubs,[ZHtrue[i,j]]);
            else
                n := Index(tempccstats,ccstats[i,j]);
                Append(~tempsubs[n],ZHtrue[i,j]);
            end if;
        end for;
        Append(~all_ccstats,tempccstats);
        Append(~subs_with_ccstat,tempsubs);
    end for;
    all_charpolstats := [];
    subs_with_charpolstat := [];
    for i := 1 to #charpolstats do
        tempcharpolstats := [];
        tempsubs := [];
        for j := 1 to #charpolstats[i] do
            if not charpolstats[i,j] in tempcharpolstats then
                Append(~tempcharpolstats,charpolstats[i,j]);
                Append(~tempsubs,[ZHtrue[i,j]]);
            else
                n := Index(tempcharpolstats,charpolstats[i,j]);
                Append(~tempsubs[n],ZHtrue[i,j]);
            end if;
        end for;
        Append(~all_charpolstats,tempcharpolstats);
        Append(~subs_with_charpolstat,tempsubs);
    end for;

    printf "For each maximal subgroup of DelU(3,F_%o), its factored index in DelU(3,F_%o), the number of subgroups contained in it, the number of distinct cc distribution stats of subgroups, the number of distinct charpol distribution stats of subgroups are shown below\n:", l, l;
    for i := 1 to #ZHtrue do
        printf "%o, %o, %o, %o", Factorisation(ExactQuotient(#DelU,MHtrue[i]`order)), #ZHtrue[i], #all_ccstats[i], #all_charpolstats[i];
    end for;

    subs_with_ccstat_GLconjinfo := [];
    for i := 1 to #all_ccstats do
        tempsubs := [];
        for j := 1 to #all_ccstats[i] do
            temp := [];
            subs := subs_with_ccstat[i,j];
            for k := 1 to #subs do
                K := subs[k]`subgroup;
                bool := true;
                for ll := 1 to #temp do
                    if IsConjugate(GL(6,Fl),K,temp[ll,1]`subgroup) then
                        temp[ll] := temp[ll] cat [subs[k]];
                        bool := false;
                        break;
                    end if;
                end for;
                if bool then
                    Append(~temp,[subs[k]]);
                end if;
            end for;
            Append(~tempsubs,temp);
        end for;
        Append(~subs_with_ccstat_GLconjinfo,tempsubs);
    end for;

    subs_with_charpolstat_GLconjinfo := [];
    for i := 1 to #all_charpolstats do
        tempsubs := [];
        for j := 1 to #all_charpolstats[i] do
            temp := [];
            subs := subs_with_charpolstat[i,j];
            for k := 1 to #subs do
                K := subs[k]`subgroup;
                bool := true;
                for ll := 1 to #temp do
                    if IsConjugate(GL(6,Fl),K,temp[ll,1]`subgroup) then
                        temp[ll] := temp[ll] cat [subs[k]];
                        bool := false;
                        break;
                    end if;
                end for;
                if bool then
                    Append(~temp,[subs[k]]);
                end if;
            end for;
            Append(~tempsubs,temp);
        end for;
        Append(~subs_with_charpolstat_GLconjinfo,tempsubs);
    end for;

    return G, H, MHtrue, ZHtrue, CCG, classmapG, charpols, cctocharpol, ccstats, charpolstats, all_ccstats, all_charpolstats, subs_with_ccstat_GLconjinfo, subs_with_charpolstat_GLconjinfo;
end function;

/*
time G, H, MH, ZH, CCs, class, charpols, cctocharpol, ccstats, charpolstats, all_ccstats, all_charpolstats, subs_with_ccstat_GLconjinfo, subs_with_charpolstat_GLconjinfo := precomputation_nonsplitcase(5);

PrintFile("all_data_5.txt", "Hgens := ");
PrintFileMagma("all_data_5.txt", [Eltseq(h) : h in Generators(H)]);
PrintFile("all_data_5.txt", ";");

PrintFile("all_data_5.txt", "H := sub<G|Hgens>;");

PrintFile("all_data_5.txt", "MH := ");
PrintFileMagma("all_data_5.txt", MH);
PrintFile("all_data_5.txt", ";");

PrintFile("all_data_5.txt", "ZH := ");
PrintFileMagma("all_data_5.txt", ZH);
PrintFile("all_data_5.txt", ";");

PrintFile("all_data_5.txt", "CCs := ");
PrintFileMagma("all_data_5.txt", CCs);
PrintFile("all_data_5.txt", ";");

PrintFile("all_data_5.txt", "charpols := ");
PrintFileMagma("all_data_5.txt", charpols);
PrintFile("all_data_5.txt", ";");

PrintFile("all_data_5.txt", "cctocharpol := ");
PrintFileMagma("all_data_5.txt", cctocharpol);
PrintFile("all_data_5.txt", ";");

PrintFile("all_data_5.txt", "ccstats := ");
PrintFileMagma("all_data_5.txt", ccstats);
PrintFile("all_data_5.txt", ";");

PrintFile("all_data_5.txt", "charpolstats := ");
PrintFileMagma("all_data_5.txt", charpolstats);
PrintFile("all_data_5.txt", ";");

PrintFile("all_data_5.txt", "all_ccstats := ");
PrintFileMagma("all_data_5.txt", all_ccstats);
PrintFile("all_data_5.txt", ";");

PrintFile("all_data_5.txt", "all_charpolstats := ");
PrintFileMagma("all_data_5.txt", all_charpolstats);
PrintFile("all_data_5.txt", ";");

PrintFile("all_data_5.txt", "subs_with_ccstat_GLconjinfo := ");
PrintFileMagma("all_data_5.txt", subs_with_ccstat_GLconjinfo);
PrintFile("all_data_5.txt", ";");

PrintFile("all_data_5.txt", "subs_with_charpolstat_GLconjinfo := ");
PrintFileMagma("all_data_5.txt", subs_with_charpolstat_GLconjinfo);
PrintFile("all_data_5.txt", ";");
*/



