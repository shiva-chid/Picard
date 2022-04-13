Attach("GSp.m");

function gassman_dist(H,G : CCs := [], classfunc:=func<x|1>);
    if CCs eq [] then
        CCs := ConjugacyClasses(G);
        classfunc := ClassMap(G);
    end if;
    if H eq G then
        return [CCs[i][2]/#G : i in [1..#CCs]];
    end if;
    /*
    if #H gt 2000 then
        return [#(Set(H) meet Orbit(G,CCs[i][3]))/#H : i in [1..#CCs]];
    end if;
    */
    newdist := [0 : j in [1..#CCs]];
    CCH := ConjugacyClasses(H);
    for x in CCH do
        n := classfunc(x[3]);
        newdist[n] +:= x[2];
    end for;
    newdist := [x/#H : x in newdist];
    return newdist;
end function;


function precomputation_splitcase(l);
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

    MH := MaximalSubgroups(H);
    MHtrue := [];
    for i := 1 to #MH do
        K := MH[i]`subgroup;
        boo := false;
        for j := 1 to #MHtrue do
            if IsConjugate(G,K,MHtrue[j]`subgroup) then
                boo := true;
                break;
            end if;
        end for;
        if not boo then
            Append(~MHtrue,MH[i]);
        end if;
        if i mod 10 eq 0 then
            printf "Checked the first %o maximal subgroups of GL(3,F_%o) for conjugacy in G...\n", i, l;
        end if;
    end for;
    printf "There are %o maximal subgroups of GL(3,F_%o) upto conjugacy in G\n", #MHtrue, l;
    printf "Their orders and index in GL(3,F_%o) are:\n", l;
    printf "%o\n", [<x`order,#H/x`order> : x in MHtrue];

    ZHs := [];
    ZHtrues := [];
    for i := 1 to #MHtrue do
        K := MHtrue[i]`subgroup;
        ZK := Subgroups(K);
        printf "The %oth maximal subgroup has %o subgroups upto conjugacy in it\n", i, #ZK;
        Append(~ZHs,ZK);
        ZKtrue := [];
        for j := 1 to #ZK do
            KK := ZK[j]`subgroup;
            boo := false;
            for k := 1 to #ZKtrue do
                if IsConjugate(G,KK,ZKtrue[k]`subgroup) then
                    boo := true;
                    break;
                end if;
            end for;
            if not boo then
                Append(~ZKtrue,ZK[j]);
            end if;
            if j mod 100 eq 0 then
                printf "Done checking for conjugacy inside G for %o of these subgroups...\nFound %o distinct subgroups upto G-conjugacy...\n", j, #ZKtrue;
            end if;
        end for;
        printf "The %ost maximal subgroup has %o subgroups upto conjugacy in G\n\n", i, #ZKtrue;
        Append(~ZHtrues,ZKtrue);
    end for;

    CCs := ConjugacyClasses(G);
    class := ClassMap(G);
    charpols := [];
    cctocharpol := [];
    for i := 1 to #CCs do
        x := CCs[i,3];
        f := CharacteristicPolynomial(x);
        if not f in charpols then
            Append(~charpols,f);
            Append(~cctocharpol,#charpols);
        else
            Append(~cctocharpol,Index(charpols,f));
        end if;
    end for;
    printf "There are %o conjugacy classes in GSp(6,F_%o), which give %o distinct characteristic polynomials\n\n", #CCs, l, #charpols;

    ccstats := [];
    for i := 1 to #ZHtrues do
        printf "Starting computation of cc distribution stats for each subgroup of the %oth maximal subgroup...\n", i;
        temp := [];
        for j := 1 to #ZHtrues[i] do
            K := ZHtrues[i][j]`subgroup;
            Append(~temp,gassman_dist(K,G : CCs := CCs, classfunc := class));
            if j mod 100 eq 0 then
                printf "Computed cc distribution stats for %o subgroups...\n", j;
            end if;
        end for;
        Append(~ccstats,temp);
        printf "Done computing cc distribution stats for all subgroups of the %oth maximal subgroup\n\n", i;
    end for;

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

    printf "For each maximal subgroup of GL(3,F_%o), its factored index in GL(3,F_%o), the number of subgroups contained in it, the number of distinct cc distribution stats of subgroups, the number of distinct charpol distribution stats of subgroups are shown below\n:", l, l;
    for i := 1 to #ZHtrues do
        printf "%o, %o, %o, %o", Factorisation(ExactQuotient(#H,MHtrue[i]`order)), #ZHtrues[i], #Set(ccstats[i]), #Set(charpolstats[i]);
    end for;

    all_ccstats := [];
    subs_with_ccstat := [];
    for i := 1 to #ccstats do
        tempccstats := [];
        tempsubs := [];
        for j := 1 to #ccstats[i] do
            if not ccstats[i,j] in tempccstats then
                Append(~tempccstats,ccstats[i,j]);
                Append(~tempsubs,[ZHtrues[i,j]]);
            else
                n := Index(tempccstats,ccstats[i,j]);
                Append(~tempsubs[n],ZHtrues[i,j]);
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
                Append(~tempsubs,[ZHtrues[i,j]]);
            else
                n := Index(tempcharpolstats,charpolstats[i,j]);
                Append(~tempsubs[n],ZHtrues[i,j]);
            end if;
        end for;
        Append(~all_charpolstats,tempcharpolstats);
        Append(~subs_with_charpolstat,tempsubs);
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
                for l := 1 to #temp do
                    if IsConjugate(GL(6,Fl),K,temp[l,1]`subgroup) then
                        temp[l] := temp[l] cat [subs[k]];
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
                for l := 1 to #temp do
                    if IsConjugate(GL(6,Fl),K,temp[l,1]`subgroup) then
                        temp[l] := temp[l] cat [subs[k]];
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

/*
    for twotorsimgind := 1 to #possZGs_large do
        All_ccstats := SetToSequence(Set(CCstats_large[twotorsimgind]));
        Subs_with_ccstat := [[possZGs_large[twotorsimgind][k] : k in [j : j in [1..#possZGs_large[twotorsimgind]] | CCstats_large[twotorsimgind,j] eq y]] : y in All_ccstats];
        Subs_with_ccstat_GLconjinfo := [];
        for k := 1 to #Subs_with_ccstat do
        subs := Subs_with_ccstat[k];
        temp := [];
        for l := 1 to #subs do
            H := subs[l]`subgroup;
            bool := true;
            for m := 1 to #temp do
            if IsConjugate(BigG,H,temp[m][1]`subgroup) then
                temp[m] := temp[m] cat [subs[l]];
                bool := false;
                break;
            end if;
            end for;
            if bool then
            Append(~temp,[subs[l]]);
            end if;
        end for;
        Append(~Subs_with_ccstat_GLconjinfo,temp);
        end for;
        Append(~all_ccstats_large, All_ccstats);
        Append(~subs_with_ccstat_large, Subs_with_ccstat);
        Append(~subs_with_ccstat_GLconjinfo_large, Subs_with_ccstat_GLconjinfo);
    end for;
*/


    return G, H, MHtrue, ZHtrues, CCs, class, charpols, cctocharpol, ccstats, charpolstats, all_ccstats, all_charpolstats, subs_with_ccstat_GLconjinfo, subs_with_charpolstat_GLconjinfo;
end function;

/*
G, H, MH, ZH, CCs, class, charpols, cctocharpol, ccstats, charpolstats, all_ccstats, all_charpolstats, subs_with_ccstat_GLconjinfo, subs_with_charpolstat_GLconjinfo := precomputation_splitcase(7);

PrintFile("all_data_7.txt", "Hgens := ");
PrintFileMagma("all_data_7.txt", [Eltseq(h) : h in Generators(H)]);
PrintFile("all_data_7.txt", ";");

PrintFile("all_data_7.txt", "H := sub<G|Hgens>;");

PrintFile("all_data_7.txt", "MH := ");
PrintFileMagma("all_data_7.txt", MH);
PrintFile("all_data_7.txt", ";");

PrintFile("all_data_7.txt", "ZH := ");
PrintFileMagma("all_data_7.txt", ZH);
PrintFile("all_data_7.txt", ";");

PrintFile("all_data_7.txt", "CCs := ");
PrintFileMagma("all_data_7.txt", CCs);
PrintFile("all_data_7.txt", ";");

PrintFile("all_data_7.txt", "charpols := ");
PrintFileMagma("all_data_7.txt", charpols);
PrintFile("all_data_7.txt", ";");

PrintFile("all_data_7.txt", "cctocharpol := ");
PrintFileMagma("all_data_7.txt", cctocharpol);
PrintFile("all_data_7.txt", ";");

PrintFile("all_data_7.txt", "ccstats := ");
PrintFileMagma("all_data_7.txt", ccstats);
PrintFile("all_data_7.txt", ";");

PrintFile("all_data_7.txt", "charpolstats := ");
PrintFileMagma("all_data_7.txt", charpolstats);
PrintFile("all_data_7.txt", ";");

PrintFile("all_data_7.txt", "all_ccstats := ");
PrintFileMagma("all_data_7.txt", all_ccstats);
PrintFile("all_data_7.txt", ";");

PrintFile("all_data_7.txt", "all_charpolstats := ");
PrintFileMagma("all_data_7.txt", all_charpolstats);
PrintFile("all_data_7.txt", ";");

PrintFile("all_data_7.txt", "subs_with_ccstat_GLconjinfo := ");
PrintFileMagma("all_data_7.txt", subs_with_ccstat_GLconjinfo);
PrintFile("all_data_7.txt", ";");

PrintFile("all_data_7.txt", "subs_with_charpolstat_GLconjinfo := ");
PrintFileMagma("all_data_7.txt", subs_with_charpolstat_GLconjinfo);
PrintFile("all_data_7.txt", ";");
*/
