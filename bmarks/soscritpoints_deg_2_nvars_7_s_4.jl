using Pkg; Pkg.activate("../")
using genFGLM
P, (x1, x2, x3, x4, x5, x6, x7)  = polynomial_ring(GF(65521), ["x1", "x2", "x3", "x4", "x5", "x6", "x7"]);
F = [2824*x1^4+7500*x1^3*x3+288*x1^3*x5-1100*x1^2*x2*x5+5625*x1^2*x3^2-1332*x1^2*x3*x6-7744*x1^2*x4^2+352*x1^2*x4*x6-1400*x1^2*x4*x7+3520*x1^2*x5^2+2952*x1^2*x5*x6+125*x1^2*x6^2+5600*x1^2*x6*x7-1650*x1*x2*x3*x5-16*x1*x2*x3*x6-3008*x1*x2*x4*x6-2048*x1*x2*x6^2-160*x1*x3^2*x4-110*x1*x3^2*x6-12000*x1*x3*x4^2-2100*x1*x3*x4*x7-592*x1*x3*x5*x6+8400*x1*x3*x6*x7-2080*x1*x4^3-1430*x1*x4^2*x6+1536*x1*x5^3+1312*x1*x5^2*x6+16*x2^2*x3^2-40*x2^2*x3*x6+121*x2^2*x5^2+8861*x2^2*x6^2+940*x2*x3^2*x6+1760*x2*x4^2*x5+12220*x2*x4^2*x6+308*x2*x4*x5*x7-1232*x2*x5*x6*x7+25*x3^4+650*x3^2*x4^2+1369*x3^2*x6^2-7104*x3*x5^2*x6-6068*x3*x5*x6^2+10625*x4^4+2240*x4^3*x7-8960*x4^2*x6*x7+196*x4^2*x7^2-1568*x4*x6*x7^2+9216*x5^4+15744*x5^3*x6+6724*x5^2*x6^2+3136*x6^2*x7^2-864*x1^2*x4+28*x1^2*x6-56*x1*x2*x3+26*x1*x2*x6+2304*x1*x3*x4+1584*x1*x3*x6-384*x1*x4*x5+88*x2^2*x3-110*x2^2*x6-13536*x2*x3*x6-720*x3^3-9360*x3*x4^2+1776*x3*x4*x6-4608*x4*x5^2-3936*x4*x5*x6+49*x1^2-154*x1*x2+344*x1*x6+121*x2^2-688*x2*x3+860*x2*x6+5184*x3^2+576*x4^2+1204*x1-1892*x2+7396, -1100*x1^2*x5-1650*x1*x3*x5-16*x1*x3*x6-3008*x1*x4*x6-2048*x1*x6^2+32*x2*x3^2-80*x2*x3*x6+242*x2*x5^2+17722*x2*x6^2+940*x3^2*x6+1760*x4^2*x5+12220*x4^2*x6+308*x4*x5*x7-1232*x5*x6*x7-56*x1*x3+26*x1*x6+176*x2*x3-220*x2*x6-13536*x3*x6-154*x1+242*x2-688*x3+860*x6-1892, 7500*x1^3+11250*x1^2*x3-1332*x1^2*x6-1650*x1*x2*x5-16*x1*x2*x6-320*x1*x3*x4-220*x1*x3*x6-12000*x1*x4^2-2100*x1*x4*x7-592*x1*x5*x6+8400*x1*x6*x7+32*x2^2*x3-40*x2^2*x6+1880*x2*x3*x6+100*x3^3+1300*x3*x4^2+2738*x3*x6^2-7104*x5^2*x6-6068*x5*x6^2-56*x1*x2+2304*x1*x4+1584*x1*x6+88*x2^2-13536*x2*x6-2160*x3^2-9360*x4^2+1776*x4*x6-688*x2+10368*x3, -15488*x1^2*x4+352*x1^2*x6-1400*x1^2*x7-3008*x1*x2*x6-160*x1*x3^2-24000*x1*x3*x4-2100*x1*x3*x7-6240*x1*x4^2-2860*x1*x4*x6+3520*x2*x4*x5+24440*x2*x4*x6+308*x2*x5*x7+1300*x3^2*x4+42500*x4^3+6720*x4^2*x7-17920*x4*x6*x7+392*x4*x7^2-1568*x6*x7^2-864*x1^2+2304*x1*x3-384*x1*x5-18720*x3*x4+1776*x3*x6-4608*x5^2-3936*x5*x6+1152*x4, 288*x1^3-1100*x1^2*x2+7040*x1^2*x5+2952*x1^2*x6-1650*x1*x2*x3-592*x1*x3*x6+4608*x1*x5^2+2624*x1*x5*x6+242*x2^2*x5+1760*x2*x4^2+308*x2*x4*x7-1232*x2*x6*x7-14208*x3*x5*x6-6068*x3*x6^2+36864*x5^3+47232*x5^2*x6+13448*x5*x6^2-384*x1*x4-9216*x4*x5-3936*x4*x6, -1332*x1^2*x3+352*x1^2*x4+2952*x1^2*x5+250*x1^2*x6+5600*x1^2*x7-16*x1*x2*x3-3008*x1*x2*x4-4096*x1*x2*x6-110*x1*x3^2-592*x1*x3*x5+8400*x1*x3*x7-1430*x1*x4^2+1312*x1*x5^2-40*x2^2*x3+17722*x2^2*x6+940*x2*x3^2+12220*x2*x4^2-1232*x2*x5*x7+2738*x3^2*x6-7104*x3*x5^2-12136*x3*x5*x6-8960*x4^2*x7-1568*x4*x7^2+15744*x5^3+13448*x5^2*x6+6272*x6*x7^2+28*x1^2+26*x1*x2+1584*x1*x3-110*x2^2-13536*x2*x3+1776*x3*x4-3936*x4*x5+344*x1+860*x2, -1400*x1^2*x4+5600*x1^2*x6-2100*x1*x3*x4+8400*x1*x3*x6+308*x2*x4*x5-1232*x2*x5*x6+2240*x4^3-8960*x4^2*x6+392*x4^2*x7-3136*x4*x6*x7+6272*x6^2*x7];
sort!(F, by = p -> total_degree(p));
id = ideal(P,F);
vrs = gens(base_ring(id))
comp_id = ideal(base_ring(id), [vrs[1]*vrs[2], vrs[1]*vrs[3], vrs[2]*vrs[3]])
gen_fglm(comp_id, just_hypersurface=true)
@time gen_fglm(id, just_hypersurface=true);

println("-----------")
println("comparing to elim method")
gb = groebner_basis_f4(id, complete_reduction = true)
lts = (leading_monomial).(gens(gb))
mis = genFGLM.maximal_ind_set(lts)
isok = false
R = base_ring(id)
k = 1
while k <= length(gens(R))
    if mis == gens(R)[k:end]
        global isok = true
        break
    end
    global k += 1
end
println("MIS is last variables: $(isok)")
tim2 = @elapsed groebner_basis_f4(id, eliminate = k - 2, info_level = 2)
println("time elim $(tim2)")
exit()