using Pkg; Pkg.activate("../")
using genFGLM
P, (x1, x2, x3, x4, x5, x6, y1, y2, y3, y4, y5, y6)  = polynomial_ring(GF(1840109), ["x1", "x2", "x3", "x4", "x5", "x6", "y1", "y2", "y3", "y4", "y5", "y6"]);
F = [-46*x1^2-33*x1*x2+87*x1*x3-34*x1*x4+40*x1*x5+77*x1*x6-10*x2^2-65*x2*x3-85*x2*x4+54*x2*x5+52*x3^2+36*x3*x4+91*x3*x5-22*x3*x6-27*x4^2+50*x4*x5+60*x4*x6-47*x5^2-97*x5*x6-31*x6^2+x1+18*x2+51*x3-91*x4-2*x5+25*x6+31, -27*x1^2+65*x1*x2+88*x1*x3+10*x1*x4-6*x1*x5+80*x1*x6+57*x2^2-49*x2*x3+31*x2*x4+73*x2*x5+95*x2*x6-29*x3^2+5*x3*x4-26*x3*x5-51*x3*x6+97*x4^2-67*x4*x5+58*x4*x6+37*x5^2+5*x5*x6-57*x6^2-84*x1+68*x2+88*x3+29*x4-36*x5+85*x6+80, 90*x1^2+74*x1*x2+27*x1*x3+9*x1*x4-91*x1*x5+81*x1*x6-12*x2^2+78*x2*x3+5*x2*x4-63*x2*x5-5*x2*x6-8*x3^2+30*x3*x4-3*x3*x5-56*x3*x6-70*x4^2+42*x4*x5+9*x4*x6-27*x5^2-79*x5*x6-51*x6^2+65*x1+36*x2-91*x3-21*x4-22*x5+16*x6-85, -44*x1^2-31*x1*x2+45*x1*x3+49*x1*x4-58*x1*x5+49*x1*x6-95*x2^2+86*x2*x3-97*x2*x4-14*x2*x5+83*x2*x6-8*x3^2-54*x3*x4+62*x3*x5+96*x3*x6+89*x4^2+14*x4*x5-79*x4*x6-95*x5^2+61*x5*x6+86*x6^2+x1-96*x2-51*x3-58*x4-2*x5+57*x6-35, 57*x1^2+28*x1*x2+63*x1*x3+21*x1*x4-71*x1*x5-66*x1*x6+72*x2^2-40*x2*x3-68*x2*x4-15*x2*x5-32*x2*x6+87*x3^2-60*x3*x4+7*x3*x5-61*x3*x6-50*x4^2-22*x4*x5+48*x4*x6+46*x5^2-49*x5*x6+18*x6^2-34*x1+17*x2+45*x3-82*x4-66*x5+16*x6-22, -46*y1^2-33*y1*y2+87*y1*y3-34*y1*y4+40*y1*y5+77*y1*y6-10*y2^2-65*y2*y3-85*y2*y4+54*y2*y5+52*y3^2+36*y3*y4+91*y3*y5-22*y3*y6-27*y4^2+50*y4*y5+60*y4*y6-47*y5^2-97*y5*y6-31*y6^2+y1+18*y2+51*y3-91*y4-2*y5+25*y6+31, -27*y1^2+65*y1*y2+88*y1*y3+10*y1*y4-6*y1*y5+80*y1*y6+57*y2^2-49*y2*y3+31*y2*y4+73*y2*y5+95*y2*y6-29*y3^2+5*y3*y4-26*y3*y5-51*y3*y6+97*y4^2-67*y4*y5+58*y4*y6+37*y5^2+5*y5*y6-57*y6^2-84*y1+68*y2+88*y3+29*y4-36*y5+85*y6+80, 90*y1^2+74*y1*y2+27*y1*y3+9*y1*y4-91*y1*y5+81*y1*y6-12*y2^2+78*y2*y3+5*y2*y4-63*y2*y5-5*y2*y6-8*y3^2+30*y3*y4-3*y3*y5-56*y3*y6-70*y4^2+42*y4*y5+9*y4*y6-27*y5^2-79*y5*y6-51*y6^2+65*y1+36*y2-91*y3-21*y4-22*y5+16*y6-85, -44*y1^2-31*y1*y2+45*y1*y3+49*y1*y4-58*y1*y5+49*y1*y6-95*y2^2+86*y2*y3-97*y2*y4-14*y2*y5+83*y2*y6-8*y3^2-54*y3*y4+62*y3*y5+96*y3*y6+89*y4^2+14*y4*y5-79*y4*y6-95*y5^2+61*y5*y6+86*y6^2+y1-96*y2-51*y3-58*y4-2*y5+57*y6-35, 57*y1^2+28*y1*y2+63*y1*y3+21*y1*y4-71*y1*y5-66*y1*y6+72*y2^2-40*y2*y3-68*y2*y4-15*y2*y5-32*y2*y6+87*y3^2-60*y3*y4+7*y3*y5-61*y3*y6-50*y4^2-22*y4*y5+48*y4*y6+46*y5^2-49*y5*y6+18*y6^2-34*y1+17*y2+45*y3-82*y4-66*y5+16*y6-22, x6-y6, x5-y5];
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
