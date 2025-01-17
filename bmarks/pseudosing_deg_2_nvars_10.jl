using Pkg; Pkg.activate("../")
using genFGLM
P, (x1, x2, x3, x4, x5, y1, y2, y3, y4, y5)  = polynomial_ring(GF(1522321), ["x1", "x2", "x3", "x4", "x5", "y1", "y2", "y3", "y4", "y5"]);
F = [72*x1^2-87*x1*x2+47*x1*x3-90*x1*x4+43*x1*x5-91*x2^2-88*x2*x3-48*x2*x4+53*x2*x5+5*x3^2+13*x3*x4-10*x3*x5+71*x4^2+16*x4*x5+9*x5^2+92*x1-28*x2-82*x3+83*x4-60*x5-83, 98*x1^2-48*x1*x2-19*x1*x3+62*x1*x4+37*x1*x5+96*x2^2-17*x2*x3+25*x2*x4+91*x2*x5+98*x3^2-64*x3*x4+64*x3*x5-60*x4^2-34*x4*x5+44*x5^2+5*x1-90*x3-13*x4-2*x5+71, -47*x1^2-39*x1*x2-53*x1*x3-72*x1*x4-97*x1*x5+10*x2^2+7*x2*x3-89*x2*x4+65*x2*x5-25*x3^2-96*x3*x4+50*x3*x5-42*x4^2+7*x4*x5-70*x5^2+33*x1+12*x2-60*x3-89*x4+34*x5-68, -60*x1^2+16*x1*x2+52*x1*x3-20*x1*x4-4*x1*x5-77*x2^2+69*x2*x3+80*x2*x4+28*x2*x5-33*x3^2+21*x3*x4-35*x3*x5+30*x4^2-64*x4*x5-16*x5^2-89*x1-42*x2+97*x3+89*x4+59*x5-69, 72*y1^2-87*y1*y2+47*y1*y3-90*y1*y4+43*y1*y5-91*y2^2-88*y2*y3-48*y2*y4+53*y2*y5+5*y3^2+13*y3*y4-10*y3*y5+71*y4^2+16*y4*y5+9*y5^2+92*y1-28*y2-82*y3+83*y4-60*y5-83, 98*y1^2-48*y1*y2-19*y1*y3+62*y1*y4+37*y1*y5+96*y2^2-17*y2*y3+25*y2*y4+91*y2*y5+98*y3^2-64*y3*y4+64*y3*y5-60*y4^2-34*y4*y5+44*y5^2+5*y1-90*y3-13*y4-2*y5+71, -47*y1^2-39*y1*y2-53*y1*y3-72*y1*y4-97*y1*y5+10*y2^2+7*y2*y3-89*y2*y4+65*y2*y5-25*y3^2-96*y3*y4+50*y3*y5-42*y4^2+7*y4*y5-70*y5^2+33*y1+12*y2-60*y3-89*y4+34*y5-68, -60*y1^2+16*y1*y2+52*y1*y3-20*y1*y4-4*y1*y5-77*y2^2+69*y2*y3+80*y2*y4+28*y2*y5-33*y3^2+21*y3*y4-35*y3*y5+30*y4^2-64*y4*y5-16*y5^2-89*y1-42*y2+97*y3+89*y4+59*y5-69, x5-y5, x4-y4];
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
