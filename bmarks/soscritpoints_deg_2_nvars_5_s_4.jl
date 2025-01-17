using Pkg; Pkg.activate("../")
using genFGLM
P, (x1, x2, x3, x4, x5)  = polynomial_ring(GF(1354337), ["x1", "x2", "x3", "x4", "x5"]);
F = [9065*x1^2*x2^2+6202*x1^2*x2*x3-1848*x1^2*x2*x5+4934*x1^2*x3^2+2772*x1^2*x3*x5+1089*x1^2*x5^2+17654*x1*x2^2*x4+364*x1*x2^2*x5+1176*x1*x2*x3^2+13644*x1*x2*x3*x4+188*x1*x2*x3*x5-1960*x1*x2*x4*x5+4126*x1*x3^3-1386*x1*x3^2*x5+7156*x1*x3*x4*x5+2310*x1*x4*x5^2+14738*x2^2*x4^2+388*x2^2*x4*x5+4*x2^2*x5^2+13870*x2*x3^2*x4+9928*x2*x4^2*x5+9466*x3^4+x3^2*x4^2+11450*x3^2*x4*x5-20*x3*x4^2*x5+5949*x4^2*x5^2-9100*x1*x2^2-12086*x1*x2*x3+4480*x1*x2*x5-5640*x1*x3^2-2864*x1*x3*x4-6720*x1*x3*x5-1740*x1*x4*x5-5280*x1*x5^2-1378*x2^2*x4-200*x2^2*x5+10830*x2*x3^2-11708*x2*x3*x4-240*x2*x3*x5-7154*x2*x4^2+8432*x2*x4*x5-9230*x3^2*x4+3360*x3^2*x5+154*x3*x4^2-800*x3*x4*x5-8204*x4^2*x5-5600*x4*x5^2+7569*x1^2-5916*x1*x2+6960*x1*x3+13398*x1*x4+6905*x2^2+3280*x2*x3-10822*x2*x4+5200*x3^2+6160*x3*x4+8330*x4^2+6400*x5^2, 18130*x1^2*x2+6202*x1^2*x3-1848*x1^2*x5+35308*x1*x2*x4+728*x1*x2*x5+1176*x1*x3^2+13644*x1*x3*x4+188*x1*x3*x5-1960*x1*x4*x5+29476*x2*x4^2+776*x2*x4*x5+8*x2*x5^2+13870*x3^2*x4+9928*x4^2*x5-18200*x1*x2-12086*x1*x3+4480*x1*x5-2756*x2*x4-400*x2*x5+10830*x3^2-11708*x3*x4-240*x3*x5-7154*x4^2+8432*x4*x5-5916*x1+13810*x2+3280*x3-10822*x4, 6202*x1^2*x2+9868*x1^2*x3+2772*x1^2*x5+2352*x1*x2*x3+13644*x1*x2*x4+188*x1*x2*x5+12378*x1*x3^2-2772*x1*x3*x5+7156*x1*x4*x5+27740*x2*x3*x4+37864*x3^3+2*x3*x4^2+22900*x3*x4*x5-20*x4^2*x5-12086*x1*x2-11280*x1*x3-2864*x1*x4-6720*x1*x5+21660*x2*x3-11708*x2*x4-240*x2*x5-18460*x3*x4+6720*x3*x5+154*x4^2-800*x4*x5+6960*x1+3280*x2+10400*x3+6160*x4, 17654*x1*x2^2+13644*x1*x2*x3-1960*x1*x2*x5+7156*x1*x3*x5+2310*x1*x5^2+29476*x2^2*x4+388*x2^2*x5+13870*x2*x3^2+19856*x2*x4*x5+2*x3^2*x4+11450*x3^2*x5-40*x3*x4*x5+11898*x4*x5^2-2864*x1*x3-1740*x1*x5-1378*x2^2-11708*x2*x3-14308*x2*x4+8432*x2*x5-9230*x3^2+308*x3*x4-800*x3*x5-16408*x4*x5-5600*x5^2+13398*x1-10822*x2+6160*x3+16660*x4, -1848*x1^2*x2+2772*x1^2*x3+2178*x1^2*x5+364*x1*x2^2+188*x1*x2*x3-1960*x1*x2*x4-1386*x1*x3^2+7156*x1*x3*x4+4620*x1*x4*x5+388*x2^2*x4+8*x2^2*x5+9928*x2*x4^2+11450*x3^2*x4-20*x3*x4^2+11898*x4^2*x5+4480*x1*x2-6720*x1*x3-1740*x1*x4-10560*x1*x5-200*x2^2-240*x2*x3+8432*x2*x4+3360*x3^2-800*x3*x4-8204*x4^2-11200*x4*x5+12800*x5];
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
