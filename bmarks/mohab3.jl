using Pkg; Pkg.activate("../")
using genFGLM
P, (a, b, c, d, e, f, x, y) = polynomial_ring(GF(1221239), ["a", "b", "c", "d", "e", "f", "x", "y"]);

F = [48*a*d^2+56*a*d*e+28*a*d*f+96*a*d*y+16*a*e^2+16*a*e*f+48*a*e*y+4*a*f^2+24*a*f*y+48*a*y^2+28*b*d^2+24*b*d*e+12*b*d*f+56*b*d*y+4*b*e^2+4*b*e*f+16*b*e*y+b*f^2+8*b*f*y+28*b*y^2+14*c*d^2+12*c*d*e+4*c*d*f+28*c*d*y+2*c*e^2+c*e*f+8*c*e*y+4*c*f*y+14*c*y^2+48*d^2*x+56*d*e*x+28*d*f*x+96*d*x*y+16*e^2*x+16*e*f*x+48*e*x*y+4*f^2*x+24*f*x*y+48*x*y^2, 28*a*d^2+24*a*d*e+12*a*d*f+56*a*d*y+4*a*e^2+4*a*e*f+16*a*e*y+a*f^2+8*a*f*y+28*a*y^2+16*b*d^2+8*b*d*e+4*b*d*f+32*b*d*y+16*b*y^2+8*c*d^2+4*c*d*e+c*d*f+16*c*d*y+8*c*y^2+24*d^2*x+16*d*e*x+8*d*f*x+48*d*x*y+8*e*x*y+4*f*x*y+24*x*y^2, 14*a*d^2+12*a*d*e+4*a*d*f+28*a*d*y+2*a*e^2+a*e*f+8*a*e*y+4*a*f*y+14*a*y^2+8*b*d^2+4*b*d*e+b*d*f+16*b*d*y+8*b*y^2+4*c*d^2+2*c*d*e+8*c*d*y+4*c*y^2+12*d^2*x+8*d*e*x+4*d*f*x+24*d*x*y+4*e*x*y+4*f*x*y+12*x*y^2, 48*a^2*d+28*a^2*e+14*a^2*f+48*a^2*y+56*a*b*d+24*a*b*e+12*a*b*f+56*a*b*y+28*a*c*d+12*a*c*e+4*a*c*f+28*a*c*y+96*a*d*x+56*a*e*x+28*a*f*x+96*a*x*y+16*b^2*d+4*b^2*e+2*b^2*f+16*b^2*y+16*b*c*d+4*b*c*e+b*c*f+16*b*c*y+48*b*d*x+16*b*e*x+8*b*f*x+48*b*x*y+4*c^2*d+c^2*e+4*c^2*y+24*c*d*x+8*c*e*x+4*c*f*x+24*c*x*y+48*d*x^2+28*e*x^2+14*f*x^2+48*x^2*y, 28*a^2*d+16*a^2*e+8*a^2*f+24*a^2*y+24*a*b*d+8*a*b*e+4*a*b*f+16*a*b*y+12*a*c*d+4*a*c*e+a*c*f+8*a*c*y+56*a*d*x+32*a*e*x+16*a*f*x+48*a*x*y+4*b^2*d+4*b*c*d+16*b*d*x+8*b*x*y+c^2*d+8*c*d*x+4*c*x*y+28*d*x^2+16*e*x^2+8*f*x^2+24*x^2*y, 14*a^2*d+8*a^2*e+4*a^2*f+12*a^2*y+12*a*b*d+4*a*b*e+2*a*b*f+8*a*b*y+4*a*c*d+a*c*e+4*a*c*y+28*a*d*x+16*a*e*x+8*a*f*x+24*a*x*y+2*b^2*d+b*c*d+8*b*d*x+4*b*x*y+4*c*d*x+4*c*x*y+14*d*x^2+8*e*x^2+4*f*x^2+12*x^2*y, 48*a*d^2+56*a*d*e+28*a*d*f+96*a*d*y+16*a*e^2+16*a*e*f+48*a*e*y+4*a*f^2+24*a*f*y+48*a*y^2+24*b*d^2+16*b*d*e+8*b*d*f+48*b*d*y+8*b*e*y+4*b*f*y+24*b*y^2+12*c*d^2+8*c*d*e+4*c*d*f+24*c*d*y+4*c*e*y+4*c*f*y+12*c*y^2+48*d^2*x+56*d*e*x+28*d*f*x+96*d*x*y+16*e^2*x+16*e*f*x+48*e*x*y+4*f^2*x+24*f*x*y+48*x*y^2, 48*a^2*d+24*a^2*e+12*a^2*f+48*a^2*y+56*a*b*d+16*a*b*e+8*a*b*f+56*a*b*y+28*a*c*d+8*a*c*e+4*a*c*f+28*a*c*y+96*a*d*x+48*a*e*x+24*a*f*x+96*a*x*y+16*b^2*d+16*b^2*y+16*b*c*d+16*b*c*y+48*b*d*x+8*b*e*x+4*b*f*x+48*b*x*y+4*c^2*d+4*c^2*y+24*c*d*x+4*c*e*x+4*c*f*x+24*c*x*y+48*d*x^2+24*e*x^2+12*f*x^2+48*x^2*y];
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
