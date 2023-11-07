using genFGLM
P, (u, v, w) = PolynomialRing(GF(1224053), ["u", "v", "w"]);

F = [-64*u^3*v^4*w^4+160*u^4*v^3*w^3+96*u^2*v^5*w^3+96*u^2*v^3*w^5-288*u^3*v^4*w^2-288*u^3*v^2*w^4-144*u*v^4*w^4+552*u^2*v^3*w^3+108*u^3*v^4-24*u^3*v^2*w^2+108*u^3*w^4-12*u*v^4*w^2-12*u*v^2*w^4-216*u^2*v^3*w-216*u^2*v*w^3-72*v^3*w^3+168*u*v^2*w^2+72*u^2*v*w+24*v^3*w+24*v*w^3-36*u*v^2-36*u*w^2-8*v*w+8*u, -64*u^4*v^3*w^4+96*u^5*v^2*w^3+160*u^3*v^4*w^3+96*u^3*v^2*w^5-288*u^4*v^3*w^2-144*u^4*v*w^4-288*u^2*v^3*w^4+552*u^3*v^2*w^3+108*u^4*v^3-12*u^4*v*w^2-24*u^2*v^3*w^2-12*u^2*v*w^4+108*v^3*w^4-216*u^3*v^2*w-72*u^3*w^3-216*u*v^2*w^3+168*u^2*v*w^2+24*u^3*w+72*u*v^2*w+24*u*w^3-36*u^2*v-36*v*w^2-8*u*w+8*v, -64*u^4*v^4*w^3+96*u^5*v^3*w^2+96*u^3*v^5*w^2+160*u^3*v^3*w^4-144*u^4*v^4*w-288*u^4*v^2*w^3-288*u^2*v^4*w^3+552*u^3*v^3*w^2-12*u^4*v^2*w+108*u^4*w^3-12*u^2*v^4*w-24*u^2*v^2*w^3+108*v^4*w^3-72*u^3*v^3-216*u^3*v*w^2-216*u*v^3*w^2+168*u^2*v^2*w+24*u^3*v+24*u*v^3+72*u*v*w^2-36*u^2*w-36*v^2*w-8*u*v+8*w];
id = ideal(P,F);
vrs = gens(base_ring(id))
comp_id = ideal(base_ring(id), [vrs[1]*vrs[2], vrs[1]*vrs[3], vrs[2]*vrs[3]])
gen_fglm(comp_id, target_order = :degrevlex)
tim = @elapsed gen_fglm(id, target_order = :degrevlex)
println("time $(tim)")
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
        isok = true
        break
    end
    k += 1
end
println("MIS is last variables: $(isok)")
tim2 = @elapsed groebner_basis_f4(id, eliminate = k - 2, info_level = 2)
println("time elim $(tim2)")
exit()
