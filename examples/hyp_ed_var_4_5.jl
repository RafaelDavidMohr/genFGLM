using genFGLM

P, (x,y,z,w) = PolynomialRing(GF(1618453), ["x", "y", "z","w"])
f = rand_poly_dense(P, 5)
id = ed_variety([f])
vrs = gens(base_ring(id))
comp_id = ideal(base_ring(id), [vrs[1]*vrs[2], vrs[1]*vrs[3]])
gen_fglm(comp_id, target_order = :degrevlex)
tim = @elapsed gen_fglm(id, target_order = :degrevlex)
println("time $(tim)")
exit()
