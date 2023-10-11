using genFGLM

P, (x,y,z) = PolynomialRing(GF(1618453), ["x", "y", "z"])
f = rand_poly_dense(P, 6)
id = ed_variety([f])
tim = @elapsed gen_fglm(id, target_order = :degrevlex)
println("time $(tim)")
exit()
