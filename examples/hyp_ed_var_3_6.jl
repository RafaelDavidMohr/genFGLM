using genFGLM

P, (x,y,z) = PolynomialRing(GF(1618453), ["x", "y", "z"])
f = rand_poly_dense(P, 6)
id = ed_variety([f])
gb = gen_fglm(id, target_order = :degrevlex)
display(gb)
exit()
