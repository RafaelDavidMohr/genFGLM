using genFGLM

P, (x,y,z,w) = PolynomialRing(GF(1618453), ["x", "y", "z","w"])
f = rand_poly_dense(P, 5)
id = ed_variety([f])
gb = gen_fglm(id, target_order = :degrevlex)
display(gb)
exit()
