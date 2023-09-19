using genFGLM

P, x = PolynomialRing(GF(1618453), "x" => (1:4, 1:4))
sys = minors(matrix(x), 3)
id = ed_variety(sys)
gb = gen_fglm(id, target_order = :degrevlex)
display(gb)
exit()
