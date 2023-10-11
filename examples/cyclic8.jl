exit() # doesnt work at the moment
using genFGLM
P, vars = polynomial_ring(GF(65521), "x" => 1:8)
F = cyclic(vars)
id = ideal(P,F);
gb = gen_fglm(id, target_order=:degrevlex);
display(gb)
exit()
