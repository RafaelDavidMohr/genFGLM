using Pkg; Pkg.activate("../")
using genFGLM

P, (x,y,z) = polynomial_ring(GF(1618453), ["x", "y", "z"])
f = rand_poly_dense(P, 3)
id = ed_variety([f])
vrs = gens(base_ring(id))
comp_id = ideal(base_ring(id), [vrs[1]*vrs[2], vrs[1]*vrs[3], vrs[2]*vrs[3]])
gen_fglm(comp_id, just_hypersurface=true)
@time gen_fglm(id, just_hypersurface=true);
