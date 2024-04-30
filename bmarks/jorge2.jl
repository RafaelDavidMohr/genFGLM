using Pkg; Pkg.activate("../")
using genFGLM
P, (x, y, z) = polynomial_ring(GF(2020853), ["x", "y", "z"])

F = [73960*x^3+46428*x^2*y-320426*x^2*z-88867*x*y^2-163934*x*y*z-184389*x*z^2-62940*y^3+356381*y^2*z+32282*y*z^2-27183*z^3-210018*x^2+721747*x*y+416981*x*z+146898*y^2+118097*y*z+116973*z^2-111106*x-377082*y-153504*z+56580, 3038*x^2*y-3686*x^2*z+2288*x*y^2-16544*x*y*z-3344*x*z^2+315*y^3+4111*y^2*z+157*y*z^2-663*z^3-27166*x*y+4168*x*z-2769*y^2+13942*y*z+1527*z^2+25806*y-690*z, 650*x^2*y+3350*x^2*z+195*x*y^2-8450*x*y*z+845*x*z^2-260*y^3-3410*y^2*z-390*y*z^2+13390*x*y-1630*x*z-276*y^2+8372*y*z-15088*y, -225*x^2*y+1685*x^2*z-705*x*y^2-450*x*y*z+345*x*z^2-420*y^3+1325*y^2*z+645*y*z^2+8056*x*y-705*x*z+918*y^2+1527*y*z-5658*y]

id = ideal(P,F);
vrs = gens(base_ring(id))
comp_id = ideal(base_ring(id), [vrs[1]*vrs[2], vrs[1]*vrs[3], vrs[2]*vrs[3]])
gen_fglm(comp_id, just_hypersurface=true)
@time gen_fglm(id, just_hypersurface=true);
exit()
