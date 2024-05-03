using Pkg; Pkg.activate("../")
using genFGLM
P, (x, y, z) = polynomial_ring(GF(1173157), ["x", "y", "z"])

F = [29250*x^3*y^2-113050*x^3*y*z-217800*x^3*z^2+85800*x^2*y^3-195265*x^2*y^2*z+501390*x^2*y*z^2-119995*x^2*z^3+81120*x*y^4-252285*x*y^3*z+392990*x*y^2*z^2+168915*x*y*z^3-16930*x*z^4+24960*y^5-134740*y^4*z-46540*y^3*z^2+68560*y^2*z^3+6300*y*z^4-516080*x^2*y^2-797290*x^2*y*z+203790*x^2*z^2-511894*x*y^3+524534*x*y^2*z-1072472*x*y*z^2+54320*x*z^3-79224*y^4+644008*y^3*z-151216*y^2*z^2-148588*y*z^3-290756*x*y^2+1353444*x*y*z-40920*x*z^2+53280*y^3-545568*y^2*z+497312*y*z^2+1054848*y^2-450672*y*z, 245440*x^3*y^2-218440*x^3*y*z+118920*x^3*z^2+388362*x^2*y^3-1589246*x^2*y^2*z+4270*x^2*y*z^2-15002*x^2*z^3+182858*x*y^4-767384*x*y^3*z-1087960*x*y^2*z^2+126912*x*y*z^3-17690*x*z^4+23400*y^5+317110*y^4*z+162978*y^3*z^2-62854*y^2*z^3+2790*y*z^4-1248*z^5-2531692*x^2*y^2+2413552*x^2*y*z-275676*x^2*z^2-2290656*x*y^3+2964612*x*y^2*z+875096*x*y*z^2+35908*x*z^3-263724*y^4-62496*y^3*z+692408*y^2*z^2-92240*y*z^3+23940*z^4+5231128*x*y^2-4239208*x*y*z+167904*x*z^2+2063160*y^3-820456*y^2*z-668000*y*z^2-14304*z^3-3013536*y^2+1952976*y*z-57168*z^2, 51750*x^3*y^2-249090*x^3*y*z+299460*x^3*z^2+87810*x^2*y^3-622808*x^2*y^2*z+1256768*x^2*y*z^2+278606*x^2*z^3+46578*x*y^4-283939*x*y^3*z-122385*x*y^2*z^2+394487*x*y*z^3+100795*x*z^4+7560*y^5+62439*y^4*z-69311*y^3*z^2-105573*y^2*z^3+1951*y*z^4+12774*z^5-782298*x^2*y^2+3033480*x^2*y*z-513192*x^2*z^2-773088*x*y^3+3006255*x*y^2*z-862598*x*y*z^2-253931*x*z^3-154854*y^4-106929*y^3*z+3408*y^2*z^2-264695*y*z^3-37758*z^4+3363228*x*y^2-4510470*x*y*z+236202*x*z^2+1113174*y^3-1899918*y^2*z-148908*y*z^2+45444*z^3-2934252*y^2+1551420*y*z-42048*z^2, 6624800*x^4*y+4456800*x^4*z+9428380*x^3*y^2-32123880*x^3*y*z+13889140*x^3*z^2-4303208*x^2*y^3-45476486*x^2*y^2*z-32385320*x^2*y*z^2+3087198*x^2*z^3-11420032*x*y^4+17830726*x*y^3*z-31601150*x*y^2*z^2-2195978*x*y*z^3-294190*x*z^4-4268160*y^5+25096600*y^4*z+17577878*y^3*z^2-3261404*y^2*z^3-77010*y*z^4-51168*z^5-17855680*x^3*y-7898280*x^3*z+46018856*x^2*y^2+130710864*x^2*y*z-14697912*x^2*z^2+68337620*x*y^3+121570128*x*y^2*z+60966800*x*y*z^2+1627348*x*z^3+16075920*y^4-50526584*y^3*z+12307644*y^2*z^2+295640*y*z^3+1083876*z^4-116812448*x^2*y+16999032*x^2*z-168966056*x*y^2-256357336*x*y*z+3887048*x*z^2-329064*y^3-38129632*y^2*z-30943256*y*z^2-2549544*z^3+286261696*x*y-11929968*x*z+53058480*y^2+133675520*y*z-1170960*z^2-144710976*y+4687776*z, 1035000*x^4*y-2566800*x^4*z+1092450*x^3*y^2-9976750*x^3*y*z+26275730*x^3*z^2-1571280*x^2*y^3-3648703*x^2*y^2*z+14898478*x^2*y*z^2+19447161*x^2*z^3-2491872*x*y^4+10455011*x*y^3*z-24472395*x*y^2*z^2+6015037*x*y*z^3+5255985*x*z^4-852480*y^5+6642444*y^4*z-4430001*y^3*z^2-9241278*y^2*z^3-20959*y*z^4+523734*z^5-1206210*x^3*y+11993940*x^3*z+17592132*x^2*y^2+5834381*x^2*y*z-39250039*x^2*z^2+25674570*x*y^3-4269971*x*y^2*z-18022208*x*y*z^2-19874311*x*z^3+8663112*y^4-45928152*y^3*z+2752721*y^2*z^2-2587003*y*z^3-2595546*z^4-60994644*x^2*y+9592434*x^2*z-124995966*x*y^2-44707334*x*y*z+25116044*x*z^2-16041132*y^3+9178620*y^2*z+2996442*y*z^2+4959360*z^3+141802404*x*y-12782724*x*z+55929780*y^2+33633948*y*z-5450376*z^2-58222296*y+3447936*z, 3036000*x^4*y-7529280*x^4*z+4754460*x^3*y^2-21886456*x^3*y*z-6125988*x^3*z^2+1083858*x^2*y^3+2882442*x^2*y^2*z-16238698*x^2*y*z^2-11096786*x^2*z^3-1238286*x*y^4+11225644*x*y^3*z+1209768*x*y^2*z^2+11358052*x*y*z^3-4233002*x*z^4-493560*y^5-1136814*y^4*z-1771102*y^3*z^2+448850*y^2*z^3+2065542*y*z^4-408084*z^5-55501776*x^3*y+24113616*x^3*z-55614846*x^2*y^2+94986016*x^2*y*z-8598546*x^2*z^2+6469710*x*y^3+1278090*x*y^2*z+83999142*x*y*z^2+5724082*x*z^3+12653748*y^4-34027290*y^3*z-6002820*y^2*z^2-3495746*y*z^3+2306412*z^4+305848404*x^2*y-34761444*x^2*z+138271764*x*y^2-78335080*x*y*z+16483548*x*z^2-71935092*y^3-256656*y^2*z-52845548*y*z^2+2134032*z^3-498731712*x*y+19626192*x*z-38576448*y^2+18346248*y*z-6573024*z^2+236207952*y-7312032*z];

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
