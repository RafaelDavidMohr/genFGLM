using genFGLM
P, (x1, x2, x3, x4, x5, x6)  = PolynomialRing(GF(1066367), ["x1", "x2", "x3", "x4", "x5", "x6"]);
F = [36*x1^2*x3^2+289*x1^2*x5^2-578*x1*x2^2*x5-1054*x1*x2*x3*x5-624*x1*x3^2*x6+480*x1*x3*x4^2-540*x1*x3*x6^2+1768*x1*x4^2*x5-1496*x1*x5^3+3770*x2^4+1054*x2^3*x3+6372*x2^3*x4+3986*x2^2*x3^2-1870*x2^2*x3*x5+1148*x2^2*x4^2+11001*x2^2*x5^2+2596*x2^2*x6^2+9130*x2*x3^2*x5-3224*x2*x3*x4^2-5998*x2*x3*x4*x5-3080*x2*x3*x4*x6-94*x2*x3*x5^2+14592*x2*x4^2*x5+20450*x2*x4*x5^2+952*x2*x4*x5*x6+2376*x2*x4*x6^2+36*x3^2*x4^2+6889*x3^2*x5^2+2704*x3^2*x6^2+912*x3*x4^3+1140*x3*x4^2*x5-4160*x3*x4^2*x6-10790*x3*x4*x5^2-4648*x3*x4*x5*x6+4680*x3*x6^3+10080*x4^4+14440*x4^3*x5+8674*x4^2*x5^2+3640*x4^2*x5*x6-2816*x4^2*x6^2+1936*x5^4+2509*x6^4-636*x1^2*x3+5512*x1*x3*x6-4240*x1*x4^2+1054*x1*x5*x6+4770*x1*x6^2-8140*x2^2*x3+6136*x2^2*x4-1850*x2^2*x5-1054*x2^2*x6-28412*x2*x3*x5-1922*x2*x3*x6+5616*x2*x4^2+5624*x2*x4*x5+4144*x2*x4*x6-15936*x2*x5^2-1008*x3^2*x4-12768*x3*x4^2-16956*x3*x4*x5-12616*x4^2*x5+3224*x4^2*x6-15770*x4*x5^2+2288*x4*x6^2-2728*x5^2*x6-1628*x5*x6^2+2809*x1^2+996*x1*x3+1818*x2^2-3348*x2*x4+7056*x3^2+13944*x3*x5-8632*x3*x6+9344*x4^2-3848*x4*x5+8258*x5^2-7873*x6^2-8798*x1-3224*x4+2294*x5+7850, -1156*x1*x2*x5-1054*x1*x3*x5+15080*x2^3+3162*x2^2*x3+19116*x2^2*x4+7972*x2*x3^2-3740*x2*x3*x5+2296*x2*x4^2+22002*x2*x5^2+5192*x2*x6^2+9130*x3^2*x5-3224*x3*x4^2-5998*x3*x4*x5-3080*x3*x4*x6-94*x3*x5^2+14592*x4^2*x5+20450*x4*x5^2+952*x4*x5*x6+2376*x4*x6^2-16280*x2*x3+12272*x2*x4-3700*x2*x5-2108*x2*x6-28412*x3*x5-1922*x3*x6+5616*x4^2+5624*x4*x5+4144*x4*x6-15936*x5^2+3636*x2-3348*x4, 72*x1^2*x3-1054*x1*x2*x5-1248*x1*x3*x6+480*x1*x4^2-540*x1*x6^2+1054*x2^3+7972*x2^2*x3-1870*x2^2*x5+18260*x2*x3*x5-3224*x2*x4^2-5998*x2*x4*x5-3080*x2*x4*x6-94*x2*x5^2+72*x3*x4^2+13778*x3*x5^2+5408*x3*x6^2+912*x4^3+1140*x4^2*x5-4160*x4^2*x6-10790*x4*x5^2-4648*x4*x5*x6+4680*x6^3-636*x1^2+5512*x1*x6-8140*x2^2-28412*x2*x5-1922*x2*x6-2016*x3*x4-12768*x4^2-16956*x4*x5+996*x1+14112*x3+13944*x5-8632*x6, 960*x1*x3*x4+3536*x1*x4*x5+6372*x2^3+2296*x2^2*x4-6448*x2*x3*x4-5998*x2*x3*x5-3080*x2*x3*x6+29184*x2*x4*x5+20450*x2*x5^2+952*x2*x5*x6+2376*x2*x6^2+72*x3^2*x4+2736*x3*x4^2+2280*x3*x4*x5-8320*x3*x4*x6-10790*x3*x5^2-4648*x3*x5*x6+40320*x4^3+43320*x4^2*x5+17348*x4*x5^2+7280*x4*x5*x6-5632*x4*x6^2-8480*x1*x4+6136*x2^2+11232*x2*x4+5624*x2*x5+4144*x2*x6-1008*x3^2-25536*x3*x4-16956*x3*x5-25232*x4*x5+6448*x4*x6-15770*x5^2+2288*x6^2-3348*x2+18688*x4-3848*x5-3224, 578*x1^2*x5-578*x1*x2^2-1054*x1*x2*x3+1768*x1*x4^2-4488*x1*x5^2-1870*x2^2*x3+22002*x2^2*x5+9130*x2*x3^2-5998*x2*x3*x4-188*x2*x3*x5+14592*x2*x4^2+40900*x2*x4*x5+952*x2*x4*x6+13778*x3^2*x5+1140*x3*x4^2-21580*x3*x4*x5-4648*x3*x4*x6+14440*x4^3+17348*x4^2*x5+3640*x4^2*x6+7744*x5^3+1054*x1*x6-1850*x2^2-28412*x2*x3+5624*x2*x4-31872*x2*x5-16956*x3*x4-12616*x4^2-31540*x4*x5-5456*x5*x6-1628*x6^2+13944*x3-3848*x4+16516*x5+2294, -624*x1*x3^2-1080*x1*x3*x6+5192*x2^2*x6-3080*x2*x3*x4+952*x2*x4*x5+4752*x2*x4*x6+5408*x3^2*x6-4160*x3*x4^2-4648*x3*x4*x5+14040*x3*x6^2+3640*x4^2*x5-5632*x4^2*x6+10036*x6^3+5512*x1*x3+1054*x1*x5+9540*x1*x6-1054*x2^2-1922*x2*x3+4144*x2*x4+3224*x4^2+4576*x4*x6-2728*x5^2-3256*x5*x6-8632*x3-15746*x6];
id = ideal(P,F);
vrs = gens(base_ring(id))
comp_id = ideal(base_ring(id), [vrs[1]*vrs[2], vrs[1]*vrs[3]])
gen_fglm(comp_id, target_order = :degrevlex)
tim = @elapsed gen_fglm(id, target_order = :degrevlex)
println("time $(tim)")
exit()
