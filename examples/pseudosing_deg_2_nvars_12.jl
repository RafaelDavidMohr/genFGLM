using Oscar
P, (x1, x2, x3, x4, x5, x6, y1, y2, y3, y4, y5, y6)  = PolynomialRing(GF(1840109), ["x1", "x2", "x3", "x4", "x5", "x6", "y1", "y2", "y3", "y4", "y5", "y6"]);
id = ideal(P,F);
gb = gen_fglm(id, target_order=:degrevlex);
display(gb)
exit()