using genFGLM
P, (c_1, c_2, c_3, c_4, c_5, c_6, x_1, x_2, x_3, x_4, x_5) = PolynomialRing(GF(1553329), ["c_1", "c_2", "c_3", "c_4", "c_5", "c_6", "x_1", "x_2", "x_3", "x_4", "x_5"]);
F = [x_3*(c_4^2*c_5*c_6-c_2*c_4*c_5-c_2*c_4*c_6+c_2^2), x_3*(c_3^2*c_5*c_6-c_1*c_3*c_5-c_1*c_3*c_6+c_1^2), x_3*(2*c_3*c_4*c_5*c_6-c_1*c_4*c_5-c_1*c_4*c_6-c_2*c_3*c_5-c_2*c_3*c_6+2*c_1*c_2), x_1*x_4*c_2*c_4, -x_1*(-c_1*c_4*x_1*x_4+c_2*c_3*x_1*x_4+c_1*c_3*x_4+2*c_1*c_4*x_2+2*c_2*c_3*x_2), -x_1*(c_3^2*c_5*c_6*x_2-c_1*c_3*c_5*x_2-c_1*c_3*c_6*x_2+c_1*c_4*x_1*x_3-c_2*c_3*x_1*x_3+c_1^2*x_2+c_1*c_3*x_3), -x_1*(c_3^2*c_5*c_6*x_4+4*c_3*c_4*c_5*c_6*x_2-c_1*c_3*c_5*x_4-c_1*c_3*c_6*x_4-2*c_1*c_4*c_5*x_2-2*c_1*c_4*c_6*x_2-c_1*c_4*x_1*x_5-2*c_2*c_3*c_5*x_2-2*c_2*c_3*c_6*x_2+c_2*c_3*x_1*x_5+c_1^2*x_4+4*c_1*c_2*x_2+c_1*c_3*x_5+2*c_1*c_4*x_2+2*c_1*c_4*x_3-2*c_2*c_3*x_2+2*c_2*c_3*x_3), -x_1*x_2*(c_1*c_4*x_1-c_2*c_3*x_1+c_1*c_3), -x_1*x_3*(c_3^2*c_5*c_6-c_1*c_3*c_5-c_1*c_3*c_6+c_1^2), -3*x_1*x_2*c_2*c_4, -3*c_4^2*c_5*c_6*x_1*x_3+3*c_2*c_4*c_5*x_1*x_3+3*c_2*c_4*c_6*x_1*x_3-2*c_3^2*c_5*c_6*x_4+2*c_1*c_3*c_5*x_4+2*c_1*c_3*c_6*x_4-3*c_2^2*x_1*x_3-2*c_1^2*x_4, c_4^2*c_5*c_6*x_1*x_4-c_2*c_4*c_5*x_1*x_4-c_2*c_4*c_6*x_1*x_4+c_2^2*x_1*x_4+c_2*c_4*x_1*x_5-c_1*c_4*x_4-c_2*c_3*x_4-2*c_2*c_4*x_2, -3*c_4^2*c_5*c_6*x_1*x_2+3*c_2*c_4*c_5*x_1*x_2+3*c_2*c_4*c_6*x_1*x_2+2*c_1*c_4*x_1*x_4-3*c_2^2*x_1*x_2-2*c_2*c_3*x_1*x_4-3*c_2*c_4*x_1*x_3-2*c_1*c_3*x_4-c_1*c_4*x_2-c_2*c_3*x_2, c_4^2*c_5*c_6*x_1*x_5-c_2*c_4*c_5*x_1*x_5-c_2*c_4*c_6*x_1*x_5-2*c_3*c_4*c_5*c_6*x_4-c_4^2*c_5*c_6*x_2+c_1*c_4*c_5*x_4+c_1*c_4*c_6*x_4+c_2^2*x_1*x_5+c_2*c_3*c_5*x_4+c_2*c_3*c_6*x_4+c_2*c_4*c_5*x_2+c_2*c_4*c_6*x_2-2*c_1*c_2*x_4-c_2^2*x_2, -c_3^2*c_5*c_6*x_1*x_5-4*c_3*c_4*c_5*c_6*x_1*x_3+c_1*c_3*c_5*x_1*x_5+c_1*c_3*c_6*x_1*x_5+2*c_1*c_4*c_5*x_1*x_3+2*c_1*c_4*c_6*x_1*x_3+2*c_2*c_3*c_5*x_1*x_3+2*c_2*c_3*c_6*x_1*x_3+c_3^2*c_5*c_6*x_2-c_1^2*x_1*x_5-4*c_1*c_2*x_1*x_3-c_1*c_3*c_5*x_2-c_1*c_3*c_6*x_2+c_1^2*x_2];

id = ideal(P,F);
gb = gen_fglm(id, target_order=:degrevlex);
display(gb)
exit()
