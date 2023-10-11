using genFGLM

id = rand_seq(7,7,3,dense=false)
gb = gen_fglm(id, target_order = :degrevlex)
display(gb)
exit()
