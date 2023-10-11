using genFGLM

id = rand_seq(6,6,3,dense=false)
gb = gen_fglm(id, target_order = :degrevlex)
display(gb)
exit()
