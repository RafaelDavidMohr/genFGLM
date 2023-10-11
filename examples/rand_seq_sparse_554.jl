using genFGLM

id = rand_seq(5,5,4,dense=false)
gb = gen_fglm(id, target_order = :degrevlex)
display(gb)
exit()
