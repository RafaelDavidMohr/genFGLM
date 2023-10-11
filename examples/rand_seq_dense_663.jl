using genFGLM

id = rand_seq(6,6,3,dense=false)
tim = @elapsed gen_fglm(id, target_order = :degrevlex)
println("time $(tim)")
exit()
