using genFGLM

id = rand_seq(5,5,4,dense=false)
tim = @elapsed gen_fglm(id, target_order = :degrevlex)
println("time $(tim)")
exit()
