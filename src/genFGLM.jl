module genFGLM

using Reexport
@reexport using Oscar
using Groebner, AbstractTrees, Printf

export critical_points, cyclic, gen_fglm, ed_variety 

const POL = MPolyElem

# type used for a canditate lifted element

mutable struct candPol{P <: POL}
    curr::P

    # support in terms of non-free variables
    support::Vector{Vector{Int}}
    pades::Vector{Tuple{P, P}}
end

function test_poly(f::candPol{P},
                   n_free_vars::Vector{P}) where {P <: POL}

    num_lcm = lcm([p[2] for p in f.pades])
    return sum([divides(f.pades[j][1] * num_lcm, f.pades[j][2])[2]*prod(n_free_vars .^ m)
                for (j, m) in enumerate(f.support)])
end

# type for ring with inverted variables

struct subVarLoc{C, P <: MPolyElem{C}, LOC <: MPolyLocRingElem, MMAP}
    R::MPolyRing{C}
    
    vars::Vector{P}
    rem_vars::Vector{P}

    transit_ring::MPolyRing{C}
    loc_map::MMAP
    loc_ring::MPolyRing{LOC}
end

function subVarLoc(R::MPolyRing{T},
                   vars::Vector{MP}) where {T, MP <: MPolyElem{T}}

    rem_vars = setdiff(gens(R), vars)
    S, _ = polynomial_ring(base_ring(R), ["z$i" for i in 1:length(vars)])

    U = complement_of_prime_ideal(ideal(S, zero(S)))
    Sloc, loc_map = localization(S, U)
    loc_ring, _ = polynomial_ring(Sloc, ["x$i" for i in 1:length(rem_vars)])

    return subVarLoc(R, vars, rem_vars, S, loc_map, loc_ring)
end

Base.show(io::IO, R::subVarLoc) = show(io, R.loc_ring)

(Rloc::subVarLoc{C, P})(f::P) where {C, P} = begin

    vars_pos = [findfirst(v -> v == w, gens(Rloc.R))
                for w in Rloc.vars]
    rem_vars_pos = [findfirst(v -> v == w, gens(Rloc.R))
                    for w in Rloc.rem_vars]
    
    exps = [[exponent(f, i, j) for j in vars_pos]
            for i in 1:length(f)]
    exps_rem = [[exponent(f, i, j) for j in rem_vars_pos]
                for i in 1:length(f)] 
    ctx = MPolyBuildCtx(Rloc.loc_ring)
    
    for i in 1:length(f)
        cf = Rloc.loc_map(prod(gens(Rloc.transit_ring) .^ exps[i]))
        push_term!(ctx, coeff(f, i)*cf, exps_rem[i])
    end
    finish(ctx)
end  

# compute a pade approximant for r of degree d
function pade(r::P,
              up_to_degd_mons::Vector{P},
              up_to_half_degd_mons::Vector{P},
              degd_pl_one_mons::Vector{P}) where {P <: POL}

    oldstd = stdout
    redirect_stdout(devnull)
    vs = coeff_vectors(degd_pl_one_mons,
                       up_to_degd_mons,
                       r .* up_to_half_degd_mons)
    redirect_stdout(oldstd)

    F = base_ring(parent(r))
    k = length(up_to_half_degd_mons)
    id_block = -identity_matrix(F, k)
    l = length(up_to_degd_mons)
    zero_block = zero_matrix(F, l - k, k)
    right_block = vcat(id_block, zero_block)
    m = hcat(transpose(matrix(F, vs)), right_block)
    K = can_solve_with_kernel(m, zero_matrix(F, l, 1))[3]
    # TODO: can there be no solution
    isempty(K) && return (zero(r), zero(r))
    q = sum(K[1:k, 1] .* up_to_half_degd_mons)
    p = sum(K[k+1:2*k, 1] .* up_to_half_degd_mons)
    g = gcd(p, q)
    return (divides(p,g)[2], divides(q,g)[2])
end

# out of the partial power series of num/denom extract the coefficient of mon
function extract_coefficient(pow_series::P,
                             num::P,
                             denom::P,
                             mon::P,
                             vars::Vector{P}) where {P <: POL}

    mon in monomials(num) && error("can't determine next coefficient")

    # the smart brute force method
    d = total_degree(mon)
    all_divisors = typeof(mon)[]
    for e in 1:(d-1)
        mons = mons_of_deg_d(vars, e)
        append!(all_divisors, filter(m -> divides(mon, m)[1], mons))
    end

    F = base_ring(mon)
    res = zero(F)
    for m in all_divisors
        n = divides(mon, m)[2]
        a = coeff(pow_series, n)
        q = coeff(denom, m) 
        res += a*q
    end
    return -(res * inv(coeff(denom, one(parent(mon)))))
end

# main function
function gen_fglm(I::Ideal{P};
                  target_order = Lex(),
                  ind_set = P[],
                  switch_to_generic = true) where {P <: POL}

    !isempty(ind_set) && !switch_to_generic && error("can't do that")
    
    # pre-computations to determine good projection
    if isempty(ind_set)
        println("determining maximally independent set")
        gb_1 = gens(groebner_basis_f4(I, complete_reduction = true))
    end
    (sort_terms!).(gb_1)

    lts = [leading_monomial(g) for g in gb_1]
    free_vars = isempty(ind_set) ? maximal_ind_set(lts) : ind_set
    isempty(free_vars) && error("ideal is zero dimensional, aborting.")
    R = base_ring(I)
    n_free_vars = setdiff(gens(R), free_vars)
    dim = length(free_vars)
    println("maximally independent set $(free_vars)")

    if switch_to_generic
        println("choosing random point in base space")
        R = base_ring(I)
        ev = Vector{typeof(first(gb_1))}(undef, nvars(R))
        j = 1
        for (i, v) in enumerate(gens(R))
            if v in free_vars
                ev[i] = v + rand(-1000:1000)
                j += 1
            else
                ev[i] = v
            end
        end
        I_new = ideal(R, [f(ev...) for f in gens(I)])
        println("Computing initial DRL GB...")
        gb = gens(groebner_basis_f4(I_new, complete_reduction = true, info_level = 2))
    else
        I_new = I
        gb = gb_1
    end
    # ----
    
    println("Computing initial target staircase...")
    if target_order == Lex()
        gb_1 = groebner(vcat(gens(I_new), free_vars), ordering = target_order)
        target_staircase = staircase(gb_1, lex(R)) 
    elseif target_order == DegRevLex()
        gb_1 = gens(groebner_basis_f4(I_new + ideal(R, free_vars), complete_reduction = true))
        target_staircase = staircase(gb_1, degrevlex(R))
    else
        error("target ordering not supported")
    end

    to_lift = Vector{candPol{typeof(first(gb_1))}}(undef,
                                                   length(gb_1) - length(free_vars))
    free_var_positions = [findfirst(v -> v == w, gens(R)) for w in free_vars]
    for (i, g) in enumerate(filter(g -> !(g in free_vars), gb_1))
        support = [deleteat!(e, free_var_positions) for e in exponents(g)]
        pades = [(zero(R), one(R)) for _ in 1:length(support)]
        to_lift[i] = candPol(g, support, pades)
    end
        
    mons = free_vars
    next_deg_mons = mons_of_deg_d(free_vars, 2)

    Rloc = subVarLoc(R, free_vars)
    result = typeof(first(gens(Rloc.loc_ring)))[]

    println("starting lift...")
    println("------")

    d = 2
    curr_deg = 1
    full = [one(R)]

    drl_staircase = [one(R)]
    montree = MonomialNode(true, 1, MonomialNode[])
    
    while !isempty(to_lift)
        while curr_deg <= d
            append!(full, mons)
            for i in 1:length(mons)
                println("current degree $(curr_deg)")
                u = mons[i]
                pt_id = point_ideal(i, mons, next_deg_mons)
                slice = u .* target_staircase

                println("computing DRL GB...")
                gb_u = gens(groebner_basis_f4(ideal(R, vcat(gb, pt_id)),
                                              complete_reduction = true))
                println("computing staircase...")
                leadmons = (leading_monomial).(gb_u)
                staircase!(leadmons, drl_staircase, montree, one(R))

                println("computing normal forms...")
                C = coeff_vectors(gb_u, drl_staircase, slice)
                D = coeff_vectors(gb_u, drl_staircase, [f.curr for f in to_lift])
                to_del = Int[]
                println("testing for stability (normal form)")
                for (j, dd) in enumerate(D)
                    f = to_lift[j]
                    if iszero(dd)
                        push!(result, Rloc(f.curr))
                        push!(to_del, j)
                    end
                end
                println("$(length(to_del))/$(length(to_lift)) stable elements (normal form)")
                deleteat!(to_lift, to_del)
                deleteat!(D, to_del)
                isempty(to_lift) && break

                sz = 0
                nzsz = 0
                for x in matrix(R,C)
                    sz += 1
                    if !iszero(x)
                        nzsz += 1
                    end
                end
                dens = nzsz/sz
                sze = size(transpose(matrix(R,C)))
                @printf "lifting %i elements, mat of size %i x %i, density %2.2f%%\n" length(to_lift) sze[1] sze[2] dens
                hassol, vs = can_solve_with_solution(transpose(matrix(R, C)),transpose(matrix(R, D)))
                !hassol && error("unliftable elements")

                empty!(to_del)
                n_stable_elements = 0
                n_tried = 0
                println("testing stability (pade)")
                for (j, f) in enumerate(to_lift)
                    if all(!iszero, [p[1] for p in f.pades])
                        n_tried += 1
                        pss = [coeff(f.curr, n_free_vars, m)
                               for m in f.support]
                        next_cfs = [extract_coefficient(cf, p[1], p[2], u,
                                                        free_vars)
                                    for (cf, p) in zip(pss, f.pades)]
                        # TODO: this is a really dumb idea
                        if all(cf -> -cf in next_cfs, vs[:, j]) 
                            n_stable_elements += 1
                            p = f.pades
                            push!(result, sum([(Rloc(p[k][1])/Rloc(p[k][2]))*Rloc(prod(n_free_vars .^ m))
                                               for (k, m) in enumerate(f.support)]))
                            push!(to_del, j)
                            continue
                        end
                    end
                    f.curr = f.curr - sum(vs[:, j] .* slice)
                    f.pades = [(zero(R), one(R)) for _ in 1:length(f.support)]
                end
                println("------")
                println("$(n_stable_elements)/$(n_tried) elements with stable pade approximation")
                deleteat!(to_lift, to_del)
                isempty(to_lift) && break
            end
            isempty(to_lift) && break
            curr_deg += 1
            mons = next_deg_mons
            next_deg_mons = unique(vcat([v .* mons for v in free_vars]...))
        end
        isempty(to_lift) && break

        println("starting pade approximations for $(length(to_lift)) elements")
        i = findfirst(m -> total_degree(m) > d/2, full)
        half = full[1:(i-1)]
        full_pl_one = mons
        for f in to_lift
            pades = [pade(coeff(f.curr, n_free_vars, m),
                          full, half, full_pl_one)
                     for m in f.support]
            any(p -> all(iszero, p), pades) && continue
            f.pades = pades
        end
        println("------")

        # double the degree to which we lift
        d *= 2
        println("doubling degree to $(d)")
    end
    return result
end


# helper functions

mutable struct MonomialNode
    inStair::Bool
    varstart::Int
    children::Vector{MonomialNode}
end

AbstractTrees.children(node::MonomialNode) = node.children
AbstractTrees.childtype(::Type{<:MonomialNode}) = MonomialNode
AbstractTrees.nodetype(::Type{<:MonomialNode}) = MonomialNode
AbstractTrees.NodeType(::Type{<:MonomialNode}) = AbstractTrees.HasNodeType()

function staircase!(leadmons::Vector{P},
                    stairc::Vector{P},
                    tree::MonomialNode,
                    currmon::P) where {P <: POL}

    R = parent(currmon)
    nvr = ngens(R)
    if !tree.inStair
        any(m -> divides(currmon, m)[1], leadmons) && return
        tree.inStair = true
        push!(stairc, currmon)
    end
    if isempty(children(tree))
        vs = tree.varstart
        tree.children = [MonomialNode(false, vs + i, MonomialNode[])
                         for i in 0:(nvr-vs)]
    end
    for ch in children(tree)
        mon = currmon * gens(R)[ch.varstart]
        staircase!(leadmons, stairc, ch, mon)
    end
    return
end

function mons_of_deg_d(vars::Vector{P},
                       d::Int) where {P <: POL}

    nvars = length(vars)
    id = ideal(vars)
    return gens(id^d)
end

function maximal_ind_set(lts::Vector{P}) where {P <: POL}

    R = parent(first(lts))
    vrs = gens(R)
    res = typeof(first(vrs))[]
    for v in vrs[end:-1:1]
        cand = vcat(res, v)
        good = true
        for lt in lts
            vs = vars(lt)
            if all(v -> v in cand, vs)
                good = false
                break
            end
        end
        if good
            res = cand
        end
    end
    return sort!(res, by = v -> findfirst(w -> w == v, gens(R)))
end

# compute m_u as in the paper
function point_ideal(i::Int,
                     mons::Vector{P},
                     next_deg_mons::Vector{P}) where {P <: POL}
    return vcat(mons[i+1:end], next_deg_mons)
end

# compute staircase given gb
function staircase(gb::Vector{P},
                   ord::MonomialOrdering,
                   vrs=gens(parent(first(gb)));
                   res=[one(parent(first(gb)))]) where {P <: POL}
    
    R = parent(first(gb))
    LI = ideal(R, [leading_monomial(g, ordering = ord) for g in gb])

    i = 1 
    while i <= length(res)
        nexts = vrs .* res[i]
        for n in nexts
            n in res && continue
            n in LI && continue
            push!(res, n)
        end
        i += 1
    end
    return sort(res, lt = (m1, m2) -> cmp(ord, m1, m2) in [-1,0] ? true : false)
end

# compute coeffs of F in terms of staircase
function coeff_vectors(gb::Vector{P},
                       vec_basis::Vector{P},
                       F::Vector{P};
                       ordering = DegRevLex()) where {P <: POL}
    
    # TODO: normalform randomly does not work
    # nfs = normalform(gb, F, ordering = ordering)
    nfs = Oscar.reduce(F, gb)
    for (f, nf) in zip(F, nfs)
        println("$f --> $(nf)")
    end
    return [[coeff(g,m) for m in vec_basis] for g in nfs]
end

function next_drl(mon::POL,
                  vars_pos::Vector{Int})

    exps = first(exponents(mon))[vars_pos]
    low = findfirst(!iszero, exps)
    high = findlast(!iszero, exps)
    if low == high
        res = zeros(Int, length(exps))
        res[end] = first(exps) + 1
    elseif isone(low)
        res = zeros(Int, length(exps))
        res[high] = exps[high] - 1
        res[high-1] = sum(exps) - res[high]
    else
        res = copy(exps)
        res[low] -= 1
        res[low-1] += 1
    end
    R = parent(mon)
    return prod(gens(R)[vars_pos] .^ res)
end  

# for benchmarking

function rand_poly_sparse(R::MPolyRing,
                          deg::Int,
                          nterms::Int)

    ctx = MPolyBuildCtx(R)

    for _ in 1:nterms
        fv_ind = rand(1:ngens(R))
        bnd = deg
        exp = Vector{Int}(undef, ngens(R))
        for i in 1:ngens(R)
            e = rand(0:bnd)
            bnd -= e
            exp[((i + fv_ind - 1) % ngens(R)) + 1] = e
        end
        cf = rand(base_ring(R))
        push_term!(ctx, cf, exp)
    end

    return finish(ctx)
end

function rand_poly_dense(R::MPolyRing,
                         deg::Int)

    mons = vcat([mons_of_deg_d(gens(R), e) for e in 0:deg]...)
    cfs = [rand(base_ring(R)) for _ in 1:length(mons)]
    return sum(cfs .* mons)
end

function critical_points(nvars, neqns, deqns, nproj)
    R, vars = polynomial_ring(GF(65521), "x" => (1:nvars, ))
    sys = [rand_poly_dense(R, deqns) for _ in 1:neqns]
    mat = jacobi_matrix(sys)
    mat2 = jacobi_matrix(gens(R)[1:nproj])
    mat = hcat(mat, mat2)
    return ideal(R, vcat(sys, minors(mat, neqns + nproj)))
end

function cyclic(vars)
    n = length(vars)
    pols = [sum(prod(vars[j%n+1] for j in k:k+i) for k in 1:n) for i in 0:n-2]
    push!(pols, prod(vars[i] for i in 1:n)-1)
    return pols
end

function ed_variety(F)
    S = parent(first(F))
    nv = ngens(S)
    c = nv - dim(ideal(S, F))
    R, x, u = polynomial_ring(base_ring(S), "x" => (1:nv, ), "u" => (1:nv, ))
    phi = hom(S, R, x)
    FF = (phi).(F)
    j = jacobi_matrix(FF)[1:nv, :]
    k = jacobi_matrix(sum((u - x) .^ 2))[1:nv, :]
    l = hcat(j, k)
    return ideal(R, [FF..., minors(l, c + 1)...])
end

end # module genFGLM
