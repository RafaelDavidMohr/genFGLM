module genFGLM

using Reexport
@reexport using Oscar
using Groebner, AbstractTrees, Printf

export critical_points, cyclic, gen_fglm, ed_variety, rand_seq, rand_poly_dense, rand_poly_sparse 

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
    q = sum([prod(a) for a in zip(K[1:k, 1], up_to_half_degd_mons)])
    p = sum([prod(a) for a in zip(K[k+1:2*k, 1], up_to_half_degd_mons)])
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

# assume that pow_series is given up to mon
function pow_series_coeff(pow_series::P,
                          p::P,
                          q::P,
                          mon::P) where {P <: POL}

    R = parent(mon)
    F = base_ring(mon)
    rhs = zero(F)

    for (c, v) in zip(coefficients(q), monomials(q))
        does_div, w = divides(mon, v)
        !does_div && continue
        rhs += c*coeff(pow_series, w)
    end

    return inv(coeff(q, one(R)))*(coeff(p, mon) - rhs)
end

function pow_series(p::P, q::P, ord::P, vrs_pos::Vector{Int}) where {P <: POL}
    R = parent(p)
    res = coeff(q, one(R))*one(R)
    curr_mon = next_drl(one(R), vrs_pos)

    while cmp(degrevlex(R), ord, curr_mon) >= 0
        next_cf = pow_series_coeff(res, p, q, curr_mon)
        res += next_cf*curr_mon
        curr_mon = next_drl(curr_mon, vrs_pos)
    end
    return res
end

function repr_in_vars(p::P, free_vars::Vector{P}) where {P <: POL}
    R = parent(p)
    free_vars_pos = [findfirst(v -> v == w, gens(R)) for w in free_vars]
    exps = collect(exponents(p))
    res = Tuple{P, P}[]
    
    for e in exps
        deleteat!(e, free_vars_pos)
    end
    unique!(exps)
    sort!(exps, by = e -> prod(free_vars .^ e), lt = (u1, u2) -> cmp(degrevlex(R), u1, u2) > 0)

    n_free_vars = setdiff(gens(R), free_vars)
    for e in exps
        cf = coeff(p, n_free_vars, e)
        push!(res, (cf, prod(n_free_vars .^ e)))
    end
    return res
end

function normalize_free_vars(p::P,
                             free_vars::Vector{P},
                             order::P) where {P <: POL}

    repr_p = repr_in_vars(p, free_vars)
    R = parent(p)
    free_vars_pos = [findfirst(v -> v == w, gens(R)) for w in free_vars]

    q = first(repr_p)[1]
    res = first(repr_p)[2]
    for (cf, m) in repr_p[2:end]
        cf_pow = pow_series(cf, q, order, free_vars_pos)
        res += (cf_pow*m)
    end

    return res
end
        

# main function
function gen_fglm(I::Ideal{P};
                  target_order = :lex,
                  compute_order = :elim,
                  ind_set = P[],
                  switch_to_generic = true,
                  double_deg_bound = 0) where {P <: POL}

    !isempty(ind_set) && !switch_to_generic && error("can't do that")
    
    # pre-computations to determine good projection
    if isempty(ind_set)
        println("determining maximally independent set")
        # gb_1 = gens(groebner_basis_f4(I, complete_reduction = true))
        gb_1 = groebner(gens(I), ordering = DegRevLex())
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
        # gb = gens(groebner_basis_f4(I_new, complete_reduction = true))
        gb = groebner(gens(I_new), ordering = DegRevLex())
    else
        I_new = I
        gb = gb_1
    end
    # ----
    
    ln_free_vars = length(n_free_vars)
    if target_order == :lex
        target_order_gr = Lex(gens(R))
        target_order_osc = lex(gens(R))
    else
        error("unsupported target order")
    end
    # target_order_gr = ProductOrdering(DegRevLex(n_free_vars[1:ln_free_vars-1]),
    #                                   DegRevLex([n_free_vars[ln_free_vars], free_vars...]))
    # target_order_osc = degrevlex(n_free_vars[1:ln_free_vars-1])*degrevlex([n_free_vars[ln_free_vars], free_vars...])
    gb_1 = groebner(vcat(gens(I_new), free_vars), ordering = target_order_gr)
    target_staircase = staircase(gb_1, target_order_osc) 

    to_lift = candPol{typeof(first(gb_1))}[]
    free_var_positions = [findfirst(v -> v == w, gens(R)) for w in free_vars]
    for (i, g) in enumerate(filter(g -> !(g in free_vars), gb_1))
        support = [deleteat!(e, free_var_positions) for e in exponents(g)]
        unique!(support)
        pades = [(zero(R), one(R)) for _ in 1:length(support)]
        push!(to_lift, candPol(g, copy(support), copy(pades)))
    end
        
    mons = free_vars
    next_deg_mons = mons_of_deg_d(free_vars, 2)

    Rloc = subVarLoc(R, free_vars)
    result = typeof(first(gens(Rloc.loc_ring)))[]

    println("starting lift...")
    println("------")

    d = 2
    lowb = 2
    curr_deg = 1
    full = [one(R)]

    drl_staircase = [one(R)]
    # used to flag all elements in slice which are also in staircase
    drl_staircase_flagmap = Dict{P, Bool}([(one(R), false)])
    montree = MonomialNode(true, 1, MonomialNode[])
    to_del = Int[]

    test_lift = true
    if compute_order == :elim
        compute_ordering_gr = ProductOrdering(DegRevLex(n_free_vars), DegRevLex(free_vars))
        compute_ordering_osc = degrevlex(n_free_vars)*degrevlex(free_vars)
    else
        compute_ordering_gr = DegRevLex(gens(R))
        compute_ordering_osc = degrevlex(gens(R))
    end
    
    while !isempty(to_lift)
        if test_lift
            println("doing a test lift")
            U = [first(mons)]
            append!(full, U)
            pt_id = point_ideal(1, mons, next_deg_mons)
        else
            println("lifting to degree $d")
            # lowb = d == 2 ? 2 : Int(d/2) + 2
            U = vcat(mons[2:end],
                     [mons_of_deg_d(free_vars, e) for e in lowb:d]...)
            append!(full, U)
            pt_id = mons_of_deg_d(free_vars, d+1)
        end
        println("computing GB...")
        # gb_u = gens(groebner_basis_f4(ideal(R, vcat(gb, pt_id)),
        #                               complete_reduction = true,
        #                               info_level = 0))
        gb_u = groebner(vcat(gb, pt_id), ordering = compute_ordering_gr)
        println("computing staircase...")
        leadmons = (p -> leading_monomial(p, ordering=compute_ordering_osc)).(gb_u)

        prev_length = length(drl_staircase)
        staircase!(leadmons, drl_staircase, montree, one(R))
        n_length = length(drl_staircase)
        for j in prev_length+1:n_length
            m = drl_staircase[j]
            drl_staircase_flagmap[m] = false 
        end

        println("computing lift normal forms...")
        # lift_nfs = Oscar.reduce([f.curr for f in to_lift], gb_u)
        lift_nfs = normalform(gb_u, [f.curr for f in to_lift],
                              ordering = compute_ordering_gr, check = false)
        # lift_nfs = Oscar.reduce([f.curr for f in to_lift], gb_u, ordering = compute_ordering_osc)
        if test_lift
            empty!(to_del)
            println("testing for stability (normal form)")
            for (j, nf_f) in enumerate(lift_nfs)
                f = to_lift[j]
                if iszero(nf_f)
                    push!(result, Rloc(f.curr))
                    push!(to_del, j)
                end
            end
            println("$(length(to_del))/$(length(to_lift)) stable elements (normal form)")
            deleteat!(to_lift, to_del)
            deleteat!(lift_nfs, to_del)
            isempty(to_lift) && break
        end

        slice = vcat([u .* target_staircase for u in U]...)
        println("computing slice normal forms...")
        # slice_nfs = Oscar.reduce(slice, gb_u, ordering = compute_ordering_osc)
        slice_nfs = normalform(gb_u, slice, ordering = compute_ordering_gr, check = false)
        empty!(to_del)
        for (i, (sl, sl_nf)) in enumerate(zip(slice, slice_nfs))
            if sl_nf == sl
                push!(to_del, i)
                drl_staircase_flagmap[sl] = true
            end
        end
        if length(to_del) != length(slice)
            println("non-trivial lift, dividing staircase...")
            triv_slice_part = slice[to_del]
            println("computing remaining slice coeff vectors ($(length(slice)-length(to_del))/$(length(slice)))...")
            deleteat!(slice_nfs, to_del)
            deleteat!(slice, to_del)
            staircase_rem = [k for k in keys(drl_staircase_flagmap) if !drl_staircase_flagmap[k]]
            for k in keys(drl_staircase_flagmap)
                drl_staircase_flagmap[k] = false
            end

            C1 = coeff_vectors(gb_u, triv_slice_part, slice_nfs, is_reduced = true)
            C2 = coeff_vectors(gb_u, staircase_rem, slice_nfs, is_reduced = true)
            println("computing lift coeff vectors...")
            D1 = coeff_vectors(gb_u, triv_slice_part, lift_nfs, is_reduced = true)
            D2 = coeff_vectors(gb_u, staircase_rem, lift_nfs, is_reduced = true)
            
            FF = base_ring(R)
            CC2 = matrix(FF, C2)
            DD2 = matrix(FF, D2)
            sz = 0
            nzsz = 0
            for x in CC2
                sz += 1
                if !iszero(x)
                    nzsz += 1
                end
            end
            dens = 100 * nzsz/sz
            sze = size(transpose(CC2))
            @printf "lifting %i elements, mat of size %i x %i, density %2.2f%%\n" length(to_lift) sze[1] sze[2] dens
            hassol, vs2 = can_solve_with_solution(transpose(CC2),transpose(DD2))
            !hassol && error("unliftable elements")
            if isempty(triv_slice_part)
                lifts = [sum(vs2[:, j] .* slice) for j in 1:length(to_lift)]
            else
                vs1 = transpose(matrix(D1)) - transpose(matrix(C1)) * vs2
                lifts = [sum(vs1[:, j] .* triv_slice_part) + sum(vs2[:, j] .* slice)
                         for j in 1:length(to_lift)]
            end
        else
            println("trivial lifting step")
            lifts = lift_nfs
        end

        if test_lift
            u = first(U)
            empty!(to_del)
            n_stable_elements = 0
            n_tried = 0
            println("testing stability (pade)")
            for (j, f) in enumerate(to_lift)
                if all(!iszero, [p[1] for p in f.pades])
                    n_tried += 1
                    pss = [coeff(f.curr, n_free_vars, m)
                           for m in f.support]
                    next_guessed_cfs = [extract_coefficient(cf, p[1], p[2], u,
                                                            free_vars)
                                        for (cf, p) in zip(pss, f.pades)]
                    next_cfs = [coeff(lifts[j], prod(n_free_vars .^ m)*u)
                                for m in f.support]

                    if next_guessed_cfs == -next_cfs
                        n_stable_elements += 1
                        p = f.pades
                        push!(result, sum([(Rloc(p[k][1])/Rloc(p[k][2]))*Rloc(prod(n_free_vars .^ m))
                                           for (k, m) in enumerate(f.support)]))
                        push!(to_del, j)
                        continue
                    else
                        f.pades = [(zero(R), one(R)) for _ in 1:length(f.support)]
                    end
                end
            end
            println("$(n_stable_elements)/$(n_tried) elements with stable pade approximation")
            deleteat!(to_lift, to_del)
            deleteat!(lifts, to_del)
            isempty(to_lift) && break
        end

        [f.curr = f.curr - l for (l, f) in zip(lifts, to_lift)]
        
        if !test_lift
            n_succ = 0
            println("starting pade approximations for $(length(to_lift)) elements")
            i = findlast(m -> total_degree(m) <= d/2, full)
            half = full[1:i]
            for f in to_lift
                pades = [pade(coeff(f.curr, n_free_vars, m),
                              full, half, pt_id)
                         for m in f.support]
                any(p -> all(iszero, p), pades) && continue
                n_succ += 1
                f.pades = pades
            end
            println("$(n_succ) elements with succesful pade approximation")
            mons = pt_id
            next_deg_mons = mons_of_deg_d(free_vars, d+2)
            lowb = d + 2
            if iszero(double_deg_bound) || d < double_deg_bound
                d *= 2
                println("doubling degree to $(d)")
            else
                d += 2
                println("increasing degree to $(d)")
            end
        end
        test_lift = !test_lift
        println("------")
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
                    currmon::P,
                    vrs=gens(parent(first(leadmons)))) where {P <: POL}

    nvr = length(vrs)
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
        mon = currmon * vrs[ch.varstart]
        staircase!(leadmons, stairc, ch, mon, vrs)
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
    stairc = [one(R)]
    montree = MonomialNode(true, 1, MonomialNode[])
    lms = [leading_monomial(p, ordering=ord) for p in gb]
    staircase!(lms, stairc, montree, one(R), vrs)
    return stairc
end

# compute coeffs of F in terms of staircase
function coeff_vectors(gb::Vector{P},
                       vec_basis::Vector{P},
                       F::Vector{P};
                       is_reduced = false) where {P <: POL}
    
    # TODO: maybe normalform does not work
    # nfs = normalform(gb, F, ordering = ordering)
    nfs = if !is_reduced
        # Oscar.reduce(F, gb)
        normalform(gb, F, ordering = DegRevLex(), check = false)
    else
        F
    end
    res = [[coeff(g,m) for m in vec_basis] for g in nfs]
    return res
end

# compute coeffs of F in terms of staircase
function coeff_vectors(gb::Vector{P},
                       vec_basis_hmap::Dict{P, Int},
                       vec_basis_length::Int,
                       F::Vector{P};
                       is_reduced = false) where {P <: POL}
    
    field = base_ring(parent(first(F)))
    res = [zeros(field, vec_basis_length) for _ in 1:length(F)]
    # TODO: maybe normalform does not work
    # nfs = normalform(gb, F, ordering = ordering)
    nfs = if !is_reduced
        # Oscar.reduce(F, gb)
        normalform(gb, F, ordering = DegRevLex(), check = false)
    else
        F
    end
    for i in 1:length(F)
        f = F[i]
        for t in terms(f)
            cf = coeff(t, 1)
            m = monomial(t, 1)
            res[i][vec_basis_hmap[m]] = cf
        end
    end

    return res
end

function next_drl(mon::POL,
                  vars_pos::Vector{Int}=collect(1:length(gens(parent(mon)))))

    R = parent(mon)
    vrs = gens(R)
    exps = first(exponents(mon))[vars_pos]
    first_nz = findfirst(!iszero, exps)

    if isnothing(first_nz)
        return vrs[last(vars_pos)]
    end

    d = total_degree(mon)
    if isone(first_nz) && exps[first_nz] == d
        return vrs[last(vars_pos)]^(d+1)
    end

    res_exps = copy(exps)
    if !isone(first_nz)
        res_exps[first_nz] -= 1
        res_exps[first_nz-1] += 1
        return prod(gens(R)[vars_pos] .^ res_exps)
    end

    second_nz = findfirst(!iszero, exps[2:end]) + 1
    res_exps[second_nz] -= 1
    res_exps[first_nz] = 0
    res_exps[second_nz-1] += exps[first_nz] + 1

    return prod(gens(R)[vars_pos] .^ res_exps)
end  

function nz_exps(mon::POL)
    R = parent(mon)
    vrs = gens(R)
    vrs_enum = (identity).(enumerate(vrs))
    nz_exps_inds = findall(((i, v), ) -> !iszero(exponent(mon, 1, i)), vrs_enum)
    return vrs[nz_exps_inds]
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

function rand_seq(nvars, deg, neqns; dense=true, nterms=10)
    R, vars = polynomial_ring(GF(65521), "x" => (1:nvars, ))
    sys = [dense ? rand_poly_dense(R, deg) : rand_poly_sparse(R, deg, nterms)
           for _ in 1:neqns]
    return ideal(R, sys)
end

end # module genFGLM
