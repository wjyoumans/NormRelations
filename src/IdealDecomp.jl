
import Hecke: decompose

export decomposition_lift, issmooth, power_product, relation_matrix

# Compute the element giving the i-th relation among primes in S
function relation(f::MapSUnitGrpFacElem, i)
  return f(gens(domain(f))[i])
end

# Compute all relations.
function relations(f::MapSUnitGrpFacElem)
  D = domain(f)
  return [f(u) for u in gens(D)]
end

# Return the matrix of relations among primes in S
function relation_matrix(f::MapSUnitGrpFacElem)
  ideals = f.idl
  n = length(ideals)
  
  K = nf(ideals[1])
  r1, r2 = signature(K)
  @assert length(f.valuations) == n + r1 + r2

  M = sparse_matrix(ZZ)
  for r in f.valuations[r1+r2+1:end]
    push!(M, r)
  end
  @assert nrows(M) == ncols(M) == n
  return matrix(M)
end

function sunit_power_product(f::MapSUnitGrpFacElem, B)
  @assert length(f.idl) == length(B)

  K = nf(f.idl[1])
  r1, r2 = signature(K)
  a = one(codomain(f))
  for i = 1:length(B)
    b = B[i]
    if !iszero(b)
      r = relation(f, i+r1+r2)
      if b < 0
	a *= inv(r^abs(b))
      elseif b > 0
	a *= r^b
      end
    end
  end
  return a
end

# variant using class group preimage/discrete log
# It takes an ideal I, and gives the exponents of I with respect to S
function decompose_preimage(I::NfOrdIdl, S::Vector{NfOrdIdl})
  O = order(S[1])
  C, mC = class_group(O)
  Sinc = [mC\p for p in S]
  Zn = free_abelian_group(length(S))
  f = hom(Zn, c, Sinc)
  v = preimage(f, mc\I).coeff
  #return A([v[i] for i in 1:length(v)])
  return v
end

# basic ideal decomposition
# TODO: use decomposition field to reduce dimension when possible
function _decompose(A::NfOrdIdl, S::Vector{NfOrdIdl})
  OK = order(A)
  n = length(S)
    
  # fast check 1
  @vprint :Decompose 4 "Doing easiest decomposition.\n"
  B, b = Hecke.reduce_ideal(A)
  bool, X = issmooth(B, S)
  if bool
    return inv(b), X
  end

  # fast check 2
  @vprint :Decompose 4 "Doing next easiest decomposition.\n"
  for i = 1:n
    B = A*S[i]
    B, b = Hecke.reduce_ideal(B)
    bool, X = issmooth(B, S)
    if bool
      X[1,i] -= 1
      return inv(b), X
    end

    B = A*inv(S[i])
    B, b = Hecke.reduce_ideal(B)
    bool, X = issmooth(B, S)
    if bool
      X[1,i] += 1
      return inv(b), X
    end
  end

  nnz = 2
  attempts = 1
  exp_bound = 1
  @vprint :Decompose 4 "Doing hard decomposition.\n"
  while true
    if attempts % 2*n == 0
      nnz += 1
    elseif attempts % n^2 == 0
      exp_bound += 1
      nnz = 2
    end

    C = one(parent(A))
    Y = zeros(ZZ, n)
    used = []
    for j = 1:nnz
      k = rand(1:n)
      if k in used
	continue
      else
	push!(used, k)
      end

      Y[k] = rand(-exp_bound:exp_bound)
      if Y[k] < 0
	C *= inv(S[k]^abs(Y[k]))
      elseif Y[k] > 0
	C *= S[k]^Y[k]
      end
    end

    B, b = Hecke.reduce_ideal(A*C)
    bool, X = issmooth(B, S)
    if bool
      return inv(b), X - matrix(ZZ, 1, n, Y)
    end
    attempts += 1
  end

  #=
  @show logd = Int(Base.ceil(log(abs(discriminant(K)))))
  iters = 1
  while true
    Y = [rand(0:logd) for i = 1:n]
    B = A*prod([S[i]^Y[i] for i = 1:n])
    B, b = Hecke.reduce_ideal(B)
    bool, X = issmooth(B, S)
    if bool
      return inv(b), X - matrix(ZZ, 1, n, Y)
    end
    iters += 1
  end
  =#
end

function decompose(
    A::NfOrdIdl,
    cache::NormRelCache;
    stable=STABLE, 
    parisizemax=PARISIZEMAX,
    strategy=:classic)

  return decompose(A, idealset(cache), cache, stable=stable, 
		   parisizemax=parisizemax, strategy=strategy)
end

# return a, V such that A = a*B where B is the power product of ideals in S
# with exponents in V. If saturation is done (norm relation with nontrivial
# denominator is used) then A != a*B but A is equivalent to B. This is because
# we skip the root computation that would give a.
function decompose(
    A::NfOrdIdl,
    S::Vector{NfOrdIdl},
    cache::NormRelCache = NormRelCache(S);
    stable=STABLE, 
    parisizemax=PARISIZEMAX,
    strategy=:classic)

  if degree(field(cache)) < 4 || !has_norm_relation(cache)
    @vprint :Decompose 1 "Doing basic ideal decomposition.\n"
    return _decompose(A, S)
  end
  
  OK = order(A)
  @assert OK == order(cache)
  @assert OK == order(S[1])
  
  if S != cache.S
    # TODO: create new cache for the subset?
    #if issubset(S, cache.S)
    #  @info "Creating new cache using S-unit group subgroup."
    #  new_cache = norm_relation_cache(cache, S)
    #else
      @warn "Creating new cache with new S-unit group."
      new_cache = norm_relation_cache(S)
    #end
    return decompose(A, S, new_cache, stable=stable, parisizemax=parisizemax,
		    strategy=strategy)
  end
  @assert S == cache.S

  K = nf(OK)
  m = length(S)
  
  # quick check and reduce input ideal
  @vprint :Decompose 1 "Doing initial ideal reduction and smoothness test.\n"
  @vtime :Decompose 2 A, b = Hecke.reduce_ideal(A)
  @vtime :Decompose 2 bool, X = issmooth(A, S)
  if bool
    return inv(b), X
  end
  
  @vprint :Decompose 1 "Getting S-unit group.\n"
  @vtime :Decompose 2 SU, mSU = sunit_group_fac_elem(cache)
  relmat = relation_matrix(mSU)
  @assert nrows(relmat) == m
  n = ncols(relmat)
  
  a = FacElem(K(1))
  Y = zero_matrix(ZZ, 1, m)
  
  N = norm_relation(cache)
  d = index(N)
  
  subfield_caches = _subfield_caches(cache)
  for i = 1:length(subfield_caches)
    subfield_cache = subfield_caches[i]
    L = field(subfield_cache)
    mL = embedding(subfield_cache)
    OL = order(subfield_cache)
    SL = idealset(subfield_cache)
    f = decomposition_lift(subfield_cache)

    AL = norm(mL, A, order=OL)
    @vprint :Decompose 1 "Recursing to $L with norm relation of index $(index(subfield_cache)) (0 => none)\n"
    @vtime :Decompose 3 aL, YL = decompose(AL, SL, subfield_cache, stable=stable, 
      strategy=strategy, parisizemax=parisizemax)
    
    c = N.coefficients_gen[i][1][1]
    Y += c*f(YL) 
    a *= FacElem(mL(aL))^c
  end

  # no root (dividing of exponents) needed
  if d == 1
    return FacElem(K(1)), Y
  end

  # equivalent to trivial ideal class so input ideal principal
  if iszero(Y)
    return a, Y
  end
  
  R = ResidueRing(ZZ, d)
  Mmod = matrix(R, m, n, collect(relmat))
  Ymod = matrix(R, 1, n, collect(Y))

  X0, rk, X = matsolvemod(transpose(Mmod), d, transpose(Ymod), parisizemax=parisizemax)
  X = lift(transpose(X))
  X0 = lift(transpose(X0))

  if rk == 0
    @vprint :Decompose 3 "System x.M = y has trivial kernel.\n"
    V = Y - X0*relmat
    Z = matrix(ZZ, 1, m, [divexact(v, d) for v in V])
  else
    @vprint :Decompose 3 "System x.M = y has kernel rank $rk.\n"

    ap = a*sunit_power_product(mSU, X0)
    deltas = FacElem[sunit_power_product(mSU, X[j,:]) for j = 1:rk]
  
    r1, r2 = signature(K)
    units = [mSU(u) for u in gens(SU)[1:r1+r2]]
    append!(units, deltas)

    @vprint :Decompose 3 "Saturating at $d, stable = $stable.\n"
    @vtime :Decompose 3 sat = saturate_with_fixed_element(units, ap, d, stable=stable)
    @assert sat[1,end] == 1

    ai = sat[1,r1+r2+1:end-1]
    @assert length(ai) == rk
    for i = 1:rk
      X0 += ai[i]*X[i,:]
    end

    V = Y - X0*relmat
    Z = matrix(ZZ, 1, m, [divexact(v, d) for v in V])
  end

  # we skip the root computation so just return 1 with the decomposition.
  return FacElem(K(1)), Z
end

# Given field extension L/K, S1 prime ideals of L and S2 prime ideals of K that 
# factor over S1, return a map sending decompositions over S2 to decompositions 
# over S1.
function decomposition_lift(S1::Vector{NfOrdIdl}, S2::Vector{NfOrdIdl}, mL::NfToNfMor)
  #=
  SL = Set{NfOrdIdl}()
  for P in S
    p = minimum(mL, P)

    if p in SL
      continue
    end

    push!(SL, p)
  end
  SL = collect(SL)
  =#
  
  m = length(S1)
  OK = order(S1[1])
  M = zero_matrix(ZZ, 0, m)
  for P in S2
    PP = ideal(OK, [OK(g) for g in gens(mL(P))])
    b, v = issmooth(PP, S1)
    @assert b
    M = vcat(M, v)
  end

  f = x -> x*M
  return f
end
