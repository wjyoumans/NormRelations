
# Algorithms for working with the Stickelberger lattice, used
# to solve the close principal multiple problem. See [??].

# TODO: switch to rows instead of cols

function fractional_part(x)
  return x - floor(x)
end

# Return the stickelberger element theta(a) for conductor m. Stickelberger elements
# are elements of Q[G] and represented as column vectors.
function stickelberger_element(a, m; galgrp = unit_group(ResidueRing(ZZ, m)))
  @assert m > 2
  G, mG = galgrp
  n = Int(order(G))
  return [fractional_part(-a*lift(mG(-g))//m) for g in G]
end

# Elements alpha of the group ring Z[G] act on ideals of OK by
# A^alpha = prod(sigma_i(a)^alpha_i) for sigma_i in G, the galois group of
# the field.
function apply_stickelberger(A::AbsSimpleNumFieldOrderIdeal, alpha::ZZMatrix; galgrp=nothing)
  K = nf(A)
  b, m = Hecke.is_cyclotomic_type(K)
  @assert b
  
  if isnothing(galgrp)
    galgrp = unit_group(ResidueRing(ZZ, m))
  end
  
  G, mG = galgrp
  OK = order(A)
  n = degree(K)
  @assert length(alpha) == n

  D = Dict(ideal(OK, 1)=>1)
  for (i, g) in enumerate(G)
    if iszero(alpha[i, 1])
      continue
    end
    f = hom(K, K, gen(K)^lift(mG(g)); check = false)
    B = f(A)
    #B = auts[i](A)
    if !haskey(D, B)
      D[B] = alpha[i, 1]
    else
      D[B] += alpha[i, 1]
    end
  end
  return FacElem(D)
end

# Return the matrix whose columns are generators of the Stickelberger ideal.
function stickelberger_generators(m; galgrp=unit_group(ResidueRing(ZZ, m)))
  G, mG = galgrp
  V = Vector{ZZRingElem}[]
  t1 = stickelberger_element(1, m, galgrp=galgrp)
  for a = 2:m
    ta = stickelberger_element(a, m, galgrp=galgrp)
    push!(V, [ZZ(x) for x in a*t1 - ta])
  end
  return transpose(matrix(V))
end

# Return the matrix whose columns are short generators of the Stickelberger ideal
function short_stickelberger_generators(m; galgrp=unit_group(ResidueRing(ZZ, m)))
  G, mG = galgrp
  V = Vector{ZZRingElem}[]
  t1 = stickelberger_element(1, m, galgrp=galgrp)
  for a = 1:m
    ta = stickelberger_element(a, m, galgrp=galgrp)
    push!(V, [ZZ(x) for x in a*t1 - ta])
  end
  return transpose(matrix([V[i] - V[i-1] for i=2:m]))
end


# Input (G, mG) where G is the galois group of a cyclotomic field K of conductor m
# as an abelian group and mG the map from G to automorphisms of K.
# Return the quotient group H = G/<tau> where tau corresponds to complex conjugation,
# the map from G to H, and the element tau.
function galois_group_mod_complex_conjugation(m; galgrp=unit_group(ResidueRing(ZZ, m)))
  G, mG = galgrp
  X = [[lift(mG(g)), g] for g in G]
  i = findfirst(x->x[1]==(m-1), X)
  tau = X[i][2]
  H, mH = quo(G, [tau])
  return H, mH, tau
end

# Take x in Z[G] and project onto R = Z[G]/(1 + tau). mH is the map from G to 
# H = G/<tau> where G is the galois group of a cyclotomic field as an abelian group 
# and tau the element corresponding to complex conjugation.
# We take mH^-1(H) as a Z-basis of R.
function project(x, mH, tau; basis=[])
  G = domain(mH)
  H = codomain(mH)
  if isempty(basis)
    basis=[mH\h for h in H]
  end
  #transversal = [mH\h for h in H]
  
  res = ZZRingElem[0 for i in 1:length(H)]
  for (i, g) in enumerate(G)
    j = findfirst(isequal(g), basis)
    if j !== nothing
      res[j] += x[i]
    else
      j = findfirst(isequal(tau + g), basis)
      @assert j !== nothing
      res[j] -= x[i]
    end
  end
  return res
end

# Input mH the canonical map from G to H where G is the galois group of a 
# cyclotomic field as an abelian group and H = G/<tau> where tau corresponds to 
# complex conjugation.
# Output a projection map from G to G/<tau> (which induces a projection of Z[G]
# to Z[G]/(1 + tau))
function projection(mH, tau)
  G = domain(mH)
  H = codomain(mH)

  x = ZZRingElem[0 for i in 1:length(G)]
  M = zero_matrix(ZZ, length(H), length(G))
  basis = [mH\h for h in H]
  for i in 1:length(G)
    x[i] = 1
    xx = project(x, mH, tau; basis=basis)
    @assert !iszero(xx)
    x[i] = 0
    M[:, i] = xx
  end
  f = a -> M*a
  return f
end

# Given an element alpha of Z[G] find beta in Z[G] with 1-norm less or equal
# to (1/4)*phi(m)^(3/2) with C^beta = C^alpha for any class C in the minus part
# of the class group.
function reduce(alpha::ZZMatrix, m; galgrp=unit_group(ResidueRing(ZZ, m)), 
    W=short_stickelberger_generators(m, galgrp=galgrp))

  @vprint :Stickelberger 1 "Checking element size before reducing.\n"
  # if 1-norm of alpha is large it should be reduced
  if sum(abs(a) for a in alpha) < (1/4)*(euler_phi(m))^(3/2)
    @vprint :Stickelberger 1 "Element already reduced.\n"
    return alpha
    beta = reduce(alpha, m)
  end

  @vprint :Stickelberger 1 "Reducing element.\n"
  G, mG = galgrp
  H, mH, tau = galois_group_mod_complex_conjugation(m, galgrp=galgrp)
  proj = projection(mH, tau)
  
  W_proj = proj(W)
  a_proj = proj(alpha)
  _, v = close_vector(W_proj, a_proj)
  gamma = W_proj*v
  beta = invert_projection(a_proj - gamma, mH, m)
  @assert proj(beta) == a_proj - gamma
  return beta
end

# Find an inverse image of the projected element of R = Z[G]/(1 + tau)
function invert_projection(proj, mH, m; basis=[])
  G = domain(mH)
  H = codomain(mH)
  if isempty(basis)
    basis=[mH\h for h in H]
  end

  y = zero_matrix(ZZ, Int(order(G)), 1)
  gs = [g for g in G]
  for (i, t) in enumerate(basis)
    j = findfirst(isequal(t), gs)
    y[j,1] = proj[i,1]
  end
  return y
end

