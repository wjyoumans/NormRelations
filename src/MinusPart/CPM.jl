
# Assuming Y is a permutation of X, return the function f such that f(X) = Y
function permutation(X::Vector, Y::Vector)
  @assert length(X) == length(Y)
  P = sortperm(X, by=x->findfirst(y->y==x, Y))
  f = Z -> [Z[P[i]] for i=1:length(Z)]
  return f
end

# Algorithm 4 of CDW21. Input a prime ideal P whose ideal class is an element of the
# minus part of the class group and an element alpha of the group ring Z[G]. 
# Returns an integral ideal B such that P^alpha * B is principal and 
# N(B) = N(P)^(O(phi(m)^(3/2))).
function close_principal_multiple(P::NfOrdIdl, alpha::fmpz_mat; galgrp=nothing)
  K = nf(P)
  n = degree(K)
  b, m = Hecke.is_cyclotomic_type(K)
  @assert b
  
  if isnothing(galgrp)
    galgrp = unit_group(ResidueRing(ZZ, m))
  end
  
  G, mG = galgrp
  H, mH, tau = galois_group_mod_complex_conjugation(m, galgrp=galgrp)

  beta = reduce(alpha, m)

  b_plus = zeros(ZZ, n)
  b_minus = zeros(ZZ, n)
  for i = 1:n
    b_sigma = beta[i]
    if b_sigma >= 0
      b_plus[i] = b_sigma
    else
      b_minus[i] = -b_sigma
    end
  end

  # acting by tau induces a permutation on the coefficients which we capture in f
  X = [lift(mG(g)) for g in G]
  Y = [lift(mG(tau + g)) for g in G]
  f = permutation(X, Y)

  # gamma = tau*b_plus + b_minus
  # permute b_plus according to f to mimic acting by tau
  gamma = matrix(f(b_plus) + b_minus)

  return apply_stickelberger(P, gamma, galgrp=galgrp)
end

# S any set of prime ideals generating the minus part of the class group
function close_principal_multiple(
    A::NfOrdIdl;
    parisizemax=PARISIZEMAX,
    stable=STABLE,
    strategy=:classic,
    minus_part=class_group_minus_part(nf(A), parisizemax=parisizemax, stable=stable, 
				      strategy=strategy))

    S, B, d = minus_part_generating_set(order(A), minus_part=minus_part, 
					parisizemax=parisizemax, stable=stable,
					strategy=strategy)
    return close_principal_multiple(A, S, B, d, minus_part=minus_part, 
				    parisizemax=parisizemax, stable=stable, 
				    strategy=strategy)
end

# S any set of prime ideals generating the minus part of the class group
function close_principal_multiple(
    A::NfOrdIdl,
    S::Vector{NfOrdIdl},
    B::Int,
    d::Int;
    parisizemax=PARISIZEMAX,
    stable=STABLE,
    strategy=:classic,
    minus_part=class_group_minus_part(nf(A), parisizemax=parisizemax, stable=stable, 
				      strategy=strategy))
 

  ker, kermap, cache_K, cache_Kp = minus_part

  K = nf(A)
  OK = order(A)
  @assert order(cache_K) == OK
  b, m = Hecke.is_cyclotomic_type(K)
  @assert b
  @assert !isempty(cache_Kp)

  @vtime :MinusPart 1 C = walk_to_minus_part(A, B, d, cache=cache_Kp)
  @vtime :MinusPart 1 _, v = decompose(A*C, S, cache_K, parisizemax=parisizemax, 
				       stable=stable, strategy=strategy)

  @hassert :MinusPart 10 decisional_pip(A*C//power_product(S, v), cache_K, parisizemax=parisizemax)
  
  if iszero(v)
    return FacElem(Dict(C => 1))
  end

  primes = []
  mins = []
  for P in S
    p = minimum(P)
    if p in mins
      continue
    else
      push!(primes, P)
      push!(mins, p)
    end
  end
  #@assert length(primes) == d

  # ensure ordering of automorphisms is correct
  G, mG = unit_group(ResidueRing(ZZ, m))
  auts = [hom(K, K, gen(K)^lift(mG(g))) for g in G]
  cpms = []

  for i=1:length(primes)
  #for i = 1:d
    alpha = zero_matrix(ZZ, degree(K), 1)
    P = primes[i]

    # this accounts for when P does not totally split. we don't repeat the
    # coefficients, only use it once
    used = []
    for (j, aut) in enumerate(auts)
      k = findfirst(isequal(aut(P)), S)
      if k in used
	continue
      else
	alpha[j,1] = v[k] 
	push!(used, k)
      end
    end
    @vtime :MinusPart 1 cpm = close_principal_multiple(P, alpha, galgrp=(G, mG))
    
    # check CPM succeeded for P, alpha
    @hassert :MinusPart 10 decisional_pip(apply_stickelberger(P, alpha)*cpm, cache_K, parisizemax=parisizemax)

    push!(cpms, cpm)
  end
  return C*prod(cpms)
end
