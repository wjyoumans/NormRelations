
# Input the maximal order OK of a cyclotomic field and upper bound B. Return the 
# prime ideals of OK with norm less than B whose equivalence class belongs to the 
# kernel of the norm map from Cl(OK) to Cl(OK)^+, i.e. Cl(OK)^-.
#
# If the S-unit group of OK^+ has already been computed and cached and S is known
# to generate Cl(OK)^+ then the cache can be provided.
function minus_part_prime_ideals_up_to(
    OK::AbsSimpleNumFieldOrder,
    B::Int;
    cache::NormRelCache=NormRelCache(), # cache of K^+
    stable=STABLE, 
    parisizemax=PARISIZEMAX,
    strategy=:classic)

  local emb, ord

  if isempty(cache)
    K = nf(OK)
    Kp, emb = subfield(K, [gen(K) + inv(gen(K))])
    ord = lll(maximal_order(Kp))
  else
    @assert codomain(embedding(cache)) == nf(OK)
    emb = embedding(cache)
    ord = order(cache)
  end

  S = sort!(prime_ideals_up_to(OK, B), by=norm)
  S0 = AbsSimpleNumFieldOrderIdeal[]
  for P in S
    A = norm(emb, P, order=ord)
    if decisional_pip(A, cache=cache, parisizemax=parisizemax, stable=stable, 
  		      strategy=strategy)
      conj = remove_conjugates!(S, P)
      append!(S0, conj)
    else
      _ = remove_conjugates!(S, P)
      continue
    end
  end
  return S0
end

function minus_part_generating_set(
    K::AbsSimpleNumField,
    B::Int=10000;
    stable=STABLE, 
    parisizemax=PARISIZEMAX,
    strategy=:classic,
    minus_part=class_group_minus_part(K, parisizemax=parisizemax, stable=stable, 
				      strategy=strategy))

  OK = lll(maximal_order(K))
  return minus_part_generating_set(OK, B, stable=stable, parisizemax=parisizemax,
				  strategy=strategy, minus_part=minus_part)
end

function minus_part_generating_set(
    OK::AbsSimpleNumFieldOrder,
    B::Int=10000;
    stable=STABLE, 
    parisizemax=PARISIZEMAX,
    strategy=:classic,
    minus_part=class_group_minus_part(nf(OK), parisizemax=parisizemax, stable=stable, 
				      strategy=strategy))

  K = nf(OK)
  ker, kermap, cache_K, cache_Kp = minus_part

  emb = embedding(cache_Kp)
  OKp = order(cache_Kp)
  CK = codomain(kermap)
  Cm = domain(kermap)
  h_minus = order(Cm)

  S = sort!(prime_ideals_up_to(OK, B), by=norm)
  mins = Set([minimum(P) for P in S])

  S0 = AbsSimpleNumFieldOrderIdeal[]
  SinCK = elem_type(CK)[]
  ord = 0
  d = 0
  norms = []
  for i = 1:length(mins)
    conj = []
    for P in S
      A = norm(emb, P, order=OKp)
      if decisional_pip(A, cache=cache_Kp, parisizemax=parisizemax, stable=stable, 
  		      strategy=strategy)
	conj = remove_conjugates!(S, P)
	break
      else
	_ = remove_conjugates!(S, P)
	continue
      end
    end

    if isempty(conj)
      @error "conj is empty! B too small?"
    end
    append!(S0, conj)
    push!(norms, norm(conj[1]))
    
    @vtime :MinusPart 3 temp = _as_elements_of_class_group(conj, CK, cache_K, 
							   stable=stable, 
							   parisizemax=parisizemax, 
							   strategy=strategy)
    append!(SinCK, temp)
    new_ord = order(sub(CK, SinCK)[1])
   
    if new_ord <= ord
      continue
    end

    ord = new_ord
    d += 1
    if ord == h_minus
      break
    end
  end
  @assert ord == h_minus
  return S0, Int(maximum(norms)), d
end


# Random subset of d primes of S0 and their conjugates.
function rand_subset(S0::Vector{AbsSimpleNumFieldOrderIdeal}, d::Int)
  K = nf(S0[1])
  temp = copy(S0)
  S = AbsSimpleNumFieldOrderIdeal[]
  for i = 1:d
    P = Base.rand(temp)
    conj = remove_conjugates!(temp, P)
    append!(S, conj)
  end
  return S
end

function test_minus_part_generating_set(
    OK::AbsSimpleNumFieldOrder,
    B::Int,
    d::Int,
    iters::Int;
    stable=STABLE, 
    parisizemax=PARISIZEMAX,
    strategy=:classic,
    minus_part=class_group_minus_part(nf(OK), parisizemax=parisizemax, stable=stable, 
				      strategy=strategy))

  K = nf(OK)
  ker, kermap, cache_K, cache_Kp = minus_part

  CK = codomain(kermap)
  Cm = domain(kermap)
  h_minus = order(Cm)

  if h_minus == 1
    # trivial minus part so always will succeed
    return iters
  end

  success = 0
  S0 = prime_ideals_up_to(OK, B)
  for i = 1:iters
    S = rand_subset(S0, d)
    @vtime :MinusPart 3 SinCK = _as_elements_of_class_group(S, CK, cache_K, 
							   stable=stable, 
							   parisizemax=parisizemax, 
							   strategy=strategy)
    if order(sub(CK, SinCK)[1]) == h_minus
      success += 1
    end
  end
  return success
end

#=
# If B or d are too small this may not terminate
function minus_part_generating_set(OK, B, d; 
    ctx::MinusPartCtx=_class_group_minus_part(OK),
    S0 = minus_part_prime_ideals_up_to(OK, B, ctx=ctx))

  CK = codomain(ctx.kermap)
  Cm = domain(ctx.kermap)
  
  if order(Cm) == 1
    # the class group is trivial, so we will always succeed
    return rand_S(S0, d)
  end

  @vprint :MinusPart 2 "Searching for generating set. h^- = $(order(Cm))\n"
  iter = 0
  while true
    iter += 1
    @vprint :MinusPart 2 "Minus part generating set - iteration: $iter\n"
    S = rand_S(S0, d)
    @vprint :MinusPart 3 "Sampled set S' has length $(length(S))\n"
    @vtime :MinusPart 3 D = _as_elements_of_class_group(S, ctx)
    new_ord = order(sub(CK, D)[1])
    @vprint :MinusPart 1 "Found subgroup of order = $(new_ord)\n"
    if order(Cm) == new_ord
      return S
    end
  end
end
=#
