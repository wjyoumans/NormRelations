
# Algorithm 5 of [??] (using decisional PIP). Input an ideal A in OK, output
# an integral ideal B such that the class of A*B is in the minus part of the
# class group and B has norm bounded by exp(O~(m))
#
# B = poly(m), d = \tilde{O}(m)
function walk_to_minus_part(
    A::NfOrdIdl, 
    B::Int, 
    d::Int;
    cache::NormRelCache=NormRelCache(), # cache_Kp
    parisizemax=PARISIZEMAX)

  K = nf(A)
  OK = order(A)
  S = prime_ideals_up_to(OK, B)

  # TODO: if cache not provided it is probably more efficient to use no S-unit PIP
  # method.
  if isempty(cache)
    Kp, mKp = subfield(K, [gen(K) + inv(gen(K))])
    OKp = maximal_order(Kp)
    
    lp = sort!(collect(Set(minimum(P) for P in S)))
    SKp = prime_ideals_over(OKp, lp)
    cache = norm_relation_cache(SKp)
    cache.embedding = mKp
  else
    @assert codomain(embedding(cache)) == K
  end

  while true
    used = []
    C = one(OK)
    for i=1:d
      j = rand(1:length(S))
      if j in used
	continue
      else
	C *= S[j] 
	push!(used, j)
      end
    end
    if decisional_pip(norm(embedding(cache), A*C, order=order(cache)), cache=cache, 
		   parisizemax=parisizemax)
      return C
    end
  end
end
