

function norm_map(
    cache_K::NormRelCache, 
    cache_Kp::NormRelCache; 
    stable=STABLE, 
    parisizemax=PARISIZEMAX,
    strategy=:classic)
  

  SK = idealset(cache_K)
  SKp = idealset(cache_Kp)

  SUK, mSUK = sunit_group_fac_elem(cache_K)
  SUKp, mSUKp = sunit_group_fac_elem(cache_Kp)

  @vtime :MinusPart 2 AK = abelian_group(mSUK)
  @vtime :MinusPart 2 AKp = abelian_group(mSUKp)
  
  @assert ngens(AK) === length(SK)
  @assert ngens(AKp) === length(SKp)

  g = I -> norm(embedding(cache_Kp), I, order=order(cache_Kp))
  img = FinGenAbGroupElem[]
  for p in SK
    _, v = decompose(g(p), SKp, cache_Kp)
    push!(img,  AKp(v))
  end
  f = hom(AK, AKp, img)
  return f
end

function _class_group_minus_part_cache_setup(OK; parisizemax=PARISIZEMAX)
  K = nf(OK)

  @vprint :MinusPart 1 "Computing class group structure in gp.\n"
  @vtime :MinusPart 1 lp = get_primes_pari(K, parisizemax=parisizemax)
  @assert !isempty(lp)
  
  S = prime_ideals_over(OK, lp)
  @vprint :MinusPart 1 "Using prime ideals above: $(lp)\n"
  @vprint :MinusPart 1 "length(S) = $(length(S))\n"
  
  cache = norm_relation_cache(S)
  @vprint :MinusPart 1 "Precomputing S-unit group.\n"
  @vtime :MinusPart 1 sunit_group_fac_elem(cache)

  return cache
end

function _class_group_minus_part_setup(K::AbsSimpleNumField; parisizemax=PARISIZEMAX)
  
  b, m = Hecke.is_cyclotomic_type(K)
  @assert b
  
  OK = lll(maximal_order(K))
  
  @vprint :MinusPart 1 "Setting up the cache for K.\n"
  cache_K = _class_group_minus_part_cache_setup(OK, parisizemax=parisizemax)

  Kp, emb = Hecke.subfield(K, [gen(K) + inv(gen(K))])
  OKp = lll(maximal_order(Kp))

  @vprint :MinusPart 1 "Setting up the cache for Kp.\n"
  cache_Kp = _class_group_minus_part_cache_setup(OKp, parisizemax=parisizemax)
  cache_Kp.embedding = emb

  return cache_K, cache_Kp
end

function class_group_minus_part(
    K::AbsSimpleNumField; 
    parisizemax=PARISIZEMAX, 
    stable=STABLE, 
    strategy=:classic)
  
  cache_K, cache_Kp = _class_group_minus_part_setup(K, parisizemax=parisizemax)

  @vprint :MinusPart 1 "Computing relative norm map as a homomorphism of groups.\n"
  @vtime :MinusPart 1 nmap = norm_map(cache_K, cache_Kp, stable=stable, 
					  strategy=strategy, parisizemax=parisizemax)
  
  @vprint :MinusPart 1 "Computing kernel.\n"
  @vtime :MinusPart 1 ker, kermap = kernel(nmap)
  return ker, kermap, cache_K, cache_Kp
end


