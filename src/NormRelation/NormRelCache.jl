
# NormRelCache is used to cache recursive norm relation and S-unit group data
# when working with norm relations. Only access with accessor functions! These
# will do expensive computations only when necessary and cache the results so
# successive calls are cheap.
#
# Assumes all norm relations are abelian norm relations with only 2 layers of 
# recursion (top field, subfields indexed by i, subsubfields indexed by i, j)
mutable struct NormRelCache
  K::AbsSimpleNumField
  OK::AbsSimpleNumFieldOrder

  # set of primes of OK to decompose over
  S::Vector{AbsSimpleNumFieldOrderIdeal}

  # norm relation data for K
  N::NormRelation
  has_norm_relation::Int
  index::Int

  # embedding to top field if it exists
  embedding::NumFieldHom
  parent_cache::NormRelCache

  # S-unit group of K
  SU::FinGenAbGroup
  #mSU::MapSUnitGrpFacElem
  mSU::Map

  # subfield decomposition lifts
  lift::Function

  # caches for subfield in norm relation
  subfield_caches::Vector{NormRelCache}

  function NormRelCache()
    return new()
  end

  function NormRelCache(S::Vector{AbsSimpleNumFieldOrderIdeal})
    out = new()
    out.S = S
    out.OK = order(S[1])
    out.K = nf(out.OK)
    out.has_norm_relation = -1
    out.index = -1
    return out
  end

  function NormRelCache(S::Vector{AbsSimpleNumFieldOrderIdeal}, N::NormRelation)
    if index(N) == 0
      return NormRelCache(S)
    end
    out = new()
    out.S = S
    out.OK = order(S[1])
    out.K = nf(out.OK)
    out.N = N
    out.has_norm_relation = 1
    out.index = index(N)
    return out
  end
end

function Base.isempty(R::NormRelCache)
  if isdefined(R, :S)
    return false
  end
  return true
end

function norm_relation_cache(S::Vector{AbsSimpleNumFieldOrderIdeal})
  return NormRelCache(S)
end

function norm_relation_cache(S::Vector{AbsSimpleNumFieldOrderIdeal}, N::NormRelation)
  return NormRelCache(S, N)
end

function norm_relation_cache(R::NormRelCache, S::Vector{AbsSimpleNumFieldOrderIdeal})
  SU, mSU = sunit_group_fac_elem(R)
  out = NormRelCache(S)
  out.SU, out.mSU = sunit_group_subgroup(S, SU, mSU)
  return out
end

### "Private" accessor functions ###

function _subfield_caches(R::NormRelCache)
  if !isdefined(R, :subfield_caches)
    R.subfield_caches = []
    if has_norm_relation(R)
      N = norm_relation(R)
      p = sort!(collect(Set([minimum(P) for P in R.S])))
      for i = 1:length(N)
	L, mL = subfield(N, i)
	OL = lll(maximal_order(L))
	SL = prime_ideals_over(OL, p)
	b, NL = abelian_norm_relation(L)
	if b
	  cache = NormRelCache(SL, NL)
	  cache.embedding = mL
	  cache.parent_cache = R
	else
	  cache = NormRelCache(SL)
	  cache.embedding = mL
	  cache.parent_cache = R
	end
	push!(R.subfield_caches, cache)
      end
    end
  end
  return R.subfield_caches
end

function _subfield_caches(R::NormRelCache, i::Int)
  return _subfield_caches(_subfield_cache(R, i))
end

function _subfield_cache(R::NormRelCache, i::Int)
  @assert index(R) != 0
  caches = _subfield_caches(R)
  return caches[i]
end

function _subfield_cache(R::NormRelCache, i::Int, j::Int)
  @assert index(R) == 1
  caches = _subfield_caches(R, i)
  return caches[j]
end

function _parent_cache(R::NormRelCache)
  @assert isdefined(R, :parent_cache)
  return R.parent_cache
end

### "Public" accessor functions ###

function order(R::NormRelCache)
  return R.OK
end

function idealset(R::NormRelCache)
  return R.S
end

function index(R::NormRelCache)
  if R.index == -1
    if has_norm_relation(R)
      N = norm_relation(R)
      R.index = index(N)
    else
      R.index = 0
    end
  end
  return R.index
end

function index(R::NormRelCache, i::Int)
  return index(_subfield_cache(R, i))
end

function embedding(R::NormRelCache)
  #if !isdefined(R, :embedding)
  #  R.embedding = id
  #end
  return R.embedding
end

function embedding(R::NormRelCache, i::Int)
  return embedding(_subfield_cache(R, i))
end

function embedding(R::NormRelCache, i::Int, j::Int)
  return embedding(_subfield_cache(R, i, j))
end

function field(R::NormRelCache)
  return R.K
end

function subfield(R::NormRelCache, i::Int)
  return field(R), embedding(R)
end

function subfield(R::NormRelCache, i::Int, j::Int)
  return subfield(_subfield_cache(R, i), j)
end

function subfields(R::NormRelCache)
  caches = _subfield_caches(R)
  return [field(RR) for RR in caches]
end

function subfields(R::NormRelCache, i::Int)
  return subfields(_subfield_cache(R, i))
end

function sunit_group_fac_elem(R::NormRelCache)
  if !isdefined(R, :SU) || !isdefined(R, :mSU)
    @vprint :NormRelCache 1 "Cache miss (sunit_group_fac_elem)\n"
    if has_norm_relation(R)
      @vtime :NormRelCache 2 sunit_group_fac_elem(R.S, R.N, cache=R)
    else
      @vtime :NormRelCache 2 R.SU, R.mSU = sunit_group_fac_elem(R.S)
    end
  else
    @vprint :NormRelCache 1 "Cache hit (sunit_group_fac_elem)\n"
  end
  return R.SU, R.mSU
end

function sunit_group_fac_elem(R::NormRelCache, i::Int)
  return sunit_group_fac_elem(_subfield_cache(R, i))
end

function sunit_group_fac_elem(R::NormRelCache, i::Int, j::Int)
  return sunit_group_fac_elem(_subfield_cache(R, i, j))
end

function norm_relation(R::NormRelCache)
  if !isdefined(R, :has_norm_relation)
    @vprint :NormRelCache 1 "Cache miss (norm_relation)\n"
    @vtime :NormRelCache 2 b, R.N = abelian_norm_relation(R.K)
    if b
      R.has_norm_relation = 1
    else
      R.has_norm_relation = 0
    end
  else
    @vprint :NormRelCache 1 "Cache hit (norm_relation)\n"
  end
  return R.N
end

function norm_relation(R::NormRelCache, i::Int)
  return norm_relation(_subfield_cache(R, i))
end

function has_norm_relation(R::NormRelCache)
  if R.has_norm_relation == -1
    @vprint :NormRelCache 1 "Cache miss (has_norm_relation)\n"
    @vtime :NormRelCache 2 b, R.N = abelian_norm_relation(R.K)
    if b
      R.has_norm_relation = 1
    else
      R.has_norm_relation = 0
    end
  else
    @vprint :NormRelCache 1 "Cache hit (has_norm_relation)\n"
  end
  return Bool(R.has_norm_relation)
end

function has_norm_relation(R::NormRelCache, i::Int)
  return has_norm_relation(_subfield_cache(R, i))
end

function decomposition_lift(R::NormRelCache)
  if !isdefined(R, :lift)
    @vprint :NormRelCache 1 "Cache miss (decomposition_lift)\n"
    emb = embedding(R)
    parent_cache = _parent_cache(R)
    @vtime :NormRelCache 2 R.lift = decomposition_lift(idealset(parent_cache), idealset(R), emb)
  else
    @vprint :NormRelCache 1 "Cache hit (decomposition_lift)\n"
  end
  return R.lift
end

function decomposition_lift(R::NormRelCache, i::Int)
  return decomposition_lift(_subfield_cache(R, i))
end

function decomposition_lift(R::NormRelCache, i::Int, j::Int)
  return decomposition_lift(_subfield_cache(R, i, j))
end

#=
function decomposition_lifts(R::NormRelCache)
  if !isdefined(R, :lifts)
    if has_norm_relation(R)
      R.lifts = decomposition_lifts(R.S, R.N)
    else
      R.lifts = []
    end
  end
  return R.lifts
end

function decomposition_lifts(R::NormRelCache, i::Int)
  return decomposition_lifts(_subfield_cache(R, i))
end
=#
