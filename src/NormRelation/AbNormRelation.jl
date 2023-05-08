# Norm relations for abelian fields. Use abelian_norm_relation to construct.
# 
# TODO: we convert from AbNormRelation to Hecke.NormRel.NormRelation for 
# compatability with Hecke. Either use Hecke.NormRel.NormRelation from the start 
# or stick to AbNormRelation


mutable struct AbNormRelation{T}
  base::T                             # underlying field or group
  den::Int                            # denominator/index of norm relation
  subs::Vector{Tuple{T, Map}}         # subfields/subgroups of the relation
  coeffs::Vector{Int}                 # coefficients of the norm relation
  brauer_coeffs::Vector{Vector{Int}}  # brauer coefficients of the norm relation
  nonred::Vector{Int}                 # nonredundant subgroups/subfields (not a subfield of
                                      # another field in the relation etc.)

  prime_decompositions::Dict{fmpz, Vector{Tuple{NfOrdIdl, Int}}}
  function AbNormRelation(A::T) where T <: Union{AnticNumberField, GrpAbFinGen}
    N = new{T}()
    N.base = A
    N.den = 1
    N.subs = [(A, id_hom(A))]
    N.coeffs = [1]
    N.brauer_coeffs = [[1]]
    N.nonred = [1]
    N.prime_decompositions = Dict{fmpz, Vector{Tuple{NfOrdIdl, Int}}}()
    return N
  end
end


field(N::AbNormRelation{AnticNumberField}) = N.base
group(N::AbNormRelation{GrpAbFinGen}) = N.base
index(N::AbNormRelation) = N.den
Base.denominator(N::AbNormRelation) = N.den
Base.size(N::AbNormRelation) = size(N.subs)
Base.length(N::AbNormRelation) = length(N.subs)
Base.IndexStyle(::Type{<:AbNormRelation}) = IndexLinear()
Base.getindex(N::AbNormRelation, i::Int) = N.subs[i]
Base.setindex!(N::AbNormRelation{GrpAbFinGen}, S::Tuple{GrpAbFinGen,GrpAbFinGenMap}, i::Int) = 
  (N.subs[i] = S)
Base.setindex!(N::AbNormRelation{AnticNumberField}, S::Tuple{AnticNumberField,NfToNfMor}, i::Int) = 
  (N.subs[i] = S)
coefficient(N::AbNormRelation, i::Int) = N.coeffs[i]
coefficients(N::AbNormRelation) = N.coeffs
embedding(N::AbNormRelation, i::Int) = N.subs[i][2]
embeddings(N::AbNormRelation) = [N.subs[i][2] for i in 1:length(N)]
subfield(N::AbNormRelation{AnticNumberField}, i::Int) = N.subs[i]
subfields(N::AbNormRelation{AnticNumberField}) = N.subs
subgroup(N::AbNormRelation{GrpAbFinGen}, i::Int) = N.subs[i]
subgroups(N::AbNormRelation{GrpAbFinGen}) = N.subs
norm(N::AbNormRelation{AnticNumberField}, i::Int, a) = norm(N.subs[i][2], a)
isredundant(N::AbNormRelation, i::Int) = !Bool(N.nonred[i])
istrivial(N::AbNormRelation) = (length(N) <= 1)


function Base.show(io::IO, N::AbNormRelation{AnticNumberField})
  print(io, "Norm relation on $(N.base) with denominator $(N.den)")
  if index(N) > 0
    print(io, " and subfields")
    for i in 1:length(N)
      print(io, "\n  ", coefficient(N, i), " * ", subfield(N, i)[1])
    end
  end
end

function Base.show(io::IO, N::AbNormRelation{GrpAbFinGen})
  print(io, "Norm relation on $(N.base) with denominator $(N.den)")
  if index(N) > 0
    print(io, " and subgroups")
    for i in 1:length(N)
      print(io, "\n  ", coefficient(N, i), " * ", subgroup(N, i)[1])
    end
  end
end

# given a norm relation N on subgroups of H for H < G, lift
# N to a relation on subgroups of G. f is the injection H -> G.
function lift!(N::AbNormRelation{GrpAbFinGen}, f::GrpAbFinGenMap)
  subs = []
  for i in 1:length(N)
    H, mH = subgroup(N, i)
    push!(subs,  (H, mH * f))
  end
  N.base = codomain(f)
  N.subs = subs
  return N
end

# combine array of norm relations using bezout identity. doesn't require
# coprime denominators, but probably should.
function bezout(A::Array{AbNormRelation{T},1}) where T <: Union{AnticNumberField,GrpAbFinGen}
  # @assert all have den > 0
  # @assert all have same top field/group, A.A
  D = [index(N) for N in A]
  d, U = bezout(D)

  brauer_zero = zeros(Int, sum([length(N) for N in A]))

  subs = []
  coeffs = []
  brauer_coeffs = []
  nonred = []
  for i in 1:length(A)

    temp = copy(brauer_zero)
    for j in 1:length(A[i])
      temp[j + length(coeffs)] = A[i].brauer_coeffs[1][j]
    end
    push!(brauer_coeffs, temp)
    #brauer_coeffs = vcat(brauer_coeffs, temp)

    subs = vcat(subs, A[i].subs)
    coeffs = vcat(coeffs, [U[i]*r for r in coefficients(A[i])])
    nonred = vcat(nonred, A[i].nonred)
  end
  
  N = AbNormRelation(A[1].base)
  N.den = d
  N.coeffs = coeffs
  N.brauer_coeffs = brauer_coeffs
  N.subs = subs
  N.nonred = nonred
  return N
end

# Get bezout coefficients. Like gcdx but works on arrays and forces
# nonzero coefficients.
function bezout(A::Array{Int, 1})
  d = 0
  U = [1]
  old_d = A[1]
  for i in 2:length(A)
    d, v1, v2 = gcdx(old_d, A[i])
    # then d == A[i] or  d == 1 resp.?
    if v1 == 0 || v2 == 0
      # transform to nonzero coeffs
      # might want to play with k to minimize coeff size
      k = 1
      v1 = numerator(v1 - k*(A[i]//d))
      v2 = numerator(v2 + k*(old_d//d))
    end
    @assert v1*old_d + v2*A[i] == d
    U = [u*v1 for u in U]
    push!(U, v2)
    old_d = d
  end
  @assert sum([U[i]*A[i] for i in 1:length(A)]) == d
  return d, U
end

# returns the p-part of G as well as the coprime-to-p-part 
function p_part(G::GrpAbFinGen, p::Union{fmpz, Int})
  ord = order(G)
  k = valuation(ord, p)
  #return quo(G, p^k), quo(G, Int64(round(ord//(p^k))))
  return sub(G, numerator(ord//(p^k))), sub(G, p^k)
end

# returns the p-rank of a group
function p_rank(G::GrpAbFinGen, p::Union{fmpz, Int})
  Q, mQ = quo(G, p)
  # should be an easier way to get the cyclic factors?
  return length(elementary_divisors(Q))
end

# Decompose G as C x Q where C is the largest cyclic factor.
# TODO: return subgroups of G with maps into G (quo is not a subgp)
function cyclic_factor(G::GrpAbFinGen)
  m = maximum(elementary_divisors(G))
  # the subgroups iterator is apparently not type stable
  C = first(subgroups(G, order=m))::Tuple{GrpAbFinGen, GrpAbFinGenMap}
  return C, quo(G, C[1])
end

# TODO: Really bad implementation, not really an issue though
function character_kernel(X::GrpAbFinGenElem, mX::Map, G::GrpAbFinGen)
  ker = GrpAbFinGenElem[]
  for g in collect(G)
    if mX(X)(g).elt == 0
      push!(ker, g)
    end
  end
  return sub(ker)
end


# proposition 2.26 of BFHP
function naive_norm_relation(G::GrpAbFinGen)
  # dual group (group of chars)
  D, mD = dual(G)
  ord = order(G)
  Lp = collect(keys(factor(ord).fac))
  rp = [p_rank(G, p) for p in Lp]

  N = AbNormRelation(G)
  if iscyclic(G)
    return N  
  end

  check = Set() 
  N.subs = []
  coeffs = []
  for chi in D
    ker = character_kernel(chi, mD, G)

    # skip duplicate subgroups
    if ker[2].map in check
      continue
    else
      push!(check, ker[2].map)
    end
    push!(N.subs, ker)

    c = order(chi)
    coeff = 1
    for i in 1:length(Lp)
      p = Lp[i]
      if c % p == 0
        if chi in Set([p*X for X in D])
          coeff *= 1 - p^(rp[i] - 1)
        end
      else
        coeff *= 1 - (p^rp[i] - 1)//(p - 1)
      end
    end
    push!(coeffs, coeff*c//ord)
  end
  N.den = lcm([denominator(c) for c in coeffs])
  N.coeffs = [numerator(c*N.den) for c in coeffs]
  N.brauer_coeffs = [[divexact(N.coeffs[i]*order(N.subs[i][1]), N.den) for i in 1:length(N)]]

  # determine indices of nonredundant subgroups
  N.nonred = [1 for i in 1:length(N)]
  for i in 1:length(N)
    for j in i+1:length(N)
      if Base.issubset(N.subs[j][1], N.subs[i][1])[1]
        N.nonred[i] = 0
        break
      end
    end
  end

  return N
end

function naive_norm_relation(G::GrpGen)
  G, AtoG, GtoA = Hecke.find_isomorphism_with_abelian_group(collect(G), *)
  return naive_norm_relation(G)
end

# optimal norm relation per theorem 2.27 of BFHP.
function _abelian_norm_relation(G::GrpAbFinGen; max_den::Int=0)
  C, Q = cyclic_factor(G)
  c = order(C[1])
  q = order(Q[1])

  if q == 1
    @vprint :NormRelation 2 "$G has no nontrivial norm relation.\n"
    return AbNormRelation(G)
  end

  primes = keys(factor(q).fac)
  if length(primes) > 1
    @vprint :NormRelation 2 "$G admits norm relation of denominator 1.\n"
    # subgroups in relation have index at most n0
    #n0 *= maximum([order(ppart(Q[1], p)[1][1]) for p in primes])
    
    normrels = Array{AbNormRelation{GrpAbFinGen}, 1}()
    for p in keys(factor(order(G)).fac)
      Gp, Gcp = p_part(G, p)
      @vtime :NormRelation 3 N = naive_norm_relation(Gcp[1])
      N = lift!(N, Gcp[2])
      push!(normrels, N)
    end
    # combine norm relations via bezout
    N = bezout(normrels)
    @assert N.den == 1

  elseif max_den == 1
    @vprint :NormRelation 2 "$G has no nontrivial norm relation with denominator <= $(max_den).\n"
    return AbNormRelation(G)

  else
    p = collect(primes)[1]
    Gp, Gcp = p_part(G, p)
    den = divexact(order(Gp[1]), p)
    @vprint :NormRelation 2 "$G admits norm relation of denominator $den.\n"

    if max_den != 0 && den > max_den
      @vprint :NormRelation 2 "Looking for norm relation with denominator <= $max_den.\n"
      # find largest noncyclic subgroup H < Gp with [Gp:H] > den/max_den

      ind = ZZ(ceil(Int(den)/max_den))
      if ind <= 1
        @vprint :NormRelation 2 "$G has no nontrivial norm relation with denominator <= $(max_den).\n"
        return AbNormRelation(G)
      end
      ind = minimum(filter(x -> x >= ind, divisors(Int(den))))

      # TODO: this approach is based on testing. how can we consistently choose a
      # noncyclic subgroup so the norm relation is optimal? (few subgroups of low order)
      # we should be able to describe it exactly instead of checking all subgroups
      H, mH = Gp
      divs1 = fmpz[]
      avg1 = 0
      subs = subgroups(H, index=ind)
      for s::Tuple{GrpAbFinGen, GrpAbFinGenMap} in subs
        if !iscyclic(s[1]) 
          divs2 = elementary_divisors(s[1])
          avg2 = Int(sum(divs2))/length(divs2)
          if (length(divs2) > length(divs1)) || (length(divs1) == length(divs2) && avg2 < avg1)
            H, mH = s
            divs1 = divs2
            avg1 = avg2
          end
        end
      end 
      Gp = (H, mH * Gp[2])
      str = join(["Z/$d" for d in divs1], " x ")
      @vprint :NormRelation 2 "Chose index $ind subgroup $str.\n"
      #@assert N.den <= max_den
    end

    @vtime :NormRelation 3 N = naive_norm_relation(Gp[1])
    N = lift!(N, Gp[2])

    #@assert N.den == order(Gp[1])//p
  end
  return N
end

function _abelian_norm_relation(G::GrpGen; max_den::Int=0)
  G, AtoG, GtoA = Hecke.find_isomorphism_with_abelian_group(collect(G), *)
  return _abelian_norm_relation(G, max_den=max_den)
end

# norm relation of a field K
# if full we skip finding denominator 1 norm relation and instead find the
# norm relation with smallest subfields (not compatible with max_den)
function _abelian_norm_relation(K::AnticNumberField; max_den::Int=0, full::Bool=false)
  N = AbNormRelation(K)
  if degree(K) == 1
    return N
  end

  @vtime :NormRelation 2 A, mA = automorphism_group(K)
  G, AtoG, GtoA = Hecke.find_isomorphism_with_abelian_group(collect(A), *)

  iscyclo, n = Hecke.iscyclotomic_type(K)
  if iscyclo
    t = basiszahl_cyclo(K)
  end

  if full
    @vtime :NormRelation 2 NG = naive_norm_relation(G)
  else
    @vtime :NormRelation 2 NG = _abelian_norm_relation(G, max_den=max_den)
  end
  flush(stdout)

  N.den = NG.den
  N.coeffs = NG.coeffs
  N.brauer_coeffs = NG.brauer_coeffs
  N.nonred = NG.nonred

  if length(NG) == 1
    return N
  end

  N.subs = Tuple{AnticNumberField, NfToNfMor}[]
  for i in 1:length(NG)
    H, mH = subgroup(NG, i)

    @vprint :NormRelation 2 "Computing fixed field for subgroup $(i)/$(length(NG)).\n"
    # should work for abelian fields in general
    #if iscyclo
    #  @vtime :NormRelation 3 L, mL = fixed_field_abelian(K, mA, GtoA, mH, gen=t)
    #  @assert length(Hecke.get_automorphisms(L)) != 0
    #  flush(stdout)
    #else
      @vtime :NormRelation 3 autos = NfToNfMor[mA(GtoA[mH(h)]) for h in gens(H)]
      @vtime :NormRelation 3 L, mL = fixed_field(K, autos)
      flush(stdout)
    #end

    if 1 < degree(L) <= 50
      @vprint :NormRelation 2 "Degree <= 50, simplifying the defining polynomial.\n"
      @vtime :NormRelation 3 S, mS = simplify(L, cached=false)
      flush(stdout)

      Hecke.set_automorphisms(S, [mS * aut * inv(mS) for aut in automorphisms(L)])
      L, mL = (S, mS * mL)
    end
    push!(N.subs, (L, mL))
  end

  return N
end

function abelian_norm_relation(K::AnticNumberField; max_den::Int=0, full::Bool=false)
  N = _abelian_norm_relation(K, max_den=max_den, full=full)
  if istrivial(N)
    return false, NormRelation{Int}()
  else
    return true, get_hecke_norm_relation(N)
  end
end


################################################################################
#
#  Conversion to Hecke native norm relations
#
################################################################################

function get_hecke_norm_relation(N::AbNormRelation{AnticNumberField})
  K = N.base
  z = Hecke.NormRel.NormRelation{Int}()
  z.K = K
  n = length(N)
  z.is_normal = trues(n)
  z.subfields = Vector{Tuple{AnticNumberField, NfToNfMor}}(undef, n)
  z.denominator = denominator(N)
  z.ispure = true
  z.embed_cache_triv = Vector{Dict{nf_elem, nf_elem}}(undef, n)
  z.nonredundant = Vector{Int}()
  for i in 1:n
    if Bool(N.nonred[i])
      push!(z.nonredundant, i)
    end
  end

  for i in 1:n
    z.subfields[i] = N.subs[i]
  end

  z.coefficients_gen = Vector{Vector{Tuple{Int, NfToNfMor, NfToNfMor}}}(undef, n)

  ii = id_hom(K)

  #coefficients_gen::Vector{Vector{Tuple{Int, NfToNfMor, NfToNfMor}}}
  for i in 1:n
    z.coefficients_gen[i] = [(N.coeffs[i], ii, ii)]
  end

  for i in 1:n
    z.embed_cache_triv[i] = Dict{nf_elem, nf_elem}()
  end

  return z
end
