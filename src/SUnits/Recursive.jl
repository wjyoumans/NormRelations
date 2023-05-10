
# Modified from Hecke: `src/NumField/NfAbs/NormRelation/SUnits.jl`

function _embed(N::NormRelation, i::Int, a::nf_elem)
  b = get(N.embed_cache_triv[i], a, nothing)
  if b === nothing
    _, mk = subfield(N, i)
    c = mk(a)
    N.embed_cache_triv[i][a] = c
    return c
  else
    return b
  end
end

function _get_sunits(N, i, lp, cache::NormRelCache)
  k = subfield(N, i)[1]
  subfield_cache = _subfield_cache(cache, i)
  if degree(k) > 36 && has_norm_relation(subfield_cache)
      Nk = norm_relation(subfield_cache)
      Szk, mS = sunit_group_fac_elem(lp, Nk, cache=subfield_cache)
  else
    Szk, mS = sunit_group_fac_elem(lp)
    subfield_cache.SU = Szk
    subfield_cache.mSU = mS
  end
  return Szk, mS
end

# pure

function _add_sunits_from_brauer_relation!(c, UZK, N, cache::NormRelCache; invariant::Bool = false, compact::Int = 0, saturate_units::Bool = false)
  # I am assuming that c.FB.ideals is invariant under the action of the automorphism group used by N
  cp = sort!(collect(Set(minimum(x) for x = c.FB.ideals)))
  K = N.K
  add_unit_later = FacElem{nf_elem, AnticNumberField}[]
  @vprint :NormRelation 1 "Adding trivial relations\n"
  for I in c.FB.ideals
    a = I.gen_one
    Hecke.class_group_add_relation(c, K(a), fmpq(abs(a)^degree(K)), fmpz(1), orbit = false)
    b = I.gen_two.elem_in_nf
    bn = Hecke.norm_div(b, fmpz(1), 600)
    if nbits(numerator(bn)) < 550
      Hecke.class_group_add_relation(c, b, abs(bn), fmpz(1), orbit = false)
    end
  end
 
  for i = 1:length(N)
    k, mk = subfield(N, i)
    if isdefined(N, :nonredundant) && !(i in N.nonredundant)
      continue
    end
    @vprint :NormRelation 1 "Looking at the subfield $i / $(length(N)) with defining equation $(k.pol) \n"
    @vprint :NormRelation 1 "Computing lll basis of maximal order ...\n"
    zk = maximal_order(k)
    zk = lll(zk)
    lpk = NfOrdIdl[]
    for p in cp
      append!(lpk, prime_ideals_over(zk, p))
    end
    @assert length(lpk) > 0
    @vprint :NormRelation 1 "Computing sunit group for set of size $(length(lpk)) ... \n"
    Szk, mS = _get_sunits(N, i, lpk, cache)

    @vprint :NormRelation 1 "Coercing the sunits into the big field ...\n"
    z = induce_action_just_from_subfield(N, i, lpk, c.FB, invariant)

    #found_torsion = false
    #CAREFUL! I AM ASSUMING THAT THE FIRST ELEMENT IS A TORSION UNIT!
    for l=2:ngens(Szk)
      @vprint :NormRelation 3 "Sunits $l / $(ngens(Szk))\n"
      u = mS(Szk[l])  #do compact rep here???
      if iszero(mS.valuations[l])
        if UZK.finished
          continue
        end
        if compact != 0
          @vprint :NormRelation 3 "  Compact presentation ...\n"
          @vtime :NormRelation 4 u = Hecke.compact_presentation(u, compact, decom = Dict{NfOrdIdl, Int}())
        elseif saturate_units
          @vprint :NormRelation 3 "  Compact presentation ...\n"
          @vtime :NormRelation 4 u = Hecke.compact_presentation(u, is_power(index(N))[2], decom = Dict{NfOrdIdl, Int}())
        end
        @vtime :NormRelation 4 img_u = FacElem(Dict{nf_elem, fmpz}((_embed(N, i, x), v) for (x,v) = u.fac))
        #=
        if !found_torsion
          fl = Hecke.is_torsion_unit(img_u, false, 16)[1]
          if fl
            found_torsion = true
            continue
          end
        end
        =#
        has_full_rk = Hecke.has_full_rank(UZK)
        @vtime :NormRelation 4 ff = Hecke.add_unit!(UZK, img_u)
        if !has_full_rk && !ff
          push!(add_unit_later, img_u)
        end
      else
        valofnewelement = mul(mS.valuations[l], z)
        #=
        if isdefined(c.M, :basis)
          push!(deb_rr, (deepcopy(c.M.basis), deepcopy(valofnewelement)))
          rr = Hecke.reduce_right!(c.M.basis, deepcopy(valofnewelement))
          MM = matrix(c.M.basis)
          vv = zero_matrix(FlintZZ, 1, ncols(MM))
          for (jj, vvv) in valofnewelement
            vv[1, jj] = vvv
          end
          Hecke.reduce_mod_hnf_ur!(vv, MM)
          @assert iszero(rr) == iszero(vv)
          if iszero(rr)
            continue
          end
        end
        =#
        if compact != 0
          sup = Dict{NfOrdIdl, Int}((lpk[w], t) for (w, t) in mS.valuations[l])
          @vprint :NormRelation 3 "  Compact presentation ...\n"
          @vtime :NormRelation 4 u = Hecke.compact_presentation(u, compact, decom = sup)
        end
        @vtime :NormRelation 4 img_u = FacElem(Dict{nf_elem, fmpz}((_embed(N, i, x), v) for (x, v) = u.fac if !iszero(v)))
        @hassert :NormRelation 1 sparse_row(FlintZZ, [ (j, valuation(img_u, p)) for (j, p) in enumerate(c.FB.ideals) if valuation(img_u, p) != 0]) == valofnewelement
        @vtime :NormRelation 4 Hecke.class_group_add_relation(c, img_u, valofnewelement)
        #=
        if rank(c.M) == length(c.FB.ideals)
          h, piv = Hecke.class_group_get_pivot_info(c)
        end
        =#
      end
    end
    @vprint :NormRelation 4 "Reducing the units\n"
    @vtime :NormRelation 4 UZK.units = Hecke.reduce(UZK.units, UZK.tors_prec)
  end

  if length(add_unit_later) > 0
    for uu in add_unit_later
      Hecke.add_unit!(UZK, uu)
    end
    UZK.units = Hecke.reduce(UZK.units, UZK.tors_prec)
  end
end

# TODO: Encode that the i-th field is normal over Q
function induce_action_just_from_subfield(N::NormRelation, i, s, FB, invariant = false)
  S = FB.ideals
  ZK = order(S[1])

  z = zero_matrix(SMat, FlintZZ, 0, length(S))

  mk = Hecke.NormRel.embedding(N, i)
  zk = order(s[1])

  @assert mod(degree(ZK), degree(zk)) == 0
  reldeg = divexact(degree(ZK), degree(zk))

  for l in 1:length(s)
    v = Tuple{Int, fmpz}[]
    P = s[l]
    genofsl = elem_in_nf(_embed(N, i, P.gen_two.elem_in_nf))
    pmin = minimum(P, copy = false)
    # Compute the number of ideals
    # We use this to speed things up if L/K and L/Q are normal.
    # We are checking this below.
    local numb_ideal::Int
    if is_normal(number_field(ZK))
      rele = divexact(ramification_index((FB.fb[pmin].lp)[1][2]), ramification_index(P))
      relf = divexact(degree((FB.fb[pmin].lp)[1][2]), degree(P))
      @assert mod(reldeg, rele * relf) == 0
      numb_ideal = divexact(reldeg, rele * relf)
    else
      numb_ideal = -1
    end
    found = 0
    for k in 1:length(S)
      Q = S[k]
      if minimum(Q, copy = false) == pmin
        if genofsl in Q
          found += 1
          @assert mod(ramification_index(Q), ramification_index(s[l])) == 0
          push!(v, (k, divexact(ramification_index(Q), ramification_index(s[l]))))
        end
      end
      if invariant && N.is_normal[i] && is_normal(number_field(ZK))
				if found == numb_ideal
					break
				end
			end
    end
    sort!(v, by = x -> x[1])
    push!(z, sparse_row(FlintZZ, v))
  end
  return z
end

function _setup_for_norm_relation_fun(K, S = prime_ideals_up_to(maximal_order(K), Hecke.factor_base_bound_grh(maximal_order(K))))
  ZK = order(S[1])
  FB = Hecke.NfFactorBase(ZK, S)
  c = Hecke.class_group_init(FB)
  UZK = get_attribute!(ZK, :UnitGrpCtx) do
    return Hecke.UnitGrpCtx{FacElem{nf_elem, AnticNumberField}}(ZK)
  end::Hecke.UnitGrpCtx{FacElem{nf_elem, AnticNumberField}}
  return c, UZK
end

function _find_perm(v::Vector{NfOrdIdl}, w::Vector{NfOrdIdl})
  p = Dict{Int, Int}()
  for i = 1:length(v)
    pi = findfirst(isequal(v[i]), w)
    @assert pi != nothing
    p[pi] = i
  end
  return p
end

function __sunit_group_fac_elem_quo_via_brauer(N::NormRelation, S::Vector{NfOrdIdl}, n::Int, invariant::Bool = false, compact::Int = 0; saturate_units::Bool = false, cache::NormRelCache=NormRelCache(S, N))
  O = order(S[1])
  K = N.K
  if invariant
    c, UZK = _setup_for_norm_relation_fun(K, S)
    _add_sunits_from_brauer_relation!(c, UZK, N, cache, invariant = true, compact = compact, saturate_units = saturate_units)
  else
    cp = sort!(collect(Set(minimum(x) for x = S)))
    Sclosed = NfOrdIdl[]
    # If K is non-normal and N does not use the full automorphism group, we
    # might be enlarging S too much.
    for p in cp
      append!(Sclosed, prime_ideals_over(O, p))
    end
    if length(Sclosed) == length(S)
      invariant = true
      Sclosed = S
    end
    if !invariant
      @vprint :NormRelation 1 "I am not Galois invariant. Working with S of size $(length(Sclosed))\n"
    end
    c, UZK = _setup_for_norm_relation_fun(K, Sclosed)
    _add_sunits_from_brauer_relation!(c, UZK, N, cache, invariant = true, compact = compact, saturate_units = saturate_units)
  end

  if gcd(index(N), n) != 1
    # I need to saturate
    for (p, e) in factor(index(N))
      @vprint :NormRelation 1 "Saturating at $p \n"
      b = Hecke.saturate!(c, UZK, Int(p), 3.5, easy_root = degree(K) > 30, use_LLL = true)
      while b
        b = Hecke.saturate!(c, UZK, Int(p), 3.5, easy_root = degree(K) > 30, use_LLL = true)
      end
    end
    UZK.finished = true
  end

  if index(N) == 1
    UZK.finished = true
  end

  if saturate_units && !UZK.finished
    for (p, e) in factor(index(N))
      @vprint :NormRelation 1 "Saturating at $p \n"
      b = Hecke.saturate!(UZK, Int(p), 3.5, easy_root = degree(K) > 30, use_LLL = true)
      while b
        b = Hecke.saturate!(UZK, Int(p), 3.5, easy_root = degree(K) > 30, use_LLL = true)
      end
    end
    UZK.finished = true
  end

  # This makes c.R.gen a basis of the S-units (modulo torsion)
  c = Hecke.RelSaturate.simplify(c, UZK, use_LLL = true)
  perm_ideals = _find_perm(S, c.FB.ideals)
  if invariant
    sunitsmodunits = FacElem{nf_elem, AnticNumberField}[x for x in c.R_gen] # These are generators for the S-units (mod units, mod n)
    valuations_sunitsmodunits = Vector{SRow{fmpz}}(undef, length(S))
    for i = 1:length(sunitsmodunits)
      r = Tuple{Int, fmpz}[(perm_ideals[j], v) for (j, v) in c.M.bas_gens[i]]
      sort!(r, lt = (a,b) -> a[1] < b[1])
      valuations_sunitsmodunits[i] = sparse_row(FlintZZ, r)
    end
  else
    # I need to extract the S-units from the Sclosed-units
    # Now I need to find the correct indices in the c.FB.ideals
    sunitsmodunits = FacElem{nf_elem, AnticNumberField}[]
    valuations_sunitsmodunits = SRow{fmpz}[]
    ind = Int[]
    for P in S
      for i in 1:length(c.FB.ideals)
        if P == c.FB.ideals[i]
          push!(ind, i)
          break
        end
      end
    end
    sort!(ind)
    # ind = indices of S inside c.FB.ideals
    @assert length(Sclosed) == length(c.FB.ideals)
    @assert length(ind) == length(S)
    z = zero_matrix(FlintZZ, length(c.R_gen), length(Sclosed) - length(S))
    for i in 1:length(c.R_gen)
      k = 1
      for j in 1:length(Sclosed)
        if !(j in ind)
          z[i, k] = c.M.bas_gens[i, j]
          if k == ncols(z)
            break
          end
          k = k + 1
        end
      end
    end
    k, K = left_kernel(z)
    for i in 1:nrows(K)
      if is_zero_row(K, i)
        continue
      end
      push!(sunitsmodunits, FacElem(c.R_gen, fmpz[K[i, j] for j in 1:ncols(K)]))
      v_c = sum(SRow{fmpz}[K[i, j]*c.M.bas_gens[j] for j = 1:ncols(K)])
      r = Tuple{Int, fmpz}[(perm_ideals[j], v) for (j, v) in v_c]
      sort!(r, lt = (a,b) -> a[1] < b[1])
      push!(valuations_sunitsmodunits, sparse_row(FlintZZ, r))
    end
  end

  unitsmodtorsion = UZK.units # These are generators for the units (mod n)
  T, mT = torsion_unit_group(O)
  Q, mQ = quo(T, n, false)
  # Q need not be in SNF, but we need that it is generated by one element.
  @assert ngens(Q) == 1
  m = order(Q)
  if !isone(m)
    units = Vector{FacElem{nf_elem, AnticNumberField}}(undef, length(unitsmodtorsion)+1)
    units[1] = FacElem(elem_in_nf(mT(mQ\Q[1])))
    for i = 2:length(units)
      units[i] = unitsmodtorsion[i-1]
    end
    res_group = abelian_group(append!(fmpz[m], [fmpz(n) for i in 1:(length(sunitsmodunits) + length(unitsmodtorsion))]))
  else
    units = unitsmodtorsion
    res_group = abelian_group([fmpz(n) for i in 1:(length(sunitsmodunits) + length(unitsmodtorsion))])
  end
  local exp
  let res_group = res_group, units = units
    function exp(a::GrpAbFinGenElem)
      @assert parent(a) == res_group
      z = prod(units[i]^a[i] for i = 1:length(units))
      if !isempty(sunitsmodunits)
        zz = prod(sunitsmodunits[i]^a[length(units) + i] for i in 1:length(sunitsmodunits))
        mul!(z, z, zz)
      end

      for (k, v) in z.fac
        if iszero(v)
          delete!(z.fac, k)
        end
      end
      return z
    end
  end


  disclog = function(a)
    throw(NotImplemented())
  end

  r = MapSUnitGrpFacElem()
  r.valuations = Vector{SRow{fmpz}}(undef, ngens(res_group))
  for i = 1:length(units)
    r.valuations[i] = sparse_row(FlintZZ)
  end
  for i = 1:length(sunitsmodunits)
    r.valuations[i+length(units)] = valuations_sunitsmodunits[i]
  end
  r.idl = S
  r.isquotientmap = n

  r.header = Hecke.MapHeader(res_group, FacElemMon(nf(O)), exp, disclog)
  @hassert :NormRelation 9001 begin
    _S, _mS = Hecke.sunit_group_fac_elem(S)
    @show _S
    @show res_group
    _Q, _mQ = quo(_S, n)
    V = quo(_Q, [_mQ(_mS\(r(res_group[i]))) for i in 1:ngens(res_group)])
    order(_Q) == order(res_group) && order(V[1]) == 1
  end
  @hassert :NormRelation 9000 begin
    fl = true
    for i = 1:ngens(res_group)
      el = r(res_group[i])
      if sparse_row(FlintZZ, [ (j, valuation(el, S[j])) for j = 1:length(S) if valuation(el, S[j]) != 0]) != r.valuations[i]
        fl = false
        break
      end
    end
    fl
  end

  cache.SU = res_group
  cache.mSU = r
  return (res_group, r)::Tuple{GrpAbFinGen, MapSUnitGrpFacElem}
end

function sunit_group_fac_elem(S::Vector{NfOrdIdl}, N::NormRelation, invariant::Bool = false, compact::Int = 0; saturate_units::Bool = false, cache::NormRelCache = NormRelCache(S, N))
  return __sunit_group_fac_elem_quo_via_brauer(N, S, 0, invariant, compact, saturate_units=saturate_units, cache=cache)
end
