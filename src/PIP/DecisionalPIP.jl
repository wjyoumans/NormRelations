
#=
# decisional PIP using ideal decomposition
function is_principal(A::NfOrdIdl, f::MapSUnitGrpFacElem, N::NormRelation; 
    stable=10, strategy=:classic, lifts=false, parisizemax=1000000000)
  AK = abelian_group(f)
  _, v = decompose(A, f.idl, N, stable=stable, strategy=strategy, sunit_group_map=f, 
		   lifts=lifts, parisizemax=parisizemax)
  return iszero(AK(v))
end

# decisional PIP using ideal decomposition
function Hecke.is_principal(A::NfOrdIdl, f::MapSUnitGrpFacElem)
  AK = abelian_group(f)
  _, v = decompose(A, f.idl)
  return iszero(AK(v))
end
=#



# decisional PIP using ideal decomposition. S must generate the class group.
function decisional_pip(
    A::NfOrdIdl, 
    S::Vector{NfOrdIdl},
    stable=STABLE, 
    parisizemax=PARISIZEMAX,
    strategy=:classic) where T <: Union{NfOrdIdl, FacElem{NfOrdIdl}}

  cache = norm_relation_cache(S)
  return decisional_pip(A, cache=cache, stable=stable, parisizemax=parisizemax, 
			strategy=strategy)
end

# decisional PIP using ideal decomposition. S must generate the class group.
function decisional_pip(
    A::T, 
    S::Vector{NfOrdIdl}, 
    N::NormRelation,
    stable=STABLE, 
    parisizemax=PARISIZEMAX,
    strategy=:classic) where T <: Union{NfOrdIdl, FacElem{NfOrdIdl}}

  cache = norm_relation_cache(S, N)
  return decisional_pip(A, cache=cache, stable=stable, parisizemax=parisizemax, 
			strategy=strategy)
end

function decisional_pip(
    A::FacElem{NfOrdIdl};
    cache::NormRelCache=NormRelCache(),
    stable=STABLE, 
    parisizemax=PARISIZEMAX,
    strategy=:classic)

  return decisional_pip(evaluate(A), cache=cache, stable=stable, 
			parisizemax=parisizemax, strategy=strategy)
end

function decisional_pip(
    A::Hecke.NfAbsOrdFracIdl;
    cache::NormRelCache=NormRelCache(),
    stable=STABLE, 
    parisizemax=PARISIZEMAX,
    strategy=:classic)

  return decisional_pip(numerator(A), cache=cache, stable=stable, 
			parisizemax=parisizemax, strategy=strategy)
end

# decisional PIP using ideal decomposition. The cached ideal set must generate the 
# class group, otherwise we fall back to search-PIP.
function decisional_pip(
    A::NfOrdIdl;
    cache::NormRelCache=NormRelCache(),
    stable=STABLE, 
    parisizemax=PARISIZEMAX,
    strategy=:classic)

  if isempty(cache)
    @warn "Decisional PIP is falling back to search PIP!"
    return search_pip(A)[1]
  end

  @assert order(A) == order(cache)
  SU, mSU = sunit_group_fac_elem(cache)
  AK = abelian_group(mSU)
  _, v = decompose(A, cache, stable=stable, strategy=strategy, 
		   parisizemax=parisizemax)
  return iszero(AK(v))
end

