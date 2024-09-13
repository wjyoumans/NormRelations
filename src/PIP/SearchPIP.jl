
# Method 1: search for a short element x of A such that (x)/A = P a prime ideal.
# Compute the S-unit group for S containing P and its conjugates. Say M is the matrix
# of relations and a_i = (a_1, ..., a_n) is a row of M. Then 
# P_1^a_1 * ... * P_n^a_n = (b_i) is a principal ideal. Try to solve a matrix 
# equation to decompose P over the b_i. If it fails then A is not principal, otherwise
# A = (x)/P is principal and we return the generator.
#
# Use norm relation to compute S-unit group. If P is in cached ideal set then
# computing S-unit group is free (TODO).
#
# Method 2: Needs norm relation. norm the input ideal down to terminal subfields 
# in the norm relation and compute generators. If at any point this fails the ideal is
# not principal. Reconstructing using the norm relation may require a root. If 
# this fails the ideal is not principal. Otherwise we succeed and return the 
# generator.
#
# Potential option: Combination. Norm down a la method 2 then use method 1 to 
# solve PIP in subfields. More or less the same as method 2 except when we have
# denominator 1 norm relation?
#
# Probably best to use method 2 whenever possible, use method 1 when grunwald-wang 
# obstruction exists. Needs to be tested.

#TODO FacElem ideals, Fractional ideals

# TODO: choose method. Only uses method 1 for now.
function search_pip(A::AbsSimpleNumFieldOrderIdeal; cache::NormRelCache=NormRelCache())
  return search_pip_with_sunits(A, cache=cache)
end

# Return true and a generator if A is principal, false otherwise.
function search_pip_with_sunits(A::AbsSimpleNumFieldOrderIdeal; cache::NormRelCache=NormRelCache())
  local P, den

  if !isempty(cache)
    @assert order(A) == order(cache)
  end

  A, d = Hecke.reduce_ideal(A)
  OK = order(A)
  K = nf(OK)

  norm_A = norm(A)
  B = lll_basis(A)
  len = length(B)

  # quick check
  @vprint :PIP 1 "Decisional PIP with S-units. Doing quick check.\n"
  a = B[1]
  if norm(a) == norm_A
    return true, FacElem(K(a))*inv(d)
  end

  # next quickest check
  @vprint :PIP 1 "Doing next quickest search.\n"
  found = false
  for i = 1:len
    a = B[i]
    n = ZZ(divexact(norm(a), norm_A))
    if is_prime(n)
      P, den = integral_split(ideal(OK, a)//A)
      #if length(prime_decomposition(OK, minimum(P))) == degree(K)
	found = true
      break
      #end
    end
  end
 
  nnz = 2
  coeff_bound = 1
  attempts = 1
  if !found
    @vprint :PIP 1 "Doing harder search.\n"
  end
  while !found
    if attempts % len == 0
      nnz += 1
    elseif attempts % nnz*len == 0
      coeff_bound += 1
    end
    
    # random small linear combination of LLL-reduced basis of I
    a = OK(0)
    for i in 1:nnz
      a += rand(-coeff_bound:coeff_bound)*B[rand(1:length(B))]
    end
    
    n = ZZ(divexact(norm(a), norm_A))
    if n == 1
      return true, FacElem(K(a))*inv(d)
    elseif is_prime(n)
      P, den = integral_split(ideal(OK, a)//A)
      #if length(prime_decomposition(OK, minimum(P))) == degree(K)
	found = true
      #end
    end
    attempts += 1
  end

  p = minimum(P)
  @assert norm(den) == 1
  @assert is_prime(p)

  S = prime_ideals_over(OK, p)
  if issubset(S, idealset(cache))
    @warn "Unimplemented optimization in decisional_pip! Computing new S-unit group."
  end
  
  @vprint :PIP 1 "Computing new S-unit group for primes above p = $p.\n"
  cache = norm_relation_cache(S)
  @vtime :PIP 2 SU, mSU = sunit_group_fac_elem(cache)

  MS = sparse_matrix(ZZ)
  for row in mSU.valuations
    push!(MS, row)
  end
  M = matrix(MS)

  i = findfirst(isequal(P), S)
  x = zero_matrix(base_ring(M), ncols(M), 1)
  x[i,1] = 1

  @vprint :PIP 1 "Solving system.\n"
  b, s = can_solve_with_solution(transpose(M), x)
  if !b
    return false, FacElem(K(0)) 
  end

  a = FacElem(K(a))
  for i in 1:length(s)
    a *= mSU(SU[i])^-s[i]
  end
  return true, a*inv(d)
end

function Hecke.basis_matrix(::Type{Hecke.FakeFmpqMat}, A::AbsNumFieldOrderIdeal; copy::Bool = true)
  return Hecke.FakeFmpqMat(basis_matrix(A; copy = copy))
end

# Return true and a generator if A is principal, false otherwise.
function isprincipal_sunits(A::AbsSimpleNumFieldOrderIdeal, N::NormRelation)
  local P, den

  A, d = Hecke.reduce_ideal(A)
  OK = order(A)
  K = nf(OK)

  norm_A = norm(A)
  B = lll_basis(A)
  len = length(B)

  # quick check
  @vprint :PIP 1 "Decisional PIP with S-units. Doing quick check.\n"
  a = B[1]
  if norm(a) == norm_A
    return true, FacElem(K(a))*inv(d)
  end

  # next quickest check
  @vprint :PIP 1 "Doing next quickest search.\n"
  found = false
  for i = 1:len
    a = B[i]
    n = ZZ(divexact(norm(a), norm_A))
    if is_prime(n)
      P, den = integral_split(ideal(OK, a)//A)
      #if length(prime_decomposition(OK, minimum(P))) == degree(K)
	found = true
      break
      #end
    end
  end
 
  nnz = 2
  coeff_bound = 1
  attempts = 1
  if !found
    @vprint :PIP 1 "Doing harder search.\n"
  end
  while !found
    if attempts % len == 0
      nnz += 1
    elseif attempts % nnz*len == 0
      coeff_bound += 1
    end
    
    # random small linear combination of LLL-reduced basis of I
    a = OK(0)
    for i in 1:nnz
      a += rand(-coeff_bound:coeff_bound)*B[rand(1:length(B))]
    end
    
    n = ZZ(divexact(norm(a), norm_A))
    if n == 1
      return true, FacElem(K(a))*inv(d)
    elseif is_prime(n)
      P, den = integral_split(ideal(OK, a)//A)
      #if length(prime_decomposition(OK, minimum(P))) == degree(K)
	found = true
      #end
    end
    attempts += 1
  end

  p = minimum(P)
  @assert norm(den) == 1
  @assert is_prime(p)

  S = prime_ideals_over(OK, p)
  @vprint :PIP 1 "Computing new S-unit group for primes above p = $p.\n"
  @vtime :PIP 2 SU, mSU = sunit_group_fac_elem(S, N)

  MS = sparse_matrix(ZZ)
  for row in mSU.valuations
    push!(MS, row)
  end
  M = matrix(MS)

  i = findfirst(isequal(P), S)
  x = zero_matrix(base_ring(M), ncols(M), 1)
  x[i,1] = 1

  @vprint :PIP 1 "Solving system.\n"
  b, s = can_solve_with_solution(transpose(M), x)
  if !b
    return false, FacElem(K(0)) 
  end

  a = FacElem(K(a))
  for i in 1:length(s)
    a *= mSU(SU[i])^-s[i]
  end
  return true, a*inv(d)
end

# Use a norm relation to help solve the PIP
# TODO: some fields in the bottom layer are isomorphic/conjugate. We can
#   reduce the amount of class group computations by leveraging the isomorphism.
function Hecke.isprincipal(
      I::AbsSimpleNumFieldOrderIdeal, 
      NN::NormRelation; 
      max_den::Int = 0,
      redo::Bool = false, 
      stable::Int = 10,
      trager::Bool = false,
      strategy::Symbol = :aurel,
      obvious_decomposition = false)

  N = get_ab_norm_relation(NN)

  K = nf(order(I))
  OK = lll(order(I))
  I = IdealSet(OK)(I)

  @assert K == field(N)
  d = index(N)
  @vprint :NormRelation 2 "Solving PIP over $(nf(order(I))) "
  @vprint :NormRelation 2 "using norm relation with denominator $(d).\n"

  local a::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}
  local c::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}
  local b::Bool

  a = FacElem(K(1))
  b = true
  for i in 1:length(N)
    @vprint :NormRelation 2 "---------------------------------------------------------\n"
    L, mL = N[i]::Tuple{AbsSimpleNumField, NumFieldHom}
    OL = lll(maximal_order(L))

    @vprint :NormRelation 2 "Solving PIP in subfield $(i)/$(length(N)) of degree $(degree(L)).\n"
    if degree(L) == 1
      @vprint :NormRelation 2 "Trivial case.\n"
      b = true
      c = FacElem(L(norm(I)))

    elseif is_prime(degree(L))
      @vprint :NormRelation 2 "Solving PIP classically.\n"
      b, c = Hecke.isprincipal_fac_elem(norm(mL, I, order=OL))
      #b, c = Hecke.isprincipal_fac_elem(intersect(I, OL, mL))
    else
      @vprint :NormRelation 2 "Computing norm relation:\n"
      b, NS = abelian_norm_relation(L, max_den = max_den)

      if b
          b, c = isprincipal(norm(mL, I, order=OL), NS, obvious_decomposition = obvious_decomposition)
          #b, c = isprincipal(intersect(I, OL, mL), NS, obvious_decomposition = obvious_decomposition)
      else
          b, c = Hecke._isprincipal_fac_elem(norm(mL, I, order=OL))
          #b, c = Hecke._isprincipal_fac_elem(intersect(I, OL, mL))
      end
    end
    if !b return (false, FacElem(K(0))) end

    c = c^coefficient(N, i)
    mul!(a, a, embedding(N, i)(c))
  end
  @vprint :NormRelation 2 "\n"
  
  if d > 1
    @vprint :NormRelation 2 "Finding u, a such that u*b = a^d for d = $(d).\n"
    #b, a = ispower_mod_units(N, a, d, redo=redo, stable=stable, trager=trager, strategy=strategy)
    #if !b return (false, FacElem(K(0))) end
    if obvious_decomposition
      b, a = ispower_mod_units(NN, a, d, redo=redo, stable=stable, trager=trager, strategy=strategy, decom=FacElem(Dict(I => ZZRingElem(d))))
    else
      b, a = ispower_mod_units(NN, a, d, redo=redo, stable=stable, trager=trager, strategy=strategy)
    end
  end

  return b, a
end

# TODO: only works with AbNormRelation at the moment, convert to NormRelation
# and maybe use cache if it exists.
#=
# Use a norm relation to help solve the PIP
# TODO: some fields in the bottom layer are isomorphic/conjugate. We can
#   reduce the amount of class group computations by leveraging the isomorphism
function search_pip_without_sunits(
      I::AbsSimpleNumFieldOrderIdeal, 
      N::AbNormRelation{AbsSimpleNumField}; 
      max_den::Int = 0,
      redo::Bool = false, 
      stable::Int = 10,
      trager::Bool = false,
      strategy::Symbol = :aurel,
      obvious_decomposition = false)

    K = nf(order(I))
    OK = lll(order(I))
    I = IdealSet(OK)(I)

    @assert K == field(N)
    d = index(N)
    @vprint :NormRelation 2 "Solving PIP over $(nf(order(I))) "
    @vprint :NormRelation 2 "using norm relation with denominator $(d).\n"

    local a::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}
    local c::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}
    local b::Bool

    a = FacElem(K(1))
    b = true
    for i in 1:length(N)
      @vprint :NormRelation 2 "---------------------------------------------------------\n"
      L, mL = N[i]::Tuple{AbsSimpleNumField, NumFieldHom}
      OL = lll(maximal_order(L))

      @vprint :NormRelation 2 "Solving PIP in subfield $(i)/$(length(N)) of degree $(degree(L)).\n"
      if degree(L) == 1
        @vprint :NormRelation 2 "Trivial case.\n"
        b = true
        c = FacElem(L(norm(I)))

      elseif is_prime(degree(L))
        @vprint :NormRelation 2 "Solving PIP classically.\n"
        b, c = Hecke.isprincipal_fac_elem(norm(mL, I, order=OL))
        #b, c = Hecke.isprincipal_fac_elem(intersect(I, OL, mL))
      else
        @vprint :NormRelation 2 "Computing norm relation:\n"
	NS = _abelian_norm_relation(L, max_den = max_den)

        if !istrivial(NS)
            b, c = isprincipal(norm(mL, I, order=OL), NS, obvious_decomposition = obvious_decomposition)
            #b, c = isprincipal(intersect(I, OL, mL), NS, obvious_decomposition = obvious_decomposition)
        else
            b, c = Hecke._isprincipal_fac_elem(norm(mL, I, order=OL))
            #b, c = Hecke._isprincipal_fac_elem(intersect(I, OL, mL))
        end
      end
      if !b return (false, FacElem(K(0))) end

      c = c^coefficient(N, i)
      mul!(a, a, embedding(N, i)(c))
    end
    @vprint :NormRelation 2 "\n"
    
    if d > 1
      @vprint :NormRelation 2 "Finding u, a such that u*b = a^d for d = $(d).\n"
      #b, a = ispower_mod_units(N, a, d, redo=redo, stable=stable, trager=trager, strategy=strategy)
      #if !b return (false, FacElem(K(0))) end
      if obvious_decomposition
        b, a = ispower_mod_units(N, a, d, redo=redo, stable=stable, trager=trager, strategy=strategy, decom=FacElem(Dict(I => ZZRingElem(d))))
      else
        b, a = ispower_mod_units(N, a, d, redo=redo, stable=stable, trager=trager, strategy=strategy)
      end
    end

    return b, a
end
=#
