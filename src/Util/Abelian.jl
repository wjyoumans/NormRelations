
# A "basiszahl" element of K is an element whose relative trace to any subfield
# is a primitive element of that subfield. Then the minimal polynomial of the trace
# is a defining polynomial for the subfield.
#
# TODO: Only works for cyclotomics but can be extended to abelian fields. Need to
# find a cyclotomic field containing it and ability to compute intersections of 
# fields.
function basiszahl(K::AbsSimpleNumField, conductor_multiple=0)
  if Hecke.is_cyclotomic_type(K)[1]
    return _basiszahl_cyclo(K)
  end

  error("Only cyclotomic fields supported.")
  # general "basiszahl" element for number fields
  # not yet implemented

  n = conductor_multiple
  m = n * 2^-valuation(n, 2)
  radm = prod(keys(factor(m).fac))
  r = divexact(m, radm)
  
  t = K(0)
  for d in divisors(r)
    if d % 4 == 2
      continue
    end

    L, a = cyclotomic_field(d)
    # TODO: intersect function?
    F = intersect(K, L)

    _, mF = issubfield(F, L)
    t += trace(mF, a)    
  end

  return t
end

function _basiszahl_cyclo(K::AbsSimpleNumField)
  b, n = Hecke.is_cyclotomic_type(K)
  !b && error("Field must be cyclotomic")

  z = gen(K)
  radn = prod(keys(factor(n).fac))
  r = divexact(n, radn)

  t = K(0)
  for d in divisors(Int(r))
    t += z^d
  end
  return t
end


### Minimal polynomials ###

function Hecke.minpoly(a::AbsSimpleNumFieldElem, autos::Vector{NumFieldHom})
  Kt, t = polynomial_ring(parent(a), "t", cached = false)
  g = one(Kt)
  for aut in autos
    mul!(g, g, t - aut(a))
  end
  Qx, x = polynomial_ring(FlintQQ, "x", cached = false)
  return Qx([coeff(coeff(g, i), 0) for i in 0:degree(g)])
end

# mA, mH as above.
function Hecke.minpoly(a::AbsSimpleNumFieldElem, mA, GtoA, mH)
  Q, mQ = quo(codomain(mH), mH, false)
  Kt, t = polynomial_ring(parent(a), "t", cached = false)
  g = one(Kt)
  for q in Q
    mul!(g, g, t - mA(GtoA[mQ\q])(a))
  end
  Qx, x = polynomial_ring(FlintQQ, "x", cached = false)
  return Qx([coeff(coeff(g, i), 0) for i in 0:degree(g)])
end

function Hecke.minpoly(a::AbsSimpleNumFieldElem, mH)
  K = parent(a)
  A, mA = automorphism_group(K)
  G, AtoG, GtoA = Hecke.find_isomorphism_with_abelian_group(collect(A), *)
  mH = hom(domain(mH), G, mH.map)
  return minpoly(a, mA, GtoA, mH)
end


### Fixed fields ###

# A automorphism group of K as a MultTableGroup, mA: A -> K. G is A as FinGenAbGroup. H is 
# a subgroup of G with mH: H -> G. Output fixed field K^H.
function fixed_field_abelian(K, mA, GtoA, mH; gen = basiszahl(K))
  # relative trace of gen
  t = K(0)
  for h in domain(mH)
    t += mA(GtoA[mH(h)])(gen)
  end
  
  # compute this set of automorphisms here since they are used both in 
  # computing the minpoly and finding automorphisms of the subfield.
  Q, mQ = quo(codomain(mH), mH, false)
  autos = Vector{NumFieldHom}(undef, length(Q))
  for (i, q) in enumerate(Q)
    autos[i] = mA(GtoA[mQ\q])
  end
  
  @vtime :Abelian 1 g = minpoly(t, autos)
  #@vtime :Abelian 1 g = minpoly(t, mA, GtoA, mH)
  L, a = number_field(g)
  mL = hom(L, K, t)
  @vtime :Abelian 1 _compute_and_set_automorphisms(L, mL, autos)
  return L, mL
end

function fixed_field_abelian(K::AbsSimpleNumField, mH; gen=basiszahl(K))
  A, mA = automorphism_group(K)
  G, AtoG, GtoA = Hecke.find_isomorphism_with_abelian_group(collect(A), *)
  #mH = hom(domain(mH), G, mH.img)
  return fixed_field_abelian(K, mA, GtoA, mH, gen=gen)
end


### Misc ###

function _compute_and_set_automorphisms(L, mL, autos)
  z = gen(L)
  b = mL(z)
  Lautos = Vector{NumFieldHom}(undef, length(autos))
  M = _matrix_of_powers(b, degree(L))
  for (i, aut) in enumerate(autos)
    fl, w = _haspreimage(mL, aut(b), M)
    @assert fl
    h = hom(L, L, w, check = true)
    Lautos[i] = h
  end
  Hecke.set_automorphisms(L, Lautos)
  return nothing
end

function _matrix_of_powers(b, n)
  d = degree(parent(b))
  z = one(parent(b))
  M = zero_matrix(FlintQQ, n, d)
  for i in 1:n
    for j in 1:d
      M[i, j] = coeff(z, j - 1)
    end
    z = mul!(z, z, b)
  end
  return M
end

function _haspreimage(f::NumFieldHom, a::AbsSimpleNumFieldElem, M = zero_matrix(FlintZZ, 0, 0))
  L = codomain(f)
  K = domain(f)
  b = f(K[1])
  d = degree(codomain(f))
  n = degree(domain(f))
  z = one(L)

  if isempty(M)
    M = _matrix_of_powers(b, n)
  end

  t = matrix(FlintQQ, 1, d, QQFieldElem[coeff(a, j - 1) for j in 1:d])

  fl, s = can_solve_with_solution(M, t, side = :left)
  
  if fl
    return true, K(QQFieldElem[s[1, i] for i in 1:n])
  else
    return false, zero(K)
  end
end

function automorphism_group_abelian(K::AbsSimpleNumField)
  b, f = Hecke.is_cyclotomic_type(K)
  if b
    a = gen(K)
    A, mA = unit_group(ResidueRing(FlintZZ, f))
    #aut = NumFieldHom[ hom(K, K, a^lift(mA(GtoA[g]))) for g in G]
    return A, a -> hom(K, K, gen(K)^lift(mA(a)), check = false)
  else
    G, mG = automorphism_group(K)
    A, GtoA, AtoG = Hecke.find_isomorphism_with_abelian_group(collect(G), *)
    return A, a -> mG(AtoG[a])
  end 
end 
