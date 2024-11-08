import Hecke: class_group_ctx, unit_group_ctx

########################################################################

function _howell_form_lower_left(x::zzModMatrix)
  h = howell_form(reverse_cols(x))
  reverse_cols!(h)
  reverse_rows!(h)
  return h
end

function _left_kernel_prime_power(A::zzModMatrix, p::Int, l::Int)
  R = base_ring(A)
  Alift = lift_nonsymmetric(A)
  F = Hecke.Nemo.Native.GF(p)
  _M = kernel(change_base_ring(F, Alift); side = :left)
  _M = vcat(_M, zero_matrix(F, nrows(Alift) - nrows(_M), ncols(_M)))
  M = lift_nonsymmetric(_M)
  Mi = hnf_modular_eldiv(M, ZZRingElem(p))
  r = nrows(Mi)
  while r > 0 && is_zero_row(Mi, r)
    r -= 1
  end
  Mi = sub(Mi, 1:r, 1:ncols(Mi))
  Mfi = Mi * Alift
  local H
  for i in 1:(l - 1)
    K = kernel(change_base_ring(F, divexact(Mfi, p^i)); side = :left)
    K = vcat(K, zero_matrix(F, nrows(Mfi) - nrows(K), ncols(K)))
    H = hnf_modular_eldiv(lift_nonsymmetric(K), ZZRingElem(p))
    r = nrows(H)
    while is_zero_row(H, r)
      r -= 1
    end
    H = sub(H, 1:r, 1:ncols(H))

    Mi = H * Mi
    Mfi = H * Mfi
  end
  Khow = howell_form(change_base_ring(R, Mi))
  i = 1
  while i <= nrows(Khow) && !is_zero_row(Khow, i)
    i += 1
  end
  return i - 1, Khow
end

function has_grunwald_wang_obstruction(K, p, d)
  @assert Hecke.is_prime_power(d)

  if mod(d, 8) != 0
    return false
  end

  x = polynomial_ring(ZZ, cached = false)[2]
  r = 1
  f = cos_minpoly(2, x)
  while Hecke.hasroot(f, K)[1]
    r += 1
    f = cos_minpoly(2^r, x)
  end
  s = r - 1
  fl, etas = Hecke.hasroot(cos_minpoly(2^s, x), K)
  @assert fl

  if d <= 2^s
    return false
  end

  if is_square(K(-1))[1]
    return false
  end

  if is_square(2 + etas)[1]
    return false
  end

  if is_square(-(2 + etas))[1]
    return false
  end

  return true
end


################################################################################
#
#  Code for saturating the unit group
#  Copied from Hecke and slightly adjusted
#
################################################################################


function lift_nonsymmetric(a::zzModMatrix)
    z = ZZMatrix(nrows(a), ncols(a))
    #z.base_ring = FlintZZ
    ccall((:fmpz_mat_set_nmod_mat_unsigned, Hecke.libflint), Nothing,
            (Ref{ZZMatrix}, Ref{zzModMatrix}), z, a)
    return z
end

function lift_nonsymmetric(a::fpMatrix)
    z = ZZMatrix(nrows(a), ncols(a))
    #z.base_ring = FlintZZ
    ccall((:fmpz_mat_set_nmod_mat_unsigned, Hecke.libflint), Nothing,
            (Ref{ZZMatrix}, Ref{fpMatrix}), z, a)
    return z
end

function dlog(dl::Dict, x, p::Int) 
    if iszero(x)
      throw(Hecke.BadPrime(1))
    end
    if haskey(dl, x)
      return dl[x]
    end
  #  println("difficult for ", parent(x))
    i = 2
    y = x*x
    while !haskey(dl, y)
      y *= x
      i += 1
      @assert i <= p
    end
    #OK: we know x^i = g^dl[y] (we don't know g)
    v = dl[y]
    g = gcd(p, i)
    r = div(p, g)
    @assert v % g == 0
    e = invmod(div(i, g), r)*div(v, g) % r
    if e == 0
      e = r
    end
    dl[x] = e
    y = x*x
    f = (e*2) % p
    while !isone(y)
      if haskey(dl, y)
        @assert dl[y] == f
      end
      dl[y] = f
      y *= x
      f = (f+e) % p
    end
    g = [ a for (a,b) = dl if b == 1]
    @assert length(g) == 1
    @assert g[1]^dl[x] == x
    return dl[x]
  end

function mod_p(R, Q::AbsSimpleNumFieldOrderIdeal, p::Int, T)
  @vprint :NormRelation 2 "mod_p: Q=$(Q), p=$(p)\n"

  Zk = order(Q)
  F, mF = Hecke.ResidueFieldSmallDegree1(Zk, Q)
  mF1 = Hecke.extend_easy(mF, number_field(Zk))
  pp, e = Hecke.ppio(Int(size(F)-1), p)
  #@assert size(F) % p == 1
  # find k with
  # F*/F*^p = k*Z/p*Z
  k = div(p, min(p, pp))
  dl = Dict{elem_type(F), Int}()
  dl[F(1)] = 0
  lp = factor(p)
  while true
    x = rand(F)
    if iszero(x)
      continue
    end
    x = x^e
    if any(i-> x^div(pp, Int(i)) == 1, keys(lp.fac))
      continue
    else
      dlog(dl, x, pp)
      @assert length(dl) == pp
      break
    end
  end
  #TODO: in the image of mF1, if the input is a FacElem, the exponents should be reduced by pp.
  #This avoids some inverses.
  return matrix(T, 1, length(R), Int[k * (dlog(dl, image(mF1, x, pp)^e, pp) % p) for x in R])
end

function saturate_exp(R, d::Int; stable = 10, strategy = :classic, must_be_unique::Bool = false)
  K = base_ring(R[1])
  OK = maximal_order(K)

  @assert is_prime(d)

  T = Hecke.Nemo.Native.GF(d)
  A = identity_matrix(T, length(R))
  n = ncols(A)
  i = 1

  # number of primes used succesfully (same as rows of matrix...?)
  num = 0
  S = Hecke.PrimesSet(Hecke.p_start, -1, d, 1)
  if strategy == :classic
    for q in S

      if isdefining_polynomial_nice(K) && isindex_divisor(OK, q)
        continue
      end

      if discriminant(OK) % q == 0
        continue
      end

      #if gcd(div(q-1, Int(pp)), pp) > 1 # not possible if cond(k) is involved
      #  continue
      #end

      lq = prime_decomposition(OK, q, 1)
      if length(lq) == 0
        continue
      end

      for Q in lq
        try
          z = mod_p(R, Q[1], d, T)
          z = z*A

          rrz, z = nullspace(z)
          if iszero(rrz)
            # We return the transposed one
            return zero_matrix(T, 0, length(R))
          end
          A = A*sub(z, 1:nrows(z), 1:rrz)

          if n == ncols(A) 
            i += 1
          else
            i = 0
            n = ncols(A)
          end
          num += 1
        catch e
          if !isa(e, Hecke.BadPrime)
            rethrow(e)
          end
        end
      end

      if i> stable*ncols(A)
        break
      end
    end
  else
    @assert strategy == :aurel
    stable = Hecke.unit_group_rank(K) + 4 * stable

    for q in S

      if isdefining_polynomial_nice(K) && isindex_divisor(OK, q)
        continue
      end

      if discriminant(OK) % q == 0
        continue
      end

      #if gcd(div(q-1, Int(pp)), pp) > 1 # not possible if cond(k) is involved
      #  continue
      #end

      lq = prime_decomposition(OK, q, 1)
      if length(lq) == 0
        continue
      end

      Q = lq[1]

      try
        z = mod_p(R, Q[1], d, T)
        z = z*A

        @vprint :NormRelation 2 "saturate_exp: computing nullspace of $(nrows(z)) by $(ncols(z)) matrix\n"
        @vtime :NormRelation 2 rrz, z = nullspace(z)
        if iszero(rrz)
          # We return the transposed one
          return zero_matrix(T, 0, length(R))
        end
        A = A*sub(z, 1:nrows(z), 1:rrz)

        if n == ncols(A) 
          i += 1
        else
          i = 0
          n = ncols(A)
        end
        num += 1
      catch e
        if !isa(e, Hecke.BadPrime)
          rethrow(e)
        end
      end

      if num > stable
        break
      end
    end
  end

  @vprint :NormRelation 2 "saturate_exp: number of primes used = $(num)\n"
  return lift_nonsymmetric(transpose(A))
end

function saturate_exp_generic(R::Vector{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}, d::Int; stable = 10, early_abort = false, strategy = :classic)
  @assert Hecke.is_prime_power(d)
  k, p = Hecke.is_power(d)
  @assert is_prime(p)
  K = base_ring(R[1])
  OK = maximal_order(K)

  T, = residue_ring(ZZ, d)
  n = length(R)
  i = 1
  A = identity_matrix(T, length(R))

  num = 0

  S = Hecke.PrimesSet(2, -1, p, 1)

  if strategy == :classic
    for q in S

      if isdefining_polynomial_nice(K) && isindex_divisor(OK, q)
        continue
      end

      if discriminant(OK) % q == 0
        continue
      end

      #if gcd(div(q-1, Int(pp)), pp) > 1 # not possible if cond(k) is involved
      #  continue
      #end

      #num += 1
      lq = prime_decomposition(OK, q, 1)
      if length(lq) == 0
        continue
      end

      for Q in lq
        try
          z = mod_p(R, Q[1], d, T)
          @assert ncols(z) == length(R)
          z = z*A
          @vtime :NormRelation 2 rrz, _z = _left_kernel_prime_power(transpose(z), p, k)
          _z = transpose(_z)
          @assert iszero(z * _z)
          z = _z
          if iszero(rrz)
            return zero_matrix(T, 0, length(R))
          end
          A = A*sub(z, 1:nrows(z), 1:rrz)
          if n == ncols(A) 
            i += 1
          else
            i = 0
            n = ncols(A)
          end
          num += 1
        catch e
          if !isa(e, Hecke.BadPrime)
            rethrow(e)
          end
        end
      end
      #@show typeof(H)
      if i> stable*ncols(A)
        break
      end

    end
  elseif strategy == :aurel
    stable = Hecke.unit_group_rank(K) + 4 * stable

    for q in S
      if isdefining_polynomial_nice(K) && isindex_divisor(OK, q)
        continue
      end

      if discriminant(OK) % q == 0
        continue
      end

      #if gcd(div(q-1, Int(pp)), pp) > 1 # not possible if cond(k) is involved
      #  continue
      #end

      #num += 1
      lq = prime_decomposition(OK, q, 1)
      if length(lq) == 0
        continue
      end

      Q = lq[1]

      try
        z = mod_p(R, Q[1], d, T)
        @assert ncols(z) == length(R)
        z = z*A
        @vtime :NormRelation 2 rrz, _z = _left_kernel_prime_power(transpose(z), p, k)
        _z = transpose(_z)
        @assert iszero(z * _z)
        z = _z
        if iszero(rrz)
          return zero_matrix(T, 0, length(R))
        end
        A = A*sub(z, 1:nrows(z), 1:rrz)
        if n == ncols(A) 
          i += 1
        else
          i = 0
          n = ncols(A)
        end
        num += 1
      catch e
        if !isa(e, Hecke.BadPrime)
          rethrow(e)
        end
      end
      #@show typeof(H)
      if num > stable
        break
      end
    end
  end
  @vprint :NormRelation 2 "saturate_exp_generic: number of primes used = $(num)\n"
  return lift_nonsymmetric(transpose(A))
end

function _simplify(c::Hecke.ClassGrpCtx, U::Hecke.UnitGrpCtx)
  d = Hecke.class_group_init(c.FB, SMat{ZZRingElem}, add_rels = false)

  for i=1:length(U.units)  
    Hecke.class_group_add_relation(d, U.units[i], SRow(FlintZZ))
  end
  return d
end

function saturate(R::Vector{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}, d::Int64; 
    stable=10, strategy=:classic)

  if is_prime(d)
    @vtime :NormRelation 2 A = saturate_exp(R, d, stable=stable, 
      strategy=strategy)
  else
    e, p = Hecke.is_power(d)
    if !has_grunwald_wang_obstruction(base_ring(R[1]), p, d)
      @vtime :NormRelation 2 A = saturate_exp_generic(R, d, stable=stable, 
        strategy=strategy)
    else
      @assert p == 2
      @warn "Bad case of grunwald-wang! Trying 2^$(e)-saturation anyway."
      @vtime :NormRelation 2 A = saturate_exp_generic(R, d, stable=stable, 
        strategy=strategy)
    end
  end
  return A
end

function saturate_with_fixed_element(
    units::Vector{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}, 
    beta::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}, 
    d::Int; 
    stable = 10, 
    strategy = :classic)

  @assert Hecke.is_prime_power(d)
  R = copy(units)
  push!(R, beta)

  A = saturate(R, d, stable=stable, strategy=strategy)
  @assert ncols(A) == length(R)

  # Remove all rows of A, where the exponents are zero
  B = zero_matrix(ZZ, 0, ncols(A))
  for i in 1:nrows(A)
    if !iszero(A[i,:])
      B = vcat(B, A[i,:])
    end
  end

  Md = MatrixSpace(ResidueRing(ZZ, d, cached=false), ncols(B), ncols(B))
  temp = vcat(B, zero_matrix(base_ring(B), ncols(B) - nrows(B), ncols(B)))
  B = _howell_form_lower_left(Md(temp))
  
  # Now scale the rows so that the last entry (corresponding to the exponent of 
  # beta) is one
  for i in 1:nrows(B)
    if isunit(B[i, ncols(B)])
      c = inv(B[i, ncols(B)])
      for j in 1:ncols(B)
        B[i, j] = B[i, j] * c
      end
    end
  end
  if nrows(B) == 0
    return saturate_with_fixed_element(units, beta, d, stable = 10*stable, 
				       strategy=strategy)
  end

  return lift(B[nrows(B),:])
end

