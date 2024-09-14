import Hecke: is_power, roots

function _ispower_mod_units_prime(units::Vector{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}},
                                  beta::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField},
                                  d::Int;
                                  stable = 10, trager = true,
                                  write = false, decom = false, strategy = :classic)
  R = copy(units)
  push!(R, beta)
  len = length(R)
  @vtime :NormRelation 1 A = saturate_exp(R, d, stable = stable, strategy = strategy)
  @assert len == ncols(A)

  # Remove all rows of A, where the exponents are zero
  n = count(i -> !iszero(A[i, len]), 1:nrows(A))
  if n == 0
    return false, beta
  end

  B = zero_matrix(Hecke.Nemo.Native.GF(d, cached = false), n, ncols(A))

  k = 0
  for i in 1:nrows(A)
    if iszero(A[i, len])
      continue
    else
      k += 1
      for j in 1:ncols(A)
        B[k, j] = A[i, j]
      end
    end
  end

  @assert k == n

  # Now scale the rows so that the last entry (corresponding to the exponent of beta) is one

  for i in 1:nrows(B)
    c = inv(B[i, ncols(B)])
    #multiply_row!(B, i, c)
    for j in 1:ncols(B)
      B[i, j] = B[i, j] * c
    end
  end

  BB = lift_nonsymmetric(B)

  @vprint :NormRelation 1 "There are $(nrows(BB)) many candidates\n"
  for i in 1:nrows(BB)
    @vprint :NormRelation 1 "Testing candidate $i/$(nrows(BB))\n"
    @vprint :NormRelation 1 "trager = $(trager)\n"
    candidate = prod([units[j]^Int(BB[i, j]) for j in 1:ncols(B) - 1])*beta
    if !(write isa Bool)
      save_factored_element(candidate, write)
    end
    if decom != false
      @vtime :NormRelation 1 b, r = is_power(candidate, d, trager = trager, decom = decom.fac)
    else
      @vtime :NormRelation 1 b, r = is_power(candidate, d, trager = trager)
    end
    if b return (b, r) end
  end

  # We have to redo with larger stable
  return _ispower_mod_units_prime(units,
                                  beta,
                                  d,
                                  stable = 10 * stable, trager = trager,
                                  write = write,
                                  strategy = strategy)
  return false, beta
end

# given factored element beta and integer d, seach for a unit u such that u*beta is a dth power
function _ispower_mod_units_generic(units::Vector{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}, beta::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}, d::Int; stable = 10, trager = true, write = false, decom = false, strategy = :classic)
  R = copy(units)
  push!(R, beta)
  len = length(R)
  @vtime :NormRelation 1 A = saturate_exp_generic(R, d, stable = stable, strategy = strategy)
  @assert len == ncols(A)

  # Remove all rows of A, where the exponents are zero
  n = count(i -> !iszero(A[i, len]), 1:nrows(A))
  if n == 0
    return false, beta
  end

  B = zero_matrix(residue_ring(FlintZZ, d, cached = false)[1], n, ncols(A))

  k = 0
  for i in 1:nrows(A)
    if iszero(A[i, len])
      continue
    else
      k += 1
      for j in 1:ncols(A)
        B[k, j] = A[i, j]
      end
    end
  end

  @assert k == n

  # I make the matrix like this
  # [ * * * * 0 0 0 ]
  # [ * * * * * 0 0 ]
  # [ * *       * 0 ]
  # [ *           * ]
  # So there is only one element to test

  B = _howell_form_lower_left(vcat(B, zero_matrix(base_ring(B), ncols(B) - nrows(B), ncols(B))))

  # Now scale the rows so that the last entry (corresponding to the exponent of beta) is one
 
  good_rows = 0

  for i in 1:nrows(B)
    if !is_unit(B[i, ncols(B)])
      continue
    end
    good_rows += 1
    c = inv(B[i, ncols(B)])
    #multiply_row!(B, i, c)
    for j in 1:ncols(B)
      B[i, j] = B[i, j] * c
    end
  end

  BB = Hecke.lift_unsigned(B)

  @assert good_rows == 1 || good_rows == 0

  @vprint :NormRelation 1 "There are $(good_rows) many candidates\n"
  for i in 1:nrows(BB)
    if BB[i, ncols(BB)] != 1
      continue
    end
    @vprint :NormRelation 1 "trager = $(trager)\n"
    candidate = prod([units[j]^Int(BB[i, j]) for j in 1:ncols(B) - 1])*beta
    if !(write isa Bool)
      save_factored_element(candidate, write)
    end
    if decom == false
      @vtime :NormRelation 1 b, r = is_power(candidate, d, trager = trager)
    else
      @vtime :NormRelation 1 b, r = is_power(candidate, d, trager = trager, decom = decom.fac)
    end
    if b return (b, r) end
  end

  return _ispower_mod_units_generic(units,
                                    beta,
                                    d,
                                    stable = 10 * stable, trager = trager,
                                    write = write,
                                    strategy = strategy)
end


function _ispower_mod_units_bad(units::Vector{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}},
                                beta::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}, d::Int;
                                stable = 10, trager = true,
                                write = false, decom = decom, strategy = :classic)
  # This is the bad case
  e = clog(ZZRingElem(d), 2)
  @assert 2^e == d
  @vprint :NormRelation 1 "Have to saturate and compute $e square roots\n"
  # We first saturate the units.
  # Use the saturate function of Hecke
  O = lll(maximal_order(base_ring(beta)))
  U = Hecke.UnitGrpCtx{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}(O)
  add_again = eltype(units)[]

  for u in units
    # This assumes that the units are not torsion
    has_full_rk = Hecke.has_full_rank(U) 
    @vtime :NormRelation 2 ff = Hecke.add_unit!(U, u)
    if !has_full_rk && !ff
      push!(add_again, u)
    end
    @vtime :NormRelation 2 U.units = Hecke.reduce(U.units, U.tors_prec)
  end

  for uu in add_again
    Hecke.add_unit!(U, uu)
  end
  U.units = Hecke.reduce(U.units, U.tors_prec)

  cur_reg = Hecke.tentative_regulator(U)

  # initialize a dummy class group context
  c = Hecke.class_group_init(O, 1, complete = false, use_aut = true)::Hecke.ClassGrpCtx{SMat{ZZRingElem}}

  fl = _saturate!(c, U, 2)

  new_reg = Hecke.tentative_regulator(U)

  @vprint :NormRelation 1 "Regulator improved by $(cur_reg/new_reg)\n"

  while fl
    cur_reg = new_reg
    fl = _saturate!(c, U, 2)
    new_reg = Hecke.tentative_regulator(U)
    @vprint :NormRelation 1 "Regulator improved by $(cur_reg/new_reg)\n"
  end

  @vprint :NormRelation 1 "Regulator is $new_reg\n"

  fl = _saturate!(c, U, 2)

  @vprint :NormRelation 1 "Regulator is $(Hecke.tentative_regulator(U))\n"

  @vtime :NormRelation 1 A = saturate_exp(U.units, 2, stable = stable, strategy = strategy)
  @assert nrows(A) == 0

  # Now U.units is (hopefully) saturated

  units = U.units

  push!(units, FacElem(Hecke._torsion_units_gen(base_ring(beta))[2]))

  for i in 1:e
    @vprint :NormRelation 1 "Determining square root for step $i/$e\n"
    fl, _beta = _ispower_mod_units_prime(units, beta, 2; stable = stable,
                                                         trager = trager,
                                                         write = write,
                                                         decom = decom,
                                                         strategy = strategy)
    if !fl
      return false, FacElem(zero(nf(O)))
    else
      beta = _beta
    end
  end
  return fl, beta
end

# given factored element beta and integer d, seach for a unit u such that u*beta is a dth power
function ispower_mod_units(units::Vector{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}},
                           beta::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}, d::Int;
                           stable = 10, trager = true,
                           write = false, decom = false, strategy = :classic)
  @assert Hecke.is_prime_power(d)
  if is_prime(d)
    b, r = _ispower_mod_units_prime(units, beta, Int(d), stable = stable,
                                                         trager = trager,
                                                         decom = decom,
                                                         write = write,
                                                         strategy = strategy)
  else
    e, p = Hecke.is_power(d)
    if !has_grunwald_wang_obstruction(base_ring(beta), p, d)
      b, r = _ispower_mod_units_generic(units, beta, Int(d), stable = stable,
                                                             trager = trager,
                                                             write = write,
                                                             decom = decom,
                                                             strategy = strategy)
    else
      @vprint :NormRelation 1 "Grunwald-Wang obstruction!\n"
      # We first do the cheap test 
      b, r = _ispower_mod_units_generic(units, beta, Int(d), stable = stable,
                                                             trager = trager,
                                                             write = write,
                                                             decom = decom,
                                                             strategy = strategy)

      if b
        return b, r
      end
      # Now do the thing with saturation
      b, r = _ispower_mod_units_bad(units, beta, Int(d), stable = stable,
                                                         trager = trager,
                                                         write = write,
                                                         decom = decom,
                                                         strategy = strategy)
    end
  end
  if b
    #@assert abs(norm(r)^d) == abs(norm(beta))
  end
  return b, r
end

function ispower_mod_units(N::NormRelation,
                           beta::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}, d::Int;
                           stable = 10, redo = false, trager = true,
                           write = false,
                           additional_units::Vector{AbsSimpleNumFieldElem} = AbsSimpleNumFieldElem[],
                           decom = false,
                           strategy = :classic)
  @vprint :NormRelation 1 "Calling ispower_mod_units with d = $d and field of degree $(degree(base_ring(beta)))\n"
  # @show beta
  K = base_ring(beta)
  @assert field(N) == K

  #utx = Hecke.UnitGrpCtx{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}(OK)
  #U = compute_unit_group_using_norm_relation(OK, N; saturate = true)
  #units = U.units
  units = FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}[]
  for i in 1:length(N)
    L, mL = subfield(N, i)
    @vprint :NormRelation 1 "Computing unit group classically in subfield\n$(L)\n"
    oL = lll(maximal_order(L))
    @vtime :NormRelation 1 _ = class_group(oL, use_aut = true, redo=redo)
    @vtime :NormRelation 1 U, mU = unit_group_fac_elem(oL, redo=redo)
    #    for j in 2:ngens(U)
    #      Hecke._add_unit(utx, mL(mU(U[j])))
    #    end
    
    # changed to 2:ngens to avoid torsion units of subfields (avoid repetition?)
    @vtime :NormRelation 1 append!(units, (Hecke.NormRel.embedding(N, i)(mU(U[j])) for j in 2:ngens(U)))
    # @show units
  end
  ##units = utx.units
  #(Hecke._torsion_units_gen(K)
  push!(units, FacElem(Hecke._torsion_units_gen(K)[2]))

  for u in additional_units
    push!(units, FacElem(u))
  end

  @vtime :NormRelation 1 b, r = ispower_mod_units(units, beta, d, stable = stable,
                                                                  trager = trager,
                                                                  write = write,
                                                                  decom = decom,
                                                                  strategy = strategy)
  # This should not be necessary anymore
  #if !b # try a little harder
  #  if !(write isa Bool)
  #    write = string(write, "_bla_")
  #  end
  #  @vtime :NormRelation 1 b, r = ispower_mod_units(units, beta, d, 
  #    stable = degree(K) * stable, trager=trager, write = write)
  #  return b, r
  #else
  return b, r
  #end
end

# given factored element beta and integer d, seach for a unit u such that u*beta is a dth power
#
# mode = 0 => use subfields via norm relations
# mode = 1 => use units of parent field
# mode = 2 => use s-units
function ispower_mod_units(beta::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}, d::Int;
                           stable = 10, mode = 0, free = false, redo = false,
                           min_degree::Int = 1, trager = true)
    K = base_ring(beta)
    @vprint :NormRelation 1 "Calling ispower_mod_units with d = $d and field of degree $(degree(K)), mode = $mode\n"

    if mode == 0
        N = NormRel.norm_relation(K)
        return ispower_mod_units(N, beta, d, stable=stable, redo=redo, trager=trager)
    elseif mode == 1
        U, mU = unit_group_fac_elem(maximal_order(K))
        units = FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}[mU(U[i]) for i in 1:ngens(U)]
        return ispower_mod_units(units, beta, d, stable=stable, redo=redo, trager=trager)
    else
        # old approach with s-units
        # We should use S = Hecke.support(I), but the sunit group computation wants at the moment
        # a Galois closed set.
        OK = lll(maximal_order(K))
        I = ideal(OK, beta)
        N = NormRel.norm_relation(K)

        S = Hecke.ideal_type(OK)[]
        nr = FlintZZ(Hecke.norm(I))
        nrf = factor(nr)
        for (p, _) in nrf
            lp = prime_decomposition(OK, p)
            for (P, _) in lp
                push!(S, P)
            end
        end

        #A, mA = Hecke.sunit_mod_units_group_fac_elem(S)
        #@vprint :NormRelation 1 "S-units of the field $(nf(order(I)))\n"
        A, mA = _sunit_group_fac_elem_mod_units_quo_via_brauer(N, S, 0, true)
        exps = mA \ beta

        new_exps = ZZRingElem[]
        for i in 1:length(S)
            b, q = divides(Int(exps[i]), d)
            if !b return (b, beta) end

            append!(new_exps, q)
        end

        a = mA(A(new_exps)) # set a = dth-root as factored element
        return (true, a)
    end
end
