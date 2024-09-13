
# Find short generator of gOK corresponding to a mildly short vector of the ideal
# lattice.
# If precision = 0 try to use low precision.
# If precision = -1 use enough to gaurauntee short generator.
# Otherwise set precision manually.
function short_associate(g::FacElem{AbsSimpleNumFieldElem,AbsSimpleNumField}; precision=0)
  K = base_ring(g)
  b, m = Hecke.is_cyclotomic_type(K)
  @assert b
  d = degree(K)

  # figure precision
  if precision == 0
  # small amount that usually works ok
    precision = 20 + m
  elseif precision == -1
  # use ~m^2 bits of prec per section 6.5.2 of [1] to gauranteee short element
    n = 0
    for k in keys(g.fac)
      n = max(n, round(g.fac[k]*ceil(maximum(map(x->abs(x),coeffs(k))))))
    end
    precision = Int64(ceil(log(2, Int64(n)) + m^2))
  end
  @vprint :IdealSVP 1 "Using $precision bits of precision.\n"
  A = ArbField(precision)
  
  # compute short cyclotomic units and log embeddings
  @vtime :IdealSVP 1 t = log_embedding(g, A)
  @vtime :IdealSVP 1 U = short_cyclotomic_units(K)
  @vtime :IdealSVP 1 W = log_embedding_lattice(U, A)
  @vtime :IdealSVP 1 _, x = close_vector(W, t)

  # recover short generator
  u = FacElem(K(1))
  for i in 1:ncols(W)
    mul!(u, u, U[i]^-x[i])
  end

  return g*u
end

# Find a mildly short vector of A assuming A is principal.
function principal_ideal_svp(
    A::AbsSimpleNumFieldOrderIdeal;
    cache::NormRelCache = NormRelCache())

  if has_norm_relation(cache)
    @vtime :IdealSVP 1 b, a = search_pip(A, cache=cache)
  else
    @vtime :IdealSVP 1 b, a = Hecke.isprincipal_fac_elem(A)
  end
  if !b
    return b, a
  end

  @vtime :IdealSVP 1 c = short_associate(a)
  return b, c
end

# Find a mildly short vector of an arbitrary ideal A.
function ideal_svp(
    A::AbsSimpleNumFieldOrderIdeal,
    S::Vector{AbsSimpleNumFieldOrderIdeal},
    B::Int,
    d::Int;
    parisizemax=PARISIZEMAX,
    stable=STABLE,
    strategy=:classic,
    minus_part=class_group_minus_part(nf(A), parisizemax=parisizemax, stable=stable, 
				      strategy=strategy))

  _, _, cache_K, _ = minus_part
  @vtime :IdealSVP 1 C = close_principal_multiple(A, S, B, d, parisizemax=parisizemax,
						 stable=stable, strategy=strategy,
						 minus_part=minus_part)
  num, den = integral_split(evaluate(A*C))
  @assert isone(den)

  @vtime :IdealSVP 1 b, a = principal_ideal_svp(num, cache=cache_K)
  return b, a
end

# Find a mildly short vector of an arbitrary ideal A.
function ideal_svp(
    A::AbsSimpleNumFieldOrderIdeal; 
    parisizemax=PARISIZEMAX,
    stable=STABLE,
    strategy=:classic,
    minus_part=class_group_minus_part(nf(A), parisizemax=parisizemax, stable=stable, 
				      strategy=strategy))

    @vtime :IdealSVP 1 S, B, d = minus_part_generating_set(order(A), 
					parisizemax=parisizemax, stable=stable,
					strategy=strategy, minus_part=minus_part)

    @vtime :IdealSVP 1 b, a = ideal_svp(A, S, B, d, parisizemax=parisizemax, 
					stable=stable, strategy=strategy, 
					minus_part=minus_part)
    return b, a
end
