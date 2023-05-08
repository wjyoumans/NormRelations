
set_verbose_level(:NormRelCache, 1)
set_verbose_level(:Decompose, 1)
set_verbose_level(:Pari, 1)
set_verbose_level(:PIP, 2)


function cache_setup(m; s=[])
  K, a = CyclotomicField(m)
  OK = lll(maximal_order(K))

  if isempty(s)
    s = [2, 11, 23, 43, 89, 109, 131, 91139404621]
  end

  S = prime_ideals_over(OK, s);
  b, N = abelian_norm_relation(K);
  return norm_relation_cache(S, N)
end

function rand_test_ideal(cache; n=3)
  return prod(rand(idealset(cache)) for i=1:n)
end

function test_decisional_pip(m=39, n=10, cache=nothing)
  if isnothing(cache)
    @info "Setting up cache"
    cache = cache_setup(m)
  end
  S = idealset(cache)

  @info "Drawing $n random ideals and testing principality."
  for i=1:n
    @info "i = $i"
    A = rand_test_ideal(cache)
    @info "Using Hecke:"
    @time b, _ = isprincipal(A)
    @info "Using decisional PIP with norm relations:"
    @time bb = decisional_pip(A, cache=cache)
    @assert b == bb
  end
  return cache
end
