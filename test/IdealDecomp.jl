
set_verbose_level(:NormRelCache, 2)
set_verbose_level(:Decompose, 3)

function cache_setup(m; s=[])
  K, a = cyclotomic_field(m)
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

function test_decompose(m=39, n=10, cache=nothing)
  if isnothing(cache)
    println("Setting up cache")
    cache = cache_setup(m)
  end
  S = idealset(cache)

  println("Doing $n random ideal decompositions")
  for i=1:n
    println(">>> i = $i")
    A = rand_test_ideal(cache)
    @time a, v = decompose(A, S, cache)
    println("Checking result.")

    println()
  end
  return cache
end
