
set_verbose_level(:NormRelCache, 1)
set_verbose_level(:Decompose, 1)
set_verbose_level(:MinusPart, 2)
set_verbose_level(:Pari, 1)


# Note: all fields in database with h+ != 1 have a norm relation
# 12: Norm relation, h = 1
# 13: No norm relation, h = 1
# 23: No norm relation, h = h- = 3
# 39: Norm relation, h = h- = 2
# 63: Den 1 norm relation, h = h- = 7
#
# Interesting cases but Grunwald-Wang obstruction so will be hard
# 136: (degree 64) Norm relation, h+ = 2
# 504: (degree 144) Den 1 norm relation, h+ = 4
function test_minus_part(conductors=[])
  if isempty(conductors)
    conductors = [12, 13, 23, 39, 63]
    orders = [1, 1, 3, 2, 7]
  end

  for i in 1:length(conductors)
    m = conductors[i]
    @info "Conductor = $m"
    K, a = CyclotomicField(m)

    @info "Minus part: "
    @time ker, kermap, c1, c2 = class_group_minus_part(K)
    @info "Result: $(elementary_divisors(ker))"
    
    @assert order(ker) == orders[i]
  end
end

function test_generating_set(conductors=[])
  if isempty(conductors)
    conductors = [12, 13, 23, 39, 63]
  end
  for m in conductors
    @info "Conductor = $m"
    K, _ = CyclotomicField(m)
    
    @info "Minus part:"
    @time ker, kermap, c1, c2 = class_group_minus_part(K)
    @info "Result: $(elementary_divisors(ker))"

    @info "Generating set:"
    @time S, B, d = minus_part_generating_set(K, minus_part=(ker, kermap, c1, c2))

    lp = sort!(collect(Set(minimum(P) for P = S)))
    @info "Result: $(length(S)) prime ideals above $lp, B = $B, d = $d"

    # assert not needed since minus_part_generating_set assures the entire minus
    # part is generated, which is tested in test_minus_part
  end
end

function test_random_walk(conductors=[], iterations=10)
  if isempty(conductors)
    conductors = [12, 13, 23, 39, 63]
  end
 
  #assert A*B in Cl_K^- i.e. N_{K/K^+}(A*B) principal
  for m in conductors
    @info "Conductor = $m"
    K, _ = CyclotomicField(m)
    
    @info "Minus part:"
    @time ker, kermap, c1, c2 = class_group_minus_part(K)
    OK = order(c1)

    @info "Generating set:"
    @time _, b, d = minus_part_generating_set(K, minus_part=(ker, kermap, c1, c2))
    S = prime_ideals_up_to(OK, 1000)

    @info "Doing random walk:"
    for i=1:iterations
      @info "iteration = $i"
      T = [rand(S) for j=1:3]
      A = prod(T)
      lp = sort!(collect(Set(minimum(P) for P in T)))
      @info "Ideal is above rational primes $lp"

      @info "Random walk:"
      @time B = walk_to_minus_part(A, b, d, cache=c2)

      # No need to assert, its required for walk_to_minus_part to terminate
      #@assert decisional_pip(norm(embedding(c2), A*B, order=order(c2)), cache=c2)
    end
  end
end

function test_prime_ideal_cpm(conductors=[], norm_bound=1000, iterations=10)
  if isempty(conductors)
    conductors = [12, 13, 23, 39, 63]
  end
  
  for m in conductors
    @info "Conductor = $m"
    K, _ = CyclotomicField(m)
    n = degree(K)

    @info "Setting up cache:"
    @time cache_K, cache_Kp = AbNfTools._class_group_minus_part_setup(K)

    OK = order(cache_K)
    @info "Getting prime ideals for test:"
    @time S = minus_part_prime_ideals_up_to(OK, norm_bound, cache=cache_Kp)

    @info "Doing CPM:"
    for i=1:iterations
      @info "iteration = $i"
      P = rand(S)
      alpha = matrix(ZZ, n, 1, rand(0:10, n))

      @info "CPM:"
      @time B = close_principal_multiple(P, alpha)
      
      @info "Apply stickelberger:"
      @time A = apply_stickelberger(P, alpha)

      @assert decisional_pip(A*B, cache=cache_K)
    end
  end
end

# TODO
function test_cpm(conductors=[])
  if isempty(conductors)
    conductors = [12, 13, 23, 39, 63]
  end
  
  for m in conductors
    @info "Conductor = $m"
    K, _ = CyclotomicField(m)
    OK = lll(maximal_order(K))

    minus_part = class_group_minus_part(K)
    ker, kermap, c1, c2 = minus_part
    
    # Construct an non-principal ideal A.
    S = prime_ideals_up_to(OK, 1000)
    A = prod(rand(S) for i=1:5)

    B = close_principal_multiple(A, minus_part=minus_part)
    @assert decisional_pip(A*B, cache=c1)

  end
end
