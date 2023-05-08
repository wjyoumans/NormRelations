

function test_ideal_svp(conductors=[], iterations=10, bound=1000)
  if isempty(conductors)
    conductors = [12, 13, 23, 39, 63]
  end

  for i in 1:length(conductors)
    m = conductors[i]
    @info "Conductor = $m"
    K, a = CyclotomicField(m)
    OK = lll(maximal_order(K))

    @info "Computing minus part: "
    @time minus_part = class_group_minus_part(K)
    
    @info "Computing generating set:"
    @time S0, B, d = minus_part_generating_set(K, minus_part=minus_part)

    S = prime_ideals_up_to(OK, bound)
    @info "Solving $iterations random instances of ideal svp:"
    for i=1:iterations
      @info "iteration = $i"
      A = prod(rand(S) for j=1:3)
      @time b, a = ideal_svp(A, S0, B, d, minus_part=minus_part)
      @assert b
      @assert a in A
    end 
  end
end
