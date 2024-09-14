
@testset "Abelian.jl" begin
  @info "Abelian.jl"
  K, a = cyclotomic_field(12, "a", cached=false)
  A, mA = automorphism_group(K)
  G, AtoG, GtoA = Hecke.find_isomorphism_with_abelian_group(collect(A), *)
  H, mH = sub(G, [G[1]])

  t = basiszahl(K)
  @test t == a^2 + a

  for aut in A
    L1, _ = fixed_field(K, mA(aut))

    H, mH = sub(G, [AtoG[aut]])
    L2, _ = fixed_field_abelian(K, mA, GtoA, mH)
    @test is_isomorphic(L1, L2)
    
    #L2, _ = fixed_field_abelian(K, mH)
    #@test is_isomorphic(L1, L2)
  end
end
