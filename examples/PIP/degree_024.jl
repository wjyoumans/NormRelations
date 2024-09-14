# Examples for computing norm relations and recursively solving the PIP.

using NormRelations

#####################################################################
#
# degree 24, class group Z/2, norm relation denominator 4
# classic PIP in degree <= 6, saturation/roots in K
#
# Norm Relation: ~0.5 sec
# PIP: ~0.8 sec
#
#####################################################################

K, a = cyclotomic_field(56, "a")
OK = lll(maximal_order(K))
g = 2*a^22 + 2*a^20 + 2*a^18 + a^17 - a^16 + 2*a^15 + a^14 + 2*a^13 + a^11 - 2*a^10 + a^9 - a^8 + 2*a^6 - 2*a^5 + 2*a^4 + 2*a^3 - a - 2
I = ideal(OK, OK(g))

println("K = cyclotomic field of conductor 56, degree 24.")
println("Classic PIP done in subfields of degree <= 6, root computation in K.")
println("Computing norm relation:")
@time _, N = abelian_norm_relation(K);
println("\nComputing generator:")
@time b, h = isprincipal(I, N);
if b
  println("Success!")
else
  println("Something went wrong.")
end
