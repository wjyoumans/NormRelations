# Examples for computing norm relations and recursively solving the PIP.

using NormRelations

#####################################################################
#
# degree 144, class group (Z/3)^2 x Z/117 x Z/468 x Z/102960 x Z/130450320, 
# norm relation denominator 1
# classic PIP in degree <= 12, saturation/roots in degree <= 48
# 
# Norm Relation: ~1.7 min
# PIP: ~31.7 min
#
#####################################################################

K, a = CyclotomicField(468, "a")
OK = lll(maximal_order(K))

g = -a^143 - a^142 - a^141 - a^139 - a^137 - a^136 - a^135 + a^134 + a^133 + a^132 - a^131 - a^129 + a^128 + a^125 - a^124 + a^123 - a^122 + a^121 - a^120 - a^119 - a^117 - a^116 + a^115 + a^114 - a^111 - a^110 + a^109 - a^108 + a^107 + a^106 - a^104 - a^103 - a^101 - a^100 + a^99 - a^96 - a^95 - a^92 - a^91 + a^90 + a^89 - a^88 + a^87 + a^86 - a^85 + a^84 - a^83 + a^82 + a^81 + a^79 - a^78 + a^76 - a^75 + a^73 + a^72 + a^70 + a^68 - a^67 + a^66 + a^64 - a^62 + a^61 + a^59 + a^57 + a^56 - a^55 - a^54 + a^53 + a^52 - a^51 + a^50 - a^49 - a^48 - a^47 + a^46 - a^45 - a^44 + a^43 + a^41 + a^40 - a^38 - a^37 - a^35 - a^33 - a^31 - a^29 + a^27 - a^24 + a^22 - a^20 + a^19 + a^18 + a^15 + a^14 + a^13 + a^12 - a^11 - a^10 + a^6 - a^5 + a^4 + a^3 - a^2 + a + 1
I = ideal(OK, OK(g))

println("K = Cyclotomic field of conductor 468, degree 144.")
println("Classic PIP done in subfields of degree <= 12, root computation in degree <= 48.")
println("Computing norm relation:")
@time _, N = abelian_norm_relation(K);
println("\nComputing generator:")
@time b, h = isprincipal(I, N);
if b
  println("Success!")
else
  println("Something went wrong.")
end
