
using NormRelations

#####################################################################
#
# degree 72, classic PIP in degree <= 6, saturation/roots in degree <= 24
#
# Norm Relation: ~4 sec
# PIP: ~1.6 min
#
#####################################################################

K, a = CyclotomicField(252, "a")
OK = lll(maximal_order(K))

g = a^71 + a^68 - a^67 + a^66 - a^65 - a^63 + a^62 - a^61 - a^60 - a^58 - a^57 - a^56 - a^55 + a^54 - a^53 - a^52 - a^48 + a^47 + a^46 - a^44 + a^40 + a^38 - a^35 + a^34 - a^33 - a^31 - a^30 - a^29 - a^28 + a^26 + a^25 - a^23 - a^22 + a^21 + a^18 - a^16 + a^12 + a^7 - a^6 - a^5 + a^3 - a
I = ideal(OK, OK(g))

println("K = Cyclotomic field of conductor 252, degree 72.")
println("Using S-unit approach.")
println("Computing norm relation:")
@time _, N = abelian_norm_relation(K);
println("Computing generator:")
@time b, h = isprincipal_sunit(I, N);
if b
  println("Success!")
else
  println("Something went wrong.")
end
