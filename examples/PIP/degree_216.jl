# Examples for computing norm relations and recursively solving the PIP.

using NormRelations

#####################################################################
#
# degree 216, 
# class group (Z/3)^5 x (Z/6)^4 x (Z/18)^3 x Z/24966 x Z/25709664933530084052 
# norm relation denominator 1
# classic PIP in degree <= 18, saturation/roots in degree 72
# 
# Norm Relation: ~50 sec
# PIP: ~3.6 hours
#
#####################################################################

K, a = CyclotomicField(399, "a")
OK = lll(maximal_order(K))

g = -a^211 - a^210 + a^209 + a^207 + a^206 - a^205 - a^204 + a^203 - a^201 + a^200 - a^199 + a^198 - a^197 + a^195 - a^194 - a^193 + a^191 - a^190 - a^188 - a^187 + a^186 + a^185 + a^184 + a^182 + a^179 - a^178 - a^177 + a^176 - a^174 - a^172 - a^171 + a^169 + a^168 + a^167 + a^166 - a^165 + a^164 - a^162 + a^161 - a^160 - a^158 - a^156 - a^151 - a^150 + a^149 - a^148 + a^147 - a^146 + a^145 + a^144 - a^143 - a^141 - a^140 - a^138 - a^137 + a^136 + a^135 + a^134 + a^132 - a^131 + a^130 + a^128 - a^127 + a^126 - a^124 + a^123 + a^122 - a^121 + a^118 - a^116 + a^115 + a^113 - a^112 + a^110 + a^108 + a^107 + a^106 - a^105 + a^103 - a^102 + a^101 + a^100 + a^99 - a^98 + a^97 - a^95 + a^91 + a^89 - a^87 + a^86 - a^85 - a^82 - a^81 - a^80 + a^77 + a^75 + a^72 - a^71 + a^69 + a^68 + a^65 - a^64 + a^62 + a^60 + a^59 - a^55 - a^54 + a^51 + a^49 - a^47 - a^46 - a^45 + a^44 + a^42 - a^41 + a^39 - a^38 + a^37 - a^36 + a^35 + a^34 - a^33 - a^31 - a^29 + a^28 - a^26 - a^25 - a^24 - a^23 - a^22 + a^19 - a^17 + a^16 + a^14 - a^13 - a^11 - a^8 - a^7 - a^5 + a^3 + a^2 + 1
I = ideal(OK, OK(g))

println("K = Cyclotomic field of conductor 399, degree 216.")
println("Classic PIP done in subfields of degree <= 18, root computation in degree <= 72.")
println("Computing norm relation:")
@time _, N = abelian_norm_relation(K);
println("\nComputing generator:")
@time b, h = isprincipal(I, N);
if b
  println("Success!")
else
  println("Something went wrong.")
end
