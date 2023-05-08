
import Hecke: is_principal

add_verbose_scope(:PIP)
add_assert_scope(:PIP)

include("PIP/DecisionalPIP.jl")
include("PIP/SearchPIP.jl")

export decisional_pip, search_pip
