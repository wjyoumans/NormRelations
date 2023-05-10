module NormRelations

using Reexport
@reexport using Hecke

import Hecke: MapSUnitGrpFacElem, sunit_group_fac_elem

# TODO: Make pari optional?

# default 4gb for pari
PARISIZEMAX = 4000000000

# PARISIZEMAX can be set with NORMREL_PARISIZEMAX environment variable.
if "NORMREL_PARISIZEMAX" in keys(ENV)
  PARISIZEMAX = parse(Int, ENV["NORMREL_PARISIZEMAX"])
  @info "Using new parisizemax: $(PARISIZEMAX)."
else
  @info "Using default parisizemax: $(PARISIZEMAX)."
end

STABLE = 10
ABELIANBNFPATH = string(@__DIR__, "/Pari/abelianbnf/abelianbnf.gp")

include("Util.jl")
include("NormRelation.jl")
include("IdealDecomp.jl")
include("IdealSVP.jl")
include("MinusPart.jl")
include("PIP.jl")
include("Root.jl")
include("Saturate.jl")
include("SUnits.jl")

Base.:*(A::arb_mat, B::fmpz_mat) = A*matrix(base_ring(A), collect(B))
Base.:*(A::fmpz_mat, B::arb_mat) = matrix(base_ring(B), collect(A))*B

# Add additional verbose scopes. Must be initialized at runtime.
function __init__()
  scopes = [
    :Abelian,
    :CVP,
    :CyclotomicUnits,
    :IdealDecomp, 
    :IdealSVP,
    :LogEmbedding,
    :MinusPart,
    :NormRelCache, 
    :Pari,
    :PIP,
    :Root,
    :Saturate,
    :SUnits
  ]

  for s in scopes
    add_verbose_scope(s)
    add_assert_scope(s)
  end
end


#TODO: 
#  Abelian 
#    make sure all works still
#    automorphism_group_abelian? are we using this?


# separate NormRelCache + MinusPartCtx
#
# Abelian utils
#   fixed fields
# Cyclotomic
#   cyc units
#   stickelberger
#   minus part
#   ideal svp
# Norm relations
#  norm rel cache
# Units (?)
# SUnits
#   recursive
# Lattice
#   CVP
#   SVP
#   Gram Schmidt
# PIP
#   decisional
#   search
# IdealSVP
#   log embeddings
#   (principal) ideal svp (check cyclotomic)
# IdealDecomposition
#   utils
#   decomposition
# Saturation (work with units + sunits)
#   utils
#   saturation (+fixed)
# Roots
# Compact Rep

end
