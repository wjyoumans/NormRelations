# Collection of lattice algorithms - gram-schmidt, LLL, CVP (Babai nearest-plane and round-off)

function l1_norm(L)
  maximum([sum([abs(x) for x in L[:,i]]) for i in 1:ncols(L)])
end

function l2_norm(B::ArbMatrix)
  @assert ncols(B) == 1
  return sqrt(dot(B, B))
end

function inf_norm(L)
  maximum([sum([abs(x) for x in L[i,:]]) for i in 1:nrows(L)])
end

function frobenius_norm(L)
  n = 0
  for x in L
    n += abs(x)^2
  end
  return sqrt(n)
end

function Base.adjoint(L::FakeFmpqMat)
  return transpose(L)
end

function insert_col(M, col, i)
  return hcat(M[:,1:i-1], col, M[:,i:end])
end

function delete_col(M, i)
  m = ncols(M)
  if m <= 1
    return zero_matrix(base_ring(M), 0, 0)
  elseif i == 1
    return M[:,2:end]
  elseif i == m
    return M[:,1:end-1]
  else
    return hcat(M[:,1:i-1], M[:,i+1:end])
  end
end

# Find the minimum working precision of the elements of an ArbMatrix
function working_precision(A::ArbMatrix)
  return Int(minimum([log2(denominator(Hecke._arb_get_fmpq(x))) for x in A if !iszero(x)]))
end

function arb_mat_to_fmpz_mat(A::ArbMatrix; prec::Int=precision(parent(A[1,1])))
  scale = ZZRingElem(2)^prec
  return map(x -> numerator(Hecke._arb_get_fmpq(x)*scale), A), prec
end

function fmpz_mat_to_arb_mat(B::ZZMatrix, prec::Int; scale=false)
  A = ArbField(prec)
  if scale
    s = ZZRingElem(2)^prec
    return map(x -> A(x)//s, B)
  end
  return map(x -> A(x), B)
end

function save_fmpz_mat(B::ZZMatrix, filename)
  open(filename, "w") do io
    write(io, "[")
    for i in 1:nrows(B)
      write(io, "$(B[i,:])\n")
    end
    write(io, "]")
  end
end

function load_fmpz_mat(nrows, ncols, filename)
  B = zero_matrix(ZZ, nrows, ncols)
  i = 0
  open(filename, "r") do io
    while !eof(io)
      row = split(replace(readline(io), ['[', ']'] => ""))
      if length(row) != ncols
        break
      end
      i += 1
      B[i,:] = map(x->ZZRingElem(String(x)), row)
    end
  end
  @assert(i == nrows)
  return B
end

function angle(v1, v2)
  return acos(dot(v1, v2)/(l2_norm(v1)*l2_norm(v2)))
end

function angles(L)
  ang = []
  mn = 2*pi
  mx = 0
  for i in 1:ncols(L)
    for j in i:ncols(L)
      push!(ang, acos(dot(L[:,i], L[:,j])/(l2_norm(L[:,i])*l2_norm(L[:,j]))))
      if ang[end] < mn
        mn = ang[end]
      end
      if ang[end] > mx
        mx = ang[end]
      end
    end
  end
  return ang, mn, mx
end

# columns of L independent, test if v is dependent or not
function isindependent(L, v)

  A = hcat(L, v)
  d = det(transpose(A)*A)
  if isfinite(d) && ispositive(d)
    return true
  else
    return false
  end
end

########################################################################
# Properties
########################################################################

# gaussian heuristic (expected first minimum) of matrix B whose columns are basis vectors for 
# a lattice L
function gaussian_heuristic(B::ArbMatrix, v=volume(B)) 
  A = parent(B[1,1])
  n = ncols(B)
  return sqrt(n/(2*A(pi)*A(exp(1))))*(v^(1/n))
end

# root hermite factor of matrix B whose columns are basis vectors for a lattice L
function root_hermite_factor(B, v=volume(B))
  n = ncols(B)
  return (sqrt(dot(B[:,1], B[:,1])*1.0)/v^(1/n))^(1/n)
end

# orthogonality defect of matrix B whose columns are basis vectors for a lattice L
# NOTE: fails to converge in dimension 68x69 (log s-unit lattice of cyclotomic field with
# conductor 47 and S containing all conjugates of the first split prime, 283) even with 
# precision up to 1200.
function orthogonality_defect(B, v=volume(B))
  return prod([l2_norm(B[:,i]) for i = 1:ncols(B)])/v
end

# log of the orthogonality defect of matrix B whose columns are basis vectors for a lattice L
function log_orthogonality_defect(B, v=volume(B))
  return sum([log(l2_norm(B[:,i])) for i = 1:ncols(B)]) - log(v)
end

# volume of the lattice spanned by columns of B
function Hecke.volume(B::ZZMatrix)
  if issquare(B)
    return abs(det(B))*1.0
  end
  return sqrt(abs(det(transpose(B)*B))*1.0)
end

# volume of the lattice spanned by columns of B
function Hecke.volume(B::ArbMatrix)
  if issquare(B)
    return abs(det(B))
  end
  return sqrt(abs(det(transpose(B)*B)))
end

function is_lll_reduced(B::ArbMatrix; delta::ArbFieldElem=parent(B[1,1])(0.99), eta::ArbFieldElem=parent(B[1,1])(0.51))
  A = parent(B[1,1])
  d = ncols(B)

  G = gram_schmidt(B)
  mu = zero_matrix(A, d, d)
  r = [dot(G[:,i], G[:,i]) for i = 1:d]

  # size-reduced
  for j = 1:d-1
    for i = j+1:d
      mu[i,j] = dot(B[:,i], G[:,j]) // r[j]
      if mu[i,j] > eta
        return false
      end
    end
  end

  # Lovasz condition
  for k = 2:d
    if delta * r[k-1] > r[k] + mu[k,k-1]^2 * r[k-1]
      return false
    end
  end

  return true
end

# Columns of B form basis. Assumes full rank (so we dont check pairwise)
function isorthogonal(B)
  if ncols(B) == 1
    return true
  end
  for i in 1:ncols(B)-1
    if !contains(dot(B[:,i], B[:,i+1]), 0)
      return false
    end
  end
  if !contains(dot(B[:,end], B[:,1]), 0)
    return false
  end
  return true
end

# Columns of B form basis. Assumes full rank (so we dont check pairwise)
function isorthonormal(B)
  if ncols(B) == 1 && contains(dot(B[:,1], B[:,1]), 0)
    return true
  end
  for i in 1:ncols(B)-1
    if !contains(dot(B[:,i], B[:,i]), 1)
      return false
    elseif !contains(dot(B[:,i], B[:,i+1]), 0)
      return false
    end
  end
  if !contains(dot(B[:,end], B[:,end]), 1)
    return false
  end
  if !contains(dot(B[:,end], B[:,1]), 0)
    return false
  end
  return true
end



########################################################################
# LLL/BKZ/HKZ/SVP
########################################################################

# rows are basis vectors!

function fplll_preprocess(B::ZZMatrix)
  out = ["["]
  for i=1:nrows(B)
    push!(out, string(B[i,:]))
  end
  push!(out, "]")
  return join(out)
end

#= why is this slower when it doesnt use files?
function test_fplll(B::ZZMatrix; filename="fplll", eta=0.51, delta=0.99)
  input = fplll_preprocess(B)
  io = IOBuffer()

  open(`fplll -a lll -e $(eta) -d $(delta)`, io, write = true) do ioo
    println(ioo, input)
  end
  out = String(take!(io))
  return out
end
=#

function fplll(B::ZZMatrix; filename="fplll", eta=0.51, delta=0.99)
  save_fmpz_mat(B, "$(filename).in")
  @vprint :NormRelation 1 "Calling fplll.\n"
  @vtime :NormRelation 1 run(
        pipeline(`fplll -a lll -e $(eta) -d $(delta) $(filename).in`, stdout="$(filename).out"))
  B = load_fmpz_mat(nrows(B), ncols(B), "$(filename).out")
  return B
end

function fplll(A::ArbMatrix; filename="fplll", eta=0.51, delta=0.99)
  B, prec = arb_mat_to_fmpz_mat(A)
  B = fplll(B, filename=filename, eta=eta, delta=delta)
  return fmpz_mat_to_arb_mat(B, prec, scale=true)
end

function svp(B::ZZMatrix; filename="fplll")
  save_fmpz_mat(B, "$(filename).in")
  @vprint :NormRelation 1 "Calling fplll.\n"
  @vtime :NormRelation 1 run(
        pipeline(`fplll -a svp $(filename).in`, stdout="$(filename).out"))
  B = load_fmpz_mat(1, ncols(B), "$(filename).out")
  return B
end

function cvp(B::ZZMatrix, target::ZZMatrix; filename="fplll")
  save_fmpz_mat(B, "$(filename).in")
  open("$(filename).in", "a") do f
    write(f, string(target))
  end
  @vprint :NormRelation 1 "Calling fplll.\n"
  @vtime :NormRelation 1 run(
        pipeline(`fplll -a cvp $(filename).in`, stdout="$(filename).out"))
  B = load_fmpz_mat(1, ncols(B), "$(filename).out")
  return B
end

#=
########################################################################
# LLL/BKZ/HKZ/SVP
########################################################################

function fplll(B::ZZMatrix; filename="fplll", eta=0.51, delta=0.99)
  save_fmpz_mat(transpose(B), "$(filename).in")
  @vprint :NormRelation 1 "Calling fplll.\n"
  @vtime :NormRelation 1 run(
        pipeline(`fplll -a lll -e $(eta) -d $(delta) $(filename).in`, stdout="$(filename).out"))
  B = transpose(load_fmpz_mat(ncols(B), nrows(B), "$(filename).out"))
  return B
end

function fplll(A::ArbMatrix; filename="fplll", eta=0.51, delta=0.99)
  B, prec = arb_mat_to_fmpz_mat(A)
  B = fplll(B, filename=filename, eta=eta, delta=delta)
  return fmpz_mat_to_arb_mat(B, prec, scale=true)
end

function flint_lll(A::ArbMatrix)
  B, prec = arb_mat_to_fmpz_mat(A)
  B = transpose(Hecke.lll(transpose(B)))
  return fmpz_mat_to_arb_mat(B, prec, scale=true)
end

# Does initial LLL reduction unless nolll=true
function bkz(B::ZZMatrix, block_size; filename="fplll")
  save_fmpz_mat(transpose(B), "$(filename).in")
  @vprint :NormRelation 1 "Calling fplll.\n"
  @vtime :NormRelation 1 run(pipeline(`fplll -a bkz -b $(block_size) $(filename).in`, 
                                         stdout="$(filename).out"))
  B = transpose(load_fmpz_mat(ncols(B), nrows(B), "$(filename).out"))
  return B
end

# Does initial LLL reduction unless nolll=true
function bkz(A::ArbMatrix, block_size; filename="fplll")
  B, prec = arb_mat_to_fmpz_mat(A)
  B = old_bkz(B, block_size, filename=filename)
  return fmpz_mat_to_arb_mat(B, prec, scale=true)
end

function wip_fplll_with_transform(B::ZZMatrix; filename="fplll", eta=0.51, delta=0.99)
  save_fmpz_mat(transpose(B), "$(filename).in")
  @vprint :NormRelation 1 "Calling fplll.\n"
  @vtime :NormRelation 1 run(
    pipeline(
      `fplll -a lll -of u -e $(eta) -d $(delta) $(filename).in`,
      stdout="$(filename).out")
    )
  U = transpose(load_fmpz_mat(ncols(B), ncols(B), "$(filename).out"))
  return B*U, U
end

function wip_fplll_with_transform(A::ArbMatrix; filename="fplll", eta=0.51, delta=0.99)
  B, _ = arb_mat_to_fmpz_mat(A)
  _, U = fplll_with_transform(B, filename=filename, eta=eta, delta=delta)
  return A*U, U
end

function wip_fplll(B::ZZMatrix; filename="fplll", eta=0.51, delta=0.99)
  B, _ = fplll_with_transform(B, filename=filename, eta=eta, delta=delta)
  return B
end

function wip_fplll(B::ArbMatrix; filename="fplll", eta=0.51, delta=0.99)
  B, _ = fplll_with_transform(B, filename=filename, eta=eta, delta=delta)
  return B
end

function wip_bkz_with_transform(B::ZZMatrix, block_size::Int; filename="fplll", max_loops::Int=0)
  save_fmpz_mat(transpose(B), "$(filename).in")
  @vprint :NormRelation 1 "Calling fplll.\n"
  if max_loops == 0
    @vtime :NormRelation 1 run(
      pipeline(
        `fplll -a bkz -of u -b $(block_size) $(filename).in`,
        stdout="$(filename).out")
      )
  else
    @vtime :NormRelation 1 run(
      pipeline(
        `fplll -a bkz -of u -b $(block_size) -bkzmaxloops $(max_loops) $(filename).in`,
        stdout="$(filename).out")
      )
  end
  U = transpose(load_fmpz_mat(ncols(B), ncols(B), "$(filename).out"))
  return B*U, U
end

function wip_bkz_with_transform(A::ArbMatrix, block_size::Int; filename="fplll", max_loops::Int=0)
  B, _ = arb_mat_to_fmpz_mat(A)
  _, U = bkz_with_transform(B, block_size, filename=filename, max_loops=max_loops)
  return A*U, U
end

function wip_bkz(B::ZZMatrix, block_size::Int; filename="fplll", max_loops::Int=0)
  B, _ = bkz_with_transform(B, block_size, filename=filename, max_loops=max_loops)
  return B
end

function wip_bkz(B::ArbMatrix, block_size::Int; filename="fplll", max_loops::Int=0)
  B, _ = bkz_with_transform(B, block_size, filename=filename, max_loops=max_loops)
  return B
end
=#

#function svp(B::ZZMatrix, filename="fplll")
#  save_fmpz_mat(transpose(B), "$(filename).in")
#  @vprint :NormRelation 1 "Calling fplll.\n"
#  @vtime :NormRelation 1 run(
#        pipeline(`fplll -a svp $(filename).in`, stdout="$(filename).out"))
#  B = transpose(load_fmpz_mat(1, nrows(B), "$(filename).out"))
#  return B
#end
#
#function svp(A::ArbMatrix, filename="fplll")
#  B, prec = arb_mat_to_fmpz_mat(A)
#  B = svp(B, filename)
#  return fmpz_mat_to_arb_mat(B, prec, scale=true)
#end
#
#function mylll(B::ZZMatrix, filename="fplll"; eta=0.51, delta=0.99)
#  save_fmpz_mat(transpose(B), "$(filename).in")
#  @vprint :NormRelation 1 "Calling fplll.\n"
#  @vtime :NormRelation 1 run(
#        pipeline(`fplll -a lll -e $(eta) -d $(delta) $(filename).in`, stdout="$(filename).out"))
#  B = transpose(load_fmpz_mat(ncols(B), nrows(B), "$(filename).out"))
#  return B
#end
#
#function Hecke.lll(A::ArbMatrix, filename="fplll"; eta=0.51, delta=0.99)
#  B, prec = arb_mat_to_fmpz_mat(A)
#  B = Hecke.lll(B, filename, eta=eta, delta=delta)
#  return fmpz_mat_to_arb_mat(B, prec, scale=true)
#end
#
#function hlll(B::ZZMatrix, filename="fplll"; eta=0.51, delta=0.99)
#  save_fmpz_mat(transpose(B), "$(filename).in")
#  @vprint :NormRelation 1 "Calling fplll.\n"
#  @vtime :NormRelation 1 run(
#        pipeline(`fplll -a hlll -e $(eta) -d $(delta) $(filename).in`, stdout="$(filename).out"))
#  B = transpose(load_fmpz_mat(ncols(B), nrows(B), "$(filename).out"))
#  return B
#end
#
#function hlll(A::ArbMatrix, filename="fplll"; eta=0.51, delta=0.99)
#  B, prec = arb_mat_to_fmpz_mat(A)
#  B = Hecke.hlll(B, filename, eta=eta, delta=delta)
#  return fmpz_mat_to_arb_mat(B, prec, scale=true)
#end
#
## Does initial LLL reduction unless nolll=true
#function bkz(B::ZZMatrix, block_size, filename="fplll"; nolll=false)
#  save_fmpz_mat(transpose(B), "$(filename).in")
#  @vprint :NormRelation 1 "Calling fplll.\n"
#  if nolll
#    @vtime :NormRelation 1 run(pipeline(`fplll -a bkz -nolll -b $(block_size) $(filename).in`, 
#                                             stdout="$(filename).out"))
#  else
#    @vtime :NormRelation 1 run(pipeline(`fplll -a bkz -b $(block_size) $(filename).in`, 
#                                             stdout="$(filename).out"))
#  end
#  B = transpose(load_fmpz_mat(ncols(B), nrows(B), "$(filename).out"))
#  return B
#end
#
## Does initial LLL reduction unless nolll=true
#function bkz(A::ArbMatrix, block_size, filename="fplll"; nolll=false)
#  B, prec = arb_mat_to_fmpz_mat(A)
#  B = bkz(B, block_size, filename, nolll=nolll)
#  return fmpz_mat_to_arb_mat(B, prec, scale=true)
#end
#
## Does initial LLL reduction
#function hkz(B::ZZMatrix, block_size, filename="fplll")
#  save_fmpz_mat(transpose(B), "$(filename).in")
#  @vprint :NormRelation 1 "Calling fplll.\n"
#  @vtime :NormRelation 1 run(pipeline(`fplll -a hkz -b $(block_size) $(filename).in`, 
#                                             stdout="$(filename).out"))
#  B = transpose(load_fmpz_mat(ncols(B), nrows(B), "$(filename).out"))
#  return B
#end
#
## Does initial LLL reduction
#function hkz(A::ArbMatrix, block_size, filename="fplll")
#  B, prec = arb_mat_to_fmpz_mat(A)
#  B = hkz(B, block_size, filename)
#  return fmpz_mat_to_arb_mat(B, prec, scale=true)
#end

# LLL with quadratic bit complexity (D. Stehle)
# NOTES:
# - eta = 1/2 may loop forever in floating point implementations. It can be achieved by choosing 
#   eta in (1/2, sqrt(delta)) then running standard LLL on the output (which is just a size 
#   reduction, aka nearest-plane instance).
# - delta in (1/4, 1]
# - precision: "asymptotically, when (delta, eta) close to (1, 1/2), a floating point precision of 
#   1.6*d suffices". So if you're not sure, produce B with arbs of precision > 1.6*d (d = number
#   of basis vectors)
function my_lll!(B::ArbMatrix; delta::ArbFieldElem=parent(B[1,1])(0.99), eta::ArbFieldElem=parent(B[1,1])(0.51))
  A = parent(B[1,1])
  d::Int = ncols(B)

  eta_bar = (eta + 1/2)/2 # should be -1/2 ...?
  delta_bar = (delta + 1)/2
  
  mu::ArbMatrix = identity_matrix(A, d)
  r = Vector{ArbFieldElem}(undef, d)

  G = gram_schmidt(B)
  r[1] = dot(B[:,1], B[:,1])
  k = 2
  while k <= d
    r[k] = dot(G[:,k], G[:,k])
    for j = 1:k-1
      r[j] = dot(G[:,j], G[:,j])
      mu[k,j] = dot(B[:,k], G[:,j]) // r[j]
    end

    if maximum(map(x -> abs(x), mu[k,1:k-1])) > eta_bar
      for i = k-1:-1:1
        x = round(Hecke._arb_get_fmpq(mu[k,i]))
        B[:,k] -= x*B[:,i]
        
        if i != 1
          mu[k,1:i-1] -= x*mu[i,1:i-1]
        end
      end
      # update G naively, improve later
      G = gram_schmidt(B)
      continue
    end
   
    if delta_bar*r[k-1] < r[k] + r[k-1]*mu[k,k-1]^2
      k += 1
    else
      swap_cols!(B, k, k-1)
      G = gram_schmidt(B)
      k = max(2, k-1)
    end
  end
end

function my_lll(B::ArbMatrix; delta::ArbFieldElem=parent(B[1,1])(0.99), eta::ArbFieldElem=parent(B[1,1])(0.51))
  BB = deepcopy(B)
  my_lll!(BB)
  return BB
end

