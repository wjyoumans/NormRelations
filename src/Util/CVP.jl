
# Computes an orthogonal basis of space spanned by the columns of M using 
# Gram-Schmidt along with a vector encoding the linearly independent columns of 
# the input matrix.
function gram_schmidt(M::ArbMatrix; orthonormal=false)
  M2 = deepcopy(M)
  N = zero_matrix(parent(M[1, 1]), nrows(M), 0)
  v = []
  for k in 1:ncols(M2)
    for j in 1:ncols(N)
      d = dot(N[:,j], N[:,j])
      @assert !contains(d, 0)
      
      x = dot(M2[:,k], N[:,j]) // d
      M2[:,k] -= x*N[:,j]
    end

    if contains(dot(M2[:,k], M2[:,k]), 0)
      continue
    end
    if orthonormal
      M2[:,k] *= sqrt(dot(M2[:,k], M2[:,k]))^-1
    end
    push!(v, k)
    N = hcat(N, M2[:,k])
  end
  return N, v
end

# Find approximate solution to CVP using Babai round-off tecnhique.
function round_off(L::ArbMatrix, t::ArbMatrix; use_lll=true)
  s = solve(L, t)
  return [round(Hecke._arb_get_fmpq(a)) for a in s]
end

# Babai's nearest plane algorithm. Given a matrix B whose columns
# form a basis for a lattice and a target (column) vector t, find a 
# vector v in Z^k and d in the fundamental parallelipiped of B such 
# that B*v + d = t. Can pass gram-schmidt basis if it's already computed.
function nearest_plane(B::ArbMatrix, t::ArbMatrix, gs=gram_schmidt(B))
  B_tilde, indep = gs
  A = parent(B[1,1])

  d = t
  #v = []
  v = zero_matrix(ZZ, ncols(B), 1)
  for i in ncols(B_tilde):-1:1
    c = dot(d, B_tilde[:,i]) // dot(B_tilde[:,i], B_tilde[:,i])
    #c = (transpose(d) * B_tilde[:,i])[1] // (transpose(B_tilde[:,i]) * B_tilde[:,i])[1]
    #push!(v, round(Hecke._arb_get_fmpq(c)))
    v[indep[i],1] = round(Hecke._arb_get_fmpq(c))
    d -= v[indep[i],1]*B[:,indep[i]]
  end

  return d, v# matrix(A, length(v), 1, reverse(v))
end

# Solve CVP via lemma 6.6 of [1]. Input matrix whose columns form a 
# basis for a lattice (not neccesarily linearly independent vectors), 
# and a target (column) vector t. Output a (v, x) with v = W*x where v is
# close to t, satisfying ||W*x - t||_inf <= (2log(8n))^(1/2) * max(w).
function close_vector(W::ArbMatrix, t::ArbMatrix)
  local x, y, v
  A = parent(W[1,1])
  n = nrows(W)

  # Terminating condition
  max_w = A(0)
  for i = 1:ncols(W)
    m = dot(W[:,i], W[:,i])
    if contains(m, 0)
      continue
    end
    max_w = max(max_w, sqrt(m))
  end
  N = sqrt(2*log(8*n))*max_w
  
  # gram schmidt basis returns linearly independent basis which may have less
  # columns
  W_tilde, indep = gram_schmidt(W)

  while true
    # sample uniform p in fundamental paralleliped of C_tilde
    # Note: careful with precision since rand uses Float64
    R = matrix(A, ncols(W_tilde), 1, [A(rand())-(1//2) for i in 1:ncols(W_tilde)])
    p = W_tilde*R

    # use nearest plane algorithm to find (d, x) such that t+p = W*x + d
    d, x = nearest_plane(W, t+p, (W_tilde, indep))

    # check terminating condition
    v = W*x
    y = v - t
    if maximum([abs(y[i,1]) for i in 1:nrows(y)]) <= N
      break
    end
  end

  return v, x
end

function close_vector(L::T, t::T; precision=100) where T
  A = ArbField(100)
  return close_vector(matrix(A, collect(L)), matrix(A, collect(t)))
end
