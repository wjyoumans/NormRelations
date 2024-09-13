
# Return column vector of log embeddings of x.
function log_embedding(x::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField},
    A::ArbField=ArbField(100), 
    project::Bool=true)

  K = base_ring(x)
  w = conjugates_arb_log(x, precision(A)+1)
  if project
      w = map(x -> x - 2 * divexact(sum(w), degree(K)), w) 
  end
  return matrix(A, length(w), 1, w)
end

# compute lattice of log embeddings (including projecting onto Log(U) tensor R).
function log_embedding_lattice(
    U::Vector{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}},
    A::ArbField=ArbField(100);
    project::Bool=true)

  m = length(U)
  K = base_ring(U[1])
  r1, r2 = signature(K)

  W = zero_matrix(A, r1+r2, m)
  for i in 1:m
    W[:,i] = log_embedding(U[i], A, project=project)
  end
  return W
end

