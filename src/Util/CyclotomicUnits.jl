
# The cyclotomic units C are of finite index in the full unit group 
# U of K, so the lattice Log(C) is of full rank in Log(U). We want a 
# set of short vectors that generate Log(C). We use the linearly indep.
# basis of theorem 4.2 in [??].
#
# TODO: fails for m = 30, 42, 60, 70, 90, ... (3+ factors? 66 not included?)
function short_cyclotomic_units(K::AnticNumberField)
  b, m = Hecke.iscyclotomic_type(K)
  @assert b
  z = gen(K)

  fac = collect(factor(m))
  k = length(fac)  

  P = [f.first for f in fac]
  Q = [f.first^f.second for f in fac]
  M = [divexact(m, Q[i]) for i in 1:k]
 
  F = x -> all([x % P[i] != 0 || x % Q[i] == 0  for i in 1:k ])
  X = filter(F, 1:m-1)
  D = []

  # fractional part of x
  frac = x -> (x - floor(x))

  # find 0 < j < m which gives a linearly independent generator
  for j in X
    # check if j in N_+
    if m % j == 0 && isodd(count(i -> j % Q[i] != 0, 1:k))
      #println("N+: $(j)")
      push!(D, j)
      continue
    end

    done = false
    for i in 1:k
      if j % Q[i] != 0
        if mod(j, Q[i]) == mod(-gcd(m, j), Q[i])
          #println("S1: $(j)")
          done = true
          break
        elseif frac(j // Q[i] * gcd(m, j)) > 1//2
          if all([mod(gcd(m, j), Q[l]) == mod(j, Q[l]) for l in (i + 1):k])
            #println("S2: $(j)")
            done = true
            break
          end
        end
      end
    end
    if done
      push!(D, j)
      continue
    end
  end

  J = []
  # compute generators v_j
  C = Vector{FacElem{nf_elem, AnticNumberField}}()
  for j in X
    if j in D
      continue
    end
    push!(J, j)

    den = K(1)
    for i in 1:k
      if j % M[i] == 0
        den = FacElem(1 - z^M[i])
        break
      end
    end
    v = FacElem(1 - z^j) * den^-1

    if !isempty(v)
      push!(C, v)
    end
  end
  @assert length(C) == degree(K)//2 - 1
  return C
end

# all short cyclotomic units, not independent
function _short_cyclotomic_units(K::AnticNumberField)
  b, m = Hecke.iscyclotomic_type(K)
  @assert b
  z = gen(K)

  fac = collect(factor(m))
  k = length(fac)  

  Q = [f.first^f.second for f in fac]
  M = [divexact(m, Q[i]) for i in 1:k]

  # compute generators v_j
  C = Vector{FacElem{nf_elem, AnticNumberField}}()
  for j in 1:m-1
    den = K(1)
    for i in 1:k
      if j % M[i] == 0
        den = FacElem(1 - z^M[i])
        break
      end
    end
    v = FacElem(1 - z^j) * den^-1

    if !isempty(v)
      push!(C, v)
    end
  end
  
  return C
end
