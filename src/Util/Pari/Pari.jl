
# run abelianbnf on input number field, extract the rational primes used
# if no norm relation for K then this should return an empty list
function get_primes_pari(K; path=ABELIANBNFPATH, filename=false, 
    parisizemax=PARISIZEMAX)
  zp, x = ZZ["x"]
  pol = zp(K.pol)

  if isa(filename, Bool)
    cmd = "get_primes($pol)"
  else
    cmd = "get_primes($pol, $filename)"
  end

  #pipe = pipeline(
  #  `echo $cmd`,
  #  `gp -D parisizemax=$parisizemax -q $(gp_path)`
  #)
  #res = Base.read(pipe, String)
  
  @vprint :Pari 1 "Pari ($parisizemax): executing \"$cmd\" \n"
  
  ioo = IOBuffer()
  open(`gp -D parisizemax=$parisizemax -q $(path)`, ioo, write = true) do io
    println(io, cmd)
  end
  res = String(take!(ioo))
  
  res = split(replace(res, "\n"=>"", "["=>"", "]"=>""), ", ")
  if res[1] == ""
    return []
  end
  return [ZZ(String(p)) for p in res]
end

function _to_pari(M::MatElem)
  function __to_pari(M::MatElem)
    M_str = "["
    for i = 1:nrows(M)
      for j = 1:ncols(M)
        M_str = string(M_str, M[i,j], ",")
      end
      M_str = string(M_str[1:end-1], ";")
    end
    M_str = string(M_str[1:end-1], "]")
    return M_str
  end

  if ncols(M) == 1
    return string(__to_pari(transpose(M)), "~")
  end
  return __to_pari(M)
end

# solve M*x = B mod n.
# Return solution x, rank of the kernel, and matrix whose columns give a basis 
# for the right kernel
function matsolvemod(M::MatElem, n, B::MatElem; parisizemax=PARISIZEMAX)
  R = base_ring(M)

  cmd = "matsolvemod($(_to_pari(M)), $n, $(_to_pari(B)), 1)"
  #pipe = pipeline(
  #	`echo $cmd`,
  #	`gp -q -D parisizemax=$parisizemax`	  
  #)
  #s = Base.read(pipe, String)
  
  @vprint :Pari 1 "Pari ($parisizemax): executing \"$cmd\" \n"
  
  ioo = IOBuffer()
  open(`gp -q -s $parisizemax`, ioo, write = true) do io
    println(io, cmd)
  end
  s = String(take!(ioo))

  # s of the form: \"[[1, 0]~, [1, 2; 3, 4]]\n\"
  # remove leading [ and trailing ]\n
  s = s[2:end-2]
  i = collect(findfirst("]", s))[1]
  col = split(s[2:i-1], ",")
  X = matrix(R, length(col), 1, [ZZ(String(x)) for x in col])

  s = s[i+4:end]
  i = collect(findfirst(";", s))[1]
  t = s[2:i-1]
  row = split(t, ",")
  mat = split(replace(s[2:end-1], ";"=>","), ",")
  Y = matrix(R, length(row), length(col), [ZZ(String(x)) for x in mat])

  Z = zero_matrix(R, length(row), 0)
  for i=1:ncols(Y)
    if !iszero(Y[:,i])
      Z = hcat(Z, Y[:,i])
    end
  end

  # ncols(Z) == rank of nullspace
  return X, ncols(Z), Z
end

