## Compute Determinant of a matrix A, solving Ax=b for a given arbitrary RHS matrix b 
## @time DetFinal(A,b,rational_reconstruction_copy,HadamardCoeff,determinant_dixon); 
######################################################################################


## Coefficients matrix of the matrix entries ##
function coeff_mat(A::Generic.Mat{nf_elem})
  r=nrows(A)
  c=ncols(A)
  d=degree(base_ring(A))
  AA=zero_matrix(QQ,r,d*c)
  for i= 1:r
    for j= 0:c-1
      for k= 1:d
        AA[i,j*d+k]= fmpq(coeff(A[i,j+1],k-1))
      end
    end
  end
return AA
end



## Bound using Hadamard
function HadamardCoeff(A::Generic.Mat{nf_elem})
  r=nrows(A)
  c=ncols(A)
  d=degree(base_ring(A))
  AC=coeff_mat(A)

   a = []
   for i=1:d*c
       push!(a, maximum(array_mat((AC[1:r,i:i]))))
   end

  h=1
  for i= 0:c-1
      bb=0
    for j=1:d
      bb += a[i*d+j]^2
    end
      h *=(r*bb)  
  end
return BigInt(numerator(h))
end


## Rational reconsrtuction (using alg recon & small coeff )
 
function ssmall_coeff(a::nf_elem, B::fmpz, i::Int)
  z = fmpz()
  Hecke.Nemo.num_coeff!(z, a, i)
  return cmpabs(z, B) <= 0
end



function rational_reconstruction_copy(A::Generic.Mat{nf_elem}, M::fmpz)
  B = similar(A)
  sM = root(M, 2)
  d = one(A[1,1])
  di = inv(d)
  for i=1:nrows(A)
    for j=1:ncols(A)
      a = A[i,j]*d
      mod_sym!(a, M)
      if all(i->ssmall_coeff(a, sM, i), 1:a.elem_length)
        B[i,j] = a*di
      else
        n, dn = Hecke.algebraic_reconstruction(a, M)
        d*=dn
        if any(i->!ssmall_coeff(d, sM, i), 1:a.elem_length)
          println("early $i $j abort")
          return false, B ,d
        end
        di*=inv(dn)
        B[i,j] = n*di
      end
    end
  end
 # println("final den: $d")
  return true, B, d 
end


## Denominator ideal

function denominator_ideal(M::Array{Any,1}, den::nf_elem)
  k = parent(M[1,1])
  zk = maximal_order(k)
  _, d = integral_split(M[1]//den * zk)
  g = simplify(den*zk * inv(d)).num ## should be small
  gi = inv(g)
  if isone(g)
    return d
  end
   
  for m = M
    i = simplify(ideal(zk, minimum(g)^2, zk(m)))
    j = simplify(i*gi)
    if denominator(j) == 1
      continue
    end
    _, dd = integral_split(m//den * zk)
    d = lcm(d, dd)
    g = simplify(simplify(den*zk * inv(d)).num)
    gi = inv(g)
    if isone(g)
      break
    end
  end
  return d
end


# Entries of the Matrix $A$ are given as an array
function array_mat(A::MatElem{T}) where T
   a = []
   for i=1:nrows(A)
     for j=1:ncols(A)
	push!(a, numerator(A[i,j]))
     end
   end
  return a
end


## CRT
function crt_ideal(A::NfOrdIdl, B::NfOrdIdl, a::NfOrdElem, b::NfOrdElem )
   v,u=idempotents(A,B)
  return a*u+b*v
end


## Dixon Solver: Solution is forwarded to the  "determinant_dixon" to compute the determinant

function DetFinal(A::Generic.Mat{nf_elem}, B::Generic.Mat{nf_elem}, recon::Function = Hecke.rational_reconstruction, bound::Function = HadamardCoeff, determinant::Function = determinant_dixon)
  p = Hecke.next_prime(Hecke.p_start)
  K = Hecke.base_ring(A)
  d=degree(K)
  n=nrows(A)
  N=bound(A)
  me = Hecke.modular_init(K, p)
  ap = Hecke.modular_proj(A, me)
  ap = [inv(x) for x= ap]
  Aip = Hecke.modular_lift(ap, me)
  sol = 0*B
  D = B
  pp = fmpz(1)
  SOL=Hecke.zero_matrix(ZZ, n, 1)

  fl = false

  while fl==false

        y = Aip*D
        mod!(y, fmpz(p))
        sol += y*pp
        pp *= p

     if ndigits(fmpz(pp)) < ndigits(N)
        fl,SOL==false,0
     else

println("RatRecon")
     fl, SOL,den = recon(sol, pp)
        if fl && A[1:1,1:n]*SOL == B[1,1]
println("solved")
          return determinant(SOL,A,den)
        else
          fl= false
        end
     end

     D = D - A*y
     Hecke.divexact!(D, fmpz(p))
    if nbits(pp) > 10000000 # a safety device to avoid infinite loops
      error("not work")
    end
  end
end



## Determinant compute using solution from DetFinal

function determinant_dixon(SOL::Generic.Mat{nf_elem},A::Generic.Mat{nf_elem},den::nf_elem)

  K=base_ring(SOL)
  d=degree(K)
  ZK=maximal_order(K)
  p=next_prime(Hecke.p_start)
t=0
  PP=fmpz(1)
  AS=array_mat(den*SOL)
  D=denominator_ideal(AS,den)
  Dl =lll(basis_matrix(D))
  U = matrix(QQ,degree(K),degree(K),array_mat(Dl))
  F = []
    for i=1:nrows(Dl)
         push!(F, order(D)([Dl[i,j] for j=1:ncols(Dl)]))
    end

  de = ZK(0)
  d1 = ZK(0)

  while true
    me = Hecke.modular_init(K, p)
    ap = Hecke.modular_proj(A, me)
    ap = [det(x) for x= ap]
    Aip= Hecke.modular_lift(ap, me)
 t+=1
    de = crt_ideal(D,ideal(ZK, p) ,de, ZK(Aip))
    D*=p
    PP*=p
    TT=coordinates(de)
    V=matrix(QQ,degree(K),1,TT)
    W=Hecke.solve(U',V)
    W=(1//PP)*W
    k=0
    for j=1:degree(K)
          k += F[j]*(round(fmpz,(W[j,1])))
    end
    k=PP*k
    de= de-k

    if d1==de
println("Number of CRT: $t")
       return de ,den
    else
    d1=de
    p = next_prime(p)
    end

  end
end


			
## Compute Determinant of a matrix A, solving Ax=b for a given arbitrary RHS matrix b 
## @time DetFinal(A,b,rational_reconstruction_copy,HadamardCoeff,determinant_di		

