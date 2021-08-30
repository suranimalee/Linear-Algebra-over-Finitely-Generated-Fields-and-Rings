###################################################################
#
#             Tools for Determinant Computation
#        
###################################################################


# Representation matrices of the matrix entries of A
function  RepresentMat(A::Generic.Mat{nf_elem})
    K = base_ring(A)
	d = degree(K)
    r = nrows(A)
	c = ncols(A)
    B = basis(K)
    AA = zero_matrix(QQ, d*r, d*c)
    for i = 1:r
        for j = 1:c
            for k = 1:d
                f = A[i,j]*gen(K)^(k-1)
                for l = 1:d
                    AA[(i-1)*d + l, (j-1)*d + k] = coeff(f,l-1)
                end
            end
        end
    end
return AA

end



## Coefficients matrix of the matrix entries of A 
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
 
function rational_reconstruction_copy(A::Generic.Mat{nf_elem}, M::fmpz)
  B = similar(A)
  sM = root(M, 2)
  d = one(A[1,1])
  di = inv(d)
  for i=1:nrows(A)
    for j=1:ncols(A)
      a = A[i,j]*d
      mod_sym!(a, M)
      if all(i->Hecke.small_coeff(a, sM, i), 1:a.elem_length)
        B[i,j] = a*di
      else
        n, dn = Hecke.algebraic_reconstruction(a, M)
        d*=dn
        if any(i->!Hecke.small_coeff(d, sM, i), 1:a.elem_length)
          println("early $i $j abort")
          return false, B ,d
        end
        di*=inv(dn)
        B[i,j] = n*di
      end
    end
  end
 # println("final den: $d")
  return true, B , d 
end




## Dixon Solver

function DetSolve(A::Generic.Mat{nf_elem}, B::Generic.Mat{nf_elem})#, recon::Function = Hecke.rational_reconstruction, bound::Function = HadamardCoeff, determinant::Function = determinant_dixon)
  p = Hecke.next_prime(Hecke.p_start)
  K = Hecke.base_ring(A)
  d=degree(K)
  n=nrows(A)
  #N=bound(A)
  N= HadamardCoeff(A)
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
     fl, SOL,den = rational_reconstruction_copy(sol, pp) #recon
        if fl && A[1:1,1:n]*SOL == B[1,1]
println("solved")
          return SOL 
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




####################################################################
#
#               Hocl with inverse transform
#
####################################################################


function pseudo_hcol(B::Hecke.PMat)
   H = deepcopy(B)
   m = nrows(H)
   A = H.matrix
   K = base_ring(A)
   V = Array(K,m)
   V[1] = K(0)
println("time 1")
@time begin
      H.coeffs[1] = H.coeffs[1]*A[1, 1]
      simplify(H.coeffs[1])
      Hecke.divide_row!(A, 1, A[1, 1])
      for l = 0: m-2 
         j = m-l
@show l
         if iszero(A[j, 1])
            continue
         end
         Aji = deepcopy(A[j, 1])
         a = H.coeffs[j]
         aa = Aji*a
         b = H.coeffs[1]
@time         d = aa + b
         id = inv(d)   
@time         ad = aa*id
@time         simplify(ad)
@time         bd = b*id
         simplify(bd)
         if ad.den != 1 || bd.den != 1
            error("Ideals are not integral.")
         end
         u, v = map(K, idempotents(ad.num, bd.num))
         u = divexact(u, Aji)
         V[j] = u     

@time         H.coeffs[j] = a*b*id
@time         simplify(H.coeffs[j])
         H.coeffs[1] = d
         simplify(H.coeffs[1])
      end
end


# HCOL 
ZK = maximal_order(K)
z = ideal(ZK,1)
C = H.coeffs
W = deepcopy(B.matrix[1:m, :])
W[1,1]=-W[1,1]
I = MatrixSpace(K,m,m)(K(1))
println("time 2")

@time begin
    for i = 1 : m
        if C[i] == z
            continue
        else
            for k = 1: i-1
                I[k,i] = mod(-V[i]*W[k,1], C[i]//C[k])
                W[k,1] = W[k,1]+I[k,i]*W[i,1]          
            end
        end
    end
end
println("pseudo_hcol")
    P = pseudo_matrix(I, C)
@time U = inv_upper_triang(I)
   return P, B.matrix*U 
end


# inverse computation of a upper-triangular matrix
function inv_upper_triang(M::Generic.Mat{T}) where T
K = base_ring(M)
n = nrows(M)
I=MatrixSpace(K,n,n)(K(1))
    for i= 1:n
        I[i, i] = 1//M[i, i]
        for j = i+1 :n
#TODO wrire as a sum
            for k= i: j-1
                I[i,j]+=I[i, k]*M[k ,j]
            end
            I[i, j] = (-I[i,j]//M[j, j])
        end
    end
    return I
end


####################################################################
#
#               Reduced Extend Code by Claus
#
####################################################################

function mod_lll(a::NfAbsOrdElem, I::NfAbsOrdIdl)
  l = lll(I)[2]
  S = l*basis_matrix(I)
  Si = pseudo_inv(S)
  c = matrix(FlintZZ, 1, nrows(l), coordinates(a)) * Si[1]
  d = matrix(FlintZZ, 1, nrows(l), [round(fmpz, x, Si[2]) for x = c])
  return a - Hecke.parent(a)(collect(d*S))
end

function mod_lll(a::nf_elem, I::Hecke.NfAbsOrdFracIdl)
  O = order(I)
  d = lcm(denominator(a, O), denominator(I))
  return divexact(Hecke.parent(a)(mod_lll(O(d*a), simplify(I*d).num)), d)
end

function _reduce(a::Hecke.PMat,U)
  A = a.coeffs
  M = a.matrix
  for i=2:nrows(M)
    for j=1:i-1
      if iszero(M[j, i])
        continue
      end
      I = A[i]*M[i,i]*inv(A[j])
      c = mod_lll(M[j,i], I)
      @assert (c - M[j,i]) in I
      d = divexact(M[j, i] -c, M[i,i])
      M[j, :] = M[j, :] - d*M[i, :]
#      T[j, :] = T[j, :] - d*T[i, :]
      U[:, i] = U[:, i] + d*U[:, j]  
      @assert M[j, i] == c
    end
  end
end



function extend2(M::Hecke.PMat, b::Generic.MatSpaceElem{nf_elem}, gamma::Generic.MatSpaceElem{nf_elem})
    K = base_ring(gamma)
    zk = maximal_order(K)
    n = nrows(gamma)
    I = MatrixSpace(K,1,1)(1)
    S = vcat(I, -gamma)
    nc = n+1
    p = pseudo_matrix( hcat(S, vcat(zero_matrix(zk, 1, n),identity_matrix(zk, n))), vcat( [1*zk],map(inv, coefficient_ideals(M))))
println("HNF")
@time    h, U = pseudo_hcol(p) 

println("Reduction")
@time begin
    _reduce(h,U)

    for i=1:nrows(h)
        j, al = Hecke.reduce_ideal(h.coeffs[i])
    #   T[i, :] *= inv(al)
        U[:, i] *= al
        h.coeffs[i] = j
        h.matrix[i, :] *= inv(al)
    end 
end
    e = pseudo_matrix((U'*hcat(b, M.matrix')')[2:nrows(M)+1, :], map(inv, h.coeffs[2:nrows(M)+1]))

    return e, pseudo_matrix(h.matrix[2:nrows(M)+1, 2:ncols(M)+1],  h.coeffs[2:nrows(M)+1])  
end


# Denominator ideal is computed using HCOL, To check whether denominator is complete DualTest or norm check can be used. 
# Norm can be computed faster using RepresentMat(A)
function denominatorDet(A::Generic.Mat{nf_elem}, U::UnitRange{Int64},   p::Int64, u::Int64, UniCert::Function = UniCert) 
    K = base_ring(A)
    n = ncols(A)
    b = rand(MatrixSpace(K, n, 1), U)
println("solver")
@time    S = DetSolve(A,b)#Hecke.solve_dixon(A,b)
println("Extend")
    m1,h = extend2(pseudo_matrix(A'), b, S) 
    tt=0
println("Det Z")
@time DD = det(RepresentMat(A))

    Dh = one(det(h))
    Dhh= identity_matrix(h.matrix)

    while true
println("Dual test or Norm test")
        #@time  fl = DualTest(m1, p, u, UniCert)
        Dnew = abs(norm(det(h))*norm(Dh))
        fl= abs(DD)==Dnew

 
        Dhh = h.matrix*Dhh
        Dh = Dh*det(h.matrix)

@show tt+=1
        if fl
            denom = pseudo_matrix(Dhh, coefficient_ideals(h))
            #show abs(norm(det(denom)))== abs(DD)
            DET = determinant_test(integral_split(det(denom))[1],A)
            return  DET 
        end

    b = rand(MatrixSpace(K, n, 1), U)   
    S = DetSolve(m1.matrix',b)#Hecke.solve_dixon(m1.matrix',b)
    m1,h = extend2(m1, b, S) 
    end
end



####################################################################
#
#               Determinant of a matrix over number field
#
####################################################################


## CRT
function crt_ideal(A::NfOrdIdl, B::NfOrdIdl, a::NfOrdElem, b::NfOrdElem )
    v,u=idempotents(A,B)
    return a*u+b*v
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

# TODO use ResidueField with one prime ideal, remove init 
# TODO Try finding the missing unit 
## Determinant computing using CRT with determinant-ideal "D" ( from denominatorDet)
function determinant_test(D::NfAbsOrdIdl{AnticNumberField,nf_elem}, A::Generic.Mat{nf_elem})
    K=base_ring(A)
    d=degree(K)
    ZK=maximal_order(K)
    p=next_prime(Hecke.p_start)
    t=0
    PP=fmpz(1)
    Dl =lll(basis_matrix(D))
    U = matrix(QQ,degree(K),degree(K),array_mat(Dl))
    F = []
    for i=1:nrows(Dl)
         push!(F, order(D)([Dl[i,j] for j=1:ncols(Dl)]))
    end
    de = ZK(0)
    d1 = ZK(0)
println("CRT")
    while true
        me = Hecke.modular_init(K, p)
        ap = Hecke.modular_proj(A, me)
        ap = [det(x) for x= ap]
        Aip= Hecke.modular_lift(ap, me)
@show t+=1
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
            return de 
        else
            d1=de
            p = next_prime(p)
        end
    end
end



####################################################################
#
#               Unimodular Certification over number field
#
####################################################################


# DualTest checks whether P is unimodular using UniCert
# UniCert(M:: matrix, I:: matrix,  p:: prime start, u:: bound on coefficients of A) 

function DualTest(P::Hecke.PMat, p::Int64 , u::Int64, UniCert::Function = UniCert)
M = (P.matrix)'
C = map(inv, coefficient_ideals(P))
n = nrows(M)
K = base_ring(M)
I = zero_matrix(K,n,n)

    for i = 1:n
        I[i,i] = C[i].num.gen_one
    end
@time    fl = UniCert(M, I, p , u) 
    if fl
        for i = 1:n
            I[i,i] = C[i].num.gen_two.elem_in_nf
        end
@time        fl = UniCert(M, I, p, u) 
        if fl
            return fl
        end
    end
    return fl
end




#TODO check new edition det(h)

#= example
include("/home/ajantha/Documents/RNS/UniCertGF.jl")
include("/home/ajantha/Documents/Determinant/PseudoHcolSeven.jl")
 Zx,x=FlintZZ["x"]
 k,a=number_field(x^3+7x+1)
 m=rand(MatrixSpace(k,10,10),100:1000);
 m = cat(m,m, dims=(1,2));
@time denominatorDet(m,100:1000,100, 10000, UniCert)
@time denominatorDet(m, U, p , u, UniCert)
U : UnitRange
p : next_prime(p) to be used in UniCert 
u : Upperbound for the size of entries of matrix m 
=#




#Error from Det Algo combined
#= timing
k,a=number_field(x^3+7x+1)
 A=rand(MatrixSpace(k,200,200),-100:100);
@time denominatorDet(A, -100:100, 100, 1000000, UniCert);
 47.893645 seconds (51.63 M allocations: 4.736 GiB, 2.41% gc time)
Hecke 86.756779 seconds (27.56 M allocations: 3.786 GiB, 0.24% gc time)
 A=rand(MatrixSpace(k,250,250),-100:100);
82.240201 seconds (92.74 M allocations: 8.360 GiB, 3.01% gc time)
Hecke 227.066364 seconds (70.01 M allocations: 12.547 GiB, 0.13% gc time)
A=rand(MatrixSpace(k,300,300),-100:100);
162.491994 seconds (149.16 M allocations: 14.201 GiB, 2.37% gc time)
Hecke 500.179925 seconds (145.87 M allocations: 31.046 GiB, 0.10% gc time)
A=rand(MatrixSpace(k,50,50),-100:100);
3.232310 seconds (2.74 M allocations: 191.457 MiB, 4.34% gc time)
Hecke 0.368396 seconds (185.85 k allocations: 8.980 MiB)
with unicert 11.717651 seconds (31.10 M allocations: 2.206 GiB, 12.50% gc time)
8 seconds unicert
k, a = wildanger_field(10, 13)
A=rand(MatrixSpace(k,50,50),-100:100);
solved
  5.507159 seconds (1.10 M allocations: 252.816 MiB, 0.49% gc time)
pseudo_hcol
addition & simplification
 59.356221 seconds (6.91 M allocations: 6.170 GiB, 0.49% gc time)
Reduction
  5.639285 seconds (2.32 M allocations: 455.558 MiB, 0.50% gc time)
Det Z
 20.665928 seconds (1.42 M allocations: 1.584 GiB, 0.38% gc time)
TOTAL
 96.774058 seconds (17.89 M allocations: 9.127 GiB, 0.54% gc time)
24 times CRT
Hecke  7.523214 seconds (4.28 M allocations: 1.092 GiB, 0.52% gc time)
=#
