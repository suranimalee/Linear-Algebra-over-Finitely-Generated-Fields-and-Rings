function randpoly(P::PolyRing{T},U::AbstractArray) where T 
  d=rand(U)
  R=base_ring(P)
  x=gen(P)
  a = P(0)
  for i=0:d
     setcoeff!(a, d-i, rand(R))
  end
  return a
end



function rand_mat(A::MatSpace{T}, U::AbstractArray) where T
  P=base_ring(A)
  A=A(0)
  for i=1:nrows(A)
    for j=1:ncols(A)
     A[i,j]=randpoly(P, U)
    end
  end
  return A
end 


function array_mat(A::MatElem{T}) where T
   a = []
   for i=1:nrows(A)
     for j=1:ncols(A)
	push!(a, A[i,j])
     end
   end
  return a
end



function rand_pol(P::PolyRing{T},U::AbstractArray) where T 
  d=rand(U)
  R=base_ring(P)
  x=gen(P)
  a = P(0)
  for i=1:d
     setcoeff!(a, d-i, rand(R))
  end
  setcoeff!(a, d, R(1))  
  return a
end


function rand_irreducible_pol(P::PolyRing{T},U::AbstractArray) where T 
  d = rand(U)
  R = base_ring(P)
  x = gen(P)
  a = P(0)
  c = characteristic(P)
  f = defining_polynomial((FiniteField(Int64(c),d))[1])
  for i=0:d
     setcoeff!(a, i, coeff(f,i))
  end
  return a
end


function NextIrreducible(x::PolyElem{T},U::AbstractArray) where T
 K = parent(x)
 i = 1
 while true
   if isirreducible(x)
      println("used $i rounds, irreducible poly $x")
      return x
   else 
      if R(i) == 0
      println("Next loop")
      x = x*randpoly(K,U)+K(1)
#       x=randpoly(K,U)+R(1)
      i = 1
      else
        i += 1
        x = x+K(1)
      end
   end
 end
end



function mod_poly(A::Generic.Mat{gfp_poly}, P::gfp_poly)
  a = array_mat(A)
  R = base_ring(A)
#  RP = ResidueField(R,P)
  RP = FiniteField(P, "s")[1]
  r = nrows(A)
  c = ncols(A)
  B = zero_matrix(RP,r,c)
  for i = 1:r
    for j = 1:c
	B[i,j] = RP(A[i,j])
    end
  end
  return B
end


function mod_poly2(A::Generic.Mat{gfp_poly}, P::gfp_poly)
  a = array_mat(A)
  R = base_ring(A)
  RP = ResidueField(R,P)
#  RP = FiniteField(P, "s")[1]
  r = nrows(A)
  c = ncols(A)
  B = zero_matrix(RP,r,c)
  for i = 1:r
    for j = 1:c
	B[i,j] = RP(A[i,j])
    end
  end
  return B
end




function lift_mat(A::Generic.Mat{Generic.ResF{gfp_fmpz_poly}})
  r = nrows(A)
  c = ncols(A)
  a = array_mat(A)
  P = parent(lift(a[1]))
  B = matrix(P,r,c,[lift(a[i]) for i=1:r*c])
  return B
end



function lift_mat(A::Generic.Mat{Generic.ResF{gfp_poly}})
  r = nrows(A)
  c = ncols(A)
  a = array_mat(A)
  P = parent(lift(a[1]))
  B = matrix(P,r,c,[lift(a[i]) for i=1:r*c])
  return B
end



function lift_(x::fq_nmod, K:: GFPPolyRing, d:: Int64)
  z = K()
  for i=0:d-1
    setcoeff!(z, i, coeff(x, i))
  end
  return z
end


function lift_mat(A::fq_nmod_mat, K:: GFPPolyRing, d:: Int64)
  r = nrows(A)
  c = ncols(A)
  a = array_mat(A)
  B = matrix(K,r,c,[lift_(a[i],K,d) for i=1:r*c])
  return B
end


function divexact_poly_mat(A::Generic.Mat{gfp_poly}, p::gfp_poly)
  for i=1:nrows(A)
    for j=1:ncols(A)
    A[i,j] = divexact(A[i,j],p)
    end
  end
end



function DetBound(A::Generic.Mat{gfp_poly})
 K = base_ring(A)
 n = nrows(A)
# a = Array(ZZ,n^2)
# b = Array(ZZ,n)
 a=[]
  for i=1:n
    for j=1:n
     push!(a,degree(A[i,j]))
    end
  end
 b=[]
  for i=0:n-1
     push!(b,maximum(a[1+i*n:n+i*n]))
  end

  return sum(b)
end


##########################################################################
#
#           Computing Common Denominator 
#
########################################################################## 


function mul_sub_Two(q::PolyElem{T}, a::PolyElem{T}, b::PolyElem{T}, t::PolyElem{T}) where T
  t = mul!(t, a, b) # t = a*b
  t = sub!(t, q, t) # b = q - ab
  return t
end



function quot(g::PolyElem{T},k::Int) where T
  P = g.parent
  x = gen(P)
  n = degree(g)
  if (n-k)>-1
    q = shift_right(g, n-k)
  else
    q = shift_left(g, k-n)
  end
  return q
end


# deg(r0)>=deg(r1)  k<=deg(r0)

function HalfGCDDen(r1::PolyElem{T}, r0::PolyElem{T}) where T
  P = r1.parent
  k = degree(r0)
  n1 = degree(r1)
 
  
  if r1 == 0 
     return r1,P(1)
  end
 
  if k == 0 && (k-n1) == 0
     q = inv(lead(r1))*lead(r0)
     return r0-q*r1, -q
  end


  d = numerator(ceil(k//2))
  s = 0
  r = quot(r0,2*d-2)
  rr = quot(r1,2*d-2-(k-n1))
  q = P()
  re = P()

  M12 = P(0)
  M22 = P(1)


  while s <= d-1 && rr != P(0)
    q,re = divrem(r, rr)
    s+=degree(q)

    if s <= (d-1) 
      MM = M22
      M22 = mul_sub_Two(M12, q, M22, r)
      M12 = MM
    end  

  r, rr, re = rr, re, r 
  q = P(0)
  re = P(0)      

  end
  return M22 
end




function DenomMidPoly(A::Generic.Mat{gfp_poly}, p::gfp_poly)
  r = nrows(A)
  y = HalfGCDDen(A[1,1],p)  
  i = 2
  while true
    v2 = HalfGCDDen(A[i,1]*y,p)
    if isunit(v2)  #v2 == 1 || v2 == -1
       return y
    else 
       if i == r
       println("CommonDenom")
	   return y*v2
       else
         y *= v2 
	     i += 1 
       end
    end
  end
end




############################################################
#       Reconstructing Solution  from common denominator
############################################################

function SolveReconPoly(A::Generic.Mat{gfp_poly}, p::gfp_poly)
   F = FractionField(base_ring(A))
   n = nrows(A)
println("DenomPolyMid")
@time y= DenomMidPoly(A,p)
   u=zero_matrix(F, n,1)

    for i=1:n
        A[i,1]=y*A[i,1]
        u[i,1]=divrem(A[i,1],p)[2]//y

     end
       return  u
  

end



###############################################################
#
#           Reconstruction without Common Denominator
#
##############################################################

function rational_reconstruction_poly_mat(A::Generic.Mat{gfp_poly}, M::gfp_poly)
F = FractionField(base_ring(A))
r = nrows(A)
c = ncols(A)
B = zero_matrix(F,r,c)

  for i = 1:r
    for j = 1:c
     fl = true
     n,d = HalfGCDReconFast(A[i,j],M)
#    fl, n,d = rational_reconstruction(A[i,j], M)
      B[i,j] = n//d
      if !fl 
        return false, B
      end
    end
  end
  return true, B
end



function HalfGCDReconFast(r1::PolyElem{T}, r0::PolyElem{T}) where T
  P = r1.parent
  k = degree(r0)
  n1 = degree(r1) 
  
  if r1==0 
     return r1,P(1)
  end
 
  if k==0 && (k-n1)==0
     q = inv(lead(r1))*lead(r0)
     return r0-q*r1, -q
  end

  d = numerator(ceil(k//2))
  s = 0
  r = quot(r0,2*d-2)
  rr= quot(r1,2*d-2-(k-n1))
  q = P()
  re = P()

  
  M11 = P(1)
  M12 = P(0)
  M21 = P(0)
  M22 = P(1)

  while s <= d-1 && rr != P(0)

    q,re =  divrem(r,rr)
    s +=degree(q)

    if s <= (d-1) 

      MM = M21
      M21 = mul_sub_Two(M11, q, M21, r)
      M11 = MM
      MM = M22
      M22 = mul_sub_Two(M12, q, M22, q)
      M12 = MM
    end  

  r, rr, re = rr, re, r 
  q = P(0)
  re = P(0)      

  end

  n = M21*r0+M22*r1
  return n, M22 
end






##############################################################################
#
#               Dixon Solver
#
##############################################################################

 
function DixonPolyDetGF(A::Generic.Mat{gfp_poly}, B::Generic.Mat{gfp_poly}, U::AbstractArray)
  r = nrows(A)
  c = ncols(A)
  K = base_ring(A)
@show  p = NextIrreducible(rand_pol(K,U),U)
#  p = rand_irreducible_pol(K, U)
  DB = 2*DetBound(A)
  d= degree(p)  
  Ap=mod_poly(A,p)
println("Inv")
@time IA=inv(Ap)
println("lifting")
@time  ap=lift_mat(IA,K,d)
  sol = 0*B
  D = B
  pp = K(1)
  last_SOL = false
  nd = 0
  u = zero_matrix(K, r,1)

  while true
    nd += 1
    y = ap*D
    y = lift_mat(mod_poly(y,p),K,d)
 #  y = lift_mat(mod_poly2(y,p))
    sol += y*pp
    pp *= p

    if d*nd > DB

println("Choose Common denominator or Solver")
    # @time DEN = DenomMidPoly(sol,pp)
     @time DEN = SolveReconPoly(sol,pp)

println("used $nd $p-adic digits")
      return DEN
    end


   D = D - A*y
   divexact_poly_mat(D, p)
#    if nbits(pp) > 10000 # a safety device to avoid infinite loops
#      error("not work")
#    end
  end
end





###########################################################################################
#
#                       Computing Determinant 
#
###########################################################################################

function iscoprime_poly(f::gfp_poly, h::gfp_poly)
   g  = gcd(f,h)
   if g == 1
     return true
   else 
     return false
   end

end


function DeterminantGF(A::Generic.Mat{gfp_poly},U::AbstractArray, V::AbstractArray)
   K = base_ring(A)
   n = nrows(A)
   b = rand_mat(MatrixSpace(K,n,1),V)
println("DixonAlgo")
@time   pe = DixonPolyDetGF(A,b,U)

   de = K(0)
   t =0
   d1 = K(0)
   p = NextIrreducible(rand_pol(K,U),U)
  while true
println("IrreduciblePoly")
   p = NextIrreducible(p+1 ,U)
println("det p")
@time   d = lift_(det(mod_poly(A,p)),K, degree(p))
println("crt")
#counting
@show t += 1
@time de = crt(de,pe ,d,p)
      pe *= p
    if d1 == de
      return d1
    else
      d1 = de
      continue
    end
  end
end






#=example
julia> Zx,x=FlintZZ["x"]
julia> R=FlintFiniteField((3511))
julia> P,x=R["x"]
julia> A=rand_mat(MatrixSpace(P,10,10),10:15);
julia> b=rand_mat(MatrixSpace(P,10,1),10:15);
@time S = DixonPolyDetGF(A,b,5:8);
# S = DixonPolyDetGF(A,b,U ); U = degree range for irreducible poly for modular operation
# Check solution with "FractionField(P)"
julia> AA=matrix(FractionField(base_ring(A)),nrows(A), ncols(A),array_mat(A));
julia> bb=matrix(FractionField(base_ring(b)),nrows(b), ncols(b),array_mat(b));
julia> AA*S==bb
For determinant computation, lock the solver line 357
                             on the common denominator computation, line 356
@time DeterminantGF(A,5:8, 10:15);
# @time DeterminantGF(A,U, V);
# U = degree range for irreducible poly for modular operation
# V = degree range to generate matrix b 
=#



