#julia> include("/home/ajantha/Documents/NonSqSolve/NonSqDixon.jl")
#NonSqDixonSolve (generic function with 1 method)

#julia> NonSqDixonSolve(A,S)

function array_mat(A::MatElem{T}) where T
   a = []
   for i=1:nrows(A)
     for j=1:ncols(A)
	push!(a, A[i,j])
     end
   end
return a
end



function PermuteMat(K::FlintIntegerRing, I::Array{Any,1}, s::Int, c::Int)
r = c-s
TT =MatrixSpace(K,c,c)
if I==[] || I[1] == s+1 
    return TT(1)
else
    TT =MatrixSpace(K,c,c)(K(0))
    for j=1:I[1]-1
        TT[j,j] = 1
    end

    for i =1: r
        if I[i] != s+i
            TT[I[i], s+i] = 1
            if i == r
                if I[i]==c
                    break 
                else
                    for k=I[i]+1:c
                        TT[k, k-i] = 1
                    end
                end
            else
                for k=I[i]+1:I[i+1]-1
                TT[k, k-i] = 1
                end
            end
        else
            TT[s+i,s+i] = 1
        end
    end 
end    
return TT
end



function rref_with_transform(A::fq_nmod_mat)
K = base_ring(A)
r = nrows(A)
c = ncols(A)
T = MatrixSpace(K,r,r)(K(1))
	R = rref(hcat(A,T))[2]
	E = R[1:r, 1:c]
	T = R[1:r, c+1:c+r]
	i = r
	while true
		fl = iszero(E[i:i, 1:c])
			if !fl
				return i,E,T
			end
		i = i-1
	end
end


function NonSqDixonSolve(A::Generic.Mat{nf_elem}, B::Generic.Mat{nf_elem}, recon::Function=rational_reconstruction)
	K = base_ring(A)
	d = degree(K)
	r = nrows(A)
	c = ncols(A)
	p = Hecke.next_prime(Hecke.p_start)
    h = c-r
	mp = Hecke.modular_init(K,p)
    AP = Hecke.modular_proj(A, mp)
    BP = Hecke.modular_proj(B, mp)
    s = size(BP)[1]
    

    RF = [rref_with_transform(x) for x in AP]
    n = RF[1][1]
    A1 = Hecke.modular_lift( [RF[i][2] for i = 1:s], mp)
    T = Hecke.modular_lift( [RF[i][3] for i = 1:s], mp)
   


#Checking column dependency
    I = []
    i = 1
    j = 1
    for j=1:c
        if isone(A1[i, j])
            if i!=r
                i = i+1
#TODO: if i=r take the whole block 
            end
            if i==n+1 && I==[]
                break
            end 
        else
            push!(I,j)   
        end
    end




# Checking Inconsistency 
# two cases can be removed as I=[] implies PM identity
    P = PermuteMat(ZZ,I,n,c)
    PM = matrix(mp.fld[1],c,c,array_mat(P))

    if h<0
        SP = RF[1][3]*BP[1]
        SP = SP[1:c,1:1]
        if I == []
            if AP[1]*SP !=BP[1]
                error("Inconsistent")
            end
        else
            SP=PM*SP
            if AP[1]*SP !=BP[1]
                error("Inconsistent")
            end
        end
        y = T*B
        y = y[1:c,1:1]
    else
        z = zero_matrix(K,h,1)
        zp = zero_matrix(mp.fld[1],h,1)
        SP = RF[1][3]*BP[1]
        SP = vcat(SP,zp)
        if I == []
            if AP[1]*SP !=BP[1]
                error("Inconsistent")
            end
        else
                SP=PM*SP
            if AP[1]*SP !=BP[1]
                error("Inconsistent")
            end
        end
        y = T*B
       	y = vcat(y,z)
    end

# Dixon Solver
  P=matrix(K,c,c,array_mat(P))
  AP = A*P
	sol = 0*y
	D = B
	pp = fmpz(1)
	last_SOL = false
	nd = 0
	while true
		nd += 1
		mod!(y, fmpz(p))
		sol += pp*y
		pp *= p
		fl, SOL = recon(sol, pp)
		if fl 
      			if last_SOL == SOL && AP*SOL == B
        		println("used $nd $p-adic digits")
        			return  P*SOL
      			else
        			last_SOL = SOL
      			end
    		end
		D = D - AP*y
		divexact!(D, fmpz(p))
		y = T*D
## 
		if h < 0
            y=y[1:c,1:1]
        else
			y=vcat(y,z)
		end

    if nbits(pp) > 10000 # a safety device to avoid infinite loops
      error("not work")
    end
  	end
end
