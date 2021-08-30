#julia> include("/home/ajantha/Documents/NonSqSolve/KernelDixon.jl")
#KernelDixon (generic function with 2 methods)



function rref_with_transform(A::Generic.Mat{nf_elem})
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



function PermuteMat(K::AnticNumberField, I::Array{Any,1}, s::Int, c::Int)
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



function KernelDixon(A::Generic.Mat{nf_elem}, recon::Function=rational_reconstruction)
K = base_ring(A)
d = degree(K)
r = nrows(A)
c = ncols(A)
p = Hecke.next_prime(Hecke.p_start)
mp = Hecke.modular_init(K,p)
RF = [rref_with_transform(x) for x = Hecke.modular_proj(A, mp)]
s  = size(RF)[1]
n = RF[1][1]
A1 = Hecke.modular_lift( [RF[i][2] for i= 1:s], mp)
T = Hecke.modular_lift( [RF[i][3] for i= 1:s], mp)
t = c-n
h = c-r
Z = matrix(K,r,0,[])

#println("Check column dependency")  
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
println("break")
                break
            end 
        else
                push!(I,j) 
                Z = hcat(Z, -A1[1:r, j:j]) 
        end
    end



#For matrices ncols < nrows    
    if h<0
        if I == []
                y = -A1[1:c, n+1:c]
            for k=1:t
                y[n+k,k]=1
            end
        else
            y = Z[1:c,1:t]
            for k=1:t
                y[n+k,k]=1
            end
        end   
    else

#For matrices ncols >= nrows
#    if h==0 || h>0
        if I == []
            y0 = -A1[1:n, n+1:c]
            N = MatrixSpace(ZZ,t,t)(1)
            y = vcat(y0,N)
        else
            N = MatrixSpace(ZZ,t,t)(1)
            Z = Z[1:n,1:t]
            y = vcat(Z,N) 
        end
    end




################ Dixon Lifting #######

P = PermuteMat(K,I,n,c)
O = zero_matrix(K,r,t)
sol = 0*y
D = O
pp = fmpz(1)
last_SOL = false
nd = 0

## Why not inv(P)??
AP = A*P
    while true
@show	nd += 1
println("mod,sol")
        mod!(y, fmpz(p))
		sol += pp*y
		pp *= p
println("recon")
        fl, SOL = recon(sol, pp)

		if fl 
            if last_SOL == SOL && AP*SOL == O
                println("used $nd $p-adic digits")
        		return t, P*SOL
            else
        		last_SOL = SOL
      		end
    	end

println("dmult")
    D = D - AP*y
		divexact!(D, fmpz(p))
		y = T*D

		if h>0
        	OO = zero_matrix(K,h,t)
			y=vcat(y,OO)
		end

        if h<0
            y=y[1:c,1:t]
        end

    if nbits(pp) > 1000000 # a safety device to avoid infinite loops
      error("not work")
    end
  	end
end

