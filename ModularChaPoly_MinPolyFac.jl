# Given factors (f_i,g_i), FactorsMult compute the product of all factors.
function FactorsMult(S::Array{Tuple{Generic.Poly{nf_elem},Int64},1})
    r, = size(S)
    f = prod([(S[i][1])^(S[i][2]) for i = 1:r])
    return f
end


# Given factors, FactorMult computes (charpoly/minpoly)mod p in F_q
function FactorMult(S::Array{Tuple{fq_nmod_poly,Int64},1})
    r, = size(S)
    f = prod([(S[i][1])^(S[i][2]-1) for i = 1:r])
    return f
end


# NextPrime computes the next totally ramified prime
function NextPrime(start::Int64, O::NfAbsOrd{AnticNumberField,nf_elem})
i = 1
start = Hecke.next_prime(start)
    while true
    P = prime_decomposition_type(O, start)
        if length(P) == 1
           @show i 
            return start
        end 
        i +=1
        start = Hecke.next_prime(start) 
    end      
end



# Computes (charpoly/minpoly) mod p
function CharPolyFacP(A::Generic.Mat{nf_elem}, p::Int64, Kt::Generic.PolyRing{nf_elem})
    println("modular")
    K = base_ring(A)
   # Kt, t = PolynomialRing(K, cached = false)
    f = Kt(1)
    me = Hecke.modular_init(K, p)
    ap = Hecke.modular_proj(A, me)

    if !isdefined(me, :fldx)
        me.fldx = [PolynomialRing(x, "_x", cached=false)[1] for x = me.fld]
        me.Kx = Kt
    end

    r = size(ap)[1]
    cp = fq_nmod_poly[]
    for j = 1:r
        push!(cp,charpoly(me.fldx[j], ap[j]))
    end 

    faC = Vector{Any}(undef, r)   
    for j = 1:r
        faC[j] = [ (f,e) for (f, e) in factor(cp[j]) ]
    end

    fcp = faC[1]
    m, = size(fcp)
    ec = [ x[2] for x in fcp ]
    S =Tuple{fq_nmod_poly,Int64}[]

    for i = 1:m
        if ec[i]> 1
            push!(S, fcp[i])
        end
    end
    
    if S== []
        return f
    else
        return f = Hecke.modular_lift([FactorMult(S)] , me)
    end

end


#####################################
#
#     Computes  charpoly/minpoly
# given a PolyRing
####################################

function CharPolyMin(Kt::Generic.PolyRing{nf_elem}, M::Generic.Mat{nf_elem}; integral::Bool = false, normal::Bool = false, proof::Bool = true)
  K = base_ring(M)
  zk = maximal_order(K)
  p = Hecke.p_start
 # Kt, t = PolynomialRing(K, cached = false)
  f = Kt(1)
  f_last = f
  d = fmpz(1)
  stable = 5
  max_stable = 5
  while true
    p = NextPrime(p, zk)
    gp = CharPolyFacP(M, p, Kt) 
    if iszero(f)
        f = gp
    else
        f, d = induce_crt(f, d, gp, fmpz(p), true)
        if integral
            fl = true
            gg = f
        else
            fl, gg = induce_rational_reconstruction(f, d)
        end

        if fl && gg == f_last
            stable -= 1
            if stable <= 0
                break
            end
        else
            stable = max_stable
        end
        f_last = gg
    end
  end
 # if !proof
    return f_last 
 # end
 # error("Proof not implemented")
end



#####################################
#
#     CRT chapoly algo by Claus
# 
####################################

function charpoly_mod(M::Generic.Mat{nf_elem}; integral::Bool = false, normal::Bool = false, proof::Bool = true)
  K = base_ring(M)
  p = Hecke.p_start
  Kt, t = PolynomialRing(K, cached = false)
  f = Kt()
  f_last = f
  d = fmpz(1)
  stable = 5
  max_stable = 5
  while true
   p  = next_prime(p)
   me = modular_init(K, p)
 length(me.fld)
    if normal && length(me.fld) < degree(K)
println("normal")
      continue
    end
    t = Hecke.modular_proj(M, me)
    if !isdefined(me, :fldx)
      me.fldx = [PolynomialRing(x, "_x", cached=false)[1] for x = me.fld]
      me.Kx = Kt
    end

    fp = map(i-> charpoly(me.fldx[i], t[i]), 1:length(t))
    gp = Hecke.modular_lift(fp, me)
    if iszero(f)
    f = gp

    else
      f, d = induce_crt(f, d, gp, fmpz(p), true)
      if integral
        fl = true
        gg = f
      else
        fl, gg = induce_rational_reconstruction(f, d)
      end

      if fl && gg == f_last
        stable -= 1
        if stable <= 0
          break
        end
      else
        stable = max_stable
      end
      f_last = gg
    end
  end
 # if !proof
    return f_last
 # end
 # error("Proof not implemented")
end



#####################################
#
#     Fast charpoly & minpoly
# 
####################################



function MinPolyFast(A::Generic.Mat{nf_elem}, CharP::Function = charpoly)
    c = CharP(A)
    Kt = parent(c)
    f = CharPolyMin(Kt, A)
    return c//f
end


function CharPolyFast(A::Generic.Mat{nf_elem}, MinP::Function = minpoly)
    c = MinP(A)
    Kt = parent(c)
    f = CharPolyMin(Kt, A)
    return c*f
end






#= example
include("/home/ajantha/Documents/CharPoly/MinToChar.jl")
include("/home/ajantha/Documents/CharPoly/charpoly_mod.jl")
CharPolyFast(m,minpoly)
MinPolyFast(m,charpoly_mod)
=#
