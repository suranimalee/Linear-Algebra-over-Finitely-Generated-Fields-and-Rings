# Linear-Algebra-over-Finitely-Generated-Fields-and-Rings
Linear Algebra over Finitely Generated Fields and Rings 

This repository provides all the implementations of the algorithms available in the Ph.D. thesis "Linear Algebra over Finitely Generated Fields and Rings". Please see https://kluedo.ub.rptu.de/frontdoor/index/index/docId/6560 

The implementations were done using the Hecke software package: https://github.com/thofma/Hecke.jl

The file ModularDeterminant.jl provides a determinant computation algorithm using modular techniques. It contains the implementations done for the paper "Fast and Practical Algorithm for Computing the Determinant of a Matrix over Number Fields" for the ISSAC 2023 conference. 

ModularDeterminant Algorithm (function named "DetFinal" in the file) computes the determinant of a matrix $A$, by solving $Ax=b$ for a given arbitrary RHS matrix $b$  

```ruby
using Hecke
Zx,x=FlintZZ["x"]
k,a=number_field(x^3+7x+1)
A = rand(MatrixSpace(k , 50,50), -10000:10000);
b = rand(MatrixSpace(k , 50,1), -10000:10000);
@time DetFinal(A,b,rational_reconstruction_copy,HadamardCoeff,determinant_dixon);
```
