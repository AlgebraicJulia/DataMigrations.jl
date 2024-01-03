# DataMigrations.jl

[![Stable Documentation](https://img.shields.io/badge/docs-stable-blue.svg)](https://AlgebraicJulia.github.io/DataMigrations.jl/stable)
[![Development Documentation](https://img.shields.io/badge/docs-dev-blue.svg)](https://AlgebraicJulia.github.io/DataMigrations.jl/dev)
[![Code Coverage](https://codecov.io/gh/AlgebraicJulia/DataMigrations.jl/branch/main/graph/badge.svg)](https://codecov.io/gh/AlgebraicJulia/DataMigrationse.jl)
[![CI/CD](https://github.com/AlgebraicJulia/DataMigrations.jl/actions/workflows/julia_ci.yml/badge.svg)](https://github.com/AlgebraicJulia/DataMigrations.jl/actions/workflows/julia_ci.yml)

This package is for contravariant data migrations using Catlab. 

The main entry point to the package is the `@migration` macro, which interprets a DSL for specifying data 
migrations in a declarative manner. The DSL's basic molecules are specifications of *diagrams*, in the formal
category-theoretic sense, as well as *maps* of diagrams. Here is a simple example of a diagram whose shape is the indexing category for graphs and whose codomain contains objects named `S` and `T` and morphisms `S -> T` named `up` and `down`:

```
begin
V => S
E => T
src => up
tgt => down
end
```

The above example leaves out the key specification of in which variance of diagram category the result is intended 
to lie. The pseudo-macros `@join` and `@glue` in front of a diagram indicate that the result should be interpreted 
in the contravariant, respectively covariant, diagram categories of the codomain. 



