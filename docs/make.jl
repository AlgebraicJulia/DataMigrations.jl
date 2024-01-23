using Documenter

@info "Loading DataMigrations"
using DataMigrations

@info "Building Documenter.jl docs"
makedocs(
  modules=[DataMigrations],
  format=Documenter.HTML(),
  sitename="DataMigrations.jl",
  doctest=false,
  checkdocs=:none,
  pages=Any[
    "DataMigrations.jl"=>"index.md",
    "Library Reference"=>"api.md",
  ]
)

@info "Deploying docs"
deploydocs(
  target="build",
  repo="github.com/AlgebraicJulia/DataMigrations.jl.git",
  branch="gh-pages"
)
