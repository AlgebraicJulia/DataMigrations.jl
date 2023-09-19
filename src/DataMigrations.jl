""" 
`DataMigrations.jl`

Extends [`Catlab.jl`](@ref) with facilities for migrating 
acsets (see [`Acsets.jl`](@ref)) to different 
schemas via *conjunctive*, *duc*, and *gluing* queries.
Such queries are determined by a functor on the 
target schema valued in diagram categories of the target
schema.
"""
module DataMigrations

using Reexport
export func
include("Migrations.jl")
include("DiagrammaticPrograms.jl")

@reexport using .Migrations
@reexport using .DiagrammaticPrograms
end
