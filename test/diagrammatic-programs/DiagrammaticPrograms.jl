module TestDiagrammaticPrograms

using Test

using Catlab
using Catlab.Theories: FreeCategory, FreePointedSetCategory, FreePointedSetSchema
using Catlab.WiringDiagrams.CPortGraphs
using DataMigrations
using DataMigrations.DiagrammaticPrograms: get_keyword_arg_val, destructure_unary_call

@present SchSet(FreeSchema) begin
  X::Ob
end

@present SchDDS <: SchSet begin
  Φ::Hom(X,X)
end

include("graphs.jl")
include("migrations.jl")

end
