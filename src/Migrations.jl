"""
Contravariant complex data migrations.
"""
module Migrations

export migrate,migrate!,colimit_representables, QueryDiagram, DataMigration, colimit_representables, force, compose, DiagramHom, QueryDiagramHom

using ACSets
using ACSets.DenseACSets: constructor, datatypes
using Catlab
using Catlab.Theories: ob, hom, dom, codom, attr, AttrTypeExpr, ⋅
import Catlab.Theories: compose
using Catlab.Graphs.BasicGraphs: vertex_named
import Catlab.CategoricalAlgebra.Categories: ob_map, hom_map
import Catlab.GATs: functor
using Catlab.CategoricalAlgebra.FinCats: make_map, mapvals, presentation_key, FinCatPresentation
import Catlab.CategoricalAlgebra.FinCats: force
using Catlab.CategoricalAlgebra.Chase: collage, crel_type, pres_to_eds, add_srctgt, chase
using Catlab.CategoricalAlgebra.FinSets: VarSet
import Catlab.CategoricalAlgebra.FunctorialDataMigrations: migrate, migrate!, AbstractDataMigration, ContravariantMigration, DeltaSchemaMigration
import Catlab.CategoricalAlgebra.Diagrams: DiagramHom
using MLStyle: @match

#Extra data structures for fancy diagrams and diagram homs,
#and their interaction with ordinary functors and nats.
#########################################################

""" Diagram representing a (conjunctive or gluing) query.

Besides the diagram functor itself, a query diagram contains a dictionary of
query parameters.
"""
struct QueryDiagram{T,C<:Cat,D<:Functor{<:FinCat,C},
                    Params<:AbstractDict} <: Diagram{T,C,D}
  diagram::D
  params::Params
end
QueryDiagram{T}(F::D, params::P) where {T,C<:Cat,D<:Functor{<:FinCat,C},P} =
  QueryDiagram{T,C,D,P}(F, params)
"""
  Force-evaluate the functor in a query diagram,
  including putting the parameters into the hom-map 
  explicitly.
"""
force(d::QueryDiagram{T},args...) where T =
  SimpleDiagram{T}(force(diagram(d),d.params,args...))

struct QueryDiagramHom{T,C<:Cat,F<:FinFunctor,Φ<:FinTransformation,D<:Functor{<:FinCat,C},Params<:AbstractDict}<:DiagramHom{T,C}
  shape_map::F
  diagram_map::Φ
  precomposed_diagram::D
  params::Params
end
QueryDiagramHom{T}(shape_map::F, diagram_map::Φ, precomposed_diagram::D,params::Params) where
{T,C,F<:FinFunctor,Φ<:FinTransformation,D<:Functor{<:FinCat,C},Params<:AbstractDict} =
QueryDiagramHom{T,C,F,Φ,D,Params}(shape_map, diagram_map, precomposed_diagram,params) 

get_params(f::QueryDiagramHom) = f.params
get_params(f::DiagramHom) = Dict()

function QueryDiagramHom{T}(params::Params,args...) where {T,Params<:AbstractDict}
  dh = DiagramHom{T}(args...)
  QueryDiagramHom{T}(dh,params)
end
QueryDiagramHom{T}(dh::DiagramHom{T},params::Params) where {T,Params<:AbstractDict} =
  QueryDiagramHom{T}(dh.shape_map,dh.diagram_map,dh.precomposed_diagram,params)
"""Convert the diagram category in which a diagram hom is being viewed."""
DiagramHom{T}(f::QueryDiagramHom) where T =
  QueryDiagramHom{T}(f.shape_map, f.diagram_map, f.precomposed_diagram,get_params(f))


#Note there's currently no composition of QueryDiagramHoms.

#This and some others can probably be dispatched to just querydiagramhoms?
function compose(f::DiagramHom{T}, F::Functor, params;kw...) where T
  whiskered = param_compose(diagram_map(f),F,params)
  DiagramHom{T}(shape_map(f), whiskered,
                compose(f.precomposed_diagram, F; kw...))
end

"""Whisker a partially natural transformation with a functor ``H``,
given any needed parameters specifying the functions in ``H``'s codomain
which the whiskered result should map to. Currently assumes
the result will be a totally defined transformation.
"""
function param_compose(α::FinTransformation, H::Functor,params)
F, G = dom(α), codom(α)
new_components = mapvals(pairs(components(α));keys=true) do i,f
  compindex = ob(dom(F),i)
  #allow non-strictness because of possible pointedness
  s, t = ob_map(compose(F,H,strict=false),compindex), 
  ob_map(compose(G,H,strict=false),compindex)
  if head(f) == :zeromap
  func = params[i]
  FinDomFunction(func,s,t)
  #may need to population params with identities
  else
  func = haskey(params,i) ? SetFunction(params[i],t,t) : SetFunction(identity,t,t)
  hom_map(H,f)⋅func
  end
end
FinTransformation(new_components,compose(F, H, strict=false), compose(G, H, strict=false))
end
"""
Compose a diagram with parameters with a functor. 
The result is not evaluated, so the functor may remain
partially defined with parameters still to be filled in.
"""
function compose(d::QueryDiagram{T},F::Functor; kw...) where T
  D = diagram(d)
  partial = compose(D,F;strict=false) #cannot be evaluated on the keys of params yet
  #Get the FinDomFunctions in the range of F that must be plugged into
  #the Functions in params
  params = d.params
  mors = hom_generators(codom(D))
  morfuns = map(x->hom_map(F,x),mors)
  params_new = Dict{keytype(params),FinDomFunction}()
  for (n,f) in params #Calculate the intended value of the composition on n
    domain = ob_map(partial,dom(hom(dom(partial),n)))
    codomain = ob_map(partial,codom(hom(dom(partial),n)))
    params_new[n] =
      FinDomFunction(f(morfuns...),domain,codomain)
  end
  #This will now contain a composite functor which can't directly be hom-mapped; ready to be forced.
  QueryDiagram{T}(partial,params_new)
end

function force(F::FinDomFunctor, params,Obtype::Type=Any, Homtype::Type=Any)
  C = dom(F)
  FinDomFunctor(
    make_map(x -> ob_map(F, x), ob_generators(C), Obtype),
    make_map(hom_generators(C), Homtype) do f 
     haskey(params,hom_generator_name(C,f)) ? params[hom_generator_name(C,f)] : hom_map(F,f) end , 
    C)
end

###New data types for complex queries
#####################################

""" Conjunctive query over schema ``C``.

The diagram comprising the query specifies a finite limit.
"""
const ConjQuery{C<:FinCat} = Diagram{op,C}

""" Gluing or agglomerative query over schema ``C``.

The diagram comprising the query specifies a finite colimit. In the important
special case that the diagram has discrete shape, it specifies a finite
coproduct and the query is called "linear" or "disjunctive".
"""
const GlueQuery{C<:FinCat} = Diagram{id,C}

""" "Gluc query" (gluing of conjunctive queries) over schema ``C``.

The diagram of diagrams comprising the query specifies a finite colimit of
finite limits. In the important special case that the outer diagram has discrete
shape, it specifies a finite coproduct of finite limits and the query is called
a "duc query" (disjoint union of conjunctive queries).
"""
const GlucQuery{C<:FinCat} = Diagram{id,<:TypeCat{<:Diagram{op,C}}}

"""
A contravariant data migration whose functor ``F`` may not be fully defined. Instead,
the migration ``F⋅X`` for an acset ``X`` can only be constructed once we have access
to ``X``'s attribute types. The dictionary of parameters contains anonymous 
functions acting on ``X``'s attributes using Julia functions defined on 
these attribute types.
"""
#The same, except for the supertype and the variance parameter T, as a QueryDiagram in older code.
#(Instead, `C` itself is probably a category of queries, which thus contain the information of T further down.)
struct DataMigration{F<:FinDomFunctor,Params<:AbstractDict} <: ContravariantMigration{F}
  functor::F
  params::Params
end
DataMigration(F::FinDomFunctor) = DataMigration(F,Dict{Any,Union{}}())
DataMigration(h::SimpleDiagram) = DataMigration(diagram(h))
DataMigration(h::QueryDiagram) = DataMigration(diagram(h),h.params)

const ComplexDeltaMigration{F<:FinFunctor,Params<:AbstractDict} = DataMigration{F,Params}

""" Schema-level functor defining a contravariant data migration using conjunctive queries.
"""
const ConjSchemaMigration{D<:FinCat,C<:FinCat} =
  ContravariantMigration{<:FinDomFunctor{D,<:TypeCat{<:ConjQuery{C}}}}

""" Schema-level functor defining a contravariant data migration using gluing queries.
"""
const GlueSchemaMigration{D<:FinCat,C<:FinCat} =
  ContravariantMigration{<:FinDomFunctor{D,<:TypeCat{<:GlueQuery{C}}}}

""" Schema-level functor defining a contravariant data migration using gluc queries.
"""
const GlucSchemaMigration{D<:FinCat,C<:FinCat} =
  ContravariantMigration{<:FinDomFunctor{D,<:TypeCat{<:GlucQuery{C}}}}


  # Contravariant migration
#########################
function migrate(X::FinDomFunctor,M::ComplexDeltaMigration)
    F = functor(M)
    tgt_schema = dom(F)
    src_schema = get_src_schema(F)
    obs = make_map(ob_generators(tgt_schema)) do c
      Fc = ob_map(F,c)
      ob_map(X,Fc)
    end
    homs = hom_generators(src_schema)
    homfuns = map(x->hom_map(X,x),homs)
    params = M.params
    funcs = make_map(hom_generators(tgt_schema)) do f
      Ff, c, d = hom_map(F, f), dom(tgt_schema, f), codom(tgt_schema, f)
      if head(Ff) == :zeromap
        domain = obs[c]
        codomain = obs[d]
        FinDomFunction(params[nameof(f)](homfuns...),domain,codomain)
      else 
        hom_map(X,Ff)
      end
    end
    FinDomFunctor(
        obs,
        funcs,
        dom(F),
        codom(X)
      )
  end

  """
Get the source schema of a data migration functor, recursing in the case
that the proximate codomain is a diagram category.
"""
function get_src_schema(F::Functor{<:Cat,<:TypeCat{<:Diagram}})
  obs = collect(keys(F.ob_map))
    length(obs) > 0 || return FinCat(0)
    get_src_schema(diagram(ob_map(F,obs[1])))
end
get_src_schema(F::Functor{<:Cat,<:FinCat}) = codom(F)


# Conjunctive migration
#----------------------
function migrate(X::FinDomFunctor, M::ConjSchemaMigration;
    return_limits::Bool=false, tabular::Bool=false)
F = functor(M)
tgt_schema = dom(F)
homs = hom_generators(get_src_schema(F))
homfuns = map(x->hom_map(X,x), homs)
params = M.params
limits = make_map(ob_generators(tgt_schema)) do c
Fc = ob_map(F, c)
J = shape(Fc)
# Must supply object/morphism types to handle case of empty diagram.
diagram_types = if c isa AttrTypeExpr
(TypeSet, SetFunction)
elseif isempty(J)
(FinSet{Int}, FinFunction{Int})
else
(SetOb, FinDomFunction{Int})
end
# Make sure the diagram to be limited is a FinCat{<:Int}.
# Disable domain check because acsets don't store schema equations.
k = dom_to_graph(diagram(force(compose(Fc, X, strict=false), diagram_types...)))
lim = limit(k,SpecializeLimit(fallback=ToBipartiteLimit()))
if tabular
names = (ob_generator_name(J, j) for j in ob_generators(J))
TabularLimit(lim, names=names)
else
lim
end
end
funcs = make_map(hom_generators(tgt_schema)) do f
Ff, c, d = hom_map(F, f), dom(tgt_schema, f), codom(tgt_schema, f)
f_params = haskey(params,nameof(f)) ? Dict(nameof(codom(tgt_schema,f)) => params[nameof(f)](homfuns...)) : Dict()
# Disable domain check for same reason.
# Hand the Julia function form of the not-yet-defined components to compose
universal(compose(Ff, X, f_params,strict=false), limits[c], limits[d])
end
Y = FinDomFunctor(mapvals(ob, limits), funcs, tgt_schema)
return_limits ? (Y, limits) : Y
end

# Gluing migration
#-----------------

function migrate(X::FinDomFunctor, M::GlueSchemaMigration)
F = functor(M)
tgt_schema = dom(F)
homs = hom_generators(get_src_schema(F))
homfuns = map(x->hom_map(X,x), homs)
params = M.params
colimits = make_map(ob_generators(tgt_schema)) do c
Fc = ob_map(F, c)
diagram_types = c isa AttrTypeExpr ? (TypeSet, SetFunction) :
(FinSet{Int}, FinFunction{Int})
k = dom_to_graph(diagram(force(compose(Fc, X, strict=false), diagram_types...)))
colimit(k,SpecializeColimit())
end
funcs = make_map(hom_generators(tgt_schema)) do f
Ff, c, d = hom_map(F, f), dom(tgt_schema, f), codom(tgt_schema, f)
#Get a single anonymous function, if there's one needed and 
#the domain of Ff's shape map is a singleton, or else get a dict
#of them if the domain is a non-singleton and there are any.
f_params = haskey(params,f) ? map(x->x(homfuns...),params[f]) : 
   isempty(get_params(Ff)) ? Dict() : mapvals(x->x(homfuns...),get_params(Ff))
universal(compose(Ff, X, f_params,strict=false), colimits[c], colimits[d])
end
FinDomFunctor(mapvals(ob, colimits), funcs, tgt_schema)
end

# Gluc migration
#---------------

function migrate(X::FinDomFunctor, M::GlucSchemaMigration)
F = functor(M)
tgt_schema = dom(F)
homs = hom_generators(get_src_schema(F))
homfuns = map(x->hom_map(X,x), homs)
colimits_of_limits = make_map(ob_generators(tgt_schema)) do c
Fc = ob_map(F, c)
m = Fc isa QueryDiagram ? DataMigration(diagram(Fc),Fc.params) : DataMigration(diagram(Fc))
Fc_set, limits = migrate(X, m, return_limits=true)
(colimit(dom_to_graph(Fc_set), SpecializeColimit()), Fc_set, limits)
end
funcs = make_map(hom_generators(tgt_schema)) do f
Ff, c, d = hom_map(F, f), dom(tgt_schema, f), codom(tgt_schema, f)
Fc_colim, Fc_set, Fc_limits = colimits_of_limits[c]
Fd_colim, Fd_set, Fd_limits = colimits_of_limits[d]
Ff_params = Ff isa DiagramHom ? get_params(Ff) : Dict{Int,Int}()
component_funcs = make_map(ob_generators(dom(Fc_set))) do j
j′, Ffⱼ = ob_map(Ff, j)
Ffⱼ_params = Ffⱼ isa DiagramHom ? 
haskey(Ff_params,nameof(j)) ? 
Dict(only(keys(components(diagram_map(Ffⱼ))))=>Ff_params[nameof(j)](homfuns...)) :
mapvals(x->x(homfuns...),get_params(Ffⱼ)) : Dict{Int,Int}()
universal(compose(Ffⱼ, X, Ffⱼ_params,strict=false), 
   Fc_limits[j], Fd_limits[j′])
end
Ff_set = DiagramHom{id}(shape_map(Ff), component_funcs, Fc_set, Fd_set)
universal(Ff_set, Fc_colim, Fd_colim)
end
FinDomFunctor(mapvals(ob∘first, colimits_of_limits), funcs, tgt_schema)
end


const ConjMigrationFunctor{Dom,Codom} = DataMigrationFunctor{Dom,Codom,<:ConjSchemaMigration}
const GlueMigrationFunctor{Dom,Codom} = DataMigrationFunctor{Dom,Codom,<:GlueSchemaMigration}
const GlucMigrationFunctor{Dom,Codom} = DataMigrationFunctor{Dom,Codom,<:GlucSchemaMigration}

""" Interpret conjunctive data migration as a colimit of representables.

Given a conjunctive data migration (a functor `J → Diag{op}(C)`) and the Yoneda
embedding for `C` (a functor `op(C) → C-Set` computed via [`yoneda`](@ref)),
take colimits of representables to construct a `op(J)`-shaped diagram of C-sets.

Since every C-set is a colimit of representables, this is a generic way of
constructing diagrams of C-sets.
"""
function colimit_representables(M::DeltaSchemaMigration, y)
  compose(op(functor(M)), y)
end
function colimit_representables(M::ConjSchemaMigration, y)
  F = functor(M)
  J = dom(F)
  #Get the constructor for a C-set.
  ACS = constructor(ob_map(y,first(ob_generators(dom(y)))))
  colimits = make_map(ob_generators(J)) do j
    Fj = dom_to_graph(diagram(ob_map(F, j))) #a diagram K to C
    clim_diag = compose(op(Fj), y) #K^op to C^op to C-Set
    # modify the diagram we take a colimit of to concretize some vars
    
    params = ob_map(F,j) isa SimpleDiagram ? Dict() : ob_map(F,j).params
    G, om, hm = [f(clim_diag) for f in [graph ∘ dom, ob_map, hom_map]]
    for (i,val) in collect(params)
      v = add_vertex!(G; vname=Symbol("param$i"))
      add_edge!(G, vertex_named(G,i), v, ename=Symbol("param$i"))
      at = nameof(ob_map(Fj, i)) # attribute type name 
      h = only(homomorphisms(ob_map(clim_diag,i), ACS(); initial=Dict(at=>[val])))
      push!(om, ACS())
      push!(hm, h)
    end
    updated_diagram = FinDomFunctor(om, hm, FinCat(G), codom(clim_diag))
    colimit(updated_diagram) # take colimit
  end
  homs = make_map(hom_generators(J)) do f
    Ff, j, k = hom_map(F, f), dom(J, f), codom(J, f)
    universal(compose(op(Ff), y), colimits[k], colimits[j])
  end
  FinDomFunctor(mapvals(ob, colimits), homs, op(J))
end

end

