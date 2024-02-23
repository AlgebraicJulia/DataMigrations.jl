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
import Catlab: ob_map, hom_map, functor
using Catlab.CategoricalAlgebra.FinCats: make_map, mapvals, presentation_key, FinCatPresentation, FinDomFunctorMap
import Catlab.CategoricalAlgebra.FinCats: force
using Catlab.CategoricalAlgebra.Chase: collage, crel_type, pres_to_eds, add_srctgt, chase
using Catlab.CategoricalAlgebra.FinSets: VarSet
using Catlab.CategoricalAlgebra.Sets: SetFunctionCallable
import Catlab.CategoricalAlgebra.FunctorialDataMigrations: migrate, migrate!, AbstractDataMigration, ContravariantMigration, DeltaSchemaMigration
import Catlab.CategoricalAlgebra.Diagrams: DiagramHom
using MLStyle: @match

#Extra data structures for fancy diagrams and diagram homs,
#and their interaction with ordinary functors and nats.
#########################################################

""" 
A diagram representing a (conjunctive, duc, gluing, or gluc) query.

Besides the diagram functor itself, a `QueryDiagram` contains a 
dictionary `params` of query parameters. 
The keys of `params` are the `hom_generators`
of the target schema `C` on which the diagram is not fully defined
until a migration is executed. The values are either `Function`s
or constants. If `Function`s, then these values will have one
argument for each `hom_generator` of the target schema `D` 
and return a further function of one argument.

When an `ACSet` ``X`` is migrated via a `QueryDiagram`, 
the `Function`s in `params` are evaluated on the 
`FinDomFunction`s in ``X``'s range, and the resulting
one-variable functions are either pasted directly into the 
migrated `ACSet` ``Y``, or else composed with intermediate
`FinDomFunction`s defined by migrating ``X`` using only
the inner `diagram`. If the keys of `params` are constants
then ``Y`` will receive constant attributes at the 
corresponding values.
"""
struct QueryDiagram{T,C<:Cat,D<:Functor{<:FinCat,C},
                    Params<:AbstractDict} <: Diagram{T,C,D}
  diagram::D
  params::Params
end
"""
    QueryDiagram{T}(F,params)

Construct a `QueryDiagram` based on the `Functor` `F`
and with parameter dictionary `params`. 

The type parameter
`T` may be `id`, `op`, or possibly `co` or `Any`, though not
all functionality is defined for `co` and not all functionality
is definable for `Any`. Other type parameters are inferred from 
the type of `F`. The type `C` of the codomain `F`
will in practice be a subtype of `FinCat` or of 
`Diagram``{T}`. 
"""
QueryDiagram{T}(F::D, params::P) where {T,C<:Cat,D<:Functor{<:FinCat,C},P} =
  QueryDiagram{T,C,D,P}(F, params)
"""
    force(d::QueryDiagram,[args...])

Force-evaluate the `d.diagram` for a `QueryDiagram` `d`.
  
The result is a `SimpleDiagram`, and in particular
the inner call to `force` attempts to use `d.params`
to produce a fully-defined `FinDomFunctor`.
"""
force(d::QueryDiagram{T},args...) where T =
  SimpleDiagram{T}(force(diagram(d),d.params,args...))

"""
A `DiagramHom` that may be partially-defined, to be evaluated later
using the dictionary `params` of parameters.

As with [`QueryDiagram`](@ref)s, `params` will be a dictionary
of `Function`s or perhaps constants. A `QueryDiagramHom`
is expected to live inside a [`DataMigration`](@ref) `M` and
to be fully evaluated whenever [`migrate`](@ref) is called
on `M` and some `ACSet` `X`. 

How this works is that the partially-defined `DiagramHom`
consisting of `shape_map`, `diagram_map`, and `precomposed_diagram`
is whiskered with `X` (except where it's undefined), 
and then the functions in `params` are used to fill in the gaps.

See also [`QueryDiagram`](@ref), [`param_compose`](@ref)
"""
struct QueryDiagramHom{T,C<:Cat,F<:FinFunctor,Φ<:FinTransformation,D<:Functor{<:FinCat,C},Params<:AbstractDict}<:DiagramHom{T,C}
  shape_map::F
  diagram_map::Φ
  precomposed_diagram::D
  params::Params
end

"""
    QueryDiagramHom{T}(shape_map, diagram_map, precomposed_diagram, params)

Construct a `QueryDiagramHom` of variance `T` and fields the given arguments,
with further type parameters inferred.
"""
QueryDiagramHom{T}(shape_map::F, diagram_map::Φ, precomposed_diagram::D,params::Params) where
{T,C,F<:FinFunctor,Φ<:FinTransformation,D<:Functor{<:FinCat,C},Params<:AbstractDict} =
QueryDiagramHom{T,C,F,Φ,D,Params}(shape_map, diagram_map, precomposed_diagram,params) 


#XX: Maybe this isn't needed?
"""
    get_params(f::DiagramHom)

Get the parameters of `f`, if `f` is a `QueryDiagramHom`.
Otherwise return an empty `Dict`.
"""
get_params(f::QueryDiagramHom) = f.params
get_params(f::DiagramHom) = Dict()

"""
    QueryDiagramHom{T}(params,args...)

Build a `QueryDiagramHom` with variance `T` by first building a `DiagramHom`
using `args...`, then adding the `params`. 

There are many methods of `DiagramHom` allowing various calling conventions,
and this allows `QueryDiagramHom` to steal them all reasonably efficiently.
"""
function QueryDiagramHom{T}(params::Params,args...) where {T,Params<:AbstractDict}
  dh = DiagramHom{T}(args...)
  QueryDiagramHom{T}(dh,params)
end
QueryDiagramHom{T}(dh::DiagramHom{T},params::Params) where {T,Params<:AbstractDict} =
  QueryDiagramHom{T}(dh.shape_map,dh.diagram_map,dh.precomposed_diagram,params)
DiagramHom{T}(f::QueryDiagramHom) where T =
  QueryDiagramHom{T}(f.shape_map, f.diagram_map, f.precomposed_diagram,get_params(f))


#Note there's currently no composition of QueryDiagramHoms.

#This and some others can probably be dispatched to just querydiagramhoms?
"""
    compose(f::DiagramHom,F::Functor,params[;kw...])

Whisker a partially-defined `DiagramHom` with a 
`Functor`, using the dictionary `params` to fill in any gaps. 

While [`QueryDiagramHom`](@ref)s have internal `params` for a similar
purpose, it is sometimes necessary to borrow `params` from
a [`QueryDiagram`](@ref) or [`DataMigration`](@ref) containing `f`, which
is the functionality enabled here.

See also: `param_compose`
"""
function compose(f::DiagramHom{T}, F::Functor, params;kw...) where T
  whiskered = param_compose(diagram_map(f),F,params)
  DiagramHom{T}(shape_map(f), whiskered,
                compose(f.precomposed_diagram, F; kw...))
end

"""
    param_compose(α,H,params)

Whisker a partially natural transformation `α` with a functor `H`,
given any needed parameters `params` specifying the functions in 
`H`'s codomain which the whiskered result should map to. 

Currently assumes the result will be a totally defined transformation.
"""
function param_compose(α::FinTransformation, H::Functor,params)
  F, G = dom(α), codom(α)
  new_components = mapvals(pairs(components(α));keys=true) do i,f
    compindex = ob(dom(F),i)
    #allow non-strictness because of possible pointedness
    s, t = ob_map(compose(F,H),compindex), 
    ob_map(compose(G,H),compindex)
    if head(f) == :zeromap
      func = params[i]
      FinDomFunction(func,s,t)
    #may need to population params with identities
    else
      Hf = hom_map(H,f)
      func = haskey(params,i) ? SetFunction(params[i],codom(Hf),t) : SetFunction(identity,t,t)
      Hf⋅func
    end
  end
  FinTransformation(new_components,compose(F, H), compose(G, H))
end

"""
    compose(d::QueryDiagram,F::Functor[;kw...])

Lazily compose a diagram with parameters (see [QueryDiagram](@ref)) 
with a `Functor`. 

The result is not evaluated, so the 
returned `QueryDiagram` may remain partially defined with parameters 
still to be filled in.

See also: `force`, `QueryDiagram`
"""
function compose(d::QueryDiagram{T},F::Functor; kw...) where T
  D = diagram(d)
  partial = compose(D,F) #cannot be evaluated on the keys of params yet
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
  #This will now contain a composite functor which can't 
  #necessarily be hom-mapped; ready to be forced.
  QueryDiagram{T}(partial,params_new)
end

#Does the type guarantee definitely hold for empty collections?
"""
    force(F::FinDomFunctor,params,[Obtype=Any,Homtype=Any])

Force-evaluate a partially-defined `FinDomFunctor` by
using `Function`s in `params` to fill in undefined 
entries of `F`'s `hom_map`.

If `Obtype` and `Homtype` are specified, then the
returned functor is guaranteed to have exactly those
value types in its `ob_map` and `hom_map`.
"""
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

""" 
A conjunctive query over schema ``C``.

When this query is used as part of a call
to `migrate`, the diagram will be composed 
with an acset and its limit will then
be computed in ``Set``.

See also: `GlueQuery`, `GlucQuery`
"""
const ConjQuery{C<:FinCat} = Diagram{op,C}

""" Gluing or agglomerative query over schema ``C``.

The diagram comprising the query specifies a finite colimit. In the important
special case that the diagram has discrete shape, it specifies a finite
coproduct and the query is called "linear" or "disjunctive".

See also: `ConjQuery`, `GlucQuery`
"""
const GlueQuery{C<:FinCat} = Diagram{id,C}

""" "Gluc query" (gluing of conjunctive queries) over schema ``C``.

The diagram of diagrams comprising the query specifies a finite colimit of
finite limits. In the important special case that the outer diagram has discrete
shape, it specifies a finite coproduct of finite limits and the query is called
a "duc query" (disjoint union of conjunctive queries).

See also: `GlueQuery`, `GlucQuery`
"""
const GlucQuery{C<:FinCat} = Diagram{id,<:TypeCat{<:Diagram{op,C}}}

#The same, except for the supertype and the variance parameter T, as a QueryDiagram.
#In this case, the codomain of F is probably a category of queri
"""
A contravariant data migration whose underlying functor ``F`` may not be fully defined. 

Instead, the migration `F⋅X` for an acset `X` can only be constructed once 
we have access to `X`'s attributes and homs. The dictionary of parameters contains anonymous 
functions acting on ``X``'s attributes using Julia functions defined on 
these attribute types.
"""
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
#what the hell happened to the indentation

# Conjunctive migration
#----------------------
function migrate(X::FinDomFunctor, M::ConjSchemaMigration;
  return_limits::Bool=false, tabular::Bool=false)
  F = functor(M)
  tgt_schema = dom(F)
  homs = hom_generators(get_src_schema(F))
  homfuns = map(x -> hom_map(X, x), homs)
  params = M.params
  limits = make_map(ob_generators(tgt_schema)) do c
    Fc = ob_map(F, c)
    J = shape(Fc)
    # Make sure the diagram to be limited has loose enough types
    diagram_types = isempty(J) ? (FinSet{Int}, FinFunction{Int}) : (SetOb,FinDomFunction{Int})
    k = dom_to_graph(diagram(force(compose(Fc, X))), diagram_types...)
    lim = limit(k, SpecializeLimit(fallback=ToBipartiteLimit()))
    if tabular
      names = (ob_generator_name(J, j) for j in ob_generators(J))
      TabularLimit(lim, names=names)
    else
      lim
    end
  end
  funcs = make_map(hom_generators(tgt_schema)) do f
    Ff, c, d = hom_map(F, f), dom(tgt_schema, f), codom(tgt_schema, f)
    if haskey(params, nameof(f)) 
      #This assumes that `d` is an AttrType and that (thus, as of Feb '24) it is mapped to a trivial diagram, hence the `only` call.
      #I'm not sure what this will look like once AttrTypes can be mapped to nontrivial diagrams; maybe the value at `nameof(f)` will
      #itself be a dict.
      f_params = Dict(nameof(only(collect_ob(ob_map(F,d)))) => params[nameof(f)](homfuns...))
    else 
      f_params = Dict()
    end 
    # Disable domain check for same reason.
    # Hand the Julia function form of the not-yet-defined components to compose
    universal(compose(Ff, X, f_params), limits[c], limits[d])
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
  homfuns = map(x -> hom_map(X, x), homs)
  params = M.params
  colimits = make_map(ob_generators(tgt_schema)) do c
    Fc = ob_map(F, c)
    diagram_types = c isa AttrTypeExpr ? (TypeSet, SetFunction) :
                    (FinSet{Int}, FinFunction{Int})
    k = dom_to_graph(diagram(force(compose(Fc, X), diagram_types...)))
    colimit(k, SpecializeColimit())
  end
  funcs = make_map(hom_generators(tgt_schema)) do f
    Ff, c, d = hom_map(F, f), dom(tgt_schema, f), codom(tgt_schema, f)
    #Get a single anonymous function, if there's one needed and 
    #the domain of Ff's shape map is a singleton, or else get a dict
    #of them if the domain is a non-singleton and there are any.
    f_params = haskey(params, f) ? map(x -> x(homfuns...), params[f]) :
               isempty(get_params(Ff)) ? Dict() : mapvals(x -> x(homfuns...), get_params(Ff))
    universal(compose(Ff, X, f_params), colimits[c], colimits[d])
  end
  FinDomFunctor(mapvals(ob, colimits), funcs, tgt_schema)
end

# Gluc migration
#---------------
"""
    migrate(M,X)

do the dang migration
"""
function migrate(X::FinDomFunctor, M::GlucSchemaMigration)
  F = functor(M)
  tgt_schema = dom(F)
  homs = hom_generators(get_src_schema(F))
  homfuns = map(x -> hom_map(X, x), homs)
  colimits_of_limits = make_map(ob_generators(tgt_schema)) do c
    Fc = ob_map(F, c)
    m = Fc isa QueryDiagram ? DataMigration(diagram(Fc), Fc.params) : DataMigration(diagram(Fc))
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
                   haskey(Ff_params, nameof(j)) ?
                   Dict(only(keys(components(diagram_map(Ffⱼ)))) => Ff_params[nameof(j)](homfuns...)) :
                   mapvals(x -> x(homfuns...), get_params(Ffⱼ)) : Dict{Int,Int}()
      universal(compose(Ffⱼ, X, Ffⱼ_params),
        Fc_limits[j], Fd_limits[j′])
    end
    Ff_set = DiagramHom{id}(shape_map(Ff), component_funcs, Fc_set, Fd_set)
    universal(Ff_set, Fc_colim, Fd_colim)
  end
  FinDomFunctor(mapvals(ob ∘ first, colimits_of_limits), funcs, tgt_schema)
end


const ConjMigrationFunctor{Dom,Codom} = DataMigrationFunctor{Dom,Codom,<:ConjSchemaMigration}
const GlueMigrationFunctor{Dom,Codom} = DataMigrationFunctor{Dom,Codom,<:GlueSchemaMigration}
const GlucMigrationFunctor{Dom,Codom} = DataMigrationFunctor{Dom,Codom,<:GlucSchemaMigration}

""" Interpret conjunctive data migration as a colimit of representables.

Given a conjunctive data migration (a functor `J → Diag{op}(C)`) and the Yoneda
embedding for `C` (a functor `op(C) → C-Set` computed via `yoneda`),
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

