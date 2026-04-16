"""
Contravariant complex data migrations.
"""
module Migrations

export migrate,migrate!,colimit_representables, QueryDiagram, DataMigration, colimit_representables, force, compose, DiagramHom, QueryDiagramHom

using ACSets
using ACSets.DenseACSets: constructor, datatypes
using Catlab
using GATlab: getvalue
using Catlab.Theories: ob, hom, dom, codom, attr, AttrTypeExpr, ⋅
import Catlab.Theories: compose
import Catlab: id, ob_map, hom_map, functor, gen_map
using Catlab.BasicSets: TaggedElem, TypeSet
using Catlab.CategoricalAlgebra.Cats.FinCats: FinCatPresentation
using Catlab.CategoricalAlgebra.Cats.FinCats.FinCatPres: presentation_key
using Catlab.CategoricalAlgebra.Cats.FinFunctors: make_map, mapvals, FinDomFunctorMap
using Catlab.CategoricalAlgebra.SetCats.SkelFinSetCat.Limits: indexed_universal, FinSetIndexedLimit
using Catlab.CategoricalAlgebra.SetCats.SkelFinSetCat: SkelFinSet
using Catlab.CategoricalAlgebra.SetCats.SkelFinSetCat.Colimits: composite_universal
using Catlab.BasicSets.FinSetInts: FinSetInt
import Catlab: force
using Catlab.CategoricalAlgebra.Chase: collage, crel_type, pres_to_eds, add_srctgt, chase
import Catlab.CategoricalAlgebra.FunctorialDataMigrations: migrate, migrate!, AbstractDataMigration, ContravariantMigration, DeltaSchemaMigration
import Catlab.CategoricalAlgebra.Diagrams: DiagramHom
using GATlab: Dispatch
using MLStyle: @match
ob_generator_name(C, x) = nameof(x)
hom_generator_name(C, f) = nameof(f)
_lookup_generator(xs, name::Symbol) = let matches = [x for x in collect(xs) if nameof(x) == name]
  length(matches) == 1 || error("No unique generator named $name")
  only(matches)
end
_resolve_ob_key(F, x::Symbol) = _lookup_generator(ob_generators(dom(F)), x)
_resolve_ob_key(F, x) = applicable(ob_map, F, x) ? x :
                        _lookup_generator(ob_generators(dom(F)), nameof(x))
_resolve_hom_key(F, x::Symbol) = _lookup_generator(hom_generators(dom(F)), x)
_resolve_hom_key(F, x) = applicable(gen_map, F, x) ? x :
                         _lookup_generator(hom_generators(dom(F)), nameof(x))
Catlab.ob_map(F::FunctorFinDom, x::Symbol) = ob_map(F, _resolve_ob_key(F, x))
Catlab.hom_map(F::FunctorFinDom, x::Symbol) = gen_map(F, _resolve_hom_key(F, x))
Catlab.hom_map(F::FunctorFinDom, x::GATlab.Models.SymbolicModels.GATExpr{:generator}) =
  gen_map(F, _resolve_hom_key(F, x))
typed_typecat(ObT, HomT) =
  Category(TypeCat{ObT,HomT}(Dispatch(Catlab.CategoricalAlgebra.Cats.Categories.ThCategory, [ObT, HomT])))
unwrap_tagged(x) = x isa TaggedElem ? getvalue(x) : x

function _diagram_freegraph_data(F::FunctorFinDom)
  C = dom(F)
  D = Category(codom(F))
  obs_gen = collect(ob_generators(C))
  obs = [ob_map(F, x) for x in obs_gen]
  obix = Dict(x => i for (i, x) in enumerate(obs_gen))
  homs = map(collect(hom_generators(C))) do h
    fh = hom_map(F, h)
    s, t = dom(C, h), codom(C, h)
    fs, ft = ob_map(F, s), ob_map(F, t)
    fh_dom, fh_cod = dom(D, fh), codom(D, fh)
    if fh_dom == fs && fh_cod == ft
      (fh, obix[s], obix[t])
    elseif fh_dom == ft && fh_cod == fs
      (fh, obix[t], obix[s])
    else
      error("Could not align mapped hom $h with diagram objects")
    end
  end
  (obs_gen=obs_gen, obs=obs, obix=obix, homs=homs, cat=D)
end
function _diagram_freegraph(F::FunctorFinDom)
  data = _diagram_freegraph_data(F)
  FreeGraph(data.obs, data.homs)
end
_diagram_freegraph(d::Diagram) = _diagram_freegraph(diagram(d))
_diagram_freegraph_data(d::Diagram) = _diagram_freegraph_data(diagram(d))

_query_path_symbols(f) = head(f) == :id ? Symbol[] :
                         head(f) == :compose ? error("Composite parameterized query paths are not yet supported here") :
                         [nameof(f)]

function _query_diagram_data(q)
  Fj = diagram(q)
  Cj = dom(Fj)
  data = Catlab.CategoricalAlgebra.Pointwise.FunctorialDataMigrations.Yoneda.DiagramData()
  fixed = Dict{Symbol,Any}(Symbol(k) => v for (k, v) in pairs(q.params))
  fixed_paths = Dict{Symbol,Pair{Symbol,Vector{Symbol}}}()
  for h in hom_generators(Cj)
    tgt = nameof(codom(Cj, h))
    if haskey(fixed, tgt)
      fixed_paths[tgt] = nameof(dom(Cj, h)) => _query_path_symbols(hom_map(Fj, h))
    end
  end
  for x in ob_generators(Cj)
    xname = nameof(x)
    if !(haskey(fixed, xname) && haskey(fixed_paths, xname))
      push!(data.reprs[nameof(ob_map(Fj, x))], xname)
    end
  end
  for h in hom_generators(Cj)
    tgt = nameof(codom(Cj, h))
    if !(haskey(fixed, tgt) && haskey(fixed_paths, tgt))
      push!(data.eqs,
            (nameof(dom(Cj, h)) => _query_path_symbols(hom_map(Fj, h))) =>
            (tgt => Symbol[]))
    end
  end
  for (k, v) in pairs(fixed)
    data.vals[get(fixed_paths, k, k => Symbol[])] = v
  end
  data
end

_query_apex(q, y::FunctorFinDom) =
  Catlab.CategoricalAlgebra.Pointwise.FunctorialDataMigrations.Yoneda.colimit_representables(
    _query_diagram_data(q), y)[2]

id(d::Catlab.CategoricalAlgebra.Cats.Diagrams.DiagramOp) =
  id[Catlab.CategoricalAlgebra.Cats.Diagrams.DiagramOpCat()](d)

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
diagram_kind(::typeof(id)) = :id
diagram_kind(::typeof(op)) = :op
diagram_kind(::Any) = :id

diagram_type(::typeof(id)) = DiagramId
diagram_type(::typeof(op)) = DiagramOp
diagram_type(::Any) = DiagramId

make_diagram(T, F::FunctorFinDom) = diagram_type(T)(F)
make_diagram_unit(T, C, x; shape=nothing) = munit(diagram_type(T), C, x; shape)
make_diagram_hom_unit(T, C, f; dom_shape=nothing, codom_shape=nothing) =
  munit(DiagramHom, C, f; dom_shape, codom_shape, cat=diagram_kind(T))

struct QueryDiagram{T,F<:FunctorFinDom,Params<:AbstractDict} <: Diagram
  fun::F
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
QueryDiagram{T}(fun::F, params::P) where {T,F<:FunctorFinDom,P<:AbstractDict} =
  QueryDiagram{T,F,P}(fun, params)
"""
    force(d::QueryDiagram,[args...])

Force-evaluate the `d.diagram` for a `QueryDiagram` `d`.

The result is a `SimpleDiagram`, and in particular
the inner call to `force` attempts to use `d.params`
to produce a fully-defined `FinDomFunctor`.
"""
force(d::QueryDiagram{T},args...) where T =
  make_diagram(T, force(diagram(d), d.params, args...))

force(d::DiagramId, args...) = DiagramId(force(diagram(d), args...))
force(d::DiagramOp, args...) = DiagramOp(force(diagram(d), args...))
force(d::DiagramCo, args...) = DiagramCo(force(diagram(d), args...))

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

See also [`QueryDiagram`](@ref)
"""
struct QueryDiagramHom{T,H<:DiagramHom,Params<:AbstractDict}
  hom::H
  params::Params
end

"""
    QueryDiagramHom{T}(shape_map, diagram_map, precomposed_diagram, params)

Construct a `QueryDiagramHom` of variance `T` and fields the given arguments,
with further type parameters inferred.
"""
QueryDiagramHom{T}(shape_map, diagram_map, precomposed_diagram::D, params::Params) where
{T,D<:Diagram,Params<:AbstractDict} =
  QueryDiagramHom{T}(DiagramHom(shape_map, diagram_map, precomposed_diagram), params)

QueryDiagramHom{T}(dh::H, params::Params) where {T,H<:DiagramHom,Params<:AbstractDict} =
  QueryDiagramHom{T,H,Params}(dh, params)

_trivial_query_ob(q::QueryDiagram) = _trivial_query_ob(only(collect_ob(diagram(q))))
_trivial_query_ob(q::Diagram) = _trivial_query_ob(only(collect_ob(q)))
_trivial_query_ob(x) = x


#XX: Maybe this isn't needed?
"""
    get_params(f::DiagramHom)

Get the parameters of `f`, if `f` is a `QueryDiagramHom`.
Otherwise return an empty `Dict`.
"""
get_params(f::QueryDiagramHom) = f.params
get_params(f::DiagramHom) = Dict()

Catlab.shape_map(f::QueryDiagramHom) = Catlab.shape_map(f.hom)
Catlab.diagram_map(f::QueryDiagramHom) = Catlab.diagram_map(f.hom)
precomposed_diagram(f::QueryDiagramHom) = f.hom.precomposed_diagram
Catlab.Theories.dom(f::QueryDiagramHom) = Catlab.Theories.dom(f.hom)
Catlab.Theories.codom(f::QueryDiagramHom) = Catlab.Theories.codom(f.hom)
Catlab.ob_map(f::QueryDiagramHom, x) = ob_map(f.hom, x)
Catlab.hom_map(f::QueryDiagramHom, x) = hom_map(f.hom, x)
Catlab.collect_ob(f::QueryDiagramHom) = collect_ob(f.hom)
Catlab.collect_hom(f::QueryDiagramHom) = collect_hom(f.hom)

"""
    QueryDiagramHom{T}(params,args...)

Build a `QueryDiagramHom` with variance `T` by first building a `DiagramHom`
using `args...`, then adding the `params`. 

There are many methods of `DiagramHom` allowing various calling conventions,
and this allows `QueryDiagramHom` to steal them all reasonably efficiently.
"""
function QueryDiagramHom{T}(params::Params,args...) where {T,Params<:AbstractDict}
  dh = DiagramHom(args...)
  QueryDiagramHom{T}(dh,params)
end
DiagramHom(f::QueryDiagramHom) = f.hom


"""
    param_compose(α,H,params)

Whisker a partially natural transformation `α` with a functor `H`,
given any needed parameters `params` specifying the functions in 
`H`'s codomain which the whiskered result should map to. 

Currently assumes the result will be a totally defined transformation.
"""
function param_compose(α::FinTransformation, H::FunctorFinDom, params)
  F, G = dom(α), codom(α)
  FH = compose_partial(F, H)
  GH = compose_partial(G, H)
  # Wrap raw model objects (e.g. FinSetInt) from ob_map into AbsSet
  _wrap(o) = o isa AbsSet ? o :
             o isa ACSets.ACSet ? o :
             o isa TaggedElem ? o :
             FinSet(length(o))
  _id_component(o) = o isa TaggedElem ? o :
                     o isa FinSet ? FinFunction(o) :
                     o isa AbsSet ? SetFunction(o) :
                     id(o)
  _param_haskey(ps, k) = haskey(ps, k) || haskey(ps, nameof(k))
  _param_get(ps, k) = haskey(ps, k) ? ps[k] : ps[nameof(k)]
  new_components = mapvals(pairs(components(α));keys=true) do i,f
    compindex = i  # generator is already an Ob in Catlab 0.17
    #allow non-strictness because of possible pointedness
    s, t = _wrap(ob_map(FH, compindex)),
    _wrap(ob_map(GH, compindex))
    if head(f) == :zeromap
      func = _param_get(params, i)
      if t isa TaggedElem
        vals_raw = [func(x) for x in collect(s)]
        ElT = isempty(vals_raw) ? Any : typejoin(typeof.(vals_raw)...)
        vals = ElT[v for v in vals_raw]
        TaggedElem(FinDomFunction(vals, SetOb(TypeSet(ElT))), GATlab.gettag(t))
      else
        FinDomFunction(func, s, t)
      end
    #may need to population params with identities
    else
      Hf = head(f) == :id ? _id_component(s) : hom_map(H, presentation_key(f))
      if _param_haskey(params, i)
        if Hf isa TaggedElem
          Hf′ = getvalue(Hf)
          func = SetFunction(_param_get(params, i), codom(Hf′), codom(Hf′))
          TaggedElem(Catlab.BasicSets.postcompose(Hf′, func), GATlab.gettag(Hf))
        elseif t isa TaggedElem
          vals_raw = [_param_get(params, i)(Hf(x)) for x in collect(dom(Hf))]
          ElT = isempty(vals_raw) ? Any : typejoin(typeof.(vals_raw)...)
          vals = ElT[v for v in vals_raw]
          TaggedElem(FinDomFunction(vals, SetOb(TypeSet(ElT))), GATlab.gettag(t))
        else
          func = SetFunction(_param_get(params, i), codom(Hf), t)
          compose[SetC()](Hf, func)
        end
      else
        Hf  # composing with identity is a no-op
      end
    end
  end
  # check=false: AttrType components may be TaggedElem placeholders that
  # are not valid morphisms in the collage category (Catlab 0.17 limitation).
  # They are handled specially by _attr_universal downstream.
  FinTransformationMap(new_components, FH, GH; check=false)
end

#Note there's currently no composition of QueryDiagramHoms.

function _compose_nested_diagram_functor(D::FunctorFinDom, F::FunctorFinDom, homfuns)
  C = dom(D)
  obs = make_map(ob_generators(C)) do x
    force(compose(ob_map(D, x), F))
  end
  _param_haskey(ps, k) = haskey(ps, k) || haskey(ps, nameof(k))
  _param_get(ps, k) = haskey(ps, k) ? ps[k] : ps[nameof(k)]
  homs = make_map(hom_generators(C)) do h
    fh = hom_map(D, h)
    if fh isa QueryDiagramHom
      ps = isempty(get_params(fh)) ? Dict{Any,Any}() : mapvals(x -> x(homfuns...), get_params(fh))
      compose(fh, F, ps)
    elseif fh isa DiagramHom
      compose(fh, F, Dict{Any,Any}())
    else
       Hf = head(fh) == :id ? id(only(collect_ob(obs[dom(C, h)]))) :
            hom_map(F, presentation_key(fh))
      s = obs[dom(C, h)]
      t = obs[codom(C, h)]
      DataMigrations.DiagrammaticPrograms.make_query_hom(get_src_schema(F), Hf, s, t)
    end
  end
  ObT = isempty(obs) ? Any : typejoin(typeof.(values(obs))...)
  HomT = isempty(homs) ? Any : typejoin(typeof.(values(homs))...)
  cod = typed_typecat(ObT, HomT)
  FinDomFunctor(obs, homs, C, cod)
end

#This and some others can probably be dispatched to just querydiagramhoms?
"""
    compose(f::DiagramHom,F::Functor,params[;kw...])

Whisker a partially-defined `DiagramHom` with a 
`Functor`, using the dictionary `params` to fill in any gaps. 

While [`QueryDiagramHom`](@ref)s have internal `params` for a similar
purpose, it is sometimes necessary to borrow `params` from
a [`QueryDiagram`](@ref) containing `f`, which
is the functionality enabled here.
"""
function compose(f::Union{DiagramHom,QueryDiagramHom}, F::FunctorFinDom, params; kw...)
  base = f isa QueryDiagramHom ? DiagramHom(f) : f
  α = diagram_map(base)
  Fα, Gα = dom(α), codom(α)
  J = dom(Fα)
  if !isempty(ob_generators(J)) && any(i -> ob_map(Fα, i) isa Diagram, ob_generators(J))
    src_pres = presentation(getvalue(dom(F)))
    homs = hom_generators(get_src_schema(F))
    homfuns = map(x -> unwrap_tagged(hom_map(F, src_pres[presentation_key(x)])), homs)
    FH = _compose_nested_diagram_functor(Fα, F, homfuns)
    GH = _compose_nested_diagram_functor(Gα, F, homfuns)
    new_components = mapvals(pairs(components(α)); keys=true) do i, comp
      if comp isa QueryDiagramHom
        ps = isempty(get_params(comp)) ? Dict{Any,Any}() : mapvals(x -> x(homfuns...), get_params(comp))
        compose(comp, F, ps)
      elseif comp isa DiagramHom
        compose(comp, F, Dict{Any,Any}())
      else
        Hcomp = head(comp) == :id ? id(only(collect_ob(ob_map(FH, i)))) :
                hom_map(F, src_pres[presentation_key(comp)])
        DataMigrations.DiagrammaticPrograms.make_query_hom(get_src_schema(F), Hcomp,
                                                          ob_map(FH, i), ob_map(GH, i))
      end
    end
    whiskered = Transformation(FinTransformationMap(new_components, FH, GH; check=false))
    return DiagramHom(shape_map(base), whiskered, compose(base.precomposed_diagram, F; kw...))
  end
  whiskered = Transformation(param_compose(diagram_map(base), F, params))
  DiagramHom(shape_map(base), whiskered,
             compose(base.precomposed_diagram, F; kw...))
end

compose(f::DiagramHom, F::FunctorFinDom; kw...) =
  compose(f, F, Dict{Any,Any}(); kw...)

function _diagram_colimit_universal(f::DiagramHom, dom_colim, codom_colim)
  J = dom(shape_map(f))
  AC = Category(ACSetCategory(apex(codom_colim)))
  obs = Dict(j => i for (i, j) in enumerate(collect(ob_generators(codom(shape_map(f))))))
  cocone = Multicospan(apex(codom_colim), map(collect(ob_generators(J))) do j
    j′, g = ob_map(f, j)
    ιⱼ′ = legs(codom_colim)[obs[j′]]
    compose(AC, g, ιⱼ′)
  end)
  Catlab.CategoricalAlgebra.Pointwise.LimitsColimits.Colimits.pointwise_universal(
    ACSetCategory(apex(dom_colim)), dom_colim, cocone)
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
function compose(d::QueryDiagram{T},F::FunctorFinDom; kw...) where T
  D = diagram(d)
  partial = compose_partial(D, F) # cannot be evaluated on the keys of params yet
  #Get the FinDomFunctions in the range of F that must be plugged into
  #the Functions in params
  params = d.params
  mors = hom_generators(codom(D))
  src_pres = presentation(getvalue(dom(F)))
  morfuns = map(x -> unwrap_tagged(hom_map(F, src_pres[presentation_key(x)])), mors)
  params_new = Dict{keytype(params),Any}()
  partial_pres = presentation(getvalue(dom(partial)))
  for (n,f) in params #Calculate the intended value of the composition on n
    h = partial_pres[presentation_key(n)]
    domain = ob_map(partial, dom(h))
    codomain = ob_map(partial, codom(h))
    func = f(morfuns...)
    if codomain isa TaggedElem
      vals_raw = [func(x) for x in collect(domain)]
      ElT = isempty(vals_raw) ? Any : typejoin(typeof.(vals_raw)...)
      vals = ElT[v for v in vals_raw]
      params_new[n] = TaggedElem(FinDomFunction(vals, SetOb(TypeSet(ElT))), nameof(codom(h)))
    else
      domain = domain isa FinSet ? domain : FinSet(length(domain))
      params_new[n] = FinDomFunction(func, domain, codomain)
    end
  end
  #This will now contain a composite functor which can't 
  #necessarily be hom-mapped; ready to be forced.
  QueryDiagram{T}(partial,params_new)
end

function compose_partial(D::FunctorFinDom, F::FunctorFinDom)
  C = dom(D)
  obs = make_map(ob_generators(C)) do x
    fx = ob_map(D, x)
    ob_map(F, _resolve_ob_key(F, fx))
  end
  homs = make_map(hom_generators(C)) do h
    fx = hom_map(D, h)
    head(fx) == :zeromap ? fx :
    head(fx) == :id ? id(codom(F), obs[dom(C, h)]) :
    gen_map(F, _resolve_hom_key(F, fx))
  end
  ObT = isempty(obs) ? Any : typejoin(typeof.(values(obs))...)
  HomT = isempty(homs) ? Any : typejoin(typeof.(values(homs))...)
  cod = typed_typecat(ObT, HomT)
  FinDomFunctor(obs, homs, C, cod)
end

compose(d::DiagramId, F::FunctorFinDom; kw...) = DiagramId(compose_partial(diagram(d), F))
compose(d::DiagramOp, F::FunctorFinDom; kw...) = DiagramOp(compose_partial(diagram(d), F))
compose(d::DiagramCo, F::FunctorFinDom; kw...) = DiagramCo(compose_partial(diagram(d), F))

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
function force(F::FinDomFunctor, params::AbstractDict, Obtype::Type=Any, Homtype::Type=Any)
  C = dom(F)
  obs = make_map(x -> ob_map(F, x), ob_generators(C), Obtype)
  homs = make_map(hom_generators(C), Homtype) do f
    haskey(params, hom_generator_name(C, f)) ? params[hom_generator_name(C, f)] : hom_map(F, f)
  end
  cod = typed_typecat(
    isempty(obs) ? Any : typejoin(typeof.(values(obs))...),
    isempty(homs) ? Any : typejoin(typeof.(values(homs))...)
  )
  FinDomFunctor(obs, homs, C, cod)
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
const ConjQuery = DiagramOp

""" Gluing or agglomerative query over schema ``C``.

The diagram comprising the query specifies a finite colimit. In the important
special case that the diagram has discrete shape, it specifies a finite
coproduct and the query is called "linear" or "disjunctive".

See also: `ConjQuery`, `GlucQuery`
"""
const GlueQuery = DiagramId

""" "Gluc query" (gluing of conjunctive queries) over schema ``C``.

The diagram of diagrams comprising the query specifies a finite colimit of
finite limits. In the important special case that the outer diagram has discrete
shape, it specifies a finite coproduct of finite limits and the query is called
a "duc query" (disjoint union of conjunctive queries).

See also: `GlueQuery`, `GlucQuery`
"""
const GlucQuery = DiagramId

#The same, except for the supertype and the variance parameter T, as a QueryDiagram.
#In this case, the codomain of F is probably a category of queri
"""
A contravariant data migration whose underlying functor ``F`` may not be fully defined. 

Instead, the migration `F⋅X` for an acset `X` can only be constructed once 
we have access to `X`'s attributes and homs. The dictionary of parameters contains anonymous 
functions acting on ``X``'s attributes using Julia functions defined on 
these attribute types.
"""
struct DataMigration{F<:FunctorFinDom,Params<:AbstractDict} <: ContravariantMigration
  functor::F
  params::Params
end
DataMigration(F::FunctorFinDom) = DataMigration(F,Dict{Any,Union{}}())
DataMigration(h::Diagram) = DataMigration(diagram(h))
DataMigration(h::QueryDiagram) = DataMigration(diagram(h),h.params)

function migrate(X::ACSet, M::DataMigration; kw...)
  migrate(Catlab.CategoricalAlgebra.Cats.FinFunctors.FinDomFunctor(X; check=false), M; kw...)
end
function migrate(::Type{T}, X::ACSet, M::DataMigration; kw...) where T <: ACSet
  T(migrate(X, M; kw...))
end

const ComplexDeltaMigration = DataMigration

""" Schema-level functor defining a contravariant data migration using conjunctive queries.
"""
const ConjSchemaMigration = ContravariantMigration

""" Schema-level functor defining a contravariant data migration using gluing queries.
"""
const GlueSchemaMigration = ContravariantMigration

""" Schema-level functor defining a contravariant data migration using gluc queries.
"""
const GlucSchemaMigration = ContravariantMigration

# Contravariant migration
#########################

function migrate(X::FinDomFunctor,M::ComplexDeltaMigration)
    F = functor(M)
    tgt_schema = dom(F)
    # Check if this is actually a diagram-valued migration (conj/glue/gluc)
    gens = collect(ob_generators(tgt_schema))
    if !isempty(gens)
      q = ob_map(F, first(gens))
      if q isa Union{DiagramOp, Catlab.CategoricalAlgebra.Cats.Diagrams.DiagramId, DiagramCo} ||
         q isa QueryDiagram
        return _migrate_contravariant(X, M)
      end
    end
    src_schema = dom(X)
    src_pres = presentation(getvalue(src_schema))
    obs = make_map(ob_generators(tgt_schema)) do c
      Fc = ob_map(F,c)
      ob_map(X, src_pres[presentation_key(Fc)])
    end
    homs = hom_generators(src_schema)
    homfuns = map(x -> unwrap_tagged(hom_map(X, x)), homs)
    params = M.params
    funcs = make_map(hom_generators(tgt_schema)) do f
      Ff, c, d = hom_map(F, f), dom(tgt_schema, f), codom(tgt_schema, f)
      if head(Ff) == :zeromap
        domain = obs[c]
        domain = domain isa FinSet ? domain : FinSet(length(domain))
        codomain = obs[d]
        func = params[nameof(f)](homfuns...)
        if codomain isa TaggedElem
          vals_raw = [func(x) for x in collect(domain)]
          ElT = isempty(vals_raw) ? Any : typejoin(typeof.(vals_raw)...)
          vals = ElT[v for v in vals_raw]
          TaggedElem(FinDomFunction(vals, SetOb(TypeSet(ElT))), GATlab.gettag(codomain))
        else
          FinDomFunction(func, domain, codomain)
        end
      else 
        if head(Ff) == :id
          obj = obs[c]
          obj isa TaggedElem ? obj :
          obj isa FinSetInt ? id(Category(SkelFinSet()), obj) :
          obj isa AbsSet ? id(Category(SetC()), obj) :
          error("Unsupported identity component for $obj")
        else
          hom_map(X, src_pres[presentation_key(Ff)])
        end
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
  obs = ob_generators(dom(F))
    length(obs) > 0 || return FinCat(0)
    get_src_schema(diagram(ob_map(F, first(obs))))
end
function get_src_schema(F::Functor{<:Cat,<:Catlab.CategoricalAlgebra.Cats.Diagrams.DiagramCat})
  obs = ob_generators(dom(F))
    length(obs) > 0 || return FinCat(0)
    get_src_schema(diagram(ob_map(F, first(obs))))
end
get_src_schema(F::Functor{<:Cat,<:FinCat}) = codom(F)
function get_src_schema(F::FunctorFinDom)
  C = codom(F)
  C = C isa Category ? getvalue(C) : C
  if C isa TypeCat{<:Diagram} ||
     C isa Catlab.CategoricalAlgebra.Cats.Diagrams.DiagramCat
    obs = ob_generators(dom(F))
    length(obs) > 0 || return FinCat(0)
    return get_src_schema(diagram(ob_map(F, first(obs))))
  elseif C isa FinCat
    return C
  else
    error("unsupported data migration codomain $(typeof(C))")
  end
end

function free_diagram(F::FunctorFinDom)
  D_cat = dom(F)
  # Determine type sets needed by inspecting hom codomains for attr morphisms
  type_sets = Dict{Int,Any}()
  gen_to_idx = Dict(g => i for (i, g) in enumerate(ob_generators(D_cat)))
  _unwrap_h(h) = begin
    h = h isa TaggedElem ? getvalue(h) : h
    h isa CopairedFinDomFunction ? get(h) : h
  end
  _set_value(x) = x isa SetOb ? getvalue(x) : x
  function _lift_to_target(h, target)
    h isa Union{FinFunction,FinDomFunction} || return h
    target_set = target isa AbsSet ? target : SetOb(target)
    raw_target = _set_value(target_set)
    raw_codom = _set_value(codom(h))
    raw_target isa EitherSet || return h
    raw_codom == raw_target && return h
    left_set = _set_value(Catlab.BasicSets.left(raw_target))
    right_set = _set_value(Catlab.BasicSets.right(raw_target))
    vals_raw =
      raw_codom == left_set ? [Left(h(x)) for x in collect(dom(h))] :
      raw_codom == right_set ? [Right(h(x)) for x in collect(dom(h))] :
      nothing
    isnothing(vals_raw) && return h
    FinDomFunction(vals_raw, dom(h), target_set)
  end

  # First pass: detect TypeSet codomains from hom_map values
  for f in hom_generators(D_cat)
    h_unwrapped = _unwrap_h(hom_map(F, f))
    if h_unwrapped isa FinDomFunction
      cd = codom(h_unwrapped)
      tgt_idx = gen_to_idx[codom(D_cat, f)]
      cd = cd isa AbsSet ? cd : SetOb(cd)
      if haskey(type_sets, tgt_idx)
        cur = type_sets[tgt_idx]
        cur_val = _set_value(cur)
        cd_val = _set_value(cd)
        type_sets[tgt_idx] = cur_val isa EitherSet ? cur :
                             cd_val isa EitherSet ? cd : cur
      else
        type_sets[tgt_idx] = cd
      end
    end
  end

  # Wrap raw model objects (e.g. FinSetInt) to match dom/codom of hom_map values
  obs = map(ob_generators(D_cat)) do g
    o = ob_map(F, g)
    idx = gen_to_idx[g]
    if haskey(type_sets, idx)
      type_sets[idx]
    elseif o isa AbsSet
      o
    elseif codom(F) isa FinCat
      o
    elseif o isa TaggedElem
      SetOb(TypeSet{Any}())
    else
      FinSet(length(o))
    end
  end
  homs = map(hom_generators(D_cat)) do f
    h = _unwrap_h(hom_map(F, f))
    h = _lift_to_target(h, obs[gen_to_idx[codom(D_cat, f)]])
    (h, gen_to_idx[dom(D_cat, f)], gen_to_idx[codom(D_cat, f)])
  end
  g = FreeGraph{Any,Any}()
  add_vertices!(g, length(obs), ob=collect(obs))
  !isempty(homs) && add_edges!(g, getindex.(homs, 2), getindex.(homs, 3), hom=first.(homs))
  FreeDiagram(g)
end

"""Build a FreeGraph with wrapped FinSet/FinFunction objects for SkelFinSet colimits."""
function raw_free_graph(F::FunctorFinDom)
  D_cat = dom(F)
  gen_to_idx = Dict(g => i for (i, g) in enumerate(ob_generators(D_cat)))
  obs_vals = map(ob_generators(D_cat)) do g
    o = ob_map(F, g)
    if o isa FinSet
      o
    elseif o isa FinSetInt
      FinSet(length(o))
    elseif o isa TaggedElem
      FinSet(0)  # placeholder for AttrType
    else
      FinSet(length(o))
    end
  end
  hom_vals = map(hom_generators(D_cat)) do f
    h = hom_map(F, f)
    h = h isa TaggedElem ? getvalue(h) : h
    h = h isa CopairedFinDomFunction ? get(h) : h
    (h, gen_to_idx[dom(D_cat, f)], gen_to_idx[codom(D_cat, f)])
  end
  ObT = isempty(obs_vals) ? FinSet : typejoin(typeof.(obs_vals)...)
  HomT = isempty(hom_vals) ? FinFunction : typejoin(typeof.(first.(hom_vals))...)
  obs = ObT[o for o in obs_vals]
  homs = Tuple{HomT,Int,Int}[h for h in hom_vals]
  g = FreeGraph{ObT,HomT}()
  add_vertices!(g, length(obs), ob=obs)
  !isempty(homs) && add_edges!(g, getindex.(homs, 2), getindex.(homs, 3), hom=first.(homs))
  g
end

"""Compute limit of a FreeDiagram with legs for ALL original vertices.

BipartiteFreeDiagram limits only return legs for V₁ (source) vertices.
This helper reconstructs legs for V₂ (target) vertices by composing
the appropriate V₁ leg with the connecting hom.
"""
function full_limit(fd::FreeDiagram)
  g = getvalue(fd)
  if nv(g) == 0
    # Empty diagram: terminal object with no legs
    term = FinSet(1)
    cone = Multispan(SetOb(term), Any[])
    return LimitCone(cone, fd)
  end
  bpd = BipartiteFreeDiagram(fd)
  lim = limit[SetC()](bpd)
  bpd_legs = legs(lim)

  n_orig = nparts(bpd, :V)
  full_legs_vec = Vector{Any}(undef, n_orig)

  # V₁ legs → original vertices
  for (i, ov) in enumerate(bpd[:orig_vert₁])
    full_legs_vec[ov] = bpd_legs[i]
  end

  # V₂ legs → compose through any incoming edge
  for (v2_local, ov) in enumerate(bpd[:orig_vert₂])
    incoming = incident(bpd, v2_local, :tgt)
    @assert !isempty(incoming) "V₂ vertex $v2_local must have incoming edges"
    e = first(incoming)
    v1_local = src(bpd, e)
    h = hom(bpd, e)
    full_legs_vec[ov] = compose[SetC()](bpd_legs[v1_local], h)
  end

  cone = Multispan(ob(lim), full_legs_vec)
  LimitCone(cone, fd)
end

function tabular_limit(lim::AbsLimit; names=nothing)
  πs = legs(lim)
  domset = dom(first(πs))
  rows = collect(domset)
  colnames = isnothing(names) ? Tuple(Symbol(i) for i in eachindex(πs)) :
    Tuple(Symbol(name) for name in names)
  columns = Tuple(map(π -> map(π, rows), πs))
  table = TabularSet(NamedTuple{colnames}(columns))
  cone = Multispan(SetOb(table), map(πs, eachindex(πs)) do π, i
    codset = let c = codom(π)
      c isa AbsSet ? c : FinSet(length(c))
    end
    SetFunction(row -> row[i], SetOb(table), codset)
  end)
  LimitCone(cone, diagram(lim))
end

"""Compute the attribute function for an Attr morphism targeting an AttrType.

For Attr morphisms, the codomain is an AttrType with a trivial (single-object)
diagram. The attribute function maps each element of the domain Ob-limit to a
value in the attribute type by composing the domain limit legs with the
DiagramHom's morphism components.
"""
function _attr_universal(f::DiagramHom, dom_lim)
  # Extract dom shape
  dom_diag_fun = f.precomposed_diagram.fun
  dom_cat = dom(dom_diag_fun)
  dom_gens = collect(ob_generators(dom_cat))
  obs = Dict(g => i for (i, g) in enumerate(dom_gens))

  # The codomain diagram has a single object (the AttrType)
  dm = getvalue(f.diagram_map)
  codom_fun = dm.codom
  J′ = dom(codom_fun)
  j′ = only(collect(ob_generators(J′)))
  j, g = ob_map(f, j′)
  πⱼ = legs(dom_lim)[obs[j]]
  # Unwrap TaggedElem (Catlab 0.17 wraps attr morphisms)
  g_val = g isa TaggedElem ? getvalue(g) : g
  if g_val === nothing
    # Identity on AttrType (placeholder from param_compose): just return leg
    πⱼ
  else
    # The attribute function: compose the limit leg with the attr function
    SetFunction(x -> g_val(πⱼ(x)), apex(dom_lim), codom(g_val))
  end
end

"""Compute the attribute function for an Attr morphism in a gluing migration.

For Attr morphisms in gluing migrations, the domain is a colimit (coproduct of cases)
and the codomain is an AttrType. For each case in the coproduct, compose the
case's attr function with the injection leg to build the complete attr function.
"""
function _attr_colimit_universal(f::DiagramHom, dom_colim)
  sm = f.shape_map
  J = dom(sm)
  J_gens = collect(ob_generators(J))

  # Build a function on the colimit apex by combining injection legs
  ιs = legs(dom_colim)
  apex_set = ob(dom_colim)

  # Collect (injection_start, injection_end, attr_function) for each case
  components = map(enumerate(J_gens)) do (i, j)
    j′, g = ob_map(f, j)
    g_val = g isa TaggedElem ? getvalue(g) : g
    if g_val === nothing
      # Identity on AttrType — should not happen for Attr morphisms typically
      nothing
    else
      (ιs[i], g_val)
    end
  end

  # Build the function on the coproduct by evaluating via injection ranges
  n = length(apex_set)
  # Each injection maps into the coproduct. Build a lookup from coproduct element
  # to (case_index, local_element).
  # First pass: collect values to determine concrete type
  raw_vals = Vector{Any}(undef, n)
  for (i, j) in enumerate(J_gens)
    j′, g = ob_map(f, j)
    g_val = g isa TaggedElem ? getvalue(g) : g
    ι = ιs[i]
    for x in dom(ι)
      raw_vals[ι(x)] = g_val === nothing ? x : g_val(x)
    end
  end
  ElT = typejoin(typeof.(raw_vals)...)
  vals = ElT[v for v in raw_vals]
  # Use FinDomFunction with explicit SetOb(TypeSet) codomain for attribute values
  FinDomFunction(vals, SetOb(TypeSet(ElT)))
end

"""Compute universal morphism for a DiagramOp hom between two limits.

In Catlab 0.17, the Diagrams/Limits.jl `universal` method is broken due to
model dispatch requirements. This helper implements the computation directly.

Given `f: D(c) → D(d)` (a DiagramHom between DiagramOp diagrams),
`dom_lim = limit(D(c))`, `codom_lim = limit(D(d))`, compute the unique
morphism `apex(dom_lim) → apex(codom_lim)` induced by the universal property.
"""
function _diagram_op_universal(f::DiagramHom, dom_lim, codom_lim)
  # Extract codom shape via direct field access (avoids model-dispatched codom)
  dm = getvalue(f.diagram_map)
  codom_fun = dm.codom
  J′ = dom(codom_fun)

  # Extract dom shape via direct field access
  dom_diag_fun = f.precomposed_diagram.fun
  dom_cat = dom(dom_diag_fun)
  dom_gens = collect(ob_generators(dom_cat))
  obs = Dict(g => i for (i, g) in enumerate(dom_gens))

  cone = Multispan(apex(dom_lim), map(collect(ob_generators(J′))) do j′
    j, g = ob_map(f, j′)
    πⱼ = legs(dom_lim)[obs[j]]
    # Compose functionally to avoid SetFunction/FinFunction type mismatch
    g′ = unwrap_tagged(g)
    cod = let c = codom(g′); c isa AbsSet ? c : FinSet(length(c)) end
    SetFunction(x -> g′(πⱼ(x)), apex(dom_lim), cod)
  end)
  _limit_universal(codom_lim, cone)
end

_limit_universal(lim::FinSetIndexedLimit, cone::Multispan) =
  indexed_universal(lim, cone)

function _limit_universal(lim::LimitCone, cone::Multispan)
  lim_legs = legs(lim)
  apex_src = apex(cone)
  apex_tgt = apex(lim)
  fs = Tuple(legs(cone))
  if length(lim_legs) == 1 && length(fs) == 1 &&
     apex_tgt isa SetOb && getvalue(apex_tgt) isa TypeSet
    return only(fs)
  end
  # Build index: (π₁(y), π₂(y), ...) → y (the actual element)
  index = Dict{Any,Any}()
  for y in collect(apex_tgt)
    key = Tuple(π(y) for π in lim_legs)
    index[key] = y
  end
  SetFunction(x -> index[Tuple(f(x) for f in fs)], apex_src, apex_tgt)
end

"""Compute the universal morphism between colimits induced by a DiagramHom.

Given `f: D_c → D_d` (DiagramHom), `dom_colim = colimit(D_c)`, `codom_colim = colimit(D_d)`,
return the induced morphism `ob(dom_colim) → ob(codom_colim)`.
Uses SkelFinSet model dispatch for compose/universal on FinSetInt/FinFunction.
"""
function _colimit_universal(f::DiagramHom, dom_colim, codom_colim)
  # Get domain and codomain shape categories from shape_map
  sm = f.shape_map
  J = dom(sm)     # domain diagram shape (e.g., {v, e} for E diagram)
  J′ = codom(sm)  # codomain diagram shape (e.g., {V} for V diagram)
  J_gens = collect(ob_generators(J))
  J′_gens = collect(ob_generators(J′))
  codom_obs = Dict(g => i for (i, g) in enumerate(J′_gens))
  codom_diag = diagram(f.precomposed_diagram)

  if isempty(J_gens)
    cod = ob(codom_colim)
    cod = cod isa FinSet ? cod : FinSet(length(cod))
    return FinFunction(Int[], cod)
  end

  cocone_legs = map(J_gens) do j
    j′, g = ob_map(f, j)
    ιⱼ′ = legs(codom_colim)[codom_obs[j′]]
    if g isa FinFunction
      compose[SkelFinSet()](g, ιⱼ′)
    else
      cod_obj = ob_map(codom_diag, j′)
      cod_index = Dict(y => i for (i, y) in enumerate(collect(cod_obj)))
      vals = Int[ιⱼ′(cod_index[g(x)]) for x in collect(dom(g))]
      FinFunction(vals, length(ob(codom_colim)))
    end
  end
  cocone = Multicospan(ob(codom_colim), cocone_legs; cat=SkelFinSet())
  composite_universal(dom_colim, cocone)
end

# Conjunctive migration
#----------------------

function migrate_conj(X::FinDomFunctor, M::ContravariantMigration;
                 return_limits::Bool=false, tabular::Bool=false)
  F = functor(M)
  tgt_schema = dom(F)
  src_pres = presentation(getvalue(dom(X)))
  homs = hom_generators(get_src_schema(F))
  homfuns = map(x -> unwrap_tagged(hom_map(X, src_pres[presentation_key(x)])), homs)
  params = M.params
  limits = make_map(ob_generators(tgt_schema)) do c
    Fc = ob_map(F, c)
    J = shape(Fc)
    if c isa AttrTypeExpr
      # AttrType generators have trivial diagrams; store ob_map(X, c) directly.
      # The type "set" is not a finite set and can't go through limit machinery.
      return ob_map(X, src_pres[presentation_key(_trivial_query_ob(Fc))])
    end
    diagram_types = isempty(J) ? (FinSet, FinFunction) : (Any,Any)
    # Make sure the diagram to be limited is a FinCat{<:Int}.
    # Disable domain check because acsets don't store schema equations.
    k = free_diagram(diagram(force(compose(Fc, X), diagram_types...)))
    #get rid of any varfunctions and
    #cover for the annoying fact that FinDomFunctions containing a lambda are SetFunctionCallables but FinDomFunctionMaps are not.
    #this isn't gonna work if k includes an attribute that should really include attrvars...
    k = isempty(J) ? k :
      fmap(k, x -> x isa SetOb ? x : SetOb(x), x -> SetFunction(x), SetOb, SetFunction)
    lim = full_limit(k)
    if tabular
      names = (ob_generator_name(J, j) for j in ob_generators(J))
      tabular_limit(lim; names=names)
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
      f_params = Dict(nameof(_trivial_query_ob(ob_map(F,d))) => params[nameof(f)](homfuns...))
    else 
      f_params = Dict()
    end 
    # Disable domain check for same reason.
    # Hand the Julia function form of the not-yet-defined components to compose
    t = compose(Ff, X, f_params)
    if d isa AttrTypeExpr
      # For Attr morphisms targeting an AttrType, the codom "limit" is trivial.
      # Build the cone into the AttrType, then the universal morphism is just
      # the single cone leg (since the limit of a single-object diagram is itself).
      _attr_universal(t, limits[c])
    else
      _diagram_op_universal(t, limits[c], limits[d])
    end
  end
  obs_map = mapvals(limits) do lim
    lim isa LimitCone ? ob(lim) : lim  # AttrType passes through as-is
  end
  if isempty(limits)
    cod = typed_typecat(FinSet, FinDomFunction)
  else
    # Infer codomain category from ob/hom value types
    ObT = typejoin(typeof.(values(obs_map))...)
    HomT = isempty(funcs) ? Any : typejoin(typeof.(values(funcs))...)
    cod = typed_typecat(ObT, HomT)
  end
  Y = FinDomFunctor(obs_map, funcs, tgt_schema, cod)
  return_limits ? (Y, limits) : Y
end

# Gluing migration
#-----------------

function migrate_glue(X::FinDomFunctor, M::ContravariantMigration)
  F = functor(M)
  tgt_schema = dom(F)
  src_pres = presentation(getvalue(dom(X)))
  homs = hom_generators(get_src_schema(F))
  homfuns = map(x -> unwrap_tagged(hom_map(X, src_pres[presentation_key(x)])), homs)
  params = M.params
  colimits = make_map(ob_generators(tgt_schema)) do c
    Fc = ob_map(F, c)
    if c isa AttrTypeExpr
      return ob_map(X, src_pres[presentation_key(c)])  # AttrType passes through directly
    end
    FX = diagram(force(compose(Fc, X)))
    isempty(ob_generators(dom(FX))) && return initial[SkelFinSet()]()
    fg = raw_free_graph(FX)
    colimit[SkelFinSet()](fg)
  end
  funcs = make_map(hom_generators(tgt_schema)) do f
    Ff, c, d = hom_map(F, f), dom(tgt_schema, f), codom(tgt_schema, f)
    f_params = haskey(params, f) ? map(x -> x(homfuns...), params[f]) :
               isempty(get_params(Ff)) ? Dict() : mapvals(x -> x(homfuns...), get_params(Ff))
    if d isa AttrTypeExpr
      # Attr morphisms: compose the diagram hom with X to get the function
      _attr_colimit_universal(compose(Ff, X, f_params), colimits[c])
    else
      _colimit_universal(compose(Ff, X, f_params), colimits[c], colimits[d])
    end
  end
  obs_map = mapvals(colimits) do v
    v isa AbsColimit ? ob(v) : v  # AttrType passes through as-is
  end
  ObT = typejoin(typeof.(values(obs_map))...)
  HomT = isempty(funcs) ? Any : typejoin(typeof.(values(funcs))...)
  cod = typed_typecat(ObT, HomT)
  FinDomFunctor(obs_map, funcs, tgt_schema, cod)
end

# Gluc migration
#---------------
"""
    migrate(M,X)

do the dang migration
"""
function migrate_gluc(X::FinDomFunctor, M::ContravariantMigration)
  F = functor(M)
  tgt_schema = dom(F)
  src_pres = presentation(getvalue(dom(X)))
  homs = hom_generators(get_src_schema(F))
  homfuns = map(x -> unwrap_tagged(hom_map(X, src_pres[presentation_key(x)])), homs)
  colimits_of_limits = make_map(ob_generators(tgt_schema)) do c
    if c isa AttrTypeExpr
      Fc = ob_map(F, c)
      set = ob_map(X, src_pres[presentation_key(_trivial_query_ob(Fc))])
      J = shape(Fc)
      obs = Dict(only(ob_generators(J)) => set)
      Fc_set = FinDomFunctor(obs, Dict{Any,Any}(), J, typed_typecat(typeof(set), Any))
      return (set, Fc_set, Dict{Any,Any}())
    end
    Fc = ob_map(F, c)
    m = Fc isa QueryDiagram ? DataMigration(diagram(Fc), Fc.params) : DataMigration(diagram(Fc))
    Fc_set, limits = migrate(X, m, return_limits=true)
    Fc_colim = isempty(ob_generators(dom(Fc_set))) ? initial[SkelFinSet()]() :
      colimit[SkelFinSet()](raw_free_graph(Fc_set))
    (Fc_colim, Fc_set, limits)
  end
  funcs = make_map(hom_generators(tgt_schema)) do f
    Ff, c, d = hom_map(F, f), dom(tgt_schema, f), codom(tgt_schema, f)
    Fc_colim, Fc_set, Fc_limits = colimits_of_limits[c]
    Fd_colim, Fd_set, Fd_limits = colimits_of_limits[d]
    Ff_params = get_params(Ff)
    component_funcs = make_map(ob_generators(dom(Fc_set))) do j
      j′, Ffⱼ = ob_map(Ff, j)
      Ffⱼ_params = Ffⱼ isa Union{DiagramHom,QueryDiagramHom} ?
                   haskey(Ff_params, nameof(j)) ?
                   Dict(only(keys(components(diagram_map(Ffⱼ)))) => Ff_params[nameof(j)](homfuns...)) :
                   mapvals(x -> x(homfuns...), get_params(Ffⱼ)) : Dict{Any,Any}()
      FfⱼX = compose(Ffⱼ, X, Ffⱼ_params)
      if d isa AttrTypeExpr || j′ isa AttrTypeExpr
        _attr_universal(FfⱼX, Fc_limits[j])
      else
        _diagram_op_universal(FfⱼX, Fc_limits[j], Fd_limits[j′])
      end
    end
    Ff_set = DiagramHom(shape_map(Ff), component_funcs, DiagramId(Fc_set), DiagramId(Fd_set))
    d isa AttrTypeExpr ? _attr_colimit_universal(Ff_set, Fc_colim) :
                         _colimit_universal(Ff_set, Fc_colim, Fd_colim)
  end
  obs_map = mapvals(colimits_of_limits) do x
    colim = first(x)
    colim isa AbsColimit ? ob(colim) : colim
  end
  ObT = typejoin(typeof.(values(obs_map))...)
  HomT = isempty(funcs) ? Any : typejoin(typeof.(values(funcs))...)
  cod = typed_typecat(ObT, HomT)
  FinDomFunctor(obs_map, funcs, tgt_schema, cod)
end

query_kind(q::DiagramOp) = :conj
query_kind(q::QueryDiagram{op}) = :conj
function query_kind(q::DiagramId)
  objs = collect_ob(q)
  isempty(objs) && return :glue
  first_obj = first(objs)
  first_obj isa DiagramOp && return :gluc
  first_obj isa QueryDiagram{op} && return :gluc
  :glue
end
query_kind(q::QueryDiagram{id}) = query_kind(diagram(q))

function migrate(X::FinDomFunctor, M::ContravariantMigration; kwargs...)
  _migrate_contravariant(X, M; kwargs...)
end

function _migrate_contravariant(X::FinDomFunctor, M::ContravariantMigration; kwargs...)
  F = functor(M)
  isempty(ob_generators(dom(F))) && return migrate_conj(X, M; kwargs...)
  q = ob_map(F, first(ob_generators(dom(F))))
  kind = query_kind(q)
  if kind === :conj
    migrate_conj(X, M; kwargs...)
  elseif kind === :gluc
    isempty(kwargs) || error("Keyword arguments not supported for gluc migrations")
    migrate_gluc(X, M)
  else
    isempty(kwargs) || error("Keyword arguments not supported for glue migrations")
    migrate_glue(X, M)
  end
end


const ConjMigrationFunctor = DataMigrationFunctor
const GlueMigrationFunctor = DataMigrationFunctor
const GlucMigrationFunctor = DataMigrationFunctor

""" Interpret conjunctive data migration as a colimit of representables.

Given a conjunctive data migration (a functor `J → Diag{op}(C)`) and the Yoneda
embedding for `C` (a functor `op(C) → C-Set` computed via `yoneda`),
take colimits of representables to construct a `op(J)`-shaped diagram of C-sets.

Since every C-set is a colimit of representables, this is a generic way of
constructing diagrams of C-sets.
"""
function colimit_representables(M::ContravariantMigration, y)
  F = functor(M)
  isempty(ob_generators(dom(F))) && return compose_partial(op(F), y)
  first_query = ob_map(F, first(ob_generators(dom(F))))
  first_query isa Diagram || return compose_partial(op(F), y)
  query_kind(first_query) === :conj ||
    error("colimit_representables is only defined for delta and conjunctive migrations")
  J = dom(F)
  if isempty(hom_generators(J))
    ACat = ACSetCategory(last(first(ob_map(y))))
    obs = make_map(ob_generators(J)) do j
      query = ob_map(F, j)
      if query isa QueryDiagram && !isempty(query.params)
        _query_apex(query, y)
      else
        Fj = diagram(query)
        clim_diag = query isa QueryDiagram ? compose_partial(op(Fj), y) :
                    compose(op(query), y)
        ob(Catlab.CategoricalAlgebra.Pointwise.LimitsColimits.Colimits.pointwise_colimit(
          ACat, _diagram_freegraph(clim_diag)))
      end
    end
    return FinDomFunctor(obs, Dict{Any,Any}(), op(J), codom(y))
  end
  #Get the constructor for a C-set.
  ACat = ACSetCategory(last(first(ob_map(y))))
  ACS = constructor(ob_map(y,first(ob_generators(dom(y)))))
  colimits = make_map(ob_generators(J)) do j
    query = ob_map(F, j)
    Fj = diagram(query) # a diagram K to C
    clim_diag = query isa QueryDiagram ? compose_partial(op(Fj), y) :
                compose(op(query), y) # K^op to C^op to C-Set
    # modify the diagram we take a colimit of to concretize some vars
    
    params = query isa QueryDiagram ? query.params : Dict()
    isempty(params) && return Catlab.CategoricalAlgebra.Pointwise.LimitsColimits.Colimits.pointwise_colimit(
      ACat, _diagram_freegraph(clim_diag))
    fgd = _diagram_freegraph_data(clim_diag)
    obs_gen, obs, obix, homs, D = fgd.obs_gen, fgd.obs, fgd.obix, fgd.homs, fgd.cat
    for (i,val) in collect(params)
      at = nameof(ob_map(Fj, i)) # attribute type name 
      h = only(homomorphisms(ob_map(clim_diag,i), ACS(); initial=Dict(at=>[val])))
      new_obj = ACS()
      push!(obs, new_obj)
      new_idx = length(obs)
      old_idx = i isa Symbol ? obix[_lookup_generator(obs_gen, i)] : obix[i]
      h_dom, h_cod = dom(D, h), codom(D, h)
      if h_dom == new_obj && h_cod == obs[old_idx]
        push!(homs, (h, new_idx, old_idx))
      elseif h_dom == obs[old_idx] && h_cod == new_obj
        push!(homs, (h, old_idx, new_idx))
      else
        error("Could not align parameter map for $i")
      end
    end
    Catlab.CategoricalAlgebra.Pointwise.LimitsColimits.Colimits.pointwise_colimit(
      ACat, FreeGraph(obs, homs)) # take colimit
  end
  homs = make_map(hom_generators(J)) do f
    Ff, j, k = hom_map(F, f), dom(J, f), codom(J, f)
    _diagram_colimit_universal(compose(op(Ff), y), colimits[k], colimits[j])
  end
  FinDomFunctor(mapvals(ob, colimits), homs, op(J), codom(y))
end

end
