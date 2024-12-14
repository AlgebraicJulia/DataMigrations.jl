""" A diagram without a codomain category.

An intermediate data representation used internally by the parser for the
[`@diagram`](@ref) and [`@migration`](@ref) macros.
"""
struct DiagramData{T,ObMap,HomMap}
  #keys may be GATExprs because this diagram doesn't have
  #a codomain yet.
  ob_map::ObMap
  hom_map::HomMap
  shape::FinCat
  params::AbstractDict
end

function DiagramData{T}(ob_map::ObMap,
						hom_map::HomMap,
                        shape, params=Dict()) where {T,ObMap,HomMap}
  DiagramData{T,ObMap,HomMap}(ob_map, hom_map, shape, params)
end

Diagrams.ob_map(d::DiagramData, x) = d.ob_map[x]
Diagrams.hom_map(d::DiagramData, f) = d.hom_map[f]
Diagrams.shape(d::DiagramData) = d.shape
unpoint(m::Module) = @match m begin
	FreePointedSetSchema => FreeSchema
	FreePointedSetCategory => FreeCategory
	_ => m
end

function Diagrams.Diagram(d::DiagramData{T}, codom) where T
  #if simple, we'll throw away the params and make
  #sure the shape is based on non-pointed stuff
  simple = isempty(d.params)
  new_shape = change_shape(simple,d.shape)
  F = FinDomFunctor(d.ob_map, d.hom_map, new_shape, codom)
  simple ? SimpleDiagram{T}(F) : QueryDiagram{T}(F, d.params)
end

function change_shape(simple::Bool, old_shape::FinCatPresentation)
  old_pres = presentation(old_shape)
  old_syntax = old_pres.syntax
  simple ? FinCat(change_theory(unpoint(old_syntax),old_pres)) : old_shape
end

change_shape(simple::Bool,old_shape) = old_shape

function change_theory(syntax::Module,pres::Presentation{S,Name}) where {S,Name}
	pres_new = Presentation(syntax)
	construct_generators!(pres,names,types,type_args) = map(eachindex(names)) do i 
		construct_generator!(pres,names[i],types[i],type_args[i]) 
	end
	construct_generators!(pres_new,map(nameof,generators(pres)),map(gat_typeof,generators(pres)),
                        map(x->map(nameof,x.type_args),generators(pres)))
	#XXX: test on equations
	pres_new
end

""" Present a diagram in a given category.

Recall that a *diagram* in a category ``C`` is a functor ``F: J → C`` from a
small category ``J`` into ``C``. Given the category ``C``, this macro presents a
diagram in ``C``, i.e., constructs a finitely presented indexing category ``J``
together with a functor ``F: J → C``. This method of simultaneous definition is
often more convenient than defining ``J`` and ``F`` separately, as could be
accomplished by calling [`@fincat`](@ref) and then [`@finfunctor`](@ref).

As an example, the limit of the following diagram consists of the paths of
length two in a graph:

```julia
@diagram SchGraph begin
  v::V
  (e₁, e₂)::E
  (t: e₁ → v)::tgt
  (s: e₂ → v)::src
end
```

Morphisms in the indexing category can be left unnamed, which is convenient for
defining free diagrams (see also [`@free_diagram`](@ref)). For example, the
following diagram is isomorphic to the previous one:

```julia
@diagram SchGraph begin
  v::V
  (e₁, e₂)::E
  (e₁ → v)::tgt
  (e₂ → v)::src
end
```

Of course, unnamed morphisms cannot be referenced by name within the `@diagram`
call or in other settings, which can sometimes be problematic.
"""
macro diagram(cat, body)
	ast = AST.Diagram(parse_diagram_ast(body, free=false))
	:(parse_diagram($(esc(cat)), $ast))
end

""" Present a free diagram in a given category.

Recall that a *free diagram* in a category ``C`` is a functor ``F: J → C`` where
``J`` is a free category on a graph, here assumed finite. This macro is
functionally a special case of [`@diagram`](@ref) but changes the interpretation
of equality expressions. Rather than interpreting them as equations between
morphisms in ``J``, equality expresions can be used to introduce anonymous
morphisms in a "pointful" style. For example, the limit of the following diagram
consists of the paths of length two in a graph:

```julia
@free_diagram SchGraph begin
  v::V
  (e₁, e₂)::E
  tgt(e₁) == v
  src(e₂) == v
end
```

Anonymous objects can also be introduced. For example, the previous diagram is
isomorphic to this one:

```julia
@free_diagram SchGraph begin
  (e₁, e₂)::E
  tgt(e₁) == src(e₂)
end
```

Some care must exercised when defining morphisms between diagrams with anonymous
objects, since they cannot be referred to by name.
"""
macro free_diagram(cat, body)
	ast = AST.Diagram(parse_diagram_ast(body, free=true, mod=__module__))
	:(parse_diagram($(esc(cat)), $ast))
end

function parse_diagram(C::FinCat, ast::AST.Diagram)
	d = Diagram(parse_diagram_data(C, ast), C)
	is_functorial(diagram(d), check_equations=false) ||
		error("Parsed diagram is not functorial: $ast")
	return d
end
parse_diagram(pres::Presentation, ast::AST.Diagram) =
  parse_diagram(FinCat(pres), ast)

"""
Take HomOvers and ObOvers, build a target schema
for the migration and its ob and hom maps,
ready for promotion and building the diagram.
"""
function parse_diagram_data(C::FinCat, statements::Vector{<:AST.DiagramExpr};
                            type=Any, ob_parser=nothing, hom_parser=nothing)
  isnothing(ob_parser) && (ob_parser = x -> parse_ob(C, x))
  isnothing(hom_parser) && (hom_parser = (f,x,y) -> parse_hom(C,f))
  g, eqs = Presentation(FreeSchema), Pair[] 
  F_ob, F_hom, params = Dict{GATExpr,Any}(), Dict{GATExpr,Any}(), Dict{Symbol,Any}()
  mornames = Symbol[nameof(x) for x in hom_generators(C)]
  for stmt in statements
    @match stmt begin
      AST.ObOver(x, X) => begin
        x′ = parse!(g, AST.Ob(x))
        #`nothing`, though zeroob would be nicer, so that not every category and schema has to be pointed
        F_ob[x′] = isnothing(X) ? nothing : ob_parser(X)
      end
      AST.HomOver(f, x, y, h) => begin
        e = parse!(g, AST.Hom(f, x, y))
        X, Y = F_ob[dom(e)], F_ob[codom(e)]
        F_hom[e] = hom_parser(h, X, Y)
        #hom_parser might be e.g. parse_query_hom(C,...)
        if isnothing(Y)
          # Infer codomain in base category from parsed hom.
          F_ob[codom(e)] = codom(C, F_hom[e])
        end
      end
      #add the hom that's going to map to h, then save for later
      AST.AttrOver(f,x,y,expr,mod) => begin
        e = parse!(g,AST.Hom(f,x,y))
        X, Y = F_ob[dom(e)], F_ob[codom(e)]
        F_hom[e] = zeromap(X,Y)
        aux_func = make_func(mod,expr,mornames)
        params[nameof(e)] = aux_func
      end
      AST.HomAndAttrOver(AST.HomOver(f,x,y,h),AST.AttrOver(f,x,y,expr,mod)) => begin
        e = parse!(g,AST.Hom(f,x,y))
        X, Y = F_ob[dom(e)], F_ob[codom(e)]
        F_hom[e] = hom_parser(h, X, Y)
        if isnothing(Y)
          F_ob[codom(e)] = codom(C, F_hom[e])
        end
        aux_func = make_func(mod,expr,mornames)
        params[nameof(e)] = aux_func
      end
      AST.AssignValue(x, value) => begin
        haskey(params, x) && error("Julia value already assigned to $x")
        params[x] = value
      end
      AST.HomEq(lhs, rhs) =>
        push!(eqs, parse_path(g, lhs) => parse_path(g, rhs))
      _ => error("Cannot use statement $stmt in diagram definition")
    end
  end
  J = FinCat(g) #oh no!
  DiagramData{type}(F_ob, 
                    F_hom, J, params)
end

parse_diagram_data(C::FinCat, ast::AST.Diagram; kw...) =
  parse_diagram_data(C, ast.statements; kw...)


