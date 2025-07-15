""" A diagram morphism without a domain or codomain.

Like `DiagramData`, this an intermediate data representation used
internally by the parser for the [`@migration`](@ref) macro.
"""
struct DiagramHomData{T,ObMap,HomMap,Params<:AbstractDict}
  #should generally be indexed by gatexprs, not symbols yet
  ob_map::ObMap
  hom_map::HomMap
  params::Params
end
DiagramHomData{T}(ob_map::ObMap, hom_map::HomMap,params::Params) where {T,ObMap,HomMap,Params<:AbstractDict} =
  DiagramHomData{T,ObMap,HomMap,Params}(ob_map, hom_map,params)
DiagramHomData{T}(ob_map::ObMap, hom_map::HomMap) where {T,ObMap,HomMap} =
  DiagramHomData{T,ObMap,HomMap,Dict{Any,Any}}(ob_map, hom_map,Dict())

""" Contravariantly migrate data from one acset to another.

This macro is shorthand for defining a data migration using the
[`@migration`](@ref) macro and then calling the `migrate` function. If the
migration will be used multiple times, it is more efficient to perform these
steps separately, reusing the functor defined by `@migration`.

For more about the syntax and supported features, see [`@migration`](@ref).
"""
macro migrate(tgt_type, src_acset, body)
  quote
    let T = $(esc(tgt_type)), X = $(esc(src_acset))
      migrate(T, X, parse_migration(Presentation(T), Presentation(X),
                                    $(Meta.quot(body))))
    end
  end
end

""" Define a contravariant data migration.

This macro provides a DSL to specify a contravariant data migration from
``C``-sets to ``D``-sets for given schemas ``C`` and ``D``. A data migration is
defined by a functor from ``D`` to a category of queries on ``C``. Thus, every
object of ``D`` is assigned a query on ``C`` and every morphism of ``D`` is
assigned a morphism of queries, in a compatible way. Example usages are in the
unit tests. What follows is a technical reference.

Several categories of queries are supported by this macro:

1. Trivial queries, specified by a single object of ``C``. In this case, the
   macro simply defines a functor ``D → C`` and is equivalent to
   [`@finfunctor`](@ref) or [`@diagram`](@ref).
2. *Conjunctive queries*, specified by a diagram in ``C`` and evaluated as a
   finite limit.
3. *Gluing queries*, specified by a diagram in ``C`` and evaluated as a finite
   colimit. An important special case is *linear queries*, evaluated as a
   finite coproduct.
4. *Gluc queries* (gluings of conjunctive queries), specified by a diagram of
   diagrams in ``C`` and evaluated as a colimit of limits. An important special
   case is *duc queries* (disjoint unions of conjunctive queries), evaluated as
   a coproduct of limits.

The query category of the data migration is not specified explicitly but is
inferred from the queries used in the macro call. Implicit conversion is
performed: trivial queries can be coerced to conjunctive queries or gluing
queries, and conjunctive queries and gluing queries can both be coerced to gluc
queries. Due to the implicit conversion, the resulting functor out of ``D`` has
a single query type and thus a well-defined codomain.

Syntax for the right-hand sides of object assignments is:

- a symbol, giving object of ``C`` (query type: trivial)
- `@product ...` (query type: conjunctive)
- `@unit` (alias: `@terminal`, query type: conjunctive)
- `@join ...` (alias: `@limit`, query type: conjunctive)
- `@cases ...` (alias: `@coproduct`, query type: gluing)
- `@empty` (alias: `@initial`, query type: gluing)
- `@glue ...` (alias: `@colimit`, query type: gluing)

Thes query types supported by this macro generalize the kind of queries familiar
from relational databases. Less familiar is the concept of a morphism between
queries, derived from the concept of a morphism between diagrams in a category.
A query morphism is given by a functor between the diagrams' indexing categories
together with a natural transformation filling a triangle of the appropriate
shape. From a practical standpoint, the most important thing to remember is that
a morphism between conjunctive queries is contravariant with respect to the
diagram shapes, whereas a morphism between gluing queries is covariant. TODO:
Reference for more on this.
"""
macro migration(src_schema, body)
  ast = AST.Diagram(parse_diagram_ast(body,mod=__module__))
  :(parse_migration($(esc(src_schema)), $ast))
end
macro migration(tgt_schema, src_schema, body)
  # Cannot parse Julia expr during expansion because target schema is needed.
  :(parse_migration($(esc(tgt_schema)), $(esc(src_schema)), $(Meta.quot(body)),$(Expr(:kw,:mod,__module__))))
end

"""
Uses the output of `yoneda`:

@acset_colim yGraph begin 
  (e1,e2)::E 
  src(e1) == tgt(e2) 
end
"""
macro acset_colim(yon, body)
  body = quote
    I => @join $body
  end
  ast = AST.Diagram(parse_diagram_ast(body, mod=__module__))
  quote
    p = Presentation(acset_schema(last(first($(esc(yon)).ob_map))))
    tmp = parse_migration(p, $ast)
    ob_map(colimit_representables(tmp, $(esc(yon))), :I)
  end
end

""" Parse a contravariant data migration from a Julia expression.

The process kicked off by this internal function is somewhat complicated due to
the need to coerce queries and query morphisms to a common category. The
high-level steps of this process are:

1. Parse the queries and query morphisms into intermediate representations
   ([`DiagramData`](@ref) and [`DiagramHomData`](@ref)) whose final types are
   not yet determined.
2. Promote the query types to the tightest type encompassing all queries, an
   approach reminiscent of Julia's own type promotion system.
3. Convert all query and query morphisms to this common type, yielding `Diagram`
   and `DiagramHom` instances.
"""
function parse_migration(src_schema::Presentation, ast::AST.Diagram)
  simple = check_simple(ast)
  C = simple ? FinCat(src_schema) : FinCat(change_theory(FreePointedSetSchema,src_schema))
  d = parse_query_diagram(C, ast.statements)
  DataMigration(make_query(C, d))
end
function parse_migration(tgt_schema::Presentation, src_schema::Presentation,
                         ast::AST.Mapping;simple::Bool=true)
  D, C = simple ? (FinCat(tgt_schema), FinCat(src_schema)) : (FinCat(change_theory(FreePointedSetSchema,tgt_schema)), FinCat(change_theory(FreePointedSetSchema,src_schema)))
  homnames = Symbol[nameof(x) for x in hom_generators(C)]
  params = Dict{Symbol,Any}()
  ob_rhs, hom_rhs = make_ob_hom_maps(D, ast, missing_hom=true)
  F_ob = mapvals(expr -> parse_query(C, expr), ob_rhs)
  F_hom = mapvals(hom_rhs, keys=true) do f, expr
    @match expr begin
    AST.JuliaCodeHom(code,mod) => begin
      aux_func = make_func(mod,code,homnames)
      params[nameof(f)] = aux_func
    end
    AST.MixedHom(hexp,jcode) => begin
      aux_func = make_func(jcode.mod,jcode.code,homnames)
      params[nameof(f)] = aux_func
      expr = expr.hexp
    end
    _ => begin end
  end
    parse_query_hom(C, ismissing(expr) ? AST.Mapping(AST.AssignExpr[]) : expr,
                    F_ob[dom(D,f)], F_ob[codom(D,f)])
  end
  DataMigration(make_query(C, DiagramData{Any}(F_ob, F_hom, D,params)))
end
function parse_migration(tgt_schema::Presentation, src_schema::Presentation,
                         body::Expr;mod::Module=Main)
  ast = parse_mapping_ast(body, FinCat(tgt_schema), preprocess=true,mod=mod)
  simple = check_simple(ast)
  parse_migration(tgt_schema, src_schema, ast;simple=simple)
end

check_simple(ast)= @match ast begin
  ::AST.Mapping => all(check_simple(a) for a in ast.assignments)
  ::AST.Apply || ::AST.Coapply => check_simple(ast.ob) && check_simple(ast.hom)
  ::AST.Compose => all(check_simple(a) for a in ast.homs)
  ::AST.HomAssign || ::AST.ObAssign => check_simple(ast.lhs) && check_simple(ast.rhs)
  ::AST.Limit || ::AST.Product || ::AST.Colimit || ::AST.Coproduct || ::AST.Diagram => all(check_simple(a) for a in ast.statements)
  ::AST.ObOver || ::AST.HomOver => check_simple(ast.over)
  ::AST.JuliaCodeOb || ::AST.MixedOb || ::AST.JuliaCodeHom || ::AST.MixedHom || ::AST.AttrOver || ::AST.HomAndAttrOver => false
  _ => true
end
