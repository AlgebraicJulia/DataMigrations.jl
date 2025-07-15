""" Construct a graph in a simple, declarative style.

The syntax is reminiscent of Graphviz. Each line a declares a vertex or set of
vertices, or an edge. For example, the following defines a directed triangle:

```julia
@graph begin
  v0, v1, v2
  fst: v0 → v1
  snd: v1 → v2
  comp: v0 → v2
end
```

Vertices in the graph must be uniquely named, whereas edges names are optional.
"""
macro graph(graph_type, body)
    ast = AST.Cat(parse_diagram_ast(body))
    :(parse_graph($(esc(graph_type)), $ast))
end

macro graph(body)
    ast = AST.Cat(parse_diagram_ast(body))
    :(parse_graph(DiagramGraph, $ast))
end

function parse_graph(::Type{G}, ast::AST.Cat) where {G <: HasGraph}
    g = G()
    foreach(stmt -> parse!(g, stmt), ast.statements)
    return g
end

parse!(g::HasGraph, ob::AST.Ob) = add_vertex!(g, vname=ob.name)
parse!(g::Presentation, ob::AST.Ob) = add_generator!(g,Ob(g.syntax,ob.name))

function parse!(g::HasGraph, hom::AST.Hom)
    e = add_edge!(g, vertex_named(g, hom.src), vertex_named(g, hom.tgt))
    if has_subpart(g, :ename)
        g[e,:ename] = hom.name
    end
    return e
end

parse!(g::Presentation,hom::AST.Hom) = add_generator!(g,Hom(hom.name,generator(g,hom.src),generator(g,hom.tgt)))

# Categories
############

struct FinCatData{G<:HasGraph}
    graph::G
    equations::Vector{Pair}
end

FinCat(C::FinCatData) = isempty(C.equations) ? FinCat(C.graph) :
  FinCat(C.graph, C.equations)

""" Present a category by generators and relations.

The result is a finitely presented category (`FinCat`) represented by a graph,
possibly with path equations. For example, the simplex category truncated to one
dimension is:

```julia
@fincat begin
  V, E
  (δ₀, δ₁): V → E
  σ₀: E → V

  σ₀ ∘ δ₀ == id(V)
  σ₀ ∘ δ₁ == id(V)
end
```

The objects and morphisms must be uniquely named.
"""
macro fincat(body)
    ast = AST.Cat(parse_diagram_ast(body))
    :(parse_category(DiagramGraph, $ast))
end

function parse_category(::Type{G}, ast::AST.Cat) where
    {G <: HasGraph}
    cat = FinCatData(G(), Pair[])
    foreach(stmt -> parse!(cat, stmt), ast.statements)
    FinCat(cat)
end

parse!(C::FinCatData, stmt) = parse!(C.graph, stmt)
parse!(C::FinCatData, eq::AST.HomEq) =
  push!(C.equations, parse_path(C.graph, eq.lhs) => parse_path(C.graph, eq.rhs))

function parse_path(g::HasGraph, expr::AST.HomExpr)
  @match expr begin
    AST.HomGenerator(f::Symbol) => Path(g, edge_named(g, f))
    AST.Compose(args) => mapreduce(arg -> parse_path(g, arg), vcat, args)
    AST.Id(AST.ObGenerator(x::Symbol)) => empty(Path, g, vertex_named(g, x))
  end
end
