""" DSLs for defining categories, diagrams, and related structures.

Here "diagram" means diagram in the standard category-theoretic sense, not
string diagram or wiring diagram. DSLs for constructing wiring diagrams are
provided by other submodules.
"""

module DiagrammaticPrograms
export @graph, @fincat, @finfunctor, @diagram, @free_diagram,
  @migrate, @migration, @acset_colim

using Base.Iterators: repeated
using MLStyle: @match

using Catlab
using Catlab.Theories: munit, FreeSchema, FreePointedSetSchema, ThPointedSetSchema, FreeCategory, FreePointedSetCategory, zeromap, Ob, Hom, dom, codom, HomExpr
using Catlab.CategoricalAlgebra.FinCats: FinCat, mapvals, make_map, FinCatPresentation
using ..Migrations
using ..Migrations: ConjQuery, GlueQuery, GlucQuery
using GATlab
import GATlab: Presentation
import GATlab.Models.Presentations:construct_generator!,construct_generators!
const DiagramGraph = NamedGraph{Symbol,Symbol}

include("ast.jl")
include("graphs.jl")
include("functors.jl")
include("diagrams.jl")
include("migrations.jl")
include("query-parsing.jl")
include("expr-to-ast.jl")

@reexport using .AST

# Julia expression utilities
############################

# Literals recognized by the Julia parser, where quote nodes will be accepted
# only if they contain symbols, hence are symbol literals.
const Literal = Union{Bool,Number,Char,String,QuoteNode}

get_literal(value::Literal) = value
get_literal(node::QuoteNode) = node.value::Symbol

statements(expr) = (expr isa Expr && expr.head == :block) ? expr.args : [expr]

""" Reparse Julia expressions for function/arrow types.

In Julia, `f : x → y` is parsed as `(f : x) → y` instead of `f : (x → y)`.
"""
function reparse_arrows(expr)
  @match expr begin
    Expr(:call, :(→), Expr(:call, :(:), f, x), y) =>
      Expr(:call, :(:), f, Expr(:call, :(→), x, y))
    Expr(head, args...) => Expr(head, (reparse_arrows(arg) for arg in args)...)
    _ => expr
  end
end
function make_func(mod::Module,body::Expr,vars::Vector{Symbol})
  expr = Expr(:(->),Expr(:tuple,vars...),body)
  mod.eval(expr)
end
""" Left-most argument plus remainder of left-associated binary operations.
`ops` denotes the operations that won't need to be reversed for the desired
parser output (AST.Apply or AST.Coapply).
"""
function leftmost_arg(expr, ops; all_ops=nothing)
  isnothing(all_ops) && (all_ops = ops)
  function leftmost(expr)
    @match expr begin
      Expr(:call, op2, Expr(:call, op1, x, y), z) &&
          if op1 ∈ all_ops && op2 ∈ all_ops end => begin
        x, rest = leftmost(Expr(:call, op1, x, y))
        (x, Expr(:call, op2, rest, z))
      end
      Expr(:call, op, x, y) && if op ∈ ops end => (x, y)
      Expr(:call, op, x, y) => (y,x)
      _ => (nothing, expr)
    end
  end
  leftmost(expr)
end

""" Destructure Julia expression `:(f(g(x)))` to `(:(f∘g), :x)`, for example.
"""
function destructure_unary_call(expr::Expr)
  @match expr begin
    Expr(:call, head, x::Symbol) => (head, x)
    Expr(:call, head, arg) => begin
      rest, x = destructure_unary_call(arg)
      (Expr(:call, :(∘), head, rest), x)
    end
  end
end

"""
Return the right-hand side of the assignment in an expression of the form
`:(var=val)`.
"""
function get_keyword_arg_val(expr::Expr)
  @match expr begin
    Expr(:(=),var,x) => x
    _ => error("Unexpected argument $expr."*
               "Acceptable inputs are of the form `:(var=val)`.")
  end
end
end
