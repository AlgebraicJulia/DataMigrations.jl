""" Define a functor between two finitely presented categories.

Such a functor is defined by sending the object and morphism generators of the
domain category to generic object and morphism expressions in the codomain
category. For example, the following functor embeds the schema for graphs into
the schema for circular port graphs by ignoring the ports:

```julia
@finfunctor SchGraph SchCPortGraph begin
  V => Box
  E => Wire
  src => src ⨟ box
  tgt => tgt ⨟ box
end
```

A constructor exists that purports to allow the user to check that a proposed
functor satisfies relations in the domain, but this functionality doesn't
yet exist (and the problem is undecidable in general.) Thus the only check
is that the source and target of the image of an arrow are the image of its
source and target.
"""
macro finfunctor(dom_cat, codom_cat, check_equations, body)
  check_equations = get_keyword_arg_val(check_equations) 
  # Cannot parse Julia expr during expansion because domain category is needed.
  :(parse_functor($(esc(dom_cat)), $(esc(codom_cat)), $(Meta.quot(body)),
                  check_equations=$check_equations))
end

macro finfunctor(dom_cat, codom_cat, body)
  :(parse_functor($(esc(dom_cat)), $(esc(codom_cat)), $(Meta.quot(body))))
end

function parse_functor(C::FinCat, D::FinCat, ast::AST.Mapping;
                       check_equations::Bool=false)
  ob_map, hom_map = make_ob_hom_maps(C, ast)
  F = FinFunctor(mapvals(x -> parse_ob(D, x), ob_map),
                 mapvals(f -> parse_hom(D, f), hom_map), C, D)
  failures = functoriality_failures(F, check_equations=check_equations)
  if !all(isempty,failures)
    doms, cods = failures[1], failures[2]
    doms = map(x -> hom_generator_name(C,x),doms)
    cods = map(x -> hom_generator_name(C,x),cods)
    error("Parsed functor is not functorial. " *
          "Images of domain differing from domain of image: $doms " *
          "Images of codomain differing from codomain of image: $cods")
  end
  F
end

parse_functor(C::FinCat, D::FinCat, body::Expr; kw...) =
  parse_functor(C, D, parse_mapping_ast(body, C); kw...)
parse_functor(C::Presentation, D::Presentation, args...; kw...) =
  parse_functor(FinCat(C), FinCat(D), args...; kw...)

"""
Converts an `AST.Mapping` of object and hom assignments to a pair
of dictionaries indexed by the generators (note: not their names!)
of the source schema `C`. 
"""
function make_ob_hom_maps(C::FinCat, ast; allow_missing::Bool=false,
                          missing_ob::Bool=false, missing_hom::Bool=false)
  allow_missing && (missing_ob = missing_hom = true)
  ob_assign = Dict(a.lhs.name => a.rhs
                   for a in ast.assignments if a isa AST.ObAssign)
  hom_assign = Dict(a.lhs.name => a.rhs
                    for a in ast.assignments if a isa AST.HomAssign)
  ob_map = make_map(ob_generators(C)) do x
    y = pop!(ob_assign, ob_generator_name(C, x), missing)
    (!ismissing(y) || missing_ob) ? y :
      error("Object $(ob_generator_name(C,x)) is not assigned")
  end
  hom_map = make_map(hom_generators(C)) do f
    g = pop!(hom_assign, hom_generator_name(C, f), missing)
    (!ismissing(g) || missing_hom) ? g :
      error("Morphism $(hom_generator_name(C,f)) is not assigned")
  end
  isempty(ob_assign) || error("Unused object assignment(s): $(keys(ob_assign))")
  isempty(hom_assign) || error("Unused morphism assignment(s): $(keys(hom_assign))")
  (ob_map, hom_map)
end

""" Parse expression for object in a category.
"""
function parse_ob(C::FinCat{Ob,Hom}, expr::AST.ObExpr) where {Ob,Hom}
  @match expr begin
    AST.ObGenerator(name) => @match name begin
      x::Symbol => ob_generator(C, x)
      Expr(:curly, _...) => parse_gat_expr(C, name)::Ob
      _ => error("Invalid object generator $name")
    end
    AST.OnlyOb() => only(ob_generators(C))
  end
end

""" Parse expression for morphism in a category.
"""
function parse_hom(C::FinCat{Ob,Hom}, expr::AST.HomExpr) where {Ob,Hom}
  @match expr begin
    AST.HomGenerator(name) => @match name begin
      f::Symbol => hom_generator(C, f)
      Expr(:curly, _...) => parse_gat_expr(C, name)::Hom
      _ => error("Invalid morphism generator $name")
    end
    AST.Compose(args) => mapreduce(
      arg -> parse_hom(C, arg), (fs...) -> compose(C, fs...), args)
    AST.Id(x) => id(C, parse_ob(C, x))
    AST.JuliaCodeHom(expr,mod) => nothing #will get dom and codom later
    AST.MixedHom(hexp,jcode) => parse_hom(C,hexp)
  end
end

""" Parse GAT expression based on curly braces, rather than parentheses.
"""
function parse_gat_expr(C::FinCat, root_expr)
  pres = presentation(C)
  function parse(expr)
    @match expr begin
      Expr(:curly, head::Symbol, args...) =>
        invoke_term(pres.syntax, head, map(parse, args))
      x::Symbol => generator(pres, x)
      _ => error("Invalid GAT expression $root_expr")
    end
  end
  parse(root_expr)
end
