""" Parse category or diagram from Julia expression to AST. """
function parse_diagram_ast(body::Expr; free::Bool=false, preprocess::Bool=true,
                           mod::Module=Main)
  if preprocess
    body = reparse_arrows(body)
  end
  state = DiagramASTState()
  stmts = mapreduce(vcat, statements(body), init=AST.CatExpr[]) do expr
    @match expr begin
      # X
      X::Symbol => [AST.Ob(X)]
      # X, Y, ...
      Expr(:tuple, Xs...) => map(AST.Ob, Xs)
      # X → Y
      Expr(:call, :(→), X::Symbol, Y::Symbol) => [AST.Hom(gen_anonhom!(state), X, Y)]
      # f : X → Y
      Expr(:call, :(:), f::Symbol, Expr(:call, :(→), X::Symbol, Y::Symbol)) =>
        [AST.Hom(f, X, Y)]
      # (f, g, ...) : X → Y
      Expr(:call, (:), Expr(:tuple, fs...),
           Expr(:call, :(→), X::Symbol, Y::Symbol)) =>
        map(f -> AST.Hom(f, X, Y), fs)
      # x => X
      # x::X
      Expr(:call, :(=>), x::Symbol, X) || Expr(:(::), x::Symbol, X) =>
        [push_ob_over!(state, AST.ObOver(x, parse_ob_ast(X)))]
      # (x, y, ...) => X
      # (x, y, ...)::X
      Expr(:call, :(=>), Expr(:tuple, xs...), X) ||
      Expr(:(::), Expr(:tuple, xs...), X) => let ob = parse_ob_ast(X)
        map(x -> push_ob_over!(state, AST.ObOver(x, ob)), xs)
      end
      # h could be Julia if y is over an attr
      # (f: x → y) :: ([weight(d),weight∘height(x)],7)
      # (f: x → y) => h
      # (f: x → y)::h
      Expr(:call, :(=>), Expr(:call, :(:), f::Symbol,
                              Expr(:call, :(→), x::Symbol, y::Symbol)), h) ||
      Expr(:(::), Expr(:call, :(:), f::Symbol,
      Expr(:call, :(→), x::Symbol, y::Symbol)), h) => begin
        parse_hom_over(f,x,y,state.ob_over[x],state.ob_over[y],h,mod=mod)
      end
      # (x → y) => h
      # (x → y)::h
      Expr(:call, :(=>), Expr(:call, :(→), x::Symbol, y::Symbol), h) ||
      Expr(:(::), Expr(:call, :(→), x::Symbol, y::Symbol), h) => 
        parse_hom_over(gen_anonhom!(state),x,y,state.ob_over[x],state.ob_over[y],h,mod=mod)

      # x == "foo"
      # "foo" == x
      Expr(:call, :(==), x::Symbol, value::Literal) ||
      Expr(:call, :(==), value::Literal, x::Symbol) =>
        [AST.AssignValue(x, get_literal(value))]
      # x == $(...)
      # $(...) == x
      Expr(:call, :(==), x::Symbol, Expr(:$, value_expr)) ||
      Expr(:call, :(==), Expr(:$, value_expr)) =>
        [AST.AssignValue(x, mod.eval(value_expr))]
     
      # h(x) == y
      # y == h(x)
      (Expr(:call, :(==), call::Expr, y::Symbol) ||
       Expr(:call, :(==), y::Symbol, call::Expr)) && if free end => begin
         h, x = destructure_unary_call(call) 
         X, Y, z = state.ob_over[x], state.ob_over[y], gen_anonhom!(state)
         [AST.HomOver(z, x, y, parse_hom_ast(h, X, Y,mod=mod))]
       end
      # h(x) == "foo"
      # "foo" == h(x)
      (Expr(:call, :(==), call::Expr, value::Literal) ||
       Expr(:call, :(==), value::Literal, call::Expr)) && if free end => begin
         h, x = destructure_unary_call(call)
         X, y, z = state.ob_over[x], gen_anonob!(state), gen_anonhom!(state)
         [AST.ObOver(y, nothing),
          AST.AssignValue(y, get_literal(value)),
          AST.HomOver(z, x, y, parse_hom_ast(h, X))]
       end
      # h(x) == $(...)
      # $(...) == h(x)
      (Expr(:call, :(==), call::Expr, Expr(:$, value_expr)) ||
       Expr(:call, :(==), Expr(:$, value_expr), call::Expr)) && if free end => begin
         h, x = destructure_unary_call(call)
         X, y, z = state.ob_over[x], gen_anonob!(state), gen_anonhom!(state)
         [AST.ObOver(y, nothing),
          AST.AssignValue(y, mod.eval(value_expr)),
          AST.HomOver(z, x, y, parse_hom_ast(h, X))]
       end

      # h(x) == k(y)
      Expr(:call, :(==), lhs::Expr, rhs::Expr) && if free end => begin
        (h, x), (k, y) = destructure_unary_call(lhs), destructure_unary_call(rhs)
        z, p, q = gen_anonob!(state), gen_anonhom!(state), gen_anonhom!(state)
        X, Y = state.ob_over[x], state.ob_over[y]
        # Assumes that codomain not needed to parse morphisms.
        [AST.ObOver(z, nothing),
         AST.HomOver(p, x, z, parse_hom_ast(h, X,mod=mod)),
         AST.HomOver(q, y, z, parse_hom_ast(k, Y,mod=mod))]
      end

      # f == g
      Expr(:call, :(==), lhs, rhs) && if !free end =>
        [AST.HomEq(parse_hom_ast(lhs,mod=mod), parse_hom_ast(rhs,mod=mod))]
      ::LineNumberNode => AST.CatExpr[]
      _ => error("Cannot parse statement in category/diagram definition: $expr")
    end
  end
  return stmts
end

function parse_hom_over(name,x,y,X,Y,rhs;mod::Module=Main)
  @match rhs begin
    #a(e) |> (x-> f(x))
    Expr(:call,:(|>),l,r) =>
      [AST.HomAndAttrOver(AST.HomOver(name,x,y,parse_hom_ast(l,X,Y,mod=mod)),
       AST.AttrOver(name,x,y,r,mod))]
    #A hom mapping to a lambda expression, or to a block ending with a lambda
    #expression, will be temporarily assigned to a blank value to be filled
    #with Julia code evaluated in the acset to be migrated.
    Expr(:(->),_...) => [AST.AttrOver(name,x,y,rhs,mod)]
    Expr(:block,args) =>
      @match args[end] begin
        Expr(:(->),_...) => [AST.AttrOver(name,x,y,rhs,mod)]
        _ => [AST.HomOver(name,x,y,parse_hom_ast(rhs,X,Y,mod=mod))]
    end
    _ => [AST.HomOver(name,x,y,parse_hom_ast(rhs,X,Y,mod=mod))] 
  end
end

"""
Counts anonymous objects and homs to allow them unique internal refs.
Tracks names of objects to avoid multiple objects with the same name.
Doesn't track names for homs since it doesn't matter for eg free diagrams;
macros like fincat will handle hom uniqueness for themselves.

Note that ob_over[x] is the object of the base which x is over, perhaps
confusingly.
"""
Base.@kwdef mutable struct DiagramASTState
  nanonob::Int=0 
  nanonhom::Int=0
  ob_over::Dict{Symbol,AST.ObExpr} = Dict{Symbol,AST.ObExpr}()
end
gen_anonob!(state::DiagramASTState) = Symbol("##unnamedob#$(state.nanonob += 1)")
gen_anonhom!(state::DiagramASTState) = Symbol("##unnamedhom#$(state.nanonhom += 1)")

function push_ob_over!(state::DiagramASTState, ob::AST.ObOver)
  isnothing(ob.name) && return ob
  haskey(state.ob_over, ob.name) &&
    error("Object with name $ob has already been defined")
  state.ob_over[ob.name] = ob.over
  return ob
end

""" Parse object expression from Julia expression to AST.
"""
function parse_ob_ast(expr;kw...)::AST.ObExpr
  @match expr begin
    Expr(:macrocall, _...) => parse_ob_macro_ast(expr;kw...) 
    #XXX: This should probably handle @julia_code
    x::Symbol || Expr(:curly, _...) => AST.ObGenerator(expr)
    _ => error("Invalid object expression $expr")
  end
end
const compose_ops = (:(⋅), :(⨟), :(∘))

function parse_ob_macro_ast(expr;kw...)::AST.ObExpr
  @match expr begin
    Expr(:macrocall, form, ::LineNumberNode, args...) =>
      parse_ob_macro_ast(Expr(:macrocall, form, args...);kw...)
    Expr(:macrocall, &(Symbol("@limit")), body) ||
    Expr(:macrocall, &(Symbol("@join")), body) =>
      AST.Limit(parse_diagram_ast(body, free=true, preprocess=false;kw...))
    Expr(:macrocall, &(Symbol("@product")), body) =>
      AST.Product(parse_diagram_ast(body, free=true, preprocess=false;kw...))
    Expr(:macrocall, &(Symbol("@terminal"))) ||
    Expr(:macrocall, &(Symbol("@unit"))) =>
      AST.Terminal()
    Expr(:macrocall, &(Symbol("@colimit")), body) ||
    Expr(:macrocall, &(Symbol("@glue")), body) =>
      AST.Colimit(parse_diagram_ast(body, free=true, preprocess=false;kw...))
    Expr(:macrocall, &(Symbol("@coproduct")), body) ||
    Expr(:macrocall, &(Symbol("@cases")), body) =>
      AST.Coproduct(parse_diagram_ast(body, free=true, preprocess=false;kw...))
    Expr(:macrocall, &(Symbol("@initial"))) ||
    Expr(:macrocall, &(Symbol("@empty"))) =>
      AST.Initial()
    _ => error("Invalid object macro $expr")
  end
end

""" Parse morphism expression from Julia expression to AST.
"""
function parse_hom_ast(expr, dom::Union{AST.ObGenerator,Nothing}=nothing,
                       codom::Union{AST.ObGenerator,Nothing}=nothing;mod::Module=Main)
  # Domain and codomain are not used, but may be supplied for uniformity.
  @match expr begin
    Expr(:call, :compose, args...) => AST.Compose(map(x->parse_hom_ast(x,mod=mod), args))
    Expr(:call, :(⋅), f, g) || Expr(:call, :(⨟), f, g) =>
      AST.Compose([parse_hom_ast(f,mod=mod), parse_hom_ast(g,mod=mod)])
    Expr(:call, :(∘), f, g) => AST.Compose([parse_hom_ast(g,mod=mod), parse_hom_ast(f,mod=mod)])
    Expr(:call, :id, x) => AST.Id(parse_ob_ast(x))
    f::Symbol || Expr(:curly, _...) => AST.HomGenerator(expr)
    Expr(:block,args...) => AST.JuliaCodeHom(expr,mod)
    Expr(:(->),inputs,body) => AST.JuliaCodeHom(expr,mod)
    _ => error("Invalid morphism expression $expr")
  end
end

"""Limit fragment: initial parsing for homs between conjunctive diagrams 
 and/or single objects. The components of the output AST 
 encode both the functor and natural transformations
 parts of a diagram morphism, so it's semantically non-obvious whether they
 should be ObExprs or HomExprs; we choose the former somewhat arbitrarily.
"""
function parse_hom_ast(expr, dom::AST.LimitExpr, cod::AST.LimitExpr;mod::Module=Main)
    parse_mapping_ast((args...) -> parse_apply_ast(args..., dom,mod=mod), expr, cod,mod=mod)
end

function parse_hom_ast(expr, dom::AST.ObGenerator, cod::AST.LimitExpr;mod::Module=Main)
    parse_mapping_ast(expr, cod,mod=mod) do (args...)
        AST.Apply(AST.OnlyOb(), parse_hom_ast(args..., dom;mod=mod))
    end
end

function parse_hom_ast(expr, dom::AST.LimitExpr, cod::AST.ObGenerator;mod::Module=Main)
    f(ex) = [AST.ObAssign(AST.OnlyOb(),ex)] |> AST.Mapping
    @match expr begin
        Expr(:(->),inputs,body) => f(AST.JuliaCodeOb(expr,mod))
        Expr(:block,args...) => f(AST.JuliaCodeOb(expr,mod))
        _ => f(parse_apply_ast(expr, cod, dom,mod=mod))
    end
end

# Colimit fragment.
function parse_hom_ast(expr, dom::AST.ColimitExpr, cod::AST.ColimitExpr;mod::Module=Main)
    parse_mapping_ast((args...) -> parse_coapply_ast(args..., cod,mod=mod), expr, dom,mod=mod)
end

function parse_hom_ast(expr, dom::Union{AST.ObGenerator,AST.LimitExpr},
                       cod::AST.ColimitExpr;mod::Module=Main)
    [AST.ObAssign(AST.OnlyOb(), parse_coapply_ast(expr, dom, cod,mod=mod))] |> AST.Mapping
end

function parse_hom_ast(expr, dom::AST.ColimitExpr,
                       cod::Union{AST.ObGenerator,AST.LimitExpr};mod::Module=Main)
    parse_mapping_ast(expr, dom,mod=mod) do (args...)
        AST.Coapply(parse_hom_ast(args..., cod;mod=mod), AST.OnlyOb())
    end
end


""" Parse object/morphism mapping from Julia expression to AST.
"""
function parse_mapping_ast(f_parse_ob_assign, body, dom; preprocess::Bool=false,mod::Module=Main)
  #Default f_parse_ob_assign is (rhs, _) -> parse_ob_ast(rhs)
  if preprocess
    body = reparse_arrows(body)
  end
  ob_map = Dict{Symbol,AST.ObExpr}()
  get_ob(x) = get(ob_map, x) do
    error("Morphism assigned before assigning (co)domain $x")
  end
  dom_obs, dom_homs = Dict(ob_over_pairs(dom)), Dict(hom_over_pairs(dom))
  stmts = mapreduce(vcat, statements(body), init=AST.AssignExpr[]) do expr
    @match expr begin
      # lhs => rhs
      Expr(:call,:(=>),lhs::Symbol,Expr(:call,:(|>),rlhs,rrhs)) => begin
        if lhs ∈ keys(dom_obs)
          x, X = lhs, dom_obs[lhs]
          ob_map[x] = x′ = f_parse_ob_assign(rlhs, X)
          [AST.ObAssign(AST.ObGenerator(x),AST.MixedOb(x′,AST.JuliaCodeOb(rrhs,mod)))]
        elseif lhs ∈ keys(dom_homs)
          f, (x, y) = lhs, dom_homs[lhs]
          x′, y′ = get_ob(x), get_ob(y)
          f′ = parse_hom_ast(rlhs, x′, y′;mod=mod)
          [AST.HomAssign(AST.HomGenerator(f),
                         AST.MixedHom(f′,AST.JuliaCodeHom(rrhs,mod)))]
        end             
      end
      Expr(:call, :(=>), lhs::Symbol, rhs) => begin
        if lhs ∈ keys(dom_obs)
          x, X = lhs, dom_obs[lhs]
          ob_map[x] = x′ = f_parse_ob_assign(rhs, X)
          [AST.ObAssign(AST.ObGenerator(x), x′)]
        elseif lhs ∈ keys(dom_homs)
          f, (x, y) = lhs, dom_homs[lhs]
          x′, y′ = get_ob(x), get_ob(y)
          f′ = parse_hom_ast(rhs, x′, y′;mod=mod)
          [AST.HomAssign(AST.HomGenerator(f), f′)]
        else
          error("$lhs is not the name of an object or morphism generator")
        end
      end
      # (lhs, lhs′, ...) => rhs
      Expr(:call, :(=>), Expr(:tuple, lhs...), rhs) => begin
        if all(∈(keys(dom_obs)), lhs)
          X = only(unique(dom_obs[x] for x in lhs))
          x′ = f_parse_ob_assign(rhs, X)
          for x in lhs; ob_map[x] = x′ end
          map(x -> AST.ObAssign(AST.ObGenerator(x), x′), lhs)
        elseif all(∈(keys(dom_homs)), lhs)
          x′, y′ = only(unique(
            (let (x,y) = dom_homs[f]; get_ob(x) => get_ob(y) end for f in lhs)))
          f′ = parse_hom_ast(rhs, x′, y′;mod=mod)
          map(f -> AST.HomAssign(AST.HomGenerator(f), f′), lhs)
        else
          error("$lhs are not all names of object or morphism generators")
        end
      end
      ::LineNumberNode => AST.AssignExpr[]
      _ => error("Cannot parse object or morphism assignment: $expr")
    end
  end
  AST.Mapping(stmts)
end
function parse_mapping_ast(body, dom; kw...)
  parse_mapping_ast((rhs, _) -> parse_ob_ast(rhs), body, dom; kw...)
end

function parse_apply_ast(expr, X, target;mod::Module=Main)
  y::Symbol, f = @match expr begin
    ::Symbol => (expr, nothing)
    Expr(:call, op, _...) && if op ∈ compose_ops end =>
      leftmost_arg(expr, (:(⋅), :(⨟)), all_ops=compose_ops)
    Expr(:call, name::Symbol, _) => reverse(destructure_unary_call(expr))
    _ => error("Cannot parse object assignment in migration: $expr")
  end
  isnothing(f) && return AST.ObGenerator(y)
  Y = only(Y′ for (y′,Y′) in ob_over_pairs(target) if y == y′)
  AST.Apply(AST.ObGenerator(y), parse_hom_ast(f, Y, X;mod=mod))
end

function parse_coapply_ast(expr, X, target;mod::Module=Main)
  y::Symbol, f = @match expr begin
    ::Symbol => (expr, nothing)
    Expr(:call, op, _...) && if op ∈ compose_ops end =>
      leftmost_arg(expr, (:(∘),), all_ops=compose_ops)
    _ => error("Cannot parse object assignment in migration: $expr")
  end
  isnothing(f) && return AST.ObGenerator(y)
  Y = only(Y′ for (y′,Y′) in ob_over_pairs(target) if y == y′)
  AST.Coapply(parse_hom_ast(f, X, Y;mod=mod), AST.ObGenerator(y))
end

ob_over_pairs(expr) = AST.ob_over_pairs(expr)
ob_over_pairs(C::FinCat) =
  (ob_generator_name(C,x) => nothing for x in ob_generators(C))

hom_over_pairs(expr) = AST.hom_over_pairs(expr)
hom_over_pairs(C::FinCat) = begin
  (hom_generator_name(C,f) =>
    (ob_generator_name(C,dom(C,f)) => ob_generator_name(C,codom(C,f)))
   for f in hom_generators(C))
end


