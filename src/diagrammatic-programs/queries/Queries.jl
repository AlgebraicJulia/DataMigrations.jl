""" Parse expression defining a query. """
function parse_query(C::FinCat, expr::AST.ObExpr)
  @match expr begin
    AST.ObGenerator(x) => ob_generator(C, x)
    AST.Limit(stmts) || AST.Product(stmts) =>
      parse_query_diagram(C, stmts, type=op)
    AST.Colimit(stmts) || AST.Coproduct(stmts) =>
      parse_query_diagram(C, stmts, type=id)
    AST.Terminal() => DiagramData{op}([], [], FinCat(Presentation(presentation(C).syntax)))
    AST.Initial() => DiagramData{id}([], [], FinCat(Presentation(presentation(C).syntax)))
  end
end

""" Helper function to provide parsers to `parse_diagram_data`. """
function parse_query_diagram(C::FinCat, stmts::Vector{<:AST.DiagramExpr}; kw...)
  parse_diagram_data(C, stmts;
    ob_parser = X -> parse_query(C,X),
    hom_parser = (f,X,Y) -> parse_query_hom(C,f,X,Y),kw...)
end

""" 
Get the map in the source schema corresponding to a map
of two singleton diagrams.
"""
function parse_query_hom(C::FinCat{Ob}, expr::AST.HomExpr, ::Ob, ::Union{Ob,Nothing}) where Ob
    parse_hom(C, expr)
end

""" Create DiagramHomData for the case of a map between two conjunctive diagrams. """
function parse_query_hom(C::FinCat{Ob}, ast::AST.Mapping, d::Union{Ob,DiagramData{op}}, d′::DiagramData{op}) where Ob
    ob_rhs, hom_rhs = make_ob_hom_maps(shape(d′), ast, allow_missing=d isa Ob)
    f_ob = mapvals(ob_rhs, keys=true) do j′, rhs
      parse_diagram_ob_rhs(C, rhs, ob_map(d′, j′), d)
    end
    f_hom = mapvals(rhs -> parse_hom(d, rhs), hom_rhs)
    DiagramHomData{op}(f_ob, f_hom)
end

"""
Create DiagramHomData for the case of a map from a single
  object to a conjunctive diagram.
"""
function parse_query_hom(C::FinCat{Ob}, ast::AST.Mapping, d::DiagramData{op}, c′::Ob) where Ob
    assign = only(ast.assignments)
    DiagramHomData{op}(Dict(c′=> parse_diagram_ob_rhs(C, assign.rhs, c′, d)), Dict())
end

# Gluing fragment.
#The reason for the possible argument variance mismatch seems to be that 
#you might still need to promote later on.
function parse_query_hom(C::FinCat{Ob}, ast::AST.Mapping, d::DiagramData{id},
                         d′::Union{Ob,DiagramData{op},DiagramData{id}}) where Ob
  ob_rhs, hom_rhs = make_ob_hom_maps(shape(d), ast,
                                     allow_missing=!(d′ isa DiagramData{id}))
  homnames = Symbol[nameof(x) for x in hom_generators(C)]
  params = Dict{Symbol,Any}()
  f_ob = mapvals(ob_rhs, keys=true) do j, rhs
    if rhs isa AST.MixedOb
      aux_func = make_func(rhs.jcode.mod,rhs.jcode.code,homnames)
      params[nameof(j)] = aux_func
      rhs = rhs.oexp
    end
    parse_diagram_ob_rhs(C, rhs, ob_map(d, j), d′)
  end
  f_hom = mapvals(rhs -> parse_hom(d′, rhs), hom_rhs)
  DiagramHomData{id}(f_ob, f_hom,params)
end
function parse_query_hom(C::FinCat{Obj}, ast::AST.Mapping,
                         c::Union{Obj,DiagramData{op}}, d′::DiagramData{id}) where Obj
  assign = only(ast.assignments)
  cob = c isa Obj ? c : Ob(FreeCategory,:anon_ob)
  DiagramHomData{id}(Dict(cob => parse_diagram_ob_rhs(C, assign.rhs, c, d′)), Dict())
end

#expr will be an ObExpr
function parse_diagram_ob_rhs(C::FinCat, expr, X, Y)
    @match expr begin
        AST.Apply(AST.OnlyOb(), f_expr) => (missing, parse_query_hom(C, f_expr, Y, X))
        AST.Apply(j_expr, f_expr) => let j = parse_ob(Y, j_expr)
            (j, parse_query_hom(C, f_expr, ob_map(Y, j), X))
        end
        AST.Coapply(f_expr, AST.OnlyOb()) => (missing, parse_query_hom(C, f_expr, X, Y))
        AST.Coapply(f_expr, j_expr) => let j = parse_ob(Y, j_expr)
          (j, parse_query_hom(C, f_expr, X, ob_map(Y, j)))
        end
        _ => parse_ob(Y, expr)
    end
end

parse_ob(d::DiagramData, expr::AST.ObExpr) = parse_ob(shape(d), expr)
parse_hom(d::DiagramData, expr::AST.HomExpr) = parse_hom(shape(d), expr)

parse_ob(C, ::Missing) = missing
parse_hom(C, ::Missing) = missing

include("query-construction.jl")
include("query-promotion.jl")
