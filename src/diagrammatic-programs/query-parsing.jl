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
function parse_query_hom(C::FinCat{Ob}, expr::AST.HomExpr,
                         ::Ob, ::Union{Ob,Nothing}) where Ob
  parse_hom(C, expr)
end

# Conjunctive fragment.
"""
Create DiagramHomData for the case of a map between two
  conjunctive diagrams.
"""
function parse_query_hom(C::FinCat{Ob}, ast::AST.Mapping,
                         d::Union{Ob,DiagramData{op}}, d′::DiagramData{op}) where Ob
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
function parse_query_hom(C::FinCat{Ob}, ast::AST.Mapping,
                         d::DiagramData{op}, c′::Ob) where Ob
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
    AST.Apply(AST.OnlyOb(), f_expr) =>
      (missing, parse_query_hom(C, f_expr, Y, X))
    AST.Apply(j_expr, f_expr) => let j = parse_ob(Y, j_expr)
      (j, parse_query_hom(C, f_expr, ob_map(Y, j), X))
    end
    AST.Coapply(f_expr, AST.OnlyOb()) =>
      (missing, parse_query_hom(C, f_expr, X, Y))
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

# Query construction
#-------------------

function make_query(C::FinCat{Ob}, data::DiagramData{T}) where {T, Ob}
  F_ob, F_hom, J = data.ob_map, data.hom_map, shape(data)
  F_hom = mapvals((h,f) -> isnothing(f) ? zeromap(F_ob[dom(J,h)],F_ob[codom(J,h)]) : f,F_hom;keys=true)
  F_ob = mapvals(x -> make_query(C, x), F_ob)
  query_type = mapreduce(typeof, promote_query_type, values(F_ob), init=Ob)
  @assert query_type != Any
  F_ob = mapvals(x -> convert_query(C, query_type, x), F_ob)
  F_hom = mapvals(F_hom;keys=true) do h,f
    d,c = F_ob[dom(J,h)],F_ob[codom(J,h)]
    make_query_hom(C,f,d,c)
  end
  if query_type <: Ob
    Diagram(DiagramData{T}(F_ob, F_hom, J, data.params), C)
  else
    # XXX: Why is the element type of `F_ob` sometimes too loose?
    D = TypeCat(typeintersect(query_type, eltype(values(F_ob))),
                eltype(values(F_hom)))
    Diagram(DiagramData{T}(F_ob, F_hom, J,data.params), D)
  end
end

make_query(C::FinCat{Ob}, x::Ob) where Ob = x

function make_query_hom(C::FinCat, f::DiagramHomData{op},
                        d::Diagram{op}, d′::Diagram{op})
  f_ob = mapvals(f.ob_map, keys=true) do j′, x
    x = @match x begin
      ::Missing => only_ob(shape(d))
      (::Missing, g) => (only_ob(shape(d)), g)
      _ => x
    end
    @match x begin
      (j, g) => Pair(j, make_query_hom(C, g, ob_map(d, j), ob_map(d′, j′)))
      j => j
    end
  end
  f_hom = mapvals(h -> ismissing(h) ? only_hom(shape(d)) : h, f.hom_map)
  DiagramHom{op}(f_ob, f_hom, d, d′)
end

function make_query_hom(C::FinCat, f::DiagramHomData{id},
                        d::Diagram{id}, d′::Diagram{id})
  f_ob = mapvals(f.ob_map, keys=true) do j, x
    x = @match x begin
      ::Missing => only_ob(shape(d′))
      (::Missing, g) => (only_ob(shape(d′)), g)
      _ => x
    end
    @match x begin
      (j′, g) => begin 
        s,t = ob_map(d, j), ob_map(d′, j′)
        g = isnothing(g) ? zeromap(s,t) : g
        Pair(j′, make_query_hom(C, g, s,t))
      end
      j′ => j′
    end
  end
  f_hom = mapvals(h -> ismissing(h) ? only_hom(shape(d′)) : h, f.hom_map)
  QueryDiagramHom{id}(f.params,f_ob, f_hom, d, d′)
end

"""If d,d' are singleton diagrams and f hasn't yet been specified, make a DiagramHom with the right
domain, codomain, and shape_map but the natural transformation component left as GATExpr{:zeromap} for now.
Otherwise just wrap f up as a DiagramHom between singletons.
"""
function make_query_hom(::C, f::Hom, d::Diagram{T,C}, d′::Diagram{T,C}) where
    {T, Ob, Hom, C<:FinCat{Ob,Hom}}
  munit(DiagramHom{T}, codom(diagram(d)), f,
  dom_shape=shape(d), codom_shape=shape(d′))
end
function make_query_hom(::C, f::HomExpr{:zeromap}, d::Diagram{T,C}, d′::Diagram{T,C}) where {T,C<:FinCat}
  j′ = only(ob_generators(shape(d′)))
  j = only(ob_generators(shape(d)))
  DiagramHom{T}(Dict(j=> Pair(j′,f)),d,d′)
end

function make_query_hom(::C, f::Hom, d::Diagram{op,C}, d′::Diagram{op,C}) where
    {Ob, Hom, C<:FinCat{Ob,Hom}}
  munit(DiagramHom{op}, codom(diagram(d)), f,
  dom_shape=shape(d), codom_shape=shape(d′))
end

function make_query_hom(::C, f::HomExpr{:zeromap}, d::Diagram{op,C}, d′::Diagram{op,C}) where C<:FinCat
  j′ = only(ob_generators(shape(d′)))
  j = only(ob_generators(shape(d)))
  DiagramHom{op}(Dict(j′=> Pair(j,f)),d,d′)
end
function make_query_hom(c::C, f::Union{Hom,DiagramHomData{op}},
                        d::Diagram{id}, d′::Diagram{id}) where
    {Ob, Hom, C<:FinCat{Ob,Hom}}
  f′ = make_query_hom(c, f, only(collect_ob(d)), only(collect_ob(d′)))
  munit(DiagramHom{id}, codom(diagram(d)), f′, dom_shape=shape(d), codom_shape=shape(d′))
end

make_query_hom(C::FinCat{Ob,Hom}, f::Hom, x::Ob, y::Ob) where {Ob,Hom} = f

only_ob(C::FinCat) = only(ob_generators(C))
only_hom(C::FinCat) = (@assert is_discrete(C); id(C, only_ob(C)))

# Query promotion
#----------------

# Promotion of query types is modeled loosely on Julia's type promotion system:
# https://docs.julialang.org/en/v1/manual/conversion-and-promotion/

promote_query_rule(::Type, ::Type) = Union{}
promote_query_rule(::Type{<:ConjQuery{C}}, ::Type{<:Ob}) where {Ob,C<:FinCat{Ob}} =
  ConjQuery{C}
promote_query_rule(::Type{<:GlueQuery{C}}, ::Type{<:Ob}) where {Ob,C<:FinCat{Ob}} =
  GlueQuery{C}
promote_query_rule(::Type{<:GlucQuery{C}}, ::Type{<:Ob}) where {Ob,C<:FinCat{Ob}} =
  GlucQuery{C}
promote_query_rule(::Type{<:GlueQuery{C}}, ::Type{<:ConjQuery{C}}) where C =
  GlucQuery{C}
promote_query_rule(::Type{<:GlucQuery{C}}, ::Type{<:ConjQuery{C}}) where C =
  GlucQuery{C}
promote_query_rule(::Type{<:GlucQuery{C}}, ::Type{<:GlueQuery{C}}) where C =
  GlucQuery{C}

promote_query_type(T, S) = promote_query_result(
  T, S, Union{promote_query_rule(T,S), promote_query_rule(S,T)})
promote_query_result(T, S, ::Type{Union{}}) = typejoin(T, S)
promote_query_result(T, S, U) = U

convert_query(::FinCat, ::Type{T}, x::S) where {T, S<:T} = x

function convert_query(cat::C, ::Type{<:Diagram{T,C}}, x::Obj) where
  {T, Obj, C<:FinCat{Obj}}
  s = presentation(cat).syntax 
  p = Presentation(s)
  add_generator!(p,Ob(s,nameof(x)))
  munit(Diagram{T}, cat, x, shape=FinCat(p))
end
function convert_query(::C, ::Type{<:GlucQuery{C}}, d::ConjQuery{C}) where C
  s = FreeCategory
  p = Presentation(s)
  add_generator!(p,Ob(s,Symbol("anon_ob")))
  munit(Diagram{id}, TypeCat(ConjQuery{C}, Any), d; shape=FinCat(p))
end
function convert_query(cat::C, ::Type{<:GlucQuery{C}}, d::GlueQuery{C}) where C
  J = shape(d)
  new_ob = make_map(ob_generators(J)) do j
    convert_query(cat, ConjQuery{C}, ob_map(d, j))
  end
  new_hom = make_map(hom_generators(J)) do h
    munit(Diagram{op}, cat, hom_map(d, h),
          dom_shape=new_ob[dom(J,h)], codom_shape=new_ob[codom(J,h)])
  end
  Diagram{id}(FinDomFunctor(new_ob, new_hom, J, TypeCat(ConjQuery{C}, Any)))
end
function convert_query(cat::C, ::Type{<:GlucQuery{C}}, x::Ob) where
    {Ob, C<:FinCat{Ob}}
  convert_query(cat, GlucQuery{C}, convert_query(cat, ConjQuery{C}, x))
end
