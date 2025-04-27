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


