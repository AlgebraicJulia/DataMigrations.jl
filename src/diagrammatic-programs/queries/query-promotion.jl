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
