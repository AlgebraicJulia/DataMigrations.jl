""" Abstract syntax trees for category and diagram DSLs. """
module AST

using MLStyle

abstract type ObExpr end
abstract type HomExpr end
abstract type AssignExpr end

export ObExpr, HomExpr, AssignExpr

@data ObExpr begin
  ObGenerator(name)
  OnlyOb()
  Apply(ob::ObExpr, hom::HomExpr)
  Coapply(hom::HomExpr, ob::ObExpr)
  JuliaCodeOb(code::Expr,mod::Module)
  MixedOb(oexp::ObExpr,jcode::JuliaCodeOb)
end

@data HomExpr begin
  HomGenerator(name)
  Compose(homs::Vector{<:HomExpr})
  Id(ob::ObExpr)
  Mapping(assignments::Vector{<:AssignExpr})
  JuliaCodeHom(code::Expr,mod::Module)
  MixedHom(hexp::HomExpr,jcode::JuliaCodeHom)
end

@data DiagramExpr begin
  ObOver(name::Symbol, over::Union{ObExpr,Nothing}) 
  HomOver(name::Symbol, src::Symbol, tgt::Symbol, over::HomExpr)
  AttrOver(name::Symbol, src::Symbol, tgt::Symbol, aux_func_def::Expr, mod::Module) # XXX: make JuliaCode
  HomAndAttrOver(lhs::HomOver,rhs::AttrOver)
  AssignValue(name::Symbol, value)
end
export DiagramExpr, ObOver, HomOver

@data CatExpr <: DiagramExpr begin
  Ob(name::Symbol)
  Hom(name::Symbol, src::Symbol, tgt::Symbol)
  HomEq(lhs::HomExpr, rhs::HomExpr)
end

@data CatDefinition begin
  Cat(statements::Vector{<:CatExpr})
  Diagram(statements::Vector{<:DiagramExpr})
end

@data LimitExpr <: ObExpr begin
  Limit(statements::Vector{<:DiagramExpr})
  Product(statements::Vector{ObOver})
  Terminal()
end
@data ColimitExpr <: ObExpr begin
  Colimit(statements::Vector{<:DiagramExpr})
  Coproduct(statements::Vector{ObOver})
  Initial()
end

@data AssignExpr begin
  ObAssign(lhs::Union{ObGenerator,OnlyOb}, rhs::ObExpr)
  HomAssign(lhs::HomGenerator, rhs::HomExpr)
end

function ob_over_pairs(expr::Union{Diagram,ObExpr})
  @match expr begin
    Diagram(statements) || Limit(statements) || Colimit(statements) =>
      (ob.name => ob.over for ob in statements if ob isa AST.ObOver)
    Product(statements) || Coproduct(statements) =>
      (ob.name => ob.over for ob in statements)
    Terminal() || Initial() => ()
	# TODO OnlyOb case not handled!
  end
end

function hom_over_pairs(expr::Union{Diagram,ObExpr})
  @match expr begin
    Diagram(statements) || Limit(statements) || Colimit(statements) =>
      (hom.name => (hom.src => hom.tgt)
       for hom in statements if hom isa Union{AST.HomOver,AST.AttrOver})
    _ => ()
  end
end

end
