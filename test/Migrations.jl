module TestMigrations
using Test

using Catlab
using DataMigrations

@present SchSet(FreeSchema) begin
  X::Ob
end
@acset_type AcsetSet(SchSet)

@present SchDDS <: SchSet begin
  Φ::Hom(X,X)
end
@acset_type DDS(SchDDS, index=[:Φ])

# Conjunctive migration
#----------------------

# Graph whose edges are paths of length 2.
V, E, s, t = generators(SchGraph)
C = FinCat(SchGraph)
F_V = FinDomFunctor([V], FinCat(1), C)
F_E = FinDomFunctor(FreeDiagram(Cospan(t, s)), C)
M = DataMigration(FinDomFunctor(Dict(V => Diagram{op}(F_V),
                       E => Diagram{op}(F_E)),
                  Dict(s => DiagramHom{op}([(1, s)], F_E, F_V),
                       t => DiagramHom{op}([(2, t)], F_E, F_V)), C))
@test M isa DataMigrations.Migrations.ConjSchemaMigration
g = path_graph(Graph, 5)
H = migrate(g, M, tabular=true)
@test length(H(V)) == 5
@test length(H(E)) == 3
@test H(s)((x1=2, x2=3, x3=3)) == (x1=2,)
@test H(t)((x1=2, x2=3, x3=3)) == (x1=4,)

# Same migration, but defining using the `@migration` macro.
M = @migration SchGraph SchGraph begin
  V => V
  E => @join begin
    v::V
    (e₁, e₂)::E
    tgt(e₁) == v
    src(e₂) == v
  end
  src => e₁ ⋅ src
  tgt => e₂ ⋅ tgt
end
F = functor(M)
H = migrate(g, M, tabular=true)
@test length(H(V)) == 5
@test length(H(E)) == 3
@test map(H(s),dom(H(s))) == [(V=1,),(V=2,),(V=3,)]
@test map(H(t),dom(H(t))) == [(V=3,),(V=4,),(V=5,)]

h = migrate(Graph, g, M)
@test (nv(h), ne(h)) == (5, 3)
@test sort!(collect(zip(h[:src], h[:tgt]))) == [(1,3), (2,4), (3,5)]

h = Graph(5)
migrate!(h, g, M)
@test (nv(h), ne(h)) == (10, 3)
@test sort!(collect(zip(h[:src], h[:tgt]))) == [(6,8), (7,9), (8,10)]

# Weighted graph whose edges are path of length 2 with equal weight.
M = @migration SchWeightedGraph SchWeightedGraph begin
  V => V
  E => @join begin
    v::V; (e₁, e₂)::E; w::Weight
    tgt(e₁) == v
    src(e₂) == v
    weight(e₁) == w
    weight(e₂) == w
  end
  Weight => Weight
  src => e₁ ⋅ src
  tgt => e₂ ⋅ tgt
  weight => w
end
g = path_graph(WeightedGraph{Float64}, 6, E=(weight=[0.5,0.5,1.5,1.5,1.5],))
h = migrate(WeightedGraph{Float64}, g, M)
@test (nv(h), ne(h)) == (6, 3)
@test sort!(collect(zip(h[:src], h[:tgt], h[:weight]))) ==
  [(1,3,0.5), (3,5,1.5), (4,6,1.5)]

# Graph whose vertices are paths of length 2 and edges are paths of length 3.
g = path_graph(Graph, 6)
h = @migrate Graph g begin
  V => @join begin
    v::V
    (e₁, e₂)::E
    (t: e₁ → v)::tgt
    (s: e₂ → v)::src
  end
  E => @join begin
    (v₁, v₂)::V
    (e₁, e₂, e₃)::E
    (t₁: e₁ → v₁)::tgt
    (s₁: e₂ → v₁)::src
    (t₂: e₂ → v₂)::tgt
    (s₂: e₃ → v₂)::src
  end
  src => (v => v₁; e₁ => e₁; e₂ => e₂; t => t₁; s => s₁)
  tgt => (v => v₂; e₁ => e₂; e₂ => e₃; t => t₂; s => s₂)
end
@test h == path_graph(Graph, 4)

# Bouquet graph on a set.
set = @acset AcsetSet begin X = 5 end
g = @migrate Graph set begin
  V => @unit
  E => X
end
g′ = @acset Graph begin
  V = 1
  E = 5
  src = [1,1,1,1,1]
  tgt = [1,1,1,1,1]
end
@test g == g′

# Gluing migration
#-----------------

# Free reflexive graph on a graph.
g = cycle_graph(Graph, 5)
h = @migrate ReflexiveGraph g begin
  V => V
  E => @cases (v::V; e::E)
  src => (e => src)
  tgt => (e => tgt)
  refl => v
end
@test h == cycle_graph(ReflexiveGraph, 5)

# Free symmetric graph on a graph.
g = star_graph(Graph, 5)
h = @migrate SymmetricGraph g begin
  V => V
  E => @cases (fwd::E; rev::E)
  src => (fwd => src; rev => tgt)
  tgt => (fwd => tgt; rev => src)
  inv => (fwd => rev; rev => fwd)
end
@test h == star_graph(SymmetricGraph, 5)

# Free symmetric weighted graph on a weighted graph.
weights = range(0, 1, length=5)
g = star_graph(WeightedGraph{Float64}, 6, E=(weight=weights,))
h = @migrate SymmetricWeightedGraph g begin
  V => V
  E => @cases (fwd::E; rev::E)
  Weight => Weight
  src => (fwd => src; rev => tgt)
  tgt => (fwd => tgt; rev => src)
  inv => (fwd => rev; rev => fwd)
  weight => (fwd => weight; rev => weight)
end
h′ = star_graph(SymmetricWeightedGraph{Float64}, 6)
h′[:weight] = vcat(weights, weights)
@test h == h′

# Free symmetric reflexive graph on a reflexive graph.
g = star_graph(ReflexiveGraph, 5)
h = @migrate SymmetricReflexiveGraph g begin
  V => V
  E => @glue begin
    (fwd, rev)::E
    v::V
    (refl_fwd: v → fwd)::refl
    (refl_rev: v → rev)::refl
  end
  src => (fwd => src; rev => tgt)
  tgt => (fwd => tgt; rev => src)
  refl => v
  inv => begin
    fwd => rev; rev => fwd; v => v;
    refl_fwd => refl_rev; refl_rev => refl_fwd
  end
end
@test is_isomorphic(h, star_graph(SymmetricReflexiveGraph, 5))

# Discrete graph on set.
set = @acset AcsetSet begin X = 5 end
g = @migrate Graph set begin
  V => X
  E => @empty
end
@test g == Graph(5)

# Gluc migration
#---------------

# Graph with edges that are paths of length <= 2.
g = path_graph(Graph, 4)
h = @migrate Graph g begin
  V => V
  E => @cases begin
    v => V
    e => E
    path => @join begin
      v::V
      (e₁, e₂)::E
      tgt(e₁) == v
      src(e₂) == v
    end
  end
  src => (e => src; path => e₁⋅src)
  tgt => (e => tgt; path => e₂⋅tgt)
end
h′ = @acset Graph begin
  V = 4
  E = 9
  src = [1,2,3,4, 1,2,3, 1,2]
  tgt = [1,2,3,4, 2,3,4, 3,4]
end
@test h == h′

# Discrete graph on one vertex.
g = @migrate Graph set begin
  V => @unit
  E => @empty
end
@test g == Graph(1)

# Migrations with Code
######################

@present SchMechLink <: SchGraph begin
  Pos::AttrType
  Len::AttrType
  pos::Attr(V,Pos)
  len::Attr(E,Len)
end
@acset_type MechLink(SchMechLink, index=[:src,:tgt])

G = @acset MechLink{Vector{Float64},Float64} begin
  V = 3
  E = 2
  src = [1,2]
  tgt = [2,3]
  len = [1.0,1.0]
  pos = [[1.0,1.0,1.0],[2.0,2.0,2.0],[2.0,2.0,1.0]]
end

#Rotate the whole linkage by a bit
M = @migration SchMechLink SchMechLink begin
  V => V
  E => E
  Pos => Pos
  Len => Len
  src => src
  tgt => tgt
  pos => begin 
          θ = π/5
          M = [[cos(θ),sin(θ),0] [-sin(θ),cos(θ),0] [0,0,1]]
          x -> M*pos(x)
          end
  len => len
end
A = migrate(MechLink,G,M)
v₃ = subpart(A,1,:pos)
v₂ = v₃[1:2]
angle(v,w)=acos( sum(v.*w)/(sqrt(sum(v.^2)*sum(w.^2))) )
@test angle(v₂,[1,1]) == π/5 && v₃[3] == 1
#Filter impossible edges out of a mechanical linkage
M = @migration SchMechLink SchMechLink begin
  V => V
  E => @join begin
          e :: E
          L :: Len
          (l:e→L) :: (x->len(x)^2)
          (d:e→L) :: (x->sum((pos(src(x))-pos(tgt(x))).^2))
      end
  Pos => Pos
  Len => Len
  src => src(e)
  tgt => tgt(e)
  pos => pos
  len => len(e)
end
B = migrate(MechLink,G,M)
@test length(parts(B,:E)) == 1
#variant
M′ = @migration SchMechLink begin
  V => V
  E => @join begin
          e :: E
          L :: Len
          (l:e→L) :: (x->len(x)^2)
          (d:e→L) :: (x->sum((pos(src(x))-pos(tgt(x))).^2))
      end
  Pos => Pos
  Len => Len
  (src:E→V) => src(e)
  (tgt:E→V) => tgt(e)
  (pos:V→Pos) => pos
  (len:E→Len) => len(e)
end
Bb = migrate(G,M)
@test length(ob_map(Bb,:E)) == 1
#Filter impossible edges out of a mechanical linkage while rotating
M = @migration SchMechLink SchMechLink begin
  V => V
  E => @join begin
          e :: E
          L :: Len
          (l:e→L) :: (x->len(x)^2)
          (d:e→L) :: (x->sum((pos(src(x))-pos(tgt(x))).^2))
      end
  Pos => Pos
  Len => Len
  src => src(e)
  tgt => tgt(e)
  pos => begin 
          θ = π/5
          M = [[cos(θ),sin(θ),0] [-sin(θ),cos(θ),0] [0,0,1]]
          x -> M*pos(x)
          end
  len => len(e)
end
C = migrate(G,M)
@test length(ob_map(C,:E)) == 1
@test angle(hom_map(C,:pos)(1)[1:2],[1,1])==pi/5
#Filter out impossible edges, but then weirdly double all the lengths
M = @migration SchMechLink begin
  V => V
  E => @join begin
      e :: E
      L :: Len
      (l:e→L) :: (x->len(x)^2)
      (d:e→L) :: (x->sum((pos(src(x))-pos(tgt(x))).^2))
  end
  Pos => Pos
  Len => Len
  (src:E→V) => src(e)
  (tgt:E→V) => tgt(e)
  (pos:V→Pos) => pos
  (len:E→Len) => (len(e)|>(x->2x))
end
D = migrate(G,M)
@test hom_map(D,:len)(1) == 2.0
#Variant
M′ = @migration SchMechLink SchMechLink begin
  V => V
  E => @join begin
      e :: E
      L :: Len
      (l:e→L) :: (x->len(x)^2)
      (d:e→L) :: (x->sum((pos(src(x))-pos(tgt(x))).^2))
  end
  Pos => Pos
  Len => Len
  src => src(e)
  tgt => tgt(e)
  pos => pos
  len => (len(e)|>(x->2x))
end
Dd = migrate(MechLink,G,M′)
@test only(subpart(Dd,:len)) == 2.0
#disjoint union linkage with itself, second copy reflected through origin
M = @migration SchMechLink SchMechLink begin
  V => @cases (v₁::V;v₂::V)
  E=> @cases (e₁::E;e₂::E)
  Pos => Pos
  Len => Len
  src => begin
    e₁ => v₁ ∘ src
    e₂ => v₂ ∘ src
  end
  tgt => begin
    e₁ => v₁ ∘ tgt
    e₂ => v₂ ∘ tgt
  end
  pos => begin
    v₁ => pos
    v₂ => (pos|> (x-> -x)) 
  end
  len => (e₁ => len ; e₂ => len)
end
E = migrate(MechLink,G,M)
@test sort(map(x->x[1],subpart(E,:pos))) == [-2.0,-2.0,-1.0,1.0,2.0,2.0]

#Filter impossible edges and also make a copy reflected through the
#origin.
M = @migration SchMechLink SchMechLink begin
  V => @cases (v₁::V;v₂::V)
  E=> @cases begin 
    e₁ => @join begin
      e :: E
      L :: Len
      (l:e→L) :: (x->len(x)^2)
      (d:e→L) :: (x->sum((pos(src(x))-pos(tgt(x))).^2))
  end
    e₂ => @join begin
      e :: E
      L :: Len
      (l:e→L) :: (x->len(x)^2)
      (d:e→L) :: (x->sum((pos(src(x))-pos(tgt(x))).^2))
  end
end
  Pos => Pos
  Len => Len
  src => begin
    e₁ => v₁ ∘ (e⋅src)
    e₂ => v₂ ∘ (e⋅src)
  end
  tgt => begin
    e₁ => v₁ ∘ (e⋅tgt)
    e₂ => v₂ ∘ (e⋅tgt)
  end
  pos => begin
    v₁ => pos
    v₂ => (pos|> (x-> -x)) 
  end
  len => (e₁ => e⋅len ; e₂ => e⋅len)
end
Ee = migrate(MechLink,G,M)
@test sort(map(x->x[1],subpart(Ee,:pos))) == [-2.0,-2.0,-1.0,1.0,2.0,2.0]
@test length(parts(Ee,:E)) == 2

F = @migration SchGraph begin
  X => E
  (I, O) => V
  (i: X → I) => src
  (o: X → O) => tgt
end
y_Graph = yoneda(Graph)
yV, yE = Graph(1), @acset(Graph, begin V=2;E=1;src=2;tgt=1 end)
G = colimit_representables(F, y_Graph) # Delta migration.
X = ob_map(G, :X)
@test is_isomorphic(X, yE)
i, o = hom_map(G, :i), hom_map(G, :o)
@test sort(only.(collect.([i[:V],o[:V]]))) == [1,2]

F = @migration SchGraph begin
  X => @join begin
    (e₁, e₂)::E
    tgt(e₁) == src(e₂)
  end
  (I, O) => V
  (i: X → I) => src(e₁)
  (o: X → O) => tgt(e₂)
end
G = colimit_representables(F, y_Graph) # Conjunctive migration.
X = ob_map(G, :X)
@test is_isomorphic(X, path_graph(Graph, 3))
i, o = hom_map(G, :i), hom_map(G, :o)
@test isempty(inneighbors(X, only(collect(i[:V]))))
@test isempty(outneighbors(X, only(collect(o[:V]))))

# Yoneda embedding for weights graphs (has attributes).
WGF = WeightedGraph{Float64}
yV, yE = WGF(1), @acset(WGF, begin 
  V=2;E=1;Weight=1;src=2;tgt=1; weight=[AttrVar(1)]
end)
@test representable(WGF, :V) == yV
@test is_isomorphic(representable(WGF, :E), yE)

yWG = yoneda(WGF)

F = @migration SchWeightedGraph begin
  X => E
  (I, O) => V
  (i: X → I) => src
  (o: X → O) => tgt
end
G = colimit_representables(F, yWG) # Delta migration.
X = ob_map(G, :X)
@test is_isomorphic(X, yE)
i, o = hom_map(G, :i), hom_map(G, :o)
@test sort(only.(collect.([i[:V],o[:V]]))) == [1,2]

d = @migration(SchWeightedGraph, begin
    I => @join begin
      (e1,e2,e3)::E
      (w1,w3)::Weight
      src(e1) == src(e2)      
      weight(e1) == w1
      w1 == 1.9     
      weight(e2) == 1.8 
      weight(e3) == w3
    end
end)

expected = @acset WeightedGraph{Float64} begin
  V=5; E=3; Weight=1; src=[1,1,3]; tgt=[2,4,5]; weight=[1.8,1.9,AttrVar(1)]
end
@test is_isomorphic(ob_map(colimit_representables(d, yWG), :I), expected)

# Can do a complex migration into a schema with no edges.
@present SchNattrSet(FreeSchema) begin
  X::Ob
  A::AttrType
end
M = @migration SchWeightedGraph SchNattrSet begin
  V => X
  E => X 
  src => id(X)
  tgt => id(X)
  Weight => A
  weight => (x->7.0)
end
@acset_type NattrSet(SchNattrSet)
S = @acset NattrSet{Float64} begin
  X = 5
end
WG = migrate(WeightedGraph{Float64}, S, M)
@test nparts(WG,:V) == nparts(WG,:E) == 5
@test subpart(WG,:weight) == fill(7.0,5)

## Can migrate inserting default values for previously missing attributes.
@present SchAttrSet(FreeSchema) begin
  X::Ob
  Label::AttrType
  hasLabel::Attr(X, Label)

  MyBool::AttrType
  MyString::AttrType
end
@present SchAttrSet2(FreeSchema) begin
  X::Ob

  Y::Ob
  m::Hom(Y, X)

  A::AttrType
  f::Attr(Y, A)
  B::AttrType
  g::Attr(Y, B)
end

M = @migration SchAttrSet2 SchAttrSet begin
  X => X

  Y => @join begin
    x::X
    L::Label
    (hl:x→L) :: hasLabel
    (foo:x→L) :: (x->"foo")
  end
  m => x

  A => MyBool
  f => (x |> (a -> false))
  B => MyString
  g => (x |> (a -> "unknown"))
end
@acset_type AttrSet(SchAttrSet)
T = @acset AttrSet{String, Bool, String} begin
  X = 2
  hasLabel = ["foo", "bar"]
end
@acset_type AttrSet2(SchAttrSet2)
S = migrate(AttrSet2{Bool, String}, T, M)
@test length(parts(S,:Y)) == 1
@test subpart(S,:f) == [false]
@test subpart(S,:g) == ["unknown"]


# Can migrate acsets with some attrvar values.
@present SchWithLabel(FreeSchema) begin
  X::Ob
  Label::AttrType
  hasLabel::Attr(X, Label)
end
@acset_type WithLabel(SchWithLabel)
yWithLabel = yoneda(WithLabel{String})

@present SchSplit(FreeSchema) begin
  A::Ob
  B::Ob
end
@acset_type Split(SchSplit)

M = @migration SchSplit SchWithLabel begin
  A => @join begin
    x::X
    L::Label
    (f:x → L)::hasLabel
    (A:x → L)::(x -> "A")
  end
  B => @join begin
    x::X
    L::Label
    (f:x → L)::hasLabel
    (A:x → L)::(x -> "B")
  end
end
data = @acset_colim yWithLabel begin x::X end
result = migrate(Split, data, M)
@test result == @acset Split begin end

#Conjunctive migrations including attrvars
@present SchWithLabel(FreeSchema) begin
  X::Ob
  Label::AttrType
  hasLabel::Attr(X, Label)
end
@acset_type WithLabel(SchWithLabel)
yWithLabel = yoneda(WithLabel{String})

@present SchSplitWithDefault(FreeSchema) begin
  Thing::Ob
  A::Ob
  B::Ob

  aIsThing::Hom(A, Thing)
  bIsThing::Hom(B, Thing)
end
@acset_type SplitWithDefault(SchSplitWithDefault)

M1 = @migration SchSplitWithDefault SchWithLabel begin
  Thing => X
  A => @join begin
    x::X
    L::Label
    (f:x → L)::hasLabel
    (A:x → L)::(x -> "A")
  end
  aIsThing => x
  B => @join begin
    x::X
    L::Label
    (f:x → L)::hasLabel
    (A:x → L)::(x -> "B")
  end
  bIsThing => x
end

data1 = @acset_colim yWithLabel begin
  x::X
  hasLabel(x) == "A"
end


data2 = @acset_colim yWithLabel begin
  (x1, x2)::X
  hasLabel(x1) == "A"
  hasLabel(x2) == "C"
end

out1 = migrate(SplitWithDefault, data1, M1)
out2 = migrate(SplitWithDefault, data2, M1)

@test nparts(out1,:Thing) == nparts(out1,:A) == 1 && nparts(out1,:B) == 0
@test nparts(out2,:Thing) == 2 && nparts(out2,:A) == 1 && nparts(out2,:B) == 0

end#module
