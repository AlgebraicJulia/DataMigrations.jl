# Graphs
########

g = @graph begin
  s
  t
  s → t
  s → t
end
@test subpart(g,:vname) == [:s,:t]

g = @graph NamedGraph{Symbol,Symbol} begin
  x, y
  (f, g): x → y
end
@test g == parallel_arrows(NamedGraph{Symbol,Symbol}, 2,
                           V=(vname=[:x,:y],), E=(ename=[:f,:g],))

tri_parsed = @graph NamedGraph{Symbol,Symbol} begin
  v0, v1, v2
  fst: v0 → v1
  snd: v1 → v2
  comp: v0 → v2
end
tri = @acset NamedGraph{Symbol,Symbol} begin
  V = 3
  E = 3
  src = [1,2,1]
  tgt = [2,3,3]
  vname = [:v0, :v1, :v2]
  ename = [:fst, :snd, :comp]
end
@test tri_parsed == tri

# Categories
############

Δ¹_parsed = @fincat begin
  V, E
  (δ₀, δ₁): V → E
  σ₀: E → V

  σ₀ ∘ δ₀ == id(V)
  σ₀ ∘ δ₁ == id(V)
end
Δ¹_graph = @acset NamedGraph{Symbol,Symbol} begin
  V = 2
  E = 3
  src = [1,1,2]
  tgt = [2,2,1]
  vname = [:V, :E]
  ename = [:δ₀, :δ₁, :σ₀]
end
Δ¹ = FinCat(Δ¹_graph, [ [1,3] => empty(Path, Δ¹_graph, 1),
                        [2,3] => empty(Path, Δ¹_graph, 1) ])
@test Δ¹_parsed == Δ¹

# Functors
##########

# Underlying graph of circular port graph.
F = @finfunctor SchGraph SchCPortGraph begin
  V => Box
  E => Wire
  src => src ⨟ box
  tgt => tgt ⨟ box
end
@test F == FinFunctor(Dict(:V => :Box, :E => :Wire),
                      Dict(:src => [:src, :box], :tgt => [:tgt, :box]),
                      SchGraph, SchCPortGraph)

# Incomplete definitions.
@test_throws ErrorException begin
  @finfunctor SchGraph SchCPortGraph begin
    V => Box
  end
end
@test_throws ErrorException begin
  @finfunctor SchGraph SchCPortGraph begin
    V => Box
    src => src ⨟ box
    tgt => tgt ⨟ box
  end
end

# Failure of functorality.
@test_throws ErrorException begin
  @finfunctor SchGraph SchCPortGraph begin
    V => Box
    E => Wire
    src => src
    tgt => tgt
  end
end

# Extra definitions.
@test_throws ErrorException begin
  @finfunctor SchGraph SchReflexiveGraph begin
    V => Box
    E => Wire
    src => src
    tgt => tgt
    refl => refl
  end
end

# GAT expressions.
F = @finfunctor SchDDS SchDDS begin
  X => X; Φ => id(X)
end
F′ = @finfunctor SchDDS SchDDS begin
  X => X; Φ => id{X}
end
@test F == F′

# Diagrams
##########

C = FinCat(SchGraph)
d = @diagram C begin
  v::V
  (e1, e2)::E
  (t: e1 → v)::tgt
  (s: e2 → v)::src
end
J = FinCat(@present P(FreeCategory) begin
  (v,e1,e2)::Ob
  t::Hom(e1,v)
  s::Hom(e2,v)
end)
F_parsed = diagram(d)
@test ob_generators(dom(F_parsed)) == ob_generators(J)
F = FinFunctor(Dict(:v=>:V,:e1=>:E,:e2=>:E), 
              Dict(:t=>:tgt,:s=>:src), J, C)
@test F_parsed.ob_map == F.ob_map

d = @diagram SchGraph begin
  v => V
  (e1, e2) => E
  t: e1 → v => tgt
  s: e2 → v => src
end
@test all([ob_map(diagram(d),x) == ob_map(F,x) for x in ob_generators(dom(F))])

d = @diagram SchGraph begin
  v::V
  (e1, e2)::E
  (e1 → v)::tgt
  (e2 → v)::src
end
F_parsed = diagram(d)
J_parsed = dom(F_parsed)
@test src(graph(J_parsed)) == src(graph(J))
@test tgt(graph(J_parsed)) == tgt(graph(J))

d′ = @free_diagram SchGraph begin
  v::V
  (e1, e2)::E
  tgt(e1) == v
  v == src(e2)
end
@test d′ == d

d = @free_diagram SchGraph begin
  (e1, e2)::E
  tgt(e1) == src(e2)
end
@test is_functorial(diagram(d))
@test collect_ob(d) == SchGraph[[:E, :E, :V]]
@test collect_hom(d) == SchGraph[[:tgt, :src]]

d = @diagram SchDDS begin
  x::X
  (f: x → x)::(Φ⋅Φ)
end
@test only(collect_ob(d)) == SchDDS[:X]
@test only(collect_hom(d)) == compose(SchDDS[:Φ], SchDDS[:Φ])

# Diagrams with parameters
#-------------------------

 d = @free_diagram SchWeightedGraph begin
  v::V
  (e1, e2)::E
  tgt(e1) == v
  src(e2) == v
  w::Weight
  w == 5.0
  weight(e1) == w 
  weight(e2) == w
end
@test sort(nameof.(collect_ob(d))) == [:E,:E,:V,:Weight]
@test sort(nameof.(collect_hom(d))) == [:src, :tgt, :weight, :weight]
@test d.params == Dict(:w => 5.0)

d = @free_diagram SchWeightedGraph begin
  (e1, e2)::E
  tgt(e1) == src(e2)
  weight(e1) == 0.5
  weight(e2) == 1.5
end
@test sort(nameof.(collect_ob(d))) == [:E, :E, :V, :Weight, :Weight]
@test sort(nameof.(collect_hom(d))) == [:src, :tgt,:weight, :weight]
@test sort(collect(values(d.params))) == [0.5,1.5]

struct Box{Value}
  value::Value
end

d = @free_diagram SchWeightedGraph begin
  e::E
  w::Weight
  weight(e) == w
  w == $(Box(0.5))
end
@test d.params == Dict(:w => Box(0.5))

d = @free_diagram SchWeightedGraph begin
  e::E
  weight(e) == $(Box(0.5))
end
@test only(values(d.params)) == Box(0.5)
