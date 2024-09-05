using DataMigrations, Catlab
using StatsBase # for sampling data
import Catlab: to_graphviz_property_graph
import Catlab.Graphics.GraphvizGraphs: default_graph_attrs, default_node_attrs, default_edge_attrs
import Catlab.Graphics.Graphviz

@present SchLogistics(FreeSchema) begin
    (Depot,Site,LaneD2D,LaneD2S)::Ob
    src_d2d::Hom(LaneD2D,Depot)
    tgt_d2d::Hom(LaneD2D,Depot)
    src_d2s::Hom(LaneD2S,Depot)
    tgt_d2s::Hom(LaneD2S,Site)
    NameType::AttrType
    DepotType::AttrType
    TimeType::AttrType
    depot_name::Attr(Depot,NameType)
    depot_type::Attr(Depot,DepotType)
    site_name::Attr(Site,NameType)
    time_d2d::Attr(LaneD2D,TimeType)
    time_d2s::Attr(LaneD2S,TimeType)
end

# to_graphviz(SchLogistics)

@abstract_acset_type AbstractLogistics

@acset_type Logistics(SchLogistics, index=[:src_d2d,:tgt_d2d,:src_d2s,:tgt_d2s]) <: AbstractLogistics

# generate some data

# depot types
# 1. only ship to sites
# 2. ships to other depots

# site types
# 1. only accessible from secondaries
# 2. accessible from secondaries and primaries
# 3. only accessible from primaries

depot_pri_names = ["DepotPrimary" * string(i) for i in 1:3]
depot_sec_names = ["DepotSecondary" * string(i) for i in 1:10]

logistics = Logistics{String,Symbol,Int}()

# add Depots and LanesD2D
add_parts!(
    logistics, 
    :Depot, 
    length(depot_pri_names) + length(depot_sec_names), 
    depot_type=[fill(:Primary,length(depot_pri_names)); fill(:Secondary,length(depot_sec_names))],
    depot_name=[depot_pri_names; depot_sec_names]
)

for depot in incident(logistics, :Secondary, :depot_type)
    pri_depots = incident(logistics, :Primary, :depot_type)
    src_d2d = sample(pri_depots, sample(1:length(pri_depots)-1))
    add_parts!(
        logistics,
        :LaneD2D,
        length(src_d2d),
        src_d2d=src_d2d,
        tgt_d2d=depot,
        time_d2d=sample(1:10, length(src_d2d))
    )
end

# add Sites
# only accessible from secondaries
for i in 1:8
    src_d2s = sample(incident(logistics, :Secondary, :depot_type), sample(1:3), replace=false)
    s = add_part!(
        logistics,
        :Site,
        site_name = "Site" * string(i)
    )
    add_parts!(
        logistics,
        :LaneD2S,
        length(src_d2s),
        src_d2s=src_d2s,
        tgt_d2s=s,
        time_d2s=sample(1:10, length(src_d2s))
    )
end

# accessible from both
for i in 9:12
    src_d2s = [sample(incident(logistics, :Secondary, :depot_type)); sample(incident(logistics, :Primary, :depot_type))]
    s = add_part!(
        logistics,
        :Site,
        site_name = "Site" * string(i)
    )
    add_parts!(
        logistics,
        :LaneD2S,
        length(src_d2s),
        src_d2s=src_d2s,
        tgt_d2s=s,
        time_d2s=sample(1:10, length(src_d2s))
    )
end

# only accessible from primaries
for i in 13:15
    src_d2s = sample(incident(logistics, :Primary, :depot_type), sample(1:3), replace=false)
    s = add_part!(
        logistics,
        :Site,
        site_name = "Site" * string(i)
    )
    add_parts!(
        logistics,
        :LaneD2S,
        length(src_d2s),
        src_d2s=src_d2s,
        tgt_d2s=s,
        time_d2s=sample(1:10, length(src_d2s))
    )
end


# --------------------------------------------------------------------------------
# graphviz visualization

depot_label(v, acs) = begin
    text_lab = acs[v, :depot_type] == :Primary ? "🏭 $(acs[v, :depot_name])" : "📦 $(acs[v, :depot_name])"
    return Graphviz.Html("""
        <TABLE BORDER="0" CELLPADDING="1" CELLSPACING="0" CELLBORDER="1">
        <TR><TD>$(text_lab)</TD></TR>
        </TABLE>""")
end

site_label(v, acs) = begin
    return Graphviz.Html("""
        <TABLE BORDER="0" CELLPADDING="1" CELLSPACING="0" CELLBORDER="1">
        <TR><TD>🏥 $(acs[v, :site_name])</TD></TR>
        </TABLE>""")
end

"""
Constructor for `PropertyGraph` from an `AbstractLogistics` object
for Graphviz visualization.
"""
function to_graphviz_property_graph(
    g::AbstractLogistics;
    prog::AbstractString="dot", 
    graph_attrs::AbstractDict=Dict(),
    node_attrs::AbstractDict=Dict(), 
    edge_attrs::AbstractDict=Dict()
)
    pg = PropertyGraph{Any}(;
        prog = prog,
        graph = merge!(default_graph_attrs(prog), graph_attrs),
        node = merge!(Dict(), node_attrs),
        edge = merge!(default_edge_attrs(prog), edge_attrs),
    )
    v_depot = add_vertices!(pg, nparts(g, :Depot))
    v_site = add_vertices!(pg, nparts(g, :Site))
    for v in v_depot
        set_vprops!(
            pg, v, Dict(:label => depot_label(v, g), :shape => "plain")
        )
    end
    for (v_acs, v) in enumerate(v_site)
        set_vprops!(
            pg, v, Dict(:label => site_label(v_acs, g), :shape => "plain")
        )
    end
    
    add_edges!(pg, g[:, :src_d2d], g[:, :tgt_d2d])
    add_edges!(pg, g[:, :src_d2s], v_site[g[:, :tgt_d2s]])
    return pg
end

to_graphviz(to_graphviz_property_graph(logistics; prog = "dot", graph_attrs = Dict(:rankdir=>"LR")))

# --------------------------------------------------------------------------------
# a simple migration
# this is the simplest conjunctive migration that did something interesting
# it computes an equalizer to filter the sites

sites_subset = sample(parts(logistics, :Site), 5, replace=false)
sites_subset_nm = logistics[sites_subset, :site_name]

@present SchSites(FreeSchema) begin
    Site::Ob
    NameType::AttrType
    site_name::Attr(Site,NameType)
end

@acset_type Sites(SchSites)

M = @migration SchSites SchLogistics begin
    Site => @join begin
        s::Site
        n::NameType
        (f:s → n)::(x -> site_name(x) ∈ sites_subset_nm ? "yes" : "no")
        (g:s → n)::(x -> "yes")
    end
    NameType => NameType
    site_name => site_name(s)
end

d = migrate(Sites, logistics, M)

@assert sort(d[:, :site_name]) == sort(sites_subset_nm)


# --------------------------------------------------------------------------------
# if we just look at the depots, it's the same as the schema for Graph

@present SchDepots(FreeSchema) begin
    (Depot,LaneD2D)::Ob
    src_d2d::Hom(LaneD2D,Depot)
    tgt_d2d::Hom(LaneD2D,Depot)
    NameType::AttrType
    DepotType::AttrType
    TimeType::AttrType
    depot_name::Attr(Depot,NameType)
    depot_type::Attr(Depot,DepotType)
    time_d2d::Attr(LaneD2D,TimeType)
end

@acset_type Depots(SchDepots)

depots_subset = sample(incident(logistics, :Primary, :depot_type), 2, replace=false)
depots_subset_nm = logistics[depots_subset, :depot_name]

# what if we have edges possibly going in both directions?
# M = @migration SchDepots SchLogistics begin
#     Depot => @join begin
#         d::Depot
#         n::NameType
#         (f:d → n)::(x -> depot_name(x) ∈ depots_subset_nm ? "yes" : "no")
#         (g:d → n)::(x -> "yes")
#     end
#     LaneD2D => @join begin
#         (d₁,d₂)::Depot
#         (n₁,n₂)::NameType
#         (f₁:d₁ → n₁)::(x -> depot_name(x) ∈ depots_subset_nm ? "yes" : "no")
#         (g₁:d₁ → n₁)::(x -> "yes")
#         (f₂:d₂ → n₂)::(x -> depot_name(x) ∈ depots_subset_nm ? "yes" : "no")
#         (g₂:d₂ → n₂)::(x -> "yes")
#         e::LaneD2D
#         src_d2d(e) == d₁
#         tgt_d2d(e) == d₂
#     end
#     src_d2d => (d => d₁; n => n₁; f => f₁; g => g₁)
#     tgt_d2d => (d => d₂; n => n₂; f => f₂; g => g₂)
#     NameType => NameType
#     DepotType => DepotType
#     TimeType => TimeType
#     depot_name => depot_name(d)
#     depot_type => depot_type(d)
#     time_d2d => time_d2d(e)
# end

M = @migration SchDepots SchLogistics begin
    Depot => @join begin
        d::Depot
        n::NameType
        (f:d → n)::(x -> depot_name(x) ∈ depots_subset_nm ? "yes" : "no")
        (g:d → n)::(x -> "yes")
    end
    LaneD2D => @join begin
        (d₁,d₂)::Depot
        n₁::NameType
        (f₁:d₁ → n₁)::(x -> depot_name(x) ∈ depots_subset_nm ? "yes" : "no")
        (g₁:d₁ → n₁)::(x -> "yes")
        e::LaneD2D
        src_d2d(e) == d₁
        tgt_d2d(e) == d₂
    end
    src_d2d => begin
        d => d₁; n => n₁; f => f₁; g => g₁
    end
    tgt_d2d => begin end
    NameType => NameType
    DepotType => DepotType
    TimeType => TimeType
    depot_name => depot_name(d)
    depot_type => depot_type(d)
    time_d2d => time_d2d(e)
end

d = migrate(Depots, logistics, M)


# --------------------------------------------------------------------------------
# explain what these are

M = @migration SchSites SchLogistics begin
    Site => @unit
    NameType => @unit
end

d = migrate(Sites, logistics, M)

M = @migration SchSites SchLogistics begin
    Site => @empty
    NameType => @unit
end

d = migrate(Sites, logistics, M)

M = @migration SchSites SchLogistics begin
    Site => @product begin end
    NameType => @unit
    site_name => begin end
end

d = migrate(Sites, logistics, M)