using DataMigrations, Catlab
using StatsBase # for sampling data
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
        tgt_d2d=depot
    )
end

# add Sites
# only accessible from secondaries
for i in 1:8
    src_d2s = sample(incident(logistics, :Secondary, :depot_type), sample(1:3))
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
        tgt_d2s=s
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
        tgt_d2s=s
    )
end

# only accessible from primaries
for i in 13:15
    src_d2s = sample(incident(logistics, :Primary, :depot_type), sample(1:3))
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
        tgt_d2s=s
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
function PropertyGraph{T}(
    g::AbstractLogistics; gprops...
) where T
    pg = PropertyGraph{T}(; gprops...)
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

to_graphviz(PropertyGraph{Any}(logistics; prog = "dot", rankdir = "LR"))