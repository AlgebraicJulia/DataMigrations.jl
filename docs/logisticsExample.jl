using DataMigrations, Catlab

@present SchLogistics(FreeSchema) begin
    (Depot,Site,LaneD2D,LaneD2S)::Ob
    src_d2d::Hom(LaneD2D,Depot)
    tgt_d2d::Hom(LaneD2D,Depot)
    src_d2s::Hom(LaneD2S,Depot)
    tgt_d2s::Hom(LaneD2S,Site)
    NameType::AttrType
    depot_name::Attr(Depot,NameType)
    site_name::Attr(Site,NameType)
end

# to_graphviz(SchLogistics)

@abstract_acset_type AbstractLogistics

@acset_type Logistics(SchLogistics, index=[:src_d2d,:tgt_d2d,:src_d2s,:tgt_d2s]) <: AbstractLogistics

