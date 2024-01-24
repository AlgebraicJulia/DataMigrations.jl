# DataMigrations.jl

```@meta
CurrentModule = Migrations
```

`DataMigrations.jl` is a Julia library for contravariant data migrations in the sense of [Spivak](https://arxiv.org/abs/2111.10968).
Such a migration is determined by a functor from a schema $C$ to another schema $D$ or else to a category of diagrams in (or diagrams in diagrams in)
$D$. The first case is the simplest, and corresponds to $\Delta$-migrations in the sense of Spivak's earlier [work](https://arxiv.org/abs/1009.1166)
on functorial data migrations. These are similar in power to SQL `SELECT` statements without a `WHERE` clause, but with the key distinction
that the output will be another complete database and in particular will generally contain multiple tables linked by foreign keys. 

For instance, consider the following schema, for a simple database of classical music recordings.
```@example 1
using Catlab, DataMigrations
@present SchRecordingLibrary(FreeSchema) begin
  (Recording,Conductor,Composer,Work)::Ob
  composer::Hom(Work,Composer)
  work::Hom(Recording,Work)
  conductor::Hom(Recording,Conductor)

  NameType::AttrType
  YearType::AttrType

  name_cond::Attr(Conductor,NameType)
  name_comp::Attr(Composer,NameType)
  name_work::Attr(Work,NameType)
  year::Attr(Recording,YearType)
end
to_graphviz(SchRecordingLibrary)
```

We can extract just the library of works and composers as follows:
```@example 1
@present SchPieceLibrary(FreeSchema) begin
  (Writer,Piece)::Ob
  writer::Hom(Piece,Writer)
  NameType::AttrType

  name_wr::Attr(Writer,NameType)
  name_piece::Attr(Piece,NameType)
end
to_graphviz(SchPieceLibrary)

M = @migration SchPieceLibrary SchRecordingLibrary begin
  Writer => Composer
  Piece => Work
  NameType => NameType
  writer => composer
  name_wr => name_comp
  name_piece => name_work
end
```

The above migration is specified directly via the obvious functor
from `SchPieceLibrary` to `SchRecordingLibrary`. It is also possible
to specify migrations by sending a morphism $f$ in the domain to a morphism
in the category of *sets* specifying where the migrated $f$ should 
land in terms of the acset being migrated and not merely its schema.
For a simple example, we could capitalize all the names or replace them
with a placeholder, either of which involves sending
the name attributes to a function into a stringlike type which we expect to
instantiate `NameType`.

```@example 1
N = @migration SchPieceLibrary SchPieceLibrary begin
  Writer => Writer
  Piece => Piece
  NameType => NameType
  writer => writer
  name_wr => (x->uppercase(name_wr(x)))
  name_piece => (x->"DELETED")
end
```

Let's see these migrations in action. We'll need some actual acsets of the relevant types.

```@example 1
using Dates
@acset_type RecordingLibrary(SchRecordingLibrary)
@acset_type PieceLibrary(SchPieceLibrary)

L = @acset RecordingLibrary{String,Dates.Year} begin
  Recording = 5
  Composer = 2
  Work = 4
  Conductor = 3
  composer = [1,1,2,2]
  work = [1,2,3,4,4]
  conductor = [1,3,2,3,2]

  name_comp = ["Messiaen","Mahler"]
  name_work = ["Quartet for the End of Time","Turangalîla-Symphonie","Symphony No. 5","Kindertotenlieder"]
  name_cond = ["Tilson Thomas","Boulez","Saariaho"]
  year = Dates.Year.([1981,1968,1994,2001,2024])
end
```

First, we extract the piece library from the recording library.

```@example 1
P = migrate(PieceLibrary,L,M)
```

Similarly, we can capitalize the names of the composers and replace the names of the pieces with "DELETED".


```@example 1
migrate(PieceLibrary,P,N)
```

Mathematically, the migration `N` is not a $\Delta$-migration any longer. In fact, it is equivalent to a certain $`Sigma`$-migration,
but we won't flesh this out just now.

## Conjunctive migrations

Migrations analogous to SQL `SELECT-FROM-WHERE` statements are called *conjunctive migrations*. These are specified by a functor from a schema $C$ to the category $\mathrm{Diag}_\leftarrow(D)$ of co-diagrams in
$D.$ (citation!) 