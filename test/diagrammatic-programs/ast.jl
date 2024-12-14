using Test

# TODO
using DataMigrations
import DataMigrations.DiagrammaticPrograms.AST as A


@test_broken A.ob_over_pairs(A.OnlyOb())

@test_broken A.hom_over_pairs
