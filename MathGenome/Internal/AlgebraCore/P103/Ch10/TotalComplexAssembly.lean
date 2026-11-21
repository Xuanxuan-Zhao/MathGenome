import MathGenome.Internal.AlgebraCore.P103.Ch10.ChainAssembly
import MathGenome.Internal.AlgebraCore.P103.Ch10.CochainAssembly
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.TotalComplexAssembly

/-!
First-quadrant assembly, paper.tex 2377–2414.

The imported construction provides the canonical algebraic direct-sum total,
its summand differential formulas and square zero, finite quadrant diagonals,
and the index interchange with sign (-1)^(pq). The chain and cochain assembly
proofs use these same objects. Here the two acyclic directions are combined
for both commuting and genuinely anticommuting input. No contraction, rank,
or finiteness assumption on the individual modules is imposed.
-/
namespace P103.Ch10.TotalComplexAssembly
universe u v
variable {R : Type u} [Ring R]

/-- First-quadrant chain assembly, allowing any fixed translate. -/
theorem chain_acyclic_of_columns_or_rows (K : ChainBicomplex.{u,v} R) (a b : ℤ)
    (hs : SupportedQuadrant K a b) (h : ColumnsAcyclic K ∨ RowsAcyclic K) :
    Complexes.Acyclic (total K) := by
  rcases h with hc | hr
  · exact chain_columns_acyclic K a b hs hc
  · exact chain_rows_acyclic K a b hs hr

/-- First-quadrant cochain assembly, allowing any fixed translate. -/
theorem cochain_acyclic_of_columns_or_rows (K : CochainBicomplex.{u,v} R) (a b : ℤ)
    (hs : SupportedQuadrant K a b) (h : ColumnsAcyclic K ∨ RowsAcyclic K) :
    Complexes.Acyclic (total K) := by
  rcases h with hc | hr
  · exact cochain_columns_acyclic K a b hs hc
  · exact cochain_rows_acyclic K a b hs hr

/-- Anticommuting chain input uses dh+dv and the original rows and columns. -/
theorem anticommuting_chain_acyclic_of_columns_or_rows
    (A : AnticommutingBicomplex.{u,v} R (ComplexShape.down ℤ)) (a b : ℤ)
    (hs : ∀ p q, p < a ∨ q < b → Subsingleton ((A.column p).X q))
    (h : (∀ p, Complexes.Acyclic (A.column p)) ∨
      (∀ q, Complexes.Acyclic (A.row q))) : Complexes.Acyclic A.total := by
  rcases h with hc | hr
  · exact anticommuting_chain_columns_acyclic A a b hs hc
  · exact anticommuting_chain_rows_acyclic A a b hs hr

/-- Anticommuting cochain input uses dh+dv and the original rows and columns. -/
theorem anticommuting_cochain_acyclic_of_columns_or_rows
    (A : AnticommutingBicomplex.{u,v} R (ComplexShape.up ℤ)) (a b : ℤ)
    (hs : ∀ p q, p < a ∨ q < b → Subsingleton ((A.column p).X q))
    (h : (∀ p, Complexes.Acyclic (A.column p)) ∨
      (∀ q, Complexes.Acyclic (A.row q))) : Complexes.Acyclic A.total := by
  rcases h with hc | hr
  · exact anticommuting_cochain_columns_acyclic A a b hs hc
  · exact anticommuting_cochain_rows_acyclic A a b hs hr

end P103.Ch10.TotalComplexAssembly
