import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.VectorRepresentation
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.MinorRank
import Mathlib.LinearAlgebra.Quotient.Defs

/-! The deletion and quotient parts of paper.tex W71. The columns keep their original
indices. All finiteness assumptions concern the matroid ground, not the ambient space.
The scalar extension assertion of W71 is allocated separately. -/
namespace FiniteCombinatorics.Matroid.Expected
open Set Submodule
open scoped _root_.Matroid
universe u v w

/-- Omitting the contracted/deleted indices is expressed by the minor's ground. -/
def deletionRepresents : Prop := ∀ {α : Type u} (K : Type v) [Field K]
    {V : Type w} [AddCommGroup V] [Module K V]
    (M : _root_.Matroid α) [M.Finite] (v : α → V), Represents K M v →
    ∀ C, C ⊆ M.E → Represents K (M ＼ C) v

/-- The span of quotient columns is the image of U + W in V/U. -/
def contractionQuotientSpan : Prop := ∀ {α : Type u} (K : Type v) [Field K]
    {V : Type w} [AddCommGroup V] [Module K V]
    (M : _root_.Matroid α) [M.Finite] (v : α → V), Represents K M v →
    ∀ C, C ⊆ M.E → ∀ A, A ⊆ M.E \ C →
    let U := span K (v '' C)
    let W := span K (v '' A)
    span K ((fun e => U.mkQ (v e)) '' A) = (U ⊔ W).map U.mkQ

/-- A linear identification of (U+W)/U with the span in V/U, preserving cosets. -/
def contractionQuotientEquiv : Prop := ∀ {α : Type u} (K : Type v) [Field K]
    {V : Type w} [AddCommGroup V] [Module K V]
    (M : _root_.Matroid α) [M.Finite] (v : α → V), Represents K M v →
    ∀ C, C ⊆ M.E → ∀ A, A ⊆ M.E \ C →
    let U := span K (v '' C)
    let S := U ⊔ span K (v '' A)
    ∃ e : (S ⧸ U.comap S.subtype) ≃ₗ[K]
        span K ((fun e => U.mkQ (v e)) '' A),
      ∀ x : S, (e (Submodule.Quotient.mk x) : V ⧸ U) = U.mkQ (x : V)

/-- The dimension difference is in ℤ and allows dependent contracted columns. -/
def contractionQuotientDimension : Prop := ∀ {α : Type u} (K : Type v) [Field K]
    {V : Type w} [AddCommGroup V] [Module K V]
    (M : _root_.Matroid α) [M.Finite] (v : α → V), Represents K M v →
    ∀ C, C ⊆ M.E → ∀ A, A ⊆ M.E \ C →
    let U := span K (v '' C)
    (Module.finrank K (span K ((fun e => U.mkQ (v e)) '' A)) : ℤ) =
      rank M (A ∪ C) - rank M C

def contractionRepresents : Prop := ∀ {α : Type u} (K : Type v) [Field K]
    {V : Type w} [AddCommGroup V] [Module K V]
    (M : _root_.Matroid α) [M.Finite] (v : α → V), Represents K M v →
    ∀ C, C ⊆ M.E →
    Represents K (M ／ C) (fun e => (span K (v '' C)).mkQ (v e))

end FiniteCombinatorics.Matroid.Expected
