import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ClosedMatrixGroups
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ReductiveDecomposition
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Algebra.Lie.Abelian

/-!
LA-J06-CompactCartans, Lie volume, res:J06, expanded lines 4885–4912.
The positive definite invariant form is represented by a real inner product.
An `InnerProductSpace.Core` specifies the positive definite form on the
existing additive group and real module, without an independent norm.
Its induced norm gives the ordinary finite dimensional topology. No embedding
in a pre-existing compact Lie group is assumed. Maximal means maximal among
all abelian real Lie subalgebras, not maximal dimension in a chosen family.
The conclusion uses a finite list of genuine adjoint exponentials, including
the empty list for the identity; it does not take their topological closure.
-/

set_option backward.isDefEq.respectTransparency false

universe u

noncomputable section

attribute [local instance] InnerProductSpace.Core.toNormedAddCommGroup
local instance LieAlgebrasAndRepresentations.CompactCartanConjugacy.coreInnerProductSpace {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    [c : InnerProductSpace.Core ℝ L] : InnerProductSpace ℝ L :=
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ L)

namespace LieAlgebrasAndRepresentations.CompactCartanConjugacy

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  [InnerProductSpace.Core ℝ L] [FiniteDimensional ℝ L]

/-- The adjoint endomorphism in the ordinary operator topology. -/
def adContinuous (z : L) : L →L[ℝ] L :=
  Module.End.toContinuousLinearMap (𝕜 := ℝ) L (LieAlgebra.ad ℝ L z)

/-- An ordered finite product, with no closure operation. -/
def innerProduct (zs : List L) : (L →L[ℝ] L)ˣ :=
  (zs.map (fun z => ClosedMatrixGroups.expUnit (adContinuous z))).prod

/-- Algebraic subgroup generation. This is not `Subgroup.topologicalClosure`. -/
def innerGroup : Subgroup (L →L[ℝ] L)ˣ :=
  Subgroup.closure (Set.range (fun z : L => ClosedMatrixGroups.expUnit (adContinuous z)))

end LieAlgebrasAndRepresentations.CompactCartanConjugacy

namespace Specs.LieAlgebrasAndRepresentations.CompactCartanConjugacy

open _root_.LieAlgebrasAndRepresentations.CompactCartanConjugacy

/-- The complete assigned statement. The invariant form and the source
notion of reductivity are explicit hypotheses, without regular-element or
group-generation certificates among the hypotheses. -/
def maximalAbelian_conjugacy_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℝ L]
    [InnerProductSpace.Core ℝ L] [FiniteDimensional ℝ L],
    ReductiveDecomposition.IsReductive_value ℝ L →
    (∀ z x y : L, inner ℝ ⁅z, x⁆ y = -inner ℝ x ⁅z, y⁆) →
    ∀ T₁ T₂ : LieSubalgebra ℝ L,
      Maximal (fun T : LieSubalgebra ℝ L => IsLieAbelian T) T₁ →
      Maximal (fun T : LieSubalgebra ℝ L => IsLieAbelian T) T₂ →
      ∃ zs : List L,
        (fun x : L => (innerProduct zs : L →L[ℝ] L) x) '' (T₁ : Set L) = (T₂ : Set L)

/-- A proved intermediate result, with precisely the centralizer meaning of
regularity used in the source. Reductivity is not needed for this lemma. -/
def exists_regular_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℝ L]
    [InnerProductSpace.Core ℝ L] [FiniteDimensional ℝ L],
    (∀ z x y : L, inner ℝ ⁅z, x⁆ y = -inner ℝ x ⁅z, y⁆) →
    ∀ T : LieSubalgebra ℝ L,
      Maximal (fun T : LieSubalgebra ℝ L => IsLieAbelian T) T →
      ∃ x ∈ T, ∀ y : L, ⁅x, y⁆ = 0 ↔ y ∈ T


/-- The finite-product interpretation of algebraic subgroup generation. -/
def mem_innerGroup_iff_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℝ L]
    [InnerProductSpace.Core ℝ L] [FiniteDimensional ℝ L]
    (g : (L →L[ℝ] L)ˣ),
    g ∈ innerGroup (L := L) ↔ ∃ zs : List L, innerProduct zs = g

/-- A conditional assembly lemma, explicitly separate from the full source
obligation `maximalAbelian_conjugacy_type` above. This is not a replacement
for proving existence of the compact group and identifying its velocities. -/
def conjugacy_of_compact_automorphisms_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℝ L]
    [InnerProductSpace.Core ℝ L] [FiniteDimensional ℝ L],
    (∀ z x y : L, inner ℝ ⁅z, x⁆ y = -inner ℝ x ⁅z, y⁆) →
    ∀ H : Subgroup (L →L[ℝ] L)ˣ,
    IsCompact (H : Set (L →L[ℝ] L)ˣ) →
    (∀ z : L, _root_.LieAlgebrasAndRepresentations.ClosedMatrixGroups.expUnit
      (adContinuous z) ∈ H) →
    (∀ g ∈ H, ∀ x y : L,
      (g : L →L[ℝ] L) ⁅x, y⁆ = ⁅(g : L →L[ℝ] L) x, (g : L →L[ℝ] L) y⁆) →
    (∀ X : L →L[ℝ] L,
      X ∈ _root_.LieAlgebrasAndRepresentations.ClosedMatrixGroups.velocities H →
      ∃ z : L, adContinuous z = X) →
    ∀ T₁ T₂ : LieSubalgebra ℝ L,
    Maximal (fun T : LieSubalgebra ℝ L => IsLieAbelian T) T₁ →
    Maximal (fun T : LieSubalgebra ℝ L => IsLieAbelian T) T₂ →
    ∃ zs : List L,
      (fun x : L => (innerProduct zs : L →L[ℝ] L) x) '' (T₁ : Set L) = (T₂ : Set L)

end Specs.LieAlgebrasAndRepresentations.CompactCartanConjugacy
