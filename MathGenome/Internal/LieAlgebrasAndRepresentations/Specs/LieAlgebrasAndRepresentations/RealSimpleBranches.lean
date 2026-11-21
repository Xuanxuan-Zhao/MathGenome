import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RealFormsConjugations
import Mathlib.Algebra.Lie.Prod
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! The general real-simple branches of LA-J07, source lines 4981–4984
and 5123–5134. Simplicity includes nonabelianness. -/

open scoped TensorProduct

universe u

namespace Specs.LieAlgebrasAndRepresentations.RealSimpleBranches

open LieAlgebrasAndRepresentations.RealForms

/-- The second branch consists of actual complementary simple ideals, exchanged
by coefficient conjugation. The original real algebra is the restriction of a
simple factor. -/
def real_simple_branches_type : Prop :=
  ∀ (L : Type u) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L],
    LieAlgebra.IsSimple ℝ L →
    LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] L) ∨
      ∃ I J : LieIdeal ℂ (ℂ ⊗[ℝ] L),
        IsCompl I J ∧ LieAlgebra.IsSimple ℂ I ∧ LieAlgebra.IsSimple ℂ J ∧
        (∀ z, z ∈ I ↔ coefficientConjugationMap L z ∈ J) ∧
        Nonempty (I ≃ₗ⁅ℂ⁆ J) ∧ Nonempty (L ≃ₗ⁅ℝ⁆ I) ∧
        ∃ e : (I × J) ≃ₗ⁅ℂ⁆ (ℂ ⊗[ℝ] L),
          ∀ x y, e (x, y) = (x : ℂ ⊗[ℝ] L) + (y : ℂ ⊗[ℝ] L)

/-- A complex simple algebra stays simple under restriction to ℝ. In the
specified product coordinates its complexification conjugation exchanges the
two copies via a conjugate-linear Lie involution. -/
def complex_simple_restriction_type : Prop :=
  ∀ (L : Type u) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    LieAlgebra.IsSimple ℂ L →
    LieAlgebra.IsSimple ℝ L ∧
      ∃ (σ : Conjugation L) (e : (ℂ ⊗[ℝ] L) ≃ₗ⁅ℂ⁆ (L × L)),
        (∀ (a : ℂ) (x : L), e (a ⊗ₜ[ℝ] x) = (a • x, a • σ.map x)) ∧
        ∀ z, e (coefficientConjugationMap L z) =
          (σ.map (e z).2, σ.map (e z).1)

end Specs.LieAlgebrasAndRepresentations.RealSimpleBranches
