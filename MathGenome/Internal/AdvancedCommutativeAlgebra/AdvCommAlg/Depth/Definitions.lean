import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.RegularSequence.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.Definitions

/-! Grade and local depth, paper.tex:2628–2636, DP-01.
We retain the regular-length definition directly. The formulas are defined
also without Noetherian or finiteness hypotheses; thus they apply in particular
to every ring and module in the source's stated domain. No identification with
Mathlib's Ext-defined depth is assumed. -/

universe u v
open scoped Pointwise
namespace AdvCommAlg.Depth

/-- Grade with respect to `I`: infinity when `IM = M`, and otherwise the
supremum in `ℕ∞` of lengths of proper regular lists contained in `I`. -/
noncomputable def grade {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] : ℕ∞ := by
  classical
  exact if I • (⊤ : Submodule R M) = ⊤ then ⊤ else
    sSup {(x.length : ℕ∞) | (x : List R)
      (_ : RegularSequence.Regular M x) (_ : ∀ a ∈ x, a ∈ I)}

/-- Local depth is grade with respect to the maximal ideal. -/
noncomputable def depth (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] : ℕ∞ :=
  grade (IsLocalRing.maximalIdeal R) M

theorem grade_of_smul_eq_top {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (h : I • (⊤ : Submodule R M) = ⊤) : grade I M = ⊤ := by
  classical
  simp [grade, h]

theorem grade_of_smul_ne_top {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (h : I • (⊤ : Submodule R M) ≠ ⊤) : grade I M =
      sSup {(x.length : ℕ∞) | (x : List R)
        (_ : RegularSequence.Regular M x) (_ : ∀ a ∈ x, a ∈ I)} := by
  classical
  simp [grade, h]

theorem depth_eq_grade (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    depth R M = grade (IsLocalRing.maximalIdeal R) M := rfl

/-- The zero module has infinite grade, for every ideal. -/
theorem grade_eq_top_of_subsingleton {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] [Subsingleton M] :
    grade I M = ⊤ := by
  apply grade_of_smul_eq_top
  exact Subsingleton.elim _ _

/-- In particular, the zero module has infinite local depth. -/
theorem depth_eq_top_of_subsingleton (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Subsingleton M] :
    depth R M = ⊤ :=
  grade_eq_top_of_subsingleton _ M

end AdvCommAlg.Depth
