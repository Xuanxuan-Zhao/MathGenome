import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.CartanData
import Mathlib.Tactic.Ring

namespace LieNotes.Contragredient

open _root_.Specs.LieNotes.Contragredient

universe u v

variable {I : Type u} {A : Matrix I I ℤ}
variable {H : Type v} [AddCommGroup H] [Module ℂ H]

abbrev IsGeneralizedCartanMatrix [Finite I] (A : Matrix I I ℤ) := CartanData.IsGeneralizedCartanMatrix A
abbrev IsSymmetrizable [Finite I] (A : Matrix I I ℤ) := CartanData.IsSymmetrizable A
abbrev Realization [Finite I] (A : Matrix I I ℤ) (H : Type v) [AddCommGroup H] [Module ℂ H] :=
  CartanData.Realization A H
abbrev Q (I : Type u) := CartanData.Q I
noncomputable abbrev simpleDegree (i : I) : Q I := CartanData.simpleDegree i
abbrev PositiveDegree (q : Q I) := CartanData.PositiveDegree q
abbrev NegativeDegree (q : Q I) := CartanData.NegativeDegree q

namespace Realization

variable [Finite I]

abbrev IsMinimal [Fintype I] (R : Realization A H) := CartanData.Realization.IsMinimal R
noncomputable abbrev rootWeight (R : Realization A H) : Q I →+ Module.Dual ℂ H :=
  CartanData.Realization.rootWeight R
abbrev weightReflection (R : Realization A H) (i : I) :
    Module.Dual ℂ H →ₗ[ℂ] Module.Dual ℂ H :=
  CartanData.Realization.weightReflection R i

theorem rootWeight_single (R : Realization A H) (i : I) (m : ℤ) :
    R.rootWeight (Finsupp.single i m) = (m : ℂ) • R.α i := by
  change (Finsupp.linearCombination ℂ R.α)
    (Finsupp.mapRange ((↑) : ℤ → ℂ) (Int.cast_zero (R := ℂ)) (Finsupp.single i m)) = _
  rw [Finsupp.mapRange_single, Finsupp.linearCombination_single]

@[simp]
theorem rootWeight_simple (R : Realization A H) (i : I) :
    R.rootWeight (simpleDegree i) = R.α i := by
  simp [CartanData.simpleDegree, rootWeight_single]

theorem rootWeight_injective (R : Realization A H) : Function.Injective R.rootWeight :=
  R.α_independent.finsuppLinearCombination_injective.comp
    (Finsupp.mapRange_injective _ (Int.cast_zero (R := ℂ)) Int.cast_injective)

end Realization

noncomputable abbrev corootPairing (A : Matrix I I ℤ) (i : I) : Q I →ₗ[ℤ] ℤ :=
  CartanData.corootPairing A i

noncomputable abbrev rootReflection (A : Matrix I I ℤ) (i : I) : Q I →ₗ[ℤ] Q I :=
  CartanData.rootReflection A i

@[simp]
theorem corootPairing_single (A : Matrix I I ℤ) (i j : I) (m : ℤ) :
    corootPairing A i (Finsupp.single j m) = m * A i j :=
  Finsupp.linearCombination_single ℤ (v := A i) m j

theorem rootReflection_apply (A : Matrix I I ℤ) (i : I) (q : Q I) :
    rootReflection A i q = q - Finsupp.single i (corootPairing A i q) :=
  rfl

variable [Finite I]

theorem Realization.rootWeight_apply_coroot (R : Realization A H) (q : Q I) (i : I) :
    R.rootWeight q (R.h i) = (corootPairing A i q : ℂ) := by
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq =>
      simp only [map_add, LinearMap.add_apply, Int.cast_add, hp, hq]
  | single j m =>
      simp [rootWeight_single, R.pairing, LinearMap.smul_apply, smul_eq_mul]

theorem Realization.weightReflection_apply (R : Realization A H) (i : I) (μ : Module.Dual ℂ H) :
    R.weightReflection i μ = μ - μ (R.h i) • R.α i :=
  rfl

theorem Realization.rootWeight_rootReflection (R : Realization A H) (i : I) (q : Q I) :
    R.rootWeight (rootReflection A i q) = R.weightReflection i (R.rootWeight q) := by
  simp only [rootReflection_apply, map_sub, rootWeight_single, weightReflection_apply,
    rootWeight_apply_coroot]

theorem rootReflection_involutive (hA : IsGeneralizedCartanMatrix A) (i : I) :
    Function.Involutive (rootReflection A i) := by
  intro q
  have h (m : ℤ) : m - m * A i i = -m := by rw [hA.1 i]; ring
  simp only [rootReflection_apply]
  rw [map_sub, corootPairing_single, h, Finsupp.single_neg]
  simp

theorem Realization.weightReflection_involutive (R : Realization A H)
    (hA : IsGeneralizedCartanMatrix A) (i : I) :
    Function.Involutive (R.weightReflection i) := by
  intro μ
  ext x
  have hdiag : R.α i (R.h i) = 2 := by simp [R.pairing, hA.1 i]
  simp only [weightReflection_apply, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hdiag]
  ring

end LieNotes.Contragredient
