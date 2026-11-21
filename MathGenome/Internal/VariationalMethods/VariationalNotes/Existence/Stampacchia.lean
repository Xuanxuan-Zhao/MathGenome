import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Existence.Stampacchia
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.StampacchiaEnergyStability

noncomputable section
universe u
namespace VariationalNotes.Existence

section Bridges
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Convert the bounded algebraic form to a continuous form and reverse
its slots to match MathGenome's test-first convention. -/
def testFirstForm (a : H →ₗ[ℝ] H →ₗ[ℝ] ℝ) (M : ℝ)
    (ha : ∀ u v, |a u v| ≤ M * ‖u‖ * ‖v‖) : H →L[ℝ] H →L[ℝ] ℝ :=
  (a.mkContinuous₂ M (by simpa only [Real.norm_eq_abs] using ha)).flip

@[simp] theorem testFirstForm_apply (a : H →ₗ[ℝ] H →ₗ[ℝ] ℝ) (M : ℝ)
    (ha : ∀ u v, |a u v| ≤ M * ‖u‖ * ‖v‖) (v u : H) :
    testFirstForm a M ha v u = a u v := rfl

/-- A nonnegative library bound is available even when the supplied M
is negative (which is allowed in the zero space). -/
theorem testFirstForm_bound (a : H →ₗ[ℝ] H →ₗ[ℝ] ℝ) (M : ℝ)
    (ha : ∀ u v, |a u v| ≤ M * ‖u‖ * ‖v‖) :
    ExpandedFA.Hilbert.Conventions.Spec.FormBoundValue ℝ H H
      (testFirstForm a M ha) (max M 0) := by
  refine ⟨le_max_right _ _, fun v u => ?_⟩
  rw [testFirstForm_apply, Real.norm_eq_abs]
  calc
    |a u v| ≤ M * ‖u‖ * ‖v‖ := ha u v
    _ ≤ max M 0 * ‖u‖ * ‖v‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left M 0) (norm_nonneg u)) (norm_nonneg v)
    _ = max M 0 * ‖v‖ * ‖u‖ := by ring

variable [CompleteSpace H]

/-- Riesz representation in precisely the slot order used by the reused
variational inequality: the datum acts as inner v f, rather than inner f v. -/
theorem riesz_testFirst (ℓ : H →L[ℝ] ℝ) (v : H) :
    inner ℝ v ((InnerProductSpace.toDual ℝ H).symm ℓ) = ℓ v := by
  rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]

end Bridges

theorem stampacchia_existsUnique : Specs.stampacchia_existsUnique.{u} := by
  intro H _ _ _ C hne hclosed hconv a M α ha hα hc ℓ
  let B := testFirstForm a M ha
  let f := (InnerProductSpace.toDual ℝ H).symm ℓ
  have hB := testFirstForm_bound a M ha
  have hco : ExpandedFA.Hilbert.Conventions.Spec.FormCoerciveValue ℝ H B α :=
    ⟨hα, hc⟩
  have h := ExpandedFA.Hilbert.StampacchiaEnergyStability.stampacchia_exists_unique
    ℝ H B (max M 0) α hB hco f C hne hclosed hconv
  change ∃! u : H, u ∈ C ∧ ∀ v ∈ C,
    inner ℝ (v - u) ((InnerProductSpace.toDual ℝ H).symm ℓ) ≤ a u (v - u) at h
  simpa only [riesz_testFirst] using h

theorem stampacchia_minimization_iff : Specs.stampacchia_minimization_iff.{u} := by
  intro H _ _ _ C hne hclosed hconv a M α ha hα hc hsym ℓ u hu
  let B := testFirstForm a M ha
  let f := (InnerProductSpace.toDual ℝ H).symm ℓ
  have hB := testFirstForm_bound a M ha
  have hco : ExpandedFA.Hilbert.Conventions.Spec.FormCoerciveValue ℝ H B α :=
    ⟨hα, hc⟩
  have hh : ExpandedFA.Hilbert.Conventions.Spec.FormHermitianValue ℝ H B := by
    intro v w
    change a w v = a v w
    exact hsym w v
  have h := (ExpandedFA.Hilbert.StampacchiaEnergyStability.stampacchia_hermitian_minimization
    ℝ H B (max M 0) α hB hco hh f C hne hclosed hconv).1 u
  change (u ∈ C ∧ ∀ v ∈ C,
    inner ℝ (v - u) ((InnerProductSpace.toDual ℝ H).symm ℓ) ≤ a u (v - u)) ↔
    (u ∈ C ∧ ∀ v ∈ C,
      a u u / 2 - inner ℝ u ((InnerProductSpace.toDual ℝ H).symm ℓ) ≤
      a v v / 2 - inner ℝ v ((InnerProductSpace.toDual ℝ H).symm ℓ)) at h
  simpa only [riesz_testFirst, hu, true_and] using h

end VariationalNotes.Existence
