import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.LaxMilgramEnergy
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.LaxMilgramSolvability

noncomputable section
open scoped ComplexConjugate

namespace ExpandedFA.Hilbert.LaxMilgramEnergy
universe u v

section Energy
variable {𝕜 H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- Hermitian diagonal values are real, including over the real scalar field. -/
theorem hermitian_diagonal_real
    (a : Conventions.Spec.BoundedSesquilinearFormValue 𝕜 H H)
    (ha : Conventions.Spec.FormHermitianValue 𝕜 H a) (v : H) :
    a v v = (RCLike.re (a v v) : 𝕜) :=
  (RCLike.conj_eq_iff_re.mp (ha v v).symm).symm

/-- At a solution, the energy difference is exactly half the diagonal form
at the displacement. This uses Hermitian symmetry for the cross terms. -/
theorem energy_difference
    (a : Conventions.Spec.BoundedSesquilinearFormValue 𝕜 H H)
    (F : Conventions.Spec.ContinuousAntidualValue 𝕜 H)
    (ha : Conventions.Spec.FormHermitianValue 𝕜 H a) {u : H}
    (hu : ∀ v : H, a v u = F v) (v : H) :
    Spec.energy a F v - Spec.energy a F u =
      (1 / 2 : ℝ) * RCLike.re (a (v - u) (v - u)) := by
  have hcross : RCLike.re (a u v) = RCLike.re (F v) := by
    rw [ha u v, RCLike.conj_re, hu v]
  have hdiag : RCLike.re (a u u) = RCLike.re (F u) := congrArg RCLike.re (hu u)
  have hexpand : a (v - u) (v - u) = a v v - a v u - (a u v - a u u) := by
    simp only [map_sub, sub_apply]
    abel
  rw [hexpand, map_sub, map_sub, map_sub, hu v, hcross]
  unfold Spec.energy
  linarith

/-- Coercivity converts the energy identity into a quantitative gap. -/
theorem energy_gap
    (a : Conventions.Spec.BoundedSesquilinearFormValue 𝕜 H H)
    (F : Conventions.Spec.ContinuousAntidualValue 𝕜 H) {α : ℝ}
    (hc : Conventions.Spec.FormCoerciveValue 𝕜 H a α)
    (ha : Conventions.Spec.FormHermitianValue 𝕜 H a) {u : H}
    (hu : ∀ v : H, a v u = F v) (v : H) :
    α / 2 * ‖v - u‖ ^ 2 ≤ Spec.energy a F v - Spec.energy a F u := by
  rw [energy_difference a F ha hu v]
  have h := hc.2 (v - u)
  linarith

end Energy

theorem lax_milgram : Spec.LaxMilgram.{u, v} := by
  intro 𝕜 H _ _ _ _ a α hc F
  obtain ⟨u, hu, hnorm, huniq⟩ := LaxMilgramSolvability.solvability 𝕜 H a α hc F
  refine ⟨u, hu, hnorm, huniq, ?_⟩
  intro ha
  refine ⟨hermitian_diagonal_real a ha, ?_, ?_⟩
  · intro v
    have h := energy_gap a F hc ha hu v
    have hn : 0 ≤ α / 2 * ‖v - u‖ ^ 2 :=
      mul_nonneg (le_of_lt (div_pos hc.1 (by norm_num))) (sq_nonneg _)
    linarith
  · intro w hw
    have hg := energy_gap a F hc ha hu w
    have hm := hw u
    have hs : ‖w - u‖ ^ 2 = 0 := by
      have hp : 0 < α / 2 := div_pos hc.1 (by norm_num)
      nlinarith [sq_nonneg ‖w - u‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hs))

theorem real_lax_milgram : Spec.RealLaxMilgram.{v} := by
  intro H _ _ _ a α hα hc F
  obtain ⟨u, hu, hnorm, huniq, hmin⟩ := lax_milgram ℝ H a α ⟨hα, hc⟩ F
  refine ⟨u, hu, hnorm, huniq, ?_⟩
  intro ha
  have hh : Conventions.Spec.FormHermitianValue ℝ H a := by
    intro x y
    simpa only [conj_trivial] using ha x y
  exact ⟨(hmin hh).2.1, (hmin hh).2.2⟩

end ExpandedFA.Hilbert.LaxMilgramEnergy
