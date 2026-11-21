import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch06.Schwarz
import Mathlib.Analysis.Complex.Schwarz

/-!
Schwarz's lemma and both rigidity cases, paper.tex:1476–1490.
Mathlib's Schwarz theorem assumes only complex differentiability on the
open disk. Its equality theorem applies to the divided difference `dslope`,
which equals the usual quotient away from zero and the derivative at zero.
The open target disk embeds in the closed target disk required by that theorem.
-/

open Metric Set

namespace D12Complex.Schwarz

private theorem mapsTo_closedBall {f : ℂ → ℂ}
    (hm : MapsTo f (ball 0 1) (ball 0 1)) (h0 : f 0 = 0) :
    MapsTo f (ball 0 1) (closedBall (f 0) 1) := by
  rw [h0]
  exact hm.mono_right ball_subset_closedBall

theorem norm_le_norm :
    Specs.D12Complex.Ch06.Schwarz.norm_le_norm_type := by
  intro f hf hm h0 z hz
  have hd : DifferentiableOn ℂ f (ball 0 1) :=
    fun w hw => (hf.2 w hw).differentiableWithinAt
  exact Complex.norm_le_norm_of_mapsTo_ball hd
    (hm.mono_right ball_subset_closedBall) h0 (mem_ball_zero_iff.mp hz)

theorem norm_deriv_zero_le_one :
    Specs.D12Complex.Ch06.Schwarz.norm_deriv_zero_le_one_type := by
  intro f hf hm h0
  exact Complex.norm_deriv_le_one_of_mapsTo_ball
    (fun z hz => (hf.2 z hz).differentiableWithinAt)
    (mapsTo_closedBall hm h0) zero_lt_one

theorem rotation_of_norm_eq :
    Specs.D12Complex.Ch06.Schwarz.rotation_of_norm_eq_type := by
  intro f hf hm h0 z hz hne heq
  have hd : DifferentiableOn ℂ f (ball 0 1) :=
    fun w hw => (hf.2 w hw).differentiableWithinAt
  have hs : ‖dslope f 0 z‖ = (1 : ℝ) / 1 := by
    simp [dslope_of_ne f hne, slope_def_module, h0, heq,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)]
  refine ⟨dslope f 0 z, by simpa using hs, ?_⟩
  have ha := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div hd
    (mapsTo_closedBall hm h0) hz hs
  intro w hw
  simpa [h0, smul_eq_mul, mul_comm] using ha hw

theorem rotation_of_norm_deriv_eq_one :
    Specs.D12Complex.Ch06.Schwarz.rotation_of_norm_deriv_eq_one_type := by
  intro f hf hm h0 heq
  have hd : DifferentiableOn ℂ f (ball 0 1) :=
    fun z hz => (hf.2 z hz).differentiableWithinAt
  have hs : ‖dslope f 0 0‖ = (1 : ℝ) / 1 := by simpa using heq
  have ha := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div hd
    (mapsTo_closedBall hm h0) (mem_ball_self zero_lt_one) hs
  refine ⟨deriv f 0, heq, fun z hz => ?_⟩
  simpa [h0, smul_eq_mul, mul_comm] using ha hz

theorem rotation_converse :
    Specs.D12Complex.Ch06.Schwarz.rotation_converse_type := by
  intro c hc
  have hd : ∀ z : ℂ, HasDerivAt (fun w : ℂ => c * w) c z := by
    intro z
    simpa using (hasDerivAt_id z).const_mul c
  refine ⟨⟨isOpen_ball, fun z _ => (hd z).differentiableAt⟩, ?_, mul_zero c,
    ?_, ?_⟩
  · intro z hz
    simpa only [mem_ball_zero_iff, norm_mul, hc, one_mul] using hz
  · intro z _
    simp only [norm_mul, hc, one_mul]
  · rw [(hd 0).deriv, hc]

end D12Complex.Schwarz
