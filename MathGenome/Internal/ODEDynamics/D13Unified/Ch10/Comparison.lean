import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch10.Comparison
import MathGenome.Internal.ODEDynamics.D13Unified.Ch10.Separation
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open Set Filter
open scoped Topology
namespace D13Unified.Ch10.Comparison
open Specs.D13Unified.Ch10.RegularProblem
open Specs.D13Unified.Ch10.Separation
open D13Unified.Ch10.Separation

/-- A continuous nonvanishing real function on an interval has constant sign. -/
lemma product_pos_of_nonvanishing {c d s x : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Ioo c d)) (hn : ∀ t ∈ Ioo c d, f t ≠ 0)
    (hs : s ∈ Ioo c d) (hx : x ∈ Ioo c d) : 0 < f s * f x := by
  rcases lt_or_gt_of_ne (hn s hs) with hsneg | hspos
  · have hxneg : f x < 0 := by
      by_contra! h
      obtain ⟨z, hz, hzero⟩ := isPreconnected_Ioo.intermediate_value hs hx hf ⟨hsneg.le, h⟩
      exact hn z hz hzero
    exact mul_pos_of_neg_of_neg hsneg hxneg
  · have hxpos : 0 < f x := by
      by_contra! h
      obtain ⟨z, hz, hzero⟩ := isPreconnected_Ioo.intermediate_value hx hs hf ⟨h, hspos.le⟩
      exact hn z hz hzero
    exact mul_pos hspos hxpos

/-- The derivatives at the ends of a nonnegative function vanishing at both
ends point into its nonnegative range. These are within derivatives, so this
also applies when the ends are the original problem's endpoints. -/
lemma endpoint_derivative_signs {c d A B : ℝ} {f : ℝ → ℝ} (hcd : c < d)
    (hc : f c = 0) (hd : f d = 0) (hn : ∀ x ∈ Icc c d, 0 ≤ f x)
    (hfc : HasDerivWithinAt f A (Icc c d) c)
    (hfd : HasDerivWithinAt f B (Icc c d) d) : 0 ≤ A ∧ B ≤ 0 := by
  have hminc : IsMinOn f (Icc c d) c := by
    intro x hx
    simpa [hc] using hn x hx
  have hmind : IsMinOn f (Icc c d) d := by
    intro x hx
    simpa [hd] using hn x hx
  have hdirc : d - c ∈ posTangentConeAt (Icc c d) c :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc c d).segment_subset (left_mem_Icc.mpr hcd.le) (right_mem_Icc.mpr hcd.le))
  have hdird : c - d ∈ posTangentConeAt (Icc c d) d :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc c d).segment_subset (right_mem_Icc.mpr hcd.le) (left_mem_Icc.mpr hcd.le))
  have hA := hminc.isLocalMinOn.hasFDerivWithinAt_nonneg hfc.hasFDerivWithinAt hdirc
  have hB := hmind.isLocalMinOn.hasFDerivWithinAt_nonneg hfd.hasFDerivWithinAt hdird
  change 0 ≤ (d - c) * A at hA
  change 0 ≤ (c - d) * B at hB
  constructor <;> nlinarith

/-- Wronskian identity for two different real spectral parameters. -/
lemma wronskian_derivative {P : Problem} {lam mu : ℝ} {u v : ℝ → ℝ}
    (hu : IsRealSolution P lam u) (hv : IsRealSolution P mu v)
    {x : ℝ} (hx : x ∈ intervalValue P) :
    HasDerivWithinAt (fun t => flux P u t * v t - u t * flux P v t)
      ((mu - lam) * P.w x * (u x * v x)) (intervalValue P) x := by
  convert ((solution_flux_derivative hu hx).mul (solution_derivative hv hx)).sub
    ((solution_derivative hu hx).mul (solution_flux_derivative hv hx)) using 1
  dsimp [flux]
  ring

/-- Sturm comparison, including a common zero at either or both endpoints. -/
theorem comparison : Specs.D13Unified.Ch10.Comparison.SturmComparison := by
  intro P lam mu u v hparam hu _hnu hv _hnv c d hzeros
  rcases hzeros with ⟨hc, hd, hcd, huc, hud, hnu⟩
  by_contra! hnv
  have hsub : Icc c d ⊆ intervalValue P := ordConnected_Icc.out hc hd
  have hsubo : Ioo c d ⊆ intervalValue P := Ioo_subset_Icc_self.trans hsub
  let f : ℝ → ℝ := fun t => u t * v t
  let k : ℝ := f ((c + d) / 2)
  have hf : ContinuousOn f (Icc c d) :=
    (hu.1.continuousOn.mono hsub).mul (hv.1.continuousOn.mono hsub)
  have hfnz : ∀ x ∈ Ioo c d, f x ≠ 0 := fun x hx => mul_ne_zero (hnu x hx) (hnv x hx)
  have hpos : ∀ x ∈ Ioo c d, 0 < k * f x := by
    intro x hx
    exact product_pos_of_nonvanishing (hf.mono Ioo_subset_Icc_self) hfnz
      ⟨by linarith, by linarith⟩ hx
  have hnonneg : ∀ x ∈ Icc c d, 0 ≤ k * f x := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with rfl | hcx
    · simp [f, huc]
    rcases eq_or_lt_of_le hx.2 with rfl | hxd
    · simp [f, hud]
    exact (hpos x ⟨hcx, hxd⟩).le
  have hdf (x : ℝ) (hx : x ∈ Icc c d) :
      HasDerivWithinAt (fun t => k * f t)
        (k * (derivative P u x * v x + u x * derivative P v x)) (Icc c d) x :=
    (((solution_derivative hu (hsub hx)).mul
      (solution_derivative hv (hsub hx))).const_mul k).mono hsub
  obtain ⟨hleft, hright⟩ := endpoint_derivative_signs hcd
    (by simp [f, huc]) (by simp [f, hud]) hnonneg
    (hdf c (left_mem_Icc.mpr hcd.le)) (hdf d (right_mem_Icc.mpr hcd.le))
  let W : ℝ → ℝ := fun t => k * (flux P u t * v t - u t * flux P v t)
  have hWc : 0 ≤ W c := by
    have hp := mul_nonneg (P.p_positive c hc).le hleft
    simpa [W, flux, huc, mul_assoc, mul_left_comm, mul_comm] using hp
  have hWd : W d ≤ 0 := by
    have hp := mul_nonpos_of_nonneg_of_nonpos (P.p_positive d hd).le hright
    simpa [W, flux, hud, mul_assoc, mul_left_comm, mul_comm] using hp
  have hWcont : ContinuousOn W (Icc c d) :=
    ((((flux_continuous hu).mul hv.1.continuousOn).sub
      (hu.1.continuousOn.mul (flux_continuous hv))).const_mul k).mono hsub
  have hmono : StrictMonoOn W (Icc c d) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc c d) hWcont
    intro x hx
    rw [interior_Icc] at hx
    have hder := ((wronskian_derivative hu hv (hsubo hx)).const_mul k).hasDerivAt
      (Icc_mem_nhds (hc.1.trans_lt hx.1) (hx.2.trans_le hd.2))
    rw [hder.deriv]
    have hp := mul_pos (mul_pos (sub_pos.mpr hparam) (P.w_positive x (hsubo hx))) (hpos x hx)
    dsimp [f] at hp
    nlinarith only [hp]
  have hlt := hmono (left_mem_Icc.mpr hcd.le) (right_mem_Icc.mpr hcd.le) hcd
  linarith

end D13Unified.Ch10.Comparison
