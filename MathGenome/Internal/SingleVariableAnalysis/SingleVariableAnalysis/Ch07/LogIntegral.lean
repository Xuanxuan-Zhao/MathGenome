import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.LogIntegral
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.LogDerivative
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.FtcFirst
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch05.ZeroDerivative

/-! The integral comparison uses only proper Darboux integration. On a positive
compact interval the reciprocal has a bounded Lipschitz constant, so its
Darboux gaps tend to zero with the mesh. FTC then gives a primitive on a
slightly larger interval containing both 1 and x in its interior. Primitive
uniqueness and oriented additivity identify its difference with seriesLog x.
Neither a measure integral nor a preexisting logarithmic integral is used. -/
namespace SingleVariableAnalysis
open Set
open scoped BigOperators Topology
open Riemann

/-- A bounded Lipschitz function has arbitrarily small Darboux gaps. -/
theorem Riemann.realIntegrable_of_bounded_lipschitz {f : ℝ → ℝ} {a b C : ℝ}
    (hab : a ≤ b) (hf : BoundedOnInterval f a b) (hC : 0 ≤ C)
    (hLip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |f x - f y| ≤ C * |x-y|) :
    RealIntegrable f a b := by
  apply (realIntegrable_iff_small_gap f hab hf).mpr
  intro ε hε
  let η := ε / (b-a+1)
  have hlen : 0 ≤ b-a := sub_nonneg.mpr hab
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨P, hP⟩ := exists_fine_partition hab (η / (C+1)) (by positivity)
  have hcell (i : Fin P.n) :
      cellSupremum f P hf i - cellInfimum f P hf i ≤ C * mesh P := by
    apply cell_oscillation_le_of_sub_le
    intro x hx y hy
    have hxy : |x-y| ≤ cellLength P i := by
      apply abs_le.mpr
      change x ∈ Icc _ _ at hx
      change y ∈ Icc _ _ at hy
      change -(P.point i.succ - P.point i.castSucc) ≤ x-y ∧
        x-y ≤ P.point i.succ - P.point i.castSucc
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    exact (le_abs_self _).trans ((hLip x (cell_subset_interval P i hx)
      y (cell_subset_interval P i hy)).trans
      (mul_le_mul_of_nonneg_left (hxy.trans (cellLength_le_mesh P i)) hC))
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    mul_le_mul_of_nonneg_right (hcell i) (cell_positive P i).le
  rw [sum_cell_oscillation, ← Finset.mul_sum, sum_cellLength] at hs
  refine ⟨P, hs.trans_lt ?_⟩
  have hsmall : C * mesh P < η := by
    have hp := (lt_div_iff₀ (show 0 < C+1 by positivity)).mp hP
    nlinarith [mesh_nonneg P]
  have hηeq : η * (b-a+1) = ε := by
    dsimp [η]
    exact div_mul_cancel₀ _ (by positivity)
  nlinarith [mul_le_mul_of_nonneg_right hsmall.le hlen]

theorem reciprocal_riemann_integrable :
    Specs.SingleVariableAnalysis.Ch07.LogIntegral.reciprocalIntegrable := by
  intro a b ha hab
  have hb : BoundedOnInterval (fun t => 1 / t) a b := by
    apply boundedOnInterval_of_abs (M := 1 / a)
    intro t ht
    simpa only [one_div, Real.norm_eq_abs] using
      norm_inv_le_of_lower_bound (u := t) ha (ht.1.trans (le_abs_self t))
  apply Riemann.realIntegrable_of_bounded_lipschitz hab hb (show 0 ≤ 1/(a*a) by positivity)
  intro u hu v hv
  simpa only [one_div, Real.norm_eq_abs] using
    norm_inv_sub_inv_le_of_lower_bound (u := u) (v := v) ha
      (by simpa only [Real.norm_eq_abs] using hu.1.trans (le_abs_self u))
      (by simpa only [Real.norm_eq_abs] using hv.1.trans (le_abs_self v))

theorem reciprocal_primitive_comparison :
    Specs.SingleVariableAnalysis.Ch07.LogIntegral.primitiveComparison := by
  intro F I hI hpos h1 hF hD x hx
  have hlog : ContinuousOn seriesLog I := seriesLog_continuousOn.mono hpos
  have hLD (t : ℝ) (ht : t ∈ interior I) : HasDerivAt seriesLog (1/t) t :=
    seriesLog_hasDerivAt t (hpos (interior_subset ht))
  obtain ⟨c, hc⟩ := real_equal_derivatives_differ_by_constant F seriesLog I hI hF hlog
    (fun t ht => (hD t ht).differentiableAt)
    (fun t ht => (hLD t ht).differentiableAt)
    (fun t ht => (hD t ht).deriv.trans (hLD t ht).deriv.symm)
  have hone := hc 1 h1
  have hx' := hc x hx
  rw [show seriesLog 1 = 0 from seriesLog_one] at hone
  change F x - F 1 = seriesLog x
  linarith

theorem seriesLog_eq_oriented_integral :
    Specs.SingleVariableAnalysis.Ch07.LogIntegral.integralComparison := by
  intro x hx
  let a := min 1 x / 2
  let b := max 1 x + 1
  have ha : 0 < a := by dsimp [a]; exact half_pos (lt_min zero_lt_one hx)
  have ha1 : a < 1 := by
    have := min_le_left (1 : ℝ) x
    dsimp [a]
    linarith
  have hax : a < x := by
    have := min_le_right (1 : ℝ) x
    dsimp [a]
    linarith
  have h1b : 1 < b := by dsimp [b]; linarith [le_max_left (1 : ℝ) x]
  have hxb : x < b := by dsimp [b]; linarith [le_max_right (1 : ℝ) x]
  have hab : a ≤ b := ha1.le.trans h1b.le
  have hf := reciprocal_riemann_integrable a b ha hab
  obtain ⟨F, hF⟩ := real_accumulation_exists (fun t => 1/t) hf
  have hD (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt F (1/t) t := by
    apply real_ftc_first_interior (fun t => 1/t) F hf hF t ht
    exact (continuousAt_const.div continuousAt_id (ne_of_gt (ha.trans ht.1))).continuousWithinAt
  have hc : ContinuousOn F (Ioo a b) := fun t ht => (hD t ht).continuousAt.continuousWithinAt
  have hdiff : F x - F 1 = seriesLog x :=
    reciprocal_primitive_comparison F (Ioo a b) ordConnected_Ioo
      (fun t ht => ha.trans ht.1) ⟨ha1, h1b⟩ hc
      (fun t ht => hD t (by simpa only [isOpen_Ioo.interior_eq] using ht)) x ⟨hax, hxb⟩
  have hHull : RealIntegrable (fun t => 1/t) (min a (min 1 x)) (max a (max 1 x)) :=
    RealIntegrable.subinterval hf (le_min le_rfl (le_min ha1.le hax.le))
      ((min_le_left _ _).trans (le_max_left _ _))
      (max_le hab (max_le h1b.le hxb.le))
  obtain ⟨haOne, hOneX, haX, hadd⟩ := oriented_real_additivity (fun t => 1/t) a 1 x hHull
  obtain ⟨h1, hF1⟩ := hF 1 ⟨ha1.le, h1b.le⟩
  obtain ⟨hxi, hFx⟩ := hF x ⟨hax.le, hxb.le⟩
  rw [oriented_real_agreement _ ha1.le haOne h1,
    oriented_real_agreement _ hax.le haX hxi, ← hF1, ← hFx] at hadd
  refine ⟨hOneX, ?_⟩
  change seriesLog x = orientedRealIntegral (fun t => 1/t) hOneX
  linarith

end SingleVariableAnalysis
