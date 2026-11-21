import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.C1Variation
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.Variation
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Order
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Calculus.MeanValue

namespace SingleVariableAnalysis.BV
open Riemann Set
open scoped BigOperators ENNReal
universe u

/-- The real polygonal sum underlying the extended-real partition sum. -/
noncomputable def polygonalSum {E : Type u} [NormedAddCommGroup E]
    {a b : ℝ} (P : Partition a b) (f : ℝ → E) : ℝ :=
  ∑ i : Fin P.n, ‖f (P.point i.succ) - f (P.point i.castSucc)‖

lemma polygonalSum_nonneg {E : Type u} [NormedAddCommGroup E]
    {a b : ℝ} (P : Partition a b) (f : ℝ → E) : 0 ≤ polygonalSum P f :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma partitionSum_ofReal {E : Type u} [NormedAddCommGroup E]
    {a b : ℝ} (P : Partition a b) (f : ℝ → E) :
    partitionSum P f = ENNReal.ofReal (polygonalSum P f) := by
  simp only [partitionSum, Specs.SingleVariableAnalysis.Ch15.Variation.partitionSumValue,
    polygonalSum, ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg _)]

lemma polygonalSum_refinement {E : Type u} [NormedAddCommGroup E]
    {a b : ℝ} (P Q : Partition a b) (f : ℝ → E) (h : Refines Q P) :
    polygonalSum P f ≤ polygonalSum Q f := by
  have hh : partitionSum P f ≤ partitionSum Q f := by
    rw [partitionSum_eq_variation_points, partitionSum_eq_variation_points]
    exact eVariationOn.mono f (by intro x hx; exact h hx)
  rw [partitionSum_ofReal, partitionSum_ofReal] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (polygonalSum_nonneg Q f)).mp hh

/-- A continuous real function on the compact interval is Darboux integrable.
This local helper uses uniform continuity and the existing Darboux criterion. -/
lemma continuousOn_realIntegrable {h : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn h (Icc a b)) : RealIntegrable h a b := by
  rcases lt_or_eq_of_le hab with hab | rfl
  · have hb : BoundedOnInterval h a b :=
      ⟨(isCompact_Icc.image_of_continuousOn hc).bddBelow,
        (isCompact_Icc.image_of_continuousOn hc).bddAbove⟩
    apply (darboux_criterion h hab hb).mpr
    intro ε hε
    let η := ε / (2 * (b - a))
    have hη : 0 < η := div_pos hε (mul_pos (by norm_num) (sub_pos.mpr hab))
    have hu := Metric.uniformContinuousOn_iff.mp
      (isCompact_Icc.uniformContinuousOn_of_continuous hc)
    obtain ⟨δ, hδ, hd⟩ := hu η hη
    obtain ⟨P, hP⟩ := exists_fine_partition hab.le δ hδ
    have ho (i : Fin P.n) :
        cellSupremum h P hb i - cellInfimum h P hb i ≤ η := by
      apply cell_oscillation_le_of_sub_le
      intro x hx y hy
      have hxy : dist x y < δ := by
        rw [Real.dist_eq, abs_lt]
        have hm := (cellLength_le_mesh P i).trans_lt hP
        change P.point i.succ - P.point i.castSucc < δ at hm
        constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
      have hh := hd x (cell_subset_interval P i hx) y (cell_subset_interval P i hy) hxy
      exact (le_abs_self _).trans (by simpa only [Real.dist_eq] using hh.le)
    refine ⟨P, ?_⟩
    have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
      mul_le_mul_of_nonneg_right (ho i) (cell_positive P i).le
    have he : η * (b - a) = ε / 2 := by dsimp [η]; field_simp
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_cellLength] at hs
    change upperSum h P hb - lowerSum h P hb ≤ η * (b - a) at hs
    rw [he] at hs
    linarith
  · exact realIntegrable_degenerate h a

/-- Bound each chord by the supremum of the speed on its cell. -/
lemma polygonalSum_le_upperSum {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {a b : ℝ}
    (hd : ∀ x ∈ Icc a b, HasDerivWithinAt f (g x) (Icc a b) x)
    (hb : BoundedOnInterval (fun x => ‖g x‖) a b) (P : Partition a b) :
    polygonalSum P f ≤ upperSum (fun x => ‖g x‖) P hb := by
  apply Finset.sum_le_sum
  intro i _
  have hsub := cell_subset_interval P i
  have hle := (convex_Icc (P.point i.castSucc) (P.point i.succ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hd x (hsub hx)).mono hsub)
    (fun x hx => le_cellSupremum (fun x => ‖g x‖) P hb i hx)
    (left_mem_Icc.mpr (P.strictMono.monotone (Fin.castSucc_le_succ i)))
    (right_mem_Icc.mpr (P.strictMono.monotone (Fin.castSucc_le_succ i)))
  change _ ≤ _ * ‖cellLength P i‖ at hle
  simpa only [Real.norm_eq_abs, abs_of_pos (cell_positive P i)] using hle

/-- Refining any fixed polygon by a small-gap Darboux partition gives an upper
bound by the integral itself, not just by one of its upper sums. -/
lemma polygonalSum_le_integral {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {a b : ℝ}
    (hd : ∀ x ∈ Icc a b, HasDerivWithinAt f (g x) (Icc a b) x)
    (hn : RealIntegrable (fun x => ‖g x‖) a b) (P : Partition a b) :
    polygonalSum P f ≤ realIntegral (fun x => ‖g x‖) hn := by
  rcases lt_or_eq_of_le (RealIntegrable.ordered hn) with hab | rfl
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨Q, hQ⟩ := (darboux_criterion _ hab (RealIntegrable.bounded hn)).mp hn ε hε
    obtain ⟨R, _, hRP, hRQ⟩ := common_refinement P Q
    have h₁ := polygonalSum_refinement P R f hRP
    have h₂ := polygonalSum_le_upperSum hd (RealIntegrable.bounded hn) R
    have h₃ := upper_refinement (fun x => ‖g x‖) Q R (RealIntegrable.bounded hn) hRQ
    have h₄ := (realIntegral_bounds (fun x => ‖g x‖) hn Q).1
    linarith
  · have hp : polygonalSum P f = 0 := by
      have : IsEmpty (Fin P.n) := Fin.isEmpty_iff.mpr (n_eq_zero_of_degenerate a P)
      simp [polygonalSum]
    rw [hp, realIntegral_degenerate]

/-- Linear approximation on a cell, using the norm mean-value inequality.
There is no assertion of a common complex mean-value point. -/
lemma chord_error_le {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {a b η : ℝ}
    (hd : ∀ x ∈ Icc a b, HasDerivWithinAt f (g x) (Icc a b) x)
    (P : Partition a b) (i : Fin P.n) (t : ℝ)
    (hg : ∀ x ∈ cell P i, ‖g x - g t‖ ≤ η) :
    ‖f (P.point i.succ) - f (P.point i.castSucc) - cellLength P i • g t‖ ≤
      η * cellLength P i := by
  have hsub := cell_subset_interval P i
  have hd' (x : ℝ) (hx : x ∈ cell P i) :
      HasDerivWithinAt (fun x => f x - x • g t) (g x - g t) (cell P i) x := by
    convert ((hd x (hsub hx)).mono hsub).sub
      ((hasDerivAt_id x).smul_const (g t)).hasDerivWithinAt using 1 <;> simp
    funext y
    rfl
  have hm := (convex_Icc (P.point i.castSucc) (P.point i.succ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hd' hg (left_mem_Icc.mpr (P.strictMono.monotone (Fin.castSucc_le_succ i)))
    (right_mem_Icc.mpr (P.strictMono.monotone (Fin.castSucc_le_succ i)))
  have he : (f (P.point i.succ) - P.point i.succ • g t) -
      (f (P.point i.castSucc) - P.point i.castSucc • g t) =
      f (P.point i.succ) - f (P.point i.castSucc) - cellLength P i • g t := by
    simp only [cellLength, S.lengthValue, sub_smul]
    abel
  rw [he] at hm
  change _ ≤ _ * ‖cellLength P i‖ at hm
  simpa only [Real.norm_eq_abs, abs_of_pos (cell_positive P i)] using hm

lemma cell_dist_le_length {a b x y : ℝ} (P : Partition a b) (i : Fin P.n)
    (hx : x ∈ cell P i) (hy : y ∈ cell P i) : dist x y ≤ cellLength P i := by
  rw [Real.dist_eq, abs_le]
  change -(P.point i.succ - P.point i.castSucc) ≤ x - y ∧
    x - y ≤ P.point i.succ - P.point i.castSucc
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- Uniform control of the derivative controls the difference between the speed
Riemann sum and the polygonal sum. -/
lemma tagged_speed_le_polygonalSum {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {a b η : ℝ}
    (hd : ∀ x ∈ Icc a b, HasDerivWithinAt f (g x) (Icc a b) x)
    (P : Partition a b) (ξ : Tagging P)
    (hg : ∀ i : Fin P.n, ∀ x ∈ cell P i, ‖g x - g (ξ i)‖ ≤ η) :
    taggedSum P ξ (fun x => ‖g x‖) ≤ polygonalSum P f + η * (b - a) := by
  have hc (i : Fin P.n) : cellLength P i * ‖g (ξ i)‖ ≤
      ‖f (P.point i.succ) - f (P.point i.castSucc)‖ + η * cellLength P i := by
    have he := chord_error_le hd P i (ξ i) (hg i)
    have hn := norm_sub_norm_le (cellLength P i • g (ξ i))
      (f (P.point i.succ) - f (P.point i.castSucc))
    rw [norm_sub_rev (cellLength P i • g (ξ i))
      (f (P.point i.succ) - f (P.point i.castSucc))] at hn
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (cell_positive P i)] at hn
    linarith
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ => hc i
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_cellLength,
    taggedSum, S.sumValue, smul_eq_mul, polygonalSum] using hs

/-- The C¹ length formula for the proper Riemann integral, including complex
paths and singleton intervals. -/
theorem c1_variation : Specs.SingleVariableAnalysis.Ch15.C1Variation.c1Variation := by
  intro E _ _ f g a b hab hd hg
  have hn := continuousOn_realIntegrable hab hg.norm
  refine ⟨hn, ?_⟩
  let I := realIntegral (fun x => ‖g x‖) hn
  have hu : totalVariation f a b ≤ ENNReal.ofReal I := by
    apply iSup_le
    intro P
    change partitionSum P f ≤ ENNReal.ofReal I
    rw [partitionSum_ofReal]
    exact ENNReal.ofReal_le_ofReal (polygonalSum_le_integral hd hn P)
  have hfinite : totalVariation f a b ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hu
  have hl : I ≤ (totalVariation f a b).toReal := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let η := ε / (2 * (b - a + 1))
    have hlen : 0 ≤ b - a := sub_nonneg.mpr hab
    have hη : 0 < η := div_pos hε (by linarith)
    have hηeq : η * (b - a + 1) = ε / 2 := by dsimp [η]; field_simp
    obtain ⟨δg, hδg, hc⟩ := Metric.uniformContinuousOn_iff.mp
      (isCompact_Icc.uniformContinuousOn_of_continuous hg) η hη
    have hlim := (real_tagged_equivalence _ hab (RealIntegrable.bounded hn) I).mp ⟨hn, rfl⟩
    obtain ⟨δn, hδn, hnclose⟩ := hlim (ε / 2) (half_pos hε)
    obtain ⟨P, hP⟩ := exists_fine_partition hab (min δg δn) (lt_min hδg hδn)
    obtain ⟨ξ⟩ := tags_exist P
    have hp : polygonalSum P f ≤ (totalVariation f a b).toReal := by
      have he : partitionSum P f ≤ totalVariation f a b := le_iSup (fun Q => partitionSum Q f) P
      have he' := ENNReal.toReal_mono hfinite he
      rwa [partitionSum_ofReal, ENNReal.toReal_ofReal (polygonalSum_nonneg P f)] at he'
    have hs := tagged_speed_le_polygonalSum hd P ξ (fun i x hx => by
      have hh := hc x (cell_subset_interval P i hx) (ξ i)
        (cell_subset_interval P i (ξ i).property)
        ((cell_dist_le_length P i hx (ξ i).property).trans_lt
          ((cellLength_le_mesh P i).trans_lt (hP.trans_le (min_le_left _ _))))
      simpa only [dist_eq_norm] using hh.le)
    have hn' := hnclose P ξ (hP.trans_le (min_le_right _ _))
    rw [Real.norm_eq_abs] at hn'
    have herr : η * (b - a) ≤ ε / 2 := by nlinarith [hη.le]
    linarith [(abs_lt.mp hn').1]
  apply le_antisymm hu
  rw [← ENNReal.ofReal_toReal hfinite]
  exact ENNReal.ofReal_le_ofReal hl

end SingleVariableAnalysis.BV
