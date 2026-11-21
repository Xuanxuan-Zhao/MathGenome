import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.RsDarboux
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.RsSums
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.DarbouxSums

namespace SingleVariableAnalysis.Stieltjes
open Riemann
open scoped BigOperators
namespace Darboux
namespace D
export Specs.SingleVariableAnalysis.Ch15.RsDarboux
  (upperSumValue lowerSumValue upperIntegralValue lowerIntegralValue)
end D
noncomputable abbrev upperSum := @D.upperSumValue
noncomputable abbrev lowerSum := @D.lowerSumValue
noncomputable abbrev upperIntegral := D.upperIntegralValue
noncomputable abbrev lowerIntegral := D.lowerIntegralValue

def weight {a b : ℝ} (α : ℝ → ℝ) (P : Partition a b) (i : Fin P.n) : ℝ :=
  α (P.point i.succ) - α (P.point i.castSucc)

theorem point_mem {a b : ℝ} (P : Partition a b) (i : Fin (P.n+1)) :
    P.point i ∈ Set.Icc a b := by
  exact ⟨by simpa only [P.first] using P.strictMono.monotone (Fin.zero_le i),
    by simpa only [P.last] using P.strictMono.monotone (Fin.le_last i)⟩

theorem weight_nonneg {a b : ℝ} {α : ℝ → ℝ}
    (hα : MonotoneOn α (Set.Icc a b)) (P : Partition a b) (i : Fin P.n) :
    0 ≤ weight α P i :=
  sub_nonneg.mpr (hα (point_mem P _) (point_mem P _)
    (P.strictMono (Fin.castSucc_lt_succ (i := i))).le)

theorem tagged_bounds {a b : ℝ} (f α : ℝ → ℝ) (hf : BoundedOnInterval f a b)
    (hα : MonotoneOn α (Set.Icc a b)) (P : Partition a b) (t : Tagging P) :
    lowerSum f α P hf ≤ Stieltjes.taggedSum P t f α ∧
    Stieltjes.taggedSum P t f α ≤ upperSum f α P hf := by
  simp only [Stieltjes.taggedSum, Stieltjes.S.sumValue, smul_eq_mul, mul_comm]
  constructor
  · exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (cellInfimum_le f P hf i (t i).property)
        (weight_nonneg hα P i)
  · exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (le_cellSupremum f P hf i (t i).property)
        (weight_nonneg hα P i)

/-- The telescoping refinement argument with integrator increments, including
zero increments. The endpoint inclusion is the upstream refinement index. -/
theorem weighted_refinement_le {a b : ℝ} (α : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b)) (P Q : Partition a b)
    (h : Refines Q P) (cP : Fin P.n → ℝ) (cQ : Fin Q.n → ℝ)
    (hc : ∀ (i : Fin P.n) (j : Fin Q.n), cell Q j ⊆ cell P i → cQ j ≤ cP i) :
    (∑ j : Fin Q.n, cQ j * weight α Q j) ≤
      ∑ i : Fin P.n, cP i * weight α P i := by
  classical
  let e := refinementIndex h
  let w : ℕ → ℝ := fun k => if hk : k < Q.n then
    cQ ⟨k, hk⟩ * weight α Q ⟨k, hk⟩ else 0
  let F : ℕ → ℝ := fun k => ∑ t ∈ Finset.range k, w t
  have hsegment (i : Fin P.n) :
      F (e i.succ).val - F (e i.castSucc).val ≤ cP i * weight α P i := by
    have hlr : (e i.castSucc).val ≤ (e i.succ).val :=
      ((refinementIndex_strictMono h) (Fin.castSucc_lt_succ (i := i))).le
    have hterm (k : ℕ) (hk : k ∈ Finset.Ico (e i.castSucc).val (e i.succ).val) :
        w k ≤ cP i * (α (endpointAt Q (k + 1)) - α (endpointAt Q k)) := by
      obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hk
      have hkQ : k < Q.n := by have := (e i.succ).isLt; omega
      let j : Fin Q.n := ⟨k, hkQ⟩
      have hsub : cell Q j ⊆ cell P i := by
        intro x hx
        have hl : Q.point (e i.castSucc) ≤ Q.point j.castSucc :=
          Q.strictMono.monotone (show e i.castSucc ≤ j.castSucc from hlo)
        have hr : Q.point j.succ ≤ Q.point (e i.succ) :=
          Q.strictMono.monotone (show j.succ ≤ e i.succ from Nat.succ_le_of_lt hhi)
        rw [point_refinementIndex] at hl hr
        exact ⟨hl.trans hx.1, hx.2.trans hr⟩
      dsimp only [w]
      rw [dite_eq_left hkQ]
      change cQ j * weight α Q j ≤
        cP i * (α (endpointAt Q (k + 1)) - α (endpointAt Q k))
      rw [show endpointAt Q (k + 1) = Q.point j.succ from endpointAt_eq Q j.succ,
        show endpointAt Q k = Q.point j.castSucc from endpointAt_eq Q j.castSucc]
      exact mul_le_mul_of_nonneg_right (hc i j hsub) (weight_nonneg hα Q j)
    calc
      F (e i.succ).val - F (e i.castSucc).val =
          ∑ k ∈ Finset.Ico (e i.castSucc).val (e i.succ).val, w k :=
        (Finset.sum_Ico_eq_sub w hlr).symm
      _ ≤ ∑ k ∈ Finset.Ico (e i.castSucc).val (e i.succ).val,
          cP i * (α (endpointAt Q (k + 1)) - α (endpointAt Q k)) :=
        Finset.sum_le_sum hterm
      _ = cP i * (α (endpointAt Q (e i.succ).val) -
          α (endpointAt Q (e i.castSucc).val)) := by
        rw [← Finset.mul_sum, Finset.sum_Ico_sub (fun k => α (endpointAt Q k)) hlr]
      _ = cP i * weight α P i := by
        rw [endpointAt_eq, endpointAt_eq, point_refinementIndex, point_refinementIndex]
        rfl
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hsegment i)
  rw [sum_cell_differences (fun i => F (e i).val)] at hs
  change F (refinementIndex h (Fin.last P.n)).val -
    F (refinementIndex h 0).val ≤ _ at hs
  rw [refinementIndex_last, refinementIndex_zero] at hs
  have htotal : F Q.n = ∑ j : Fin Q.n, cQ j * weight α Q j :=
    (Finset.sum_fin_eq_sum_range (fun j : Fin Q.n => cQ j * weight α Q j)).symm
  have hzero : F 0 = 0 := Finset.sum_range_zero w
  simpa only [Fin.val_last, Fin.val_zero, htotal, hzero, sub_zero] using hs

theorem refinement : Specs.SingleVariableAnalysis.Ch15.RsDarboux.refinement := by
  intro a b f α hf hα P Q h
  constructor
  · have hs := weighted_refinement_le α hα P Q h
      (fun i => -cellInfimum f P hf i) (fun j => -cellInfimum f Q hf j)
      (fun i j hc => neg_le_neg (cellInfimum_mono f P Q hf i j hc))
    change (∑ i : Fin P.n, cellInfimum f P hf i * weight α P i) ≤
      ∑ j : Fin Q.n, cellInfimum f Q hf j * weight α Q j
    simpa only [neg_mul, Finset.sum_neg_distrib, neg_le_neg_iff] using hs
  · exact weighted_refinement_le α hα P Q h (cellSupremum f P hf)
      (cellSupremum f Q hf) (fun i j hc => cellSupremum_mono f P Q hf i j hc)

theorem lower_le_upper {a b : ℝ} (f α : ℝ → ℝ) (hf : BoundedOnInterval f a b)
    (hα : MonotoneOn α (Set.Icc a b)) (P Q : Partition a b) :
    lowerSum f α P hf ≤ upperSum f α Q hf := by
  obtain ⟨R, _, hRP, hRQ⟩ := common_refinement P Q
  obtain ⟨t⟩ := tags_exist R
  exact (refinement a b f α hf hα P R hRP).1.trans
    (((tagged_bounds f α hf hα R t).1.trans (tagged_bounds f α hf hα R t).2).trans
      (refinement a b f α hf hα Q R hRQ).2)

/-- Finite independent choices approximate a weighted sum even when some
weights vanish. There is no requirement that any extremum be attained. -/
theorem approximate_weighted_sum {n : ℕ} (X : Fin n → Type)
    (g : ∀ i, X i → ℝ) (v w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hv : ∀ δ : ℝ, 0 < δ → ∀ i, ∃ x : X i, |g i x - v i| < δ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ∀ i, X i, |(∑ i, g i (t i) * w i) - ∑ i, v i * w i| < ε := by
  classical
  let W := ∑ i, w i
  have hW : 0 ≤ W := Finset.sum_nonneg fun i _ => hw i
  let δ := ε / (W + 1)
  have hd : 0 < δ := div_pos hε (by linarith)
  choose t ht using hv δ hd
  refine ⟨t, ?_⟩
  have heq : δ * (W + 1) = ε := div_mul_cancel₀ _ (by linarith : W+1 ≠ 0)
  calc
    |(∑ i, g i (t i) * w i) - ∑ i, v i * w i| =
        |∑ i, (g i (t i) - v i) * w i| := by
      simp only [sub_mul, Finset.sum_sub_distrib]
    _ ≤ ∑ i, |(g i (t i) - v i) * w i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, δ * w i := Finset.sum_le_sum fun i _ => by
      rw [abs_mul, abs_of_nonneg (hw i)]
      exact mul_le_mul_of_nonneg_right (ht i).le (hw i)
    _ = δ * W := (Finset.mul_sum _ _ _).symm
    _ < ε := by nlinarith

theorem tag_approximation {a b : ℝ} (f α : ℝ → ℝ)
    (hf : BoundedOnInterval f a b) (hα : MonotoneOn α (Set.Icc a b))
    (P : Partition a b) (ε : ℝ) (hε : 0 < ε) :
    (∃ t : Tagging P, |Stieltjes.taggedSum P t f α - lowerSum f α P hf| < ε) ∧
    (∃ t : Tagging P, |Stieltjes.taggedSum P t f α - upperSum f α P hf| < ε) := by
  have hsup (δ : ℝ) (hd : 0 < δ) (i : Fin P.n) :
      ∃ x : {x : ℝ // x ∈ cell P i}, |f x - cellSupremum f P hf i| < δ := by
    obtain ⟨y, ⟨x, hx, rfl⟩, hlt, hle⟩ :=
      (cell_bounds f P hf i).2.exists_between (sub_lt_self _ hd)
    exact ⟨⟨x, hx⟩, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
  have hinf (δ : ℝ) (hd : 0 < δ) (i : Fin P.n) :
      ∃ x : {x : ℝ // x ∈ cell P i}, |f x - cellInfimum f P hf i| < δ := by
    obtain ⟨y, ⟨x, hx, rfl⟩, hle, hlt⟩ :=
      (cell_bounds f P hf i).1.exists_between (lt_add_of_pos_right _ hd)
    exact ⟨⟨x, hx⟩, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
  constructor
  · obtain ⟨t, ht⟩ := approximate_weighted_sum (fun i => {x : ℝ // x ∈ cell P i})
      (fun _ x => f x) (cellInfimum f P hf) (weight α P) (weight_nonneg hα P)
      hinf ε hε
    refine ⟨t, ?_⟩
    simp only [Stieltjes.taggedSum, Stieltjes.S.sumValue, smul_eq_mul, mul_comm]
    exact ht
  · obtain ⟨t, ht⟩ := approximate_weighted_sum (fun i => {x : ℝ // x ∈ cell P i})
      (fun _ x => f x) (cellSupremum f P hf) (weight α P) (weight_nonneg hα P)
      hsup ε hε
    refine ⟨t, ?_⟩
    simp only [Stieltjes.taggedSum, Stieltjes.S.sumValue, smul_eq_mul, mul_comm]
    exact ht

theorem tag_extrema : Specs.SingleVariableAnalysis.Ch15.RsDarboux.tagExtrema := by
  intro a b f α hf hα P
  constructor
  · constructor
    · rintro _ ⟨t, rfl⟩
      exact (tagged_bounds f α hf hα P t).1
    · intro u hu
      apply le_of_forall_pos_lt_add
      intro ε hε
      obtain ⟨t, ht⟩ := (tag_approximation f α hf hα P ε hε).1
      have h := hu (Set.mem_range_self t)
      have h' := (abs_lt.mp ht).2
      linarith
  · constructor
    · rintro _ ⟨t, rfl⟩
      exact (tagged_bounds f α hf hα P t).2
    · intro u hu
      apply le_of_forall_pos_lt_add
      intro ε hε
      obtain ⟨t, ht⟩ := (tag_approximation f α hf hα P ε hε).2
      have h := hu (Set.mem_range_self t)
      have h' := (abs_lt.mp ht).1
      linarith

theorem partitions_nonempty {a b : ℝ} (hab : a ≤ b) : Nonempty (Partition a b) := by
  rcases hab.eq_or_lt with rfl | hlt
  · exact ⟨emptyPartition a⟩
  · exact ⟨uniformPartition hlt 1 (by decide)⟩

theorem integral_bounds : Specs.SingleVariableAnalysis.Ch15.RsDarboux.integralBounds := by
  intro a b hab f α hf hα
  letI : Nonempty (Partition a b) := partitions_nonempty hab
  let P₀ : Partition a b := Classical.choice (partitions_nonempty hab)
  have hbU : BddBelow (Set.range (fun P : Partition a b => upperSum f α P hf)) := by
    refine ⟨lowerSum f α P₀ hf, ?_⟩
    rintro _ ⟨Q, rfl⟩
    exact lower_le_upper f α hf hα P₀ Q
  have hbL : BddAbove (Set.range (fun P : Partition a b => lowerSum f α P hf)) := by
    refine ⟨upperSum f α P₀ hf, ?_⟩
    rintro _ ⟨P, rfl⟩
    exact lower_le_upper f α hf hα P P₀
  refine ⟨isGLB_csInf (Set.range_nonempty _) hbU,
    isLUB_csSup (Set.range_nonempty _) hbL, ?_⟩
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨Q, rfl⟩
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨P, rfl⟩
  exact lower_le_upper f α hf hα P Q

theorem epsilon_criterion : Specs.SingleVariableAnalysis.Ch15.RsDarboux.epsilonCriterion := by
  intro a b hab f α hf hα
  obtain ⟨hU, hL, hLU⟩ := integral_bounds a b hab f α hf hα
  constructor
  · intro heq ε hε
    obtain ⟨u, ⟨P, rfl⟩, _, hP⟩ :=
      hU.exists_between (lt_add_of_pos_right _ (half_pos hε))
    obtain ⟨l, ⟨Q, rfl⟩, hQ, _⟩ :=
      hL.exists_between (sub_lt_self _ (half_pos hε))
    obtain ⟨R, _, hRP, hRQ⟩ := common_refinement P Q
    refine ⟨R, ?_⟩
    have hu := (refinement a b f α hf hα P R hRP).2
    have hl := (refinement a b f α hf hα Q R hRQ).1
    linarith
  · intro h
    apply le_antisymm _ hLU
    apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨P, hP⟩ := h ε hε
    have hu := hU.1 (Set.mem_range_self P)
    have hl := hL.1 (Set.mem_range_self P)
    linarith

/-- Interval boundedness in order form implies the upstream norm bound. -/
theorem boundedOn_of_boundedOnInterval {a b : ℝ} {f : ℝ → ℝ}
    (hf : BoundedOnInterval f a b) : BoundedOn a b f := by
  obtain ⟨l, hl⟩ := hf.1
  obtain ⟨u, hu⟩ := hf.2
  refine ⟨max |l| |u|, ?_⟩
  intro x hx
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · exact (neg_le_neg (le_max_left |l| |u|)).trans
      ((neg_abs_le l).trans (hl (Set.mem_image_of_mem f hx)))
  · exact (hu (Set.mem_image_of_mem f hx)).trans
      ((le_abs_self u).trans (le_max_right |l| |u|))

theorem monotone_boundedOn {a b : ℝ} (hab : a ≤ b) {α : ℝ → ℝ}
    (hα : MonotoneOn α (Set.Icc a b)) : BoundedOn a b α := by
  apply boundedOn_of_boundedOnInterval
  constructor
  · refine ⟨α a, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hα ⟨le_rfl, hab⟩ hx hx.1
  · refine ⟨α b, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hα hx ⟨hab, le_rfl⟩ hx.2

theorem integral_of_equal {a b : ℝ} (hab : a ≤ b) (f α : ℝ → ℝ)
    (hf : BoundedOnInterval f a b) (hα : MonotoneOn α (Set.Icc a b))
    (heq : upperIntegral f α a b hf = lowerIntegral f α a b hf) :
    HasIntegral a b f α (lowerIntegral f α a b hf) := by
  apply (integral_iff_of_le a b hab f α _).mpr
  refine ⟨boundedOn_of_boundedOnInterval hf, monotone_boundedOn hab hα, ?_⟩
  intro ε hε
  obtain ⟨P₀, hP₀⟩ := (epsilon_criterion a b hab f α hf hα).mp heq ε hε
  refine ⟨P₀, ?_⟩
  intro P hP t
  obtain ⟨hU, hL, _⟩ := integral_bounds a b hab f α hf hα
  have hli := hL.1 (Set.mem_range_self P₀)
  have hiu := hU.1 (Set.mem_range_self P₀)
  have hbounds := tagged_bounds f α hf hα P t
  have href := refinement a b f α hf hα P₀ P hP
  rw [Real.norm_eq_abs]
  apply abs_lt.mpr
  constructor <;> linarith

theorem epsilon_of_integral {a b : ℝ} (hab : a ≤ b) (f α : ℝ → ℝ)
    (hf : BoundedOnInterval f a b) (hα : MonotoneOn α (Set.Icc a b))
    {I : ℝ} (hI : HasIntegral a b f α I) :
    ∀ ε : ℝ, 0 < ε → ∃ P : Partition a b,
      upperSum f α P hf - lowerSum f α P hf < ε := by
  have hlim := ((integral_iff_of_le a b hab f α I).mp hI).2.2
  intro ε hε
  obtain ⟨P, hP⟩ := hlim (ε/3) (by linarith)
  have hrefl : Refines P P := (refinement_laws P P P).1
  have hsum (t : Tagging P) := hP P hrefl t
  obtain ⟨hl, hu⟩ := tag_extrema a b f α hf hα P
  have hupper : upperSum f α P hf ≤ I + ε/3 := by
    apply hu.2
    rintro _ ⟨t, rfl⟩
    have ht := (abs_lt.mp (show |Stieltjes.taggedSum P t f α - I| < ε/3 by
      simpa only [Real.norm_eq_abs] using hsum t)).2
    linarith
  have hlower : I - ε/3 ≤ lowerSum f α P hf := by
    apply hl.2
    rintro _ ⟨t, rfl⟩
    have ht := (abs_lt.mp (show |Stieltjes.taggedSum P t f α - I| < ε/3 by
      simpa only [Real.norm_eq_abs] using hsum t)).1
    linarith
  exact ⟨P, by linarith⟩

theorem integrability_criterion :
    Specs.SingleVariableAnalysis.Ch15.RsDarboux.integrabilityCriterion := by
  intro a b hab f α hf hα
  constructor
  · rintro ⟨I, hI⟩
    exact (epsilon_criterion a b hab f α hf hα).mpr (epsilon_of_integral hab f α hf hα hI)
  · intro heq
    exact ⟨_, integral_of_equal hab f α hf hα heq⟩

theorem integral_value : Specs.SingleVariableAnalysis.Ch15.RsDarboux.integralValue := by
  intro a b hab f α hf hα I
  constructor
  · intro hI
    have heq := (integrability_criterion a b hab f α hf hα).mp ⟨I, hI⟩
    exact ⟨heq, integral_unique a b f α I _ hI (integral_of_equal hab f α hf hα heq)⟩
  · rintro ⟨heq, rfl⟩
    exact integral_of_equal hab f α hf hα heq

end Darboux
end SingleVariableAnalysis.Stieltjes
