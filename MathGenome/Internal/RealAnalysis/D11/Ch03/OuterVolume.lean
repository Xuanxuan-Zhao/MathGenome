import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.OuterVolume
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace D11.Ch03.OuterVolume

noncomputable def outerVolume (d : ℕ) [NeZero d] : OuterMeasure (Point d) :=
  OuterMeasure.ofFunction boxCost (boxCost_empty d)

theorem volume_openBox {d : ℕ} (a b : Fin d → ℝ) :
    volume (openBox a b) = boxContent a b := by
  have hs : openBox a b =
      WithLp.ofLp ⁻¹' (Set.pi Set.univ fun j => Set.Ioo (a j) (b j)) := by
    ext x
    simp [openBox]
  rw [hs, (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    (MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)).nullMeasurableSet]
  exact Real.volume_pi_Ioo

theorem volume_closedBox {d : ℕ} (a b : Fin d → ℝ) :
    volume (closedBox a b) = boxContent a b := by
  have hs : closedBox a b =
      WithLp.ofLp ⁻¹' (Set.pi Set.univ fun j => Set.Icc (a j) (b j)) := by
    ext x
    simp only [closedBox, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_pi,
      Set.mem_univ, forall_const, Set.mem_Icc]
  rw [hs, (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    (MeasurableSet.univ_pi (fun _ => measurableSet_Icc)).nullMeasurableSet]
  simpa only [Set.pi_univ_Icc, boxContent] using (Real.volume_Icc_pi (a := a) (b := b))

theorem volume_le_boxCost {d : ℕ} (s : Set (Point d)) : volume s ≤ boxCost s := by
  refine le_iInf fun a => le_iInf fun b => le_iInf fun hs => ?_
  rw [hs, volume_openBox]

theorem boxCost_openBox {d : ℕ} (a b : Fin d → ℝ) :
    boxCost (openBox a b) = boxContent a b := by
  apply le_antisymm
  · exact iInf_le_of_le a (iInf_le_of_le b (iInf_le _ rfl))
  · rw [← volume_openBox]
    exact volume_le_boxCost _

theorem volume_le_outerVolume (d : ℕ) [NeZero d] (s : Set (Point d)) :
    volume s ≤ outerVolume d s := by
  exact (OuterMeasure.le_ofFunction.mpr volume_le_boxCost) s

theorem outerVolume_axioms : Specs.D11.Ch03.OuterVolume.outerVolume_axioms := by
  intro d _
  exact ⟨measure_empty, fun _ _ h => measure_mono h, fun E => measure_iUnion_le E⟩

theorem covering_formula : Specs.D11.Ch03.OuterVolume.covering_formula := by
  intro d _ E
  change outerVolume d E = _
  unfold outerVolume
  rw [OuterMeasure.ofFunction_eq_iInf_mem _ _
    (P := fun s => ∃ a b : Fin d → ℝ, s = openBox a b) (fun s hs => ?_)]
  · apply le_antisymm
    · refine le_iInf fun a => le_iInf fun b => le_iInf fun hE => ?_
      refine iInf_le_of_le (fun n => openBox (a n) (b n))
        (iInf_le_of_le (fun n => ⟨a n, b n, rfl⟩) (iInf_le_of_le hE ?_))
      simp_rw [boxCost_openBox]
      exact le_rfl
    · refine le_iInf fun F => le_iInf fun hF => le_iInf fun hE => ?_
      choose a b hab using hF
      refine iInf_le_of_le a (iInf_le_of_le b (iInf_le_of_le ?_ ?_))
      · simpa only [hab] using hE
      · simp_rw [hab, boxCost_openBox]
        exact le_rfl
  · apply iInf_eq_top.mpr
    intro a
    apply iInf_eq_top.mpr
    intro b
    apply iInf_eq_top.mpr
    intro hab
    exact (hs ⟨a, b, hab⟩).elim

theorem openBox_min_left {d : ℕ} (a b : Fin d → ℝ) :
    openBox (fun j => min (a j) (b j)) b = openBox a b := by
  ext x
  constructor
  · intro hx j
    refine ⟨?_, (hx j).2⟩
    rcases min_lt_iff.mp (hx j).1 with h | h
    · exact h
    · exact ((lt_trans h (hx j).2).false).elim
  · intro hx j
    exact ⟨lt_of_le_of_lt (min_le_left _ _) (hx j).1, (hx j).2⟩

theorem ordered_covering_formula :
    Specs.D11.Ch03.OuterVolume.ordered_covering_formula := by
  intro d _ E
  rw [covering_formula]
  apply le_antisymm
  · refine le_iInf fun a => le_iInf fun b => le_iInf fun hab => le_iInf fun hE => ?_
    refine iInf_le_of_le a (iInf_le_of_le b (iInf_le_of_le hE ?_))
    exact ENNReal.tsum_le_tsum fun n => le_of_eq
      (ENNReal.ofReal_prod_of_nonneg (fun j _ => sub_nonneg.mpr (hab n j))).symm
  · refine le_iInf fun a => le_iInf fun b => le_iInf fun hE => ?_
    refine iInf_le_of_le (fun n j => min (a n j) (b n j))
      (iInf_le_of_le b (iInf_le_of_le (fun n j => min_le_right (a n j) (b n j))
        (iInf_le_of_le ?_ ?_)))
    · simpa only [openBox_min_left] using hE
    · apply ENNReal.tsum_le_tsum
      intro n
      rw [ENNReal.ofReal_prod_of_nonneg (fun j _ => sub_nonneg.mpr (min_le_right _ _))]
      change boxContent (fun j => min (a n j) (b n j)) (b n) ≤ boxContent (a n) (b n)
      rw [← volume_openBox, openBox_min_left, volume_openBox]

theorem outerVolume_openBox_le (d : ℕ) [NeZero d] (a b : Fin d → ℝ) :
    outerVolume d (openBox a b) ≤ boxContent a b := by
  calc
    outerVolume d (openBox a b) ≤ boxCost (openBox a b) := OuterMeasure.ofFunction_le _
    _ = boxContent a b := boxCost_openBox a b

theorem closedBox_volume : Specs.D11.Ch03.OuterVolume.closedBox_volume := by
  intro d _ a b
  change outerVolume d (closedBox a b) = boxContent a b
  apply le_antisymm
  · have hlim : Tendsto
        (fun t : ℝ => boxContent (fun j => a j - t) (fun j => b j + t))
        (𝓝[>] 0) (𝓝 (boxContent a b)) := by
      unfold boxContent
      apply ENNReal.tendsto_finsetProd_of_ne_top
      · intro j _
        have h : Tendsto (fun t : ℝ => (b j + t) - (a j - t))
            (𝓝[>] 0) (𝓝 (b j - a j)) := by
          have hc : Continuous (fun t : ℝ => (b j + t) - (a j - t)) :=
            (continuous_const.add continuous_id).sub (continuous_const.sub continuous_id)
          have h0 : Tendsto (fun t : ℝ => (b j + t) - (a j - t))
              (𝓝 (0 : ℝ)) (𝓝 (b j - a j)) := by
            simpa only [add_zero, sub_zero] using hc.tendsto 0
          exact h0.mono_left inf_le_left
        exact ENNReal.tendsto_ofReal h
      · intro j _
        exact ENNReal.ofReal_ne_top
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with t ht
    refine (measure_mono (show closedBox a b ⊆
      openBox (fun j => a j - t) (fun j => b j + t) from ?_)).trans
      (outerVolume_openBox_le d _ _)
    intro x hx j
    exact ⟨lt_of_lt_of_le (sub_lt_self _ ht) (hx j).1,
      lt_of_le_of_lt (hx j).2 (lt_add_of_pos_right _ ht)⟩
  · rw [← volume_closedBox]
    exact volume_le_outerVolume d _

theorem endpointBox_volume : Specs.D11.Ch03.OuterVolume.endpointBox_volume := by
  intro d _ a b lower upper
  change outerVolume d (endpointBox a b lower upper) = boxContent a b
  have hinner : openBox a b ⊆ endpointBox a b lower upper := by
    intro x hx j
    constructor
    · cases lower j <;> simp only [Bool.false_eq_true, ite_false, ite_true]
      · exact (hx j).1
      · exact (hx j).1.le
    · cases upper j <;> simp only [Bool.false_eq_true, ite_false, ite_true]
      · exact (hx j).2
      · exact (hx j).2.le
  have houter : endpointBox a b lower upper ⊆ closedBox a b := by
    intro x hx j
    constructor
    · have h := (hx j).1
      cases heq : lower j <;> simp only [heq, Bool.false_eq_true, ite_false, ite_true] at h
      · exact h.le
      · exact h
    · have h := (hx j).2
      cases heq : upper j <;> simp only [heq, Bool.false_eq_true, ite_false, ite_true] at h
      · exact h.le
      · exact h
  apply le_antisymm
  · exact (measure_mono houter).trans_eq (closedBox_volume d a b)
  · calc
      boxContent a b = volume (openBox a b) := (volume_openBox a b).symm
      _ ≤ outerVolume d (openBox a b) := volume_le_outerVolume d _
      _ ≤ outerVolume d (endpointBox a b lower upper) := measure_mono hinner

theorem side_length_product : Specs.D11.Ch03.OuterVolume.side_length_product := by
  intro d _ a b hab lower upper
  rw [endpointBox_volume]
  exact (ENNReal.ofReal_prod_of_nonneg (fun j _ => sub_nonneg.mpr (hab j))).symm

theorem degenerate_box : Specs.D11.Ch03.OuterVolume.degenerate_box := by
  intro d _ a b lower upper h
  rw [endpointBox_volume]
  obtain ⟨j, hj⟩ := h
  exact Finset.prod_eq_zero (Finset.mem_univ j) (ENNReal.ofReal_eq_zero.mpr (sub_nonpos.mpr hj))

end D11.Ch03.OuterVolume
