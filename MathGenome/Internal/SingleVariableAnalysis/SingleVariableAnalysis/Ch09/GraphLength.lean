import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.GraphLength
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.FtcSecond
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Oriented

namespace SingleVariableAnalysis.Riemann
open Set
open scoped BigOperators

noncomputable abbrev polygonalGraphLength := @Specs.SingleVariableAnalysis.Ch09.GraphLength.polygonalLengthValue
noncomputable abbrev graphLength := Specs.SingleVariableAnalysis.Ch09.GraphLength.graphLengthValue

/-- A continuous real function on a compact interval is Darboux integrable.
This local helper proves existence with the project's proper integral. -/
theorem graph_continuous_integrable {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b)) : RealIntegrable f a b := by
  have hb : BoundedOnInterval f a b := by
    exact ⟨isCompact_Icc.bddBelow_image hc, isCompact_Icc.bddAbove_image hc⟩
  apply (realIntegrable_iff_small_gap f hab hb).mpr
  intro ε hε
  let η := ε / (2 * (b - a + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨δ, hδ, hd⟩ := (Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hc)) η hη
  obtain ⟨P, hP⟩ := exists_fine_partition hab δ hδ
  have hcell (i : Fin P.n) : cellSupremum f P hb i - cellInfimum f P hb i ≤ η := by
    apply cell_oscillation_le_of_sub_le
    intro x hx y hy
    have hxy : dist x y < δ := by
      rw [Real.dist_eq]
      exact (abs_sub_le_iff.mpr ⟨by dsimp [cellLength, S.lengthValue]; linarith [hx.2, hy.1],
          by dsimp [cellLength, S.lengthValue]; linarith [hy.2, hx.1]⟩ :
        |x-y| ≤ cellLength P i).trans_lt ((cellLength_le_mesh P i).trans_lt hP)
    have hv := hd x (cell_subset_interval P i hx) y (cell_subset_interval P i hy) hxy
    exact (le_abs_self _).trans (le_of_lt (by simpa only [Real.dist_eq] using hv))
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    mul_le_mul_of_nonneg_right (hcell i) (cell_positive P i).le
  rw [sum_cell_oscillation] at hs
  simp only [← Finset.mul_sum, sum_cellLength] at hs
  refine ⟨P, hs.trans_lt ?_⟩
  have he : η * (2 * (b-a+1)) = ε := by
    dsimp [η]; exact div_mul_cancel₀ _ (by positivity)
  nlinarith [mul_nonneg hη.le (sub_nonneg.mpr hab)]


private def graphPath (f : ℝ → ℝ) (x : ℝ) : ℂ := (x : ℂ) + (f x : ℂ) * Complex.I
private def graphVelocity (g : ℝ → ℝ) (x : ℝ) : ℂ := 1 + (g x : ℂ) * Complex.I

private theorem graphVelocity_norm (g : ℝ → ℝ) (x : ℝ) :
    ‖graphVelocity g x‖ = Real.sqrt (1 + (g x)^2) := by
  simp [Complex.norm_eq_sqrt_sq_add_sq, graphVelocity]

private theorem graphPath_chord (f : ℝ → ℝ) (x y : ℝ) :
    ‖graphPath f y - graphPath f x‖ = Real.sqrt ((y-x)^2 + (f y-f x)^2) := by
  simp [Complex.norm_eq_sqrt_sq_add_sq, graphPath]

theorem graph_point_mem {a b : ℝ} (P : Partition a b) (j : Fin (P.n+1)) :
    P.point j ∈ Icc a b :=
  ⟨by simpa only [P.first] using P.strictMono.monotone (Fin.zero_le j),
   by simpa only [P.last] using P.strictMono.monotone (Fin.le_last j)⟩

/-- Additivity over every finite strict partition, including a zero-cell one. -/
theorem graph_sum_cell_integrals {v : ℝ → ℝ} {a b : ℝ}
    (hv : RealIntegrable v a b) (P : Partition a b) :
    (∑ i : Fin P.n, realIntegral v
      (hv.subinterval (graph_point_mem P i.castSucc).1
        (P.strictMono.monotone (Fin.castSucc_le_succ i))
        (graph_point_mem P i.succ).2)) = realIntegral v hv := by
  let H (j : Fin (P.n+1)) := realIntegral v
    (hv.subinterval le_rfl (graph_point_mem P j).1 (graph_point_mem P j).2)
  have he (i : Fin P.n) : realIntegral v
      (hv.subinterval (graph_point_mem P i.castSucc).1
        (P.strictMono.monotone (Fin.castSucc_le_succ i))
        (graph_point_mem P i.succ).2) = H i.succ - H i.castSucc := by
    have hs := (real_split v (graph_point_mem P i.castSucc).1
      (P.strictMono.monotone (Fin.castSucc_le_succ i))
      (hv.bounded.mono (Icc_subset_Icc le_rfl (graph_point_mem P i.succ).2))).2
        (hv.subinterval le_rfl (graph_point_mem P i.succ).1 (graph_point_mem P i.succ).2)
        (hv.subinterval le_rfl (graph_point_mem P i.castSucc).1 (graph_point_mem P i.castSucc).2)
        (hv.subinterval (graph_point_mem P i.castSucc).1
          (P.strictMono.monotone (Fin.castSucc_le_succ i)) (graph_point_mem P i.succ).2)
    dsimp [H]
    linarith
  simp_rw [he]
  rw [sum_cell_differences]
  dsimp [H]
  simp only [P.first, P.last, realIntegral_degenerate, sub_zero]

/-- The real mean value theorem makes each chord exactly a tagged speed term. -/
theorem graph_exists_length_tagging {f g : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x) (P : Partition a b) :
    ∃ ξ : Tagging P, polygonalGraphLength f P =
      taggedSum P ξ (fun x => Real.sqrt (1 + (g x)^2)) := by
  have hex (i : Fin P.n) : ∃ c ∈ Ioo (P.point i.castSucc) (P.point i.succ),
      f (P.point i.succ) - f (P.point i.castSucc) = g c * cellLength P i := by
    have hsub := cell_subset_interval P i
    have hint (x : ℝ) (hx : x ∈ Ioo (P.point i.castSucc) (P.point i.succ)) :
        x ∈ Ioo a b := by
      have hl := hsub (left_mem_Icc.mpr (P.strictMono.monotone (Fin.castSucc_le_succ i)))
      have hr := hsub (right_mem_Icc.mpr (P.strictMono.monotone (Fin.castSucc_le_succ i)))
      exact ⟨hl.1.trans_lt hx.1, hx.2.trans_le hr.2⟩
    obtain ⟨c, hci, he⟩ := SingleVariableAnalysis.lagrange_deriv f
      (P.point i.castSucc) (P.point i.succ)
      (P.strictMono (Fin.castSucc_lt_succ (i := i)))
      (hc.mono hsub) (fun x hx => (hd x (hint x hx)).differentiableAt)
    exact ⟨c, hci, by simpa only [(hd c (hint c hci)).deriv, cellLength, S.lengthValue] using he⟩
  choose c hc' he using hex
  let ξ : Tagging P := fun i => ⟨c i, (hc' i).1.le, (hc' i).2.le⟩
  refine ⟨ξ, Finset.sum_congr rfl ?_⟩
  intro i _
  change Real.sqrt (cellLength P i ^ 2 +
    (f (P.point i.succ) - f (P.point i.castSucc))^2) =
    cellLength P i * Real.sqrt (1 + (g (c i))^2)
  rw [he i, show cellLength P i ^ 2 + (g (c i) * cellLength P i)^2 =
    cellLength P i ^ 2 * (1 + (g (c i))^2) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (cell_positive P i).le]


/-- The fundamental theorem and the complex integral norm bound control a chord. -/
private theorem graph_chord_le_integral {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x)
    (hs : RealIntegrable (fun x => Real.sqrt (1 + (g x)^2)) a b) :
    Real.sqrt ((b-a)^2 + (f b-f a)^2) ≤ realIntegral _ hs := by
  have hpath : ContinuousOn (graphPath f) (Icc a b) :=
    (Complex.continuous_ofReal.comp_continuousOn continuous_id.continuousOn).add
      ((Complex.continuous_ofReal.comp_continuousOn hc).mul continuous_const.continuousOn)
  have hder (x : ℝ) (hx : x ∈ Ioo a b) :
      HasDerivAt (graphPath f) (graphVelocity g x) x := by
    apply (SingleVariableAnalysis.complex_hasDerivAt_iff_components _ _ _).mpr
    constructor
    · simpa [graphPath, graphVelocity] using hasDerivAt_id' x
    · simpa [graphPath, graphVelocity] using hd x hx
  have hv : ComplexIntegrable (graphVelocity g) a b := by
    constructor
    · simpa [graphVelocity] using graph_continuous_integrable hab
        (continuous_const.continuousOn : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Icc a b))
    · simpa [graphVelocity] using graph_continuous_integrable hab hg
  have he := complex_ftc_second (graphPath f) (graphVelocity g) a b hab hpath hder hv
  obtain ⟨hn, hnorm, _⟩ := complex_norm_estimate (graphVelocity g) hv
  rw [he, graphPath_chord] at hnorm
  simpa only [graphVelocity_norm] using hnorm

theorem graph_length_formula : Specs.SingleVariableAnalysis.Ch09.GraphLength.graphLengthFormula := by
  intro f g a b hab hc hg hd
  have hspeed : ContinuousOn (fun x => Real.sqrt (1 + (g x)^2)) (Icc a b) :=
    Real.continuous_sqrt.comp_continuousOn (continuous_const.continuousOn.add (hg.pow 2))
  let hs := graph_continuous_integrable hab hspeed
  have hup (P : Partition a b) : polygonalGraphLength f P ≤ realIntegral _ hs := by
    calc
      polygonalGraphLength f P ≤ ∑ i : Fin P.n, realIntegral _
          (hs.subinterval (graph_point_mem P i.castSucc).1
            (P.strictMono.monotone (Fin.castSucc_le_succ i))
            (graph_point_mem P i.succ).2) := by
        apply Finset.sum_le_sum
        intro i _
        apply graph_chord_le_integral (P.strictMono.monotone (Fin.castSucc_le_succ i))
          (hc.mono (cell_subset_interval P i)) (hg.mono (cell_subset_interval P i))
        intro x hx
        exact hd x ⟨(graph_point_mem P i.castSucc).1.trans_lt hx.1,
          hx.2.trans_le (graph_point_mem P i.succ).2⟩
      _ = realIntegral _ hs := graph_sum_cell_integrals hs P
  have hbdd : BddAbove (range (fun P : Partition a b => polygonalGraphLength f P)) :=
    ⟨realIntegral _ hs, by rintro _ ⟨P, rfl⟩; exact hup P⟩
  have hlu : IsLUB (range (fun P : Partition a b => polygonalGraphLength f P))
      (realIntegral _ hs) := by
    refine ⟨by rintro _ ⟨P, rfl⟩; exact hup P, ?_⟩
    intro B hB
    by_contra hn
    have hpos : 0 < realIntegral _ hs - B := sub_pos.mpr (lt_of_not_ge hn)
    have hl := (real_tagged_equivalence _ hab hs.bounded (realIntegral _ hs)).mp ⟨hs, rfl⟩
    obtain ⟨δ, hδ, hclose⟩ := hl _ hpos
    obtain ⟨P, hP⟩ := exists_fine_partition hab δ hδ
    obtain ⟨ξ, he⟩ := graph_exists_length_tagging hc hd P
    have heps := hclose P ξ hP
    change ‖taggedSum P ξ (fun x => Real.sqrt (1 + (g x)^2)) - realIntegral _ hs‖ < _ at heps
    rw [← he, Real.norm_eq_abs] at heps
    have hle := hB (mem_range_self P)
    linarith [(abs_lt.mp heps).1]
  refine ⟨hs, hbdd, hlu, ?_⟩
  exact hlu.csSup_eq (by obtain ⟨P⟩ := partition_exists hab; exact ⟨_, mem_range_self P⟩)

theorem graph_length_degenerate :
    Specs.SingleVariableAnalysis.Ch09.GraphLength.graphLengthDegenerate := by
  intro f a
  have hz (P : Partition a a) : polygonalGraphLength f P = 0 := by
    have hn := n_eq_zero_of_degenerate a P
    apply Finset.sum_eq_zero
    intro i _
    exact False.elim (by have hi := i.isLt; omega)
  refine ⟨?_, hz⟩
  change sSup (range (fun P : Partition a a => polygonalGraphLength f P)) = 0
  have he : range (fun P : Partition a a => polygonalGraphLength f P) = {0} := by
    ext x
    constructor
    · rintro ⟨P, rfl⟩; exact hz P
    · intro hx
      refine ⟨emptyPartition a, ?_⟩
      exact (hz _).trans (mem_singleton_iff.mp hx).symm
  rw [he, csSup_singleton]

end SingleVariableAnalysis.Riemann
