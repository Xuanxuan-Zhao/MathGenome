import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.FiniteChanges
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Linearity

namespace SingleVariableAnalysis.Riemann
open scoped BigOperators Classical

/-- Half-open cells of a strict partition are disjoint. -/
theorem halfOpen_cell_unique {a b x : ℝ} (P : Partition a b)
    (i j : Fin P.n)
    (hi : P.point i.castSucc < x ∧ x ≤ P.point i.succ)
    (hj : P.point j.castSucc < x ∧ x ≤ P.point j.succ) : i = j := by
  apply Fin.ext
  by_contra h
  rcases lt_or_gt_of_ne h with h | h
  · have hle := P.strictMono.monotone
      (show i.succ ≤ j.castSucc from Nat.succ_le_of_lt h)
    linarith [hi.2, hj.1]
  · have hle := P.strictMono.monotone
      (show j.succ ≤ i.castSucc from Nat.succ_le_of_lt h)
    linarith [hj.2, hi.1]

/-- A fixed point charges at most two closed cells, even at an endpoint. -/
theorem sum_touching_point_le {a b : ℝ} (P : Partition a b) (x C : ℝ)
    (hC : 0 ≤ C) :
    (∑ i : Fin P.n, if x ∈ cell P i then C * cellLength P i else 0) ≤
      2 * C * mesh P := by
  classical
  have hleft :
      (∑ i : Fin P.n, if x = P.point i.castSucc then C * cellLength P i else 0) ≤
        C * mesh P := by
    by_cases hx : ∃ i : Fin P.n, x = P.point i.castSucc
    · obtain ⟨i, hi⟩ := hx
      rw [Finset.sum_eq_single i]
      · rw [ite_eq_left hi]
        exact mul_le_mul_of_nonneg_left (cellLength_le_mesh P i) hC
      · intro j _ hji
        apply ite_eq_right
        intro hj
        exact hji (Fin.castSucc_injective _ (P.strictMono.injective (hj.symm.trans hi)))
      · simp
    · have hz : ∀ i : Fin P.n, x ≠ P.point i.castSucc := fun i hi => hx ⟨i, hi⟩
      simp only [ite_eq_right (hz _), Finset.sum_const_zero]
      exact mul_nonneg hC (mesh_nonneg P)
  have hright :
      (∑ i : Fin P.n, if P.point i.castSucc < x ∧ x ≤ P.point i.succ
        then C * cellLength P i else 0) ≤ C * mesh P := by
    by_cases hx : ∃ i : Fin P.n, P.point i.castSucc < x ∧ x ≤ P.point i.succ
    · obtain ⟨i, hi⟩ := hx
      rw [Finset.sum_eq_single i]
      · rw [ite_eq_left hi]
        exact mul_le_mul_of_nonneg_left (cellLength_le_mesh P i) hC
      · intro j _ hji
        exact ite_eq_right (fun hj => hji (halfOpen_cell_unique P j i hj hi))
      · simp
    · have hz : ∀ i : Fin P.n, ¬ (P.point i.castSucc < x ∧ x ≤ P.point i.succ) :=
        fun i hi => hx ⟨i, hi⟩
      simp only [ite_eq_right (hz _), Finset.sum_const_zero]
      exact mul_nonneg hC (mesh_nonneg P)
  have hsplit (i : Fin P.n) :
      (if x ∈ cell P i then C * cellLength P i else 0) =
        (if x = P.point i.castSucc then C * cellLength P i else 0) +
        (if P.point i.castSucc < x ∧ x ≤ P.point i.succ
          then C * cellLength P i else 0) := by
    have hp := P.strictMono (Fin.castSucc_lt_succ (i := i))
    simp only [cell, D.cellValue, Set.mem_Icc]
    by_cases he : x = P.point i.castSucc
    · subst x
      simp only [le_refl, hp.le, and_self, ite_true, lt_self_iff_false, false_and,
        ite_false, add_zero]
    · by_cases hx : P.point i.castSucc < x ∧ x ≤ P.point i.succ
      · rw [ite_eq_left ⟨hx.1.le, hx.2⟩, ite_eq_right he, ite_eq_left hx, zero_add]
      · have hout : ¬ (P.point i.castSucc ≤ x ∧ x ≤ P.point i.succ) :=
          fun h => hx ⟨lt_of_le_of_ne h.1 (Ne.symm he), h.2⟩
        rw [ite_eq_right hout, ite_eq_right he, ite_eq_right hx, add_zero]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  linarith

/-- Sum the charges over a finite exceptional set. -/
theorem sum_finite_cell_charges_le {a b : ℝ} (P : Partition a b)
    (s : Finset ℝ) (C : ℝ) (hC : 0 ≤ C) :
    (∑ i : Fin P.n, (∑ x ∈ s, if x ∈ cell P i then C else 0) * cellLength P i) ≤
      2 * C * (s.card : ℝ) * mesh P := by
  classical
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _x ∈ s, 2 * C * mesh P :=
      Finset.sum_le_sum fun x _ => sum_touching_point_le P x C hC
    _ = _ := by simp; ring

/-- Finite-support contributions obey the manuscript's explicit 2MN estimate. -/
theorem finite_support_tagged_bound :
    Specs.SingleVariableAnalysis.Ch08.FiniteChanges.finiteSupportTaggedBound := by
  intro E _ _ h a b s M hM hbound hs P ξ
  classical
  have hcharge (i : Fin P.n) :
      ‖h (ξ i)‖ ≤ ∑ x ∈ s, if x ∈ cell P i then M else 0 := by
    have hnonneg : ∀ x ∈ s, 0 ≤ (if x ∈ cell P i then M else 0) :=
      fun x _ => by split_ifs <;> positivity
    by_cases hx : (ξ i : ℝ) ∈ s
    · have ht := Finset.single_le_sum hnonneg hx
      rw [ite_eq_left (show (ξ i : ℝ) ∈ cell P i from (ξ i).property)] at ht
      exact (hbound _ (cell_subset_interval P i (ξ i).property)).trans ht
    · rw [hs _ (cell_subset_interval P i (ξ i).property) hx, norm_zero]
      exact Finset.sum_nonneg hnonneg
  calc
    ‖taggedSum P ξ h‖ ≤ ∑ i : Fin P.n, ‖cellLength P i • h (ξ i)‖ :=
      norm_sum_le _ _
    _ = ∑ i : Fin P.n, ‖h (ξ i)‖ * cellLength P i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (cell_positive P i), mul_comm]
    _ ≤ ∑ i : Fin P.n, (∑ x ∈ s, if x ∈ cell P i then M else 0) * cellLength P i :=
      Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (hcharge i) (cell_positive P i).le
    _ ≤ _ := sum_finite_cell_charges_le P s M hM

/-- Finite support also bounds the real Darboux gap with the stated constant. -/
theorem finite_support_darboux_bound :
    Specs.SingleVariableAnalysis.Ch08.FiniteChanges.finiteSupportDarbouxBound := by
  intro h a b s M hM hbound hs P hh
  classical
  let c (i : Fin P.n) : ℝ := ∑ x ∈ s, if x ∈ cell P i then M else 0
  have hc (i : Fin P.n) : 0 ≤ c i :=
    Finset.sum_nonneg fun x _ => by split_ifs <;> positivity
  have hpoint (i : Fin P.n) (x : ℝ) (hx : x ∈ cell P i) : |h x| ≤ c i := by
    by_cases hxs : x ∈ s
    · have ht := Finset.single_le_sum (s := s)
        (f := fun y => if y ∈ cell P i then M else 0)
        (fun y _ => by split_ifs <;> positivity) hxs
      rw [ite_eq_left hx] at ht
      exact (hbound x (cell_subset_interval P i hx)).trans ht
    · rw [hs x (cell_subset_interval P i hx) hxs, abs_zero]
      exact hc i
  have hcoeff (i : Fin P.n) :
      cellSupremum h P hh i - cellInfimum h P hh i ≤
        ∑ x ∈ s, if x ∈ cell P i then 2 * M else 0 := by
    have hu : cellSupremum h P hh i ≤ c i := by
      apply csSup_le ((cell_nonempty P i).image h)
      rintro _ ⟨x, hx, rfl⟩
      exact (le_abs_self _).trans (hpoint i x hx)
    have hl : -c i ≤ cellInfimum h P hh i := by
      apply le_csInf ((cell_nonempty P i).image h)
      rintro _ ⟨x, hx, rfl⟩
      exact (abs_le.mp (hpoint i x hx)).1
    have he : (∑ x ∈ s, if x ∈ cell P i then 2 * M else 0) = 2 * c i := by
      simp only [c, Finset.mul_sum, mul_ite, mul_zero]
    rw [he]
    linarith
  calc
    upperSum h P hh - lowerSum h P hh =
        ∑ i : Fin P.n, (cellSupremum h P hh i - cellInfimum h P hh i) *
          cellLength P i := by
      simp only [sub_mul, Finset.sum_sub_distrib]
      rfl
    _ ≤ ∑ i : Fin P.n, (∑ x ∈ s, if x ∈ cell P i then 2 * M else 0) *
        cellLength P i := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hcoeff i) (cell_positive P i).le
    _ ≤ 2 * (2 * M) * (s.card : ℝ) * mesh P :=
      sum_finite_cell_charges_le P s (2 * M) (by positivity)
    _ = _ := by ring

/-- Finite support forces every tagged sum to tend to zero. -/
theorem fineTaggedLimit_finiteSupport {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (h : ℝ → E) {a b : ℝ}
    (hb : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, ‖h x‖ ≤ M)
    (hs : {x | x ∈ Set.Icc a b ∧ h x ≠ 0}.Finite) :
    FineTaggedLimit h a b 0 := by
  classical
  obtain ⟨M, hM⟩ := hb
  let s := hs.toFinset
  let C : ℝ := 2 * max M 0 * (s.card : ℝ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hs' : ∀ x ∈ Set.Icc a b, x ∉ s → h x = 0 := by
    intro x hx hxs
    by_contra hn
    exact hxs (hs.mem_toFinset.mpr ⟨hx, hn⟩)
  intro ε hε
  refine ⟨ε / (C + 1), by positivity, fun P ξ hP => ?_⟩
  have ht := finite_support_tagged_bound h s (max M 0) (le_max_right _ _)
    (fun x hx => (hM x hx).trans (le_max_left _ _)) hs' P ξ
  rw [sub_zero]
  calc
    ‖taggedSum P ξ h‖ ≤ C * mesh P := ht
    _ ≤ (C + 1) * mesh P :=
      mul_le_mul_of_nonneg_right (by linarith) (mesh_nonneg P)
    _ < (C + 1) * (ε / (C + 1)) := mul_lt_mul_of_pos_left hP (by positivity)
    _ = ε := by field_simp

/-- A bounded error supported on finitely many points preserves a tagged limit. -/
theorem FineTaggedLimit.congr_finite {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f g : ℝ → E} {a b : ℝ} {I : E}
    (hf : FineTaggedLimit f a b I)
    (hs : {x | x ∈ Set.Icc a b ∧ f x ≠ g x}.Finite)
    (hb : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, ‖g x - f x‖ ≤ M) :
    FineTaggedLimit g a b I := by
  have hfinite : {x | x ∈ Set.Icc a b ∧ g x - f x ≠ 0}.Finite := by
    apply hs.subset
    intro x hx
    exact ⟨hx.1, fun he => hx.2 (sub_eq_zero.mpr he.symm)⟩
  have hd := fineTaggedLimit_finiteSupport (fun x => g x - f x) hb hfinite
  simpa only [sub_add_cancel, zero_add] using hd.add hf

theorem real_finite_support :
    Specs.SingleVariableAnalysis.Ch08.FiniteChanges.realFiniteSupport := by
  intro h a b hab hb hs
  apply (real_tagged_equivalence h hab hb 0).mpr
  obtain ⟨M, hM⟩ := BoundedOnInterval.abs_bound hb
  exact fineTaggedLimit_finiteSupport h ⟨M, by simpa only [Real.norm_eq_abs] using hM⟩ hs

theorem complex_finite_support :
    Specs.SingleVariableAnalysis.Ch08.FiniteChanges.complexFiniteSupport := by
  intro h a b hab hb hs
  exact (complex_tagged_equivalence h hab hb 0).mpr (fineTaggedLimit_finiteSupport h hb hs)

theorem real_finite_changes :
    Specs.SingleVariableAnalysis.Ch08.FiniteChanges.realFiniteChanges := by
  intro f g a b hbF hbG hs hf
  apply (real_tagged_equivalence g (RealIntegrable.ordered hf) hbG (realIntegral f hf)).mpr
  have hlim := (real_tagged_equivalence f (RealIntegrable.ordered hf) hbF _).mp ⟨hf, rfl⟩
  obtain ⟨M, hM⟩ := BoundedOnInterval.abs_bound hbF
  obtain ⟨N, hN⟩ := BoundedOnInterval.abs_bound hbG
  apply hlim.congr_finite hs
  refine ⟨N + M, fun x hx => ?_⟩
  simpa only [Real.norm_eq_abs] using (norm_sub_le (g x) (f x)).trans
    (by simpa only [Real.norm_eq_abs] using add_le_add (hN x hx) (hM x hx))

theorem complex_finite_changes :
    Specs.SingleVariableAnalysis.Ch08.FiniteChanges.complexFiniteChanges := by
  intro f g a b hbF hbG hs hf
  apply (complex_tagged_equivalence g (RealIntegrable.ordered hf.1) hbG (complexIntegral f hf)).mpr
  have hlim := (complex_tagged_equivalence f (RealIntegrable.ordered hf.1) hbF _).mp ⟨hf, rfl⟩
  obtain ⟨M, hM⟩ := hbF
  obtain ⟨N, hN⟩ := hbG
  exact hlim.congr_finite hs ⟨N + M, fun x hx =>
    (norm_sub_le (g x) (f x)).trans (add_le_add (hN x hx) (hM x hx))⟩

end SingleVariableAnalysis.Riemann
