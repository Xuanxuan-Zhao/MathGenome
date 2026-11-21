import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.TaggedForward
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Criterion

namespace SingleVariableAnalysis.Riemann
open scoped BigOperators

/-- No endpoint of a strict partition lies strictly inside one of its cells. -/
theorem point_not_inside_cell {a b : ℝ} (Q : Partition a b)
    (i : Fin Q.n) (k : Fin (Q.n + 1)) :
    ¬ (Q.point i.castSucc < Q.point k ∧ Q.point k < Q.point i.succ) := by
  intro h
  have h₁ := Q.strictMono.lt_iff_lt.mp h.1
  have h₂ := Q.strictMono.lt_iff_lt.mp h.2
  have : i.val < k.val := h₁
  have : k.val < i.val + 1 := h₂
  omega

/-- A point can lie in the interiors of at most one cell. -/
theorem interior_cell_unique {a b x : ℝ} (Q : Partition a b)
    (i j : Fin Q.n)
    (hi : Q.point i.castSucc < x ∧ x < Q.point i.succ)
    (hj : Q.point j.castSucc < x ∧ x < Q.point j.succ) : i = j := by
  apply Fin.ext
  by_contra h
  rcases lt_or_gt_of_ne h with h | h
  · have hle := Q.strictMono.monotone
      (show i.succ ≤ j.castSucc from Nat.succ_le_of_lt h)
    linarith [hi.2, hj.1]
  · have hle := Q.strictMono.monotone
      (show j.succ ≤ i.castSucc from Nat.succ_le_of_lt h)
    linarith [hj.2, hi.1]

/-- Inserting endpoints leaves any cell without an inserted interior point intact. -/
theorem cell_eq_of_no_inserted_interior {a b : ℝ} (P Q R : Partition a b)
    (hpoints : points R = points P ∪ points Q)
    (i : Fin Q.n) (j : Fin R.n) (hsub : cell R j ⊆ cell Q i)
    (hgood : ¬ ∃ k : Fin (P.n + 1),
      Q.point i.castSucc < P.point k ∧ P.point k < Q.point i.succ) :
    cell R j = cell Q i := by
  have hnone (x : ℝ) (hx : x ∈ points R) :
      ¬ (Q.point i.castSucc < x ∧ x < Q.point i.succ) := by
    rw [hpoints] at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
      exact fun hk => hgood ⟨k, hk⟩
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
      exact point_not_inside_cell Q i k
  have hlt := R.strictMono (Fin.castSucc_lt_succ (i := j))
  have hl := hsub (show R.point j.castSucc ∈ cell R j from ⟨le_rfl, hlt.le⟩)
  have hr := hsub (show R.point j.succ ∈ cell R j from ⟨hlt.le, le_rfl⟩)
  have hnl := hnone (R.point j.castSucc)
    (Finset.mem_image.mpr ⟨j.castSucc, Finset.mem_univ _, rfl⟩)
  have hnr := hnone (R.point j.succ)
    (Finset.mem_image.mpr ⟨j.succ, Finset.mem_univ _, rfl⟩)
  have hel : R.point j.castSucc = Q.point i.castSucc := by
    by_contra hne
    exact hnl ⟨lt_of_le_of_ne hl.1 (Ne.symm hne), hlt.trans_le hr.2⟩
  have her : R.point j.succ = Q.point i.succ := by
    by_contra hne
    exact hnr ⟨hl.1.trans_lt hlt, lt_of_le_of_ne hr.2 hne⟩
  change Set.Icc _ _ = Set.Icc _ _
  rw [hel, her]

/-- The total length charged to a fixed endpoint is at most the mesh:
the interiors of the cells are disjoint. -/
theorem sum_crossing_point_le {a b : ℝ} (Q : Partition a b) (x C : ℝ)
    (hC : 0 ≤ C) :
    (∑ i : Fin Q.n, if Q.point i.castSucc < x ∧ x < Q.point i.succ
      then C * cellLength Q i else 0) ≤ C * mesh Q := by
  classical
  by_cases hx : ∃ i : Fin Q.n, Q.point i.castSucc < x ∧ x < Q.point i.succ
  · obtain ⟨i, hi⟩ := hx
    rw [Finset.sum_eq_single i]
    · simp only [ite_eq_left hi]
      exact mul_le_mul_of_nonneg_left (cellLength_le_mesh Q i) hC
    · intro j _ hji
      have hj : ¬ (Q.point j.castSucc < x ∧ x < Q.point j.succ) :=
        fun hj => hji (interior_cell_unique Q j i hj hi)
      exact ite_eq_right hj
    · simp
  · have hzero : ∀ i : Fin Q.n,
        ¬ (Q.point i.castSucc < x ∧ x < Q.point i.succ) := by
      intro i hi
      exact hx ⟨i, hi⟩
    simp only [ite_eq_right (hzero _), Finset.sum_const_zero]
    exact mul_nonneg hC (mesh_nonneg Q)

/-- A mesh estimate for the Darboux gap of an arbitrary partition.
Only cells containing a comparison endpoint in their interiors incur a charge. -/
theorem darboux_gap_le_gap_add_mesh (f : ℝ → ℝ) {a b : ℝ}
    (hf : BoundedOnInterval f a b) (P Q : Partition a b)
    (lo hi : ℝ) (hlo : ∀ x ∈ Set.Icc a b, lo ≤ f x)
    (hhi : ∀ x ∈ Set.Icc a b, f x ≤ hi) (hbound : lo ≤ hi) :
    upperSum f Q hf - lowerSum f Q hf ≤
      upperSum f P hf - lowerSum f P hf +
        (P.n + 1 : ℕ) * (hi - lo) * mesh Q := by
  classical
  obtain ⟨R, hpoints, hRP, hRQ⟩ := common_refinement P Q
  let o (T : Partition a b) (i : Fin T.n) :=
    cellSupremum f T hf i - cellInfimum f T hf i
  let e (i : Fin Q.n) := ∑ k : Fin (P.n + 1),
    if Q.point i.castSucc < P.point k ∧ P.point k < Q.point i.succ
      then hi - lo else 0
  have ho_nonneg (T : Partition a b) (i : Fin T.n) : 0 ≤ o T i := by
    obtain ⟨x, hx⟩ := cell_nonempty T i
    exact sub_nonneg.mpr ((cellInfimum_le f T hf i hx).trans
      (le_cellSupremum f T hf i hx))
  have ho_le (T : Partition a b) (i : Fin T.n) : o T i ≤ hi - lo := by
    have hu : cellSupremum f T hf i ≤ hi := by
      apply csSup_le ((cell_nonempty T i).image f)
      rintro _ ⟨x, hx, rfl⟩
      exact hhi x (cell_subset_interval T i hx)
    have hl : lo ≤ cellInfimum f T hf i := by
      apply le_csInf ((cell_nonempty T i).image f)
      rintro _ ⟨x, hx, rfl⟩
      exact hlo x (cell_subset_interval T i hx)
    exact sub_le_sub hu hl
  have he_nonneg (i : Fin Q.n) : 0 ≤ e i := by
    exact Finset.sum_nonneg fun k _ => by split_ifs <;> linarith
  have hcoeff (i : Fin Q.n) (j : Fin R.n) (hsub : cell R j ⊆ cell Q i) :
      -o R j ≤ -o Q i + e i := by
    by_cases hbad : ∃ k : Fin (P.n + 1),
        Q.point i.castSucc < P.point k ∧ P.point k < Q.point i.succ
    · obtain ⟨k, hk⟩ := hbad
      have he : hi - lo ≤ e i := by
        have hs := Finset.single_le_sum (s := Finset.univ)
          (f := fun k : Fin (P.n + 1) =>
            if Q.point i.castSucc < P.point k ∧ P.point k < Q.point i.succ
              then hi - lo else 0)
          (fun k _ => by split_ifs <;> linarith) (Finset.mem_univ k)
        simpa only [ite_eq_left hk] using hs
      linarith [ho_nonneg R j, ho_le Q i]
    · have hcell := cell_eq_of_no_inserted_interior P Q R hpoints i j hsub hbad
      have heq : o R j = o Q i := by
        dsimp [o, cellSupremum, cellInfimum, D.cellSupremumValue, D.cellInfimumValue]
        change Specs.SingleVariableAnalysis.Ch08.DarbouxSums.cellValue R j = _ at hcell
        rw [hcell]
      linarith [he_nonneg i]
  have hw := weighted_sum_refinement_le Q R hRQ
    (fun i => -o Q i + e i) (fun j => -o R j) hcoeff
  have ho_sum (T : Partition a b) :
      (∑ i : Fin T.n, o T i * cellLength T i) =
        upperSum f T hf - lowerSum f T hf := by
    simp only [o, sub_mul, Finset.sum_sub_distrib]
    rfl
  have hQR : upperSum f Q hf - lowerSum f Q hf ≤
      upperSum f R hf - lowerSum f R hf + ∑ i : Fin Q.n, e i * cellLength Q i := by
    simp only [add_mul, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      ho_sum] at hw
    linarith
  have he_sum : (∑ i : Fin Q.n, e i * cellLength Q i) ≤
      (P.n + 1 : ℕ) * (hi - lo) * mesh Q := by
    dsimp only [e]
    simp_rw [Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _k : Fin (P.n + 1), (hi - lo) * mesh Q :=
        Finset.sum_le_sum fun k _ => sum_crossing_point_le Q (P.point k) (hi-lo)
          (sub_nonneg.mpr hbound)
      _ = _ := by simp; ring
  have hR_upper := upper_refinement f P R hf hRP
  have hR_lower := lower_refinement f P R hf hRP
  linarith

/-- Darboux integrability implies convergence of all sufficiently fine tagged
sums, including partitions unrelated to the chosen comparison partition. -/
theorem tagged_forward : Specs.SingleVariableAnalysis.Ch08.TaggedForward.taggedForward := by
  intro f a b hab hf hint I hI ε hε
  obtain ⟨lo, hlo⟩ := hf.1
  obtain ⟨hi, hhi⟩ := hf.2
  have hlo' : ∀ x ∈ Set.Icc a b, lo ≤ f x :=
    fun x hx => hlo (Set.mem_image_of_mem f hx)
  have hhi' : ∀ x ∈ Set.Icc a b, f x ≤ hi :=
    fun x hx => hhi (Set.mem_image_of_mem f hx)
  have hbound : lo ≤ hi :=
    (hlo' a ⟨le_rfl, hab.le⟩).trans (hhi' a ⟨le_rfl, hab.le⟩)
  obtain ⟨P, hP⟩ := (darboux_criterion f hab hf).mp hint (ε / 2) (half_pos hε)
  let K : ℝ := (P.n + 1 : ℕ) * (hi - lo)
  have hK : 0 ≤ K := mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hbound)
  have hKpos : 0 < K + 1 := by linarith
  let δ : ℝ := (ε / 2) / (K + 1)
  refine ⟨δ, div_pos (half_pos hε) hKpos, ?_⟩
  intro Q ξ hmesh
  have herror : K * mesh Q < ε / 2 := by
    calc
      K * mesh Q ≤ (K + 1) * mesh Q :=
        mul_le_mul_of_nonneg_right (by linarith) (mesh_nonneg Q)
      _ < (K + 1) * δ := mul_lt_mul_of_pos_left hmesh hKpos
      _ = ε / 2 := by dsimp only [δ]; field_simp
  have hgap := darboux_gap_le_gap_add_mesh f hf P Q lo hi hlo' hhi' hbound
  have htag := tagged_bounds f Q hf ξ
  have hval := realIntegral_bounds f hint Q
  rw [hI] at hval
  change upperSum f Q hf - lowerSum f Q hf ≤
    upperSum f P hf - lowerSum f P hf + K * mesh Q at hgap
  apply abs_lt.mpr
  constructor <;> linarith [htag.1, htag.2, hval.1, hval.2]

end SingleVariableAnalysis.Riemann
