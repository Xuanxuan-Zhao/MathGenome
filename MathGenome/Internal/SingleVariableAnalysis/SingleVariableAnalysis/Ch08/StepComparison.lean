import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.StepComparison
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Integral

namespace SingleVariableAnalysis.Riemann.Step
open scoped BigOperators

/-- No partition node is strictly inside a cell. -/
theorem node_not_in_open {a b : ℝ} (P : Partition a b)
    (i : Fin P.n) (k : Fin (P.n + 1)) :
    P.point k ∉ Set.Ioo (P.point i.castSucc) (P.point i.succ) := by
  intro hk
  have h₁ := P.strictMono.lt_iff_lt.mp hk.1
  have h₂ := P.strictMono.lt_iff_lt.mp hk.2
  have : i.val < k.val := h₁
  have : k.val < i.val + 1 := h₂
  omega

theorem open_cells_disjoint {a b : ℝ} (P : Partition a b)
    (i j : Fin P.n) {x : ℝ}
    (hi : x ∈ Set.Ioo (P.point i.castSucc) (P.point i.succ))
    (hj : x ∈ Set.Ioo (P.point j.castSucc) (P.point j.succ)) : i = j := by
  apply le_antisymm
  · by_contra h
    have hji : j.val + 1 ≤ i.val := by omega
    have hp := P.strictMono.monotone (show j.succ ≤ i.castSucc from hji)
    linarith [hi.1, hj.2]
  · by_contra h
    have hij : i.val + 1 ≤ j.val := by omega
    have hp := P.strictMono.monotone (show i.succ ≤ j.castSucc from hij)
    linarith [hj.1, hi.2]

theorem value_on_open : Specs.SingleVariableAnalysis.Ch08.StepComparison.openCellValues := by
  classical
  intro a b s i x hx
  unfold value
  have hcell : (∑ j : Fin s.partition.n,
      if x ∈ Set.Ioo (s.partition.point j.castSucc) (s.partition.point j.succ)
        then s.constant j else 0) = s.constant i := by
    rw [Finset.sum_eq_single i]
    · simp [hx]
    · intro j _ hji
      have : x ∉ Set.Ioo (s.partition.point j.castSucc) (s.partition.point j.succ) :=
        fun hj => hji (open_cells_disjoint s.partition j i hj hx)
      simp [this]
    · simp
  have hnode : (∑ k : Fin (s.partition.n + 1),
      if x = s.partition.point k then s.node k else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    have : x ≠ s.partition.point k := by
      intro h
      rw [h] at hx
      exact node_not_in_open s.partition i k hx
    simp [this]
  rw [hcell, hnode, add_zero]

theorem value_on_node : Specs.SingleVariableAnalysis.Ch08.StepComparison.nodeValues := by
  classical
  intro a b s k
  unfold value
  have hc : (∑ i : Fin s.partition.n,
      if s.partition.point k ∈ Set.Ioo (s.partition.point i.castSucc) (s.partition.point i.succ)
        then s.constant i else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact ite_eq_right (node_not_in_open s.partition i k)
  rw [hc, zero_add, Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    exact ite_eq_right (fun h => hj (s.partition.strictMono.injective h).symm)
  · simp

/-- Every point before the last endpoint lies in a half-open cell. -/
theorem exists_halfOpen_cell {a b x : ℝ} (P : Partition a b)
    (ha : a ≤ x) (hb : x < b) :
    ∃ i : Fin P.n, P.point i.castSucc ≤ x ∧ x < P.point i.succ := by
  have hlast : x < endpointAt P P.n := by
    simpa only [show P.n = (Fin.last P.n).val from rfl, endpointAt_eq, P.last] using hb
  have hex : ∃ k : ℕ, x < endpointAt P k := ⟨P.n, hlast⟩
  let m := Nat.find hex
  have hm : x < endpointAt P m := Nat.find_spec hex
  have hmn : m ≤ P.n := Nat.find_min' hex hlast
  have hm0 : m ≠ 0 := by
    intro heq
    have hz : endpointAt P 0 = a := (endpointAt_eq P 0).trans P.first
    rw [heq, hz] at hm
    exact (not_lt_of_ge ha) hm
  have hprev : endpointAt P (m - 1) ≤ x :=
    le_of_not_gt (Nat.find_min hex (show m - 1 < m by omega))
  let i : Fin P.n := ⟨m - 1, by omega⟩
  refine ⟨i, ?_, ?_⟩
  · simpa only [show m - 1 = i.castSucc.val from rfl, endpointAt_eq] using hprev
  · have heq : m = i.succ.val := by dsimp [i]; omega
    simpa only [heq, endpointAt_eq] using hm

theorem node_or_open {a b x : ℝ} (P : Partition a b) (hx : x ∈ Set.Icc a b) :
    (∃ k, x = P.point k) ∨
    ∃ i : Fin P.n, x ∈ Set.Ioo (P.point i.castSucc) (P.point i.succ) := by
  by_cases hb : x = b
  · exact Or.inl ⟨Fin.last P.n, hb.trans P.last.symm⟩
  · obtain ⟨i, hi, hj⟩ := exists_halfOpen_cell P hx.1 (lt_of_le_of_ne hx.2 hb)
    rcases hi.eq_or_lt with hi | hi
    · exact Or.inl ⟨i.castSucc, hi.symm⟩
    · exact Or.inr ⟨i, hi, hj⟩

theorem refinement_cell_contained {a b : ℝ} (P Q : Partition a b)
    (h : Refines Q P) (j : Fin Q.n) : ∃ i : Fin P.n, cell Q j ⊆ cell P i := by
  have hleft := (cell_subset_interval Q j) (show Q.point j.castSucc ∈ cell Q j from
    ⟨le_rfl, (Q.strictMono (Fin.castSucc_lt_succ (i := j))).le⟩)
  have hright := (cell_subset_interval Q j) (show Q.point j.succ ∈ cell Q j from
    ⟨(Q.strictMono (Fin.castSucc_lt_succ (i := j))).le, le_rfl⟩)
  obtain ⟨i, hi, hj⟩ := exists_halfOpen_cell P hleft.1
    (lt_of_lt_of_le (Q.strictMono (Fin.castSucc_lt_succ (i := j))) hright.2)
  obtain ⟨k, hk⟩ := exists_refinementIndex h i.succ
  have hjk : j.castSucc < k := Q.strictMono.lt_iff_lt.mp (by simpa [hk] using hj)
  have hsucc : j.succ ≤ k := by change j.val + 1 ≤ k.val; exact hjk
  refine ⟨i, fun x hx => ⟨hi.trans hx.1, hx.2.trans ?_⟩⟩
  simpa only [hk] using Q.strictMono.monotone hsucc

theorem mesh_refinement_le {a b : ℝ} (P Q : Partition a b) (h : Refines Q P) :
    mesh Q ≤ mesh P := by
  apply mesh_le Q (mesh_nonneg P)
  intro j
  obtain ⟨i, hi⟩ := refinement_cell_contained P Q h j
  have hl := hi (show Q.point j.castSucc ∈ cell Q j from
    ⟨le_rfl, (Q.strictMono (Fin.castSucc_lt_succ (i := j))).le⟩)
  have hr := hi (show Q.point j.succ ∈ cell Q j from
    ⟨(Q.strictMono (Fin.castSucc_lt_succ (i := j))).le, le_rfl⟩)
  exact (show cellLength Q j ≤ cellLength P i by
    change _ - _ ≤ _ - _; linarith [hl.1, hr.2]).trans (cellLength_le_mesh P i)

/-- Incidences with old nodes; a fine cell has at most two such incidences. -/
noncomputable def nodeWeight {a b : ℝ} (P Q : Partition a b) (j : Fin Q.n) : ℝ :=
  ∑ k : Fin (P.n + 1),
    ((if Q.point j.castSucc = P.point k then 1 else 0) +
     (if Q.point j.succ = P.point k then 1 else 0))

theorem nodeWeight_nonneg {a b : ℝ} (P Q : Partition a b) (j : Fin Q.n) :
    0 ≤ nodeWeight P Q j := by
  classical
  apply Finset.sum_nonneg
  intro k _
  exact add_nonneg (by split <;> norm_num) (by split <;> norm_num)

theorem nodeWeight_ge_one {a b : ℝ} (P Q : Partition a b) (j : Fin Q.n)
    (k : Fin (P.n + 1))
    (h : Q.point j.castSucc = P.point k ∨ Q.point j.succ = P.point k) :
    1 ≤ nodeWeight P Q j := by
  classical
  have hk : (1 : ℝ) ≤
      (if Q.point j.castSucc = P.point k then 1 else 0) +
      (if Q.point j.succ = P.point k then 1 else 0) := by
    rcases h with h | h <;> simp only [h, ite_true] <;> split <;> norm_num
  apply hk.trans
  unfold nodeWeight
  apply Finset.single_le_sum _ (Finset.mem_univ k)
  intro l _
  exact add_nonneg (by split <;> norm_num) (by split <;> norm_num)

/-- For an injective endpoint list, a specified point meets at most one left
endpoint and at most one right endpoint. -/
theorem incidence_length_le {a b : ℝ} (Q : Partition a b) (z : ℝ)
    (e : Fin Q.n → Fin (Q.n + 1)) (he : Function.Injective e) :
    (∑ j : Fin Q.n, (if Q.point (e j) = z then 1 else 0) * cellLength Q j) ≤ mesh Q := by
  classical
  by_cases h : ∃ j, Q.point (e j) = z
  · obtain ⟨j, hj⟩ := h
    have hh (k : Fin Q.n) : Q.point (e k) = z ↔ k = j := by
      constructor
      · intro hk; exact he (Q.strictMono.injective (hk.trans hj.symm))
      · rintro rfl; exact hj
    simpa only [hh, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, one_mul, zero_mul]
      using cellLength_le_mesh Q j
  · have hz (j : Fin Q.n) : Q.point (e j) ≠ z := fun hj => h ⟨j, hj⟩
    simpa only [hz, ite_false, zero_mul, Finset.sum_const_zero] using mesh_nonneg Q

theorem node_length_le {a b : ℝ} (P Q : Partition a b) :
    (∑ j : Fin Q.n, nodeWeight P Q j * cellLength Q j) ≤
      (2 * (P.n + 1 : ℕ) : ℝ) * mesh Q := by
  classical
  calc
    _ = ∑ k : Fin (P.n + 1), ∑ j : Fin Q.n,
        ((if Q.point j.castSucc = P.point k then 1 else 0) +
         (if Q.point j.succ = P.point k then 1 else 0)) * cellLength Q j := by
      simp only [nodeWeight, Finset.sum_mul]
      rw [Finset.sum_comm]
    _ ≤ ∑ _k : Fin (P.n + 1), (mesh Q + mesh Q) := by
      apply Finset.sum_le_sum
      intro k _
      simp only [add_mul, Finset.sum_add_distrib]
      exact add_le_add
        (incidence_length_le Q (P.point k) Fin.castSucc (Fin.castSucc_injective _))
        (incidence_length_le Q (P.point k) Fin.succ (Fin.succ_injective _))
    _ = _ := by simp; ring

theorem short_node_neighborhoods :
    Specs.SingleVariableAnalysis.Ch08.StepComparison.shortNodeNeighborhoods := by
  classical
  intro a b P ε hε
  have hab : a ≤ b := by
    simpa only [P.first, P.last] using P.strictMono.monotone (Fin.zero_le (Fin.last P.n))
  rcases hab.eq_or_lt with rfl | hab
  · refine ⟨P, Finset.Subset.refl _, ?_⟩
    have : IsEmpty (Fin P.n) := Fin.isEmpty_iff.mpr (n_eq_zero_of_degenerate a P)
    simpa using hε
  · let N : ℝ := 2 * (P.n + 1 : ℕ)
    have hN : 0 < N := by dsimp [N]; positivity
    obtain ⟨R, _, hR⟩ := arbitrarily_fine hab (ε / N) (div_pos hε hN)
    obtain ⟨Q, _, hQP, hQR⟩ := common_refinement P R
    refine ⟨Q, hQP, ?_⟩
    have hmesh : mesh Q < ε / N := (mesh_refinement_le R Q hQR).trans_lt hR
    have hlen := node_length_le P Q
    have heq : (∑ k : Fin (P.n + 1), ∑ j : Fin Q.n,
        ((if Q.point j.castSucc = P.point k then 1 else 0) +
         (if Q.point j.succ = P.point k then 1 else 0)) * cellLength Q j) =
        ∑ j : Fin Q.n, nodeWeight P Q j * cellLength Q j := by
      simp only [nodeWeight, Finset.sum_mul]; rw [Finset.sum_comm]
    rw [heq]
    exact hlen.trans_lt ((lt_div_iff₀' hN).mp hmesh)

/-- Reverse the upstream weighted refinement inequality by negating coefficients. -/
theorem weighted_refinement_ge {a b : ℝ} (P Q : Partition a b) (h : Refines Q P)
    (c : Fin P.n → ℝ) (d : Fin Q.n → ℝ)
    (hd : ∀ i j, cell Q j ⊆ cell P i → c i ≤ d j) :
    (∑ i, c i * cellLength P i) ≤ ∑ j, d j * cellLength Q j := by
  have hh := weighted_sum_refinement_le P Q h (fun i => -c i) (fun j => -d j)
    (fun i j hij => neg_le_neg (hd i j hij))
  simpa only [neg_mul, Finset.sum_neg_distrib, neg_le_neg_iff] using hh

/-- Quantitative comparison on a refinement. Off old nodes the open-cell
hypothesis applies to the entire new closed cell. Node cells cost at most C. -/
theorem open_bound_refinement {a b : ℝ} (f : ℝ → ℝ) (P Q : Partition a b)
    (hf : BoundedOnInterval f a b) (h : Refines Q P)
    (c : Fin P.n → ℝ) (m C : ℝ) (hC : 0 ≤ C)
    (hm : ∀ x ∈ Set.Icc a b, m ≤ f x) (hc : ∀ i, c i ≤ m + C)
    (hopen : ∀ i x, x ∈ Set.Ioo (P.point i.castSucc) (P.point i.succ) → c i ≤ f x) :
    (∑ i, c i * cellLength P i) ≤ lowerSum f Q hf +
      C * ((2 * (P.n + 1 : ℕ) : ℝ) * mesh Q) := by
  classical
  have hmin (j : Fin Q.n) : m ≤ cellInfimum f Q hf j := by
    apply (cell_bounds f Q hf j).1.2
    rintro y ⟨x, hx, rfl⟩
    exact hm x (cell_subset_interval Q j hx)
  have hcoeff (i : Fin P.n) (j : Fin Q.n) (hij : cell Q j ⊆ cell P i) :
      c i ≤ cellInfimum f Q hf j + C * nodeWeight P Q j := by
    have hl := hij (show Q.point j.castSucc ∈ cell Q j from
      ⟨le_rfl, (Q.strictMono (Fin.castSucc_lt_succ (i := j))).le⟩)
    have hr := hij (show Q.point j.succ ∈ cell Q j from
      ⟨(Q.strictMono (Fin.castSucc_lt_succ (i := j))).le, le_rfl⟩)
    by_cases hbad : Q.point j.castSucc = P.point i.castSucc ∨
        Q.point j.succ = P.point i.succ
    · have hw : 1 ≤ nodeWeight P Q j := by
        rcases hbad with hl | hr
        · exact nodeWeight_ge_one P Q j i.castSucc (Or.inl hl)
        · exact nodeWeight_ge_one P Q j i.succ (Or.inr hr)
      have := mul_le_mul_of_nonneg_left hw hC
      linarith [hc i, hmin j]
    · push Not at hbad
      have hgood : c i ≤ cellInfimum f Q hf j := by
        apply (cell_bounds f Q hf j).1.2
        rintro y ⟨x, hx, rfl⟩
        apply hopen i x
        exact ⟨(lt_of_le_of_ne hl.1 (Ne.symm hbad.1)).trans_le hx.1,
          hx.2.trans_lt (lt_of_le_of_ne hr.2 hbad.2)⟩
      exact hgood.trans (le_add_of_nonneg_right (mul_nonneg hC (nodeWeight_nonneg P Q j)))
  have hs := weighted_refinement_ge P Q h c
    (fun j => cellInfimum f Q hf j + C * nodeWeight P Q j) hcoeff
  calc
    _ ≤ ∑ j, (cellInfimum f Q hf j + C * nodeWeight P Q j) * cellLength Q j := hs
    _ = lowerSum f Q hf + C * (∑ j, nodeWeight P Q j * cellLength Q j) := by
      simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
      rfl
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (node_length_le P Q) hC)

/-- Values of f at the finitely many partition nodes do not enter this
hypothesis. The preceding quantitative estimate proves they have zero cost. -/
theorem open_bound_lowerIntegral {a b : ℝ} (f : ℝ → ℝ) (P : Partition a b)
    (hab : a ≤ b) (hf : BoundedOnInterval f a b) (c : Fin P.n → ℝ)
    (hopen : ∀ i x, x ∈ Set.Ioo (P.point i.castSucc) (P.point i.succ) → c i ≤ f x) :
    (∑ i, c i * cellLength P i) ≤ lowerIntegral f hab hf := by
  classical
  rcases hab.eq_or_lt with rfl | hab
  · have : IsEmpty (Fin P.n) := Fin.isEmpty_iff.mpr (n_eq_zero_of_degenerate a P)
    have hz : (∑ i, c i * cellLength P i) = 0 := by simp
    exact hz.trans_le (degenerate_integral_bounds f a hf).1.ge
  · obtain ⟨m, hm⟩ := hf.1
    obtain ⟨M, hM⟩ := (Set.finite_range c).bddAbove
    let C := |M - m| + 1
    have hC : 0 < C := by dsimp [C]; positivity
    have hc (i : Fin P.n) : c i ≤ m + C := by
      have hi := hM (Set.mem_range_self i)
      have ha := le_abs_self (M - m)
      dsimp [C]
      linarith
    let N : ℝ := 2 * (P.n + 1 : ℕ)
    have hN : 0 < N := by dsimp [N]; positivity
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨R, _, hR⟩ := arbitrarily_fine hab (ε / (C * N))
      (div_pos hε (mul_pos hC hN))
    obtain ⟨Q, _, hQP, hQR⟩ := common_refinement P R
    have hs := open_bound_refinement f P Q hf hQP c m C hC.le
      (fun x hx => hm (Set.mem_image_of_mem f hx)) hc hopen
    have hmesh : mesh Q < ε / (C * N) := (mesh_refinement_le R Q hQR).trans_lt hR
    have herr : C * (N * mesh Q) < ε := by
      have := (lt_div_iff₀' (mul_pos hC hN)).mp hmesh
      nlinarith
    have hsum := (lowerIntegral_isLUB f hab.le hf).1 (Set.mem_range_self Q)
    exact hs.trans (by change lowerSum f Q hf + C * (N * mesh Q) ≤ _; linarith)

/-- Boundedness is preserved by changing sign. -/
theorem bounded_neg {a b : ℝ} (f : ℝ → ℝ) (hf : BoundedOnInterval f a b) :
    BoundedOnInterval (fun x => -f x) a b := by
  obtain ⟨m, hm⟩ := hf.1
  obtain ⟨M, hM⟩ := hf.2
  constructor
  · refine ⟨-M, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact neg_le_neg (hM (Set.mem_image_of_mem f hx))
  · refine ⟨-m, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact neg_le_neg (hm (Set.mem_image_of_mem f hx))

/-- Negation exchanges the cell infimum with minus the cell supremum. -/
theorem cellInfimum_neg {a b : ℝ} (f : ℝ → ℝ) (P : Partition a b)
    (hf : BoundedOnInterval f a b) (i : Fin P.n) :
    cellInfimum (fun x => -f x) P (bounded_neg f hf) i = -cellSupremum f P hf i := by
  apply le_antisymm
  · have hs : cellSupremum f P hf i ≤
        -cellInfimum (fun x => -f x) P (bounded_neg f hf) i := by
      apply (cell_bounds f P hf i).2.2
      rintro y ⟨x, hx, rfl⟩
      have := cellInfimum_le (fun x => -f x) P (bounded_neg f hf) i hx
      linarith
    linarith
  · apply (cell_bounds (fun x => -f x) P (bounded_neg f hf) i).1.2
    rintro y ⟨x, hx, rfl⟩
    exact neg_le_neg (le_cellSupremum f P hf i hx)

theorem lowerSum_neg {a b : ℝ} (f : ℝ → ℝ) (P : Partition a b)
    (hf : BoundedOnInterval f a b) :
    lowerSum (fun x => -f x) P (bounded_neg f hf) = -upperSum f P hf := by
  change (∑ i, cellInfimum (fun x => -f x) P (bounded_neg f hf) i * cellLength P i) =
    -(∑ i, cellSupremum f P hf i * cellLength P i)
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun (i : Fin P.n) _ => congrArg (fun r : ℝ => r * cellLength P i)
      (cellInfimum_neg f P hf i))
  simpa only [neg_mul, Finset.sum_neg_distrib] using hs

theorem lowerIntegral_neg_le {a b : ℝ} (f : ℝ → ℝ) (hab : a ≤ b)
    (hf : BoundedOnInterval f a b) :
    lowerIntegral (fun x => -f x) hab (bounded_neg f hf) ≤ -upperIntegral f hab hf := by
  apply (lowerIntegral_isLUB (fun x => -f x) hab (bounded_neg f hf)).2
  rintro r ⟨P, rfl⟩
  exact (lowerSum_neg f P hf).le.trans
    (neg_le_neg ((upperIntegral_isGLB f hab hf).1 (Set.mem_range_self P)))

theorem open_bound_upperIntegral {a b : ℝ} (f : ℝ → ℝ) (P : Partition a b)
    (hab : a ≤ b) (hf : BoundedOnInterval f a b) (c : Fin P.n → ℝ)
    (hopen : ∀ i x, x ∈ Set.Ioo (P.point i.castSucc) (P.point i.succ) → f x ≤ c i) :
    upperIntegral f hab hf ≤ ∑ i, c i * cellLength P i := by
  have hh := open_bound_lowerIntegral (fun x => -f x) P hab (bounded_neg f hf)
    (fun i => -c i) (fun i x hx => neg_le_neg (hopen i x hx))
  have hh' := hh.trans (lowerIntegral_neg_le f hab hf)
  simp only [neg_mul, Finset.sum_neg_distrib, neg_le_neg_iff] at hh'
  exact hh'

/-- Every finite step datum is bounded on its closed interval, including nodes. -/
theorem value_bounded {a b : ℝ} (s : StepData a b) :
    BoundedOnInterval (value s) a b := by
  classical
  let T : Set ℝ := Set.range s.constant ∪ Set.range s.node
  have hT : T.Finite := (Set.finite_range s.constant).union (Set.finite_range s.node)
  have hsub : value s '' Set.Icc a b ⊆ T := by
    rintro y ⟨x, hx, rfl⟩
    rcases node_or_open s.partition hx with ⟨k, rfl⟩ | ⟨i, hi⟩
    · rw [value_on_node s k]
      exact Or.inr (Set.mem_range_self k)
    · rw [value_on_open s i x hi]
      exact Or.inl (Set.mem_range_self i)
  exact ⟨hT.bddBelow.mono hsub, hT.bddAbove.mono hsub⟩

/-- Both Darboux bounds of a step datum equal its independently defined
weighted integral. The open-bound lemmas supply the endpoint argument. -/
theorem step_darboux_bounds : Specs.SingleVariableAnalysis.Ch08.StepComparison.stepBounds := by
  intro a b s hab
  let hf := value_bounded s
  have hl := open_bound_lowerIntegral (value s) s.partition hab hf s.constant
    (fun i x hx => (value_on_open s i x hx).ge)
  have hu := open_bound_upperIntegral (value s) s.partition hab hf s.constant
    (fun i x hx => (value_on_open s i x hx).le)
  have hlu := lowerIntegral_le_upperIntegral (value s) hab hf
  exact ⟨hf, le_antisymm (hlu.trans hu) hl, le_antisymm hu (hl.trans hlu)⟩

/-- A partition supplies a step minorant with the actual node values. -/
noncomputable def lowerStep {a b : ℝ} (f : ℝ → ℝ) (P : Partition a b)
    (hf : BoundedOnInterval f a b) : StepData a b :=
  ⟨P, cellInfimum f P hf, fun k => f (P.point k)⟩

noncomputable def upperStep {a b : ℝ} (f : ℝ → ℝ) (P : Partition a b)
    (hf : BoundedOnInterval f a b) : StepData a b :=
  ⟨P, cellSupremum f P hf, fun k => f (P.point k)⟩

theorem lowerStep_le {a b : ℝ} (f : ℝ → ℝ) (P : Partition a b)
    (hf : BoundedOnInterval f a b) : ∀ x ∈ Set.Icc a b, value (lowerStep f P hf) x ≤ f x := by
  intro x hx
  rcases node_or_open P hx with ⟨k, rfl⟩ | ⟨i, hi⟩
  · exact (value_on_node (lowerStep f P hf) k).le
  · rw [value_on_open (lowerStep f P hf) i x hi]
    exact cellInfimum_le f P hf i ⟨hi.1.le, hi.2.le⟩

theorem le_upperStep {a b : ℝ} (f : ℝ → ℝ) (P : Partition a b)
    (hf : BoundedOnInterval f a b) : ∀ x ∈ Set.Icc a b, f x ≤ value (upperStep f P hf) x := by
  intro x hx
  rcases node_or_open P hx with ⟨k, rfl⟩ | ⟨i, hi⟩
  · exact (value_on_node (upperStep f P hf) k).ge
  · rw [value_on_open (upperStep f P hf) i x hi]
    exact le_cellSupremum f P hf i ⟨hi.1.le, hi.2.le⟩

/-- The supremum and infimum really range over all finite step minorants and
majorants, with no restriction relating the nodes to neighboring constants. -/
theorem darboux_step_comparison : Specs.SingleVariableAnalysis.Ch08.StepComparison.comparison := by
  intro f a b hab hf
  have hminor (s : StepData a b) (hs : ∀ x ∈ Set.Icc a b, value s x ≤ f x) :
      weightedIntegral s ≤ lowerIntegral f hab hf := by
    apply open_bound_lowerIntegral f s.partition hab hf s.constant
    intro i x hx
    rw [← value_on_open s i x hx]
    exact hs x (cell_subset_interval s.partition i ⟨hx.1.le, hx.2.le⟩)
  have hmajor (s : StepData a b) (hs : ∀ x ∈ Set.Icc a b, f x ≤ value s x) :
      upperIntegral f hab hf ≤ weightedIntegral s := by
    apply open_bound_upperIntegral f s.partition hab hf s.constant
    intro i x hx
    rw [← value_on_open s i x hx]
    exact hs x (cell_subset_interval s.partition i ⟨hx.1.le, hx.2.le⟩)
  obtain ⟨P⟩ := partition_exists hab
  have hneL : (minorantIntegrals f a b).Nonempty :=
    ⟨_, lowerStep f P hf, lowerStep_le f P hf, rfl⟩
  have hneU : (majorantIntegrals f a b).Nonempty :=
    ⟨_, upperStep f P hf, le_upperStep f P hf, rfl⟩
  have hbL : BddAbove (minorantIntegrals f a b) := by
    refine ⟨lowerIntegral f hab hf, ?_⟩
    rintro r ⟨s, hs, rfl⟩
    exact hminor s hs
  have hbU : BddBelow (majorantIntegrals f a b) := by
    refine ⟨upperIntegral f hab hf, ?_⟩
    rintro r ⟨s, hs, rfl⟩
    exact hmajor s hs
  constructor
  · apply le_antisymm
    · apply (lowerIntegral_isLUB f hab hf).2
      rintro r ⟨Q, rfl⟩
      exact le_csSup hbL ⟨lowerStep f Q hf, lowerStep_le f Q hf, rfl⟩
    · apply csSup_le hneL
      rintro r ⟨s, hs, rfl⟩
      exact hminor s hs
  · apply le_antisymm
    · apply le_csInf hneU
      rintro r ⟨s, hs, rfl⟩
      exact hmajor s hs
    · apply (upperIntegral_isGLB f hab hf).2
      rintro r ⟨Q, rfl⟩
      exact csInf_le hbU ⟨upperStep f Q hf, le_upperStep f Q hf, rfl⟩

/-- The usual proof-requiring Riemann value agrees with the finite weighted sum. -/
theorem step_integrable : Specs.SingleVariableAnalysis.Ch08.StepComparison.stepIntegrable := by
  intro a b s hab
  obtain ⟨hf, hl, hu⟩ := step_darboux_bounds s hab
  let h : RealIntegrable (value s) a b := ⟨hab, hf, hl.trans hu.symm⟩
  exact ⟨h, ((realIntegral_common_value (value s) h hab hf).1).trans hl⟩

/-- The extrema in the comparison theorem are mathematical finite real bounds,
rather than defaults of the total conditional supremum/infimum operations. -/
theorem step_families_finite :
    Specs.SingleVariableAnalysis.Ch08.StepComparison.stepFamiliesFinite := by
  intro f a b hab hf
  obtain ⟨P⟩ := partition_exists hab
  refine ⟨⟨_, lowerStep f P hf, lowerStep_le f P hf, rfl⟩,
    ⟨_, upperStep f P hf, le_upperStep f P hf, rfl⟩, ?_, ?_⟩
  · refine ⟨lowerIntegral f hab hf, ?_⟩
    rintro r ⟨s, hs, rfl⟩
    apply open_bound_lowerIntegral f s.partition hab hf s.constant
    intro i x hx
    rw [← value_on_open s i x hx]
    exact hs x (cell_subset_interval s.partition i ⟨hx.1.le, hx.2.le⟩)
  · refine ⟨upperIntegral f hab hf, ?_⟩
    rintro r ⟨s, hs, rfl⟩
    apply open_bound_upperIntegral f s.partition hab hf s.constant
    intro i x hx
    rw [← value_on_open s i x hx]
    exact hs x (cell_subset_interval s.partition i ⟨hx.1.le, hx.2.le⟩)

end SingleVariableAnalysis.Riemann.Step
