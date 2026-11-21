import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.RegulatedApproximation
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Partitions
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-! Finite step approximation from finite one-sided limits. We subdivide at the
centers AND boundaries of a finite interval cover, so no Lebesgue-number or
mesh-refinement bridge is needed. The argument works for normed additive groups;
the exported source statements specialize to the canonical ℝ and ℂ. -/
namespace SingleVariableAnalysis
open Set
namespace RegulatedApproximation
open Riemann

/-- No node lies strictly between two consecutive nodes. -/
lemma node_not_in_cell {a b : ℝ} (P : Partition a b)
    (i : Fin P.n) (j : Fin (P.n + 1)) :
    ¬ P.point j ∈ Ioo (P.point i.castSucc) (P.point i.succ) := by
  intro hj
  have h₁ := P.strictMono.lt_iff_lt.mp hj.1
  have h₂ := P.strictMono.lt_iff_lt.mp hj.2
  have h₁' : i.val < j.val := h₁
  have h₂' : j.val < i.val + 1 := h₂
  omega

lemma cell_subset_interval {a b : ℝ} (P : Partition a b) (i : Fin P.n) :
    Ioo (P.point i.castSucc) (P.point i.succ) ⊆ Icc a b := by
  intro x hx
  have h₁ : a ≤ P.point i.castSucc := by
    simpa only [P.first] using P.strictMono.monotone (Fin.zero_le i.castSucc)
  have h₂ : P.point i.succ ≤ b := by
    simpa only [P.last] using P.strictMono.monotone (Fin.le_last i.succ)
  exact ⟨h₁.trans hx.1.le, hx.2.le.trans h₂⟩

lemma cells_unique {a b x : ℝ} (P : Partition a b) (i j : Fin P.n)
    (hi : x ∈ Ioo (P.point i.castSucc) (P.point i.succ))
    (hj : x ∈ Ioo (P.point j.castSucc) (P.point j.succ)) : i = j := by
  apply le_antisymm
  · by_contra h
    have hji : j.succ ≤ i.castSucc := by
      change j.val + 1 ≤ i.val
      have : j < i := lt_of_not_ge h
      exact this
    have := P.strictMono.monotone hji
    linarith [hi.1, hj.2]
  · by_contra h
    have hij : i.succ ≤ j.castSucc := by
      change i.val + 1 ≤ j.val
      have : i < j := lt_of_not_ge h
      exact this
    have := P.strictMono.monotone hij
    linarith [hj.1, hi.2]

/-- Every interval point is either a node or lies in a unique open cell. -/
lemma node_or_cell {a b x : ℝ} (P : Partition a b) (hx : x ∈ Icc a b) :
    (∃ j, x = P.point j) ∨ ∃ i : Fin P.n,
      x ∈ Ioo (P.point i.castSucc) (P.point i.succ) := by
  classical
  by_cases hnode : ∃ j, x = P.point j
  · exact Or.inl hnode
  right
  let t := Finset.univ.filter (fun j : Fin (P.n + 1) => P.point j ≤ x)
  have ht : t.Nonempty := ⟨0, by simp [t, P.first, hx.1]⟩
  let j := t.max' ht
  have hj : P.point j ≤ x := (Finset.mem_filter.mp (t.max'_mem ht)).2
  have hjlt : P.point j < x := lt_of_le_of_ne hj (fun h => hnode ⟨j, h.symm⟩)
  have hjlast : j ≠ Fin.last P.n := by
    intro h
    rw [h, P.last] at hjlt
    exact (not_lt_of_ge hx.2) hjlt
  obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.mpr hjlast
  refine ⟨i, hi ▸ hjlt, ?_⟩
  by_contra h
  have hmem : i.succ ∈ t := Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_gt h⟩
  have hle := t.le_max' i.succ hmem
  change i.succ ≤ j at hle
  rw [← hi] at hle
  exact (not_le_of_gt (Fin.castSucc_lt_succ (i := i))) hle

/-- At each center there is a neighborhood with small oscillation on each
strict side. At an endpoint the missing side is empty. -/
lemma local_oscillation {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {a b c : ℝ} (hf : RegulatedOn f a b) (hc : c ∈ Icc a b)
    {η : ℝ} (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧
      (∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
        c - r < x → x < c → c - r < y → y < c → ‖f x - f y‖ < η) ∧
      (∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
        c < x → x < c + r → c < y → y < c + r → ‖f x - f y‖ < η) := by
  have hhalf : 0 < η / 2 := half_pos hη
  have hl : ∃ r : ℝ, 0 < r ∧ ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      c - r < x → x < c → c - r < y → y < c → ‖f x - f y‖ < η := by
    by_cases hac : a < c
    · obtain ⟨L, hL⟩ := hf.1 c ⟨hac, hc.2⟩
      obtain ⟨r, hr, h⟩ := hL.2 (η / 2) hhalf
      refine ⟨r, hr, ?_⟩
      intro x hx y hy hxr hxc hyr hyc
      have h₁ : dist (f x) L < η / 2 := h x hx ⟨hxr, hxc⟩
      have h₂ : dist (f y) L < η / 2 := h y hy ⟨hyr, hyc⟩
      rw [← dist_eq_norm]
      calc
        dist (f x) (f y) ≤ dist (f x) L + dist (f y) L := dist_triangle_right _ _ _
        _ < η := by linarith
    · exact ⟨1, zero_lt_one, fun x hx y hy _ hxc _ _ =>
        False.elim (by linarith [hx.1])⟩
  have hr : ∃ r : ℝ, 0 < r ∧ ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      c < x → x < c + r → c < y → y < c + r → ‖f x - f y‖ < η := by
    by_cases hcb : c < b
    · obtain ⟨L, hL⟩ := hf.2 c ⟨hc.1, hcb⟩
      obtain ⟨r, hr, h⟩ := hL.2 (η / 2) hhalf
      refine ⟨r, hr, ?_⟩
      intro x hx y hy hcx hxr hcy hyr
      have h₁ : dist (f x) L < η / 2 := h x hx ⟨hcx, hxr⟩
      have h₂ : dist (f y) L < η / 2 := h y hy ⟨hcy, hyr⟩
      rw [← dist_eq_norm]
      calc
        dist (f x) (f y) ≤ dist (f x) L + dist (f y) L := dist_triangle_right _ _ _
        _ < η := by linarith
    · exact ⟨1, zero_lt_one, fun x hx y hy hcx _ _ _ =>
        False.elim (by linarith [hx.2])⟩
  obtain ⟨l, hl, hleft⟩ := hl
  obtain ⟨r, hr, hright⟩ := hr
  refine ⟨min l r, lt_min hl hr, ?_, ?_⟩
  · intro x hx y hy hx₁ hx₂ hy₁ hy₂
    exact hleft x hx y hy (by linarith [min_le_left l r]) hx₂
      (by linarith [min_le_left l r]) hy₂
  · intro x hx y hy hx₁ hx₂ hy₁ hy₂
    exact hright x hx y hy hx₁ (by linarith [min_le_right l r]) hy₁
      (by linarith [min_le_right l r])

lemma point_not_in_cell {a b c : ℝ} (P : Partition a b) (i : Fin P.n)
    (hc : c ∈ points P) : ¬ c ∈ Ioo (P.point i.castSucc) (P.point i.succ) := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hc
  exact node_not_in_cell P i j

noncomputable def cellMidpoint {a b : ℝ} (P : Partition a b) (i : Fin P.n) : ℝ :=
  (P.point i.castSucc + P.point i.succ) / 2

lemma cellMidpoint_mem {a b : ℝ} (P : Partition a b) (i : Fin P.n) :
    cellMidpoint P i ∈ Ioo (P.point i.castSucc) (P.point i.succ) := by
  have h := P.strictMono (Fin.castSucc_lt_succ (i := i))
  constructor <;> dsimp [cellMidpoint] <;> linarith

/-- Cut at all selected centers and neighborhood boundaries. Every cell then
lies in one member of the cover, strictly on one side of its center. -/
theorem exists_partition_small_oscillation {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {a b : ℝ} (hab : a ≤ b) (hf : RegulatedOn f a b)
    {η : ℝ} (hη : 0 < η) :
    ∃ P : Partition a b, ∀ i : Fin P.n,
      ∀ x ∈ Ioo (P.point i.castSucc) (P.point i.succ),
      ∀ y ∈ Ioo (P.point i.castSucc) (P.point i.succ), ‖f x - f y‖ < η := by
  classical
  choose r hr hleft hright using
    (fun c : Icc a b => local_oscillation hf c.property hη)
  let U : Icc a b → Set ℝ := fun c => Ioo (c.val - r c) (c.val + r c)
  have hcover : Icc a b ⊆ ⋃ c, U c := by
    intro x hx
    refine mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    have h := hr ⟨x, hx⟩
    change x - r ⟨x, hx⟩ < x ∧ x < x + r ⟨x, hx⟩
    constructor <;> linarith
  obtain ⟨t, ht⟩ := isCompact_Icc.elim_finite_subcover U (fun _ => isOpen_Ioo) hcover
  let cuts : Finset ℝ := (t.image Subtype.val) ∪
    (t.image (fun c => c.val - r c)) ∪ (t.image (fun c => c.val + r c))
  let nodes : Finset ℝ := insert a (insert b (cuts.filter (fun x => x ∈ Icc a b)))
  have hbounds : ∀ x ∈ nodes, x ∈ Icc a b := by
    intro x hx
    simp only [nodes, Finset.mem_insert, Finset.mem_filter] at hx
    rcases hx with rfl | rfl | ⟨_, hx⟩
    · exact ⟨le_rfl, hab⟩
    · exact ⟨hab, le_rfl⟩
    · exact hx
  let P := ofPoints nodes (by simp [nodes]) (by simp [nodes]) hbounds
  have hP : points P = nodes := points_ofPoints _ _ _ _
  have hcut {x : ℝ} (hx : x ∈ cuts) (hx' : x ∈ Icc a b) : x ∈ points P := by
    rw [hP]
    simp only [nodes, Finset.mem_insert, Finset.mem_filter]
    exact Or.inr (Or.inr ⟨hx, hx'⟩)
  refine ⟨P, ?_⟩
  intro i
  let m := cellMidpoint P i
  have hm := cellMidpoint_mem P i
  have hmcover := ht (cell_subset_interval P i hm)
  simp only [mem_iUnion, exists_prop] at hmcover
  obtain ⟨c, hc, hmc⟩ := hmcover
  change c.val - r c < m ∧ m < c.val + r c at hmc
  have hcmem : c.val ∈ cuts := by
    simp only [cuts, Finset.mem_union, Finset.mem_image]
    exact Or.inl (Or.inl ⟨c, hc, rfl⟩)
  have hlmem : c.val - r c ∈ cuts := by
    simp only [cuts, Finset.mem_union, Finset.mem_image]
    exact Or.inl (Or.inr ⟨c, hc, rfl⟩)
  have hrmem : c.val + r c ∈ cuts := by
    simp only [cuts, Finset.mem_union, Finset.mem_image]
    exact Or.inr ⟨c, hc, rfl⟩
  have hnc := point_not_in_cell P i (hcut hcmem c.property)
  have hinU : ∀ x ∈ Ioo (P.point i.castSucc) (P.point i.succ),
      c.val - r c < x ∧ x < c.val + r c := by
    intro x hx
    constructor
    · by_contra h
      have hxl : x ≤ c.val - r c := le_of_not_gt h
      have hlcell : c.val - r c ∈ Ioo (P.point i.castSucc) (P.point i.succ) :=
        ⟨hx.1.trans_le hxl, hmc.1.trans hm.2⟩
      exact point_not_in_cell P i
        (hcut hlmem (cell_subset_interval P i hlcell)) hlcell
    · by_contra h
      have hrx : c.val + r c ≤ x := le_of_not_gt h
      have hrcell : c.val + r c ∈ Ioo (P.point i.castSucc) (P.point i.succ) :=
        ⟨hm.1.trans hmc.2, hrx.trans_lt hx.2⟩
      exact point_not_in_cell P i
        (hcut hrmem (cell_subset_interval P i hrcell)) hrcell
  intro x hx y hy
  rcases le_or_gt c.val (P.point i.castSucc) with hcu | huc
  · exact hright c x (cell_subset_interval P i hx) y (cell_subset_interval P i hy)
      (hcu.trans_lt hx.1) (hinU x hx).2 (hcu.trans_lt hy.1) (hinU y hy).2
  · have hvc : P.point i.succ ≤ c.val := le_of_not_gt (fun h => hnc ⟨huc, h⟩)
    exact hleft c x (cell_subset_interval P i hx) y (cell_subset_interval P i hy)
      (hinU x hx).1 (hx.2.trans_le hvc) (hinU y hy).1 (hy.2.trans_le hvc)

/-- Choose one value of f in each cell, retaining f exactly at every node. -/
theorem exists_step_pointwise {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {a b : ℝ} (hab : a ≤ b) (hf : RegulatedOn f a b)
    {η : ℝ} (hη : 0 < η) :
    ∃ P : Partition a b, ∃ s : ℝ → E,
      IsStepOn P s ∧ (∀ j, s (P.point j) = f (P.point j)) ∧
      ∀ x ∈ Icc a b, ‖f x - s x‖ < η := by
  classical
  obtain ⟨P, hP⟩ := exists_partition_small_oscillation hab hf hη
  let s : ℝ → E := fun x =>
    if h : ∃ i : Fin P.n, x ∈ Ioo (P.point i.castSucc) (P.point i.succ)
    then f (cellMidpoint P h.choose) else f x
  have hcell (i : Fin P.n) (x : ℝ)
      (hx : x ∈ Ioo (P.point i.castSucc) (P.point i.succ)) :
      s x = f (cellMidpoint P i) := by
    have h : ∃ j : Fin P.n, x ∈ Ioo (P.point j.castSucc) (P.point j.succ) := ⟨i, hx⟩
    have hi : h.choose = i := cells_unique P h.choose i h.choose_spec hx
    simp only [s, dite_eq_left h, hi]
  refine ⟨P, s, ?_, ?_, ?_⟩
  · exact fun i => ⟨f (cellMidpoint P i), fun x hx => hcell i x hx⟩
  · intro j
    have h : ¬ ∃ i : Fin P.n, P.point j ∈ Ioo (P.point i.castSucc) (P.point i.succ) := by
      rintro ⟨i, hi⟩
      exact node_not_in_cell P i j hi
    simp only [s, dite_eq_right h]
  · intro x hx
    by_cases h : ∃ i : Fin P.n, x ∈ Ioo (P.point i.castSucc) (P.point i.succ)
    · obtain ⟨i, hi⟩ := h
      rw [hcell i x hi]
      exact hP i x hi (cellMidpoint P i) (cellMidpoint_mem P i)
    · simp only [s, dite_eq_right h, sub_self, norm_zero]
      exact hη

/-- Finitely many cell constants and independently assigned node values give a
finite bound on any step function, including when there are no cells. -/
theorem step_bounded {E : Type*} [NormedAddCommGroup E]
    {a b : ℝ} (P : Partition a b) {s : ℝ → E} (hs : IsStepOn P s) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Icc a b, ‖s x‖ ≤ M := by
  classical
  choose v hv using hs
  let norms : Finset ℝ := insert 0 ((Finset.univ.image (fun i => ‖v i‖)) ∪
    (Finset.univ.image (fun j => ‖s (P.point j)‖)))
  have hn : norms.Nonempty := Finset.insert_nonempty _ _
  refine ⟨norms.sup' hn id, ?_, ?_⟩
  · exact Finset.le_sup' id (Finset.mem_insert_self _ _)
  · intro x hx
    apply Finset.le_sup' id
    rcases node_or_cell P hx with ⟨j, rfl⟩ | ⟨i, hi⟩
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
    · rw [hv i x hi]
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))

/-- Use half the requested tolerance before taking a supremum. Pointwise
strict inequalities alone would only give a non-strict supremum bound. -/
theorem step_approximation {E : Type*} [NormedAddCommGroup E] :
    Specs.SingleVariableAnalysis.Ch15.RegulatedApproximation.stepApproximation E := by
  intro a b hab f hf ε hε
  obtain ⟨P, s, hs, hn, herr⟩ := exists_step_pointwise hab hf (half_pos hε)
  refine ⟨P, s, hs, hn, ?_, ?_⟩
  · exact ⟨ε / 2, by rintro z ⟨x, hx, rfl⟩; exact (herr x hx).le⟩
  · have he : ((fun x => ‖f x - s x‖) '' Icc a b).Nonempty :=
      ⟨‖f a - s a‖, a, ⟨le_rfl, hab⟩, rfl⟩
    exact (csSup_le he (by rintro z ⟨x, hx, rfl⟩; exact (herr x hx).le)).trans_lt
      (half_lt_self hε)

theorem regulated_bounded {E : Type*} [NormedAddCommGroup E]
    {a b : ℝ} (hab : a ≤ b) {f : ℝ → E} (hf : RegulatedOn f a b) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Icc a b, ‖f x‖ ≤ M := by
  obtain ⟨P, s, hs, _, herr⟩ := exists_step_pointwise hab hf zero_lt_one
  obtain ⟨M, hM, hsM⟩ := step_bounded P hs
  refine ⟨1 + M, by linarith, ?_⟩
  intro x hx
  calc
    ‖f x‖ ≤ ‖f x - s x‖ + ‖s x‖ := by
      simpa only [add_comm] using norm_le_insert' (f x) (s x)
    _ ≤ 1 + M := add_le_add (herr x hx).le (hsM x hx)

end RegulatedApproximation

/-- The source real statement, with absolute value interpreted by the usual norm. -/
theorem real_regulated_step_approximation :
    Specs.SingleVariableAnalysis.Ch15.RegulatedApproximation.realStepApproximation :=
  RegulatedApproximation.step_approximation

/-- The same construction for complex values uses their usual modulus. -/
theorem complex_regulated_step_approximation :
    Specs.SingleVariableAnalysis.Ch15.RegulatedApproximation.complexStepApproximation :=
  RegulatedApproximation.step_approximation

theorem real_regulated_bounded :
    Specs.SingleVariableAnalysis.Ch15.RegulatedApproximation.realBoundedness := by
  intro a b hab f hf
  simpa only [Real.norm_eq_abs] using RegulatedApproximation.regulated_bounded hab hf

theorem complex_regulated_bounded :
    Specs.SingleVariableAnalysis.Ch15.RegulatedApproximation.complexBoundedness := by
  intro a b hab f hf
  exact RegulatedApproximation.regulated_bounded hab hf

end SingleVariableAnalysis
