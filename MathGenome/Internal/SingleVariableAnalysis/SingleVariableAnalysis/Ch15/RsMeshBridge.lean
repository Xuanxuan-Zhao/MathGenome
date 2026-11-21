import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.RsMeshBridge
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.RsDarboux
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.HeineCantor
import Mathlib.Tactic.Abel

namespace SingleVariableAnalysis.Stieltjes
open Riemann
open scoped BigOperators
universe u
abbrev MeshLimit := @Specs.SingleVariableAnalysis.Ch15.RsMeshBridge.meshLimitValue

namespace MeshBridge

/-- A finite endpoint list crosses every index between its endpoints. -/
theorem exists_adjacent {n : ℕ} (g : Fin (n+1) → ℕ) (k : ℕ)
    (hlo : g 0 ≤ k) (hhi : k < g (Fin.last n)) :
    ∃ i : Fin n, g i.castSucc ≤ k ∧ k < g i.succ := by
  induction n with
  | zero => exact False.elim (by simpa using (not_lt_of_ge hlo hhi))
  | succ n ih =>
    by_cases h : k < g (Fin.succ 0)
    · exact ⟨0, hlo, h⟩
    · obtain ⟨i, hl, hr⟩ := ih (fun j => g j.succ) (le_of_not_gt h) hhi
      exact ⟨i.succ, hl, hr⟩

/-- Every fine cell is contained in a coarse cell. -/
theorem cell_contained {a b : ℝ} {P T : Partition a b} (h : Refines T P)
    (j : Fin T.n) : ∃ i : Fin P.n, cell T j ⊆ cell P i := by
  obtain ⟨i, hl, hr⟩ := exists_adjacent (fun k => (refinementIndex h k).val) j.val
    (by rw [refinementIndex_zero]; exact Nat.zero_le _)
    (by rw [refinementIndex_last]; exact j.isLt)
  refine ⟨i, fun x hx => ⟨?_, ?_⟩⟩
  · have hp := T.strictMono.monotone (show refinementIndex h i.castSucc ≤ j.castSucc from hl)
    rw [point_refinementIndex] at hp
    exact hp.trans hx.1
  · have hp := T.strictMono.monotone
      (show j.succ ≤ refinementIndex h i.succ from Nat.succ_le_of_lt hr)
    rw [point_refinementIndex] at hp
    exact hx.2.trans hp

theorem mesh_refinement_le {a b : ℝ} {P T : Partition a b} (h : Refines T P) :
    mesh T ≤ mesh P := by
  apply mesh_le _ (mesh_nonneg P)
  intro j
  obtain ⟨i, hi⟩ := cell_contained h j
  have hleft := hi (show T.point j.castSucc ∈ cell T j from
    ⟨le_rfl, (T.strictMono (Fin.castSucc_lt_succ (i := j))).le⟩)
  have hright := hi (show T.point j.succ ∈ cell T j from
    ⟨(T.strictMono (Fin.castSucc_lt_succ (i := j))).le, le_rfl⟩)
  have hc : cellLength T j ≤ cellLength P i := by
    change T.point j.succ - T.point j.castSucc ≤ P.point i.succ - P.point i.castSucc
    linarith [hleft.1, hright.2]
  exact hc.trans (cellLength_le_mesh P i)

theorem fine_partition {a b : ℝ} (hab : a ≤ b) {δ : ℝ} (hd : 0 < δ) :
    ∃ P : Partition a b, mesh P < δ := by
  rcases hab.eq_or_lt with rfl | hlt
  · exact ⟨emptyPartition a, by simpa only [mesh_eq_zero_of_n_eq_zero (emptyPartition a) rfl] using hd⟩
  · obtain ⟨P, _, hP⟩ := arbitrarily_fine hlt δ hd
    exact ⟨P, hP⟩

theorem refinementLimit_of_meshLimit {E : Type u} [NormedAddCommGroup E] [Module ℝ E]
    {a b : ℝ} (hab : a ≤ b) {f : ℝ → E} {α : ℝ → ℝ} {I : E}
    (hI : MeshLimit a b f α I) : RefinementLimit a b f α I := by
  intro ε hε
  obtain ⟨δ, hd, hδ⟩ := hI ε hε
  obtain ⟨P, hP⟩ := fine_partition hab hd
  exact ⟨P, fun T hT t => hδ T ((mesh_refinement_le hT).trans_lt hP) t⟩

/-- Telescoping works in arbitrary additive groups, including complex scalars. -/
theorem sum_differences {E : Type u} [AddCommGroup E] {n : ℕ}
    (g : Fin (n+1) → E) :
    (∑ i : Fin n, (g i.succ - g i.castSucc)) = g (Fin.last n) - g 0 := by
  have h₁ := Fin.sum_univ_succ g
  have h₂ := Fin.sum_univ_castSucc g
  rw [Finset.sum_sub_distrib]
  apply (sub_eq_sub_iff_add_eq_add).mpr
  calc
    (∑ i : Fin n, g i.succ) + g 0 = ∑ i, g i := by rw [h₁]; abel
    _ = g (Fin.last n) + ∑ i : Fin n, g i.castSucc := by rw [h₂]; abel

/-- Cells crossing a node of Q are the only cells changed by union. -/
def Crosses {a b : ℝ} (P Q : Partition a b) (i : Fin P.n) : Prop :=
  ∃ q : Fin (Q.n+1), P.point i.castSucc < Q.point q ∧ Q.point q < P.point i.succ

theorem disjoint_interiors {a b : ℝ} (P : Partition a b) (i j : Fin P.n) {x : ℝ}
    (hi : P.point i.castSucc < x ∧ x < P.point i.succ)
    (hj : P.point j.castSucc < x ∧ x < P.point j.succ) : i = j := by
  have h₁ := P.strictMono.lt_iff_lt.mp (hi.1.trans hj.2)
  have h₂ := P.strictMono.lt_iff_lt.mp (hj.1.trans hi.2)
  apply Fin.ext
  change i.val < j.val + 1 at h₁
  change j.val < i.val + 1 at h₂
  omega

noncomputable def crossingCells {a b : ℝ} (P Q : Partition a b) : Finset (Fin P.n) := by
  classical
  exact Finset.univ.filter (Crosses P Q)

theorem crossing_card_le {a b : ℝ} (P Q : Partition a b) :
    (crossingCells P Q).card ≤ Q.n+1 := by
  classical
  let node : {i : Fin P.n // Crosses P Q i} → Fin (Q.n+1) :=
    fun i => Classical.choose i.property
  have hinj : Function.Injective node := by
    intro i j hij
    apply Subtype.ext
    apply disjoint_interiors P i.val j.val (Classical.choose_spec i.property)
    have hj := Classical.choose_spec j.property
    change P.point j.val.castSucc < Q.point (node j) ∧ Q.point (node j) < P.point j.val.succ at hj
    rw [← hij] at hj
    exact hj
  have hc := Fintype.card_le_of_injective node hinj
  rw [Fintype.card_subtype] at hc
  simpa [crossingCells] using hc

noncomputable def compatibleTags {a b : ℝ} (P : Partition a b) (t : Tagging P)
    (T : Partition a b) : Tagging T := fun j => by
  classical
  by_cases h : ∃ i : Fin P.n,
      T.point j.castSucc = P.point i.castSucc ∧ T.point j.succ = P.point i.succ
  · refine ⟨t h.choose, ?_, ?_⟩
    · exact h.choose_spec.1.le.trans (t h.choose).property.1
    · exact (t h.choose).property.2.trans h.choose_spec.2.ge
  · exact ⟨T.point j.castSucc, le_rfl,
      (T.strictMono (Fin.castSucc_lt_succ (i := j))).le⟩

theorem compatibleTags_eq {a b : ℝ} (P : Partition a b) (t : Tagging P)
    (T : Partition a b) (i : Fin P.n) (j : Fin T.n)
    (hl : T.point j.castSucc = P.point i.castSucc)
    (hr : T.point j.succ = P.point i.succ) :
    (compatibleTags P t T j : ℝ) = t i := by
  classical
  have h : ∃ i : Fin P.n,
      T.point j.castSucc = P.point i.castSucc ∧ T.point j.succ = P.point i.succ := ⟨i, hl, hr⟩
  have he : h.choose = i := by
    have hp := P.strictMono.injective (h.choose_spec.1.symm.trans hl)
    apply Fin.ext
    exact congrArg (fun k : Fin (P.n+1) => k.val) hp
  simp only [compatibleTags, dite_eq_left h]
  change (t h.choose : ℝ) = t i
  rw [he]

/-- A union cell has no extra points when the coarse cell crosses no Q node. -/
theorem unsplit {a b : ℝ} (P Q T : Partition a b)
    (hpoints : points T = points P ∪ points Q) (h : Refines T P)
    (i : Fin P.n) (hi : ¬ Crosses P Q i) :
    (refinementIndex h i.succ).val = (refinementIndex h i.castSucc).val + 1 := by
  have hlt := refinementIndex_strictMono h (Fin.castSucc_lt_succ (i := i))
  by_contra he
  have hgap : (refinementIndex h i.castSucc).val + 1 < (refinementIndex h i.succ).val := by
    change (refinementIndex h i.castSucc).val < (refinementIndex h i.succ).val at hlt
    omega
  let k : Fin (T.n+1) := ⟨(refinementIndex h i.castSucc).val+1,
    lt_trans hgap (refinementIndex h i.succ).isLt⟩
  have hl : P.point i.castSucc < T.point k := by
    rw [← point_refinementIndex h]
    exact T.strictMono (show refinementIndex h i.castSucc < k from Nat.lt_succ_self _)
  have hr : T.point k < P.point i.succ := by
    rw [← point_refinementIndex h]
    exact T.strictMono hgap
  have hk : T.point k ∈ points T := Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  rw [hpoints] at hk
  rcases Finset.mem_union.mp hk with hp | hq
  · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hp
    rw [← hj] at hl hr
    have h₁ := P.strictMono.lt_iff_lt.mp hl
    have h₂ := P.strictMono.lt_iff_lt.mp hr
    change i.val < j.val at h₁
    change j.val < i.val+1 at h₂
    omega
  · obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hq
    exact hi ⟨q, by simpa only [hq] using hl, by simpa only [hq] using hr⟩

section Vector
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def termAt {a b : ℝ} (T : Partition a b) (t : Tagging T)
    (f : ℝ → E) (α : ℝ → ℝ) (k : ℕ) : E :=
  if hk : k < T.n then Darboux.weight α T ⟨k, hk⟩ • f (t ⟨k, hk⟩) else 0

noncomputable def segment {a b : ℝ} {P T : Partition a b} (h : Refines T P)
    (t : Tagging T) (f : ℝ → E) (α : ℝ → ℝ) (i : Fin P.n) : E :=
  ∑ k ∈ Finset.Ico (refinementIndex h i.castSucc).val (refinementIndex h i.succ).val,
    termAt T t f α k

theorem sum_segments {a b : ℝ} {P T : Partition a b} (h : Refines T P)
    (t : Tagging T) (f : ℝ → E) (α : ℝ → ℝ) :
    (∑ i : Fin P.n, segment h t f α i) = Stieltjes.taggedSum T t f α := by
  let F : ℕ → E := fun k => ∑ j ∈ Finset.range k, termAt T t f α j
  have hs (i : Fin P.n) : segment h t f α i =
      F (refinementIndex h i.succ).val - F (refinementIndex h i.castSucc).val := by
    exact Finset.sum_Ico_eq_sub _
      ((refinementIndex_strictMono h (Fin.castSucc_lt_succ (i := i))).le)
  simp_rw [hs]
  rw [sum_differences (fun i => F (refinementIndex h i).val),
    refinementIndex_last, refinementIndex_zero]
  have ht : F T.n = Stieltjes.taggedSum T t f α := by
    exact (Finset.sum_fin_eq_sum_range
      (fun j : Fin T.n => Darboux.weight α T j • f (t j))).symm
  simp only [Fin.val_last, Fin.val_zero, ht, F, Finset.sum_range_zero, sub_zero]

theorem segment_norm_le {a b : ℝ} {P T : Partition a b} (h : Refines T P)
    (t : Tagging T) (f : ℝ → E) (α : ℝ → ℝ) (M : ℝ)
    (hf : ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ M) (hα : MonotoneOn α (Set.Icc a b))
    (i : Fin P.n) : ‖segment h t f α i‖ ≤ M * Darboux.weight α P i := by
  have hterm (k : ℕ)
      (hk : k ∈ Finset.Ico (refinementIndex h i.castSucc).val (refinementIndex h i.succ).val) :
      ‖termAt T t f α k‖ ≤
        M * (α (endpointAt T (k+1)) - α (endpointAt T k)) := by
    have hkT : k < T.n := by have := (refinementIndex h i.succ).isLt; have := (Finset.mem_Ico.mp hk).2; omega
    let j : Fin T.n := ⟨k, hkT⟩
    rw [show endpointAt T (k+1) = T.point j.succ from endpointAt_eq T j.succ,
      show endpointAt T k = T.point j.castSucc from endpointAt_eq T j.castSucc]
    simp only [termAt, dite_eq_left hkT, norm_smul, Real.norm_eq_abs]
    change |Darboux.weight α T j| * ‖f (t j)‖ ≤ M * Darboux.weight α T j
    rw [abs_of_nonneg (Darboux.weight_nonneg hα T j)]
    exact (mul_le_mul_of_nonneg_left (hf _ (cell_subset_interval T j (t j).property))
      (Darboux.weight_nonneg hα T j)).trans_eq (mul_comm _ _)
  calc
    ‖segment h t f α i‖ ≤ ∑ k ∈ Finset.Ico (refinementIndex h i.castSucc).val
        (refinementIndex h i.succ).val, ‖termAt T t f α k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Ico (refinementIndex h i.castSucc).val
        (refinementIndex h i.succ).val,
        M * (α (endpointAt T (k+1)) - α (endpointAt T k)) := Finset.sum_le_sum hterm
    _ = M * Darboux.weight α P i := by
      rw [← Finset.mul_sum, Finset.sum_Ico_sub (fun k => α (endpointAt T k))
        (refinementIndex_strictMono h (Fin.castSucc_lt_succ (i := i))).le,
        endpointAt_eq, endpointAt_eq, point_refinementIndex, point_refinementIndex]
      rfl

theorem segment_unsplit {a b : ℝ} (P Q T : Partition a b)
    (hpoints : points T = points P ∪ points Q) (h : Refines T P)
    (t : Tagging P) (f : ℝ → E) (α : ℝ → ℝ) (i : Fin P.n)
    (hi : ¬ Crosses P Q i) :
    segment h (compatibleTags P t T) f α i = Darboux.weight α P i • f (t i) := by
  have he := unsplit P Q T hpoints h i hi
  have hk : (refinementIndex h i.castSucc).val < T.n := by
    have := (refinementIndex h i.succ).isLt; omega
  let j : Fin T.n := ⟨(refinementIndex h i.castSucc).val, hk⟩
  have hl : T.point j.castSucc = P.point i.castSucc := point_refinementIndex h i.castSucc
  have hr : T.point j.succ = P.point i.succ := by
    have hj : j.succ = refinementIndex h i.succ := Fin.ext he.symm
    rw [hj, point_refinementIndex]
  unfold segment
  rw [he, Nat.Ico_succ_singleton, Finset.sum_singleton]
  simp only [termAt, dite_eq_left hk]
  change Darboux.weight α T j • f (compatibleTags P t T j) = _
  rw [compatibleTags_eq P t T i j hl hr]
  congr 1
  exact congrArg₂ (fun x y => α x - α y) hr hl

/-- Compare an arbitrary sum with a compatible sum on its union with Q.
No regularity of f is needed. There are at most Q.n+1 crossing cells. -/
theorem union_error_le {a b : ℝ} (P Q T : Partition a b)
    (hpoints : points T = points P ∪ points Q) (h : Refines T P)
    (t : Tagging P) (f : ℝ → E) (α : ℝ → ℝ) (M η : ℝ)
    (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hf : ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ M) (hα : MonotoneOn α (Set.Icc a b))
    (hsmall : ∀ i : Fin P.n, Darboux.weight α P i ≤ η) :
    ‖Stieltjes.taggedSum P t f α -
      Stieltjes.taggedSum T (compatibleTags P t T) f α‖ ≤
      (Q.n+1 : ℕ) * (2*M*η) := by
  classical
  let u := compatibleTags P t T
  have hlocal (i : Fin P.n) :
      ‖Darboux.weight α P i • f (t i) - segment h u f α i‖ ≤
        if Crosses P Q i then 2*M*η else 0 := by
    by_cases hi : Crosses P Q i
    · rw [ite_eq_left hi]
      have hb := hf _ (cell_subset_interval P i (t i).property)
      have hs := segment_norm_le h u f α M hf hα i
      have hn : ‖Darboux.weight α P i • f (t i)‖ ≤ M * Darboux.weight α P i := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Darboux.weight_nonneg hα P i)]
        exact (mul_le_mul_of_nonneg_left hb (Darboux.weight_nonneg hα P i)).trans_eq (mul_comm _ _)
      have ht := norm_sub_le (Darboux.weight α P i • f (t i)) (segment h u f α i)
      have hsm := mul_le_mul_of_nonneg_left (hsmall i) hM
      linarith
    · rw [ite_eq_right hi, show segment h u f α i = Darboux.weight α P i • f (t i) from
        segment_unsplit P Q T hpoints h t f α i hi, sub_self, norm_zero]
  calc
    ‖Stieltjes.taggedSum P t f α - Stieltjes.taggedSum T u f α‖ =
        ‖∑ i : Fin P.n, (Darboux.weight α P i • f (t i) - segment h u f α i)‖ := by
      rw [Finset.sum_sub_distrib, sum_segments]
      rfl
    _ ≤ ∑ i : Fin P.n, ‖Darboux.weight α P i • f (t i) - segment h u f α i‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin P.n, if Crosses P Q i then 2*M*η else 0 := Finset.sum_le_sum fun i _ => hlocal i
    _ = (crossingCells P Q).card * (2*M*η) := by
      rw [← Finset.sum_filter]
      simp [crossingCells]
    _ ≤ (Q.n+1 : ℕ) * (2*M*η) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast crossing_card_le P Q) (by positivity)

/-- Uniform continuity of α makes the union error small uniformly in all tags. -/
theorem union_error_small {a b : ℝ} (hab : a ≤ b) (Q : Partition a b)
    (f : ℝ → E) (α : ℝ → ℝ) (hf : BoundedOn a b f)
    (hc : ContinuousOn α (Set.Icc a b)) (hα : MonotoneOn α (Set.Icc a b))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (P T : Partition a b),
      points T = points P ∪ points Q → ∀ h : Refines T P,
      mesh P < δ → ∀ t : Tagging P,
      ‖Stieltjes.taggedSum P t f α -
        Stieltjes.taggedSum T (compatibleTags P t T) f α‖ < ε := by
  obtain ⟨M, hf⟩ := hf
  have hM : 0 ≤ M := (norm_nonneg (f a)).trans (hf a ⟨le_rfl, hab⟩)
  let C : ℝ := (Q.n+1 : ℕ) * (2*M)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let η := ε / (C+1)
  have hη : 0 < η := div_pos hε (by linarith)
  have hηeq : η * (C+1) = ε := div_mul_cancel₀ _ (by linarith : C+1 ≠ 0)
  have hηε : C*η < ε := by nlinarith
  obtain ⟨δ, hd, hδ⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hc) η hη
  refine ⟨δ, hd, ?_⟩
  intro P T hpoints h hmesh t
  have hsmall (i : Fin P.n) : Darboux.weight α P i ≤ η := by
    have hi := hδ (P.point i.succ) (Darboux.point_mem P _)
      (P.point i.castSucc) (Darboux.point_mem P _)
      (show dist (P.point i.succ) (P.point i.castSucc) < δ by
        rw [Real.dist_eq]
        change |cellLength P i| < δ
        rw [abs_of_nonneg (cell_positive P i).le]
        exact (cellLength_le_mesh P i).trans_lt hmesh)
    exact (le_abs_self _).trans (by simpa only [Real.dist_eq, Darboux.weight] using hi.le)
  have hu := union_error_le P Q T hpoints h t f α M η hM hη.le hf hα hsmall
  exact hu.trans_lt (by dsimp only [C] at hηε; nlinarith [hηε])

/-- The same norm argument proves the bridge in any real normed space.
For the source this is used at exactly E=ℝ and E=ℂ. -/
theorem meshLimit_of_refinementLimit {a b : ℝ} (hab : a ≤ b)
    {f : ℝ → E} {α : ℝ → ℝ} {I : E} (hf : BoundedOn a b f)
    (hc : ContinuousOn α (Set.Icc a b)) (hα : MonotoneOn α (Set.Icc a b))
    (hI : RefinementLimit a b f α I) : MeshLimit a b f α I := by
  intro ε hε
  obtain ⟨Q, hQ⟩ := hI (ε/2) (half_pos hε)
  obtain ⟨δ, hd, hδ⟩ := union_error_small hab Q f α hf hc hα (ε/2) (half_pos hε)
  refine ⟨δ, hd, ?_⟩
  intro P hP t
  obtain ⟨T, hpoints, hTP, hTQ⟩ := common_refinement P Q
  have h₁ := hδ P T hpoints hTP hP t
  have h₂ := hQ T hTQ (compatibleTags P t T)
  have ht := norm_add_le
    (Stieltjes.taggedSum P t f α - Stieltjes.taggedSum T (compatibleTags P t T) f α)
    (Stieltjes.taggedSum T (compatibleTags P t T) f α - I)
  rw [sub_add_sub_cancel] at ht
  linarith

end Vector
end MeshBridge

/-- Equality of the two limiting values, including the boundedness conditions
of the refinement integral. -/
theorem integral_iff_meshLimit {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} (hab : a ≤ b) (f : ℝ → E) (α : ℝ → ℝ)
    (hf : BoundedOn a b f) (hc : ContinuousOn α (Set.Icc a b))
    (hα : MonotoneOn α (Set.Icc a b)) (I : E) :
    HasIntegral a b f α I ↔ MeshLimit a b f α I := by
  constructor
  · intro h
    exact MeshBridge.meshLimit_of_refinementLimit hab hf hc hα
      ((integral_iff_of_le a b hab f α I).mp h).2.2
  · intro h
    exact (integral_iff_of_le a b hab f α I).mpr
      ⟨hf, Darboux.monotone_boundedOn hab hα,
        MeshBridge.refinementLimit_of_meshLimit hab h⟩

theorem real_mesh_bridge : Specs.SingleVariableAnalysis.Ch15.RsMeshBridge.realBridge := by
  intro a b hab f α hf hc hα I
  exact integral_iff_meshLimit hab f α hf hc hα I

theorem complex_mesh_bridge : Specs.SingleVariableAnalysis.Ch15.RsMeshBridge.complexBridge := by
  intro a b hab f α hf hc hα I
  exact integral_iff_meshLimit hab f α hf hc hα I

theorem real_mesh_existence : Specs.SingleVariableAnalysis.Ch15.RsMeshBridge.realExistence := by
  intro a b hab f α hf hc hα
  exact exists_congr fun I => real_mesh_bridge a b hab f α hf hc hα I

theorem complex_mesh_existence : Specs.SingleVariableAnalysis.Ch15.RsMeshBridge.complexExistence := by
  intro a b hab f α hf hc hα
  exact exists_congr fun I => complex_mesh_bridge a b hab f α hf hc hα I

theorem mesh_degenerate : Specs.SingleVariableAnalysis.Ch15.RsMeshBridge.degenerate := by
  intro E _ _ a f α I
  constructor
  · intro hI
    have hzero := (degenerate_integral a f α (0 : E)).mpr rfl
    have hzero' := ((integral_iff_of_le a a le_rfl f α 0).mp hzero).2.2
    exact refinementLimit_unique (MeshBridge.refinementLimit_of_meshLimit le_rfl hI) hzero'
  · rintro rfl ε hε
    refine ⟨1, zero_lt_one, ?_⟩
    intro P _ t
    rw [degenerate_sum a P t f α, sub_self, norm_zero]
    exact hε

theorem mesh_constant_integrator : Specs.SingleVariableAnalysis.Ch15.RsMeshBridge.constantIntegrator := by
  intro E _ _ a b f c ε hε
  refine ⟨1, zero_lt_one, ?_⟩
  intro P _ t
  simpa only [S.sumValue, sub_self, zero_smul, Finset.sum_const_zero, norm_zero] using hε

theorem constant_integrand_sum {E : Type u} [AddCommGroup E] [Module ℝ E]
    {a b : ℝ} (P : Partition a b) (t : Tagging P) (c : E) (α : ℝ → ℝ) :
    Stieltjes.taggedSum P t (fun _ => c) α = (α b - α a) • c := by
  unfold Stieltjes.taggedSum S.sumValue
  rw [← Finset.sum_smul, sum_cell_differences (fun i => α (P.point i)), P.last, P.first]

theorem mesh_constant_integrand : Specs.SingleVariableAnalysis.Ch15.RsMeshBridge.constantIntegrand := by
  intro E _ _ a b c α ε hε
  refine ⟨1, zero_lt_one, ?_⟩
  intro P _ t
  change ‖Stieltjes.taggedSum P t (fun _ => c) α - (α b - α a) • c‖ < ε
  rw [constant_integrand_sum P t c α, sub_self, norm_zero]
  exact hε


theorem taggedSum_re {a b : ℝ} (P : Partition a b) (t : Tagging P)
    (f : ℝ → ℂ) (α : ℝ → ℝ) :
    (Stieltjes.taggedSum P t f α).re = Stieltjes.taggedSum P t (fun x => (f x).re) α := by
  change Complex.reLm (∑ i : Fin P.n, Darboux.weight α P i • f (t i)) =
    ∑ i : Fin P.n, Darboux.weight α P i • Complex.reLm (f (t i))
  simp only [map_sum, map_smul]

theorem taggedSum_im {a b : ℝ} (P : Partition a b) (t : Tagging P)
    (f : ℝ → ℂ) (α : ℝ → ℝ) :
    (Stieltjes.taggedSum P t f α).im = Stieltjes.taggedSum P t (fun x => (f x).im) α := by
  change Complex.imLm (∑ i : Fin P.n, Darboux.weight α P i • f (t i)) =
    ∑ i : Fin P.n, Darboux.weight α P i • Complex.imLm (f (t i))
  simp only [map_sum, map_smul]

theorem mesh_complex_components : Specs.SingleVariableAnalysis.Ch15.RsMeshBridge.complexComponents := by
  intro a b f α I
  constructor
  · intro h
    constructor
    · intro ε hε
      obtain ⟨δ, hd, hδ⟩ := h ε hε
      refine ⟨δ, hd, ?_⟩
      intro P hP t
      have he := (Complex.abs_re_le_norm (Stieltjes.taggedSum P t f α - I)).trans_lt (hδ P hP t)
      simpa only [Real.norm_eq_abs, Complex.sub_re, taggedSum_re] using he
    · intro ε hε
      obtain ⟨δ, hd, hδ⟩ := h ε hε
      refine ⟨δ, hd, ?_⟩
      intro P hP t
      have he := (Complex.abs_im_le_norm (Stieltjes.taggedSum P t f α - I)).trans_lt (hδ P hP t)
      simpa only [Real.norm_eq_abs, Complex.sub_im, taggedSum_im] using he
  · rintro ⟨hr, hi⟩ ε hε
    obtain ⟨δr, hdr, hδr⟩ := hr (ε/2) (half_pos hε)
    obtain ⟨δi, hdi, hδi⟩ := hi (ε/2) (half_pos hε)
    refine ⟨min δr δi, lt_min hdr hdi, ?_⟩
    intro P hP t
    have hr' := hδr P (lt_of_lt_of_le hP (min_le_left _ _)) t
    have hi' := hδi P (lt_of_lt_of_le hP (min_le_right _ _)) t
    have he := Complex.norm_le_abs_re_add_abs_im (Stieltjes.taggedSum P t f α - I)
    simp only [Real.norm_eq_abs] at hr' hi'
    simp only [Complex.sub_re, Complex.sub_im, taggedSum_re, taggedSum_im] at he
    linarith

end SingleVariableAnalysis.Stieltjes
