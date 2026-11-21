import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.RsExistence
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.RsSums
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.Variation
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.HeineCantor
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Positivity

/-! Continuous integrands against real BV integrators (K03.15.rs_existence).

The proof expands coarse increments along the node embedding of a refinement.
Telescoping gives the exact finite expansion; oscillation times total variation
bounds its error. Completeness then supplies a refinement limit. Comparing an
arbitrary fine partition with its union with a controlling partition proves
unrestricted mesh convergence. The same proof covers singleton intervals and
zero variation. No measure integral or normalization of the integrator is used.

Supplementary reference: P. Spreij, *Functions of bounded variation and Stieltjes
integrals*, Proposition 1.5,
https://staff.fnwi.uva.nl/p.j.c.spreij/onderwijs/master/bv.pdf .
-/
namespace SingleVariableAnalysis.Stieltjes
open Riemann
open scoped BigOperators

universe u

/-- The node embedding induced by inclusion of the endpoint sets. -/
noncomputable def refinementNode {a b : ℝ} (P Q : Partition a b)
    (h : Refines Q P) (i : Fin (P.n+1)) : Fin (Q.n+1) :=
  Classical.choose (Finset.mem_image.mp
    (h (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)))

theorem refinementNode_point {a b : ℝ} (P Q : Partition a b)
    (h : Refines Q P) (i : Fin (P.n+1)) :
    Q.point (refinementNode P Q h i) = P.point i :=
  (Classical.choose_spec (Finset.mem_image.mp
    (h (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)))).2

theorem refinementNode_strictMono {a b : ℝ} (P Q : Partition a b)
    (h : Refines Q P) : StrictMono (refinementNode P Q h) := by
  intro i j hij
  apply Q.strictMono.lt_iff_lt.mp
  simpa only [refinementNode_point] using P.strictMono hij

theorem refinementNode_first {a b : ℝ} (P Q : Partition a b)
    (h : Refines Q P) : refinementNode P Q h 0 = 0 := by
  apply Q.strictMono.injective
  rw [refinementNode_point, P.first, Q.first]

theorem refinementNode_last {a b : ℝ} (P Q : Partition a b)
    (h : Refines Q P) : refinementNode P Q h (Fin.last P.n) = Fin.last Q.n := by
  apply Q.strictMono.injective
  rw [refinementNode_point, P.last, Q.last]

/-- Telescoping over a finite endpoint list. -/
theorem sum_fin_increments {A : Type*} [AddCommGroup A] {n : ℕ}
    (v : Fin (n+1) → A) :
    (∑ i : Fin n, (v i.succ - v i.castSucc)) = v (Fin.last n) - v 0 := by
  rw [Finset.sum_sub_distrib]
  apply sub_eq_sub_iff_add_eq_add.mpr
  simpa only [add_comm] using
    (Fin.sum_univ_succ v).symm.trans (Fin.sum_univ_castSucc v)

/-- Splitting a finite sum at any increasing list of indices. -/
theorem sum_index_intervals {A : Type*} [AddCommGroup A] {n : ℕ}
    (e : Fin (n+1) → ℕ) (he : Monotone e) (v : ℕ → A) :
    (∑ i : Fin n, ∑ j ∈ Finset.Ico (e i.castSucc) (e i.succ), v j) =
      ∑ j ∈ Finset.Ico (e 0) (e (Fin.last n)), v j := by
  simp_rw [Finset.sum_Ico_eq_sub v (he (Fin.castSucc_le_succ _))]
  rw [sum_fin_increments (fun i => ∑ j ∈ Finset.range (e i), v j),
    Finset.sum_Ico_eq_sub v (he (Fin.zero_le _))]


variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every finite polygonal variation sum is bounded by the finite supremum. -/
theorem partition_variation_le {a b : ℝ} (P : Partition a b) (α : ℝ → ℝ)
    (hα : BV.HasBoundedVariation α a b) :
    (∑ i : Fin P.n, ‖α (P.point i.succ) - α (P.point i.castSucc)‖) ≤
      (BV.totalVariation α a b).toReal := by
  have h : BV.partitionSum P α ≤ BV.totalVariation α a b :=
    le_iSup (fun Q : Partition a b => BV.partitionSum Q α) P
  have ht := ENNReal.toReal_mono (ne_of_lt hα) h
  simpa [BV.partitionSum, Specs.SingleVariableAnalysis.Ch15.Variation.partitionSumValue,
    ENNReal.toReal_sum, ENNReal.toReal_ofReal] using ht

/-- All tags, including endpoint tags, belong to the original closed interval. -/
theorem tag_mem_interval {a b : ℝ} (P : Partition a b) (t : Tagging P) (i : Fin P.n) :
    (t i : ℝ) ∈ Set.Icc a b := by
  have hl := (endpoints P).2.2 _ (Finset.mem_image.mpr ⟨i.castSucc, Finset.mem_univ _, rfl⟩)
  have hr := (endpoints P).2.2 _ (Finset.mem_image.mpr ⟨i.succ, Finset.mem_univ _, rfl⟩)
  exact ⟨hl.1.trans (t i).property.1, (t i).property.2.trans hr.2⟩

/-- The finite-sum norm bound, with an arbitrary pointwise bound on the integrand. -/
theorem norm_taggedSum_le {a b : ℝ} (P : Partition a b) (t : Tagging P)
    (f : ℝ → E) (α : ℝ → ℝ) (hα : BV.HasBoundedVariation α a b)
    {M : ℝ} (hM : 0 ≤ M) (hf : ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ M) :
    ‖taggedSum P t f α‖ ≤ M * (BV.totalVariation α a b).toReal := by
  calc
    ‖taggedSum P t f α‖ ≤ ∑ i : Fin P.n,
        ‖(α (P.point i.succ) - α (P.point i.castSucc)) • f (t i)‖ := norm_sum_le _ _
    _ = ∑ i : Fin P.n,
        ‖α (P.point i.succ) - α (P.point i.castSucc)‖ * ‖f (t i)‖ := by
      simp only [norm_smul]
    _ ≤ ∑ i : Fin P.n,
        ‖α (P.point i.succ) - α (P.point i.castSucc)‖ * M := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hf _ (tag_mem_interval P t i)) (norm_nonneg _)
    _ = M * ∑ i : Fin P.n, ‖α (P.point i.succ) - α (P.point i.castSucc)‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _
    _ ≤ M * (BV.totalVariation α a b).toReal :=
      mul_le_mul_of_nonneg_left (partition_variation_le P α hα) hM

/-- A BV integrator is bounded with its actual endpoint and node values. -/
theorem boundedOn_of_bv {a b : ℝ} (hab : a ≤ b) (α : ℝ → ℝ)
    (hα : BV.HasBoundedVariation α a b) : BoundedOn a b α := by
  have hv := (BV.boundedVariation_iff α hab).mp hα
  refine ⟨‖α a‖ + (BV.totalVariation α a b).toReal, ?_⟩
  intro x hx
  have hd := hv.dist_le hx (Set.left_mem_Icc.mpr hab)
  rw [← BV.totalVariation_eq_eVariationOn α hab, dist_eq_norm] at hd
  calc
    ‖α x‖ ≤ ‖α x - α a‖ + ‖α a‖ := by
      simpa only [sub_add_cancel] using norm_add_le (α x - α a) (α a)
    _ ≤ ‖α a‖ + (BV.totalVariation α a b).toReal := by linarith

/-- Extend a tagging to natural indices only to simplify finite interval sums.
Out-of-range values never occur in a partition sum. -/
def extendedTag {a b : ℝ} (Q : Partition a b) (u : Tagging Q) (j : ℕ) : ℝ :=
  if h : j < Q.n then (u ⟨j,h⟩ : ℝ) else a

def extendedIncrement {a b : ℝ} (Q : Partition a b) (α : ℝ → ℝ) (j : ℕ) : ℝ :=
  α (BV.extendedPoints Q (j+1)) - α (BV.extendedPoints Q j)

theorem extendedPoints_fin {a b : ℝ} (Q : Partition a b) (i : Fin (Q.n+1)) :
    BV.extendedPoints Q i.val = Q.point i := by
  simp only [BV.extendedPoints, min_eq_left (Nat.le_of_lt_succ i.isLt)]

theorem extendedTag_fin {a b : ℝ} (Q : Partition a b) (u : Tagging Q) (i : Fin Q.n) :
    extendedTag Q u i.val = (u i : ℝ) := by
  simp [extendedTag, i.isLt]

theorem extendedIncrement_fin {a b : ℝ} (Q : Partition a b) (α : ℝ → ℝ) (i : Fin Q.n) :
    extendedIncrement Q α i.val = α (Q.point i.succ) - α (Q.point i.castSucc) := by
  change α (BV.extendedPoints Q i.succ.val) - α (BV.extendedPoints Q i.castSucc.val) = _
  rw [extendedPoints_fin, extendedPoints_fin]

theorem taggedSum_eq_range {a b : ℝ} (Q : Partition a b) (u : Tagging Q)
    (f : ℝ → E) (α : ℝ → ℝ) : taggedSum Q u f α =
      ∑ j ∈ Finset.range Q.n, extendedIncrement Q α j • f (extendedTag Q u j) := by
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [extendedIncrement_fin, extendedTag_fin]

/-- The exact common-refinement estimate. Only oscillation of f on coarse
cells is used; the integrator may have jumps on either side of any node. -/
theorem refinement_estimate {a b : ℝ} (P Q : Partition a b) (h : Refines Q P)
    (t : Tagging P) (u : Tagging Q) (f : ℝ → E) (α : ℝ → ℝ)
    (hα : BV.HasBoundedVariation α a b) {η : ℝ} (hη : 0 ≤ η)
    (hf : ∀ i : Fin P.n, ∀ x ∈ Set.Icc (P.point i.castSucc) (P.point i.succ),
      ∀ y ∈ Set.Icc (P.point i.castSucc) (P.point i.succ), ‖f x - f y‖ ≤ η) :
    ‖taggedSum P t f α - taggedSum Q u f α‖ ≤
      η * (BV.totalVariation α a b).toReal := by
  classical
  let e : Fin (P.n+1) → ℕ := fun i => (refinementNode P Q h i).val
  have he : Monotone e := fun i j hij => (refinementNode_strictMono P Q h).monotone hij
  have he0 : e 0 = 0 := congrArg Fin.val (refinementNode_first P Q h)
  have helast : e (Fin.last P.n) = Q.n := congrArg Fin.val (refinementNode_last P Q h)
  have hnode (i : Fin (P.n+1)) : BV.extendedPoints Q (e i) = P.point i := by
    rw [extendedPoints_fin, refinementNode_point]
  have hcoarse : taggedSum P t f α =
      ∑ i : Fin P.n, ∑ j ∈ Finset.Ico (e i.castSucc) (e i.succ),
        extendedIncrement Q α j • f (t i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_smul]
    unfold extendedIncrement
    rw [Finset.sum_Ico_sub (fun j => α (BV.extendedPoints Q j))
      (he (Fin.castSucc_le_succ i)), hnode, hnode]
  have hfine : taggedSum Q u f α =
      ∑ i : Fin P.n, ∑ j ∈ Finset.Ico (e i.castSucc) (e i.succ),
        extendedIncrement Q α j • f (extendedTag Q u j) := by
    rw [sum_index_intervals e he, he0, helast, Nat.Ico_zero_eq_range, taggedSum_eq_range]
  have hbound (i : Fin P.n) (j : ℕ)
      (hj : j ∈ Finset.Ico (e i.castSucc) (e i.succ)) :
      ‖f (t i) - f (extendedTag Q u j)‖ ≤ η := by
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hj
    have hjn : j < Q.n := lt_of_lt_of_le hhi (Fin.is_le (refinementNode P Q h i.succ))
    let k : Fin Q.n := ⟨j, hjn⟩
    rw [show extendedTag Q u j = (u k : ℝ) from extendedTag_fin Q u k]
    apply hf i _ (t i).property _
    have hl : P.point i.castSucc ≤ Q.point k.castSucc := by
      rw [← refinementNode_point P Q h i.castSucc]
      exact Q.strictMono.monotone hlo
    have hr : Q.point k.succ ≤ P.point i.succ := by
      rw [← refinementNode_point P Q h i.succ]
      exact Q.strictMono.monotone (Nat.succ_le_of_lt hhi)
    exact ⟨hl.trans (u k).property.1, (u k).property.2.trans hr⟩
  have hvariation :
      (∑ i : Fin P.n, ∑ j ∈ Finset.Ico (e i.castSucc) (e i.succ),
        ‖extendedIncrement Q α j‖) ≤ (BV.totalVariation α a b).toReal := by
    rw [sum_index_intervals e he, he0, helast, Nat.Ico_zero_eq_range,
      ← Fin.sum_univ_eq_sum_range]
    simp_rw [extendedIncrement_fin]
    exact partition_variation_le Q α hα
  rw [hcoarse, hfine, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, ← smul_sub]
  calc
    _ ≤ ∑ i : Fin P.n, ∑ j ∈ Finset.Ico (e i.castSucc) (e i.succ),
        ‖extendedIncrement Q α j‖ * ‖f (t i) - f (extendedTag Q u j)‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      simpa only [norm_smul] using norm_sum_le _
        (fun j => extendedIncrement Q α j • (f (t i) - f (extendedTag Q u j)))
    _ ≤ ∑ i : Fin P.n, ∑ j ∈ Finset.Ico (e i.castSucc) (e i.succ),
        ‖extendedIncrement Q α j‖ * η := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hbound i j hj) (norm_nonneg _)
    _ = η * (∑ i : Fin P.n, ∑ j ∈ Finset.Ico (e i.castSucc) (e i.succ),
        ‖extendedIncrement Q α j‖) := by simp_rw [Finset.mul_sum, mul_comm η]
    _ ≤ η * (BV.totalVariation α a b).toReal := mul_le_mul_of_nonneg_left hvariation hη

omit [NormedSpace ℝ E] in
/-- A positive modulus controls the oscillation on every sufficiently fine cell. -/
theorem continuous_cell_oscillation {a b : ℝ} (f : ℝ → E)
    (hf : ContinuousOn f (Set.Icc a b)) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ P : Partition a b, mesh P < δ →
      ∀ i : Fin P.n, ∀ x ∈ Set.Icc (P.point i.castSucc) (P.point i.succ),
        ∀ y ∈ Set.Icc (P.point i.castSucc) (P.point i.succ), ‖f x - f y‖ ≤ η := by
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hf
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuousOn_iff.mp hu η hη
  refine ⟨δ, hδ, ?_⟩
  intro P hP i x hx y hy
  have hleft := (endpoints P).2.2 _
    (Finset.mem_image.mpr ⟨i.castSucc, Finset.mem_univ _, rfl⟩)
  have hright := (endpoints P).2.2 _
    (Finset.mem_image.mpr ⟨i.succ, Finset.mem_univ _, rfl⟩)
  have hxi : x ∈ Set.Icc a b := ⟨hleft.1.trans hx.1, hx.2.trans hright.2⟩
  have hyi : y ∈ Set.Icc a b := ⟨hleft.1.trans hy.1, hy.2.trans hright.2⟩
  have hxy : dist x y < δ := by
    rw [Real.dist_eq, abs_lt]
    have hm := cellLength_le_mesh P i
    change P.point i.succ - P.point i.castSucc ≤ mesh P at hm
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  simpa only [dist_eq_norm] using (hd x hxi y hyi hxy).le

/-- There are arbitrarily fine partitions also on a singleton interval. -/
theorem exists_mesh_lt {a b : ℝ} (hab : a ≤ b) {δ : ℝ} (hδ : 0 < δ) :
    ∃ P : Partition a b, mesh P < δ := by
  rcases lt_or_eq_of_le hab with hab | rfl
  · obtain ⟨P, _, hP⟩ := arbitrarily_fine hab δ hδ
    exact ⟨P, hP⟩
  · exact ⟨emptyPartition a, by simpa only [(degenerate_all a (emptyPartition a)).2] using hδ⟩

/-- Continuous integrands give refinement-Cauchy sums. The tolerance uses V+1,
so the proof includes V=0. -/
theorem continuous_bv_refinementCauchy {a b : ℝ} (hab : a ≤ b)
    (f : ℝ → E) (α : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b))
    (hα : BV.HasBoundedVariation α a b) : RefinementCauchy a b f α := by
  intro ε hε
  let V := (BV.totalVariation α a b).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  let η := ε / (4 * (V+1))
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hd⟩ := continuous_cell_oscillation f hf hη
  obtain ⟨P₀, hP₀⟩ := exists_mesh_lt hab hδ
  obtain ⟨t₀⟩ := tags_exist P₀
  refine ⟨P₀, ?_⟩
  intro P hP t Q hQ u
  have h₁ := refinement_estimate P₀ P hP t₀ t f α hα hη.le (hd P₀ hP₀)
  have h₂ := refinement_estimate P₀ Q hQ t₀ u f α hα hη.le (hd P₀ hP₀)
  have ht : ‖taggedSum P t f α - taggedSum Q u f α‖ ≤
      ‖taggedSum P t f α - taggedSum P₀ t₀ f α‖ +
      ‖taggedSum P₀ t₀ f α - taggedSum Q u f α‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le
      (taggedSum P t f α - taggedSum P₀ t₀ f α)
      (taggedSum P₀ t₀ f α - taggedSum Q u f α)
  rw [norm_sub_rev (taggedSum P t f α) (taggedSum P₀ t₀ f α)] at ht
  have hsmall : 2 * η * V < ε := by
    dsimp [η]
    have hp : 0 < 4 * (V+1) := by positivity
    have heq := (div_mul_cancel₀ ε (ne_of_gt hp))
    nlinarith
  exact ht.trans_lt (lt_of_le_of_lt (add_le_add h₁ h₂) (by
    change η * V + η * V < ε
    linarith))

/-- A refinement limit of a continuous integrand is also its unrestricted mesh
limit, even when the BV integrator jumps. -/
theorem meshLimit_of_refinementLimit {a b : ℝ}
    (f : ℝ → E) (α : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b))
    (hα : BV.HasBoundedVariation α a b) {I : E}
    (hI : RefinementLimit a b f α I) :
    Specs.SingleVariableAnalysis.Ch15.RsExistence.meshLimit a b f α I := by
  intro ε hε
  let V := (BV.totalVariation α a b).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  let η := ε / (4 * (V+1))
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hd⟩ := continuous_cell_oscillation f hf hη
  obtain ⟨P₀, hP₀⟩ := hI (ε/2) (half_pos hε)
  refine ⟨δ, hδ, ?_⟩
  intro P hP t
  obtain ⟨Q, _, hQP, hQ₀⟩ := common_refinement P P₀
  obtain ⟨u⟩ := tags_exist Q
  have h₁ := refinement_estimate P Q hQP t u f α hα hη.le (hd P hP)
  have h₂ := hP₀ Q hQ₀ u
  have ht : ‖taggedSum P t f α - I‖ ≤
      ‖taggedSum P t f α - taggedSum Q u f α‖ + ‖taggedSum Q u f α - I‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le
      (taggedSum P t f α - taggedSum Q u f α) (taggedSum Q u f α - I)
  have hsmall : η * V < ε/2 := by
    dsimp [η]
    have hp : 0 < 4 * (V+1) := by positivity
    have heq := (div_mul_cancel₀ ε (ne_of_gt hp))
    nlinarith
  exact ht.trans_lt (by linarith)

/-- Passing the finite tagged-sum estimate to any refinement limit. -/
theorem norm_refinementLimit_le {a b : ℝ} (f : ℝ → E) (α : ℝ → ℝ)
    (hα : BV.HasBoundedVariation α a b) {I : E} (hI : RefinementLimit a b f α I)
    {M : ℝ} (hM : 0 ≤ M) (hf : ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ M) :
    ‖I‖ ≤ M * (BV.totalVariation α a b).toReal := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨P, hP⟩ := hI ε hε
  obtain ⟨t⟩ := tags_exist P
  have hs := hP P (refinement_laws P P P).1 t
  have hb := norm_taggedSum_le P t f α hα hM hf
  have ht : ‖I‖ ≤ ‖taggedSum P t f α‖ + ‖taggedSum P t f α - I‖ := by
    calc
      ‖I‖ = ‖(I - taggedSum P t f α) + taggedSum P t f α‖ := by rw [sub_add_cancel]
      _ ≤ ‖I - taggedSum P t f α‖ + ‖taggedSum P t f α‖ := norm_add_le _ _
      _ = ‖taggedSum P t f α‖ + ‖taggedSum P t f α - I‖ := by
        rw [norm_sub_rev I]
        exact add_comm _ _
  linarith

/-- The generic complete-space proof, specialized below to the two source scalars. -/
theorem continuous_bv_integral [CompleteSpace E] {a b : ℝ} (hab : a ≤ b)
    (f : ℝ → E) (α : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b))
    (hα : BV.HasBoundedVariation α a b) :
    ∃ I : E, HasIntegral a b f α I ∧
      ‖I‖ ≤ Specs.SingleVariableAnalysis.Ch15.RsExistence.supNorm a b f *
        (BV.totalVariation α a b).toReal ∧
      Specs.SingleVariableAnalysis.Ch15.RsExistence.meshLimit a b f α I := by
  have hc := continuous_bv_refinementCauchy hab f α hf hα
  have complete : ∀ s : ℕ → E,
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ‖s n-s m‖ < ε) →
      ∃ I : E, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ‖s n-I‖ < ε := by
    intro s hs
    have hcs : CauchySeq s := Metric.cauchySeq_iff.mpr (by
      simpa only [dist_eq_norm, norm_sub_rev] using hs)
    obtain ⟨I, hI⟩ := cauchySeq_tendsto_of_complete hcs
    exact ⟨I, by simpa only [dist_eq_norm] using Metric.tendsto_atTop.mp hI⟩
  obtain ⟨I, hI⟩ := exists_refinementLimit_of_cauchy complete hc
  have hbdd : BddAbove ((fun x => ‖f x‖) '' Set.Icc a b) :=
    isCompact_Icc.bddAbove_image hf.norm
  have hM (x : ℝ) (hx : x ∈ Set.Icc a b) :
      ‖f x‖ ≤ Specs.SingleVariableAnalysis.Ch15.RsExistence.supNorm a b f :=
    le_csSup hbdd (Set.mem_image_of_mem _ hx)
  have hM0 : 0 ≤ Specs.SingleVariableAnalysis.Ch15.RsExistence.supNorm a b f :=
    (norm_nonneg (f a)).trans (hM a (Set.left_mem_Icc.mpr hab))
  refine ⟨I, ?_, norm_refinementLimit_le f α hα hI hM0 hM,
    meshLimit_of_refinementLimit f α hf hα hI⟩
  exact (integral_iff_of_le a b hab f α I).mpr
    ⟨⟨_, hM⟩, boundedOn_of_bv hab α hα, hI⟩

theorem real_continuous_bv_integral :
    Specs.SingleVariableAnalysis.Ch15.RsExistence.realExistence := by
  intro a b hab f α hf hα
  exact continuous_bv_integral hab f α hf hα

theorem complex_continuous_bv_integral :
    Specs.SingleVariableAnalysis.Ch15.RsExistence.complexExistence := by
  intro a b hab f α hf hα
  exact continuous_bv_integral hab f α hf hα

end SingleVariableAnalysis.Stieltjes
