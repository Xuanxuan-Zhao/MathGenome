import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.AP.AdjacentTensorDifferences
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.AP.EnfloCoordinates
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.AP.SmallWalshDifference
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module
import Mathlib.Tactic.Abel

noncomputable section
open scoped BigOperators TensorProduct ENNReal
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
namespace ExpandedFA.AP.AdjacentTensorDifferences
open EnfloSpace.Spec AlgebraicRankOneTensorsSpec
open EnfloCoordinates
open ExpandedFA.AP.AdjacentTensorDifferences.Spec

/- The normed group instances fix the additive structures used in the algebraic
 tensor product; raw subtype monoid inference otherwise selects a different
 structure before its additive inverse is requested. -/
local instance (D : IncidenceData) : AddCommMonoid (X D) :=
  (inferInstance : NormedAddCommGroup (X D)).toAddCommMonoid
local instance (D : IncidenceData) : AddCommGroup (X D) :=
  (inferInstance : NormedAddCommGroup (X D)).toAddCommGroup
local instance (D : IncidenceData) : AddCommMonoid (X D →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (X D →L[ℝ] ℝ)).toAddCommMonoid
local instance (D : IncidenceData) : AddCommGroup (X D →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (X D →L[ℝ] ℝ)).toAddCommGroup

lemma nu_smul_sum_le {D : IncidenceData} {I : Type*} (A : Finset I)
    (c : I → ℝ) (f : I → X D →L[ℝ] ℝ) (x : I → X D) :
    nu (∑ i ∈ A, c i • (f i ⊗ₜ[ℝ] x i)) ≤
      ∑ i ∈ A, |c i| * (‖f i‖ * ‖x i‖) := by
  simp_rw [TensorProduct.smul_tmul']
  apply le_trans (nu_sum_tmul_le A (fun i => c i • f i) x)
  apply Finset.sum_le_sum
  intro i hi
  calc
    _ ≤ (‖c i‖ * ‖f i‖) * ‖x i‖ :=
      mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_smul_le _ _) (norm_nonneg _)
    _ = _ := by rw [Real.norm_eq_abs, mul_assoc]

lemma nu_sum_le {D : IncidenceData} {I : Type*} (A : Finset I)
    (v : I → Tensor ℝ (X D)) : nu (∑ i ∈ A, v i) ≤ ∑ i ∈ A, nu (v i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using (projectiveInfimum_zero (𝕜 := ℝ) (X := X D)).le
  | @insert i A hi ih =>
    simp only [Finset.sum_insert hi]
    exact (projectiveInfimum_add_le _ _).trans (add_le_add_right ih _)

lemma nu_neg {D : IncidenceData} (v : Tensor ℝ (X D)) : nu (-v) = nu v := by
  have hle (w : Tensor ℝ (X D)) : nu (-w) ≤ nu w := by
    have := tensor_representable w
    apply le_ciInf
    intro r
    let l := r.val.map (fun p => (-p.1, p.2))
    have hl : tensorSum l = -w := by
      rw [← r.property]
      change tensorSum (r.val.map (fun p => (-p.1, p.2))) = -tensorSum r.val
      have hh (l : List ((X D →L[ℝ] ℝ) × X D)) :
          tensorSum (l.map (fun p => (-p.1, p.2))) = -tensorSum l := by
        induction l with
        | nil => simp
        | cons p l ih =>
          simp only [List.map_cons, tensorSum_cons, TensorProduct.neg_tmul, ih, neg_add_rev]
          exact add_comm _ _
      exact hh _
    have hc : cost l = cost r.val := by
      unfold cost l
      simp only [List.map_map]
      change (r.val.map (fun p => ‖-p.1‖ * ‖p.2‖)).sum =
        (r.val.map (fun p => ‖p.1‖ * ‖p.2‖)).sum
      simp only [norm_neg]
    rw [← hl, ← hc]
    exact projectiveInfimum_le_cost l
  exact le_antisymm (hle v) (by simpa using hle (-v))

lemma balance_tensor_identity (D : IncidenceData) (m : ℕ) :
    EnfloCoordinates.Spec.u D m -
      (k D (m + 1) : ℝ)⁻¹ • ∑ j, lowerTensor D m j =
    ∑ e : Symbol D m,
      (1 / ((k D m : ℝ) * t D m) -
        (Incidence.incidenceCount (incident D m) e : ℝ) /
          ((k D (m + 1) : ℝ) * t D (m + 1))) •
        (EnfloCoordinates.coordinate D ⟨m, e⟩ ⊗ₜ[ℝ] generatorX D m e) := by
  classical
  let v := fun e : Symbol D m => EnfloCoordinates.coordinate D ⟨m, e⟩ ⊗ₜ[ℝ] generatorX D m e
  have hcount (e : Symbol D m) :
      (∑ j : Row D (m + 1), if e ∈ incident D m j then v e else 0) =
        (Incidence.incidenceCount (incident D m) e : ℝ) • v e := by
    simp [Incidence.incidenceCount, ← Finset.sum_filter, ← Nat.cast_smul_eq_nsmul ℝ]
  have hs : (∑ j : Row D (m + 1), ∑ e ∈ incident D m j, v e) =
      ∑ e : Symbol D m, (Incidence.incidenceCount (incident D m) e : ℝ) • v e := by
    have hh (j : Row D (m + 1)) : (∑ e ∈ incident D m j, v e) =
        ∑ e : Symbol D m, if e ∈ incident D m j then v e else 0 := by
      rw [← Finset.sum_filter]
      congr 1
      ext e
      simp
    simp_rw [hh]
    rw [Finset.sum_comm]
    simp_rw [hcount]
  change (((k D m : ℝ) * t D m)⁻¹ • (∑ e, v e) -
    (k D (m + 1) : ℝ)⁻¹ •
      (∑ j, (t D (m + 1) : ℝ)⁻¹ • (∑ e ∈ incident D m j, v e)) : Tensor ℝ (X D)) = _
  rw [← Finset.smul_sum, hs]
  simp only [Finset.smul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e he
  simp only [smul_smul, div_eq_mul_inv, mul_inv_rev]
  module

theorem balance_bound : BalanceBound := by
  intro D m
  rw [balance_tensor_identity]
  calc
    _ ≤ ∑ e : Symbol D m,
        |1 / ((k D m : ℝ) * t D m) -
          (Incidence.incidenceCount (incident D m) e : ℝ) /
            ((k D (m + 1) : ℝ) * t D (m + 1))| *
          (‖EnfloCoordinates.coordinate D ⟨m, e⟩‖ * ‖generatorX D m e‖) := nu_smul_sum_le _ _ _ _
    _ = ∑ e : Symbol D m,
        |1 / ((k D m : ℝ) * t D m) -
          (Incidence.incidenceCount (incident D m) e : ℝ) /
            ((k D (m + 1) : ℝ) * t D (m + 1))| := by
      apply Finset.sum_congr rfl
      intro e he
      rw [EnfloCoordinates.coordinate_sharp_norm D ⟨m, e⟩, mul_one]
    _ ≤ 1 / (n D (m + 1) : ℝ) := (D.properties (m + 1) (by omega)).2.2.2

lemma upper_average (D : IncidenceData) (m : ℕ) :
    (k D (m + 1) : ℝ)⁻¹ • ∑ j, upperTensor D m j =
      EnfloCoordinates.Spec.u D (m + 1) := by
  classical
  simp only [upperTensor, ← Finset.smul_sum, smul_smul, EnfloCoordinates.Spec.u,
    mul_inv_rev]
  rw [mul_comm]
  congr 1
  change (∑ j : Row D (m + 1), ∑ p : Fin (t D (m + 1)),
    EnfloCoordinates.coordinate D ⟨m + 1, (j, p)⟩ ⊗ₜ[ℝ] generatorX D (m + 1) (j, p)) = _
  exact (Fintype.sum_prod_type (fun e : Row D (m + 1) × Fin (t D (m + 1)) =>
    (EnfloCoordinates.coordinate D ⟨m + 1, e⟩ ⊗ₜ[ℝ] generatorX D (m + 1) e :
      Tensor ℝ (X D)))).symm

lemma rowEvaluation_apply (D : IncidenceData) (m : ℕ) (j : Row D (m + 1))
    (a : Walsh.Cube (n D (m + 1))) (x : X D) :
    rowEvaluation D m j a x = x.val (m + 1) (j, a) := rfl

lemma rowEvaluation_norm (D : IncidenceData) (m : ℕ) (j : Row D (m + 1))
    (a : Walsh.Cube (n D (m + 1))) : ‖rowEvaluation D m j a‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [one_mul, rowEvaluation_apply]
  exact ((x.val (m + 1)).norm_coe_le_norm (j, a)).trans
    (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) x.val (m + 1))

lemma averaged_rowEvaluation (D : IncidenceData) (m : ℕ) (j : Row D (m + 1))
    (S : Finset (Fin (2 * n D (m + 1)))) :
    (Fintype.card (Walsh.Cube (n D (m + 1))) : ℝ)⁻¹ •
      ∑ a, Walsh.character (n D (m + 1)) S a • rowEvaluation D m j a =
    (EnfloCoordinates.Spec.rowFourier D (m + 1) j S).comp
      ((lp.evalCLM ℝ (Summand D) 2 (m + 1)).comp (closedSpan D).subtypeL) := by
  ext x
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    rowEvaluation_apply, ContinuousLinearMap.comp_apply, rowFourier_apply, smul_eq_mul]
  rfl

lemma averaged_lower (D : IncidenceData) (m : ℕ) (j : Row D (m + 1))
    (e : ↥(incident D m j)) :
    (Fintype.card (Walsh.Cube (n D (m + 1))) : ℝ)⁻¹ •
      ∑ a, Walsh.character (n D (m + 1)) (lowerLabels D m j e).val a •
        rowEvaluation D m j a = EnfloCoordinates.coordinate D ⟨m, e.val⟩ := by
  rw [averaged_rowEvaluation]
  ext x
  exact lower_agrees D m j e x

lemma averaged_upper (D : IncidenceData) (m : ℕ) (j : Row D (m + 1))
    (p : Fin (t D (m + 1))) :
    (Fintype.card (Walsh.Cube (n D (m + 1))) : ℝ)⁻¹ •
      ∑ a, Walsh.character (n D (m + 1)) (upperLabels D (m + 1) p).val a •
        rowEvaluation D m j a = EnfloCoordinates.coordinate D ⟨m + 1, (j, p)⟩ := by
  exact averaged_rowEvaluation D m j _

lemma average_tmul_sum {D : IncidenceData} {A I : Type*} [Fintype A] [Fintype I]
    (c d : ℝ) (f : A → X D →L[ℝ] ℝ) (b : I → A → ℝ) (x : I → X D) :
    c • ∑ a, f a ⊗ₜ[ℝ] (d • ∑ i, b i a • x i) =
      d • ∑ i, (c • ∑ a, b i a • f a) ⊗ₜ[ℝ] x i := by
  simp only [TensorProduct.tmul_smul, TensorProduct.tmul_sum,
    ← TensorProduct.smul_tmul', TensorProduct.sum_tmul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  ring

theorem row_representation : RowRepresentation := by
  classical
  intro D m j
  have hsplit : (Fintype.card (Walsh.Cube (n D (m + 1))) : ℝ)⁻¹ •
      ∑ a, rowEvaluation D m j a ⊗ₜ[ℝ] rowVector D m j a =
    (t D (m + 1) : ℝ)⁻¹ •
      ((∑ e : ↥(incident D m j), (EnfloCoordinates.coordinate D ⟨m, e.val⟩ ⊗ₜ[ℝ]
        generatorX D m e.val : Tensor ℝ (X D))) -
       (∑ p : Fin (t D (m + 1)), (EnfloCoordinates.coordinate D ⟨m + 1, (j, p)⟩ ⊗ₜ[ℝ]
         generatorX D (m + 1) (j, p) : Tensor ℝ (X D)))) := by
    unfold rowVector
    simp_rw [smul_sub, TensorProduct.tmul_sub, Finset.sum_sub_distrib]
    rw [smul_sub, average_tmul_sum, average_tmul_sum]
    simp_rw [averaged_lower, averaged_upper]
  rw [hsplit, smul_sub]
  simp only [lowerTensor, upperTensor]
  congr 2
  exact (Finset.sum_coe_sort _ _).symm

/-- The one-symbol-per-row condition as a uniqueness statement. -/
lemma incident_row_unique (D : IncidenceData) (m : ℕ) (j : Row D (m + 1))
    (e d : Symbol D m) (he : e ∈ incident D m j) (hd : d ∈ incident D m j)
    (hrow : e.1 = d.1) : e = d := by
  have hc := (D.properties (m + 1) (by omega)).2.2.1 j e.1
  exact Finset.card_le_one.mp hc e (Finset.mem_filter.mpr ⟨he, rfl⟩) d (Finset.mem_filter.mpr ⟨hd, hrow.symm⟩)

lemma norm_sum_le_one_of_unique {I V : Type*} [Fintype I] [NormedAddCommGroup V]
    (P : I → Prop) (v : I → V)
    (hunique : ∀ i j, P i → P j → i = j)
    (hbound : ∀ i, P i → ‖v i‖ ≤ 1) (hzero : ∀ i, ¬P i → v i = 0) :
    ‖∑ i, v i‖ ≤ 1 := by
  classical
  by_cases hex : ∃ i, P i
  · obtain ⟨i, hi⟩ := hex
    rw [Finset.sum_eq_single i]
    · exact hbound i hi
    · intro j hj hji
      exact hzero j (fun hj => hji (hunique j i hj hi))
    · simp
  · rw [Finset.sum_eq_zero (fun i _ => hzero i (fun hi => hex ⟨i, hi⟩)), norm_zero]
    norm_num

lemma lower_own_norm (D : IncidenceData) (m : ℕ) (j : Row D (m + 1))
    (c : ↥(incident D m j) → ℝ) (hc : ∀ e, ‖c e‖ = 1) :
    ‖∑ e : ↥(incident D m j), c e • ownBlock D m e.val‖ ≤ 1 := by
  classical
  apply (ContinuousMap.norm_le _ (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro p
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  apply norm_sum_le_one_of_unique (fun e : ↥(incident D m j) => e.val.1 = p.1)
  · intro e d he hd
    exact Subtype.ext (incident_row_unique D m j e d e.property d.property (he.trans hd.symm))
  · intro e he
    simp [ownBlock, he, hc, norm_mul, ← Real.norm_eq_abs, character_norm]
  · intro e he
    simp [ownBlock, Ne.symm he]

lemma upper_next_norm (D : IncidenceData) (m : ℕ) (j : Row D m)
    (c : Fin (t D m) → ℝ) (hc : ∀ p, ‖c p‖ = 1) :
    ‖∑ p : Fin (t D m), c p • nextBlock D m (j, p)‖ ≤ 1 := by
  classical
  apply (ContinuousMap.norm_le _ (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro p
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  apply norm_sum_le_one_of_unique (fun b : Fin (t D m) => (j, b) ∈ incident D m p.1)
  · intro b d hb hd
    exact congrArg Prod.snd (incident_row_unique D m p.1 (j, b) (j, d) hb hd rfl)
  · intro b hb
    simp [nextBlock, hb, norm_mul, hc, ← Real.norm_eq_abs, character_norm]
  · intro b hb
    simp [nextBlock, hb]

lemma ownBlock_apply (D : IncidenceData) (m : ℕ) (e : Symbol D m)
    (r : Row D m) (a : Walsh.Cube (n D m)) :
    ownBlock D m e (r, a) = if r = e.1 then
      Walsh.character (n D m) (upperLabels D m e.2).val a else 0 := rfl

lemma nextBlock_apply (D : IncidenceData) (m : ℕ) (e : Symbol D m)
    (r : Row D (m + 1)) (a : Walsh.Cube (n D (m + 1))) :
    nextBlock D m e (r, a) = if h : e ∈ incident D m r then
      Walsh.character (n D (m + 1)) (lowerLabels D m r ⟨e, h⟩).val a else 0 := rfl

/-- The three blocks of the explicit representing vector. -/
def previousBlock (D : IncidenceData) (m : ℕ) (j : Row D (m + 1))
    (a : Walsh.Cube (n D (m + 1))) : Summand D m :=
  (t D (m + 1) : ℝ)⁻¹ • ∑ e : ↥(incident D m j),
    Walsh.character (n D (m + 1)) (lowerLabels D m j e).val a • ownBlock D m e.val

def middleBlock (D : IncidenceData) (m : ℕ) (j : Row D (m + 1))
    (a : Walsh.Cube (n D (m + 1))) : Summand D (m + 1) :=
  (t D (m + 1) : ℝ)⁻¹ •
    ((∑ e : ↥(incident D m j),
      Walsh.character (n D (m + 1)) (lowerLabels D m j e).val a • nextBlock D m e.val) -
     ∑ p : Fin (t D (m + 1)),
      Walsh.character (n D (m + 1)) (upperLabels D (m + 1) p).val a •
        ownBlock D (m + 1) (j, p))

def followingBlock (D : IncidenceData) (m : ℕ) (j : Row D (m + 1))
    (a : Walsh.Cube (n D (m + 1))) : Summand D (m + 1 + 1) :=
  -(t D (m + 1) : ℝ)⁻¹ • ∑ p : Fin (t D (m + 1)),
    Walsh.character (n D (m + 1)) (upperLabels D (m + 1) p).val a •
      nextBlock D (m + 1) (j, p)

lemma previousBlock_norm (D : IncidenceData) (m : ℕ) (j : Row D (m + 1))
    (a : Walsh.Cube (n D (m + 1))) :
    ‖previousBlock D m j a‖ ≤ (t D (m + 1) : ℝ)⁻¹ := by
  rw [previousBlock, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Nat.cast_nonneg _)]
  exact mul_le_of_le_one_right (by positivity)
    (lower_own_norm D m j _ (fun e => character_norm _ _ _))

lemma followingBlock_norm (D : IncidenceData) (m : ℕ) (j : Row D (m + 1))
    (a : Walsh.Cube (n D (m + 1))) :
    ‖followingBlock D m j a‖ ≤ (t D (m + 1) : ℝ)⁻¹ := by
  rw [followingBlock, norm_smul, norm_neg, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Nat.cast_nonneg _)]
  exact mul_le_of_le_one_right (by positivity)
    (upper_next_norm D (m + 1) j _ (fun p => character_norm _ _ _))

lemma middleBlock_distinguished (D : IncidenceData) (m : ℕ) (j : Row D (m + 1))
    (a b : Walsh.Cube (n D (m + 1))) :
    middleBlock D m j a (j, b) =
      Walsh.difference (n D (m + 1)) (fun z => xor (a z) (b z)) := by
  classical
  have hl := Equiv.sum_comp (lowerLabels D m j)
    (fun S => Walsh.character (n D (m + 1)) S.val a *
      Walsh.character (n D (m + 1)) S.val b)
  have hu := Equiv.sum_comp (upperLabels D (m + 1))
    (fun S => Walsh.character (n D (m + 1)) S.val a *
      Walsh.character (n D (m + 1)) S.val b)
  simp only [middleBlock, ContinuousMap.coe_smul, ContinuousMap.coe_sub,
    ContinuousMap.coe_sum, Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, smul_eq_mul,
    nextBlock_apply, ownBlock_apply]
  simp only [show ∀ e : ↥(incident D m j), e.val ∈ incident D m j from fun e => e.property,
    ↓reduceDIte, ↓reduceIte]
  rw [hl, hu]
  simp_rw [← WalshBlocks.character_xor]
  rw [Finset.sum_coe_sort (Walsh.level (n D (m + 1)) (n D (m + 1) - 1))
      (fun S => Walsh.character (n D (m + 1)) S (fun z => xor (a z) (b z))),
    Finset.sum_coe_sort (Walsh.level (n D (m + 1)) (n D (m + 1) + 1))
      (fun S => Walsh.character (n D (m + 1)) S (fun z => xor (a z) (b z)))]
  simp only [Walsh.difference, Walsh.levelSum, Pi.smul_apply, Pi.sub_apply,
    Finset.sum_apply, smul_eq_mul]
  rfl

lemma middleBlock_other (D : IncidenceData) (m : ℕ) (j r : Row D (m + 1))
    (hr : r ≠ j) (a b : Walsh.Cube (n D (m + 1))) :
    ‖middleBlock D m j a (r, b)‖ ≤ 1 / (2 * (n D (m + 1) : ℝ)) := by
  classical
  let c : ↥(incident D m j) → ℝ := fun e =>
    Walsh.character (n D (m + 1)) (lowerLabels D m j e).val a
  have hb (e : ↥(incident D m j)) :
      ‖c e * nextBlock D m e.val (r, b)‖ = if e.val ∈ incident D m r then 1 else 0 := by
    dsimp [c]
    by_cases he : e.val ∈ incident D m r <;>
      simp [nextBlock, he, ← Real.norm_eq_abs, character_norm]
  have hcard : (∑ e : ↥(incident D m j), if e.val ∈ incident D m r then (1 : ℝ) else 0) =
      ((incident D m j ∩ incident D m r).card : ℝ) := by
    calc
      _ = ∑ e ∈ incident D m j, if e ∈ incident D m r then (1 : ℝ) else 0 :=
        Finset.sum_coe_sort (incident D m j) (fun e => if e ∈ incident D m r then (1 : ℝ) else 0)
      _ = _ := by simp
  have hintersection : ((incident D m j ∩ incident D m r).card : ℝ) ≤
      (t D (m + 1) : ℝ) / (2 * n D (m + 1)) :=
    (D.properties (m + 1) (by omega)).2.1 j r hr.symm
  have ht : 0 < (t D (m + 1) : ℝ) :=
    Nat.cast_pos.mpr (BalancedIncidenceSets.levelSize_pos D.offset (m + 1 + 1))
  have hn : 0 < (n D (m + 1) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by omega : 0 < 2)
      (D.dimension_ge_two (m + 1 + 1) (by omega))
  simp only [middleBlock, ContinuousMap.coe_smul, ContinuousMap.coe_sub,
    ContinuousMap.coe_sum, Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, smul_eq_mul]
  change ‖(t D (m + 1) : ℝ)⁻¹ *
    ((∑ e : ↥(incident D m j), c e * nextBlock D m e.val (r, b)) -
     ∑ p : Fin (t D (m + 1)), Walsh.character (n D (m + 1))
       (upperLabels D (m + 1) p).val a * ownBlock D (m + 1) (j, p) (r, b))‖ ≤ _
  simp only [ownBlock_apply, hr, ↓reduceIte, mul_zero, Finset.sum_const_zero, sub_zero]
  rw [norm_mul, norm_inv, Real.norm_natCast]
  calc
    _ ≤ (t D (m + 1) : ℝ)⁻¹ *
        ∑ e : ↥(incident D m j), ‖c e * nextBlock D m e.val (r, b)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr ht.le)
    _ = (t D (m + 1) : ℝ)⁻¹ * ((incident D m j ∩ incident D m r).card : ℝ) := by
      simp_rw [hb]
      rw [hcard]
    _ ≤ (t D (m + 1) : ℝ)⁻¹ * ((t D (m + 1) : ℝ) / (2 * n D (m + 1))) :=
      mul_le_mul_of_nonneg_left hintersection (inv_nonneg.mpr ht.le)
    _ = 1 / (2 * (n D (m + 1) : ℝ)) := by field_simp [ht.ne']

lemma middleBlock_norm (D : IncidenceData) (m : ℕ) (j : Row D (m + 1))
    (a : Walsh.Cube (n D (m + 1))) :
    ‖middleBlock D m j a‖ ≤ 2 / (n D (m + 1) : ℝ) := by
  have hn : 0 < (n D (m + 1) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by omega : 0 < 2)
      (D.dimension_ge_two (m + 1 + 1) (by omega))
  apply (ContinuousMap.norm_le _ (by positivity : (0 : ℝ) ≤ 2 / (n D (m + 1) : ℝ))).mpr
  rintro ⟨r, b⟩
  by_cases hr : r = j
  · subst r
    rw [middleBlock_distinguished]
    calc
      _ ≤ ‖Walsh.difference (n D (m + 1))‖ := norm_le_pi_norm _ _
      _ = _ := SmallWalshDifference.exact_norm _
        (D.dimension_ge_two (m + 1 + 1) (by omega))
  · exact (middleBlock_other D m j r hr a b).trans (by
      apply (div_le_div_iff₀ (by positivity : 0 < 2 * (n D (m + 1) : ℝ)) hn).mpr
      nlinarith)

lemma rowVector_blocks (D : IncidenceData) (m : ℕ) (j : Row D (m + 1))
    (a : Walsh.Cube (n D (m + 1))) :
    (rowVector D m j a).val =
      lp.single 2 m (previousBlock D m j a) +
        lp.single 2 (m + 1) (middleBlock D m j a) +
          lp.single 2 (m + 1 + 1) (followingBlock D m j a) := by
  classical
  apply lp.ext
  funext b
  simp only [rowVector, Submodule.coe_smul, Submodule.coe_sub, Submodule.coe_sum,
    generatorX]
  change ((t D (m + 1) : ℝ)⁻¹ •
    ((∑ e : ↥(incident D m j), Walsh.character (n D (m + 1))
      (lowerLabels D m j e).val a • generator D m e.val) -
     ∑ p : Fin (t D (m + 1)), Walsh.character (n D (m + 1))
      (upperLabels D (m + 1) p).val a • generator D (m + 1) (j, p))) b = _
  simp only [lp.coeFn_smul, lp.coeFn_sub, lp.coeFn_sum, Pi.smul_apply, Pi.sub_apply,
    Finset.sum_apply, lp.coeFn_add, Pi.add_apply]
  by_cases hb : b = m
  · subst b
    simp only [generator_block_own, EnfloSpace.generator_other D (m + 1) _ m
      (by omega) (by omega), smul_zero, Finset.sum_const_zero, sub_zero,
      lp.single_apply_self, lp.single_apply_ne 2 (m + 1) _ (j := m) (by omega),
      lp.single_apply_ne 2 (m + 1 + 1) _ (j := m) (by omega), add_zero, previousBlock]
  · by_cases hb' : b = m + 1
    · subst b
      simp only [generator_block_next, generator_block_own,
        lp.single_apply_self, lp.single_apply_ne 2 m _ (j := m + 1) (by omega),
        lp.single_apply_ne 2 (m + 1 + 1) _ (j := m + 1) (by omega), zero_add, add_zero, middleBlock]
    · by_cases hb'' : b = m + 1 + 1
      · subst b
        simp only [EnfloSpace.generator_other D m _ (m + 1 + 1) (by omega) (by omega),
          generator_block_next, smul_zero, Finset.sum_const_zero, zero_sub,
          lp.single_apply_self, lp.single_apply_ne 2 m _ (j := m + 1 + 1) (by omega),
          lp.single_apply_ne 2 (m + 1) _ (j := m + 1 + 1) (by omega), zero_add, followingBlock, neg_smul]
        exact smul_neg _ _
      · simp only [EnfloSpace.generator_other D m _ b hb hb',
          EnfloSpace.generator_other D (m + 1) _ b hb' hb'', smul_zero,
          Finset.sum_const_zero, sub_zero, lp.single_apply_ne 2 m _ hb,
          lp.single_apply_ne 2 (m + 1) _ hb',
          lp.single_apply_ne 2 (m + 1 + 1) _ hb'', add_zero]

lemma dimension_le_size (D : IncidenceData) (m : ℕ) : n D m ≤ t D m := by
  have hn : 2 ≤ n D m := D.dimension_ge_two (m + 1) (by omega)
  have h := SmallWalshDifference.choose_mono_to_middle
    (N := 2 * n D m) (r := 1) (s := n D m - 1) (by omega) (by omega)
  simp only [Nat.choose_one_right] at h
  exact (by omega : n D m ≤ 2 * n D m).trans h

theorem row_vector_bound : RowVectorBound := by
  intro D m j a
  have hn : 0 < (n D (m + 1) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by omega : 0 < 2)
      (D.dimension_ge_two (m + 1 + 1) (by omega))
  have ht : (n D (m + 1) : ℝ) ≤ t D (m + 1) := by exact_mod_cast dimension_le_size D (m + 1)
  have hinv : (t D (m + 1) : ℝ)⁻¹ ≤ (n D (m + 1) : ℝ)⁻¹ := inv_anti₀ hn ht
  change ‖(rowVector D m j a).val‖ ≤ _
  rw [rowVector_blocks]
  calc
    _ ≤ ‖lp.single 2 m (previousBlock D m j a)‖ +
        ‖lp.single 2 (m + 1) (middleBlock D m j a)‖ +
        ‖lp.single 2 (m + 1 + 1) (followingBlock D m j a)‖ := norm_add₃_le
    _ = ‖previousBlock D m j a‖ + ‖middleBlock D m j a‖ + ‖followingBlock D m j a‖ := by
      simp only [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
    _ ≤ (t D (m + 1) : ℝ)⁻¹ + 2 / (n D (m + 1) : ℝ) + (t D (m + 1) : ℝ)⁻¹ :=
      add_le_add (add_le_add (previousBlock_norm D m j a) (middleBlock_norm D m j a))
        (followingBlock_norm D m j a)
    _ ≤ 4 / (n D (m + 1) : ℝ) := by rw [div_eq_mul_inv, div_eq_mul_inv]; linarith

lemma nu_average_tmul_le {D : IncidenceData} {I : Type} [Fintype I] [Nonempty I]
    (f : I → X D →L[ℝ] ℝ) (x : I → X D) (C : ℝ)
    (hf : ∀ i, ‖f i‖ ≤ 1) (hx : ∀ i, ‖x i‖ ≤ C) :
    nu ((Fintype.card I : ℝ)⁻¹ • ∑ i, f i ⊗ₜ[ℝ] x i) ≤ C := by
  rw [Finset.smul_sum]
  calc
    _ ≤ ∑ i : I, |(Fintype.card I : ℝ)⁻¹| * (‖f i‖ * ‖x i‖) :=
      nu_smul_sum_le _ _ _ _
    _ ≤ ∑ _i : I, (Fintype.card I : ℝ)⁻¹ * C := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_of_nonneg (by positivity : 0 ≤ (Fintype.card I : ℝ)⁻¹)]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (mul_le_mul_of_nonneg_right (hf i) (norm_nonneg _)).trans
        (by simpa using hx i)
    _ = C := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero (α := I)), one_mul]

theorem row_bound : RowBound := by
  intro D m j
  rw [row_representation D m j]
  exact nu_average_tmul_le _ _ _ (rowEvaluation_norm D m j) (row_vector_bound D m j)

lemma averaged_row_identity (D : IncidenceData) (m : ℕ) :
    (k D (m + 1) : ℝ)⁻¹ • (∑ j, lowerTensor D m j) - EnfloCoordinates.Spec.u D (m + 1) =
      (Fintype.card (Row D (m + 1) × Walsh.Cube (n D (m + 1))) : ℝ)⁻¹ •
        ∑ p : Row D (m + 1) × Walsh.Cube (n D (m + 1)),
          rowEvaluation D m p.1 p.2 ⊗ₜ[ℝ] rowVector D m p.1 p.2 := by
  classical
  rw [← upper_average D m]
  have hsplit : (k D (m + 1) : ℝ)⁻¹ • (∑ j, lowerTensor D m j) -
      (k D (m + 1) : ℝ)⁻¹ • (∑ j, upperTensor D m j) =
      (k D (m + 1) : ℝ)⁻¹ • (∑ j, (lowerTensor D m j - upperTensor D m j)) := by
    rw [Finset.sum_sub_distrib]
    module
  rw [hsplit]
  simp_rw [row_representation D m]
  rw [← Finset.smul_sum, smul_smul, Fintype.sum_prod_type]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, mul_inv_rev, Row]
  rw [mul_comm]

lemma averaged_row_bound (D : IncidenceData) (m : ℕ) :
    nu ((k D (m + 1) : ℝ)⁻¹ • (∑ j, lowerTensor D m j) -
      EnfloCoordinates.Spec.u D (m + 1)) ≤ 4 / (n D (m + 1) : ℝ) := by
  rw [averaged_row_identity]
  haveI : Nonempty (Row D (m + 1)) := Fin.pos_iff_nonempty.mp
    (BalancedIncidenceSets.rowCount_pos D.offset (m + 1 + 1))
  exact nu_average_tmul_le _ _ _
    (fun p => rowEvaluation_norm D m p.1 p.2)
    (fun p => row_vector_bound D m p.1 p.2)

/-- The full source estimate for the canonical algebraic tensors. -/
theorem adjacent_bound : AdjacentBound := by
  intro D m
  let A : Tensor ℝ (X D) := (k D (m + 1) : ℝ)⁻¹ • ∑ j, lowerTensor D m j
  have hb : nu (EnfloCoordinates.Spec.u D m - A) ≤ 1 / (n D (m + 1) : ℝ) :=
    balance_bound D m
  have hr : nu (A - EnfloCoordinates.Spec.u D (m + 1)) ≤ 4 / (n D (m + 1) : ℝ) :=
    averaged_row_bound D m
  have hdecomp : EnfloCoordinates.Spec.u D (m + 1) - EnfloCoordinates.Spec.u D m =
      -(A - EnfloCoordinates.Spec.u D (m + 1)) + -(EnfloCoordinates.Spec.u D m - A) := by
    abel
  rw [hdecomp]
  calc
    _ ≤ nu (-(A - EnfloCoordinates.Spec.u D (m + 1))) +
        nu (-(EnfloCoordinates.Spec.u D m - A)) := projectiveInfimum_add_le _ _
    _ = nu (A - EnfloCoordinates.Spec.u D (m + 1)) +
        nu (EnfloCoordinates.Spec.u D m - A) := by rw [nu_neg, nu_neg]
    _ ≤ 4 / (n D (m + 1) : ℝ) + 1 / (n D (m + 1) : ℝ) := add_le_add hr hb
    _ = 5 / (n D (m + 1) : ℝ) := by ring

end ExpandedFA.AP.AdjacentTensorDifferences
