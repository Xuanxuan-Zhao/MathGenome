import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.AP.EnfloCoordinates
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.AP.EnfloSpace
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.AP.WalshBlocks
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.AP.AlgebraicRankOneTensors
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

noncomputable section
open scoped BigOperators TensorProduct ENNReal
set_option maxHeartbeats 800000
namespace ExpandedFA.AP.EnfloCoordinates
open EnfloSpace.Spec
abbrev coordinate := Spec.coordinate
abbrev u := Spec.u

lemma character_norm (n : ℕ) (S : Finset (Fin (2 * n))) (a : Walsh.Cube n) :
    ‖Walsh.character n S a‖ = 1 := by
  simp [Walsh.character, norm_pow]

lemma rowFourier_apply (D : IncidenceData) (m : ℕ) (r : Row D m)
    (S : Finset (Fin (2 * n D m))) (f : Summand D m) :
    Spec.rowFourier D m r S f =
      (Fintype.card (Walsh.Cube (n D m)) : ℝ)⁻¹ *
        ∑ a, Walsh.character (n D m) S a * f (r, a) := by
  simp [Spec.rowFourier, ContinuousMap.evalCLM]

lemma rowFourier_bound (D : IncidenceData) (m : ℕ) (r : Row D m)
    (S : Finset (Fin (2 * n D m))) (f : Summand D m) :
    ‖Spec.rowFourier D m r S f‖ ≤ ‖f‖ := by
  rw [rowFourier_apply, norm_mul, norm_inv, Real.norm_natCast]
  calc
    _ ≤ (Fintype.card (Walsh.Cube (n D m)) : ℝ)⁻¹ *
        ∑ a : Walsh.Cube (n D m), ‖Walsh.character (n D m) S a * f (r, a)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (Fintype.card (Walsh.Cube (n D m)) : ℝ)⁻¹ *
        ∑ _a : Walsh.Cube (n D m), ‖f‖ := by
      gcongr with a
      rw [norm_mul, character_norm, one_mul]
      exact f.norm_coe_le_norm (r, a)
    _ = ‖f‖ := by
      simp

lemma rowFourier_character (D : IncidenceData) (m : ℕ) (r : Row D m)
    (S T : Finset (Fin (2 * n D m))) (f : Summand D m)
    (hf : ∀ a, f (r, a) = Walsh.character (n D m) T a) :
    Spec.rowFourier D m r S f = if S = T then 1 else 0 := by
  simp_rw [rowFourier_apply, hf]
  exact WalshBlocks.character_orthonormal _ _ _

lemma rowFourier_zero (D : IncidenceData) (m : ℕ) (r : Row D m)
    (S : Finset (Fin (2 * n D m))) (f : Summand D m)
    (hf : ∀ a, f (r, a) = 0) : Spec.rowFourier D m r S f = 0 := by
  simp [rowFourier_apply, hf]

lemma upper_lower_ne (D : IncidenceData) (m : ℕ)
    (S T : Finset (Fin (2 * n D m)))
    (hS : S ∈ Walsh.level (n D m) (n D m + 1))
    (hT : T ∈ Walsh.level (n D m) (n D m - 1)) : S ≠ T := by
  have hs := (Finset.mem_powersetCard.mp hS).2
  have ht := (Finset.mem_powersetCard.mp hT).2
  have hn := D.dimension_ge_two (m + 1) (by omega)
  intro h
  rw [h] at hs
  omega

lemma own_upper (D : IncidenceData) (m : ℕ) (e d : Symbol D m) :
    Spec.rowFourier D m e.1 (upperLabels D m e.2).val (ownBlock D m d) =
      if e = d then 1 else 0 := by
  classical
  by_cases hr : e.1 = d.1
  · rw [rowFourier_character D m e.1 _ (upperLabels D m d.2).val _
      (by intro a; simp [ownBlock, hr])]
    congr 1
    apply propext
    constructor
    · intro h
      exact Prod.ext hr ((upperLabels D m).injective (Subtype.ext h))
    · rintro rfl; rfl
  · rw [rowFourier_zero D m e.1 _ _ (by intro a; simp [ownBlock, hr])]
    rw [if_neg (fun h => hr (congrArg Prod.fst h))]

lemma own_lower (D : IncidenceData) (m : ℕ) (r : Row D m)
    (S : ↥(Walsh.level (n D m) (n D m - 1))) (d : Symbol D m) :
    Spec.rowFourier D m r S.val (ownBlock D m d) = 0 := by
  classical
  by_cases hr : r = d.1
  · rw [rowFourier_character D m r _ (upperLabels D m d.2).val _
      (by intro a; simp [ownBlock, hr])]
    exact if_neg (Ne.symm (upper_lower_ne D m _ _ (upperLabels D m d.2).property S.property))
  · exact rowFourier_zero D m r _ _ (by intro a; simp [ownBlock, hr])

lemma next_upper (D : IncidenceData) (m : ℕ) (r : Row D (m + 1))
    (S : ↥(Walsh.level (n D (m + 1)) (n D (m + 1) + 1))) (d : Symbol D m) :
    Spec.rowFourier D (m + 1) r S.val (nextBlock D m d) = 0 := by
  classical
  by_cases hd : d ∈ incident D m r
  · rw [rowFourier_character D (m + 1) r _
      (lowerLabels D m r ⟨d, hd⟩).val _ (by intro a; simp [nextBlock, hd])]
    exact if_neg (upper_lower_ne D (m + 1) _ _ S.property
      (lowerLabels D m r ⟨d, hd⟩).property)
  · exact rowFourier_zero D (m + 1) r _ _ (by intro a; simp [nextBlock, hd])

lemma next_lower (D : IncidenceData) (m : ℕ) (r : Row D (m + 1))
    (e : ↥(incident D m r)) (d : Symbol D m) :
    Spec.rowFourier D (m + 1) r (lowerLabels D m r e).val (nextBlock D m d) =
      if e.val = d then 1 else 0 := by
  classical
  by_cases hd : d ∈ incident D m r
  · rw [rowFourier_character D (m + 1) r _
      (lowerLabels D m r ⟨d, hd⟩).val _ (by intro a; simp [nextBlock, hd])]
    congr 1
    apply propext
    constructor
    · intro h
      exact congrArg Subtype.val ((lowerLabels D m r).injective (Subtype.ext h))
    · intro h
      exact congrArg (fun x : ↥(incident D m r) => (lowerLabels D m r x).val)
        (Subtype.ext h)
  · rw [rowFourier_zero D (m + 1) r _ _ (by intro a; simp [nextBlock, hd])]
    simp only [if_neg (show e.val ≠ d from fun h => hd (h ▸ e.property))]



lemma generator_block_own (D : IncidenceData) (m : ℕ) (e : Symbol D m) :
    generator D m e m = ownBlock D m e := by
  ext p
  exact EnfloSpace.generator_own D m e p.1 p.2

lemma generator_block_next (D : IncidenceData) (m : ℕ) (e : Symbol D m) :
    generator D m e (m + 1) = nextBlock D m e := by
  ext p
  exact EnfloSpace.generator_next D m e p.1 p.2

lemma ambient_biorthogonal (D : IncidenceData) (e d : AllSymbols D) :
    Spec.ambientCoordinate D e (generator D d.1 d.2) = if e = d then 1 else 0 := by
  classical
  obtain ⟨m, e⟩ := e
  obtain ⟨q, d⟩ := d
  change Spec.rowFourier D m e.1 (upperLabels D m e.2).val
    (generator D q d m) = _
  by_cases h : m = q
  · subst q
    rw [generator_block_own, own_upper]
    simp
  · rw [if_neg (fun he => h (congrArg Sigma.fst he))]
    by_cases h' : m = q + 1
    · subst m
      rw [generator_block_next]
      exact next_upper D q e.1 (upperLabels D (q + 1) e.2) d
    · rw [EnfloSpace.generator_other D q d m h h', map_zero]

theorem biorthogonal (D : IncidenceData) (e d : AllSymbols D) :
    coordinate D e (generatorX D d.1 d.2) = if e = d then 1 else 0 := by
  exact ambient_biorthogonal D e d

theorem coordinate_extension (D : IncidenceData) (A : Finset (AllSymbols D))
    (c : AllSymbols D → ℝ) (e : AllSymbols D) (he : e ∈ A) :
    coordinate D e (∑ d ∈ A, c d • generatorX D d.1 d.2) = c e := by
  classical
  simp only [map_sum, map_smul, biorthogonal, smul_eq_mul]
  rw [Finset.sum_eq_single e]
  · simp
  · intro d hd hde
    simp [Ne.symm hde]
  · simp [he]

theorem generators_independent : Spec.Independence := by
  classical
  intro D
  apply linearIndependent_iff'.mpr
  intro A c hc e he
  have h := congrArg (coordinate D e) hc
  rw [coordinate_extension D A c e he, map_zero] at h
  exact h

lemma ownBlock_norm (D : IncidenceData) (m : ℕ) (e : Symbol D m) :
    ‖ownBlock D m e‖ = 1 := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro p
    by_cases h : p.1 = e.1 <;> simp [ownBlock, h, ← Real.norm_eq_abs, character_norm]
  · have h := (ownBlock D m e).norm_coe_le_norm (e.1, fun _ => false)
    simpa [ownBlock, ← Real.norm_eq_abs, character_norm] using h

lemma nextBlock_norm_le (D : IncidenceData) (m : ℕ) (e : Symbol D m) :
    ‖nextBlock D m e‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro p
  by_cases h : e ∈ incident D m p.1 <;> simp [nextBlock, h, ← Real.norm_eq_abs, character_norm]

lemma generator_norm_pos (D : IncidenceData) (e : AllSymbols D) :
    0 < ‖generatorX D e.1 e.2‖ := by
  have h := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (generator D e.1 e.2) e.1
  rw [generator_block_own, ownBlock_norm] at h
  exact lt_of_lt_of_le (by norm_num) h

/-- A lower-row coefficient is the same functional on X as its own-row coefficient. -/
lemma lower_agrees (D : IncidenceData) (m : ℕ) (r : Row D (m + 1))
    (e : ↥(incident D m r)) (x : X D) :
    Spec.rowFourier D (m + 1) r (lowerLabels D m r e).val (x.val (m + 1)) =
      coordinate D ⟨m, e.val⟩ x := by
  classical
  let L : Y D →L[ℝ] ℝ :=
    (Spec.rowFourier D (m + 1) r (lowerLabels D m r e).val).comp
      (lp.evalCLM ℝ (Summand D) 2 (m + 1)) - Spec.ambientCoordinate D ⟨m, e.val⟩
  have hgen : ∀ d : AllSymbols D, L (generator D d.1 d.2) = 0 := by
    rintro ⟨q, d⟩
    change Spec.rowFourier D (m + 1) r (lowerLabels D m r e).val
      (generator D q d (m + 1)) -
        Spec.ambientCoordinate D ⟨m, e.val⟩ (generator D q d) = 0
    rw [ambient_biorthogonal D ⟨m, e.val⟩ ⟨q, d⟩]
    by_cases h : q = m
    · subst q
      rw [generator_block_next, next_lower]
      simp
    · have hmd : (⟨m, e.val⟩ : AllSymbols D) ≠ ⟨q, d⟩ := by
        intro hh
        exact h (congrArg Sigma.fst hh).symm
      rw [if_neg hmd, sub_zero]
      by_cases h' : m + 1 = q
      · subst q
        rw [generator_block_own]
        exact own_lower D (m + 1) r (lowerLabels D m r e) d
      · rw [EnfloSpace.generator_other D q d (m + 1) h' (by omega), map_zero]
  have hspan : Submodule.span ℝ (generators D) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨d, rfl⟩
    exact hgen d
  have hx := (Submodule.topologicalClosure_minimal _ hspan L.isClosed_ker) x.property
  exact sub_eq_zero.mp hx

lemma coordinate_block_bound (D : IncidenceData) (e : AllSymbols D)
    (x : X D) (b : ℕ) :
    ‖coordinate D e x • generator D e.1 e.2 b‖ ≤ ‖x.val b‖ := by
  classical
  obtain ⟨m, e⟩ := e
  by_cases hb : b = m
  · subst b
    rw [generator_block_own, norm_smul, ownBlock_norm, mul_one]
    exact rowFourier_bound D m e.1 _ _
  · by_cases hb' : b = m + 1
    · subst b
      rw [generator_block_next, norm_smul]
      by_cases hex : ∃ r : Row D (m + 1), e ∈ incident D m r
      · obtain ⟨r, hr⟩ := hex
        calc
          ‖coordinate D ⟨m, e⟩ x‖ * ‖nextBlock D m e‖ ≤
              ‖coordinate D ⟨m, e⟩ x‖ :=
            mul_le_of_le_one_right (norm_nonneg _) (nextBlock_norm_le D m e)
          _ ≤ ‖x.val (m + 1)‖ := by
            rw [← lower_agrees D m r ⟨e, hr⟩ x]
            exact rowFourier_bound D (m + 1) r _ _
      · have hz : nextBlock D m e = 0 := by
          ext p
          simp [nextBlock, show e ∉ incident D m p.1 from fun h => hex ⟨p.1, h⟩]
        simp [hz]
    · rw [EnfloSpace.generator_other D m e b hb hb', smul_zero, norm_zero]
      exact norm_nonneg _

/-- The sharp coefficient inequality holds on the entire closed span. -/
lemma coordinate_bound (D : IncidenceData) (e : AllSymbols D) (x : X D) :
    |coordinate D e x| * ‖generatorX D e.1 e.2‖ ≤ ‖x‖ := by
  change |coordinate D e x| * ‖generator D e.1 e.2‖ ≤ ‖x.val‖
  have h := lp.norm_mono (x := coordinate D e x • generator D e.1 e.2)
    (y := x.val) (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (fun b => coordinate_block_bound D e x b)
  simpa only [lp.coeFn_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs] using h

theorem coefficient_estimate : Spec.CoefficientEstimate := by
  intro D A c e he
  simpa only [coordinate_extension D A c e he] using
    coordinate_bound D e (∑ d ∈ A, c d • generatorX D d.1 d.2)

theorem coordinate_sharp_norm (D : IncidenceData) (e : AllSymbols D) :
    ‖coordinate D e‖ * ‖generatorX D e.1 e.2‖ = 1 := by
  have hp := generator_norm_pos D e
  have hu : ‖coordinate D e‖ ≤ ‖generatorX D e.1 e.2‖⁻¹ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hp.le)
    intro x
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ hp).mpr (coordinate_bound D e x)
  apply le_antisymm
  · calc
      _ ≤ ‖generatorX D e.1 e.2‖⁻¹ * ‖generatorX D e.1 e.2‖ :=
        mul_le_mul_of_nonneg_right hu hp.le
      _ = 1 := inv_mul_cancel₀ hp.ne'
  · have h := (coordinate D e).le_opNorm (generatorX D e.1 e.2)
    rw [biorthogonal D e e, if_pos rfl, norm_one] at h
    exact h



lemma normalization_pos (D : IncidenceData) (m : ℕ) :
    0 < (k D m : ℝ) * t D m := by
  exact mul_pos (Nat.cast_pos.mpr (BalancedIncidenceSets.rowCount_pos D.offset (m + 1)))
    (Nat.cast_pos.mpr (BalancedIncidenceSets.levelSize_pos D.offset (m + 1)))

lemma symbol_card (D : IncidenceData) (m : ℕ) :
    (Fintype.card (Symbol D m) : ℝ) = (k D m : ℝ) * t D m := by
  simp [Symbol, Incidence.Symbol]

theorem tensor_trace_one : Spec.TraceOne := by
  intro D m
  change AlgebraicRankOneTensorsSpec.trace (Spec.u D m) = 1
  simp only [Spec.u, map_smul, map_sum]
  have ht : ∀ e : Symbol D m,
      AlgebraicRankOneTensorsSpec.trace
        (coordinate D ⟨m, e⟩ ⊗ₜ[ℝ] generatorX D m e) = 1 := by
    intro e
    change coordinate D ⟨m, e⟩ (generatorX D m e) = 1
    simpa using biorthogonal D ⟨m, e⟩ ⟨m, e⟩
  simp_rw [ht]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, smul_eq_mul]
  rw [symbol_card]
  exact inv_mul_cancel₀ (normalization_pos D m).ne'

/-- Estimate a finite algebraic representation directly; no operator quotient is used. -/
lemma nu_sum_tmul_le {D : IncidenceData} {I : Type*} (A : Finset I)
    (f : I → X D →L[ℝ] ℝ) (x : I → X D) :
    AlgebraicRankOneTensorsSpec.nu (∑ i ∈ A, f i ⊗ₜ[ℝ] x i) ≤
      ∑ i ∈ A, ‖f i‖ * ‖x i‖ := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (projectiveInfimum_zero (𝕜 := ℝ) (X := X D)).le
  | @insert i A hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    apply le_trans (projectiveInfimum_add_le _ _)
    apply add_le_add _ ih
    simpa only [AlgebraicRankOneTensorsSpec.tensorSum, AlgebraicRankOneTensorsSpec.cost,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using
      (projectiveInfimum_le_cost [(f i, x i)])

theorem tensor_projective_bound : Spec.ProjectiveBound := by
  intro D m
  let a : ℝ := ((k D m : ℝ) * t D m)⁻¹
  have ha : 0 ≤ a := inv_nonneg.mpr (normalization_pos D m).le
  change AlgebraicRankOneTensorsSpec.nu
    (a • ∑ e : Symbol D m, coordinate D ⟨m, e⟩ ⊗ₜ[ℝ] generatorX D m e) ≤ 1
  rw [Finset.smul_sum]
  calc
    _ ≤ ∑ e : Symbol D m, ‖a • coordinate D ⟨m, e⟩‖ * ‖generatorX D m e‖ :=
      nu_sum_tmul_le _ _ _
    _ ≤ ∑ _e : Symbol D m, a := by
      apply Finset.sum_le_sum
      intro e he
      calc
        _ ≤ (‖a‖ * ‖coordinate D ⟨m, e⟩‖) * ‖generatorX D m e‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_smul_le _ _) (norm_nonneg _)
        _ = a := by rw [Real.norm_eq_abs, abs_of_nonneg ha, mul_assoc,
          coordinate_sharp_norm D ⟨m, e⟩, mul_one]
    _ = 1 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, symbol_card]
      exact mul_inv_cancel₀ (normalization_pos D m).ne'

end ExpandedFA.AP.EnfloCoordinates
