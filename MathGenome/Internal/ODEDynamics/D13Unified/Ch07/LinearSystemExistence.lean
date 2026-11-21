import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch07.LinearSystemExistence
import MathGenome.Internal.ODEDynamics.D13Unified.Ch06.LinearVolterra
import Mathlib.Analysis.Normed.Module.RCLike.Basic

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Matrix Matrix.Norms.Operator

namespace D13Unified.Ch07.LinearSystemExistence
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Every point of a real interval has a compact relative neighborhood inside
that interval, enlarged to contain a specified base time. -/
lemma compact_neighborhood (I : TimeInterval) {s t : ℝ}
    (hs : s ∈ I.carrier) (ht : t ∈ I.carrier) :
    ∃ a b : ℝ, s ∈ Icc a b ∧ t ∈ Icc a b ∧
      Icc a b ⊆ I.carrier ∧ Icc a b ∈ 𝓝[I.carrier] t := by
  have hl : ∃ a ∈ I.carrier, a ≤ t ∧ I.carrier ∩ Ioi a ∈ 𝓝[I.carrier] t ∨
      a = t ∧ I.carrier ⊆ Ici t := by
    by_cases h : ∃ a ∈ I.carrier, a < t
    · obtain ⟨a, ha, hat⟩ := h
      exact ⟨a, ha, Or.inl ⟨hat.le, inter_mem self_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hat))⟩⟩
    · refine ⟨t, ht, Or.inr ⟨rfl, ?_⟩⟩
      intro a ha
      exact le_of_not_gt (fun hat => h ⟨a, ha, hat⟩)
  have hr : ∃ b ∈ I.carrier, t ≤ b ∧ I.carrier ∩ Iio b ∈ 𝓝[I.carrier] t ∨
      b = t ∧ I.carrier ⊆ Iic t := by
    by_cases h : ∃ b ∈ I.carrier, t < b
    · obtain ⟨b, hb, htb⟩ := h
      exact ⟨b, hb, Or.inl ⟨htb.le, inter_mem self_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htb))⟩⟩
    · refine ⟨t, ht, Or.inr ⟨rfl, ?_⟩⟩
      intro b hb
      exact le_of_not_gt (fun htb => h ⟨b, hb, htb⟩)
  obtain ⟨a, ha, hla⟩ := hl
  obtain ⟨b, hb, hrb⟩ := hr
  have hat : a ≤ t := hla.elim And.left (fun h => h.1.le)
  have htb : t ≤ b := hrb.elim And.left (fun h => h.1.ge)
  refine ⟨min a s, max b s, ⟨min_le_right _ _, le_max_right _ _⟩,
    ⟨(min_le_left _ _).trans hat, htb.trans (le_max_left _ _)⟩, ?_, ?_⟩
  · exact I.ordConnected.out (min_rec' (· ∈ I.carrier) ha hs)
      (max_rec' (· ∈ I.carrier) hb hs)
  · have hleft : ∀ᶠ x in 𝓝[I.carrier] t, a ≤ x := by
      rcases hla with ⟨_, h⟩ | ⟨rfl, h⟩
      · filter_upwards [h] with x hx
        exact hx.2.le
      · exact Filter.mem_of_superset self_mem_nhdsWithin h
    have hright : ∀ᶠ x in 𝓝[I.carrier] t, x ≤ b := by
      rcases hrb with ⟨_, h⟩ | ⟨rfl, h⟩
      · filter_upwards [h] with x hx
        exact hx.2.le
      · exact Filter.mem_of_superset self_mem_nhdsWithin h
    filter_upwards [hleft, hright] with x hx hy
    exact ⟨(min_le_left _ _).trans hx, hy.trans (le_max_left _ _)⟩

omit [CompleteSpace E] in
/-- Restriction of an integral solution to a compact subinterval containing s. -/
lemma restrict_integral {a b c d s : ℝ} {A : ℝ → E →L[ℝ] E}
    {ξ : E} {Y : ℝ → E}
    (hY : Ch06.LinearVolterra.IsIntegralSolution a b s A (fun _ => 0) ξ Y)
    (hsub : Icc c d ⊆ Icc a b) :
    Ch06.LinearVolterra.IsIntegralSolution c d s A (fun _ => 0) ξ Y :=
  ⟨hY.1.mono hsub, fun t ht => hY.2 t (hsub ht)⟩

omit [CompleteSpace E] in
/-- A continuous prescribed velocity gives C¹ regularity on the actual set,
including at endpoints and on a singleton. -/
lemma regularity {J : Set ℝ} {Y g : ℝ → E}
    (hg : ContinuousOn g J) (hd : ∀ t ∈ J, HasDerivWithinAt Y (g t) J t) :
    ContDiffOn ℝ 1 Y J := by
  apply (contDiffOn_succ_iff_hasFDerivWithinAt (n := 0) (by simp)).mpr
  intro t ht
  refine ⟨J, ?_, by simp, fun r => ContinuousLinearMap.toSpanSingleton ℝ (g r),
    fun r hr => (hd r hr).hasFDerivWithinAt, ?_⟩
  · rw [insert_eq_of_mem ht]
    exact self_mem_nhdsWithin
  · exact contDiffOn_zero.mpr
      ((ContinuousLinearMap.toSpanSingletonLIE ℝ E).continuous.comp_continuousOn hg)

/-- Patching compact Volterra solutions. No boundedness on a noncompact
interval is required. -/
theorem existence : Specs.D13Unified.Ch07.LinearSystemExistence.Existence.{u} := by
  intro E _ _ _ I A s ξ hs hA
  classical
  have hex (a b : ℝ) (hsab : s ∈ Icc a b) (hab : Icc a b ⊆ I.carrier) :=
    Ch06.LinearVolterra.existence a b s A (fun _ => 0) ξ hsab (hA.mono hab) continuousOn_const
  choose W hW huniq using hex
  have hseg (t : ℝ) (ht : t ∈ I.carrier) : uIcc s t ⊆ I.carrier :=
    I.ordConnected.uIcc_subset hs ht
  let Y : ℝ → E := fun t => if ht : t ∈ I.carrier then
    W (min s t) (max s t) (left_mem_uIcc) (hseg t ht) t else ξ
  have hagree (a b : ℝ) (hsab : s ∈ Icc a b) (hab : Icc a b ⊆ I.carrier) :
      EqOn Y (W a b hsab hab) (Icc a b) := by
    intro t ht
    have htI := hab ht
    dsimp only [Y]
    rw [dite_eq_left htI]
    have hsub : uIcc s t ⊆ Icc a b := ordConnected_Icc.uIcc_subset hsab ht
    exact (huniq (min s t) (max s t) left_mem_uIcc (hseg t htI)
      (W a b hsab hab) (restrict_integral (hW a b hsab hab) hsub) right_mem_uIcc).symm
  have hc : ContinuousOn Y I.carrier := by
    intro t ht
    obtain ⟨a, b, hsab, htab, hab, hn⟩ := compact_neighborhood I hs ht
    exact (((hW a b hsab hab).1.congr (hagree a b hsab hab)) t htab).mono_of_mem_nhdsWithin hn
  have hi : ∀ t ∈ I.carrier, Y t = ξ + ∫ r in s..t, A r (Y r) := by
    intro t ht
    let a := min s t
    let b := max s t
    have hab := hseg t ht
    have heq := hagree a b left_mem_uIcc hab
    dsimp only [a, b] at heq ⊢
    rw [heq right_mem_uIcc, (hW a b left_mem_uIcc hab).2 t right_mem_uIcc]
    simp only [add_zero]
    congr 1
    apply intervalIntegral.integral_congr
    intro r hr
    exact congrArg (A r) (heq hr).symm
  have hd : ∀ t ∈ I.carrier, HasDerivWithinAt Y (A t (Y t)) I.carrier t := by
    intro t ht
    exact ((hasDerivWithinAt_integral_on_interval I.ordConnected
      (hA.clm_apply hc) hs ht).const_add ξ).congr_of_mem hi ht
  refine ⟨Y, hc, ?_, hd, hi, regularity (hA.clm_apply hc) hd, ?_⟩
  · simpa only [intervalIntegral.integral_same, add_zero] using hi s hs
  · intro Z hZ hZs hZd t ht
    have hzint : Ch06.LinearVolterra.IsIntegralSolution (min s t) (max s t) s A
        (fun _ => 0) ξ Z := by
      refine ⟨hZ.mono (hseg t ht), ?_⟩
      intro r hr
      simp only [add_zero]
      rw [integral_eq_sub_on_interval I.ordConnected hZ (hA.clm_apply hZ) hZd hs
        (hseg t ht hr), hZs]
      abel
    have hyint : Ch06.LinearVolterra.IsIntegralSolution (min s t) (max s t) s A
        (fun _ => 0) ξ Y :=
      ⟨hc.mono (hseg t ht), fun r hr => by simpa only [add_zero] using hi r (hseg t ht hr)⟩
    exact Ch06.LinearVolterra.unique left_mem_uIcc (hA.mono (hseg t ht)) continuousOn_const
      hzint hyint right_mem_uIcc


/-- Gronwall with the actual continuous coefficient majorant on each segment. -/
theorem growth_bound : Specs.D13Unified.Ch07.LinearSystemExistence.GrowthBound.{u} := by
  intro E _ _ _ I A s ξ Y b hs hY hb hb0 hnorm heq t ht
  by_cases hst : s ≤ t
  · have hsub : Icc s t ⊆ I.carrier := I.ordConnected.out hs ht
    have hineq : ∀ v ∈ Icc s t,
        ‖Y v‖ ≤ ‖ξ‖ + ∫ r in s..v, (b r * ‖Y r‖ + 0) := by
      intro v hv
      calc
        ‖Y v‖ = ‖ξ + ∫ r in s..v, A r (Y r)‖ := congrArg norm (heq v (hsub hv))
        _ ≤ ‖ξ‖ + ‖∫ r in s..v, A r (Y r)‖ := norm_add_le _ _
        _ ≤ ‖ξ‖ + ∫ r in s..v, (b r * ‖Y r‖ + 0) := by
          apply add_le_add (le_refl ‖ξ‖)
          apply intervalIntegral.norm_integral_le_of_norm_le hv.1
          · exact Eventually.of_forall (fun r hr => by
              simpa only [add_zero] using hnorm r (hsub ⟨hr.1.le, hr.2.trans hv.2⟩))
          · exact (((hb.mul hY.norm).add continuousOn_const).mono (by
              rw [uIcc_of_le hv.1]
              exact (Icc_subset_Icc le_rfl hv.2).trans hsub)).intervalIntegrable
    have h := Ch05.Gronwall.forward s t ‖ξ‖ (fun r => ‖Y r‖) b (fun _ => 0)
      hst (norm_nonneg _) (hY.norm.mono hsub) (hb.mono hsub) continuousOn_const
      (fun r hr => ⟨norm_nonneg _, hb0 r (hsub hr), le_rfl⟩) hineq t ⟨hst, le_rfl⟩
    simpa only [min_eq_left hst, max_eq_right hst, zero_mul,
      intervalIntegral.integral_zero, add_zero] using h
  · have hts : t ≤ s := le_of_not_ge hst
    have hsub : Icc t s ⊆ I.carrier := I.ordConnected.out ht hs
    have hineq : ∀ v ∈ Icc t s,
        ‖Y v‖ ≤ ‖ξ‖ + ∫ r in v..s, (b r * ‖Y r‖ + 0) := by
      intro v hv
      calc
        ‖Y v‖ = ‖ξ + ∫ r in s..v, A r (Y r)‖ := congrArg norm (heq v (hsub hv))
        _ ≤ ‖ξ‖ + ‖∫ r in s..v, A r (Y r)‖ := norm_add_le _ _
        _ = ‖ξ‖ + ‖∫ r in v..s, A r (Y r)‖ := by rw [intervalIntegral.integral_symm, norm_neg]
        _ ≤ ‖ξ‖ + ∫ r in v..s, (b r * ‖Y r‖ + 0) := by
          apply add_le_add (le_refl ‖ξ‖)
          apply intervalIntegral.norm_integral_le_of_norm_le hv.2
          · exact Eventually.of_forall (fun r hr => by
              simpa only [add_zero] using hnorm r (hsub ⟨hv.1.trans hr.1.le, hr.2⟩))
          · exact (((hb.mul hY.norm).add continuousOn_const).mono (by
              rw [uIcc_of_le hv.2]
              exact (Icc_subset_Icc hv.1 le_rfl).trans hsub)).intervalIntegrable
    have h := Ch05.Gronwall.backward t s ‖ξ‖ (fun r => ‖Y r‖) b (fun _ => 0)
      hts (norm_nonneg _) (hY.norm.mono hsub) (hb.mono hsub) continuousOn_const
      (fun r hr => ⟨norm_nonneg _, hb0 r (hsub hr), le_rfl⟩) hineq t ⟨le_rfl, hts⟩
    simpa only [min_eq_right hts, max_eq_left hts, zero_mul,
      intervalIntegral.integral_zero, add_zero] using h

/-- The source's estimate in every complete real normed state space. -/
theorem norm_bound (I : TimeInterval) (A : ℝ → E →L[ℝ] E) (s : ℝ) (ξ : E)
    (Y : ℝ → E) (hs : s ∈ I.carrier) (hA : ContinuousOn A I.carrier)
    (hY : ContinuousOn Y I.carrier)
    (hi : ∀ t ∈ I.carrier, Y t = ξ + ∫ r in s..t, A r (Y r)) :
    ∀ t ∈ I.carrier,
      ‖Y t‖ ≤ ‖ξ‖ * Real.exp (∫ r in min s t..max s t, ‖A r‖) :=
  growth_bound I A s ξ Y (fun r => ‖A r‖) hs hY hA.norm
    (fun _ _ => norm_nonneg _) (fun r _ => (A r).le_opNorm _) hi

/-- Multiplication supplies a real continuous linear action even when the
algebra is complex. The Bochner integrals and derivatives still use real time. -/
theorem algebra_existence : Specs.D13Unified.Ch07.LinearSystemExistence.AlgebraExistence.{u} := by
  intro R _ _ _ I A s ξ hs hA
  let C : ℝ → R →L[ℝ] R := fun t => ContinuousLinearMap.mul ℝ R (A t)
  have hC : ContinuousOn C I.carrier :=
    (ContinuousLinearMap.mul ℝ R).continuous.comp_continuousOn hA
  obtain ⟨Y, hY, hYs, hd, hi, hreg, hu⟩ := existence I C s ξ hs hC
  refine ⟨Y, hY, hYs, hd, ?_, hreg, hu⟩
  exact growth_bound I C s ξ Y (fun t => ‖A t‖) hs hY hA.norm
    (fun _ _ => norm_nonneg _) (fun r _ => norm_mul_le _ _) hi


/-- Restricting scalars preserves the operator norm and the actual integrand;
all calculus in this theorem is with respect to real time. -/
theorem scalar_existence : Specs.D13Unified.Ch07.LinearSystemExistence.ScalarExistence.{u} := by
  intro 𝕂 _ E _ _ _ _ _ I A s ξ hs hA
  let C : ℝ → E →L[ℝ] E := fun t => (A t).restrictScalars ℝ
  have hC : ContinuousOn C I.carrier :=
    (ContinuousLinearMap.restrictScalarsIsometry 𝕂 E E ℝ ℝ).continuous.comp_continuousOn hA
  obtain ⟨Y, hc, hi, hd, hint, hreg, hu⟩ := existence I C s ξ hs hC
  refine ⟨Y, hc, hi, hd, ?_, hreg, hu⟩
  simpa only [C, ContinuousLinearMap.norm_restrictScalars] using
    norm_bound I C s ξ Y hs hC hc hint

/-- Operator-valued evolution with the original induced operator norm, on an
arbitrarily normed real or complex Banach space. -/
theorem operator_evolution : Specs.D13Unified.Ch07.LinearSystemExistence.OperatorEvolution.{u} := by
  intro 𝕂 _ E _ _ _ _ _ I A s hs hA
  let C : ℝ → (E →L[𝕂] E) →L[ℝ] (E →L[𝕂] E) := fun t =>
    ((ContinuousLinearMap.compL 𝕂 E E E) (A t)).restrictScalars ℝ
  have hC : ContinuousOn C I.carrier :=
    (ContinuousLinearMap.restrictScalarsIsometry 𝕂 _ _ ℝ ℝ).continuous.comp_continuousOn
      ((ContinuousLinearMap.compL 𝕂 E E E).continuous.comp_continuousOn hA)
  obtain ⟨U, hc, hi, hd, hint, hreg, hu⟩ := existence I C s 1 hs hC
  refine ⟨U, hc, hi, hd, ?_, hreg, hu⟩
  have hb := growth_bound I C s 1 U (fun t => ‖A t‖) hs hc hA.norm
    (fun _ _ => norm_nonneg _) (fun t _ => (A t).opNorm_comp_le (U t)) hint
  have hunit : ‖(1 : E →L[𝕂] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  intro t ht
  exact (hb t ht).trans ((mul_le_mul_of_nonneg_right hunit
    (Real.exp_pos (∫ r in min s t..max s t, ‖A r‖)).le).trans_eq (one_mul _))

section Matrices
variable {𝕂 : Type} [RCLike 𝕂] {n r : ℕ}

/-- Complex multiplication is a real continuous linear map on the same normed
space. Restriction of scalars changes neither the map nor its norm. -/
def matrixLeftAction (A : Matrix (Fin n) (Fin n) 𝕂) :
    Matrix (Fin n) (Fin r) 𝕂 →L[ℝ] Matrix (Fin n) (Fin r) 𝕂 :=
  ((mulLeftLinearMap (Fin r) 𝕂 A).toContinuousLinearMap).restrictScalars ℝ

@[simp] lemma matrixLeftAction_apply (A : Matrix (Fin n) (Fin n) 𝕂)
    (Y : Matrix (Fin n) (Fin r) 𝕂) : matrixLeftAction A Y = A * Y := rfl

lemma continuous_matrixLeftAction :
    Continuous (matrixLeftAction (𝕂 := 𝕂) (n := n) (r := r)) := by
  let T : Matrix (Fin n) (Fin n) 𝕂 →ₗ[𝕂]
      (Matrix (Fin n) (Fin r) 𝕂 →L[𝕂] Matrix (Fin n) (Fin r) 𝕂) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp (mulLinearMap 𝕂)
  exact (ContinuousLinearMap.restrictScalarsIsometry 𝕂 _ _ ℝ ℝ).continuous.comp
    T.continuous_of_finiteDimensional

/-- Rectangular matrix multiplication over ℝ or ℂ is covered by the real
Banach-space construction without using complex-time differentiation. -/
theorem matrix_existence : Specs.D13Unified.Ch07.LinearSystemExistence.MatrixExistence := by
  intro 𝕂 _ n r I A s ξ hs hA
  obtain ⟨Y, hc, hi, hd, _, hreg, hu⟩ := existence I
    (fun t => matrixLeftAction (r := r) (A t)) s ξ hs
    (continuous_matrixLeftAction.comp_continuousOn hA)
  exact ⟨Y, hc, hi, hd, hreg, hu⟩

def vectorAction (A : Matrix (Fin n) (Fin n) 𝕂) :
    (Fin n → 𝕂) →L[ℝ] (Fin n → 𝕂) :=
  A.mulVecLin.toContinuousLinearMap.restrictScalars ℝ

@[simp] lemma vectorAction_apply (A : Matrix (Fin n) (Fin n) 𝕂)
    (x : Fin n → 𝕂) : vectorAction A x = A *ᵥ x := rfl

lemma continuous_vectorAction : Continuous (vectorAction (𝕂 := 𝕂) (n := n)) := by
  let T : Matrix (Fin n) (Fin n) 𝕂 →ₗ[𝕂] ((Fin n → 𝕂) →L[𝕂] (Fin n → 𝕂)) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp (Matrix.mulVecBilin 𝕂 𝕂)
  exact (ContinuousLinearMap.restrictScalarsIsometry 𝕂 _ _ ℝ ℝ).continuous.comp
    T.continuous_of_finiteDimensional

theorem vector_existence : Specs.D13Unified.Ch07.LinearSystemExistence.VectorExistence := by
  intro 𝕂 _ n I A s ξ hs hA
  obtain ⟨Y, hc, hi, hd, _, hreg, hu⟩ := existence I (fun t => vectorAction (A t)) s ξ hs
    (continuous_vectorAction.comp_continuousOn hA)
  exact ⟨Y, hc, hi, hd, hreg, hu⟩

/-- Includes the zero-dimensional system: its identity matrix is zero. -/
lemma matrix_norm_one_le : ‖(1 : Matrix (Fin n) (Fin n) 𝕂)‖ ≤ 1 := by
  cases isEmpty_or_nonempty (Fin n) with
  | inl h =>
    have := h
    rw [show (1 : Matrix (Fin n) (Fin n) 𝕂) = 0 from Subsingleton.elim _ _, norm_zero]
    exact zero_le_one
  | inr h =>
    have := h
    simp

theorem evolution_existence : Specs.D13Unified.Ch07.LinearSystemExistence.EvolutionExistence := by
  intro 𝕂 _ n I A s hs hA
  obtain ⟨U, hc, hi, hd, hb, hreg, hu⟩ := algebra_existence I A s 1 hs hA
  refine ⟨U, hc, hi, hd, ?_, hreg, hu⟩
  intro t ht
  exact (hb t ht).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (matrix_norm_one_le (𝕂 := 𝕂) (n := n))
      (Real.exp_pos (∫ r in min s t..max s t, ‖A r‖)).le)
end Matrices


section InducedNorm
variable {𝕂 : Type} [RCLike 𝕂] {n : ℕ}
variable (e : (Fin n → 𝕂) ≃L[ℝ] E)

omit [CompleteSpace E] in
@[simp] lemma matrixOperatorIn_apply (A : Matrix (Fin n) (Fin n) 𝕂) (x : E) :
    matrixOperatorIn e A x = e (A *ᵥ e.symm x) := rfl

omit [CompleteSpace E] in
@[simp] lemma matrixOperatorIn_one : matrixOperatorIn e 1 = 1 := by
  ext x
  simp

omit [CompleteSpace E] in
@[simp] lemma matrixOperatorIn_mul (A B : Matrix (Fin n) (Fin n) 𝕂) :
    matrixOperatorIn e (A * B) = matrixOperatorIn e A * matrixOperatorIn e B := by
  ext x
  simp [Matrix.mulVec_mulVec]

/-- The matrix-to-operator bridge is linear and continuous in finite dimension. -/
def matrixOperatorInMap : Matrix (Fin n) (Fin n) 𝕂 →L[ℝ] (E →L[ℝ] E) :=
  let T : Matrix (Fin n) (Fin n) 𝕂 →ₗ[ℝ] (E →L[ℝ] E) :=
    { toFun := matrixOperatorIn e
      map_add' := by intro A B; ext x; simp [Matrix.add_mulVec]
      map_smul' := by intro c A; ext x; simp [Matrix.smul_mulVec] }
  T.toContinuousLinearMap

omit [CompleteSpace E] in
@[simp] lemma matrixOperatorInMap_apply (A : Matrix (Fin n) (Fin n) 𝕂) :
    matrixOperatorInMap e A = matrixOperatorIn e A := rfl

/-- The arbitrary-norm estimate is for the original matrix equation, rather
than for an unrelated scalar or a differently timed system. -/
theorem matrix_evolution_in : Specs.D13Unified.Ch07.LinearSystemExistence.MatrixEvolutionIn.{u} := by
  intro 𝕂 _ n E _ _ _ e I A s hs hA
  obtain ⟨U, hc, hi, hd, hreg, hu⟩ := matrix_existence 𝕂 n n I A s 1 hs hA
  let T := matrixOperatorInMap e
  let V : ℝ → E →L[ℝ] E := fun t => T (U t)
  let B : ℝ → E →L[ℝ] E := fun t => T (A t)
  let C : ℝ → (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) := fun t =>
    (ContinuousLinearMap.compL ℝ E E E) (B t)
  have hV : ContinuousOn V I.carrier := T.continuous.comp_continuousOn hc
  have hB : ContinuousOn B I.carrier := T.continuous.comp_continuousOn hA
  have hVs : V s = 1 := by simp [V, T, hi]
  have hdV : ∀ t ∈ I.carrier, HasDerivWithinAt V (C t (V t)) I.carrier t := by
    intro t ht
    have h := T.hasFDerivAt.comp_hasDerivWithinAt t (hd t ht)
    change HasDerivWithinAt V (T (A t * U t)) I.carrier t at h
    have heq : T (A t * U t) = C t (V t) := by
      change matrixOperatorIn e (A t * U t) = matrixOperatorIn e (A t) * matrixOperatorIn e (U t)
      exact matrixOperatorIn_mul e _ _
    rw [heq] at h
    exact h
  have hint : ∀ t ∈ I.carrier, V t = 1 + ∫ r in s..t, C r (V r) := by
    intro t ht
    have hint' : (∫ r in s..t, C r (V r)) = V t - V s :=
      integral_eq_sub_on_interval I.ordConnected hV (hB.clm_comp hV) hdV hs ht
    rw [hint', hVs]
    abel
  have hb := growth_bound I C s 1 V (fun t => ‖B t‖) hs hV hB.norm
    (fun _ _ => norm_nonneg _) (fun t _ => (B t).opNorm_comp_le (V t)) hint
  refine ⟨U, hc, hi, hd, ?_, hreg, hu⟩
  have hunit : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  intro t ht
  exact (hb t ht).trans ((mul_le_mul_of_nonneg_right hunit
    (Real.exp_pos (∫ r in min s t..max s t, ‖B r‖)).le).trans_eq (one_mul _))
end InducedNorm

end D13Unified.Ch07.LinearSystemExistence
