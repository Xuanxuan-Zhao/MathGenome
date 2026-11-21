import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch18.NormIndependence
import MathGenome.Internal.ODEDynamics.D13Unified.Ch18.GrowthDefinitions
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

noncomputable section
open Set Filter
open scoped Topology
namespace D13Unified.Ch18.NormIndependence
open GrowthDefinitions

private theorem rate_nonzero (t r : ℝ) (hr : r ≠ 0) :
    logarithmicRate t r = ((Real.log r / t : ℝ) : EReal) :=
  logarithmicRate_nonzero t r hr

/-- A fixed multiplicative comparison gives an additive logarithmic comparison,
including simultaneous zero magnitudes. -/
theorem logarithmicRate_le {a b K t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hK : 0 < K) (ht : 0 < t) (hz : a = 0 ↔ b = 0) (h : b ≤ K * a) :
    logarithmicRate t b ≤ logarithmicRate t a + ((Real.log K / t : ℝ) : EReal) := by
  by_cases hzero : a = 0
  · simp [GrowthDefinitions.logarithmicRate, Specs.D13Unified.Ch18.GrowthDefinitions.logarithmicRate,
      hzero, hz.mp hzero]
  · have hbzero : b ≠ 0 := mt hz.mpr hzero
    have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hzero)
    have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hbzero)
    rw [rate_nonzero _ _ hbzero, rate_nonzero _ _ hzero,
      ← EReal.coe_add]
    apply EReal.coe_le_coe_iff.mpr
    rw [← add_div, add_comm (Real.log a), ← Real.log_mul hK.ne' hzero]
    exact div_le_div_of_nonneg_right (Real.log_le_log hbp h) ht.le

/-- Comparison of actual extended-real limits, with no existence assumption. -/
theorem comparison_tendsto {ι : Type*} {l : Filter ι} {a b t : ι → ℝ}
    {K : ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hK : 0 < K)
    (hz : ∀ i, a i = 0 ↔ b i = 0)
    (hab : ∀ i, b i ≤ K * a i) (hba : ∀ i, a i ≤ K * b i)
    (ht : Tendsto t l atTop) (z : EReal) :
    Tendsto (fun i => logarithmicRate (t i) (a i)) l (𝓝 z) ↔
    Tendsto (fun i => logarithmicRate (t i) (b i)) l (𝓝 z) := by
  have hpos : ∀ᶠ i in l, 0 < t i := ht.eventually (eventually_gt_atTop 0)
  have hd : Tendsto (fun i => ((Real.log K / t i : ℝ) : EReal)) l (𝓝 0) := by
    exact EReal.tendsto_coe.mpr (tendsto_const_nhds.div_atTop ht)
  have hdn : Tendsto (fun i => ((-Real.log K / t i : ℝ) : EReal)) l (𝓝 0) := by
    exact EReal.tendsto_coe.mpr (tendsto_const_nhds.div_atTop ht)
  have aux (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
      (hz : ∀ i, a i = 0 ↔ b i = 0) (hab : ∀ i, b i ≤ K*a i)
      (hba : ∀ i, a i ≤ K*b i)
      (hlim : Tendsto (fun i => logarithmicRate (t i) (a i)) l (𝓝 z)) :
      Tendsto (fun i => logarithmicRate (t i) (b i)) l (𝓝 z) := by
    have hup := (EReal.continuousAt_add (p := (z, 0)) (Or.inr (by simp))
      (Or.inr (by simp))).tendsto.comp (hlim.prodMk_nhds hd)
    have hlo := (EReal.continuousAt_add (p := (z, 0)) (Or.inr (by simp))
      (Or.inr (by simp))).tendsto.comp (hlim.prodMk_nhds hdn)
    simp only [add_zero] at hup hlo
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup
    · filter_upwards [hpos] with i hi
      by_cases hz0 : a i = 0
      · simp [GrowthDefinitions.logarithmicRate, Specs.D13Unified.Ch18.GrowthDefinitions.logarithmicRate,
          hz0, (hz i).mp hz0]
      · have hb0 : b i ≠ 0 := mt (hz i).mpr hz0
        dsimp only [Function.comp_def]
        have hh := logarithmicRate_le (hb i) (ha i) hK hi (hz i).symm (hba i)
        rw [rate_nonzero _ _ hz0, rate_nonzero _ _ hb0,
          ← EReal.coe_add] at hh
        rw [rate_nonzero _ _ hz0, rate_nonzero _ _ hb0,
          ← EReal.coe_add]
        apply EReal.coe_le_coe_iff.mpr
        have := EReal.coe_le_coe_iff.mp hh
        simp only [neg_div] at *
        linarith
    · filter_upwards [hpos] with i hi
      exact logarithmicRate_le (ha i) (hb i) hK hi (hz i) (hab i)
  exact ⟨aux a b ha hb hz hab hba, aux b a hb ha (fun i => (hz i).symm) hba hab⟩

theorem comparison_limsup {ι : Type*} {l : Filter ι} [l.NeBot] {a b t : ι → ℝ}
    {K : ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hK : 0 < K)
    (hz : ∀ i, a i = 0 ↔ b i = 0)
    (hab : ∀ i, b i ≤ K * a i) (hba : ∀ i, a i ≤ K * b i)
    (ht : Tendsto t l atTop) :
    limsup (fun i => logarithmicRate (t i) (a i)) l =
    limsup (fun i => logarithmicRate (t i) (b i)) l := by
  have hd : Tendsto (fun i => ((Real.log K / t i : ℝ) : EReal)) l (𝓝 0) := by
    exact EReal.tendsto_coe.mpr (tendsto_const_nhds.div_atTop ht)
  have hds : limsup (fun i => ((Real.log K / t i : ℝ) : EReal)) l = 0 := hd.limsup_eq
  have aux (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
      (hz : ∀ i, a i = 0 ↔ b i = 0) (hab : ∀ i, b i ≤ K*a i) :
      limsup (fun i => logarithmicRate (t i) (b i)) l ≤
      limsup (fun i => logarithmicRate (t i) (a i)) l := by
    have hh : ∀ᶠ i in l, logarithmicRate (t i) (b i) ≤
        logarithmicRate (t i) (a i) + ((Real.log K / t i : ℝ) : EReal) := by
      filter_upwards [ht.eventually (eventually_gt_atTop 0)] with i hi
      exact logarithmicRate_le (ha i) (hb i) hK hi (hz i) (hab i)
    have hsum := EReal.limsup_add_le (u := fun i => logarithmicRate (t i) (a i))
      (v := fun i => ((Real.log K / t i : ℝ) : EReal)) (f := l)
      (Or.inr (by rw [hds]; simp)) (Or.inr (by rw [hds]; simp))
    have hm : limsup (fun i => logarithmicRate (t i) (b i)) l ≤
        limsup ((fun i => logarithmicRate (t i) (a i)) +
          (fun i => ((Real.log K / t i : ℝ) : EReal))) l := limsup_le_limsup hh
    exact hm.trans (by simpa only [hds, add_zero, Pi.add_apply] using hsum)
  exact le_antisymm (aux b a hb ha (fun i => (hz i).symm) hba) (aux a b ha hb hz hab)

theorem magnitude_agreement {ι : Type*} {l : Filter ι} [l.NeBot] {a b t : ι → ℝ}
    {K : ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hK : 0 < K)
    (hz : ∀ i, a i = 0 ↔ b i = 0)
    (hab : ∀ i, b i ≤ K * a i) (hba : ∀ i, a i ≤ K * b i)
    (ht : Tendsto t l atTop) :
    RateAgreement l (fun i => logarithmicRate (t i) (a i))
      (fun i => logarithmicRate (t i) (b i)) := by
  have hh := comparison_tendsto ha hb hK hz hab hba ht
  refine ⟨hh, ?_, comparison_limsup ha hb hK hz hab hba ht⟩
  apply Option.ext
  intro z
  exact (partialLimit_some_iff l _ z).trans ((hh z).trans (partialLimit_some_iff l _ z).symm)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

@[simp] theorem transportedOperator_apply (e : E ≃L[ℝ] F) (L : E →L[ℝ] E) (w : F) :
    transportedOperator e L w = e (L (e.symm w)) := rfl

@[simp] theorem transportedOperator_apply_image (e : E ≃L[ℝ] F)
    (L : E →L[ℝ] E) (w : E) : transportedOperator e L (e w) = e (L w) := by simp

@[simp] theorem transportedOperator_symm (e : E ≃L[ℝ] F) (L : E →L[ℝ] E) :
    transportedOperator e.symm (transportedOperator e L) = L := by ext; simp

@[simp] theorem transportedOperator_eq_zero (e : E ≃L[ℝ] F) (L : E →L[ℝ] E) :
    transportedOperator e L = 0 ↔ L = 0 := by
  constructor
  · intro h
    have := congrArg (transportedOperator e.symm) h
    simpa only [transportedOperator_symm, show transportedOperator e.symm 0 = 0 from by ext; simp] using this
  · rintro rfl
    ext
    simp

private theorem ratio_le {a b c d C D : ℝ} (hb : 0 < b) (hd : 0 < d)
    (hc : 0 ≤ c) (hC : 0 ≤ C) (hac : a ≤ C*c) (hdb : d ≤ D*b) :
    a/b ≤ (C*D)*(c/d) := by
  apply (div_le_iff₀ hb).mpr
  apply (mul_le_mul_iff_left₀ hd).mp
  calc
    a*d ≤ (C*c)*d := mul_le_mul_of_nonneg_right hac hd.le
    _ ≤ (C*c)*(D*b) := mul_le_mul_of_nonneg_left hdb (mul_nonneg hC hc)
    _ = ((C*D)*(c/d)*b)*d := by field_simp

private theorem transportedOperator_norm_le (e : E ≃L[ℝ] F) (L : E →L[ℝ] E) :
    ‖transportedOperator e L‖ ≤
      ((‖e.toContinuousLinearMap‖ + 1) * (‖e.symm.toContinuousLinearMap‖ + 1))*‖L‖ := by
  unfold transportedOperator
  calc
    ‖e.toContinuousLinearMap.comp (L.comp e.symm.toContinuousLinearMap)‖ ≤
      ‖e.toContinuousLinearMap‖ * (‖L‖ * ‖e.symm.toContinuousLinearMap‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ ((‖e.toContinuousLinearMap‖ + 1) * (‖e.symm.toContinuousLinearMap‖ + 1))*‖L‖ := by
      nlinarith [norm_nonneg e.toContinuousLinearMap, norm_nonneg e.symm.toContinuousLinearMap,
        norm_nonneg L]

theorem norm_comparison : Specs.D13Unified.Ch18.NormIndependence.normComparisonStatement
    (E := E) (F := F) := by
  intro e
  let C := ‖e.toContinuousLinearMap‖ + 1
  let D := ‖e.symm.toContinuousLinearMap‖ + 1
  have hC : 1 ≤ C := by dsimp [C]; linarith [norm_nonneg e.toContinuousLinearMap]
  have hD : 1 ≤ D := by dsimp [D]; linarith [norm_nonneg e.symm.toContinuousLinearMap]
  have hc : 0 ≤ C := le_trans zero_le_one hC
  have hd : 0 ≤ D := le_trans zero_le_one hD
  have he (w : E) : ‖e w‖ ≤ C * ‖w‖ := by
    exact (e.toContinuousLinearMap.le_opNorm w).trans (by dsimp [C]; nlinarith [norm_nonneg w])
  have hei (w : F) : ‖e.symm w‖ ≤ D * ‖w‖ := by
    exact (e.symm.toContinuousLinearMap.le_opNorm w).trans (by dsimp [D]; nlinarith [norm_nonneg w])
  refine ⟨C*D, by nlinarith, ?_, ?_⟩
  · intro v w hv
    have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hevp : 0 < ‖e v‖ := norm_pos_iff.mpr (by simpa using hv)
    constructor
    · exact ratio_le hevp hvp (norm_nonneg w) hc (he w) (by simpa using hei (e v))
    · simpa [mul_comm D C] using
        ratio_le hvp hevp (norm_nonneg (e w)) hd (by simpa using hei (e w)) (he v)
  · intro L
    refine ⟨transportedOperator_norm_le e L, ?_⟩
    simpa [C, D, mul_comm] using
      transportedOperator_norm_le e.symm (transportedOperator e L)

private theorem log_abs_sub_le {a b K : ℝ} (ha : 0 < a) (hb : 0 < b) (hK : 0 < K)
    (hab : b ≤ K*a) (hba : a ≤ K*b) : |Real.log b - Real.log a| ≤ Real.log K := by
  have h₁ := Real.log_le_log hb hab
  have h₂ := Real.log_le_log ha hba
  rw [Real.log_mul hK.ne' ha.ne'] at h₁
  rw [Real.log_mul hK.ne' hb.ne'] at h₂
  rw [abs_le]
  constructor <;> linarith

theorem logarithmic_comparison :
    Specs.D13Unified.Ch18.NormIndependence.logarithmicComparisonStatement (E := E) (F := F) := by
  intro e
  obtain ⟨K, hK, hRatio, hOp⟩ := norm_comparison e
  have hKp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  refine ⟨Real.log K, Real.log_nonneg hK, ?_, ?_⟩
  · intro v w hv hw
    exact log_abs_sub_le
      (div_pos (norm_pos_iff.mpr hw) (norm_pos_iff.mpr hv))
      (div_pos (norm_pos_iff.mpr (by simpa using hw)) (norm_pos_iff.mpr (by simpa using hv)))
      hKp (hRatio v w hv).1 (hRatio v w hv).2
  · intro L hL
    exact log_abs_sub_le (norm_pos_iff.mpr hL)
      (norm_pos_iff.mpr (fun hz => hL ((transportedOperator_eq_zero e L).mp hz)))
      hKp (hOp L).1 (hOp L).2

theorem operator_family_norm_independence :
    Specs.D13Unified.Ch18.NormIndependence.operatorFamilyStatement (E := E) (F := F) := by
  intro e ι l _ t ht L
  obtain ⟨K, hK, _, hOp⟩ := norm_comparison e
  change RateAgreement l (fun i => logarithmicRate (t i) ‖L i‖)
    (fun i => logarithmicRate (t i) ‖transportedOperator e (L i)‖)
  exact magnitude_agreement (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    (lt_of_lt_of_le zero_lt_one hK)
    (fun i => by simp only [norm_eq_zero, transportedOperator_eq_zero])
    (fun i => (hOp (L i)).1) (fun i => (hOp (L i)).2) ht

theorem family_norm_independence :
    Specs.D13Unified.Ch18.NormIndependence.familyStatement (E := E) (F := F) := by
  intro e ι l _ t ht L v hv
  refine ⟨?_, operator_family_norm_independence e l t ht L⟩
  obtain ⟨K, hK, hRatio, _⟩ := norm_comparison e
  change RateAgreement l (fun i => logarithmicRate (t i) (‖L i v‖ / ‖v‖))
    (fun i => logarithmicRate (t i) (‖transportedOperator e (L i) (e v)‖ / ‖e v‖))
  simp only [transportedOperator_apply_image]
  exact magnitude_agreement (fun _ => div_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun _ => div_nonneg (norm_nonneg _) (norm_nonneg _))
    (lt_of_lt_of_le zero_lt_one hK)
    (fun i => by simp [div_eq_zero_iff, hv])
    (fun i => (hRatio v (L i v) hv).1) (fun i => (hRatio v (L i v) hv).2) ht

theorem finite_dimensional_norm_independence :
    Specs.D13Unified.Ch18.NormIndependence.finiteDimensionalStatement (E := E) (F := F) := by
  intro _ _ e ι l _ t ht L v hv
  exact family_norm_independence e.toContinuousLinearEquiv l t ht L v hv

private theorem tendsto_successor_time :
    Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)

theorem discrete_norm_independence :
    Specs.D13Unified.Ch18.NormIndependence.discreteStatement (E := E) (F := F) := by
  intro e f x v hv
  simpa only [Specs.D13Unified.Ch18.GrowthDefinitions.discreteDirectionalRate,
    Specs.D13Unified.Ch15.DiscreteDefinitions.iterate, Nat.cast_add, Nat.cast_one] using
    family_norm_independence e atTop _ tendsto_successor_time
      (fun n : ℕ => fderivWithin ℝ (f.value^[n+1]) f.domain x) v hv

theorem flow_norm_independence :
    Specs.D13Unified.Ch18.NormIndependence.flowStatement (E := E) (F := F) := by
  intro e Φ x v hv hc
  exact family_norm_independence e atTop (fun t : Ioi (0 : ℝ) => (t : ℝ))
    (tendsto_comp_val_Ioi_atTop.mpr tendsto_id)
    (fun t : Ioi (0 : ℝ) => fderivWithin ℝ (Φ.value t) {y | ((t : ℝ),y) ∈ Φ.domain} x) v hv

@[simp] theorem transportedOperator_id (e : E ≃L[ℝ] F) :
    transportedOperator e (ContinuousLinearMap.id ℝ E) = ContinuousLinearMap.id ℝ F := by
  ext; simp

@[simp] theorem transportedOperator_comp (e : E ≃L[ℝ] F) (L M : E →L[ℝ] E) :
    transportedOperator e (L.comp M) = (transportedOperator e L).comp (transportedOperator e M) := by
  ext; simp

theorem transported_cocycle {X : Type*} (e : E ≃L[ℝ] F) (T : X → X)
    (A : X → E →L[ℝ] E) (n : ℕ) (x : X) :
    transportedOperator e (cocycleProduct T A n x) =
      cocycleProduct T (fun y => transportedOperator e (A y)) n x := by
  induction n with
  | zero => exact transportedOperator_id e
  | succ n ih =>
    change transportedOperator e ((A (T^[n] x)).comp (cocycleProduct T A n x)) = _
    rw [transportedOperator_comp, ih]
    rfl

theorem cocycle_norm_independence :
    Specs.D13Unified.Ch18.NormIndependence.cocycleStatement (E := E) (F := F) := by
  intro e X T A x v hv
  have hh := family_norm_independence e atTop _ tendsto_successor_time
    (fun n : ℕ => cocycleProduct T A (n+1) x) v hv
  simp only [transported_cocycle] at hh
  exact ⟨hh.1, hh.1.2.1, by simpa only [Specs.D13Unified.Ch18.GrowthDefinitions.cocycleOperatorUpperRate,
    Nat.cast_add, Nat.cast_one] using hh.2.2.2⟩

theorem transported_matrixOperator [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (e : E ≃L[ℝ] F) {d : ℕ} (b : Module.Basis (Fin d) ℝ E)
    (M : Matrix (Fin d) (Fin d) ℝ) :
    matrixOperator (b.map e.toLinearEquiv) M = transportedOperator e (matrixOperator b M) := by
  suffices h : (matrixOperator (b.map e.toLinearEquiv) M).toLinearMap =
      (transportedOperator e (matrixOperator b M)).toLinearMap by
    exact ContinuousLinearMap.ext (fun y => congrArg (fun L : F →ₗ[ℝ] F => L y) h)
  apply (b.map e.toLinearEquiv).ext
  intro i
  change (Matrix.toLin (b.map e.toLinearEquiv) (b.map e.toLinearEquiv) M)
    ((b.map e.toLinearEquiv) i) = e ((Matrix.toLin b b M) (e.symm ((b.map e.toLinearEquiv) i)))
  rw [Matrix.toLin_self]
  simp only [Module.Basis.map_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
    ContinuousLinearEquiv.symm_apply_apply, Matrix.toLin_self, map_sum, map_smul]

theorem matrix_norm_independence :
    Specs.D13Unified.Ch18.NormIndependence.matrixStatement (E := E) (F := F) := by
  intro _ _ e X d b T A x v hv
  have hh := family_norm_independence e atTop _ tendsto_successor_time
    (fun n : ℕ => matrixOperator b (matrixCocycleProduct T A (n+1) x)) v hv
  simp only [← transported_matrixOperator] at hh
  exact ⟨hh.1, hh.1.2.1, by simpa only [Specs.D13Unified.Ch18.GrowthDefinitions.matrixOperatorUpperRate,
    Nat.cast_add, Nat.cast_one] using hh.2.2.2⟩

theorem derivative_transport :
    Specs.D13Unified.Ch18.NormIndependence.derivativeTransportStatement (E := E) (F := F) := by
  intro e f s x hs hx hf
  rw [fderivWithin_of_isOpen (e.isOpenMap s hs) (mem_image_of_mem e hx),
    fderivWithin_of_isOpen hs hx]
  have hf' : HasFDerivAt f (fderiv ℝ f x) (e.symm (e x)) := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using
      (hf.differentiableAt (hs.mem_nhds hx)).hasFDerivAt
  have h := e.toContinuousLinearMap.hasFDerivAt.comp (e x)
    (hf'.comp (e x) e.symm.toContinuousLinearMap.hasFDerivAt)
  convert h.fderiv using 1 <;> rfl

theorem complex_operator_family_norm_independence :
    Specs.D13Unified.Ch18.NormIndependence.complexOperatorFamilyStatement := by
  intro E F _ _ _ _ e ι l _ t ht L
  let := NormedSpace.restrictScalars ℝ ℂ E
  let := NormedSpace.restrictScalars ℝ ℂ F
  let er : E ≃L[ℝ] F :=
    { e.toLinearEquiv.restrictScalars ℝ with
      continuous_toFun := e.continuous
      continuous_invFun := e.symm.continuous }
  have ho := operator_family_norm_independence er l t ht (fun i => (L i).restrictScalars ℝ)
  have hop (i : ι) : transportedOperator er ((L i).restrictScalars ℝ) =
      (e.toContinuousLinearMap.comp ((L i).comp e.symm.toContinuousLinearMap)).restrictScalars ℝ := by
    ext
    rfl
  change RateAgreement l (fun i => logarithmicRate (t i) ‖(L i).restrictScalars ℝ‖)
    (fun i => logarithmicRate (t i) ‖transportedOperator er ((L i).restrictScalars ℝ)‖) at ho
  simpa only [hop, ContinuousLinearMap.norm_restrictScalars] using ho

theorem complex_family_norm_independence :
    Specs.D13Unified.Ch18.NormIndependence.complexFamilyStatement := by
  intro E F _ _ _ _ e ι l _ t ht L v hv
  let := NormedSpace.restrictScalars ℝ ℂ E
  let := NormedSpace.restrictScalars ℝ ℂ F
  let er : E ≃L[ℝ] F :=
    { e.toLinearEquiv.restrictScalars ℝ with
      continuous_toFun := e.continuous
      continuous_invFun := e.symm.continuous }
  have hh := family_norm_independence er l t ht (fun i => (L i).restrictScalars ℝ) v hv
  have hop (i : ι) : transportedOperator er ((L i).restrictScalars ℝ) =
      (e.toContinuousLinearMap.comp ((L i).comp e.symm.toContinuousLinearMap)).restrictScalars ℝ := by
    ext
    rfl
  constructor
  · have hd := hh.1
    change RateAgreement l (fun i => logarithmicRate (t i) (‖(L i).restrictScalars ℝ v‖ / ‖v‖))
      (fun i => logarithmicRate (t i)
        (‖transportedOperator er ((L i).restrictScalars ℝ) (er v)‖ / ‖er v‖)) at hd
    simp only [transportedOperator_apply_image] at hd
    exact hd
  · have ho := hh.2
    change RateAgreement l (fun i => logarithmicRate (t i) ‖(L i).restrictScalars ℝ‖)
      (fun i => logarithmicRate (t i) ‖transportedOperator er ((L i).restrictScalars ℝ)‖) at ho
    simpa only [hop, ContinuousLinearMap.norm_restrictScalars] using ho

end D13Unified.Ch18.NormIndependence
