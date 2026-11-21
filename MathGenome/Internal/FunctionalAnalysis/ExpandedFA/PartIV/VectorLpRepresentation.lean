import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarLpDuality
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Operator.Mul
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.VectorLpRepresentation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.VectorRadonNikodym
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal Topology symmDiff
universe u v

namespace ExpandedFA.PartIV.VectorLpRepresentation
open VectorLpRepresentationSpec

/-- Evaluation followed by integration is scalar-linear in both arguments. -/
def pairing : PairingType.{u,v} := PairingValue

theorem pairing_formula : PairingFormula.{u,v} := by
  intro 𝕜 _ X E _ _ _ μ p q _ _ _ g f
  let B : (E →L[𝕜] 𝕜) →L[𝕜] E →L[𝕜] 𝕜 := ContinuousLinearMap.id 𝕜 _
  exact ⟨memLp_one_iff_integrable.mp (B.memLp_of_bilin 1 (Lp.memLp g) (Lp.memLp f)),
    B.lpPairing_eq_integral g f⟩

theorem pairing_apply_bound {𝕜 : Type} [RCLike 𝕜] {X : Type u} {E : Type v}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (μ : Measure X) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (g : Lp (E →L[𝕜] 𝕜) q μ) (f : Lp E p μ) :
    ‖PairingValue 𝕜 μ p q g f‖ ≤ ‖g‖ * ‖f‖ := by
  let B : (E →L[𝕜] 𝕜) →L[𝕜] E →L[𝕜] 𝕜 := ContinuousLinearMap.id 𝕜 _
  calc
    ‖PairingValue 𝕜 μ p q g f‖ = ‖L1.integral (B.holder 1 g f)‖ := by
      simp only [PairingValue, ContinuousLinearMap.lpPairing,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.postcomp_apply,
        ContinuousLinearMap.holderL_apply_apply, ← L1.integral_eq', B]
    _ ≤ ‖B.holder 1 g f‖ := L1.norm_integral_le _
    _ ≤ ‖B‖ * ‖g‖ * ‖f‖ := B.norm_holder_apply_apply_le g f
    _ ≤ 1 * ‖g‖ * ‖f‖ := by
      gcongr
      exact ContinuousLinearMap.norm_id_le
    _ = ‖g‖ * ‖f‖ := by rw [one_mul]

theorem pairing_bound : PairingBound.{u,v} := by
  intro 𝕜 _ X E _ _ _ μ p q _ _ _ g
  exact (PairingValue 𝕜 μ p q g).opNorm_le_bound (norm_nonneg _)
    (pairing_apply_bound μ p q g)

/-- Surjectivity of canonical evaluation passes to the scalar-linear dual. -/
theorem dual_reflexive (𝕜 : Type) [RCLike 𝕜] (E : Type v)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (hE : P1.C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E) :
    P1.C04CanonicalMap.Spec.IsReflexiveValue 𝕜 (E →L[𝕜] 𝕜) := by
  intro F
  let ℓ : E →L[𝕜] 𝕜 := F.comp (P1.C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E)
  refine ⟨ℓ, ?_⟩
  ext U
  obtain ⟨x, rfl⟩ := hE U
  rfl

/-- Phase-adjusted almost norming vectors; the zero space is allowed. -/
theorem exists_almost_norming {𝕜 : Type} [RCLike 𝕜] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (ℓ : E →L[𝕜] 𝕜) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : E, ‖x‖ ≤ 1 ∧ ‖ℓ‖ ≤ RCLike.re (ℓ x) + ε := by
  obtain ⟨y, hy, hval⟩ := ℓ.exists_lt_apply_of_lt_opNorm (by linarith : ‖ℓ‖ - ε < ‖ℓ‖)
  let c : 𝕜 := star (ℓ y) / (‖ℓ y‖ : 𝕜)
  have hc : ‖c‖ ≤ 1 := by
    simp only [c, norm_div, norm_star, RCLike.norm_ofReal, abs_norm]
    exact div_self_le_one _
  have hcy : c * ℓ y = (‖ℓ y‖ : 𝕜) := by
    by_cases hz : ℓ y = 0
    · simp [c, hz]
    · have hn : (‖ℓ y‖ : 𝕜) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
      change (starRingEnd 𝕜) (ℓ y) / (‖ℓ y‖ : 𝕜) * ℓ y = _
      rw [div_mul_eq_mul_div, RCLike.conj_mul, pow_two, mul_div_cancel_right₀ _ hn]
  refine ⟨c • y, ?_, ?_⟩
  · rw [norm_smul]
    exact (mul_le_mul hc hy.le (norm_nonneg _) zero_le_one).trans (by simp)
  · rw [map_smul, smul_eq_mul, hcy, RCLike.ofReal_re]
    linarith

/-- A finite bound on disjoint measurable partition costs bounds total variation. -/
theorem variation_bound_of_partition_bound {X : Type u} {Y : Type v}
    [MeasurableSpace X] [NormedAddCommGroup Y] (m : VectorMeasure X Y) (C : ℝ)
    (h : ∀ P : Finset (Set X), (∀ A ∈ P, MeasurableSet A) →
      (P : Set (Set X)).PairwiseDisjoint id → ∑ A ∈ P, ‖m A‖ ≤ C) :
    m.variation univ ≤ ENNReal.ofReal C := by
  classical
  by_contra! hlarge
  obtain ⟨P, _, hd, hP, hlt⟩ := m.exists_lt_sum_of_lt_variation MeasurableSet.univ hlarge
  have hb := ENNReal.ofReal_le_ofReal (h P hP hd)
  have hsum : ∑ A ∈ P, ‖m A‖ₑ ≤ ENNReal.ofReal C := by
    simpa only [← ofReal_norm,
      ENNReal.ofReal_sum_of_nonneg (fun A _ => norm_nonneg _)] using hb
  exact hlt.not_ge hsum

section FiniteMeasure
variable {𝕜 : Type} [RCLike 𝕜] {X : Type u} {E : Type v}
  [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (μ : Measure X) [IsFiniteMeasure μ] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Insertion of a vector as a constant on a measurable set. -/
def indicatorEmbedding (A : Set X) (hA : MeasurableSet A) : E →L[𝕜] Lp E p μ :=
  LinearMap.mkContinuous
    { toFun := indicatorConstLp p hA (measure_ne_top μ A)
      map_add' := fun _ _ => indicatorConstLp_add.symm
      map_smul' := by
        intro c x
        apply Lp.ext
        filter_upwards [indicatorConstLp_coeFn (μ := μ) (p := p) (hs := hA)
          (hμs := measure_ne_top μ A) (c := c • x),
          Lp.coeFn_smul c (indicatorConstLp p hA (measure_ne_top μ A) x),
          indicatorConstLp_coeFn (μ := μ) (p := p) (hs := hA)
          (hμs := measure_ne_top μ A) (c := x)] with t ht hs hx
        simp only [RingHom.id_apply]
        rw [ht, hs, Pi.smul_apply, hx]
        by_cases h : t ∈ A <;> simp [h] }
    (μ.real A ^ (1 / p.toReal)) (fun x => by
      change ‖indicatorConstLp (μ := μ) p hA (measure_ne_top μ A) x‖ ≤ _
      simpa only [mul_comm] using (norm_indicatorConstLp_le (μ := μ) (p := p)
        (hs := hA) (hμs := measure_ne_top μ A) (c := x)))

/-- The dual vector assigned to a measurable set, before countable additivity. -/
def indicatorFunctional (L : Lp E p μ →L[𝕜] 𝕜)
    (A : Set X) (hA : MeasurableSet A) : E →L[𝕜] 𝕜 :=
  L.comp (indicatorEmbedding μ p A hA)

@[simp] theorem indicatorFunctional_apply (L : Lp E p μ →L[𝕜] 𝕜)
    (A : Set X) (hA : MeasurableSet A) (x : E) :
    indicatorFunctional μ p L A hA x =
      L (indicatorConstLp p hA (measure_ne_top μ A) x) := rfl

/-- A uniform estimate for every finite disjoint family. The vectors chosen
for its members may differ; this is what yields finite variation. -/
theorem sum_norm_indicatorFunctional_le {ι : Type*} (I : Finset ι)
    (A : ι → Set X) (hA : ∀ i, MeasurableSet (A i))
    (hd : Pairwise fun i j => Disjoint (A i) (A j))
    (L : Lp E p μ →L[𝕜] 𝕜) :
    ∑ i ∈ I, ‖indicatorFunctional μ p L (A i) (hA i)‖ ≤
      ‖L‖ * (μ.real univ ^ (1 / p.toReal)) := by
  classical
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε / (I.card + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  choose x hx hv using fun i => exists_almost_norming
    (indicatorFunctional μ p L (A i) (hA i)) hδ
  let f : Lp E p μ := ∑ i ∈ I, indicatorConstLp p (hA i) (measure_ne_top μ _) (x i)
  have hcoe : (f : X → E) =ᵐ[μ] fun t => ∑ i ∈ I, (A i).indicator (fun _ => x i) t := by
    refine (Lp.coeFn_fun_finsetSum I _).trans ?_
    have hh : ∀ i ∈ I, ⇑(indicatorConstLp (μ := μ) p (hA i) (measure_ne_top μ _) (x i))
        =ᵐ[μ] (A i).indicator (fun _ => x i) := fun i _ => indicatorConstLp_coeFn
    filter_upwards [eventuallyEq_sum hh] with t ht
    simpa only [Finset.sum_apply] using ht
  have hf : ∀ᵐ t ∂μ, ‖f t‖ ≤ 1 := by
    filter_upwards [hcoe] with t ht
    rw [ht]
    by_cases hex : ∃ i ∈ I, t ∈ A i
    · obtain ⟨i, hi, hti⟩ := hex
      rw [Finset.sum_eq_single i]
      · simpa [hti] using hx i
      · intro j hj hji
        have htj : t ∉ A j := fun htj => (hd hji).le_bot ⟨htj, hti⟩
        simp [htj]
      · exact fun h => (h hi).elim
    · have hz : ∀ i ∈ I, t ∉ A i := by simpa using hex
      rw [Finset.sum_eq_zero (fun i hi => by simp [hz i hi]), norm_zero]
      exact zero_le_one
  have hfn : ‖f‖ ≤ μ.real univ ^ (1 / p.toReal) := by
    simpa [measureUnivNNReal, measureReal_def, ENNReal.coe_toNNReal_eq_toReal] using Lp.norm_le_of_ae_bound zero_le_one hf
  have hval : RCLike.re (L f) =
      ∑ i ∈ I, RCLike.re (indicatorFunctional μ p L (A i) (hA i) (x i)) := by
    simp [f]
  have hsum : (∑ i ∈ I, ‖indicatorFunctional μ p L (A i) (hA i)‖) ≤
      RCLike.re (L f) + I.card * δ := by
    calc
      _ ≤ ∑ i ∈ I, (RCLike.re (indicatorFunctional μ p L (A i) (hA i) (x i)) + δ) :=
        Finset.sum_le_sum (fun i _ => hv i)
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hval]
  have hre : RCLike.re (L f) ≤ ‖L‖ * (μ.real univ ^ (1 / p.toReal)) :=
    (RCLike.re_le_norm _).trans ((L.le_opNorm f).trans
      (mul_le_mul_of_nonneg_left hfn (norm_nonneg _)))
  have hcard : (I.card : ℝ) * δ ≤ ε := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < I.card + 1)).mpr
    nlinarith
  linarith

/-- Finite additivity of constant indicators in the vector-valued Lp space. -/
theorem sum_indicatorConstLp {ι : Type*} (I : Finset ι)
    (A : ι → Set X) (hA : ∀ i, MeasurableSet (A i))
    (hd : Pairwise fun i j => Disjoint (A i) (A j)) (x : E) :
    ∑ i ∈ I, indicatorConstLp (μ := μ) p (hA i) (measure_ne_top μ _) x =
      indicatorConstLp p (Finset.measurableSet_biUnion I (fun i _ => hA i))
        (measure_ne_top μ _) x := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi, ih]
    simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left]
    rw [indicatorConstLp_disjoint_union (hA i)
      (Finset.measurableSet_biUnion I (fun j _ => hA j))
      (measure_ne_top μ _) (measure_ne_top μ _)]
    exact disjoint_iUnion_right.mpr fun j => disjoint_iUnion_right.mpr fun hj =>
      hd (fun hij => hi (hij ▸ hj))

/-- Norm countable additivity, using the partition estimate for absolute
convergence and scalar evaluations to identify the sum. -/
theorem hasSum_indicatorFunctional (hp : p ≠ ∞)
    (L : Lp E p μ →L[𝕜] 𝕜) (A : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i))
    (hd : Pairwise fun i j => Disjoint (A i) (A j)) :
    HasSum (fun i => indicatorFunctional μ p L (A i) (hA i))
      (indicatorFunctional μ p L (⋃ i, A i) (MeasurableSet.iUnion hA)) := by
  have hs : Summable (fun i => ‖indicatorFunctional μ p L (A i) (hA i)‖) :=
    summable_of_sum_le (fun _ => norm_nonneg _)
      (fun I => sum_norm_indicatorFunctional_le μ p I A hA hd L)
  have hv : Summable (fun i => indicatorFunctional μ p L (A i) (hA i)) := hs.of_norm
  have htail := tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
    (fun i => (hA i).nullMeasurableSet) hd (μ := μ)
  have hsets : Tendsto
      (fun n => μ ((⋃ i ∈ Finset.range n, A i) ∆ ⋃ i, A i)) atTop (𝓝 0) := by
    convert htail using 1
    ext n
    congr 1
    ext t
    simp only [mem_symmDiff, mem_iUnion, exists_prop, Finset.mem_range]
    constructor
    · rintro (⟨_, h⟩ | ⟨⟨i, hti⟩, hnot⟩)
      · exact (h (by aesop)).elim
      · exact ⟨i, Nat.le_of_not_gt (fun hi => hnot ⟨i, hi, hti⟩), hti⟩
    · rintro ⟨i, hi, hti⟩
      right
      refine ⟨⟨i, hti⟩, ?_⟩
      rintro ⟨j, hj, htj⟩
      exact (hd (ne_of_lt (hj.trans_le hi))).le_bot ⟨htj, hti⟩
  have heq : (∑' i, indicatorFunctional μ p L (A i) (hA i)) =
      indicatorFunctional μ p L (⋃ i, A i) (MeasurableSet.iUnion hA) := by
    ext x
    have h₁ := ((ContinuousLinearMap.apply 𝕜 𝕜 x).hasSum hv.hasSum).tendsto_sum_nat
    have h₂ : Tendsto
        (fun n => ∑ i ∈ Finset.range n, indicatorFunctional μ p L (A i) (hA i) x)
        atTop (𝓝 (indicatorFunctional μ p L (⋃ i, A i) (MeasurableSet.iUnion hA) x)) := by
      have he n : (∑ i ∈ Finset.range n, indicatorFunctional μ p L (A i) (hA i) x) =
          L (indicatorConstLp p
            (Finset.measurableSet_biUnion (Finset.range n) (fun i _ => hA i))
            (measure_ne_top μ _) x) := by
        simp only [indicatorFunctional_apply, ← map_sum]
        rw [sum_indicatorConstLp μ p _ A hA hd]
      simp_rw [he]
      exact L.continuous.continuousAt.tendsto.comp (tendsto_indicatorConstLp_set (hs := MeasurableSet.iUnion hA)
        (hμs := measure_ne_top μ _) hp hsets)
    exact tendsto_nhds_unique h₁ h₂
  rw [← heq]
  exact hv.hasSum

open scoped Classical in
/-- The functional's finite-measure E'-valued vector measure. -/
def functionalMeasure (hp : p ≠ ∞) (L : Lp E p μ →L[𝕜] 𝕜) :
    VectorMeasure X (E →L[𝕜] 𝕜) where
  measureOf' A := if hA : MeasurableSet A then indicatorFunctional μ p L A hA else 0
  empty' := by ext x; simp
  not_measurable' _ hA := by simp [hA]
  m_iUnion' _ hA hd := by
    simpa only [dite_eq_left (hA _), dite_eq_left (MeasurableSet.iUnion hA)] using
      hasSum_indicatorFunctional μ p hp L _ hA hd

@[simp] theorem functionalMeasure_apply (hp : p ≠ ∞)
    (L : Lp E p μ →L[𝕜] 𝕜) (A : Set X) (hA : MeasurableSet A) :
    functionalMeasure μ p hp L A = indicatorFunctional μ p L A hA := by
  simp only [functionalMeasure, VectorMeasure.coe_mk, dite_eq_left hA]

/-- Quantitative finite variation, proved before any density is assumed. -/
theorem functionalMeasure_variation_bound (hp : p ≠ ∞)
    (L : Lp E p μ →L[𝕜] 𝕜) :
    (VectorMeasure.variation (V := E →L[𝕜] 𝕜) (functionalMeasure μ p hp L)) univ ≤
      ENNReal.ofReal (‖L‖ * μ.real univ ^ (1 / p.toReal)) := by
  classical
  apply variation_bound_of_partition_bound
  intro P hP hd
  have hd' : Pairwise fun i j : P => Disjoint (i : Set X) (j : Set X) := by
    intro i j hij
    exact hd i.property j.property (fun heq => hij (Subtype.ext heq))
  have hb := sum_norm_indicatorFunctional_le μ p (Finset.univ : Finset P)
    (fun i => (i : Set X)) (fun i => hP i i.property) hd' L
  calc
    _ = ∑ i : P, ‖functionalMeasure μ p hp L (i : Set X)‖ :=
      (Finset.sum_coe_sort P _).symm
    _ = ∑ i : P, ‖indicatorFunctional μ p L (i : Set X) (hP i i.property)‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [functionalMeasure_apply μ p hp L _ (hP i i.property)]
    _ ≤ _ := hb

theorem functionalMeasure_null (hp : p ≠ ∞) (L : Lp E p μ →L[𝕜] 𝕜)
    (A : Set X) (hA : MeasurableSet A) (hz : μ A = 0) :
    functionalMeasure μ p hp L A = 0 := by
  ext x
  rw [functionalMeasure_apply μ p hp L A hA, indicatorFunctional_apply]
  have hi : indicatorConstLp (μ := μ) p hA (measure_ne_top μ _) x = 0 := by
    apply Lp.ext
    filter_upwards [indicatorConstLp_coeFn (μ := μ) (p := p) (hs := hA)
      (hμs := measure_ne_top μ _) (c := x), measure_eq_zero_iff_ae_notMem.mp hz,
      Lp.coeFn_zero E p μ] with t ht htA ht0
    rw [ht, Set.indicator_of_notMem htA]
    exact ht0.symm
  rw [hi, map_zero]
  rfl

end FiniteMeasure

/-- The finite-measure density is strongly measurable in norm, even when E
and its dual are not separable. All vector RN hypotheses were proved above. -/
theorem finite_density : FiniteDensity.{u,v} := by
  intro 𝕜 _ X E _ _ _ _ hE μ _ p _ hp L
  letI : NormedSpace ℝ (E →L[𝕜] 𝕜) := NormedSpace.restrictScalars ℝ 𝕜 (E →L[𝕜] 𝕜)
  let m := functionalMeasure μ p hp L
  have hm : (VectorMeasure.variation (V := E →L[𝕜] 𝕜) m) univ < ∞ :=
    (functionalMeasure_variation_bound μ p hp L).trans_lt ENNReal.ofReal_lt_top
  obtain ⟨g, hg, _, hrep, _⟩ := VectorRadonNikodym.vector_radon_nikodym
    𝕜 (dual_reflexive 𝕜 E hE) μ m hm (functionalMeasure_null μ p hp L)
  refine ⟨g, hg, ?_⟩
  intro A hA x
  calc
    L (indicatorConstLp p hA (measure_ne_top μ A) x) = m A x := by
      rw [functionalMeasure_apply μ p hp L A hA, indicatorFunctional_apply]
    _ = (∫ t in A, g t ∂μ) x := congrArg (fun U : E →L[𝕜] 𝕜 => U x) (hrep A hA)
    _ = ∫ t in A, g t x ∂μ :=
      ((ContinuousLinearMap.apply 𝕜 𝕜 x).integral_comp_comm hg.restrict).symm

/-- A separable set of functionals admits a countable family in the primal
unit ball which almost norms every one of its members by real evaluation.
No separability of the primal space, or reflexivity, is needed. -/
theorem exists_countable_norming_family {𝕜 : Type} [RCLike 𝕜] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (s : Set (E →L[𝕜] 𝕜)) (hs : TopologicalSpace.IsSeparable s) :
    ∃ x : ℕ → E, (∀ n, ‖x n‖ ≤ 1) ∧
      ∀ ℓ ∈ s, ∀ ε : ℝ, 0 < ε → ∃ n, ‖ℓ‖ ≤ RCLike.re (ℓ (x n)) + ε := by
  classical
  let S := closure (s ∪ {0})
  letI : SeparableSpace S := (hs.union (finite_singleton _).isSeparable).closure.separableSpace
  letI : Nonempty S := ⟨⟨0, subset_closure (Or.inr (mem_singleton _))⟩⟩
  obtain ⟨a, ha⟩ := TopologicalSpace.exists_dense_seq S
  choose x hx hv using fun (j r : ℕ) => exists_almost_norming (a j).val
    (show (0 : ℝ) < 1 / (r + 1 : ℝ) by positivity)
  refine ⟨fun n => x (Nat.unpair n).1 (Nat.unpair n).2, fun n => hx _ _, ?_⟩
  intro ℓ hℓ ε hε
  obtain ⟨r, hr⟩ := exists_nat_one_div_lt (show (0 : ℝ) < ε / 3 by positivity)
  obtain ⟨j, hj⟩ := ha.exists_dist_lt (⟨ℓ, subset_closure (Or.inl hℓ)⟩ : S)
    (show (0 : ℝ) < ε / 3 by positivity)
  have hd : ‖(a j).val - ℓ‖ < ε / 3 := by
    simpa only [Subtype.dist_eq, dist_eq_norm, norm_sub_rev] using hj
  refine ⟨Nat.pair j r, ?_⟩
  simp only [Nat.unpair_pair]
  have hn := norm_sub_norm_le ℓ (a j).val
  rw [norm_sub_rev] at hn
  have he := RCLike.re_le_norm (((a j).val - ℓ) (x j r))
  have hb := (((a j).val - ℓ).le_opNorm (x j r)).trans
    (mul_le_of_le_one_right (norm_nonneg _) (hx j r))
  simp only [ContinuousLinearMap.sub_apply, map_sub] at he hb
  have hv' := hv j r
  linarith

/-- A strongly measurable dual-valued function has a strongly measurable
unit-ball test which almost norms it pointwise. The choice is made by the
first successful member of a countable norming family. -/
theorem exists_stronglyMeasurable_norming_test {𝕜 : Type} [RCLike 𝕜]
    {X : Type u} {E : Type v} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {g : X → (E →L[𝕜] 𝕜)} (hg : StronglyMeasurable g)
    {η : ℝ} (hη : 0 < η) :
    ∃ z : X → E, StronglyMeasurable z ∧ (∀ t, ‖z t‖ ≤ 1) ∧
      ∀ t, (1 - η) * ‖g t‖ ≤ RCLike.re (g t (z t)) := by
  classical
  obtain ⟨x, hx, hn⟩ := exists_countable_norming_family (range g) hg.isSeparable_range
  let P : X → ℕ → Prop := fun t n => (1 - η) * ‖g t‖ ≤ RCLike.re (g t (x n))
  have hP : ∀ t, ∃ n, P t n := by
    intro t
    by_cases hz : g t = 0
    · exact ⟨0, by simp [P, hz]⟩
    · obtain ⟨n, hn⟩ := hn (g t) (mem_range_self t) (η * ‖g t‖)
        (mul_pos hη (norm_pos_iff.mpr hz))
      exact ⟨n, by dsimp [P]; nlinarith⟩
  have hPm : ∀ n, MeasurableSet {t | P t n} := by
    intro n
    exact measurableSet_le (measurable_const.mul hg.norm.measurable)
      (RCLike.continuous_re.comp_stronglyMeasurable
        ((ContinuousLinearMap.apply 𝕜 𝕜 (x n)).continuous.comp_stronglyMeasurable hg)).measurable
  let k : X → ℕ := fun t => Nat.find (hP t)
  have hk : Measurable k := measurable_find hP hPm
  have hxsm : StronglyMeasurable x := StronglyMeasurable.of_discrete
  refine ⟨fun t => x (k t), hxsm.comp_measurable hk, fun t => hx (k t), ?_⟩
  exact fun t => Nat.find_spec (hP t)


section NormTesting

/-- Scalar evaluations that almost norm a function control its entire Lq norm.
The approximation is allowed to vary with the accuracy, and every exponent,
including infinity, is covered by the same Fatou argument. -/
theorem memLp_bound_of_norming_scalar_tests {𝕜 : Type} [RCLike 𝕜]
    {X : Type u} {Y : Type v} [MeasurableSpace X] [NormedAddCommGroup Y]
    {μ : Measure X} {q : ℝ≥0∞} {g : X → Y}
    (hg : AEStronglyMeasurable g μ) (C : ℝ)
    (htest : ∀ η : ℝ, 0 < η → ∃ h : X → 𝕜,
      MemLp h q μ ∧ eLpNorm h q μ ≤ ENNReal.ofReal C ∧
        ∀ᵐ t ∂μ, (1 - η) * ‖g t‖ ≤ ‖h t‖) :
    MemLp g q μ ∧ eLpNorm g q μ ≤ ENNReal.ofReal C := by
  let a : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 1)
  have ha : ∀ n, 0 ≤ a n := by
    intro n
    dsimp [a]
    have hn : (1 : ℝ) ≤ n + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
    have hd := (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr hn
    linarith
  let f : ℕ → X → ℝ := fun n t => a n * ‖g t‖
  have hfm n : AEStronglyMeasurable (f n) μ :=
    aestronglyMeasurable_const.mul hg.norm
  have hbound : ∀ n, eLpNorm (f n) q μ ≤ ENNReal.ofReal C := by
    intro n
    obtain ⟨h, _, hnorm, hpoint⟩ := htest (1 / ((n : ℝ) + 1)) (by positivity)
    apply (eLpNorm_mono_ae (hfm n) ?_).trans hnorm
    filter_upwards [hpoint] with t ht
    simpa only [f, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (ha n) (norm_nonneg _))]
      using ht
  have hlim : ∀ᵐ t ∂μ, Tendsto (fun n => f n t) atTop (𝓝 ‖g t‖) := by
    filter_upwards with t
    have h : Tendsto a atTop (𝓝 (1 : ℝ)) := by
      simpa only [sub_zero, a] using
        (tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 - 0)))
    simpa only [one_mul, f] using h.mul_const ‖g t‖
  have hb : eLpNorm (fun t => ‖g t‖) q μ ≤ ENNReal.ofReal C :=
    Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall hbound) hfm hg.norm hlim
  rw [eLpNorm_norm g hg] at hb
  exact ⟨hb.trans_lt ENNReal.ofReal_lt_top, hb⟩

/-- A locally integrable scalar density representing the finite-set tests of a
continuous functional is its ordinary Lq density. The local sets need only be
a countable finite-measure cover. -/
theorem scalar_memLp_bound_of_local_indicator_representation
    {𝕜 : Type} [RCLike 𝕜] {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp : p ≠ ∞) (L : Lp 𝕜 p μ →L[𝕜] 𝕜) (h : X → 𝕜)
    (S : ℕ → Set X) (hS : ∀ n, MeasurableSet (S n))
    (hSfin : ∀ n, μ (S n) < ∞) (hScover : ⋃ n, S n = univ)
    (hI : ∀ n, IntegrableOn h (S n) μ)
    (hrep : ∀ (n : ℕ) (A : Set X) (hA : MeasurableSet A) (hAS : A ⊆ S n),
      L (indicatorConstLp p hA (lt_of_le_of_lt (measure_mono hAS) (hSfin n)).ne 1) =
        ∫ t in A, h t ∂μ) :
    MemLp h q μ ∧ eLpNorm h q μ ≤ ENNReal.ofReal ‖L‖ := by
  obtain ⟨k, hk, _⟩ := FunctionSpaces.lp_duality_sigmaFinite μ p q hp L
  have hki n : IntegrableOn (fun t => k t) (S n) μ := by
    letI : IsFiniteMeasure (μ.restrict (S n)) := ⟨by
      simpa only [Measure.restrict_apply MeasurableSet.univ, univ_inter] using hSfin n⟩
    exact ((Lp.memLp k).restrict (S n)).integrable (Fact.out : 1 ≤ q)
  have hlocal n : h =ᵐ[μ.restrict (S n)] (fun t => k t) := by
    apply Integrable.ae_eq_of_forall_setIntegral_eq h (fun t => k t) (hI n) (hki n)
    intro A hA _
    simp only [Measure.restrict_restrict hA]
    let B := A ∩ S n
    have hB : MeasurableSet B := hA.inter (hS n)
    have hBS : B ⊆ S n := inter_subset_right
    let f : Lp 𝕜 p μ := indicatorConstLp p hB
      (lt_of_le_of_lt (measure_mono hBS) (hSfin n)).ne 1
    have hf : L f = ∫ t in B, k t ∂μ := by
      rw [(hk.1 f).2, ← integral_indicator hB]
      apply integral_congr_ae
      filter_upwards [indicatorConstLp_coeFn (μ := μ) (p := p) (hs := hB)
        (hμs := (lt_of_le_of_lt (measure_mono hBS) (hSfin n)).ne) (c := (1 : 𝕜))]
        with t ht
      by_cases htB : t ∈ B <;> simp [f, ht, htB]
    exact (hrep n B hB hBS).symm.trans hf
  have heq : h =ᵐ[μ] (fun t => k t) := by
    have hh : ∀ n, ∀ᵐ t ∂μ, t ∈ S n → h t = k t := fun n =>
      (ae_restrict_iff' (hS n)).mp (hlocal n)
    filter_upwards [ae_all_iff.mpr hh] with t ht
    have htU : t ∈ ⋃ n, S n := hScover.symm ▸ mem_univ t
    obtain ⟨n, hn⟩ := mem_iUnion.mp htU
    exact ht n hn
  refine ⟨(memLp_congr_ae heq.symm).mp (Lp.memLp k), ?_⟩
  rw [eLpNorm_congr_ae heq, ← ENNReal.ofReal_toReal (Lp.memLp k).eLpNorm_ne_top,
    ← Lp.norm_def, hk.2]

/-- Every strongly measurable unit-ball test suffices to control the dual
valued Lq norm. Strong measurability of the original density is only needed
a.e.; the selector is chosen from a strongly measurable representative. -/
theorem memLp_bound_of_unit_scalar_tests {𝕜 : Type} [RCLike 𝕜]
    {X : Type u} {E : Type v} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {μ : Measure X} {q : ℝ≥0∞} {g : X → (E →L[𝕜] 𝕜)}
    (hg : AEStronglyMeasurable g μ) (C : ℝ)
    (htest : ∀ z : X → E, StronglyMeasurable z → (∀ t, ‖z t‖ ≤ 1) →
      MemLp (fun t => g t (z t)) q μ ∧
        eLpNorm (fun t => g t (z t)) q μ ≤ ENNReal.ofReal C) :
    MemLp g q μ ∧ eLpNorm g q μ ≤ ENNReal.ofReal C := by
  apply memLp_bound_of_norming_scalar_tests (𝕜 := 𝕜) hg C
  intro η hη
  obtain ⟨z, hz, hzb, hzn⟩ :=
    exists_stronglyMeasurable_norming_test hg.stronglyMeasurable_mk hη
  obtain ⟨hm, hb⟩ := htest z hz hzb
  refine ⟨fun t => g t (z t), hm, hb, ?_⟩
  filter_upwards [hg.ae_eq_mk] with t ht
  calc
    (1 - η) * ‖g t‖ = (1 - η) * ‖hg.mk g t‖ := by rw [ht]
    _ ≤ RCLike.re (hg.mk g t (z t)) := hzn t
    _ = RCLike.re (g t (z t)) := by rw [ht]
    _ ≤ ‖g t (z t)‖ := RCLike.re_le_norm _


end NormTesting

section LocalDensity

variable {𝕜 : Type} [RCLike 𝕜] {X : Type u} {E : Type v}
  [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- An integrable dual-valued function can be evaluated at a bounded strongly
measurable primal-valued function. -/
theorem integrable_eval_of_bound {μ : Measure X} {g : X → E →L[𝕜] 𝕜}
    (hg : Integrable g μ) {f : X → E} (hf : AEStronglyMeasurable f μ)
    {C : ℝ} (hC : ∀ᵐ t ∂μ, ‖f t‖ ≤ C) :
    Integrable (fun t => g t (f t)) μ := by
  apply (hg.norm.mul_const C).mono'
  · exact (ContinuousLinearMap.id 𝕜 (E →L[𝕜] 𝕜)).aestronglyMeasurable_comp₂ hg.aestronglyMeasurable hf
  · filter_upwards [hC] with t ht
    exact ((g t).le_opNorm (f t)).trans (mul_le_mul_of_nonneg_left ht (norm_nonneg _))

variable (μ : Measure X) [IsFiniteMeasure μ] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Indicator identities extend to arbitrary finite-valued simple functions. -/
theorem simple_density_identity (L : Lp E p μ →L[𝕜] 𝕜)
    {g : X → E →L[𝕜] 𝕜} (hg : Integrable g μ)
    (hrep : ∀ (A : Set X) (hA : MeasurableSet A) (x : E),
      L (indicatorConstLp p hA (measure_ne_top μ A) x) = ∫ t in A, g t x ∂μ)
    (f : SimpleFunc X E) :
    L ((f.memLp_of_isFiniteMeasure p μ).toLp f) = ∫ t, g t (f t) ∂μ := by
  induction f using SimpleFunc.induction with
  | @const c A hA =>
    have hc : ((SimpleFunc.piecewise _ hA (SimpleFunc.const X c) (SimpleFunc.const X 0)).memLp_of_isFiniteMeasure p μ).toLp _ =
        indicatorConstLp p hA (measure_ne_top μ _) c := by
      apply Lp.ext
      filter_upwards [MemLp.coeFn_toLp ((SimpleFunc.piecewise _ hA (SimpleFunc.const X c) (SimpleFunc.const X 0)).memLp_of_isFiniteMeasure p μ),
        indicatorConstLp_coeFn (μ := μ) (p := p) (hs := hA) (hμs := measure_ne_top μ _) (c := c)] with t ht hi
      rw [ht, hi]
      by_cases h : t ∈ A <;> simp [h]
    rw [hc, hrep]
    rw [← integral_indicator hA]
    apply integral_congr_ae
    filter_upwards with t
    by_cases h : t ∈ A <;> simp [h]
  | @add f₁ f₂ hd ih₁ ih₂ =>
    have hint (h : SimpleFunc X E) : Integrable (fun t => g t (h t)) μ := by
      obtain ⟨C, hC⟩ := h.exists_forall_norm_le
      exact integrable_eval_of_bound hg h.aestronglyMeasurable (.of_forall hC)
    change L (((f₁.memLp_of_isFiniteMeasure p μ).add (f₂.memLp_of_isFiniteMeasure p μ)).toLp (⇑f₁ + ⇑f₂)) = _
    rw [MemLp.toLp_add (f₁.memLp_of_isFiniteMeasure p μ) (f₂.memLp_of_isFiniteMeasure p μ), map_add, ih₁, ih₂, ← integral_add (hint f₁) (hint f₂)]
    congr 1
    ext t
    simp

/-- The density identity extends to all bounded strongly measurable tests. -/
theorem bounded_density_identity (hp : p ≠ ∞) (L : Lp E p μ →L[𝕜] 𝕜)
    {g : X → E →L[𝕜] 𝕜} (hg : Integrable g μ)
    (hrep : ∀ (A : Set X) (hA : MeasurableSet A) (x : E),
      L (indicatorConstLp p hA (measure_ne_top μ A) x) = ∫ t in A, g t x ∂μ)
    {f : X → E} (hf : StronglyMeasurable f) {C : ℝ}
    (hC : ∀ᵐ t ∂μ, ‖f t‖ ≤ C) (hfp : MemLp f p μ) :
    L (hfp.toLp f) = ∫ t, g t (f t) ∂μ := by
  borelize E
  letI : SeparableSpace (range f ∪ {0} : Set E) :=
    (hf.isSeparable_range.union (finite_singleton _).isSeparable).separableSpace
  let fs : ℕ → SimpleFunc X E :=
    SimpleFunc.approxOn f hf.measurable (range f ∪ {0}) 0 (by simp)
  have hfs (n : ℕ) : MemLp (fs n) p μ := SimpleFunc.memLp_approxOn_range hf.measurable hfp n
  have hLp : Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 (hfp.toLp f)) :=
    SimpleFunc.tendsto_approxOn_range_Lp hp hf.measurable hfp
  have hb (n : ℕ) : ∀ᵐ t ∂μ, ‖g t (fs n t)‖ ≤ ‖g t‖ * (C + C) := by
    filter_upwards [hC] with t ht
    apply ((g t).le_opNorm (fs n t)).trans
    gcongr
    exact (SimpleFunc.norm_approxOn_zero_le hf.measurable (s := range f ∪ {0}) (by simp) t n).trans (add_le_add ht ht)
  have hm (n : ℕ) : AEStronglyMeasurable (fun t => g t (fs n t)) μ :=
    (ContinuousLinearMap.id 𝕜 (E →L[𝕜] 𝕜)).aestronglyMeasurable_comp₂ hg.aestronglyMeasurable (fs n).aestronglyMeasurable
  have ht : ∀ᵐ t ∂μ, Tendsto (fun n => g t (fs n t)) atTop (𝓝 (g t (f t))) := by
    filter_upwards with t
    exact (g t).continuous.continuousAt.tendsto.comp
      (SimpleFunc.tendsto_approxOn hf.measurable (s := range f ∪ {0}) (by simp) (subset_closure (by simp)))
  have hi := tendsto_integral_of_dominated_convergence (fun t => ‖g t‖ * (C + C)) hm
    (hg.norm.mul_const _) hb ht
  have he (n : ℕ) : L ((hfs n).toLp (fs n)) = ∫ t, g t (fs n t) ∂μ :=
    simple_density_identity μ p L hg hrep (fs n)
  exact tendsto_nhds_unique (L.continuous.continuousAt.tendsto.comp hLp)
    (by simpa only [Function.comp_def, he] using hi)

/-- The same identity is insensitive to the choice of a measurable representative. -/
theorem aestronglyMeasurable_bounded_density_identity (hp : p ≠ ∞)
    (L : Lp E p μ →L[𝕜] 𝕜) {g : X → E →L[𝕜] 𝕜} (hg : Integrable g μ)
    (hrep : ∀ (A : Set X) (hA : MeasurableSet A) (x : E),
      L (indicatorConstLp p hA (measure_ne_top μ A) x) = ∫ t in A, g t x ∂μ)
    {f : X → E} (hf : AEStronglyMeasurable f μ) {C : ℝ}
    (hC : ∀ᵐ t ∂μ, ‖f t‖ ≤ C) (hfp : MemLp f p μ) :
    L (hfp.toLp f) = ∫ t, g t (f t) ∂μ := by
  have hmk : MemLp (hf.mk f) p μ := hfp.ae_eq hf.ae_eq_mk
  have hmkC : ∀ᵐ t ∂μ, ‖hf.mk f t‖ ≤ C := by
    filter_upwards [hC, hf.ae_eq_mk] with t ht heq
    simpa only [← heq] using ht
  calc
    L (hfp.toLp f) = L (hmk.toLp (hf.mk f)) := congrArg L (hfp.toLp_congr hmk hf.ae_eq_mk)
    _ = ∫ t, g t (hf.mk f t) ∂μ :=
      bounded_density_identity μ p hp L hg hrep hf.stronglyMeasurable_mk hmkC hmk
    _ = ∫ t, g t (f t) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf.ae_eq_mk] with t ht
      rw [ht]


end LocalDensity

section Gluing

variable {𝕜 : Type} [RCLike 𝕜] {X : Type u} {E : Type v}
  [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Extend a function on a measurable restriction by zero. -/
def extendByZeroLp (A : Set X) (hA : MeasurableSet A) :
    Lp E p (μ.restrict A) →L[𝕜] Lp E p μ :=
  LinearMap.mkContinuous
    { toFun := fun f => ((memLp_indicator_iff_restrict hA.nullMeasurableSet).2 (Lp.memLp f)).toLp
        (A.indicator f)
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp ((memLp_indicator_iff_restrict hA.nullMeasurableSet).2 (Lp.memLp (f+g))),
          Lp.coeFn_add f g |> (ae_restrict_iff' hA).mp,
          Lp.coeFn_add
            (((memLp_indicator_iff_restrict hA.nullMeasurableSet).2 (Lp.memLp f)).toLp (A.indicator f))
            (((memLp_indicator_iff_restrict hA.nullMeasurableSet).2 (Lp.memLp g)).toLp (A.indicator g)),
          MemLp.coeFn_toLp ((memLp_indicator_iff_restrict hA.nullMeasurableSet).2 (Lp.memLp f)),
          MemLp.coeFn_toLp ((memLp_indicator_iff_restrict hA.nullMeasurableSet).2 (Lp.memLp g))]
          with t hfg hfgg hadd hf hg
        rw [hfg, hadd, Pi.add_apply, hf, hg]
        by_cases ht : t ∈ A
        · simpa [ht] using hfgg ht
        · simp [ht]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp ((memLp_indicator_iff_restrict hA.nullMeasurableSet).2 (Lp.memLp (c • f))),
          Lp.coeFn_smul c f |> (ae_restrict_iff' hA).mp,
          Lp.coeFn_smul c
            (((memLp_indicator_iff_restrict hA.nullMeasurableSet).2 (Lp.memLp f)).toLp (A.indicator f)),
          MemLp.coeFn_toLp ((memLp_indicator_iff_restrict hA.nullMeasurableSet).2 (Lp.memLp f))]
          with t hcf hcf' hsm hf
        simp only [RingHom.id_apply]
        rw [hcf, hsm, Pi.smul_apply, hf]
        by_cases ht : t ∈ A
        · simpa [ht] using hcf' ht
        · simp [ht] }
    1 (fun f => by
      rw [one_mul]
      change ‖((memLp_indicator_iff_restrict hA.nullMeasurableSet).2 (Lp.memLp f)).toLp
        (A.indicator f)‖ ≤ ‖f‖
      rw [Lp.norm_toLp, Lp.norm_def,
        eLpNorm_indicator_eq_eLpNorm_restrict hA.nullMeasurableSet])

theorem extendByZeroLp_coeFn (A : Set X) (hA : MeasurableSet A)
    (f : Lp E p (μ.restrict A)) :
    extendByZeroLp (𝕜 := 𝕜) μ p A hA f =ᵐ[μ] A.indicator f :=
  MemLp.coeFn_toLp ((memLp_indicator_iff_restrict hA.nullMeasurableSet).2 (Lp.memLp f))

theorem norm_extendByZeroLp (A : Set X) (hA : MeasurableSet A)
    (f : Lp E p (μ.restrict A)) :
    ‖extendByZeroLp (𝕜 := 𝕜) μ p A hA f‖ = ‖f‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (extendByZeroLp_coeFn (𝕜 := 𝕜) μ p A hA f),
    eLpNorm_indicator_eq_eLpNorm_restrict hA.nullMeasurableSet, Lp.norm_def]

theorem extendByZeroLp_indicatorConstLp (A B : Set X) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hμA : μ A ≠ ∞) (x : E) :
    extendByZeroLp (𝕜 := 𝕜) μ p A hA
      (indicatorConstLp p hB (by
        rw [Measure.restrict_apply hB]
        exact ne_top_of_le_ne_top hμA (measure_mono inter_subset_right)) x) =
      indicatorConstLp p (hB.inter hA)
        (ne_top_of_le_ne_top hμA (measure_mono inter_subset_right)) x := by
  apply Lp.ext
  filter_upwards [extendByZeroLp_coeFn (𝕜 := 𝕜) μ p A hA
    (indicatorConstLp p hB (by
      rw [Measure.restrict_apply hB]
      exact ne_top_of_le_ne_top hμA (measure_mono inter_subset_right)) x),
    (ae_restrict_iff' hA).mp (indicatorConstLp_coeFn (μ := μ.restrict A)
      (p := p) (hs := hB) (c := x)),
    indicatorConstLp_coeFn (μ := μ) (p := p) (hs := hB.inter hA)
      (hμs := ne_top_of_le_ne_top hμA (measure_mono inter_subset_right)) (c := x)]
      with t he hl hr
  rw [he, hr]
  by_cases htA : t ∈ A
  · rw [Set.indicator_of_mem htA, hl htA]
    by_cases htB : t ∈ B <;> simp [htA, htB]
  · simp [htA]

/-- Local densities of a global functional, on any finite measurable restriction. -/
theorem finite_restrict_density [CompleteSpace E]
    (hE : P1.C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E)
    (hp : p ≠ ∞) (L : Lp E p μ →L[𝕜] 𝕜)
    (A : Set X) (hA : MeasurableSet A) (hμA : μ A ≠ ∞) :
    ∃ g : X → (E →L[𝕜] 𝕜), Integrable g (μ.restrict A) ∧
      ∀ (B : Set X) (hB : MeasurableSet B) (x : E),
        L (indicatorConstLp p (hB.inter hA)
          (ne_top_of_le_ne_top hμA (measure_mono inter_subset_right)) x) =
          ∫ t in B, g t x ∂(μ.restrict A) := by
  letI : Fact (μ A < ∞) := ⟨hμA.lt_top⟩
  obtain ⟨g, hg, hrep⟩ := finite_density 𝕜 hE (μ.restrict A) p hp
    (L.comp (extendByZeroLp (𝕜 := 𝕜) μ p A hA))
  refine ⟨g, hg, ?_⟩
  intro B hB x
  simpa only [ContinuousLinearMap.comp_apply,
    extendByZeroLp_indicatorConstLp μ p A B hA hB hμA x] using hrep B hB x

/-- On σ-finite measure spaces, local norm-measurable dual densities can be glued
without a separability hypothesis on the ambient dual. -/
theorem sigmaFinite_piece_density [CompleteSpace E] [SigmaFinite μ]
    (hE : P1.C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E)
    (hp : p ≠ ∞) (L : Lp E p μ →L[𝕜] 𝕜) :
    ∃ g : X → (E →L[𝕜] 𝕜), AEStronglyMeasurable g μ ∧
      ∀ n : ℕ, Integrable g (μ.restrict (disjointed (spanningSets μ) n)) ∧
        ∀ (B : Set X) (hB : MeasurableSet B) (x : E),
          L (indicatorConstLp p (hB.inter (MeasurableSet.disjointed (measurableSet_spanningSets μ) n))
            (ne_top_of_le_ne_top
              ((measure_mono (disjointed_subset (spanningSets μ) n)).trans_lt
                (measure_spanningSets_lt_top μ n)).ne
              (measure_mono inter_subset_right)) x) =
            ∫ t in B, g t x ∂(μ.restrict (disjointed (spanningSets μ) n)) := by
  classical
  let A := disjointed (spanningSets μ)
  have hA n : MeasurableSet (A n) := MeasurableSet.disjointed (measurableSet_spanningSets μ) n
  have hμA n : μ (A n) ≠ ∞ :=
    ((measure_mono (disjointed_subset (spanningSets μ) n)).trans_lt
      (measure_spanningSets_lt_top μ n)).ne
  choose g hg hrep using fun n => finite_restrict_density μ p hE hp L (A n) (hA n) (hμA n)
  let G : X → (E →L[𝕜] 𝕜) := fun t => g (spanningSetsIndex μ t) t
  have heq n : G =ᵐ[μ.restrict (A n)] g n := by
    filter_upwards [ae_restrict_mem (hA n)] with t ht
    exact congrArg (fun k => g k t) ((spanningSetsIndex_eq_iff μ).mpr ht)
  have hG n : Integrable G (μ.restrict (A n)) := (hg n).congr (heq n).symm
  refine ⟨G, ?_, fun n => ⟨hG n, ?_⟩⟩
  · have := AEStronglyMeasurable.iUnion (fun n => (hG n).aestronglyMeasurable)
    simpa only [A, iUnion_disjointed, iUnion_spanningSets, Measure.restrict_univ] using this
  · intro B hB x
    rw [hrep n B hB x]
    exact integral_congr_ae ((ae_restrict_of_ae (heq n)).mono (fun t ht => congrArg (fun U => U x) ht.symm))

/-- Finite-piece constant indicators determine a continuous functional. -/
theorem functional_eq_zero_of_piece_indicators [SigmaFinite μ]
    (hp : p ≠ ∞) (M : Lp E p μ →L[𝕜] 𝕜)
    (hM : ∀ (n : ℕ) (B : Set X) (hB : MeasurableSet B) (x : E),
      M (indicatorConstLp p
        (hB.inter (MeasurableSet.disjointed (measurableSet_spanningSets μ) n))
        (ne_top_of_le_ne_top
          ((measure_mono (disjointed_subset (spanningSets μ) n)).trans_lt
            (measure_spanningSets_lt_top μ n)).ne
          (measure_mono inter_subset_right)) x) = 0) : M = 0 := by
  have hzero (B : Set X) (hB : MeasurableSet B) (hμB : μ B ≠ ∞) (x : E) :
      M (indicatorConstLp p hB hμB x) = 0 := by
    letI : Fact (μ B < ∞) := ⟨hμB.lt_top⟩
    let MB := M.comp (extendByZeroLp (𝕜 := 𝕜) μ p B hB)
    let D := disjointed (spanningSets μ)
    have hD n : MeasurableSet (D n) :=
      MeasurableSet.disjointed (measurableSet_spanningSets μ) n
    have hz n : indicatorFunctional (μ.restrict B) p MB (D n) (hD n) = 0 := by
      ext y
      rw [indicatorFunctional_apply]
      change M (extendByZeroLp (𝕜 := 𝕜) μ p B hB _) = 0
      rw [extendByZeroLp_indicatorConstLp μ p B (D n) hB (hD n) hμB y]
      have hh := hM n B hB y
      simpa only [D, inter_comm] using hh
    have hs := hasSum_indicatorFunctional (μ.restrict B) p hp MB D hD
      (disjoint_disjointed (spanningSets μ))
    have hz' : indicatorFunctional (μ.restrict B) p MB (⋃ n, D n)
        (MeasurableSet.iUnion hD) = 0 := by
      rw [show (fun n => indicatorFunctional (μ.restrict B) p MB (D n) (hD n)) = fun _ => 0
        from funext hz] at hs
      exact hs.unique (hasSum_zero)
    have heval := congrArg (fun U : E →L[𝕜] 𝕜 => U x) hz'
    simp only [indicatorFunctional_apply, ContinuousLinearMap.zero_apply,
      D, iUnion_disjointed, iUnion_spanningSets] at heval
    change M (extendByZeroLp (𝕜 := 𝕜) μ p B hB _) = 0 at heval
    rw [extendByZeroLp_indicatorConstLp μ p B univ hB MeasurableSet.univ hμB x] at heval
    simpa only [univ_inter] using heval
  ext f
  change M f = 0
  refine Lp.induction hp (fun f => M f = 0) ?_ ?_ ?_ f
  · intro x B hB hμB
    exact hzero B hB hμB.ne x
  · intro f g hf hg _ hf' hg'
    simp only [map_add, hf', hg', add_zero]
  · exact isClosed_eq M.continuous continuous_const


end Gluing

section ScalarMultiplier
open VectorLpRepresentationSpec

/-- Multiplication by a measurable vector field. -/
def scalarMultiplier {𝕜 : Type} [RCLike 𝕜] {X : Type u} {E : Type v}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (z : X → E) (hz : MemLp z ∞ μ) : Lp 𝕜 p μ →L[𝕜] Lp E p μ :=
  ((ContinuousLinearMap.lsmul 𝕜 𝕜 : 𝕜 →L[𝕜] E →L[𝕜] E).holderL μ p ∞ p).flip
    (hz.toLp z)

theorem scalarMultiplier_coe {𝕜 : Type} [RCLike 𝕜] {X : Type u} {E : Type v}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (z : X → E) (hz : MemLp z ∞ μ) (f : Lp 𝕜 p μ) :
    scalarMultiplier μ p z hz f =ᵐ[μ] fun t => f t • z t := by
  have hc := (ContinuousLinearMap.lsmul 𝕜 𝕜 : 𝕜 →L[𝕜] E →L[𝕜] E).coeFn_holder
    (r := p) f (hz.toLp z)
  filter_upwards [hc, MemLp.coeFn_toLp hz] with t ht hz'
  simpa only [scalarMultiplier, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.holderL_apply_apply, ContinuousLinearMap.lsmul_apply, hz'] using ht

theorem scalarMultiplier_norm_le {𝕜 : Type} [RCLike 𝕜] {X : Type u} {E : Type v}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (z : X → E) (hz : MemLp z ∞ μ) (hbound : ∀ᵐ t ∂μ, ‖z t‖ ≤ 1) :
    ‖scalarMultiplier (𝕜 := 𝕜) μ p z hz‖ ≤ 1 := by
  have hz' : ‖hz.toLp z‖ ≤ 1 := by
    rw [Lp.norm_toLp, eLpNorm_exponent_top hz.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (eLpNormEssSup_le_of_ae_bound hbound)
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  have hb := (ContinuousLinearMap.lsmul 𝕜 𝕜 : 𝕜 →L[𝕜] E →L[𝕜] E).norm_holder_apply_apply_le
    (r := p) f (hz.toLp z)
  change ‖(ContinuousLinearMap.lsmul 𝕜 𝕜 : 𝕜 →L[𝕜] E →L[𝕜] E).holder p f (hz.toLp z)‖ ≤ _
  calc
    _ ≤ ‖(ContinuousLinearMap.lsmul 𝕜 𝕜 : 𝕜 →L[𝕜] E →L[𝕜] E)‖ * ‖f‖ * ‖hz.toLp z‖ := hb
    _ ≤ 1 * ‖f‖ * 1 := by gcongr; exact ContinuousLinearMap.opNorm_lsmul_le
    _ = 1 * ‖f‖ := by ring


end ScalarMultiplier


section GlobalEvaluation

variable {𝕜 : Type} [RCLike 𝕜] {X : Type u} {E : Type v}
  [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Local bounded tests identify the scalar functional obtained by multiplying
by a bounded measurable vector field. -/
theorem scalar_eval_local_indicator
    (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (L : Lp E p μ →L[𝕜] 𝕜) (A : Set X) (hA : MeasurableSet A) (hμA : μ A ≠ ∞)
    {g : X → E →L[𝕜] 𝕜} (hg : Integrable g (μ.restrict A))
    (hrep : ∀ (D : Set X) (hD : MeasurableSet D) (x : E),
      L (indicatorConstLp p (hD.inter hA)
        (ne_top_of_le_ne_top hμA (measure_mono inter_subset_right)) x) =
        ∫ t in D, g t x ∂(μ.restrict A))
    (z : X → E) (hz : StronglyMeasurable z) (hzLp : MemLp z ∞ μ)
    (hzB : ∀ᵐ t ∂μ, ‖z t‖ ≤ 1)
    (B : Set X) (hB : MeasurableSet B) (hBA : B ⊆ A) :
    (L.comp (scalarMultiplier μ p z hzLp))
      (indicatorConstLp p hB (ne_top_of_le_ne_top hμA (measure_mono hBA)) 1) =
        ∫ t in B, g t (z t) ∂μ := by
  letI : Fact (μ A < ∞) := ⟨hμA.lt_top⟩
  let LA := L.comp (extendByZeroLp (𝕜 := 𝕜) μ p A hA)
  let φ := B.indicator z
  have hφsm : StronglyMeasurable φ := hz.indicator hB
  have hφB : ∀ᵐ t ∂(μ.restrict A), ‖φ t‖ ≤ 1 := by
    filter_upwards [ae_restrict_of_ae hzB] with t ht
    by_cases htB : t ∈ B
    · simpa [φ, htB] using ht
    · simp [φ, htB]
  have hφ : MemLp φ p (μ.restrict A) := MemLp.of_bound hφsm.aestronglyMeasurable 1 hφB
  have hLA (D : Set X) (hD : MeasurableSet D) (x : E) :
      LA (indicatorConstLp p hD (measure_ne_top (μ.restrict A) D) x) =
        ∫ t in D, g t x ∂(μ.restrict A) := by
    change L (extendByZeroLp (𝕜 := 𝕜) μ p A hA _) = _
    rw [extendByZeroLp_indicatorConstLp μ p A D hA hD hμA]
    exact hrep D hD x
  let fB : Lp 𝕜 p μ := indicatorConstLp p hB
    (ne_top_of_le_ne_top hμA (measure_mono hBA)) 1
  have he : scalarMultiplier μ p z hzLp fB =
      extendByZeroLp (𝕜 := 𝕜) μ p A hA (hφ.toLp φ) := by
    apply Lp.ext
    filter_upwards [scalarMultiplier_coe μ p z hzLp fB,
      indicatorConstLp_coeFn (μ := μ) (p := p) (hs := hB)
        (hμs := ne_top_of_le_ne_top hμA (measure_mono hBA)) (c := (1 : 𝕜)),
      extendByZeroLp_coeFn (𝕜 := 𝕜) μ p A hA (hφ.toLp φ),
      (ae_restrict_iff' hA).mp (MemLp.coeFn_toLp hφ)] with t hsm hi hext hloc
    rw [hsm, hi, hext]
    by_cases htB : t ∈ B
    · simp [htB, hBA htB, hloc (hBA htB), φ]
    · by_cases htA : t ∈ A
      · simp [htB, htA, hloc htA, φ]
      · simp [htB, htA]
  calc
    (L.comp (scalarMultiplier μ p z hzLp)) fB = LA (hφ.toLp φ) := congrArg L he
    _ = ∫ t, g t (φ t) ∂(μ.restrict A) :=
      bounded_density_identity (μ.restrict A) p hp LA hg hLA hφsm hφB hφ
    _ = ∫ t in B, g t (z t) ∂μ := by
      have hval : (fun t => g t (φ t)) = B.indicator (fun t => g t (z t)) := by
        ext t
        by_cases ht : t ∈ B <;> simp [φ, ht]
      rw [hval, integral_indicator hB, Measure.restrict_restrict hB, inter_eq_left.mpr hBA]

/-- A countable finite-measure family of local dual densities controls every
bounded measurable scalar evaluation in the conjugate exponent. -/
theorem scalar_eval_memLp_bound_of_local_density
    (μ : Measure X) [SigmaFinite μ] (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp : p ≠ ∞) (L : Lp E p μ →L[𝕜] 𝕜) {g : X → E →L[𝕜] 𝕜}
    (S : ℕ → Set X) (hS : ∀ n, MeasurableSet (S n))
    (hSfin : ∀ n, μ (S n) < ∞) (hScover : ⋃ n, S n = univ)
    (hg : ∀ n, Integrable g (μ.restrict (S n)))
    (hrep : ∀ (n : ℕ) (D : Set X) (hD : MeasurableSet D) (x : E),
      L (indicatorConstLp p (hD.inter (hS n))
        (ne_top_of_le_ne_top (hSfin n).ne (measure_mono inter_subset_right)) x) =
        ∫ t in D, g t x ∂(μ.restrict (S n)))
    (z : X → E) (hz : StronglyMeasurable z) (hzB : ∀ᵐ t ∂μ, ‖z t‖ ≤ 1) :
    MemLp (fun t => g t (z t)) q μ ∧
      eLpNorm (fun t => g t (z t)) q μ ≤ ENNReal.ofReal ‖L‖ := by
  let hzLp : MemLp z ∞ μ := memLp_top_of_bound hz.aestronglyMeasurable 1 hzB
  let ℓ := L.comp (scalarMultiplier μ p z hzLp)
  have htest : MemLp (fun t => g t (z t)) q μ ∧
      eLpNorm (fun t => g t (z t)) q μ ≤ ENNReal.ofReal ‖ℓ‖ := by
    apply scalar_memLp_bound_of_local_indicator_representation μ p q hp ℓ
      (fun t => g t (z t)) S hS hSfin hScover
    · intro n
      exact integrable_eval_of_bound (hg n) hz.aestronglyMeasurable.restrict
        (ae_restrict_of_ae hzB)
    · intro n B hB hBS
      exact scalar_eval_local_indicator μ p hp L (S n) (hS n) (hSfin n).ne
        (hg n) (hrep n) z hz hzLp hzB B hB hBS
  refine ⟨htest.1, htest.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  exact (L.opNorm_comp_le (scalarMultiplier μ p z hzLp)).trans (mul_le_of_le_one_right (norm_nonneg _)
    (scalarMultiplier_norm_le μ p z hzLp hzB))


end GlobalEvaluation

section RepresentationAssembly

variable {𝕜 : Type} [RCLike 𝕜] {X : Type u} {E : Type v}
  [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (μ : Measure X) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  [ENNReal.HolderConjugate p q]

/-- The integral pairing acts on a constant indicator by a set integral. -/
theorem pairing_indicatorConstLp {g : X → (E →L[𝕜] 𝕜)} (hg : MemLp g q μ)
    (A : Set X) (hA : MeasurableSet A) (hμA : μ A ≠ ∞) (x : E) :
    pairing 𝕜 μ p q (hg.toLp g) (indicatorConstLp p hA hμA x) =
      ∫ t in A, g t x ∂μ := by
  calc
    _ = ∫ t, (hg.toLp g) t ((indicatorConstLp p hA hμA x) t) ∂μ :=
      (pairing_formula 𝕜 μ p q (hg.toLp g) (indicatorConstLp p hA hμA x)).2
    _ = ∫ t, A.indicator (fun t => g t x) t ∂μ := by
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp hg,
        indicatorConstLp_coeFn (μ := μ) (p := p) (hs := hA) (hμs := hμA) (c := x)]
        with t hgt hft
      rw [hgt, hft]
      by_cases ht : t ∈ A <;> simp [ht]
    _ = _ := integral_indicator hA

/-- A global Lq density representing all finite-piece constant indicators
represents the original functional on the whole Lp space. -/
theorem pairing_eq_of_piece_density [SigmaFinite μ] (hp : p ≠ ∞)
    (L : Lp E p μ →L[𝕜] 𝕜) {g : X → (E →L[𝕜] 𝕜)} (hg : MemLp g q μ)
    (hrep : ∀ (n : ℕ) (B : Set X) (hB : MeasurableSet B) (x : E),
      L (indicatorConstLp p
        (hB.inter (MeasurableSet.disjointed (measurableSet_spanningSets μ) n))
        (ne_top_of_le_ne_top
          ((measure_mono (disjointed_subset (spanningSets μ) n)).trans_lt
            (measure_spanningSets_lt_top μ n)).ne
          (measure_mono inter_subset_right)) x) =
        ∫ t in B, g t x ∂(μ.restrict (disjointed (spanningSets μ) n))) :
    pairing 𝕜 μ p q (hg.toLp g) = L := by
  apply sub_eq_zero.mp
  apply functional_eq_zero_of_piece_indicators μ p hp
  intro n B hB x
  rw [ContinuousLinearMap.sub_apply, pairing_indicatorConstLp μ p q hg,
    hrep n B hB x, Measure.restrict_restrict hB, sub_self]


end RepresentationAssembly

section PairingIsometry
open VectorLpRepresentationSpec

/-- The evaluation integral preserves norms, independently of reflexivity. -/
theorem pairing_norm {𝕜 : Type} [RCLike 𝕜] {X : Type u} {E : Type v}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (μ : Measure X) [SigmaFinite μ] (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp : p ≠ ∞) (g : Lp (E →L[𝕜] 𝕜) q μ) :
    ‖PairingValue 𝕜 μ p q g‖ = ‖g‖ := by
  apply le_antisymm (pairing_bound 𝕜 μ p q g)
  have hb : eLpNorm (fun t => g t) q μ ≤ ENNReal.ofReal ‖PairingValue 𝕜 μ p q g‖ := by
    apply (memLp_bound_of_unit_scalar_tests (Lp.aestronglyMeasurable g)
      ‖PairingValue 𝕜 μ p q g‖ ?_).2
    intro z hz hzb
    let hzTop : MemLp z ∞ μ := memLp_top_of_bound hz.aestronglyMeasurable 1 (.of_forall hzb)
    let B : (E →L[𝕜] 𝕜) →L[𝕜] E →L[𝕜] 𝕜 := ContinuousLinearMap.id 𝕜 _
    have hmem : MemLp (fun t => g t (z t)) q μ := B.memLp_of_bilin q (Lp.memLp g) hzTop
    let h : Lp 𝕜 q μ := hmem.toLp (fun t => g t (z t))
    have heq : FunctionSpaces.ScalarLpIntegralPairingSpec.IntegralPairingValue μ p q h =
        (PairingValue 𝕜 μ p q g).comp (scalarMultiplier μ p z hzTop) := by
      ext f
      rw [(FunctionSpaces.lp_pairing_integral μ p q h f).2,
        ContinuousLinearMap.comp_apply, (pairing_formula 𝕜 μ p q g _).2]
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp hmem, scalarMultiplier_coe μ p z hzTop f] with t ht hf
      rw [ht, hf, map_smul, smul_eq_mul]
    have hn : ‖h‖ ≤ ‖PairingValue 𝕜 μ p q g‖ := by
      rw [← FunctionSpaces.lp_pairing_exact_norm μ p q hp (Or.inl inferInstance) h, heq]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _) (scalarMultiplier_norm_le μ p z hzTop (.of_forall hzb)))
    refine ⟨hmem, ?_⟩
    rw [← ENNReal.ofReal_toReal hmem.eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal (by simpa only [h, Lp.norm_toLp] using hn)
  rw [Lp.norm_def]
  exact ENNReal.toReal_le_of_le_ofReal (norm_nonneg _) hb

theorem pairing_isometry {𝕜 : Type} [RCLike 𝕜] {X : Type u} {E : Type v}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (μ : Measure X) [SigmaFinite μ] (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp : p ≠ ∞) : Isometry (PairingValue (E := E) 𝕜 μ p q) :=
  AddMonoidHomClass.isometry_of_norm _ (pairing_norm μ p q hp)


end PairingIsometry


section GlobalDensity

variable {𝕜 : Type} [RCLike 𝕜] {X : Type u} {E : Type v}
  [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Local vector Radon--Nikodym densities automatically have the optimal
conjugate-exponent bound. -/
theorem memLp_bound_of_local_density
    (μ : Measure X) [SigmaFinite μ] (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp : p ≠ ∞) (L : Lp E p μ →L[𝕜] 𝕜) {g : X → E →L[𝕜] 𝕜}
    (hgm : AEStronglyMeasurable g μ)
    (S : ℕ → Set X) (hS : ∀ n, MeasurableSet (S n))
    (hSfin : ∀ n, μ (S n) < ∞) (hScover : ⋃ n, S n = univ)
    (hg : ∀ n, Integrable g (μ.restrict (S n)))
    (hrep : ∀ (n : ℕ) (D : Set X) (hD : MeasurableSet D) (x : E),
      L (indicatorConstLp p (hD.inter (hS n))
        (ne_top_of_le_ne_top (hSfin n).ne (measure_mono inter_subset_right)) x) =
        ∫ t in D, g t x ∂(μ.restrict (S n))) :
    MemLp g q μ ∧ eLpNorm g q μ ≤ ENNReal.ofReal ‖L‖ := by
  apply memLp_bound_of_unit_scalar_tests hgm ‖L‖
  intro z hz hzb
  exact scalar_eval_memLp_bound_of_local_density μ p q hp L S hS hSfin hScover hg hrep
    z hz (.of_forall hzb)

/-- The σ-finite raw density, with its required ordinary Lq bound. -/
theorem sigmaFinite_density_memLp [CompleteSpace E]
    (μ : Measure X) [SigmaFinite μ] (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hE : P1.C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E)
    (hp : p ≠ ∞) (L : Lp E p μ →L[𝕜] 𝕜) :
    ∃ g : X → (E →L[𝕜] 𝕜), MemLp g q μ ∧ eLpNorm g q μ ≤ ENNReal.ofReal ‖L‖ ∧
      ∀ n : ℕ, Integrable g (μ.restrict (disjointed (spanningSets μ) n)) ∧
        ∀ (B : Set X) (hB : MeasurableSet B) (x : E),
          L (indicatorConstLp p (hB.inter (MeasurableSet.disjointed (measurableSet_spanningSets μ) n))
            (ne_top_of_le_ne_top
              ((measure_mono (disjointed_subset (spanningSets μ) n)).trans_lt
                (measure_spanningSets_lt_top μ n)).ne
              (measure_mono inter_subset_right)) x) =
            ∫ t in B, g t x ∂(μ.restrict (disjointed (spanningSets μ) n)) := by
  obtain ⟨g, hgm, hg⟩ := sigmaFinite_piece_density μ p hE hp L
  let S := disjointed (spanningSets μ)
  have hS n : MeasurableSet (S n) := MeasurableSet.disjointed (measurableSet_spanningSets μ) n
  have hSfin n : μ (S n) < ∞ :=
    (measure_mono (disjointed_subset (spanningSets μ) n)).trans_lt (measure_spanningSets_lt_top μ n)
  have hScover : ⋃ n, S n = univ := by simp [S, iUnion_disjointed, iUnion_spanningSets]
  have hb := memLp_bound_of_local_density μ p q hp L hgm S hS hSfin hScover
    (fun n => (hg n).1) (fun n => (hg n).2)
  exact ⟨g, hb.1, hb.2, hg⟩


end GlobalDensity

/-- Full Bochner duality for reflexive real or complex Banach spaces, including
nonseparable ranges and the endpoint p = 1, q = infinity. -/
theorem full_duality : FullDuality.{u,v} := by
  intro 𝕜 _ X E _ _ _ _ hE μ _ p q _ _ _ hp
  refine ⟨pairing_isometry μ p q hp, ?_⟩
  intro L
  obtain ⟨g, hgm, _, hg⟩ := sigmaFinite_density_memLp μ p q hE hp L
  exact ⟨hgm.toLp g, pairing_eq_of_piece_density μ p q hp L hgm (fun n => (hg n).2)⟩

end ExpandedFA.PartIV.VectorLpRepresentation
