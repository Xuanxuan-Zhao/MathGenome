import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.LpDualFiniteMeasure
import MathGenome.Internal.RealAnalysis.D11.Ch20.PairingNormFiniteQ
import MathGenome.Internal.RealAnalysis.D11.Ch20.PairingNormEndpoint
import MathGenome.Internal.RealAnalysis.D11.Ch15.RNSignedComplex
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.LpSpace.Complete

open Set MeasureTheory Filter
open scoped ENNReal Topology
universe u
noncomputable section
namespace D11.Ch20.LpDualFiniteMeasure

variable {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]

theorem pairing_norm : Specs.D11.Ch20.LpDualFiniteMeasure.pairing_norm := by
  intro X 𝕜 _ _ μ _ p q _ _ _ g
  by_cases hq : q = ∞
  · subst q
    have hp : p = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ∞ p).mp rfl
    subst p
    exact PairingNormEndpoint.pairing_norm_endpoint μ
      (PairingNormEndpoint.sigmaFinite_semifinite μ inferInstance) g
  · exact PairingNormFiniteQ.norm_pairing μ p q hq g

theorem representation_unique_norm :
    Specs.D11.Ch20.LpDualFiniteMeasure.representation_unique_norm := by
  intro X 𝕜 _ _ μ _ p q _ _ _ ℓ g hg
  have heq : IntegralPairing.pairing μ p q g = ℓ := by
    ext f
    exact (IntegralPairing.pairing_eq_integral μ p q g f).2.trans (hg f).symm
  refine ⟨(pairing_norm μ p q g).symm.trans (congrArg norm heq), ?_⟩
  intro k hk
  have hi : Function.Injective
      (Specs.D11.Ch20.IntegralPairing.pairing_value (𝕜 := 𝕜) μ p q) :=
    (AddMonoidHomClass.isometry_of_norm
      (Specs.D11.Ch20.IntegralPairing.pairing_value (𝕜 := 𝕜) μ p q)
      (pairing_norm μ p q)).injective
  apply hi
  ext f
  exact (IntegralPairing.pairing_eq_integral μ p q k f).2.trans
    ((hk f).symm.trans ((hg f).trans
      (IntegralPairing.pairing_eq_integral μ p q g f).2.symm))



section ScalarMeasure
variable (μ : Measure X) [IsFiniteMeasure μ] (p : ℝ≥0∞) [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- Finite additivity of indicators in the literal ordinary Lp quotient. -/
lemma sum_indicatorConstLp {ι : Type*} (I : Finset ι) (A : ι → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (hd : Pairwise fun i j => Disjoint (A i) (A j)) :
    ∑ i ∈ I, indicatorConstLp (μ := μ) p (hA i) (measure_ne_top μ _) (1 : 𝕜) =
      indicatorConstLp p (Finset.measurableSet_biUnion I (fun i _ => hA i))
        (measure_ne_top μ _) 1 := by
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

/-- Phase-aligned disjoint indicator tests control every finite partition cost. -/
lemma sum_norm_functional_indicator_le {ι : Type*} (I : Finset ι)
    (A : ι → Set X) (hA : ∀ i, MeasurableSet (A i))
    (hd : Pairwise fun i j => Disjoint (A i) (A j))
    (ℓ : Lp 𝕜 p μ →L[𝕜] 𝕜) :
    ∑ i ∈ I, ‖ℓ (indicatorConstLp p (hA i) (measure_ne_top μ _) 1)‖ ≤
      ‖ℓ‖ * ((measureUnivNNReal μ : ℝ) ^ p.toReal⁻¹) := by
  classical
  let v (i : ι) : Lp 𝕜 p μ := indicatorConstLp p (hA i) (measure_ne_top μ _) 1
  let z (i : ι) : 𝕜 := PairingNormFiniteQ.conjugatePhase (ℓ (v i))
  let f : Lp 𝕜 p μ := ∑ i ∈ I, z i • v i
  have hcoe : (f : X → 𝕜) =ᵐ[μ] fun x => ∑ i ∈ I, z i * (A i).indicator (fun _ => 1) x := by
    refine (Lp.coeFn_fun_finsetSum I (fun i => z i • v i)).trans ?_
    have hh : ∀ i ∈ I, (fun x => (z i • v i) x) =ᵐ[μ]
        (fun x => z i * (A i).indicator (fun _ => 1) x) := by
      intro i hi
      exact (Lp.coeFn_smul (z i) (v i)).trans
        ((indicatorConstLp_coeFn (p := p) (hs := hA i)
          (hμs := measure_ne_top μ _) (c := (1 : 𝕜))).fun_comp (fun a : 𝕜 => z i * a))
    filter_upwards [eventuallyEq_sum hh] with x hx
    simpa only [Finset.sum_apply] using hx
  have hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ 1 := by
    filter_upwards [hcoe] with x hx
    rw [hx]
    by_cases hex : ∃ i ∈ I, x ∈ A i
    · obtain ⟨i, hi, hxi⟩ := hex
      rw [Finset.sum_eq_single i]
      · simpa [hxi] using PairingNormFiniteQ.norm_conjugatePhase_le (ℓ (v i))
      · intro j hj hji
        have hxj : x ∉ A j := fun hxj => (hd hji).le_bot ⟨hxj, hxi⟩
        simp [hxj]
      · exact fun h => (h hi).elim
    · have hz : ∀ i ∈ I, x ∉ A i := by simpa using hex
      have he : ∑ i ∈ I, z i * (A i).indicator (fun _ => (1 : 𝕜)) x = 0 :=
        Finset.sum_eq_zero fun i hi => by simp [hz i hi]
      rw [he, norm_zero]
      exact zero_le_one
  have hn : ‖f‖ ≤ (measureUnivNNReal μ : ℝ) ^ p.toReal⁻¹ := by
    simpa using Lp.norm_le_of_ae_bound (zero_le_one : (0 : ℝ) ≤ 1) hbound
  have hv : ℓ f = ((∑ i ∈ I, ‖ℓ (v i)‖ : ℝ) : 𝕜) := by
    simp only [f, map_sum, map_smul, smul_eq_mul, z,
      PairingNormFiniteQ.conjugatePhase_mul]
  have hh := ℓ.le_opNorm f
  rw [hv, RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hn (norm_nonneg _))

/-- Countable additivity is proved before invoking Radon–Nikodym. -/
lemma hasSum_functional_indicator (hp : p ≠ ∞)
    (ℓ : Lp 𝕜 p μ →L[𝕜] 𝕜) (A : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (hd : Pairwise fun i j => Disjoint (A i) (A j)) :
    HasSum (fun i => ℓ (indicatorConstLp p (hA i) (measure_ne_top μ _) 1))
      (ℓ (indicatorConstLp p (MeasurableSet.iUnion hA) (measure_ne_top μ _) 1)) := by
  have hs : Summable (fun i => ‖ℓ (indicatorConstLp p (hA i) (measure_ne_top μ _) 1)‖) :=
    summable_of_sum_le (fun i => norm_nonneg _)
      (fun I => sum_norm_functional_indicator_le μ p I A hA hd ℓ)
  rw [hasSum_iff_tendsto_nat_of_summable_norm hs]
  have heq n : ∑ i ∈ Finset.range n, ℓ (indicatorConstLp p (hA i) (measure_ne_top μ _) 1) =
      ℓ (indicatorConstLp p (Finset.measurableSet_biUnion (Finset.range n) (fun i _ => hA i))
        (measure_ne_top μ _) 1) := by
    rw [← map_sum, sum_indicatorConstLp μ p]
    exact hd
  simp_rw [heq]
  apply ℓ.continuous.tendsto _ |>.comp
  apply tendsto_indicatorConstLp_set hp
  have htail := tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
    (fun i => (hA i).nullMeasurableSet) hd (μ := μ)
  convert htail using 1
  ext n
  congr 1
  ext x
  simp only [mem_symmDiff, mem_iUnion, exists_prop, Finset.mem_range]
  constructor
  · rintro (⟨_, h⟩ | ⟨⟨i, hxi⟩, hnot⟩)
    · exact (h (by aesop)).elim
    · exact ⟨i, Nat.le_of_not_gt (fun hi => hnot ⟨i, hi, hxi⟩), hxi⟩
  · rintro ⟨i, hi, hxi⟩
    right
    refine ⟨⟨i, hxi⟩, ?_⟩
    rintro ⟨j, hj, hxj⟩
    exact (hd (ne_of_lt (hj.trans_le hi))).le_bot ⟨hxj, hxi⟩



open scoped Classical in
/-- The measure of measurable A is ℓ(1_A); zero on nonmeasurable sets is
only the convention of the shared vector-measure interface. -/
def functionalMeasure (hp : p ≠ ∞) (ℓ : Lp 𝕜 p μ →L[𝕜] 𝕜) : VectorMeasure X 𝕜 where
  measureOf' A := if hA : MeasurableSet A then
    ℓ (indicatorConstLp p hA (measure_ne_top μ _) 1) else 0
  empty' := by simp
  not_measurable' _ hA := by simp [hA]
  m_iUnion' _ hA hd := by
    simpa only [dite_eq_left (hA _), dite_eq_left (MeasurableSet.iUnion hA)] using
      hasSum_functional_indicator μ p hp ℓ _ hA hd

lemma functionalMeasure_apply (hp : p ≠ ∞) (ℓ : Lp 𝕜 p μ →L[𝕜] 𝕜)
    (A : Set X) (hA : MeasurableSet A) :
    functionalMeasure μ p hp ℓ A = ℓ (indicatorConstLp p hA (measure_ne_top μ _) 1) := by
  simp only [functionalMeasure, VectorMeasure.coe_mk, dite_eq_left hA]

/-- A quantitative finite-variation bound, established without RN. -/
lemma functionalMeasure_variation_bound (hp : p ≠ ∞) (ℓ : Lp 𝕜 p μ →L[𝕜] 𝕜) :
    (functionalMeasure μ p hp ℓ).variation univ ≤
      ENNReal.ofReal (‖ℓ‖ * ((measureUnivNNReal μ : ℝ) ^ p.toReal⁻¹)) := by
  classical
  by_contra! h
  obtain ⟨P, _, hd, hP, hlt⟩ :=
    (functionalMeasure μ p hp ℓ).exists_lt_sum_of_lt_variation MeasurableSet.univ h
  have hd' : Pairwise fun i j : P => Disjoint (i : Set X) (j : Set X) := by
    intro i j hij
    exact hd i.property j.property (fun heq => hij (Subtype.ext heq))
  have hb := sum_norm_functional_indicator_le μ p (Finset.univ : Finset P)
    (fun i => (i : Set X)) (fun i => hP i i.property) hd' ℓ
  simp only [← functionalMeasure_apply μ p hp ℓ] at hb
  rw [Finset.sum_coe_sort P (fun A => ‖functionalMeasure μ p hp ℓ A‖)] at hb
  have hbe : (∑ A ∈ P, ‖functionalMeasure μ p hp ℓ A‖ₑ) ≤
      ENNReal.ofReal (‖ℓ‖ * ((measureUnivNNReal μ : ℝ) ^ p.toReal⁻¹)) := by
    simpa only [← ofReal_norm, ENNReal.ofReal_sum_of_nonneg (fun A _ => norm_nonneg _)] using
      ENNReal.ofReal_le_ofReal hb
  exact hlt.not_ge hbe

lemma functionalMeasure_finite (hp : p ≠ ∞) (ℓ : Lp 𝕜 p μ →L[𝕜] 𝕜) :
    IsFiniteMeasure (functionalMeasure μ p hp ℓ).variation :=
  ⟨(functionalMeasure_variation_bound μ p hp ℓ).trans_lt ENNReal.ofReal_lt_top⟩

lemma functionalMeasure_null (hp : p ≠ ∞) (ℓ : Lp 𝕜 p μ →L[𝕜] 𝕜)
    (A : Set X) (hA : MeasurableSet A) (hzero : μ A = 0) :
    functionalMeasure μ p hp ℓ A = 0 := by
  rw [functionalMeasure_apply μ p hp ℓ A hA]
  have hz : indicatorConstLp (μ := μ) p hA (measure_ne_top μ _) (1 : 𝕜) = 0 := by
    apply Lp.ext
    filter_upwards [indicatorConstLp_coeFn (μ := μ) (p := p) (hs := hA)
      (hμs := measure_ne_top μ _) (c := (1 : 𝕜)), measure_eq_zero_iff_ae_notMem.mp hzero, Lp.coeFn_zero 𝕜 p μ]
      with x hx hxA hx0
    rw [hx, Set.indicator_of_notMem hxA]
    exact hx0.symm
  rw [hz, map_zero]

end ScalarMeasure

theorem scalar_measure_exists : Specs.D11.Ch20.LpDualFiniteMeasure.scalar_measure_exists := by
  intro X 𝕜 _ _ μ _ p _ hp ℓ
  exact ⟨functionalMeasure μ p hp ℓ, functionalMeasure_apply μ p hp ℓ,
    functionalMeasure_finite μ p hp ℓ, functionalMeasure_null μ p hp ℓ⟩



/-- The real and imaginary signed RN densities combine without conjugation.
The scalar measure and its finite variation have already been constructed. -/
theorem integrable_density_exists : Specs.D11.Ch20.LpDualFiniteMeasure.integrable_density_exists := by
  intro X 𝕜 _ _ _ _ μ _ p _ hp ℓ
  obtain ⟨ν, hν, hfin, hnull⟩ := scalar_measure_exists μ p hp ℓ
  let νr : SignedMeasure X := VectorMeasure.mapRangeL (RCLike.reCLM : 𝕜 →L[ℝ] ℝ) ν
  let νi : SignedMeasure X := VectorMeasure.mapRangeL (RCLike.imCLM : 𝕜 →L[ℝ] ℝ) ν
  have hrac : Ch15.AbsoluteContinuity.scalarAbsolutelyContinuous νr μ := by
    apply (Ch15.AbsoluteContinuity.scalar_iff νr μ).mpr
    intro A hA hz
    change RCLike.re (ν A) = 0
    rw [hnull A hA hz, map_zero]
  have hiac : Ch15.AbsoluteContinuity.scalarAbsolutelyContinuous νi μ := by
    apply (Ch15.AbsoluteContinuity.scalar_iff νi μ).mpr
    intro A hA hz
    change RCLike.im (ν A) = 0
    rw [hnull A hA hz, map_zero]
  obtain ⟨r, hrm, hri, hr⟩ := Ch15.RNSignedComplex.exists_signed_density μ νr hrac
  obtain ⟨i, him, hii, hi⟩ := Ch15.RNSignedComplex.exists_signed_density μ νi hiac
  let h : X → 𝕜 := fun x => (r x : 𝕜) + (i x : 𝕜) * RCLike.I
  have hm : Measurable h :=
    (RCLike.continuous_ofReal.measurable.comp hrm).add
      ((RCLike.continuous_ofReal.measurable.comp him).mul_const _)
  have hI : Integrable h μ := hri.ofReal.add (hii.ofReal.mul_const _)
  refine ⟨h, hm, hI, ?_⟩
  intro A hA
  rw [← hν A hA]
  have hrA : ∫ x in A, r x ∂μ = RCLike.re (ν A) := by
    rw [← withDensityᵥ_apply hri hA, hr]
    rfl
  have hiA : ∫ x in A, i x ∂μ = RCLike.im (ν A) := by
    rw [← withDensityᵥ_apply hii hA, hi]
    rfl
  dsimp only [h]
  rw [integral_add hri.ofReal.restrict (hii.ofReal.mul_const _).restrict,
    integral_mul_const, integral_ofReal, integral_ofReal, hrA, hiA, RCLike.re_add_im]



section DensityUpgrade
variable (μ : Measure X) [IsFiniteMeasure μ] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Continuous functionals on finite-exponent Lp are determined by indicators. -/
lemma ext_of_indicators (hp : p ≠ ∞) (L M : Lp 𝕜 p μ →L[𝕜] 𝕜)
    (h : ∀ (A : Set X) (hA : MeasurableSet A),
      L (indicatorConstLp p hA (measure_ne_top μ _) 1) =
        M (indicatorConstLp p hA (measure_ne_top μ _) 1)) : L = M := by
  borelize 𝕜
  ext f
  apply Lp.induction hp (fun f => L f = M f) ?_ ?_ (isClosed_eq L.continuous M.continuous) f
  · intro c A hA hfin
    rw [Lp.simpleFunc.coe_indicatorConst]
    have he : indicatorConstLp (μ := μ) p hA hfin.ne c =
        c • indicatorConstLp p hA (measure_ne_top μ _) 1 := by
      apply Lp.ext
      filter_upwards [indicatorConstLp_coeFn (μ := μ) (p := p) (hs := hA)
        (hμs := hfin.ne) (c := c), Lp.coeFn_smul c
        (indicatorConstLp (μ := μ) p hA (measure_ne_top μ _) (1 : 𝕜)),
        indicatorConstLp_coeFn (μ := μ) (p := p) (hs := hA)
        (hμs := measure_ne_top μ _) (c := (1 : 𝕜))] with x hx hs hx1
      by_cases hxA : x ∈ A <;> simp [hx, hs, hx1, hxA]
    rw [he, map_smul, map_smul, h A hA]
  · intro f g hf hg hd hLf hLg
    rw [map_add, map_add, hLf, hLg]

/-- Restriction to a measurable set, extended by zero, is a contraction on Lp. -/
def cutoff (A : Set X) (hA : MeasurableSet A) : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ :=
  ((ContinuousLinearMap.mul 𝕜 𝕜).holderL μ ∞ p p)
    (indicatorConstLp ∞ hA (measure_ne_top μ _) 1)

lemma cutoff_coe (A : Set X) (hA : MeasurableSet A) (f : Lp 𝕜 p μ) :
    cutoff μ p A hA f =ᵐ[μ] A.indicator (f : X → 𝕜) := by
  filter_upwards [(ContinuousLinearMap.mul 𝕜 𝕜).coeFn_holder (r := p)
    (indicatorConstLp (μ := μ) ∞ hA (measure_ne_top μ _) (1 : 𝕜)) f,
    indicatorConstLp_coeFn (μ := μ) (p := ∞) (hs := hA)
      (hμs := measure_ne_top μ _) (c := (1 : 𝕜))] with x hx hxA
  by_cases hxmem : x ∈ A <;> simpa [cutoff, hxA, hxmem] using hx

lemma norm_cutoff_apply_le (A : Set X) (hA : MeasurableSet A) (f : Lp 𝕜 p μ) :
    ‖cutoff μ p A hA f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (cutoff_coe μ p A hA f), Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_indicator_le (f : X → 𝕜) hA.nullMeasurableSet)

lemma cutoff_indicator (A : Set X) (hA : MeasurableSet A)
    (B : Set X) (hB : MeasurableSet B) :
    cutoff μ p A hA (indicatorConstLp p hB (measure_ne_top μ _) (1 : 𝕜)) =
      indicatorConstLp p (hB.inter hA) (measure_ne_top μ _) 1 := by
  apply Lp.ext
  filter_upwards [cutoff_coe μ p A hA
      (indicatorConstLp (μ := μ) p hB (measure_ne_top μ _) (1 : 𝕜)),
    indicatorConstLp_coeFn (μ := μ) (p := p) (hs := hB)
      (hμs := measure_ne_top μ _) (c := (1 : 𝕜)),
    indicatorConstLp_coeFn (μ := μ) (p := p) (hs := hB.inter hA)
      (hμs := measure_ne_top μ _) (c := (1 : 𝕜))] with x hx hxB hxBA
  by_cases hxA : x ∈ A <;> by_cases hxmemB : x ∈ B <;> simp_all

lemma pairing_indicator (q : ℝ≥0∞) [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (g : Lp 𝕜 q μ) (A : Set X) (hA : MeasurableSet A) :
    IntegralPairing.pairing μ p q g (indicatorConstLp p hA (measure_ne_top μ _) 1) =
      ∫ x in A, g x ∂μ := by
  change Specs.D11.Ch20.IntegralPairing.pairing_value μ p q g _ = _
  rw [(IntegralPairing.pairing_eq_integral μ p q g _).2, ← integral_indicator hA]
  apply integral_congr_ae
  filter_upwards [indicatorConstLp_coeFn (μ := μ) (p := p) (hs := hA)
    (hμs := measure_ne_top μ _) (c := (1 : 𝕜))] with x hx
  by_cases hxA : x ∈ A <;> simp [hx, hxA]



/-- Truncation, the exact norm of the pairing, and Fatou give the conjugate
norm bound. This proof works unchanged for q=∞, so includes p=1. -/
lemma density_memLp_bound [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (hp : p ≠ ∞) (q : ℝ≥0∞) [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (ℓ : Lp 𝕜 p μ →L[𝕜] 𝕜) (h : X → 𝕜) (hm : Measurable h) (_hi : Integrable h μ)
    (hr : ∀ (A : Set X) (hA : MeasurableSet A),
      ℓ (indicatorConstLp p hA (measure_ne_top μ _) 1) = ∫ x in A, h x ∂μ) :
    MemLp h q μ ∧ eLpNorm h q μ ≤ ENNReal.ofReal ‖ℓ‖ := by
  let A (n : ℕ) : Set X := {x | ‖h x‖ ≤ (n : ℝ)}
  have hA n : MeasurableSet (A n) := measurableSet_le hm.norm measurable_const
  let H (n : ℕ) : X → 𝕜 := (A n).indicator h
  have hb n : ∀ x, ‖H n x‖ ≤ (n : ℝ) := by
    intro x
    by_cases hx : x ∈ A n
    · rw [show H n = (A n).indicator h from rfl, Set.indicator_of_mem hx]
      exact hx
    · simp only [H, Set.indicator_of_notMem hx, norm_zero]
      positivity
  have hH n : MemLp (H n) q μ :=
    MemLp.of_bound (hm.indicator (hA n)).aestronglyMeasurable n (ae_of_all μ (hb n))
  have hnorm n : eLpNorm (H n) q μ ≤ ENNReal.ofReal ‖ℓ‖ := by
    let g : Lp 𝕜 q μ := (hH n).toLp (H n)
    have heq : IntegralPairing.pairing μ p q g = ℓ.comp (cutoff μ p (A n) (hA n)) := by
      apply ext_of_indicators μ p hp
      intro B hB
      rw [pairing_indicator μ p q g B hB, ContinuousLinearMap.comp_apply,
        cutoff_indicator μ p (A n) (hA n) B hB, hr (B ∩ A n) (hB.inter (hA n))]
      calc
        _ = ∫ x in B, H n x ∂μ := integral_congr_ae
          (ae_restrict_of_ae (MemLp.coeFn_toLp (hH n)))
        _ = ∫ x in B ∩ A n, h x ∂μ := by
          rw [show H n = (A n).indicator h from rfl, integral_indicator (hA n),
            Measure.restrict_restrict (hA n), inter_comm]
    have hg : ‖g‖ ≤ ‖ℓ‖ := by
      rw [← pairing_norm μ p q g]
      change ‖IntegralPairing.pairing μ p q g‖ ≤ _
      rw [heq]
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro f
      exact (ℓ.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (norm_cutoff_apply_le μ p _ (hA n) f) (norm_nonneg _))
    have hgg : ‖g‖ = (eLpNorm (H n) q μ).toReal := Lp.norm_toLp (H n) (hH n)
    rw [hgg] at hg
    rw [← ENNReal.ofReal_toReal (hH n).eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal hg
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => H n x) atTop (𝓝 (h x)) := by
    apply ae_of_all
    intro x
    apply tendsto_const_nhds.congr'
    obtain ⟨N, hN⟩ := exists_nat_ge ‖h x‖
    filter_upwards [eventually_ge_atTop N] with n hn
    have hx : x ∈ A n := hN.trans (by exact_mod_cast hn)
    exact (Set.indicator_of_mem hx h).symm
  have hnormlim : eLpNorm h q μ ≤ ENNReal.ofReal ‖ℓ‖ :=
    Lp.eLpNorm_le_of_ae_tendsto (Filter.Eventually.of_forall hnorm)
      (fun n => (hH n).aestronglyMeasurable) hm.aestronglyMeasurable hlim
  exact ⟨hnormlim.trans_lt ENNReal.ofReal_lt_top, hnormlim⟩

end DensityUpgrade


/-- Finite-measure scalar Lp duality for 1 ≤ p < ∞, including p=1 and
zero measures/functionals. The pairing is bilinear, with no conjugation. -/
theorem finite_measure_duality : Specs.D11.Ch20.LpDualFiniteMeasure.finite_measure_duality := by
  intro X 𝕜 _ _ μ _ p q _ _ _ hp ℓ
  borelize 𝕜
  obtain ⟨h, hm, hi, hr⟩ := integrable_density_exists μ p hp ℓ
  obtain ⟨hq, hbound⟩ := density_memLp_bound μ p hp q ℓ h hm hi hr
  let g : Lp 𝕜 q μ := hq.toLp h
  have heq : IntegralPairing.pairing μ p q g = ℓ := by
    apply ext_of_indicators μ p hp
    intro A hA
    calc
      _ = ∫ x in A, g x ∂μ := pairing_indicator μ p q g A hA
      _ = ∫ x in A, h x ∂μ :=
        integral_congr_ae (ae_restrict_of_ae (MemLp.coeFn_toLp hq))
      _ = _ := (hr A hA).symm
  have hg : ∀ f : Lp 𝕜 p μ, ℓ f = ∫ x, f x * g x ∂μ := by
    intro f
    exact (congrArg (fun L : Lp 𝕜 p μ →L[𝕜] 𝕜 => L f) heq).symm.trans
      (IntegralPairing.pairing_eq_integral μ p q g f).2
  obtain ⟨hnorm, huniq⟩ := representation_unique_norm μ p q ℓ g hg
  refine ⟨g, ⟨fun f => ⟨(IntegralPairing.pairing_eq_integral μ p q g f).1, hg f⟩,
    hnorm⟩, ?_⟩
  intro k hk
  exact huniq k (fun f => (hk.1 f).2)

end D11.Ch20.LpDualFiniteMeasure
