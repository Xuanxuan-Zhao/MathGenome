import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.ProkhorovMetric
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.LawSpaceSeparability
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.Topology.Instances.Rat
import Mathlib.Data.NNRat.Encodable
import Mathlib.Data.NNRat.BigOperators

open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace ProbabilityFoundations.Ch06
universe u
noncomputable section

/-- Probability laws with finite support in `D` and rational weights. -/
def rationalFiniteLaws {S : Type u} [MeasurableSpace S]
    (D : Set S) : Set (ProbabilityMeasure S) :=
  Specs.ProbabilityFoundations.Ch06.LawSpaceSeparability.rationalFiniteLawsValue D

theorem rationalFiniteLaws_countable {S : Type u} [MeasurableSpace S]
    (D : Set S) (hD : D.Countable) : (rationalFiniteLaws D).Countable := by
  classical
  let : Countable D := hD.to_subtype
  let f : (Σ n : ℕ, (Fin n → D) × (Fin n → ℚ≥0)) → Measure S :=
    fun c => ∑ i, ((c.2.2 i : ℝ≥0) : ℝ≥0∞) • Measure.dirac (c.2.1 i).val
  apply (Set.countable_range f).preimage ProbabilityMeasure.toMeasure_injective |>.mono
  rintro μ ⟨n, x, q, hx, hq, hμ⟩
  exact ⟨⟨n, (fun i => ⟨x i, hx i⟩), q⟩, hμ.symm⟩

private theorem nnrat_dense : DenseRange ((↑) : ℚ≥0 → ℝ≥0) := by
  apply dense_of_exists_between
  intro a b hab
  obtain ⟨q, haq, hqb⟩ := exists_rat_btwn (show (a : ℝ) < (b : ℝ) from hab)
  have hq : 0 ≤ q := by exact_mod_cast (a.coe_nonneg.trans haq.le)
  refine ⟨_, ⟨⟨q, hq⟩, rfl⟩, ?_, ?_⟩
  · exact_mod_cast haq
  · exact_mod_cast hqb

private def finiteDirac {S : Type u} [MeasurableSpace S]
    {ι : Type*} [Fintype ι] (x : ι → S) (p : ι → ℝ≥0) : FiniteMeasure S :=
  let d : ι → FiniteMeasure S := fun i => ⟨Measure.dirac (x i), inferInstance⟩
  ∑ i, p i • d i

private theorem finiteDirac_coe {S : Type u} [MeasurableSpace S]
    {ι : Type*} [Fintype ι] (x : ι → S) (p : ι → ℝ≥0) :
    (finiteDirac x p : Measure S) = ∑ i, (p i : ℝ≥0∞) • Measure.dirac (x i) := by
  simp only [finiteDirac, FiniteMeasure.toMeasure_sum]
  apply Finset.sum_congr rfl
  intro i _
  rfl

private theorem finiteDirac_mass {S : Type u} [MeasurableSpace S]
    {ι : Type*} [Fintype ι] (x : ι → S) (p : ι → ℝ≥0) :
    (finiteDirac x p).mass = ∑ i, p i := by
  apply ENNReal.coe_injective
  simp [FiniteMeasure.ennreal_mass, finiteDirac_coe]

private theorem finiteDirac_tendsto {S : Type u} [TopologicalSpace S]
    [MeasurableSpace S] [OpensMeasurableSpace S]
    {ι : Type*} [Fintype ι] (x : ι → S) (p : ι → ℝ≥0)
    (ps : ℕ → ι → ℝ≥0) (hp : ∀ i, Tendsto (fun k => ps k i) atTop (𝓝 (p i))) :
    Tendsto (fun k => finiteDirac x (ps k)) atTop (𝓝 (finiteDirac x p)) := by
  exact tendsto_finsetSum _ fun i _ => (hp i).smul tendsto_const_nhds

private theorem exists_nnrat_seq (p : ℝ≥0) :
    ∃ q : ℕ → ℚ≥0, Tendsto (fun k => (q k : ℝ≥0)) atTop (𝓝 p) := by
  obtain ⟨s, hs, ht⟩ := mem_closure_iff_seq_limit.mp (nnrat_dense p)
  choose q hq using hs
  exact ⟨q, by simpa only [show (fun k => (q k : ℝ≥0)) = s from funext hq] using ht⟩

private theorem normalize_rational_mem {S : Type u} [MeasurableSpace S] [Nonempty S]
    (D : Set S) {n : ℕ} (x : Fin n → S) (hx : ∀ i, x i ∈ D)
    (q : Fin n → ℚ≥0) (hq : ∑ i, q i ≠ 0) :
    (finiteDirac x (fun i => (q i : ℝ≥0))).normalize ∈ rationalFiniteLaws D := by
  classical
  have hmass : (finiteDirac x (fun i => (q i : ℝ≥0))).mass ≠ 0 := by
    rw [finiteDirac_mass]
    exact_mod_cast hq
  refine ⟨n, x, (fun i => q i / ∑ j, q j), hx, ?_, ?_⟩
  · rw [← Finset.sum_div, div_self hq]
  · rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero _
      ((FiniteMeasure.mass_nonzero_iff _).mp hmass), finiteDirac_coe, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Measure.coe_nnreal_smul, smul_smul, finiteDirac_mass]
    congr 1
    rw [← ENNReal.coe_mul]
    congr 1
    simp [NNRat.cast_sum, NNRat.cast_mul, NNRat.cast_inv,
      div_eq_mul_inv, mul_comm]

/-- Rational perturbation of a law already supported on finitely many chosen points. -/
private theorem finiteLaw_mem_closure {S : Type u} [TopologicalSpace S]
    [MeasurableSpace S] [OpensMeasurableSpace S]
    (D : Set S) {n : ℕ} (x : Fin n → S) (hx : ∀ i, x i ∈ D)
    (p : Fin n → ℝ≥0) (μ : ProbabilityMeasure S)
    (hμ : (μ : Measure S) = (finiteDirac x p : Measure S)) :
    μ ∈ closure (rationalFiniteLaws D) := by
  classical
  let : Nonempty S := μ.nonempty
  have heq : finiteDirac x p = μ.toFiniteMeasure :=
    FiniteMeasure.toMeasure_injective hμ.symm
  choose q hq using fun i => exists_nnrat_seq (p i)
  have ht := finiteDirac_tendsto x p (fun k i => (q i k : ℝ≥0)) hq
  have hn : finiteDirac x p ≠ 0 := by
    rw [heq]
    exact μ.toFiniteMeasure_nonzero
  have ht' := FiniteMeasure.tendsto_normalize_of_tendsto ht hn
  rw [heq, ProbabilityMeasure.toFiniteMeasure_normalize_eq_self] at ht'
  apply mem_closure_of_tendsto ht'
  have hpos : 0 < (finiteDirac x p).mass := by simp [heq]
  filter_upwards [ht.mass.eventually (lt_mem_nhds hpos)] with k hk
  apply normalize_rational_mem D x hx (fun i => q i k)
  intro hz
  have hz' : (finiteDirac x (fun i => (q i k : ℝ≥0))).mass = 0 := by
    rw [finiteDirac_mass, ← NNRat.cast_sum, hz]
    simp
  exact (ne_of_gt hk) hz'

private theorem finiteLaw_mem_closure_of_fintype {S : Type u} [TopologicalSpace S]
    [MeasurableSpace S] [OpensMeasurableSpace S] {ι : Type*} [Fintype ι]
    (D : Set S) (x : ι → S) (hx : ∀ i, x i ∈ D)
    (p : ι → ℝ≥0) (μ : ProbabilityMeasure S)
    (hμ : (μ : Measure S) = (finiteDirac x p : Measure S)) :
    μ ∈ closure (rationalFiniteLaws D) := by
  let e := (Fintype.equivFin ι).symm
  apply finiteLaw_mem_closure D (fun i => x (e i)) (fun i => hx (e i))
    (fun i => p (e i)) μ
  rw [hμ, finiteDirac_coe, finiteDirac_coe]
  exact (e.sum_comp (fun i => (p i : ℝ≥0∞) • Measure.dirac (x i))).symm

private theorem simpleLaw_mem_closure {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (D : Set S) (f : SimpleFunc S S) (hf : ∀ s, f s ∈ D) (μ : ProbabilityMeasure S) :
    μ.map f ∈ closure (rationalFiniteLaws D) := by
  classical
  apply finiteLaw_mem_closure_of_fintype D (fun i : f.range => (i : S))
    (fun i => by
      obtain ⟨s, hs⟩ := SimpleFunc.mem_range.mp i.property
      exact hs ▸ hf s)
    (fun i => μ (f ⁻¹' {(i : S)})) (μ.map f)
  rw [finiteDirac_coe]
  simp only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  rw [Finset.sum_coe_sort f.range (fun s : S =>
    (μ : Measure S) (f ⁻¹' {s}) • Measure.dirac s)]
  change (μ : Measure S).map f = _
  have h := (Measure.ae_mem_finset_iff_map_eq_sum_dirac (s := f.range)
    f.measurable.aemeasurable (μ := (μ : Measure S))).mp
      (Filter.Eventually.of_forall f.mem_range_self)
  simpa only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using h

private theorem simpleLaw_tendsto {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (μ : ProbabilityMeasure S) (fs : ℕ → SimpleFunc S S)
    (hfs : ∀ s, Tendsto (fun k => fs k s) atTop (𝓝 s)) :
    Tendsto (fun k => μ.map (fs k)) atTop (𝓝 μ) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  simp only [ProbabilityMeasure.toMeasure_map,
    integral_map (fs _).measurable.aemeasurable f.continuous.aestronglyMeasurable]
  apply tendsto_integral_filter_of_norm_le_const
  · exact Eventually.of_forall fun k => (f.continuous.measurable.comp
      (fs k).measurable).aestronglyMeasurable
  · exact ⟨‖f‖, Eventually.of_forall fun k =>
      Eventually.of_forall fun s => f.norm_coe_le_norm (fs k s)⟩
  · exact Eventually.of_forall fun s => (f.continuous.tendsto s).comp (hfs s)

/-- Density for the canonical weak topology; simple approximations take their
values in the specified dense set, even if the ambient space is incomplete. -/
private theorem rationalFiniteLaws_dense_weak {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (D : Set S) (hD : D.Countable) (hd : Dense D) :
    Dense (rationalFiniteLaws D) := by
  classical
  intro μ
  let : Nonempty S := μ.nonempty
  let : Countable D := hD.to_subtype
  obtain ⟨s₀, hs₀⟩ := hd.nonempty
  let fs : ℕ → SimpleFunc S S :=
    SimpleFunc.approxOn id measurable_id D s₀ hs₀
  have ht : Tendsto (fun k => μ.map (fs k)) atTop (𝓝 μ) :=
    simpleLaw_tendsto μ fs (fun s =>
      SimpleFunc.tendsto_approxOn measurable_id hs₀ (hd s))
  exact isClosed_closure.mem_of_tendsto ht (Eventually.of_forall fun k =>
    simpleLaw_mem_closure D (fs k)
      (SimpleFunc.approxOn_mem measurable_id hs₀ k) μ)

/-- The finite rational laws on any chosen countable dense set are π-dense. -/
theorem rationalFiniteLaws_dense {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (D : Set S) (hD : D.Countable) (hd : Dense D) :
    @Dense (ProbabilityMeasure S)
      (prokhorovMetricSpace (S := S)).toUniformSpace.toTopologicalSpace
      (rationalFiniteLaws D) := by
  let : SeparableSpace S := ⟨⟨D, hD, hd⟩⟩
  have heq : (prokhorovMetricSpace (S := S)).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (ProbabilityMeasure S)) :=
    (LevyProkhorov.probabilityMeasureHomeomorph (Ω := S)).isInducing.eq_induced.symm
  rw [heq]
  exact rationalFiniteLaws_dense_weak D hD hd

/-- All Borel probability laws form a separable space under the source metric π. -/
theorem lawSpace_separable {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] [SeparableSpace S] :
    @SeparableSpace (ProbabilityMeasure S)
      (prokhorovMetricSpace (S := S)).toUniformSpace.toTopologicalSpace := by
  obtain ⟨D, hD, hd⟩ := exists_countable_dense S
  let : TopologicalSpace (ProbabilityMeasure S) :=
    (prokhorovMetricSpace (S := S)).toUniformSpace.toTopologicalSpace
  exact ⟨⟨rationalFiniteLaws D, rationalFiniteLaws_countable D hD,
    rationalFiniteLaws_dense D hD hd⟩⟩

/-- On the empty state space, there are no probability laws. -/
theorem isEmpty_probabilityMeasure {S : Type u} [MeasurableSpace S] [IsEmpty S] :
    IsEmpty (ProbabilityMeasure S) :=
  ⟨fun μ => isEmptyElim (Classical.choice μ.nonempty)⟩

end
end ProbabilityFoundations.Ch06
