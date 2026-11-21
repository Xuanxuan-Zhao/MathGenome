import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.BochnerLpCompleteness
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hardy.AtomicHardySpace
import Batteries.Tactic.OpenPrivate

/-!
Atomic Hardy space from paper.tex:18378--18395. The independent Specs contain
canonical atoms, full-set ℓ¹ synthesis, and its kernel quotient. Here we prove
completeness, the contractive injective L¹ map, the infimum norm formula, and
zero integral. The countability and sequence theorems identify this quotient
with all the atomic series in the source, including repeated atoms. Euclidean
specializations remove the auxiliary ball-measure conditions, and pointwise
representatives identify the essential atom conditions with the original ones.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology lp
universe u v

namespace ExpandedFA.Hardy
namespace AtomicHardySpace

open AtomicHardySpaceSpec

abbrev IsAtom : IsAtomType.{u,v} := @IsAtomValue
abbrev Atom : AtomType.{u,v} := @AtomValue
abbrev Coefficients : CoefficientsType.{u,v} := @CoefficientsValue
abbrev synthesis : SynthesisType.{u,v} := @SynthesisValue
abbrev Hardy : HardyType.{u,v} := @HardyValue
abbrev embedding : EmbeddingType.{u,v} := @EmbeddingValue
abbrev atomicNorm : AtomicNormType.{u,v} := @AtomicNormValue

open private atom_bound from MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hardy.AtomicHardySpace

theorem atom_norm_le : AtomBound.{u,v} := by
  intro X _ _ _ 𝕜 _ μ a
  exact atom_bound μ a

theorem coefficient_norm : CoefficientNorm.{u,v} := by
  intro X _ _ _ 𝕜 _ μ c
  simpa using lp.norm_eq_tsum_rpow (by simp : 0 < (1 : ℝ≥0∞).toReal) c

theorem coefficient_support : CoefficientSupport.{u,v} := by
  intro X _ _ _ 𝕜 _ μ c
  exact (lp.memℓp c).summable_of_one.countable_support

theorem synthesis_series : SynthesisSeries.{u,v} := by
  intro X _ _ _ 𝕜 _ μ c
  have hs : Summable (fun a => c a • a.val) :=
    (lp.memℓp (weightedAtoms μ c)).summable_of_one
  refine ⟨hs.hasSum, ?_⟩
  change ‖∑' a, c a • a.val‖ ≤ ∑' a, ‖c a‖
  have hcn : Summable (fun a => ‖c a‖) := by
    simpa using (lp.memℓp c).summable (by simp)
  apply hs.hasSum.norm_le_of_bounded hcn.hasSum
  intro a
  rw [norm_smul]
  exact mul_le_of_le_one_right (norm_nonneg _) (atom_norm_le μ a)

theorem kernel_closed : KernelClosed.{u,v} := by
  intro X _ _ _ 𝕜 _ μ
  exact (SynthesisValue μ).isClosed_ker

theorem hardy_complete : HardyComplete.{u,v} := by
  intro X _ _ _ 𝕜 _ μ
  infer_instance

theorem embedding_properties : EmbeddingProperties.{u,v} := by
  intro X _ _ _ 𝕜 _ μ
  have hinj : Function.Injective (EmbeddingValue (𝕜 := 𝕜) μ) := by
    apply LinearMap.ker_eq_bot.mp
    exact Submodule.ker_liftQ_eq_bot _ _ le_rfl le_rfl
  refine ⟨hinj, fun h => ?_⟩
  apply QuotientAddGroup.le_norm_iff.mpr
  intro c hc
  rw [← hc]
  change ‖SynthesisValue μ c‖ ≤ ‖c‖
  rw [coefficient_norm μ c]
  exact (synthesis_series μ c).2

theorem atomic_range : AtomicRange.{u,v} := by
  intro X _ _ _ 𝕜 _ μ f
  constructor
  · rintro ⟨h, rfl⟩
    obtain ⟨c, rfl⟩ := (KernelValue (𝕜 := 𝕜) μ).mkQ_surjective h
    exact ⟨c, (synthesis_series μ c).1⟩
  · rintro ⟨c, hc⟩
    exact ⟨(KernelValue μ).mkQ c, (synthesis_series μ c).1.unique hc⟩

theorem atomic_norm_formula : AtomicNormFormula.{u,v} := by
  intro X _ _ _ 𝕜 _ μ h
  have hn : {r : ℝ | ∃ c : CoefficientsValue μ,
      SynthesisValue μ c = EmbeddingValue μ h ∧ (∑' a, ‖c a‖) = r}.Nonempty := by
    obtain ⟨c, rfl⟩ := (KernelValue (𝕜 := 𝕜) μ).mkQ_surjective h
    exact ⟨∑' a, ‖c a‖, c, rfl, rfl⟩
  have hb : BddBelow {r : ℝ | ∃ c : CoefficientsValue μ,
      SynthesisValue μ c = EmbeddingValue μ h ∧ (∑' a, ‖c a‖) = r} := by
    refine ⟨0, ?_⟩
    rintro r ⟨c, hc, rfl⟩
    positivity
  change ‖h‖ = sInf _
  apply le_antisymm
  · apply le_csInf hn
    rintro r ⟨c, hc, rfl⟩
    have heq : (KernelValue μ).mkQ c = h := (embedding_properties μ).1 hc
    rw [← coefficient_norm μ c, ← heq]
    exact Submodule.Quotient.norm_mk_le _ c
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨c, hc, hcn⟩ := Submodule.Quotient.norm_mk_lt h hε
    have he : SynthesisValue μ c = EmbeddingValue μ h := congrArg (EmbeddingValue μ) hc
    apply (csInf_le hb ⟨c, he, rfl⟩).trans
    rw [← coefficient_norm μ c]
    exact hcn.le

theorem integral_zero : IntegralZero.{u,v} := by
  intro X _ _ _ 𝕜 _ μ h
  obtain ⟨c, rfl⟩ := (KernelValue (𝕜 := 𝕜) μ).mkQ_surjective h
  have hs := (synthesis_series μ c).1
  have hi := (MeasureTheory.L1.integralCLM' 𝕜).hasSum hs
  have hz : ∀ a : AtomValue (𝕜 := 𝕜) μ,
      MeasureTheory.L1.integralCLM' 𝕜 (c a • a.val) = 0 := by
    intro a
    rw [map_smul]
    rw [← MeasureTheory.L1.integral_eq', MeasureTheory.L1.integral_eq_integral,
      a.property.1, smul_zero]
  have he := hi.unique (by simpa only [hz] using (hasSum_zero (α := 𝕜)
      (β := AtomValue (𝕜 := 𝕜) μ)))
  change (∫ x, SynthesisValue μ c x ∂μ) = 0
  rw [← MeasureTheory.L1.integral_eq_integral, MeasureTheory.L1.integral_eq' 𝕜]
  exact he

theorem raw_atom_realization : RawAtomRealization.{u,v} := by
  intro X _ _ _ 𝕜 _ μ f hf hz hb
  rcases hb with ⟨c, r, hr, hm0, hmt, hb⟩
  let B := Metric.ball c r
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hg : Integrable (B.indicator (fun _ : X => (μ.real B)⁻¹)) μ :=
    (integrable_indicator_iff hB).mpr (integrableOn_const hmt)
  have hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ B.indicator (fun _ : X => (μ.real B)⁻¹) x := by
    filter_upwards [hb] with x hx
    by_cases hxB : x ∈ B
    · simpa [Set.indicator_of_mem hxB] using hx.2
    · simp [Set.indicator_of_notMem hxB, hx.1 hxB]
  have hfi : Integrable f μ := hg.mono' hf hbound
  let F := hfi.toL1 f
  have he : F =ᵐ[μ] f := hfi.coeFn_toL1
  refine ⟨⟨F, ?_⟩, he⟩
  refine ⟨(integral_congr_ae he).trans hz, c, r, hr, hm0, hmt, ?_⟩
  filter_upwards [he, hb] with x hx hxB
  simpa only [hx] using hxB

theorem countable_representation : CountableRepresentation.{u,v} := by
  intro X _ _ _ 𝕜 _ μ h
  obtain ⟨c, rfl⟩ := (KernelValue (𝕜 := 𝕜) μ).mkQ_surjective h
  refine ⟨c, coefficient_support μ c, ?_⟩
  apply (hasSum_subtype_iff_of_support_subset ?_).mpr (synthesis_series μ c).1
  intro a ha
  by_contra hzero
  have hz : c a = 0 := not_not.mp hzero
  exact ha (by simp [hz])

section AtomicSeries
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable {𝕜 : Type v} [RCLike 𝕜] (μ : Measure X)

/-- A single atom as an element of the quotient. -/
def atomElement (a : AtomValue (𝕜 := 𝕜) μ) : HardyValue (𝕜 := 𝕜) μ :=
  by
    classical
    exact (KernelValue μ).mkQ (lp.single 1 a (1 : 𝕜))

theorem atomElement_norm (a : AtomValue (𝕜 := 𝕜) μ) : ‖atomElement μ a‖ ≤ 1 := by
  classical
  apply (Submodule.Quotient.norm_mk_le _ _).trans
  simp [lp.norm_single (by simp : 0 < (1 : ℝ≥0∞))]

theorem embedding_atomElement (a : AtomValue (𝕜 := 𝕜) μ) :
    EmbeddingValue μ (atomElement μ a) = a.val := by
  classical
  change (∑' b : AtomValue (𝕜 := 𝕜) μ, lp.single (E := fun _ : AtomValue (𝕜 := 𝕜) μ => 𝕜) 1 a (1 : 𝕜) b • b.val) = a.val
  rw [tsum_eq_single a]
  · simp
  · intro b hb
    have hz : lp.single (E := fun _ : AtomValue (𝕜 := 𝕜) μ => 𝕜) 1 a (1 : 𝕜) b = 0 :=
      lp.single_apply_ne 1 a 1 hb
    exact (congrArg (fun k : 𝕜 => k • b.val) hz).trans (zero_smul 𝕜 b.val)

end AtomicSeries

theorem sequence_series : SequenceSeries.{u,v} := by
  intro X _ _ _ 𝕜 _ μ a c hc
  have hs : Summable (fun j => c j • atomElement μ (a j)) := by
    apply hc.of_norm_bounded
    intro j
    rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) (atomElement_norm μ (a j))
  refine ⟨∑' j, c j • atomElement μ (a j), ?_, ?_⟩
  · convert hs.hasSum.mapL (EmbeddingValue μ) using 1
    simp only [map_smul, embedding_atomElement]
  · apply hs.hasSum.norm_le_of_bounded hc.hasSum
    intro j
    rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) (atomElement_norm μ (a j))

theorem euclidean_atom_realization : EuclideanAtomRealization.{v} := by
  intro d 𝕜 _ f hf hz hb
  rcases hb with ⟨c, r, hr, hb⟩
  apply raw_atom_realization volume f hf hz
  exact ⟨c, r, hr, (Metric.measure_ball_pos volume c hr).ne',
    measure_ball_ne_top, hb⟩

/-- The zero atom provides the filler when a finite expansion is written as
an infinite sequence. It is allowed by the source's definition of an atom. -/
theorem euclidean_atoms_nonempty (d : ℕ) (𝕜 : Type v) [RCLike 𝕜] :
    Nonempty (AtomValue (𝕜 := 𝕜) (volume : Measure (EuclideanSpace ℝ (Fin d)))) := by
  obtain ⟨a, _⟩ := euclidean_atom_realization d (fun _ => (0 : 𝕜))
    aestronglyMeasurable_zero (by simp)
    ⟨0, 1, zero_lt_one, Filter.Eventually.of_forall (fun x => by
      simp only [norm_zero, implies_true, true_and]
      positivity)⟩
  exact ⟨a⟩

theorem coefficient_sequence : CoefficientSequence.{u,v} := by
  classical
  intro X _ _ _ 𝕜 _ μ _ c
  let S := Function.support c
  have : Countable S := (coefficient_support μ c).to_subtype
  obtain ⟨e, he⟩ := exists_injective_nat S
  let a₀ : AtomValue (𝕜 := 𝕜) μ := Classical.choice inferInstance
  let a : ℕ → AtomValue (𝕜 := 𝕜) μ := Function.extend e Subtype.val (fun _ => a₀)
  let b : ℕ → 𝕜 := Function.extend e (fun s : S => c s.val) 0
  have hnorm : (fun n => ‖b n‖) = Function.extend e (fun s : S => ‖c s.val‖) 0 := by
    funext n
    by_cases hn : ∃ s, e s = n
    · rcases hn with ⟨s, rfl⟩
      simp [b, he.extend_apply]
    · simp [b, Function.extend_apply' _ _ _ hn]
  have hvec : (fun n => b n • (a n).val) =
      Function.extend e (fun s : S => c s.val • s.val.val) 0 := by
    funext n
    by_cases hn : ∃ s, e s = n
    · rcases hn with ⟨s, rfl⟩
      simp [a, b, he.extend_apply]
    · simp [a, b, Function.extend_apply' _ _ _ hn]
  refine ⟨a, b, ?_, ?_⟩
  · rw [hnorm, hasSum_extend_zero he]
    apply (hasSum_subtype_iff_of_support_subset
      (f := fun a : AtomValue (𝕜 := 𝕜) μ => ‖c a‖) (s := S) ?_).mpr
    · rw [coefficient_norm μ c]
      exact (show Summable (fun a => ‖c a‖) from
        by simpa using (lp.memℓp c).summable (by simp)).hasSum
    · intro s hs
      simpa only [S, Function.mem_support, norm_ne_zero_iff] using hs
  · rw [hvec, hasSum_extend_zero he]
    apply (hasSum_subtype_iff_of_support_subset ?_).mpr (synthesis_series μ c).1
    intro s hs
    by_contra hzero
    have hz : c s = 0 := not_not.mp hzero
    exact hs (by simp [hz])

theorem euclidean_sequence_range : EuclideanSequenceRange.{v} := by
  intro d 𝕜 _ f
  let μ : Measure (EuclideanSpace ℝ (Fin d)) := volume
  have := euclidean_atoms_nonempty d 𝕜
  constructor
  · rintro ⟨h, rfl⟩
    obtain ⟨c, hc⟩ := (KernelValue (𝕜 := 𝕜) μ).mkQ_surjective h
    obtain ⟨a, b, hb, hv⟩ := coefficient_sequence μ c
    refine ⟨a, b, hb.summable, ?_⟩
    have he : SynthesisValue μ c = EmbeddingValue μ h := congrArg (EmbeddingValue μ) hc
    exact he ▸ hv
  · rintro ⟨a, c, hc, hf⟩
    obtain ⟨h, hh, _⟩ := sequence_series μ a c hc
    exact ⟨h, hh.unique hf⟩

theorem euclidean_sequence_norm : EuclideanSequenceNorm.{v} := by
  intro d 𝕜 _ h
  let μ : Measure (EuclideanSpace ℝ (Fin d)) := volume
  have := euclidean_atoms_nonempty d 𝕜
  let R : Set ℝ := {r : ℝ | ∃ a : ℕ → AtomValue (𝕜 := 𝕜) μ, ∃ c : ℕ → 𝕜,
    Summable (fun j => ‖c j‖) ∧
    HasSum (fun j => c j • (a j).val) (EmbeddingValue μ h) ∧
    (∑' j, ‖c j‖) = r}
  have hR : R.Nonempty := by
    obtain ⟨a, c, hc, hv⟩ := (euclidean_sequence_range d (EmbeddingValue μ h)).mp ⟨h, rfl⟩
    exact ⟨∑' j, ‖c j‖, a, c, hc, hv, rfl⟩
  have hB : BddBelow R := by
    refine ⟨0, ?_⟩
    rintro r ⟨a, c, hc, hv, rfl⟩
    positivity
  change ‖h‖ = sInf R
  apply le_antisymm
  · apply le_csInf hR
    rintro r ⟨a, c, hc, hv, rfl⟩
    obtain ⟨h', hh', hn'⟩ := sequence_series μ a c hc
    have he : h' = h := (embedding_properties μ).1 (hh'.unique hv)
    exact he ▸ hn'
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨c, hc, hn⟩ := Submodule.Quotient.norm_mk_lt h hε
    obtain ⟨a, b, hb, hv⟩ := coefficient_sequence μ c
    have he : SynthesisValue μ c = EmbeddingValue μ h := congrArg (EmbeddingValue μ) hc
    have hm : ‖c‖ ∈ R := ⟨a, b, hb.summable, he ▸ hv, hb.tsum_eq⟩
    exact (csInf_le hB hm).trans hn.le

theorem atom_representative : AtomRepresentative.{u,v} := by
  classical
  intro X _ _ _ 𝕜 _ μ a
  rcases a.property with ⟨hz, c, r, hr, hm0, hmt, hb⟩
  let ha := Lp.aestronglyMeasurable a.val
  let g := ha.mk a.val
  have hg : StronglyMeasurable g := ha.stronglyMeasurable_mk
  have hga : g =ᵐ[μ] a.val := ha.ae_eq_mk.symm
  let B := Metric.ball c r
  let M := (μ.real B)⁻¹
  let S : Set X := B ∩ {x | ‖g x‖ ≤ M}
  have hS : MeasurableSet S := Metric.isOpen_ball.measurableSet.inter
    (measurableSet_le hg.norm.measurable measurable_const)
  let f := S.indicator g
  have hfa : f =ᵐ[μ] a.val := by
    filter_upwards [hga, hb] with x hx hxb
    by_cases hxB : x ∈ B
    · have hxs : x ∈ S := ⟨hxB, by
        change ‖g x‖ ≤ M
        rw [hx]
        exact hxb.2⟩
      simpa only [f, Set.indicator_of_mem hxs] using hx
    · have hxs : x ∉ S := fun h => hxB h.1
      simp [f, Set.indicator_of_notMem hxs, hxb.1 hxB]
  refine ⟨f, hg.indicator hS, hfa, (integral_congr_ae hfa).trans hz,
    c, r, hr, hm0, hmt, ?_, ?_⟩
  · intro x hx
    exact Set.indicator_of_notMem (fun h : x ∈ S => hx h.1) g
  · intro x
    by_cases hx : x ∈ S
    · change ‖S.indicator g x‖ ≤ M
      rw [Set.indicator_of_mem hx]
      exact hx.2
    · simp only [f, Set.indicator_of_notMem hx, norm_zero]
      positivity

end AtomicHardySpace
end ExpandedFA.Hardy
