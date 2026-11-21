import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Analysis.Normed.Affine.ContinuousAffineMap
import Mathlib.Topology.Algebra.ContinuousAffineEquiv
import Mathlib.Topology.Compactness.LocallyFinite
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.SmoothPartitionOfUnity
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.MeanValue
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.FractionalSobolev
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.LpTranslationContinuity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.AbsoluteContinuityOnLines

noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace ExpandedFA.PartIV.FractionalSobolev

abbrev Space : Specs.ExpandedFA.PartIV.FractionalSobolev.SpaceType :=
  Specs.ExpandedFA.PartIV.FractionalSobolev.SpaceValue

abbrev HigherSpace : Specs.ExpandedFA.PartIV.FractionalSobolev.SpaceType :=
  Specs.ExpandedFA.PartIV.FractionalSobolev.HigherSpaceValue

def seminormPower : Specs.ExpandedFA.PartIV.FractionalSobolev.EnergyType :=
  Specs.ExpandedFA.PartIV.FractionalSobolev.EnergyValue

def differenceSeminorm : Specs.ExpandedFA.PartIV.FractionalSobolev.EnergyType :=
  Specs.ExpandedFA.PartIV.FractionalSobolev.SeminormValue

def fullNorm : Specs.ExpandedFA.PartIV.FractionalSobolev.NormType :=
  Specs.ExpandedFA.PartIV.FractionalSobolev.NormValue

def higherFullNorm : Specs.ExpandedFA.PartIV.FractionalSobolev.HigherNormType :=
  Specs.ExpandedFA.PartIV.FractionalSobolev.HigherNormValue

theorem difference_kernel_formula : Specs.ExpandedFA.PartIV.FractionalSobolev.KernelFormula := by
  intro d s p h hh
  simp only [differenceKernel, ite_eq_right hh, ENNReal.rpow_neg, one_div]

theorem difference_seminorm_finite_iff :
    Specs.ExpandedFA.PartIV.FractionalSobolev.SeminormFiniteIff := by
  intro 𝕜 _ d s p _ hp u
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  exact ENNReal.rpow_lt_top_iff_of_pos (one_div_pos.mpr (ENNReal.toReal_pos hp0 hp))

theorem norm_formula : Specs.ExpandedFA.PartIV.FractionalSobolev.NormFormula := by
  intro 𝕜 _ d s p _ u
  rfl

@[simp] theorem euclideanLength_zero {d : ℕ} : euclideanLength (0 : Fin d → ℝ) = 0 := by
  simp [euclideanLength]

@[simp] theorem euclideanLength_eq_zero {d : ℕ} (h : Fin d → ℝ) :
    euclideanLength h = 0 ↔ h = 0 := by
  simp [euclideanLength]

theorem euclideanLength_continuous {d : ℕ} : Continuous (@euclideanLength d) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).norm

@[simp] theorem differenceKernel_zero {d : ℕ} (s : ℝ) (p : ℝ≥0∞) :
    differenceKernel s p (0 : Fin d → ℝ) = 0 := by
  simp [differenceKernel]

theorem differenceKernel_measurable {d : ℕ} (s : ℝ) (p : ℝ≥0∞) :
    Measurable (@differenceKernel d s p) := by
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    ((euclideanLength_continuous.measurable.ennreal_ofReal).pow_const _)

/-- The defining pth-power integral agrees with the actual translation norm. -/
theorem difference_energy_translation :
    Specs.ExpandedFA.PartIV.FractionalSobolev.TranslationFormula := by
  intro 𝕜 _ d s p _ hp u
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hpr : p.toReal ≠ 0 := (ENNReal.toReal_pos hp0 hp).ne'
  unfold differenceEnergy
  apply lintegral_congr
  intro h
  congr 1
  let v := ExpandedFA.Distributions.LpTranslationContinuitySpec.LpTranslationValue p (-h) u - u
  have hv : v =ᵐ[volume] fun x => u (x + h) - u x := by
    filter_upwards [Lp.coeFn_sub
      (ExpandedFA.Distributions.LpTranslationContinuitySpec.LpTranslationValue p (-h) u) u,
      ExpandedFA.Distributions.lpTranslation_representative p (-h) u] with x hx htx
    change v x = _ - _ at hx
    rw [hx, htx]
    simp only [sub_neg_eq_add]
  have hv' : (fun x => ‖v x‖ₑ ^ p.toReal) =ᵐ[volume]
      fun x => ‖u (x + h) - u x‖ₑ ^ p.toReal :=
    hv.mono fun x hx => congrArg (fun z : 𝕜 => ‖z‖ₑ ^ p.toReal) hx
  rw [← lintegral_congr_ae hv']
  change (∫⁻ x, ‖v x‖ₑ ^ p.toReal) = ‖v‖ₑ ^ p.toReal
  rw [Lp.enorm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp (Lp.aestronglyMeasurable v),
    ← ENNReal.rpow_mul, one_div_mul_cancel hpr, ENNReal.rpow_one]

/-- Tonelli and translation of Lebesgue measure give the Gagliardo formula. -/
theorem difference_energy_double_integral :
    Specs.ExpandedFA.PartIV.FractionalSobolev.DoubleIntegralFormula := by
  intro 𝕜 _ d s p _ u
  have hu := (Lp.stronglyMeasurable u).measurable
  have hm : Measurable (fun z : (Fin d → ℝ) × (Fin d → ℝ) =>
      differenceKernel s p z.1 * ‖u (z.2 + z.1) - u z.2‖ₑ ^ p.toReal) := by
    exact ((differenceKernel_measurable s p).comp measurable_fst).mul
      (((hu.comp (measurable_snd.add measurable_fst)).sub
        (hu.comp measurable_snd)).enorm.pow_const _)
  unfold differenceEnergy doubleEnergy
  calc
    _ = ∫⁻ h, ∫⁻ x, differenceKernel s p h * ‖u (x + h) - u x‖ₑ ^ p.toReal := by
      apply lintegral_congr
      intro h
      exact (lintegral_const_mul _
        (((hu.comp (measurable_id.add_const h)).sub hu).enorm.pow_const _)).symm
    _ = ∫⁻ x, ∫⁻ h, differenceKernel s p h * ‖u (x + h) - u x‖ₑ ^ p.toReal :=
      lintegral_lintegral_swap hm.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro x
      have hf : Measurable (fun y : Fin d → ℝ =>
          differenceKernel s p (y - x) * ‖u y - u x‖ₑ ^ p.toReal) := by
        exact ((differenceKernel_measurable s p).comp (measurable_id.sub_const x)).mul
          ((hu.sub measurable_const).enorm.pow_const _)
      convert (measurePreserving_add_left (volume : Measure (Fin d → ℝ)) x).lintegral_comp hf using 1
      simp only [add_sub_cancel_left]

theorem difference_energy_representative :
    Specs.ExpandedFA.PartIV.FractionalSobolev.RepresentativeFormula := by
  intro 𝕜 _ d s p _ u f huf
  unfold differenceEnergy
  apply lintegral_congr
  intro h
  congr 1
  apply lintegral_congr_ae
  filter_upwards [huf,
    (measurePreserving_add_right (volume : Measure (Fin d → ℝ)) h).quasiMeasurePreserving.ae_eq_comp huf]
    with x hx hxh
  change u (x + h) = f (x + h) at hxh
  rw [hx, hxh]

theorem lpIncrement_continuous {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : Lp 𝕜 p (volume : Measure (Fin d → ℝ))) :
    Continuous (fun h => lpIncrement p h u) :=
  ((ExpandedFA.Distributions.lpTranslation_continuous p hp u).comp continuous_neg).sub
    continuous_const

theorem difference_energy_weighted_integral {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : Lp 𝕜 p (volume : Measure (Fin d → ℝ))) :
    differenceEnergy s p u =
      ∫⁻ h, ‖lpIncrement p h u‖ₑ ^ p.toReal ∂differenceMeasure s p := by
  rw [difference_energy_translation 𝕜 d s p hp u]
  exact (lintegral_withDensity_eq_lintegral_mul volume (differenceKernel_measurable s p)
    ((lpIncrement_continuous p hp u).enorm.measurable.pow_const _)).symm

theorem difference_energy_weightedLp :
    Specs.ExpandedFA.PartIV.FractionalSobolev.WeightedLpFormula := by
  intro 𝕜 _ d s p _ hp u
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  rw [difference_energy_weighted_integral s p hp u,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp
      (lpIncrement_continuous p hp u).stronglyMeasurable.aestronglyMeasurable]

theorem finite_energy_iff_memLp {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : Lp 𝕜 p (volume : Measure (Fin d → ℝ))) :
    differenceEnergy s p u < ∞ ↔
      MemLp (fun h => lpIncrement p h u) p (differenceMeasure s p) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hp
    (lpIncrement_continuous p hp u).stronglyMeasurable.aestronglyMeasurable,
    ← difference_energy_weighted_integral s p hp u]

theorem finite_energy_zero {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    differenceEnergy s p (0 : Lp 𝕜 p (volume : Measure (Fin d → ℝ))) < ∞ := by
  rw [finite_energy_iff_memLp s p hp]
  simpa only [map_zero, Pi.zero_def] using
    (MemLp.zero : MemLp (0 : (Fin d → ℝ) → Lp 𝕜 p volume) p (differenceMeasure s p))

theorem finite_energy_add {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u v : Lp 𝕜 p (volume : Measure (Fin d → ℝ)))
    (hu : differenceEnergy s p u < ∞) (hv : differenceEnergy s p v < ∞) :
    differenceEnergy s p (u + v) < ∞ := by
  rw [finite_energy_iff_memLp s p hp] at hu hv ⊢
  simpa only [map_add, Pi.add_def] using hu.add hv

theorem finite_energy_smul {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (c : 𝕜) (u : Lp 𝕜 p (volume : Measure (Fin d → ℝ)))
    (hu : differenceEnergy s p u < ∞) : differenceEnergy s p (c • u) < ∞ := by
  rw [finite_energy_iff_memLp s p hp] at hu ⊢
  simpa only [map_smul, Pi.smul_def] using hu.const_smul c

theorem fractionalNorm_eq_weightedLp {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : FractionalSpace 𝕜 d s p) :
    fractionalNorm s p u = ‖u.val‖ +
      (eLpNorm (fun h => lpIncrement p h u.val) p (differenceMeasure s p)).toReal := by
  rw [fractionalNorm, ENNReal.toReal_rpow, difference_energy_weightedLp 𝕜 d s p hp u.val]

theorem fractionalNorm_nonneg {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : FractionalSpace 𝕜 d s p) :
    0 ≤ fractionalNorm s p u :=
  add_nonneg (norm_nonneg _) (Real.rpow_nonneg (ENNReal.toReal_nonneg) _)

theorem norm_le_fractionalNorm {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : FractionalSpace 𝕜 d s p) :
    ‖u.val‖ ≤ fractionalNorm s p u :=
  le_add_of_nonneg_right (Real.rpow_nonneg (ENNReal.toReal_nonneg) _)

theorem fractionalNorm_eq_zero_iff {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : FractionalSpace 𝕜 d s p) : fractionalNorm s p u = 0 ↔ u.val = 0 := by
  constructor
  · intro hz
    apply norm_eq_zero.mp
    exact le_antisymm (hz ▸ norm_le_fractionalNorm s p u) (norm_nonneg _)
  · intro hz
    rw [fractionalNorm_eq_weightedLp s p hp, hz]
    simp only [map_zero, norm_zero, ← Pi.zero_def, eLpNorm_zero, ENNReal.toReal_zero, add_zero]

theorem fractionalNorm_add_le {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u v : FractionalSpace 𝕜 d s p) :
    fractionalNorm s p ⟨u.val + v.val, finite_energy_add s p hp _ _ u.property v.property⟩ ≤
      fractionalNorm s p u + fractionalNorm s p v := by
  simp only [fractionalNorm_eq_weightedLp s p hp]
  have hu := (finite_energy_iff_memLp s p hp u.val).mp u.property
  have hv := (finite_energy_iff_memLp s p hp v.val).mp v.property
  have hadd : (eLpNorm (fun h => lpIncrement p h (u.val + v.val)) p (differenceMeasure s p)).toReal ≤
      (eLpNorm (fun h => lpIncrement p h u.val) p (differenceMeasure s p)).toReal +
      (eLpNorm (fun h => lpIncrement p h v.val) p (differenceMeasure s p)).toReal := by
    rw [← ENNReal.toReal_add hu.ne hv.ne]
    apply ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hu.ne, hv.ne⟩)
    simpa only [map_add, Pi.add_def] using
      (eLpNorm_add_le (p := p) (μ := differenceMeasure s p) (f := fun h => lpIncrement p h u.val)
        (g := fun h => lpIncrement p h v.val) (Fact.out : 1 ≤ p))
  have hn := norm_add_le u.val v.val
  linarith

theorem fractionalNorm_smul {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (c : 𝕜) (u : FractionalSpace 𝕜 d s p) :
    fractionalNorm s p ⟨c • u.val, finite_energy_smul s p hp c _ u.property⟩ =
      ‖c‖ * fractionalNorm s p u := by
  simp only [fractionalNorm_eq_weightedLp s p hp, norm_smul]
  have hs : eLpNorm (fun h => lpIncrement p h (c • u.val)) p (differenceMeasure s p) =
      ‖c‖ₑ * eLpNorm (fun h => lpIncrement p h u.val) p (differenceMeasure s p) := by
    simpa only [map_smul, Pi.smul_def] using
      (eLpNorm_const_smul c (fun h => lpIncrement p h u.val) p (differenceMeasure s p))
  rw [hs, ENNReal.toReal_mul, toReal_enorm]
  ring

theorem fractional_full_norm_axioms : Specs.ExpandedFA.PartIV.FractionalSobolev.FullNormAxioms := by
  intro 𝕜 _ d s p _ hp
  refine ⟨finite_energy_zero s p hp, ?_⟩
  intro u v hu hv
  exact ⟨fractionalNorm_nonneg s p ⟨u, hu⟩,
    fractionalNorm_eq_zero_iff s p hp ⟨u, hu⟩,
    ⟨finite_energy_add s p hp u v hu hv, fractionalNorm_add_le s p hp ⟨u, hu⟩ ⟨v, hv⟩⟩,
    fun c => ⟨finite_energy_smul s p hp c u hu, fractionalNorm_smul s p hp c ⟨u, hu⟩⟩⟩

/-- The canonical finite-energy subset is a scalar-linear subspace. -/
def finiteEnergySubmodule {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Submodule 𝕜 (Lp 𝕜 p (volume : Measure (Fin d → ℝ))) where
  carrier := {u | differenceEnergy s p u < ∞}
  zero_mem' := finite_energy_zero s p hp
  add_mem' := fun hu hv => finite_energy_add s p hp _ _ hu hv
  smul_mem' := fun c _ hu => finite_energy_smul s p hp c _ hu

section NormedStructure
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (s : ℝ) (p : ℝ≥0∞)
  [Fact (1 ≤ p)] [Fact (p ≠ ∞)]

instance fractionalAddCommGroup : AddCommGroup (FractionalSpace 𝕜 d s p) :=
  inferInstanceAs (AddCommGroup (finiteEnergySubmodule (𝕜 := 𝕜) (d := d) s p Fact.out))

instance fractionalModule : Module 𝕜 (FractionalSpace 𝕜 d s p) :=
  inferInstanceAs (Module 𝕜 (finiteEnergySubmodule (𝕜 := 𝕜) (d := d) s p Fact.out))

private theorem fractionalNormCore : NormedSpace.Core 𝕜 (FractionalSpace 𝕜 d s p) where
  norm_nonneg := fractionalNorm_nonneg s p
  norm_smul := fun c u => fractionalNorm_smul s p Fact.out c u
  norm_triangle := fun u v => fractionalNorm_add_le s p Fact.out u v
  norm_eq_zero_iff u := (fractionalNorm_eq_zero_iff s p Fact.out u).trans
    ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

instance fractionalNormedAddCommGroup : NormedAddCommGroup (FractionalSpace 𝕜 d s p) :=
  NormedAddCommGroup.ofCore (fractionalNormCore s p)

/-- Use the full norm topology on the finite-energy subtype. -/
instance fractionalMetricSpace : MetricSpace (FractionalSpace 𝕜 d s p) :=
  (fractionalNormedAddCommGroup s p).toMetricSpace

instance fractionalPseudoMetricSpace : PseudoMetricSpace (FractionalSpace 𝕜 d s p) :=
  (fractionalNormedAddCommGroup s p).toMetricSpace.toPseudoMetricSpace

instance fractionalUniformSpace : UniformSpace (FractionalSpace 𝕜 d s p) :=
  (fractionalNormedAddCommGroup s p).toMetricSpace.toPseudoMetricSpace.toUniformSpace

instance fractionalBornology : Bornology (FractionalSpace 𝕜 d s p) :=
  (fractionalNormedAddCommGroup s p).toMetricSpace.toPseudoMetricSpace.toBornology

instance fractionalTopologicalSpace : TopologicalSpace (FractionalSpace 𝕜 d s p) :=
  (fractionalNormedAddCommGroup s p).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

instance fractionalEDist : EDist (FractionalSpace 𝕜 d s p) :=
  (fractionalNormedAddCommGroup s p).toMetricSpace.toPseudoMetricSpace.toEDist

instance fractionalPseudoEMetricSpace : PseudoEMetricSpace (FractionalSpace 𝕜 d s p) :=
  (fractionalNormedAddCommGroup s p).toMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace

instance fractionalEMetricSpace : EMetricSpace (FractionalSpace 𝕜 d s p) :=
  (fractionalNormedAddCommGroup s p).toMetricSpace.toEMetricSpace

instance fractionalNNDist : NNDist (FractionalSpace 𝕜 d s p) :=
  (fractionalNormedAddCommGroup s p).toMetricSpace.toPseudoMetricSpace.toNNDist

instance fractionalNormedSpace : NormedSpace 𝕜 (FractionalSpace 𝕜 d s p) :=
  NormedSpace.ofCore (fractionalNormCore s p)

end NormedStructure

@[simp] theorem natIndex_firstIndex {d : ℕ} (i : Fin d) :
    ExpandedFA.Sobolev.natIndex (firstIndex i) = Pi.single i 1 := by
  classical
  funext j
  simp [ExpandedFA.Sobolev.natIndex, firstIndex, Pi.single_apply, apply_ite]

theorem first_derivative_formula {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : ExpandedFA.Sobolev.SobolevSpace 𝕜 d ⊤ 1 p) (i : Fin d) :
    ExpandedFA.Sobolev.lpDistribution (u.val (firstIndex i)) =
      -(ExpandedFA.Sobolev.lpDistribution (u.val (ExpandedFA.Sobolev.zeroIndex d 1))).comp
        (ExpandedFA.Distributions.testPartialCLM [i]) := by
  have he := u.property (firstIndex i)
  change ExpandedFA.Sobolev.lpDistribution (u.val (firstIndex i)) =
    ExpandedFA.Distributions.distributionDerivative 𝕜 d ⊤
      (ExpandedFA.Distributions.multiIndexWord (ExpandedFA.Sobolev.natIndex (firstIndex i)))
        (ExpandedFA.Sobolev.lpDistribution (u.val (ExpandedFA.Sobolev.zeroIndex d 1))) at he
  simpa [natIndex_firstIndex, ExpandedFA.Sobolev.Lines.multiIndexWord_single,
    ExpandedFA.Distributions.distributionDerivative_cons,
    ExpandedFA.Distributions.distributionDerivative_nil] using he

theorem higher_fractional_membership :
    Specs.ExpandedFA.PartIV.FractionalSobolev.HigherMembership := by
  intro 𝕜 _ d s p _ u
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨fun i => v.val.val (firstIndex i), ?_, v.property⟩
    intro i
    rw [← hv]
    exact first_derivative_formula v.val i
  · rintro ⟨g, hg, hgf⟩
    obtain ⟨v, hv⟩ := (ExpandedFA.Sobolev.Lines.first_order_membership_iff u).mpr ⟨g, hg⟩
    have he (i : Fin d) : v.val (firstIndex i) = g i := by
      apply ExpandedFA.Sobolev.lpDistribution_injective
      rw [first_derivative_formula v i, hv]
      exact (hg i).symm
    refine ⟨⟨v, ?_⟩, hv⟩
    intro i
    rw [he i]
    exact hgf i

theorem difference_zero_dimension : Specs.ExpandedFA.PartIV.FractionalSobolev.ZeroDimension := by
  intro 𝕜 _ s p _ u
  have hz : differenceEnergy s p u = 0 := by
    have hzero : ∀ h : Fin 0 → ℝ, h = 0 := fun h => Subsingleton.elim h 0
    unfold differenceEnergy
    calc
      _ = ∫⁻ _ : Fin 0 → ℝ, (0 : ℝ≥0∞) := by
        apply lintegral_congr
        intro h
        rw [hzero h, differenceKernel_zero, zero_mul]
      _ = 0 := lintegral_zero
  exact ⟨hz, hz ▸ ENNReal.zero_lt_top⟩

theorem fractionalNorm_zero_dimension :
    Specs.ExpandedFA.PartIV.FractionalSobolev.ZeroDimensionNorm := by
  intro 𝕜 _ s p _ hp u
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  rw [fractionalNorm, (difference_zero_dimension 𝕜 s p u.val).1, ENNReal.toReal_zero,
    Real.zero_rpow (one_div_ne_zero (ENNReal.toReal_pos hp0 hp).ne'), add_zero]

section HigherFullNorm
open ExpandedFA.Distributions ExpandedFA.Sobolev
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

@[simp] theorem wholeLp_zero :
    wholeLp (0 : DomainLp 𝕜 (⊤ : Opens (Domain d)) p) = 0 :=
  wholeLpLI.map_zero
@[simp] theorem wholeLp_add (u v : DomainLp 𝕜 (⊤ : Opens (Domain d)) p) :
    wholeLp (u + v) = wholeLp u + wholeLp v :=
  wholeLpLI.map_add u v
@[simp] theorem wholeLp_smul (c : 𝕜) (u : DomainLp 𝕜 (⊤ : Opens (Domain d)) p) :
    wholeLp (c • u) = c • wholeLp u :=
  wholeLpLI.map_smul c u
@[simp] theorem norm_wholeLp (u : DomainLp 𝕜 (⊤ : Opens (Domain d)) p) :
    ‖wholeLp u‖ = ‖u‖ := wholeLpLI.norm_map u

theorem wholeLp_representative
    (u : DomainLp 𝕜 (⊤ : Opens (Domain d)) p) :
    wholeLp u =ᵐ[volume] u := by
  change Lp.compMeasurePreserving id _ u =ᵐ[volume] u
  exact Lp.coeFn_compMeasurePreserving u _

theorem wholeLp_injective : Function.Injective (wholeLp (𝕜 := 𝕜) (d := d) (p := p)) :=
  (wholeLpLI (𝕜 := 𝕜) (d := d) (p := p)).injective

variable (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)

include hp

theorem higher_finite_energy_zero :
    ∀ i : Fin d, differenceEnergy (s - 1) p
      (wholeLp ((0 : SobolevSpace 𝕜 d ⊤ 1 p).val (firstIndex i))) < ∞ := by
  intro i
  simpa using (finite_energy_zero (𝕜 := 𝕜) (d := d) (s - 1) p hp)

theorem higher_finite_energy_add (u v : HigherFractionalSpace 𝕜 d s p) :
    ∀ i : Fin d, differenceEnergy (s - 1) p
      (wholeLp ((u.val + v.val).val (firstIndex i))) < ∞ := by
  intro i
  simpa only [Submodule.coe_add, PiLp.add_apply, wholeLp_add] using (finite_energy_add (s - 1) p hp _ _ (u.property i) (v.property i))

theorem higher_finite_energy_smul (c : 𝕜) (u : HigherFractionalSpace 𝕜 d s p) :
    ∀ i : Fin d, differenceEnergy (s - 1) p
      (wholeLp ((c • u.val).val (firstIndex i))) < ∞ := by
  intro i
  simpa only [Submodule.coe_smul, PiLp.smul_apply, wholeLp_smul] using (finite_energy_smul (s - 1) p hp c _ (u.property i))

omit hp in
theorem higherFractionalNorm_nonneg (u : HigherFractionalSpace 𝕜 d s p) :
    0 ≤ higherFractionalNorm s p u := by
  exact add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun i _ => fractionalNorm_nonneg _ _ _)

theorem higherFractionalNorm_eq_zero_iff (u : HigherFractionalSpace 𝕜 d s p) :
    higherFractionalNorm s p u = 0 ↔ u.val = 0 := by
  constructor
  · intro h
    apply sobolev_underlying_injective 𝕜 d ⊤ 1 p
    apply norm_eq_zero.mp
    have hb : ‖u.val.val (zeroIndex d 1)‖ ≤ higherFractionalNorm s p u := by
      unfold higherFractionalNorm
      rw [norm_wholeLp]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => fractionalNorm_nonneg _ _ _)
    exact le_antisymm (h ▸ hb) (norm_nonneg _)
  · intro h
    unfold higherFractionalNorm
    have hz (i : Fin d) : fractionalNorm (s - 1) p
        ⟨wholeLp (u.val.val (firstIndex i)), u.property i⟩ = 0 := by
      apply (fractionalNorm_eq_zero_iff (s - 1) p hp _).mpr
      simp [h]
    simp only [hz, Finset.sum_const_zero, add_zero]
    simp [h]

set_option maxHeartbeats 1200000 in
theorem higherFractionalNorm_add_le (u v : HigherFractionalSpace 𝕜 d s p) :
    higherFractionalNorm s p ⟨u.val + v.val, higher_finite_energy_add s p hp u v⟩ ≤
      higherFractionalNorm s p u + higherFractionalNorm s p v := by
  unfold higherFractionalNorm
  simp only [Submodule.coe_add, PiLp.add_apply, wholeLp_add]
  have hsum : (∑ i : Fin d,
      fractionalNorm (s - 1) p ⟨wholeLp (u.val.val (firstIndex i)) +
        wholeLp (v.val.val (firstIndex i)),
        finite_energy_add (s - 1) p hp _ _ (u.property i) (v.property i)⟩) ≤
      ∑ i : Fin d, (fractionalNorm (s - 1) p
        ⟨wholeLp (u.val.val (firstIndex i)), u.property i⟩ +
      fractionalNorm (s - 1) p ⟨wholeLp (v.val.val (firstIndex i)), v.property i⟩) := by
    apply Finset.sum_le_sum
    intro i _
    exact fractionalNorm_add_le (𝕜 := 𝕜) (d := d) (s - 1) p hp
      ⟨wholeLp (u.val.val (firstIndex i)), u.property i⟩
      ⟨wholeLp (v.val.val (firstIndex i)), v.property i⟩
  rw [Finset.sum_add_distrib] at hsum
  linarith [norm_add_le (wholeLp (u.val.val (zeroIndex d 1)))
    (wholeLp (v.val.val (zeroIndex d 1)))]

set_option maxHeartbeats 1200000 in
theorem higherFractionalNorm_smul (c : 𝕜) (u : HigherFractionalSpace 𝕜 d s p) :
    higherFractionalNorm s p ⟨c • u.val, higher_finite_energy_smul s p hp c u⟩ =
      ‖c‖ * higherFractionalNorm s p u := by
  unfold higherFractionalNorm
  simp only [Submodule.coe_smul, PiLp.smul_apply, wholeLp_smul, norm_smul]
  have hs (i : Fin d) : fractionalNorm (s - 1) p
      ⟨c • wholeLp (u.val.val (firstIndex i)),
        finite_energy_smul (s - 1) p hp c _ (u.property i)⟩ =
      ‖c‖ * fractionalNorm (s - 1) p
        ⟨wholeLp (u.val.val (firstIndex i)), u.property i⟩ := by
    exact fractionalNorm_smul (𝕜 := 𝕜) (d := d) (s - 1) p hp c
      ⟨wholeLp (u.val.val (firstIndex i)), u.property i⟩
  simp_rw [hs]
  rw [← Finset.mul_sum, mul_add]

/-- First derivatives of finite fractional energy form a linear subspace
of the accepted first-order weak derivative graph. -/
def higherFiniteEnergySubmodule : Submodule 𝕜 (SobolevSpace 𝕜 d ⊤ 1 p) where
  carrier := {u | ∀ i : Fin d, differenceEnergy (s - 1) p
    (wholeLp (u.val (firstIndex i))) < ∞}
  zero_mem' := higher_finite_energy_zero s p hp
  add_mem' := fun hu hv => higher_finite_energy_add s p hp ⟨_, hu⟩ ⟨_, hv⟩
  smul_mem' := fun c _ hu => higher_finite_energy_smul s p hp c ⟨_, hu⟩

section HigherNormedStructure
variable [Fact (p ≠ ∞)]
omit hp

instance higherFractionalAddCommGroup : AddCommGroup (HigherFractionalSpace 𝕜 d s p) :=
  inferInstanceAs (AddCommGroup (higherFiniteEnergySubmodule (𝕜 := 𝕜) (d := d) s p Fact.out))

instance higherFractionalModule : Module 𝕜 (HigherFractionalSpace 𝕜 d s p) :=
  inferInstanceAs (Module 𝕜 (higherFiniteEnergySubmodule (𝕜 := 𝕜) (d := d) s p Fact.out))

private theorem higherFractionalNormCore : NormedSpace.Core 𝕜 (HigherFractionalSpace 𝕜 d s p) where
  norm_nonneg := higherFractionalNorm_nonneg s p
  norm_smul := fun c u => higherFractionalNorm_smul s p Fact.out c u
  norm_triangle := fun u v => higherFractionalNorm_add_le s p Fact.out u v
  norm_eq_zero_iff u := (higherFractionalNorm_eq_zero_iff s p Fact.out u).trans
    ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

instance higherFractionalNormedAddCommGroup : NormedAddCommGroup (HigherFractionalSpace 𝕜 d s p) :=
  NormedAddCommGroup.ofCore (higherFractionalNormCore s p)

/-- Use the full norm topology on the finite-energy subtype. -/
instance higherFractionalMetricSpace : MetricSpace (HigherFractionalSpace 𝕜 d s p) :=
  (higherFractionalNormedAddCommGroup s p).toMetricSpace

instance higherFractionalPseudoMetricSpace : PseudoMetricSpace (HigherFractionalSpace 𝕜 d s p) :=
  (higherFractionalNormedAddCommGroup s p).toMetricSpace.toPseudoMetricSpace

instance higherFractionalUniformSpace : UniformSpace (HigherFractionalSpace 𝕜 d s p) :=
  (higherFractionalNormedAddCommGroup s p).toMetricSpace.toPseudoMetricSpace.toUniformSpace

instance higherFractionalBornology : Bornology (HigherFractionalSpace 𝕜 d s p) :=
  (higherFractionalNormedAddCommGroup s p).toMetricSpace.toPseudoMetricSpace.toBornology

instance higherFractionalTopologicalSpace : TopologicalSpace (HigherFractionalSpace 𝕜 d s p) :=
  (higherFractionalNormedAddCommGroup s p).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

instance higherFractionalEDist : EDist (HigherFractionalSpace 𝕜 d s p) :=
  (higherFractionalNormedAddCommGroup s p).toMetricSpace.toPseudoMetricSpace.toEDist

instance higherFractionalPseudoEMetricSpace : PseudoEMetricSpace (HigherFractionalSpace 𝕜 d s p) :=
  (higherFractionalNormedAddCommGroup s p).toMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace

instance higherFractionalEMetricSpace : EMetricSpace (HigherFractionalSpace 𝕜 d s p) :=
  (higherFractionalNormedAddCommGroup s p).toMetricSpace.toEMetricSpace

instance higherFractionalNNDist : NNDist (HigherFractionalSpace 𝕜 d s p) :=
  (higherFractionalNormedAddCommGroup s p).toMetricSpace.toPseudoMetricSpace.toNNDist

instance higherFractionalNormedSpace : NormedSpace 𝕜 (HigherFractionalSpace 𝕜 d s p) :=
  NormedSpace.ofCore (higherFractionalNormCore s p)

end HigherNormedStructure


end HigherFullNorm

theorem higher_norm_formula : Specs.ExpandedFA.PartIV.FractionalSobolev.HigherNormFormula := by
  intro 𝕜 _ d s p _ u
  rfl

theorem higher_fractional_full_norm_axioms :
    Specs.ExpandedFA.PartIV.FractionalSobolev.HigherFullNormAxioms := by
  intro 𝕜 _ d s p _ hp
  refine ⟨higher_finite_energy_zero s p hp, ?_⟩
  intro u v
  exact ⟨higherFractionalNorm_nonneg s p u,
    higherFractionalNorm_eq_zero_iff s p hp u,
    ⟨higher_finite_energy_add s p hp u v, higherFractionalNorm_add_le s p hp u v⟩,
    fun c => ⟨higher_finite_energy_smul s p hp c u, higherFractionalNorm_smul s p hp c u⟩⟩

theorem higher_fractionalNorm_zero_dimension :
    Specs.ExpandedFA.PartIV.FractionalSobolev.HigherZeroDimensionNorm := by
  intro 𝕜 _ s p _ u
  simp [higherFractionalNorm]

end ExpandedFA.PartIV.FractionalSobolev


open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

namespace ExpandedFA.PartIV.FractionalSobolev.MultiplierEstimates

def radialMajorant (d : ℕ) (s q : ℝ) (r : ℝ) : ℝ :=
  if r < 1 then r ^ (-d + (1-s)*q) else r ^ (-d-s*q)

lemma radialMajorant_integrable (d : ℕ) (hd : 0 < d) (s q : ℝ)
    (hs0 : 0 < s) (hs1 : s < 1) (hq : 0 < q) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => radialMajorant d s q ‖x‖) := by
  have : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using hd)
  rw [integrable_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin d)))]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul]
  have hnear : IntegrableOn (fun r : ℝ => r ^ ((1-s)*q - 1)) (Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by nlinarith)
  have hfar : IntegrableOn (fun r : ℝ => r ^ (-s*q-1)) (Ici 1) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr
      (integrableOn_Ioi_rpow_of_lt (by nlinarith) zero_lt_one)
  have hnear' : IntegrableOn (fun r : ℝ => r ^ (d-1) * radialMajorant d s q r) (Ioo 0 1) := by
    apply hnear.congr_fun _ measurableSet_Ioo
    intro r hr
    dsimp only
    rw [radialMajorant, ite_eq_left hr.2, ← Real.rpow_natCast r (d-1), ← Real.rpow_add hr.1]
    congr 1
    have : (↑(d-1) : ℝ) = d - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [this]
    ring
  have hfar' : IntegrableOn (fun r : ℝ => r ^ (d-1) * radialMajorant d s q r) (Ici 1) := by
    apply hfar.congr_fun _ measurableSet_Ici
    intro r hr
    dsimp only
    rw [radialMajorant, ite_eq_right (not_lt.mpr hr), ← Real.rpow_natCast r (d-1),
      ← Real.rpow_add (lt_of_lt_of_le zero_lt_one hr)]
    congr 1
    have : (↑(d-1) : ℝ) = d - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [this]
    ring
  have hset : Ioo (0:ℝ) 1 ∪ Ici 1 = Ioi 0 := by
    ext r
    simp only [mem_union, mem_Ioo, mem_Ici, mem_Ioi]
    constructor
    · rintro (h | h) <;> linarith
    · intro h
      by_cases hr : r < 1
      · exact Or.inl ⟨h, hr⟩
      · exact Or.inr (le_of_not_gt hr)
  rw [← hset]
  exact hnear'.union hfar'

end ExpandedFA.PartIV.FractionalSobolev.MultiplierEstimates

namespace ExpandedFA.PartIV.FractionalSobolev
open ExpandedFA.PartIV.FractionalSobolev.MultiplierEstimates

def incrementCutoff {d : ℕ} (h : Fin d → ℝ) : ℝ := min (euclideanLength h) 1

lemma incrementCutoff_continuous {d : ℕ} : Continuous (@incrementCutoff d) :=
  euclideanLength_continuous.min continuous_const

lemma incrementCutoff_nonneg {d : ℕ} (h : Fin d → ℝ) : 0 ≤ incrementCutoff h :=
  le_min (norm_nonneg _) zero_le_one

lemma incrementCutoff_weight_le {d : ℕ} (s q : ℝ) (hq : 0 ≤ q) (h : Fin d → ℝ) :
    differenceKernel s (ENNReal.ofReal q) h * ‖incrementCutoff h‖ₑ ^ q ≤
      ENNReal.ofReal (radialMajorant d s q (euclideanLength h)) := by
  by_cases hh : h = 0
  · simp [hh]
  have hn : 0 < euclideanLength h := lt_of_le_of_ne (norm_nonneg _) (Ne.symm ((euclideanLength_eq_zero h).not.mpr hh))
  rw [differenceKernel, ite_eq_right hh, ENNReal.toReal_ofReal hq,
    Real.enorm_of_nonneg (incrementCutoff_nonneg h)]
  by_cases hr : euclideanLength h < 1
  · rw [incrementCutoff, min_eq_left hr.le, ← ENNReal.rpow_add _ _ (by positivity) (by finiteness)]
    have hexp : -(↑d + s*q) + q = -d + (1-s)*q := by ring
    rw [hexp, ENNReal.ofReal_rpow_of_pos hn]
    simp [radialMajorant, hr]
  · rw [incrementCutoff, min_eq_right (le_of_not_gt hr)]
    simp only [ENNReal.ofReal_one, ENNReal.one_rpow, mul_one]
    rw [ENNReal.ofReal_rpow_of_pos hn]
    have hexp : -(↑d + s*q) = -d-s*q := by ring
    simp [radialMajorant, hr, hexp]

lemma incrementCutoff_memLp {d : ℕ} (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞) :
    MemLp (@incrementCutoff d) p (differenceMeasure s p) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hp
    incrementCutoff_continuous.stronglyMeasurable.aestronglyMeasurable]
  rw [differenceMeasure, lintegral_withDensity_eq_lintegral_mul _ (differenceKernel_measurable s p)
    (incrementCutoff_continuous.enorm.measurable.pow_const _)]
  by_cases hd : 0 < d
  · have hi := (PiLp.volume_preserving_toLp (Fin d)).integrable_comp_of_integrable
      (radialMajorant_integrable d hd s p.toReal hs0 hs1 hpr)
    have hn : ∀ᵐ h : Fin d → ℝ ∂volume,
        0 ≤ radialMajorant d s p.toReal (euclideanLength h) := by
      filter_upwards with h
      unfold radialMajorant
      split <;> exact Real.rpow_nonneg (norm_nonneg _) _
    have hfin : (∫⁻ h : Fin d → ℝ,
        ENNReal.ofReal (radialMajorant d s p.toReal (euclideanLength h))) < ∞ :=
      (hasFiniteIntegral_iff_ofReal hn).mp hi.hasFiniteIntegral
    apply lt_of_le_of_lt (lintegral_mono fun h => ?_) hfin
    change differenceKernel s p h * ‖incrementCutoff h‖ₑ ^ p.toReal ≤ _
    convert incrementCutoff_weight_le s p.toReal hpr.le h using 1
    rw [ENNReal.ofReal_toReal hp]
  · have hdz : d = 0 := by omega
    subst d
    have hz (h : Fin 0 → ℝ) : h = 0 := Subsingleton.elim _ _
    have he : (∫⁻ h : Fin 0 → ℝ, differenceKernel s p h * ‖incrementCutoff h‖ₑ ^ p.toReal) = 0 := by
      calc
        _ = ∫⁻ _h : Fin 0 → ℝ, (0 : ℝ≥0∞) := by
          apply lintegral_congr
          intro h
          rw [hz h, differenceKernel_zero, zero_mul]
        _ = 0 := lintegral_zero
    change (∫⁻ h : Fin 0 → ℝ, differenceKernel s p h * ‖incrementCutoff h‖ₑ ^ p.toReal) < ∞
    rw [he]
    exact ENNReal.zero_lt_top

end ExpandedFA.PartIV.FractionalSobolev
namespace ExpandedFA.PartIV.FractionalSobolev

lemma euclideanLipschitz_continuous {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (a : (Fin d → ℝ) → 𝕜) (L : ℝ≥0)
    (hL : ∀ x y, ‖a x-a y‖ ≤ L * euclideanLength (x-y)) : Continuous a := by
  have h : LipschitzWith L (fun z : EuclideanSpace ℝ (Fin d) => a (WithLp.ofLp z)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm, euclideanLength, ← WithLp.ofLp_sub, WithLp.toLp_ofLp] using
      hL (WithLp.ofLp x) (WithLp.ofLp y)
  exact h.continuous.comp (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))

lemma bounded_mul_memLp {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (a : (Fin d → ℝ) → 𝕜)
    (ha : Continuous a) (M : ℝ) (hM : ∀ x, ‖a x‖ ≤ M)
    (u : Lp 𝕜 p (volume : Measure (Fin d → ℝ))) : MemLp (fun x => a x*u x) p volume := by
  apply MemLp.of_le_mul (Lp.memLp u)
    (ha.stronglyMeasurable.mul (Lp.stronglyMeasurable u)).aestronglyMeasurable
  filter_upwards with x
  simpa only [Pi.mul_apply, norm_mul] using mul_le_mul_of_nonneg_right (hM x) (norm_nonneg (u x))

lemma lpIncrement_representative {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : Lp 𝕜 p (volume : Measure (Fin d → ℝ)))
    (h : Fin d → ℝ) : lpIncrement p h u =ᵐ[volume] fun x => u (x+h)-u x := by
  filter_upwards [Lp.coeFn_sub
      (ExpandedFA.Distributions.LpTranslationContinuitySpec.LpTranslationValue p (-h) u) u,
      ExpandedFA.Distributions.lpTranslation_representative p (-h) u] with x hx htx
  change lpIncrement p h u x = _ - _ at hx
  rw [hx, htx]
  simp only [sub_neg_eq_add]

lemma bounded_lipschitz_difference {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (a : (Fin d → ℝ) → 𝕜) (M L : ℝ≥0)
    (hM : ∀ x, ‖a x‖ ≤ M)
    (hL : ∀ x y, ‖a x-a y‖ ≤ L * euclideanLength (x-y))
    (x h : Fin d → ℝ) :
    ‖a (x+h)-a x‖ ≤ max (L:ℝ) (2*M) * incrementCutoff h := by
  have hnear : ‖a (x+h)-a x‖ ≤ L * euclideanLength h := by
    simpa only [add_sub_cancel_left] using hL (x+h) x
  have hfar : ‖a (x+h)-a x‖ ≤ 2*M :=
    (norm_sub_le _ _).trans (by linarith [hM (x+h), hM x])
  unfold incrementCutoff
  by_cases hr : euclideanLength h ≤ 1
  · rw [min_eq_left hr]
    exact hnear.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · rw [min_eq_right (le_of_not_ge hr), mul_one]
    exact hfar.trans (le_max_right _ _)

lemma bounded_mul_increment_norm {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : (Fin d → ℝ) → 𝕜) (M L : ℝ≥0)
    (hM : ∀ x, ‖a x‖ ≤ M)
    (hL : ∀ x y, ‖a x-a y‖ ≤ L * euclideanLength (x-y))
    (u : Lp 𝕜 p (volume : Measure (Fin d → ℝ)))
    (v : Lp 𝕜 p (volume : Measure (Fin d → ℝ)))
    (hv : v =ᵐ[volume] fun x => a x*u x) (h : Fin d → ℝ) :
    ‖lpIncrement p h v‖ ≤ M * ‖lpIncrement p h u‖ +
      (max (L:ℝ) (2*M) * incrementCutoff h) * ‖u‖ := by
  have ha := euclideanLipschitz_continuous a L hL
  let f := fun x => a (x+h)*(u (x+h)-u x)
  let g := fun x => (a (x+h)-a x)*u x
  have hfmeas : AEStronglyMeasurable f volume :=
    ((ha.comp (continuous_id.add_const h)).stronglyMeasurable.mul
      (((Lp.stronglyMeasurable u).comp_measurable (measurable_id.add_const h)).sub
        (Lp.stronglyMeasurable u))).aestronglyMeasurable
  have hgmeas : AEStronglyMeasurable g volume :=
    (((ha.comp (continuous_id.add_const h)).sub ha).stronglyMeasurable.mul
      (Lp.stronglyMeasurable u)).aestronglyMeasurable
  have hfbd : ∀ᵐ x ∂volume, ‖f x‖ ≤ M * ‖lpIncrement p h u x‖ := by
    filter_upwards [lpIncrement_representative p u h] with x hx
    rw [hx]
    dsimp [f]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hM (x+h)) (norm_nonneg _)
  have hgbd : ∀ᵐ x ∂volume,
      ‖g x‖ ≤ (max (L:ℝ) (2*M)*incrementCutoff h)*‖u x‖ := by
    filter_upwards with x
    dsimp [g]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (bounded_lipschitz_difference a M L hM hL x h)
      (norm_nonneg _)
  have hf := MemLp.of_le_mul (Lp.memLp (lpIncrement p h u)) hfmeas hfbd
  have hg := MemLp.of_le_mul (Lp.memLp u) hgmeas hgbd
  have hfe : ‖hf.toLp f‖ ≤ M * ‖lpIncrement p h u‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hf.coeFn_toLp, hfbd] with x hx hbd
    rw [hx]
    exact hbd
  have hge : ‖hg.toLp g‖ ≤ (max (L:ℝ) (2*M)*incrementCutoff h)*‖u‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hg.coeFn_toLp, hgbd] with x hx hbd
    rw [hx]
    exact hbd
  have hvh := (measurePreserving_add_right (volume : Measure (Fin d → ℝ)) h).quasiMeasurePreserving.ae_eq_comp hv
  have he : lpIncrement p h v = hf.toLp f + hg.toLp g := by
    apply Lp.ext
    filter_upwards [lpIncrement_representative p v h, hv, hvh,
      Lp.coeFn_add (hf.toLp f) (hg.toLp g), hf.coeFn_toLp, hg.coeFn_toLp] with x hx hx0 hxh hxa hxf hxg
    rw [hx, hxa]
    simp only [Pi.add_apply]
    dsimp only [Function.comp_apply] at hxh
    rw [hxf, hxg, hx0, hxh]
    dsimp [f,g]
    ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hfe hge)

end ExpandedFA.PartIV.FractionalSobolev
namespace ExpandedFA.PartIV.FractionalSobolev

def multiplierBound {d : ℕ} (s : ℝ) (p : ℝ≥0∞) (M L : ℝ≥0) : ℝ :=
  M + max (L:ℝ) (2*M) * (eLpNorm (@incrementCutoff d) p (differenceMeasure s p)).toReal

lemma bounded_mul_finite_energy_norm {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞)
    (a : (Fin d → ℝ) → 𝕜) (M L : ℝ≥0)
    (hM : ∀ x, ‖a x‖ ≤ M)
    (hL : ∀ x y, ‖a x-a y‖ ≤ L * euclideanLength (x-y))
    (u : FractionalSpace 𝕜 d s p)
    (v : Lp 𝕜 p (volume : Measure (Fin d → ℝ)))
    (hv : v =ᵐ[volume] fun x => a x*u.val x) :
    ∃ hfin : differenceEnergy s p v < ∞,
      fractionalNorm s p ⟨v,hfin⟩ ≤ multiplierBound (d:=d) s p M L * fractionalNorm s p u := by
  let B : ℝ := max (L:ℝ) (2*M)
  have hB : 0 ≤ B := le_trans L.coe_nonneg (le_max_left _ _)
  have hUi := (finite_energy_iff_memLp s p hp u.val).mp u.property
  have hq := incrementCutoff_memLp (d:=d) s p hs0 hs1 hp
  let F1 := fun h => (M:ℝ) * ‖lpIncrement p h u.val‖
  let F2 := fun h : Fin d → ℝ => (B*‖u.val‖) * incrementCutoff h
  have hF1 : MemLp F1 p (differenceMeasure s p) := hUi.norm.const_mul M
  have hF2 : MemLp F2 p (differenceMeasure s p) := hq.const_mul (B*‖u.val‖)
  have hbound : ∀ h, ‖lpIncrement p h v‖ ≤ ‖(F1+F2) h‖ := by
    intro h
    have hb := bounded_mul_increment_norm p a M L hM hL u.val v hv h
    rw [Real.norm_of_nonneg]
    · dsimp [F1,F2,B]
      convert hb using 1
      ring
    · dsimp [F1,F2]
      exact add_nonneg (mul_nonneg M.coe_nonneg (norm_nonneg _))
        (mul_nonneg (mul_nonneg hB (norm_nonneg _)) (incrementCutoff_nonneg h))
  have hVi : MemLp (fun h => lpIncrement p h v) p (differenceMeasure s p) :=
    (hF1.add hF2).of_le (lpIncrement_continuous p hp v).stronglyMeasurable.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  have hfin := (finite_energy_iff_memLp s p hp v).mpr hVi
  refine ⟨hfin, ?_⟩
  have hsemi : (eLpNorm (fun h => lpIncrement p h v) p (differenceMeasure s p)).toReal ≤
      M * (eLpNorm (fun h => lpIncrement p h u.val) p (differenceMeasure s p)).toReal +
        (B*‖u.val‖) * (eLpNorm (@incrementCutoff d) p (differenceMeasure s p)).toReal := by
    have hle : eLpNorm (fun h => lpIncrement p h v) p (differenceMeasure s p) ≤
        eLpNorm F1 p (differenceMeasure s p) + eLpNorm F2 p (differenceMeasure s p) :=
      (eLpNorm_mono_ae (lpIncrement_continuous p hp v).stronglyMeasurable.aestronglyMeasurable
        (Filter.Eventually.of_forall hbound)).trans (eLpNorm_add_le (Fact.out : 1≤p))
    have hle' := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hF1.ne,hF2.ne⟩) hle
    rw [ENNReal.toReal_add hF1.ne hF2.ne] at hle'
    have h1 : eLpNorm F1 p (differenceMeasure s p) =
        ‖(M:ℝ)‖ₑ * eLpNorm (fun h => lpIncrement p h u.val) p (differenceMeasure s p) := by
      dsimp [F1]
      convert eLpNorm_const_smul (M:ℝ) (fun h => ‖lpIncrement p h u.val‖) p (differenceMeasure s p) using 1
      rw [eLpNorm_norm _ hUi.aestronglyMeasurable]
    have h2 : eLpNorm F2 p (differenceMeasure s p) =
        ‖B*‖u.val‖‖ₑ * eLpNorm (@incrementCutoff d) p (differenceMeasure s p) := by
      exact eLpNorm_const_smul (B*‖u.val‖) (@incrementCutoff d) p (differenceMeasure s p)
    rw [h1,h2, ENNReal.toReal_mul, ENNReal.toReal_mul, toReal_enorm, toReal_enorm,
      Real.norm_of_nonneg M.coe_nonneg, Real.norm_of_nonneg (mul_nonneg hB (norm_nonneg _))] at hle'
    exact hle'
  have hvnorm : ‖v‖ ≤ M*‖u.val‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hv] with x hx
    rw [hx,norm_mul]
    exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
  rw [fractionalNorm_eq_weightedLp s p hp, fractionalNorm_eq_weightedLp s p hp]
  unfold multiplierBound
  dsimp only
  change ‖v‖ + _ ≤ ((M:ℝ) + B * _) * (‖u.val‖ + _)
  have hD : 0 ≤ (eLpNorm (@incrementCutoff d) p (differenceMeasure s p)).toReal := ENNReal.toReal_nonneg
  have hE : 0 ≤ (eLpNorm (fun h => lpIncrement p h u.val) p (differenceMeasure s p)).toReal := ENNReal.toReal_nonneg
  nlinarith [mul_nonneg (mul_nonneg hB hD) hE]

end ExpandedFA.PartIV.FractionalSobolev

namespace ExpandedFA.PartIV.FractionalSobolev

def lpMultiply {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : (Fin d → ℝ) → 𝕜) (M L : ℝ≥0) (hM : ∀ x, ‖a x‖ ≤ M)
    (hL : ∀ x y, ‖a x-a y‖ ≤ L * euclideanLength (x-y))
    (u : Lp 𝕜 p (volume : Measure (Fin d → ℝ))) : Lp 𝕜 p (volume : Measure (Fin d → ℝ)) :=
  (bounded_mul_memLp a (euclideanLipschitz_continuous a L hL) M hM u).toLp (fun x => a x*u x)

lemma lpMultiply_representative {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : (Fin d → ℝ) → 𝕜) (M L : ℝ≥0) (hM : ∀ x, ‖a x‖ ≤ M)
    (hL : ∀ x y, ‖a x-a y‖ ≤ L * euclideanLength (x-y))
    (u : Lp 𝕜 p (volume : Measure (Fin d → ℝ))) :
    lpMultiply p a M L hM hL u =ᵐ[volume] fun x => a x*u x :=
  MemLp.coeFn_toLp _

def fractionalMultiply {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞)
    (a : (Fin d → ℝ) → 𝕜) (M L : ℝ≥0) (hM : ∀ x, ‖a x‖ ≤ M)
    (hL : ∀ x y, ‖a x-a y‖ ≤ L * euclideanLength (x-y))
    (u : FractionalSpace 𝕜 d s p) : FractionalSpace 𝕜 d s p :=
  ⟨lpMultiply p a M L hM hL u.val,
    (bounded_mul_finite_energy_norm s p hs0 hs1 hp a M L hM hL u _
      (lpMultiply_representative p a M L hM hL u.val)).choose⟩

lemma fractionalMultiply_representative {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞)
    (a : (Fin d → ℝ) → 𝕜) (M L : ℝ≥0) (hM : ∀ x, ‖a x‖ ≤ M)
    (hL : ∀ x y, ‖a x-a y‖ ≤ L * euclideanLength (x-y))
    (u : FractionalSpace 𝕜 d s p) :
    (fractionalMultiply s p hs0 hs1 hp a M L hM hL u).val =ᵐ[volume] fun x => a x*u.val x :=
  lpMultiply_representative p a M L hM hL u.val

lemma fractionalMultiply_norm_le {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞)
    (a : (Fin d → ℝ) → 𝕜) (M L : ℝ≥0) (hM : ∀ x, ‖a x‖ ≤ M)
    (hL : ∀ x y, ‖a x-a y‖ ≤ L * euclideanLength (x-y))
    (u : FractionalSpace 𝕜 d s p) :
    fractionalNorm s p (fractionalMultiply s p hs0 hs1 hp a M L hM hL u) ≤
      multiplierBound (d:=d) s p M L * fractionalNorm s p u :=
  (bounded_mul_finite_energy_norm s p hs0 hs1 hp a M L hM hL u _
      (lpMultiply_representative p a M L hM hL u.val)).choose_spec

section ContinuousMultiplier
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (s : ℝ) (p : ℝ≥0∞)
  [Fact (1 ≤ p)] [Fact (p ≠ ∞)] (hs0 : 0 < s) (hs1 : s < 1)
  (a : (Fin d → ℝ) → 𝕜) (M L : ℝ≥0) (hM : ∀ x, ‖a x‖ ≤ M)
  (hL : ∀ x y, ‖a x-a y‖ ≤ L * euclideanLength (x-y))

def multiplierLinearMap : FractionalSpace 𝕜 d s p →ₗ[𝕜] FractionalSpace 𝕜 d s p where
  toFun := fractionalMultiply s p hs0 hs1 Fact.out a M L hM hL
  map_add' u v := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [fractionalMultiply_representative s p hs0 hs1 Fact.out a M L hM hL (u+v),
      fractionalMultiply_representative s p hs0 hs1 Fact.out a M L hM hL u,
      fractionalMultiply_representative s p hs0 hs1 Fact.out a M L hM hL v,
      Lp.coeFn_add u.val v.val,
      Lp.coeFn_add (fractionalMultiply s p hs0 hs1 Fact.out a M L hM hL u).val
        (fractionalMultiply s p hs0 hs1 Fact.out a M L hM hL v).val] with x hx huv hvv hadd hmuladd
    change (fractionalMultiply s p hs0 hs1 Fact.out a M L hM hL (u+v)).val x = _
    rw [hx]
    change a x * (u.val+v.val) x = _
    rw [hadd]
    change _ = ((fractionalMultiply s p hs0 hs1 Fact.out a M L hM hL u).val +
      (fractionalMultiply s p hs0 hs1 Fact.out a M L hM hL v).val) x
    rw [hmuladd]
    simp only [Pi.add_apply]
    rw [huv,hvv]
    ring
  map_smul' c u := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [fractionalMultiply_representative s p hs0 hs1 Fact.out a M L hM hL (c • u),
      fractionalMultiply_representative s p hs0 hs1 Fact.out a M L hM hL u,
      Lp.coeFn_smul c u.val,
      Lp.coeFn_smul c (fractionalMultiply s p hs0 hs1 Fact.out a M L hM hL u).val]
      with x hx hu hsmul hmulsmul
    change (fractionalMultiply s p hs0 hs1 Fact.out a M L hM hL (c • u)).val x = _
    rw [hx]
    change a x * (c • u.val) x = _
    rw [hsmul]
    change _ = (c • (fractionalMultiply s p hs0 hs1 Fact.out a M L hM hL u).val) x
    rw [hmulsmul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hu]
    ring

def boundedLipschitzMultiplier : FractionalSpace 𝕜 d s p →L[𝕜] FractionalSpace 𝕜 d s p :=
  (multiplierLinearMap s p hs0 hs1 a M L hM hL).mkContinuous
    (multiplierBound (d:=d) s p M L)
    (fractionalMultiply_norm_le s p hs0 hs1 Fact.out a M L hM hL)

lemma boundedLipschitzMultiplier_representative (u : FractionalSpace 𝕜 d s p) :
    (boundedLipschitzMultiplier s p hs0 hs1 a M L hM hL u).val =ᵐ[volume]
      fun x => a x*u.val x :=
  fractionalMultiply_representative s p hs0 hs1 Fact.out a M L hM hL u

lemma boundedLipschitzMultiplier_norm_le (u : FractionalSpace 𝕜 d s p) :
    ‖boundedLipschitzMultiplier s p hs0 hs1 a M L hM hL u‖ ≤
      multiplierBound (d:=d) s p M L * ‖u‖ :=
  fractionalMultiply_norm_le s p hs0 hs1 Fact.out a M L hM hL u

end ContinuousMultiplier

lemma multiplierBound_nonneg {d : ℕ} (s : ℝ) (p : ℝ≥0∞) (M L : ℝ≥0) :
    0 ≤ multiplierBound (d:=d) s p M L := by
  unfold multiplierBound
  exact add_nonneg M.coe_nonneg
    (mul_nonneg (le_trans L.coe_nonneg (le_max_left _ _)) ENNReal.toReal_nonneg)

/-- The bound depends only on dimension, order, exponent, sup bound and
Lipschitz bound. In particular, the same constant works over both scalar fields
and for every multiplier with those two bounds. -/
theorem bounded_lipschitz_multiplication (d : ℕ) (s : ℝ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞) (M L : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (𝕜 : Type) [RCLike 𝕜] (a : (Fin d → ℝ) → 𝕜),
      (∀ x, ‖a x‖ ≤ M) →
      (∀ x y, ‖a x-a y‖ ≤ L * euclideanLength (x-y)) →
      ∀ u : FractionalSpace 𝕜 d s p, ∃ v : FractionalSpace 𝕜 d s p,
        v.val =ᵐ[volume] (fun x => a x*u.val x) ∧
        fractionalNorm s p v ≤ C * fractionalNorm s p u := by
  refine ⟨multiplierBound (d:=d) s p M L, multiplierBound_nonneg s p M L, ?_⟩
  intro 𝕜 _ a hM hL u
  exact ⟨fractionalMultiply s p hs0 hs1 hp a M L hM hL u,
    fractionalMultiply_representative s p hs0 hs1 hp a M L hM hL u,
    fractionalMultiply_norm_le s p hs0 hs1 hp a M L hM hL u⟩

end ExpandedFA.PartIV.FractionalSobolev

namespace ExpandedFA.PartIV.FractionalSobolev

lemma norm_le_euclideanLength {d : ℕ} (h : Fin d → ℝ) : ‖h‖ ≤ euclideanLength h := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact PiLp.norm_apply_le (WithLp.toLp 2 h) i

lemma bounded_fderiv_euclideanLipschitz {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (a : (Fin d → ℝ) → 𝕜) (L : ℝ≥0) (ha : Differentiable ℝ a)
    (hD : ∀ x, ‖fderiv ℝ a x‖₊ ≤ L) :
    ∀ x y, ‖a x-a y‖ ≤ L * euclideanLength (x-y) := by
  intro x y
  exact ((lipschitzWith_of_nnnorm_fderiv_le ha hD).norm_sub_le x y).trans
    (mul_le_mul_of_nonneg_left (norm_le_euclideanLength (x-y)) L.coe_nonneg)

/-- Smooth bounded multipliers with a bounded first derivative are bounded on
all finite-exponent order-s spaces. The derivative bound is retained. -/
theorem smooth_bounded_multiplication (d : ℕ) (s : ℝ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞) (M L : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (𝕜 : Type) [RCLike 𝕜] (a : (Fin d → ℝ) → 𝕜),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → (∀ x, ‖a x‖ ≤ M) → (∀ x, ‖fderiv ℝ a x‖₊ ≤ L) →
      ∀ u : FractionalSpace 𝕜 d s p, ∃ v : FractionalSpace 𝕜 d s p,
        v.val =ᵐ[volume] (fun x => a x*u.val x) ∧
        fractionalNorm s p v ≤ C * fractionalNorm s p u := by
  obtain ⟨C,hC,hmult⟩ := bounded_lipschitz_multiplication d s p hs0 hs1 hp M L
  refine ⟨C,hC,?_⟩
  intro 𝕜 _ a ha hM hD
  exact hmult 𝕜 a hM (bounded_fderiv_euclideanLipschitz a L (ha.differentiable (by simp)) hD)

end ExpandedFA.PartIV.FractionalSobolev


open MeasureTheory Set
open scoped ENNReal NNReal
namespace ExpandedFA.PartIV.FractionalSobolev.Transport

 theorem volume_image_le {d : ℕ} {K : ℝ≥0} {f : (Fin d → ℝ) → (Fin d → ℝ)}
    (hf : LipschitzWith K f) (s : Set (Fin d → ℝ)) :
    volume (f '' s) ≤ (K : ℝ≥0∞)^d * volume s := by
  simpa only [← MeasureTheory.hausdorffMeasure_pi_real, Fintype.card_fin,
    ENNReal.rpow_natCast] using hf.hausdorffMeasure_image_le (d := (d : ℝ)) (Nat.cast_nonneg d) s

 theorem map_volume_le {d : ℕ} (f : (Fin d → ℝ) ≃ₜ (Fin d → ℝ))
    {K : ℝ≥0} (hf : LipschitzWith K f.symm) :
    Measure.map f volume ≤ (K : ℝ≥0∞)^d • volume := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.map_apply f.continuous.measurable hs, Measure.smul_apply,
    smul_eq_mul]
  have he : f ⁻¹' s = f.symm '' s := by
    ext x
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro hx
      exact ⟨f x, hx, f.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [he]
  exact volume_image_le hf s

 theorem lintegral_comp_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} (f : α ≃ᵐ β)
    {C : ℝ≥0∞} (hC : Measure.map f μ ≤ C • ν) (g : β → ℝ≥0∞) :
    ∫⁻ x, g (f x) ∂μ ≤ C * ∫⁻ y, g y ∂ν := by
  rw [← lintegral_map_equiv]
  calc
    _ ≤ ∫⁻ y, g y ∂C • ν := lintegral_mono' hC le_rfl
    _ = _ := by simp only [lintegral_smul_measure, smul_eq_mul]

 theorem double_lintegral_comp_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} (f : α ≃ᵐ β)
    {C : ℝ≥0∞} (hC : Measure.map f μ ≤ C • ν) (hCtop : C ≠ ∞) (g : β → β → ℝ≥0∞) :
    ∫⁻ x, ∫⁻ y, g (f x) (f y) ∂μ ∂μ ≤ C^2 * ∫⁻ x, ∫⁻ y, g x y ∂ν ∂ν := by
  calc
    _ ≤ ∫⁻ x, C * ∫⁻ y, g (f x) y ∂ν ∂μ :=
      lintegral_mono fun x => lintegral_comp_le f hC (g (f x))
    _ = C * ∫⁻ x, ∫⁻ y, g (f x) y ∂ν ∂μ := by rw [lintegral_const_mul' _ _ hCtop]
    _ ≤ C * (C * ∫⁻ x, ∫⁻ y, g x y ∂ν ∂ν) :=
      by gcongr; exact lintegral_comp_le f hC (fun x => ∫⁻ y, g x y ∂ν)
    _ = _ := by rw [pow_two, mul_assoc]

end ExpandedFA.PartIV.FractionalSobolev.Transport
namespace ExpandedFA.PartIV.FractionalSobolev.Transport
open ExpandedFA.PartIV.FractionalSobolev
 theorem reciprocal_rpow_comparison (a b L q : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hL : 0 < L) (hq : 0 ≤ q) (hab : b ≤ L * a) :
    ENNReal.ofReal a ^ (-q) ≤ ENNReal.ofReal L ^ q * ENNReal.ofReal b ^ (-q) := by
  simp only [ENNReal.ofReal_rpow_of_pos ha, ENNReal.ofReal_rpow_of_pos hb,
    ENNReal.ofReal_rpow_of_pos hL]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hL.le _)]
  apply ENNReal.ofReal_le_ofReal
  have hdiv : b / L ≤ a := (div_le_iff₀ hL).mpr (by simpa only [mul_comm] using hab)
  have hr := Real.rpow_le_rpow_of_nonpos (div_pos hb hL) hdiv (neg_nonpos.mpr hq)
  have he : (b / L) ^ (-q) = L ^ q * b ^ (-q) := by
    rw [Real.div_rpow hb.le hL.le, Real.rpow_neg hL.le, div_inv_eq_mul, mul_comm]
  exact hr.trans_eq he

 theorem kernel_comparison {d : ℕ} (f : (Fin d → ℝ) → (Fin d → ℝ))
    (hinj : Function.Injective f) (L : ℝ) (hL : 0 < L) (s : ℝ) (p : ℝ≥0∞)
    (hq : 0 ≤ (d : ℝ) + s * p.toReal)
    (hLip : ∀ x y, euclideanLength (f y - f x) ≤ L * euclideanLength (y-x))
    (x y : Fin d → ℝ) :
    differenceKernel s p (y-x) ≤ ENNReal.ofReal L ^ ((d : ℝ) + s * p.toReal) *
      differenceKernel s p (f y - f x) := by
  by_cases hxy : y=x
  · subst y
    simp [differenceKernel]
  · have ha : 0 < euclideanLength (y-x) := by
      apply norm_pos_iff.mpr
      simpa only [ne_eq, WithLp.toLp_eq_zero, sub_eq_zero] using hxy
    have hfxy : f y - f x ≠ 0 := by simpa only [sub_ne_zero] using hinj.ne hxy
    have hb : 0 < euclideanLength (f y-f x) := by
      apply norm_pos_iff.mpr
      simpa only [ne_eq, WithLp.toLp_eq_zero] using hfxy
    simp only [differenceKernel, ite_eq_right (sub_ne_zero.mpr hxy), ite_eq_right hfxy]
    exact reciprocal_rpow_comparison _ _ _ _ ha hb hL hq (hLip x y)
end ExpandedFA.PartIV.FractionalSobolev.Transport
namespace ExpandedFA.PartIV.FractionalSobolev.Transport
open ExpandedFA.PartIV.FractionalSobolev
 theorem exists_euclidean_lipschitz_constant {d : ℕ} {K : ℝ≥0}
    {f : (Fin d → ℝ) → (Fin d → ℝ)} (hf : LipschitzWith K f) :
    ∃ L : ℝ, 0 < L ∧ ∀ x y, euclideanLength (f y-f x) ≤ L * euclideanLength (y-x) := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)
  have hE := e.symm.toContinuousLinearMap.lipschitzWith.comp (hf.comp e.toContinuousLinearMap.lipschitzWith)
  let c : ℝ≥0 := ‖e.symm.toContinuousLinearMap‖₊ * (K * ‖e.toContinuousLinearMap‖₊)
  refine ⟨max 1 (c : ℝ), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x y
  have h := hE.dist_le_mul (WithLp.toLp 2 y) (WithLp.toLp 2 x)
  have hc : euclideanLength (f y-f x) ≤ (c : ℝ) * euclideanLength (y-x) := by
    change ‖WithLp.toLp 2 (f y) - WithLp.toLp 2 (f x)‖ ≤
      (c : ℝ) * ‖WithLp.toLp 2 y - WithLp.toLp 2 x‖ at h
    simpa only [← WithLp.toLp_sub, euclideanLength] using h
  exact hc.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

 def rawDoubleEnergy {𝕜 : Type*} [RCLike 𝕜] {d : ℕ} (s : ℝ) (p : ℝ≥0∞)
    (u : (Fin d → ℝ) → 𝕜) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, differenceKernel s p (y-x) * ‖u y-u x‖ₑ ^ p.toReal

 theorem rawDoubleEnergy_comp_le {𝕜 : Type*} [RCLike 𝕜] {d : ℕ}
    (f : (Fin d → ℝ) ≃ₜ (Fin d → ℝ)) (s : ℝ) (p : ℝ≥0∞)
    {C D : ℝ≥0∞} (hC : C ≠ ∞) (hD : D ≠ ∞)
    (hvol : Measure.map f volume ≤ C • volume)
    (hkernel : ∀ x y, differenceKernel s p (y-x) ≤ D * differenceKernel s p (f y-f x))
    (u : (Fin d → ℝ) → 𝕜) :
    rawDoubleEnergy s p (u ∘ f) ≤ (D * C^2) * rawDoubleEnergy s p u := by
  unfold rawDoubleEnergy
  calc
    _ ≤ ∫⁻ x, ∫⁻ y, D * (differenceKernel s p (f y-f x) * ‖u (f y)-u (f x)‖ₑ ^ p.toReal) := by
      apply lintegral_mono
      intro x
      apply lintegral_mono
      intro y
      dsimp only [Function.comp_apply]
      rw [← mul_assoc]
      gcongr
      exact hkernel x y
    _ = D * ∫⁻ x, ∫⁻ y, differenceKernel s p (f y-f x) * ‖u (f y)-u (f x)‖ₑ ^ p.toReal := by
      simp_rw [lintegral_const_mul' _ _ hD]
    _ ≤ D * (C^2 * ∫⁻ x, ∫⁻ y, differenceKernel s p (y-x) * ‖u y-u x‖ₑ ^ p.toReal) := by
      gcongr
      exact double_lintegral_comp_le f.toMeasurableEquiv hvol hC
        (fun x y => differenceKernel s p (y-x) * ‖u y-u x‖ₑ ^ p.toReal)
    _ = _ := by rw [mul_assoc]
end ExpandedFA.PartIV.FractionalSobolev.Transport
namespace ExpandedFA.PartIV.FractionalSobolev.Transport
open ExpandedFA.PartIV.FractionalSobolev
 theorem rawDoubleEnergy_congr {𝕜 : Type*} [RCLike 𝕜] {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) {u v : (Fin d → ℝ) → 𝕜} (huv : u =ᵐ[volume] v) :
    rawDoubleEnergy s p u = rawDoubleEnergy s p v := by
  apply lintegral_congr_ae
  filter_upwards [huv] with x hx
  apply lintegral_congr_ae
  filter_upwards [huv] with y hy
  simp only [hx, hy]

 theorem memLp_comp {𝕜 : Type*} [RCLike 𝕜] {d : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : (Fin d → ℝ) ≃ₜ (Fin d → ℝ)) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hvol : Measure.map f volume ≤ C • volume) (u : Lp 𝕜 p (volume : Measure (Fin d → ℝ))) :
    MemLp (u ∘ f) p volume :=
  ((Lp.memLp u).of_measure_le_smul hC hvol).comp_of_map f.continuous.measurable.aemeasurable

 def pullbackLp {𝕜 : Type*} [RCLike 𝕜] {d : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : (Fin d → ℝ) ≃ₜ (Fin d → ℝ)) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hvol : Measure.map f volume ≤ C • volume) (u : Lp 𝕜 p (volume : Measure (Fin d → ℝ))) :
    Lp 𝕜 p (volume : Measure (Fin d → ℝ)) :=
  (memLp_comp p f hC hvol u).toLp (u ∘ f)

 theorem pullbackLp_ae_eq {𝕜 : Type*} [RCLike 𝕜] {d : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : (Fin d → ℝ) ≃ₜ (Fin d → ℝ)) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hvol : Measure.map f volume ≤ C • volume) (u : Lp 𝕜 p (volume : Measure (Fin d → ℝ))) :
    pullbackLp p f hC hvol u =ᵐ[volume] u ∘ f :=
  (memLp_comp p f hC hvol u).coeFn_toLp

 theorem energy_pullbackLp_le {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f : (Fin d → ℝ) ≃ₜ (Fin d → ℝ)) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {C D : ℝ≥0∞} (hC : C ≠ ∞) (hD : D ≠ ∞)
    (hvol : Measure.map f volume ≤ C • volume)
    (hkernel : ∀ x y, differenceKernel s p (y-x) ≤ D * differenceKernel s p (f y-f x))
    (u : Lp 𝕜 p (volume : Measure (Fin d → ℝ))) :
    differenceEnergy s p (pullbackLp p f hC hvol u) ≤ D * C^2 * differenceEnergy s p u := by
  rw [difference_energy_double_integral 𝕜 d s p,
    difference_energy_double_integral 𝕜 d s p]
  change rawDoubleEnergy s p _ ≤ _ * rawDoubleEnergy s p _
  rw [rawDoubleEnergy_congr s p (pullbackLp_ae_eq p f hC hvol u)]
  exact rawDoubleEnergy_comp_le f s p hC hD hvol hkernel u

 theorem enorm_pullbackLp_le {𝕜 : Type*} [RCLike 𝕜] {d : ℕ}
    (f : (Fin d → ℝ) ≃ₜ (Fin d → ℝ)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hvol : Measure.map f volume ≤ C • volume)
    (u : Lp 𝕜 p (volume : Measure (Fin d → ℝ))) :
    ‖pullbackLp p f hC hvol u‖ₑ ≤ C ^ (1 / p).toReal * ‖u‖ₑ := by
  simp only [Lp.enorm_def]
  rw [eLpNorm_congr_ae (pullbackLp_ae_eq p f hC hvol u),
    ← eLpNorm_map_measure (Lp.stronglyMeasurable u).aestronglyMeasurable
      f.continuous.measurable.aemeasurable]
  exact eLpNorm_le_of_measure_le_smul hvol

 theorem norm_pullbackLp_le {𝕜 : Type*} [RCLike 𝕜] {d : ℕ}
    (f : (Fin d → ℝ) ≃ₜ (Fin d → ℝ)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hvol : Measure.map f volume ≤ C • volume)
    (u : Lp 𝕜 p (volume : Measure (Fin d → ℝ))) :
    ‖pullbackLp p f hC hvol u‖ ≤ C.toReal ^ (1 / p.toReal) * ‖u‖ := by
  have h := enorm_pullbackLp_le f p hC hvol u
  have hfin : C ^ (1 / p).toReal * ‖u‖ₑ ≠ ∞ := by
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) hC) enorm_ne_top
  have hr := ENNReal.toReal_mono hfin h
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, toReal_enorm,
    ENNReal.toReal_div, ENNReal.toReal_one, one_div, ENNReal.toReal_inv] using hr
end ExpandedFA.PartIV.FractionalSobolev.Transport
namespace ExpandedFA.PartIV.FractionalSobolev.Transport
 theorem volume_image_le_on {d : ℕ} {K : ℝ≥0} {f : (Fin d → ℝ) → (Fin d → ℝ)}
    {s : Set (Fin d → ℝ)} (hf : LipschitzOnWith K f s) :
    volume (f '' s) ≤ (K : ℝ≥0∞)^d * volume s := by
  simpa only [← MeasureTheory.hausdorffMeasure_pi_real, Fintype.card_fin,
    ENNReal.rpow_natCast] using hf.hausdorffMeasure_image_le (d := (d : ℝ)) (Nat.cast_nonneg d)

 theorem map_restrict_volume_le {d : ℕ} {K : ℝ≥0}
    {f g : (Fin d → ℝ) → (Fin d → ℝ)} {U V : Set (Fin d → ℝ)}
    (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hf : ContinuousOn f U) (hg : LipschitzOnWith K g V)
    (hfg : ∀ x ∈ U, f x ∈ V ∧ g (f x) = x)
    (hgf : ∀ y ∈ V, g y ∈ U ∧ f (g y) = y) :
    Measure.map f (volume.restrict U) ≤ (K : ℝ≥0∞)^d • volume.restrict V := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.map_apply_of_aemeasurable (hf.aemeasurable hU) hs,
    Measure.restrict_apply' hU, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply' hV]
  have he : f ⁻¹' s ∩ U = g '' (s ∩ V) := by
    ext x
    constructor
    · rintro ⟨hx, hxu⟩
      exact ⟨f x, ⟨hx, (hfg x hxu).1⟩, (hfg x hxu).2⟩
    · rintro ⟨y, ⟨hys, hyv⟩, rfl⟩
      exact ⟨by simpa only [Set.mem_preimage, (hgf y hyv).2] using hys, (hgf y hyv).1⟩
  rw [he]
  exact volume_image_le_on (hg.mono inter_subset_right)
end ExpandedFA.PartIV.FractionalSobolev.Transport
namespace ExpandedFA.PartIV.FractionalSobolev.Transport
open ExpandedFA.PartIV.FractionalSobolev
 theorem finite_energy_pullbackLp {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f : (Fin d → ℝ) ≃ₜ (Fin d → ℝ)) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {C D : ℝ≥0∞} (hC : C ≠ ∞) (hD : D ≠ ∞)
    (hvol : Measure.map f volume ≤ C • volume)
    (hkernel : ∀ x y, differenceKernel s p (y-x) ≤ D * differenceKernel s p (f y-f x))
    (u : FractionalSpace 𝕜 d s p) :
    differenceEnergy s p (pullbackLp p f hC hvol u.val) < ∞ :=
  lt_of_le_of_lt (energy_pullbackLp_le f s p hC hD hvol hkernel u.val)
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top hD.lt_top (ENNReal.pow_lt_top hC.lt_top)) u.property)

 def pullbackFractional {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f : (Fin d → ℝ) ≃ₜ (Fin d → ℝ)) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {C D : ℝ≥0∞} (hC : C ≠ ∞) (hD : D ≠ ∞)
    (hvol : Measure.map f volume ≤ C • volume)
    (hkernel : ∀ x y, differenceKernel s p (y-x) ≤ D * differenceKernel s p (f y-f x))
    (u : FractionalSpace 𝕜 d s p) : FractionalSpace 𝕜 d s p :=
  ⟨pullbackLp p f hC hvol u.val, finite_energy_pullbackLp f s p hC hD hvol hkernel u⟩

 theorem fractionalNorm_pullback_le {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f : (Fin d → ℝ) ≃ₜ (Fin d → ℝ)) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {C D : ℝ≥0∞} (hC : C ≠ ∞) (hD : D ≠ ∞)
    (hvol : Measure.map f volume ≤ C • volume)
    (hkernel : ∀ x y, differenceKernel s p (y-x) ≤ D * differenceKernel s p (f y-f x))
    (u : FractionalSpace 𝕜 d s p) :
    fractionalNorm s p (pullbackFractional f s p hC hD hvol hkernel u) ≤
      (C.toReal ^ (1 / p.toReal) + (D * C^2).toReal ^ (1 / p.toReal)) * fractionalNorm s p u := by
  have hE := energy_pullbackLp_le f s p hC hD hvol hkernel u.val
  have hfin : D * C^2 * differenceEnergy s p u.val ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hD (ENNReal.pow_ne_top hC)) u.property.ne
  have hreal := ENNReal.toReal_mono hfin hE
  rw [ENNReal.toReal_mul] at hreal
  have hroot := Real.rpow_le_rpow ENNReal.toReal_nonneg hreal
    (by positivity : 0 ≤ 1 / p.toReal)
  rw [Real.mul_rpow ENNReal.toReal_nonneg ENNReal.toReal_nonneg] at hroot
  have hnorm := norm_pullbackLp_le f p hC hvol u.val
  change ‖pullbackLp p f hC hvol u.val‖ +
    (differenceEnergy s p (pullbackLp p f hC hvol u.val)).toReal ^ (1 / p.toReal) ≤ _
  unfold fractionalNorm
  have hA : 0 ≤ C.toReal ^ (1 / p.toReal) := Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hB : 0 ≤ (D * C^2).toReal ^ (1 / p.toReal) := Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hu : 0 ≤ (differenceEnergy s p u.val).toReal ^ (1 / p.toReal) :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  nlinarith [mul_nonneg hA hu, mul_nonneg hB (norm_nonneg u.val)]
end ExpandedFA.PartIV.FractionalSobolev.Transport
namespace ExpandedFA.PartIV.FractionalSobolev.Transport
open ExpandedFA.PartIV.FractionalSobolev
 theorem pullbackLp_symm_apply {𝕜 : Type*} [RCLike 𝕜] {d : ℕ}
    (f : (Fin d → ℝ) ≃ₜ (Fin d → ℝ)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {C C' : ℝ≥0∞} (hC : C ≠ ∞) (hC' : C' ≠ ∞)
    (hvol : Measure.map f volume ≤ C • volume)
    (hvol' : Measure.map f.symm volume ≤ C' • volume)
    (u : Lp 𝕜 p (volume : Measure (Fin d → ℝ))) :
    pullbackLp p f.symm hC' hvol' (pullbackLp p f hC hvol u) = u := by
  have hq : QuasiMeasurePreserving f.symm volume volume :=
    ⟨f.symm.continuous.measurable, Measure.absolutelyContinuous_of_le_smul hvol'⟩
  apply Lp.ext
  filter_upwards [pullbackLp_ae_eq p f.symm hC' hvol' (pullbackLp p f hC hvol u),
    hq.ae_eq_comp (pullbackLp_ae_eq p f hC hvol u)] with x hx hy
  change _ = pullbackLp p f hC hvol u (f.symm x) at hx
  change pullbackLp p f hC hvol u (f.symm x) = u (f (f.symm x)) at hy
  rw [hx, hy, f.apply_symm_apply]

 theorem pullbackLp_add {𝕜 : Type*} [RCLike 𝕜] {d : ℕ}
    (f : (Fin d → ℝ) ≃ₜ (Fin d → ℝ)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hvol : Measure.map f volume ≤ C • volume)
    (u v : Lp 𝕜 p (volume : Measure (Fin d → ℝ))) :
    pullbackLp p f hC hvol (u+v) = pullbackLp p f hC hvol u + pullbackLp p f hC hvol v := by
  have hq : QuasiMeasurePreserving f volume volume :=
    ⟨f.continuous.measurable, Measure.absolutelyContinuous_of_le_smul hvol⟩
  apply Lp.ext
  filter_upwards [pullbackLp_ae_eq p f hC hvol (u+v), pullbackLp_ae_eq p f hC hvol u,
    pullbackLp_ae_eq p f hC hvol v, Lp.coeFn_add (pullbackLp p f hC hvol u) (pullbackLp p f hC hvol v),
    hq.ae_eq_comp (Lp.coeFn_add u v)] with x huv hu hv hadd hcomp
  change _ = (u+v) (f x) at huv
  change (u+v) (f x) = u (f x)+v (f x) at hcomp
  change _ = u (f x) at hu
  change _ = v (f x) at hv
  simp only [Pi.add_apply] at hadd
  rw [huv, hadd, hu, hv, hcomp]

 theorem pullbackLp_smul {𝕜 : Type*} [RCLike 𝕜] {d : ℕ}
    (f : (Fin d → ℝ) ≃ₜ (Fin d → ℝ)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hvol : Measure.map f volume ≤ C • volume)
    (c : 𝕜) (u : Lp 𝕜 p (volume : Measure (Fin d → ℝ))) :
    pullbackLp p f hC hvol (c • u) = c • pullbackLp p f hC hvol u := by
  have hq : QuasiMeasurePreserving f volume volume :=
    ⟨f.continuous.measurable, Measure.absolutelyContinuous_of_le_smul hvol⟩
  apply Lp.ext
  filter_upwards [pullbackLp_ae_eq p f hC hvol (c • u), pullbackLp_ae_eq p f hC hvol u,
    Lp.coeFn_smul c (pullbackLp p f hC hvol u), hq.ae_eq_comp (Lp.coeFn_smul c u)] with x hcu hu hsmul hcomp
  change _ = (c • u) (f x) at hcu
  change (c • u) (f x) = c • u (f x) at hcomp
  change _ = u (f x) at hu
  simp only [Pi.smul_apply] at hsmul
  rw [hcu, hsmul, hu, hcomp]
end ExpandedFA.PartIV.FractionalSobolev.Transport
namespace ExpandedFA.PartIV.FractionalSobolev.Transport
open ExpandedFA.PartIV.FractionalSobolev
 def fractionalTransportLinearEquiv {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f : (Fin d → ℝ) ≃ₜ (Fin d → ℝ)) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (p ≠ ∞)]
    {C D C' D' : ℝ≥0∞} (hC : C ≠ ∞) (hD : D ≠ ∞) (hC' : C' ≠ ∞) (hD' : D' ≠ ∞)
    (hvol : Measure.map f volume ≤ C • volume)
    (hvol' : Measure.map f.symm volume ≤ C' • volume)
    (hkernel : ∀ x y, differenceKernel s p (y-x) ≤ D * differenceKernel s p (f y-f x))
    (hkernel' : ∀ x y, differenceKernel s p (y-x) ≤ D' * differenceKernel s p (f.symm y-f.symm x)) :
    FractionalSpace 𝕜 d s p ≃ₗ[𝕜] FractionalSpace 𝕜 d s p where
  toFun := pullbackFractional f s p hC hD hvol hkernel
  invFun := pullbackFractional f.symm s p hC' hD' hvol' hkernel'
  left_inv u := Subtype.ext (pullbackLp_symm_apply f p hC hC' hvol hvol' u.val)
  right_inv u := Subtype.ext (pullbackLp_symm_apply f.symm p hC' hC hvol' hvol u.val)
  map_add' u v := Subtype.ext (pullbackLp_add f p hC hvol u.val v.val)
  map_smul' c u := Subtype.ext (pullbackLp_smul f p hC hvol c u.val)

 def fractionalTransportContinuousLinearEquiv {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f : (Fin d → ℝ) ≃ₜ (Fin d → ℝ)) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (p ≠ ∞)]
    {C D C' D' : ℝ≥0∞} (hC : C ≠ ∞) (hD : D ≠ ∞) (hC' : C' ≠ ∞) (hD' : D' ≠ ∞)
    (hvol : Measure.map f volume ≤ C • volume)
    (hvol' : Measure.map f.symm volume ≤ C' • volume)
    (hkernel : ∀ x y, differenceKernel s p (y-x) ≤ D * differenceKernel s p (f y-f x))
    (hkernel' : ∀ x y, differenceKernel s p (y-x) ≤ D' * differenceKernel s p (f.symm y-f.symm x)) :
    FractionalSpace 𝕜 d s p ≃L[𝕜] FractionalSpace 𝕜 d s p :=
  (fractionalTransportLinearEquiv (𝕜 := 𝕜) f s p hC hD hC' hD' hvol hvol' hkernel hkernel').toContinuousLinearEquivOfBounds
    (C.toReal ^ (1 / p.toReal) + (D * C^2).toReal ^ (1 / p.toReal))
    (C'.toReal ^ (1 / p.toReal) + (D' * C'^2).toReal ^ (1 / p.toReal))
    (fractionalNorm_pullback_le f s p hC hD hvol hkernel)
    (fractionalNorm_pullback_le f.symm s p hC' hD' hvol' hkernel')
end ExpandedFA.PartIV.FractionalSobolev.Transport
namespace ExpandedFA.PartIV.FractionalSobolev.Transport
open ExpandedFA.PartIV.FractionalSobolev
 def pullbackLpLinearEquiv {𝕜 : Type*} [RCLike 𝕜] {d : ℕ}
    (f : (Fin d → ℝ) ≃ₜ (Fin d → ℝ)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {C C' : ℝ≥0∞} (hC : C ≠ ∞) (hC' : C' ≠ ∞)
    (hvol : Measure.map f volume ≤ C • volume)
    (hvol' : Measure.map f.symm volume ≤ C' • volume) :
    Lp 𝕜 p (volume : Measure (Fin d → ℝ)) ≃ₗ[𝕜] Lp 𝕜 p (volume : Measure (Fin d → ℝ)) where
  toFun := pullbackLp p f hC hvol
  invFun := pullbackLp p f.symm hC' hvol'
  left_inv u := pullbackLp_symm_apply f p hC hC' hvol hvol' u
  right_inv u := pullbackLp_symm_apply f.symm p hC' hC hvol' hvol u
  map_add' u v := pullbackLp_add f p hC hvol u v
  map_smul' c u := pullbackLp_smul f p hC hvol c u

 theorem biLipschitz_transport {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f : (Fin d → ℝ) ≃ₜ (Fin d → ℝ)) {K K' : ℝ≥0}
    (hf : LipschitzWith K f) (hf' : LipschitzWith K' f.symm)
    (s : ℝ) (hs : 0 < s) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ e : Lp 𝕜 p (volume : Measure (Fin d → ℝ)) ≃ₗ[𝕜] Lp 𝕜 p (volume : Measure (Fin d → ℝ)),
      (∀ u, e u =ᵐ[volume] u ∘ f) ∧
      (∀ u, differenceEnergy s p (e u) < ∞ ↔ differenceEnergy s p u < ∞) ∧
      ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
        ∀ u : FractionalSpace 𝕜 d s p,
          ∃ hu : differenceEnergy s p (e u.val) < ∞,
            fractionalNorm s p ⟨e u.val, hu⟩ ≤ A * fractionalNorm s p u ∧
            fractionalNorm s p u ≤ B * fractionalNorm s p ⟨e u.val, hu⟩ := by
  obtain ⟨L, hL, hLip⟩ := exists_euclidean_lipschitz_constant hf
  obtain ⟨L', hL', hLip'⟩ := exists_euclidean_lipschitz_constant hf'
  let q : ℝ := d + s * p.toReal
  have hq : 0 ≤ q := add_nonneg (Nat.cast_nonneg _) (mul_nonneg hs.le ENNReal.toReal_nonneg)
  let C : ℝ≥0∞ := (K' : ℝ≥0∞)^d
  let C' : ℝ≥0∞ := (K : ℝ≥0∞)^d
  let D : ℝ≥0∞ := ENNReal.ofReal L ^ q
  let D' : ℝ≥0∞ := ENNReal.ofReal L' ^ q
  have hC : C ≠ ∞ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hC' : C' ≠ ∞ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hD : D ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hq ENNReal.ofReal_ne_top
  have hD' : D' ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hq ENNReal.ofReal_ne_top
  have hvol : Measure.map f volume ≤ C • volume := map_volume_le f hf'
  have hvol' : Measure.map f.symm volume ≤ C' • volume := map_volume_le f.symm hf
  have hkernel : ∀ x y, differenceKernel s p (y-x) ≤ D * differenceKernel s p (f y-f x) :=
    kernel_comparison f f.injective L hL s p hq hLip
  have hkernel' : ∀ x y, differenceKernel s p (y-x) ≤ D' * differenceKernel s p (f.symm y-f.symm x) :=
    kernel_comparison f.symm f.symm.injective L' hL' s p hq hLip'
  let e := pullbackLpLinearEquiv (𝕜 := 𝕜) f p hC hC' hvol hvol'
  refine ⟨e, pullbackLp_ae_eq p f hC hvol, ?_, ?_⟩
  · intro u
    constructor
    · intro hu
      have hv := finite_energy_pullbackLp f.symm s p hC' hD' hvol' hkernel' ⟨e u, hu⟩
      change differenceEnergy s p (pullbackLp p f.symm hC' hvol' (pullbackLp p f hC hvol u)) < ∞ at hv
      rwa [pullbackLp_symm_apply] at hv
    · intro hu
      exact finite_energy_pullbackLp f s p hC hD hvol hkernel ⟨u, hu⟩
  · let A := C.toReal ^ (1 / p.toReal) + (D * C^2).toReal ^ (1 / p.toReal)
    let B := C'.toReal ^ (1 / p.toReal) + (D' * C'^2).toReal ^ (1 / p.toReal)
    have hA : 0 ≤ A := add_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _) (Real.rpow_nonneg ENNReal.toReal_nonneg _)
    have hB : 0 ≤ B := add_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _) (Real.rpow_nonneg ENNReal.toReal_nonneg _)
    refine ⟨A+1, B+1, by positivity, by positivity, ?_⟩
    intro u
    let v := pullbackFractional f s p hC hD hvol hkernel u
    refine ⟨v.property, ?_, ?_⟩
    · have hb := fractionalNorm_pullback_le f s p hC hD hvol hkernel u
      change fractionalNorm s p v ≤ (A+1) * fractionalNorm s p u
      change fractionalNorm s p v ≤ A * fractionalNorm s p u at hb
      nlinarith [fractionalNorm_nonneg s p u]
    · have hb := fractionalNorm_pullback_le f.symm s p hC' hD' hvol' hkernel' v
      have hinv : pullbackFractional f.symm s p hC' hD' hvol' hkernel' v = u := by
        apply Subtype.ext
        exact pullbackLp_symm_apply f p hC hC' hvol hvol' u.val
      rw [hinv] at hb
      change fractionalNorm s p u ≤ (B+1) * fractionalNorm s p v
      change fractionalNorm s p u ≤ B * fractionalNorm s p v at hb
      nlinarith [fractionalNorm_nonneg s p v]
end ExpandedFA.PartIV.FractionalSobolev.Transport
namespace ExpandedFA.PartIV.FractionalSobolev.Transport
 theorem lintegral_comp_le_of_measurable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α → β} (hf : AEMeasurable f μ)
    {C : ℝ≥0∞} (hC : Measure.map f μ ≤ C • ν) {g : β → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g (f x) ∂μ ≤ C * ∫⁻ y, g y ∂ν := by
  rw [← lintegral_map' hg.aemeasurable hf]
  calc
    _ ≤ ∫⁻ y, g y ∂C • ν := lintegral_mono' hC le_rfl
    _ = _ := by simp only [lintegral_smul_measure, smul_eq_mul]

 theorem double_lintegral_comp_le_of_measurable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν] {f : α → β} (hf : AEMeasurable f μ)
    {C : ℝ≥0∞} (hC : Measure.map f μ ≤ C • ν) (hCtop : C ≠ ∞)
    {g : β → β → ℝ≥0∞} (hg : Measurable (Function.uncurry g)) :
    ∫⁻ x, ∫⁻ y, g (f x) (f y) ∂μ ∂μ ≤ C^2 * ∫⁻ x, ∫⁻ y, g x y ∂ν ∂ν := by
  calc
    _ ≤ ∫⁻ x, C * ∫⁻ y, g (f x) y ∂ν ∂μ := by
      apply lintegral_mono
      intro x
      exact lintegral_comp_le_of_measurable hf hC (hg.comp (measurable_const.prodMk measurable_id))
    _ = C * ∫⁻ x, ∫⁻ y, g (f x) y ∂ν ∂μ := by rw [lintegral_const_mul' _ _ hCtop]
    _ ≤ C * (C * ∫⁻ x, ∫⁻ y, g x y ∂ν ∂ν) := by
      gcongr
      exact lintegral_comp_le_of_measurable hf hC hg.lintegral_prod_right
    _ = _ := by rw [pow_two, mul_assoc]

open ExpandedFA.PartIV.FractionalSobolev
 def rawDoubleEnergyOn {𝕜 : Type*} [RCLike 𝕜] {d : ℕ} (s : ℝ) (p : ℝ≥0∞)
    (U : Set (Fin d → ℝ)) (u : (Fin d → ℝ) → 𝕜) : ℝ≥0∞ :=
  ∫⁻ x in U, ∫⁻ y in U, differenceKernel s p (y-x) * ‖u y-u x‖ₑ ^ p.toReal

 theorem rawDoubleEnergyOn_comp_le {𝕜 : Type*} [RCLike 𝕜] {d : ℕ}
    {f : (Fin d → ℝ) → (Fin d → ℝ)} {U V : Set (Fin d → ℝ)}
    (hU : MeasurableSet U) (hf : ContinuousOn f U) (s : ℝ) (p : ℝ≥0∞)
    {C D : ℝ≥0∞} (hC : C ≠ ∞) (hD : D ≠ ∞)
    (hvol : Measure.map f (volume.restrict U) ≤ C • volume.restrict V)
    (hkernel : ∀ x ∈ U, ∀ y ∈ U, differenceKernel s p (y-x) ≤ D * differenceKernel s p (f y-f x))
    {u : (Fin d → ℝ) → 𝕜} (hu : Measurable u) :
    rawDoubleEnergyOn s p U (u ∘ f) ≤ (D * C^2) * rawDoubleEnergyOn s p V u := by
  unfold rawDoubleEnergyOn
  calc
    _ ≤ ∫⁻ x in U, ∫⁻ y in U, D * (differenceKernel s p (f y-f x) * ‖u (f y)-u (f x)‖ₑ ^ p.toReal) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hU] with x hx
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hU] with y hy
      dsimp only [Function.comp_apply]
      rw [← mul_assoc]
      gcongr
      exact hkernel x hx y hy
    _ = D * ∫⁻ x in U, ∫⁻ y in U, differenceKernel s p (f y-f x) * ‖u (f y)-u (f x)‖ₑ ^ p.toReal := by
      simp_rw [lintegral_const_mul' _ _ hD]
    _ ≤ D * (C^2 * ∫⁻ x in V, ∫⁻ y in V, differenceKernel s p (y-x) * ‖u y-u x‖ₑ ^ p.toReal) := by
      gcongr
      apply double_lintegral_comp_le_of_measurable (hf.aemeasurable hU) hvol hC
        (g := fun x y => differenceKernel s p (y-x) * ‖u y-u x‖ₑ ^ p.toReal)
      exact ((differenceKernel_measurable s p).comp (measurable_snd.sub measurable_fst)).mul
        (((hu.comp measurable_snd).sub (hu.comp measurable_fst)).enorm.pow_const _)
    _ = _ := by rw [mul_assoc]
end ExpandedFA.PartIV.FractionalSobolev.Transport
namespace ExpandedFA.PartIV.FractionalSobolev.Transport
open ExpandedFA.PartIV.FractionalSobolev
 theorem exists_euclidean_lipschitz_constant_on {d : ℕ} {K : ℝ≥0}
    {f : (Fin d → ℝ) → (Fin d → ℝ)} {U : Set (Fin d → ℝ)} (hf : LipschitzOnWith K f U) :
    ∃ L : ℝ, 0 < L ∧ ∀ x ∈ U, ∀ y ∈ U,
      euclideanLength (f y-f x) ≤ L * euclideanLength (y-x) := by
  obtain ⟨g, hg, hgf⟩ := hf.extend_pi
  obtain ⟨L, hL, hLip⟩ := exists_euclidean_lipschitz_constant hg
  exact ⟨L, hL, fun x hx y hy => by simpa only [hgf hx, hgf hy] using hLip x y⟩

 theorem kernel_comparison_on {d : ℕ} {U : Set (Fin d → ℝ)}
    (f : (Fin d → ℝ) → (Fin d → ℝ)) (hinj : Set.InjOn f U)
    (L : ℝ) (hL : 0 < L) (s : ℝ) (p : ℝ≥0∞)
    (hq : 0 ≤ (d : ℝ) + s * p.toReal)
    (hLip : ∀ x ∈ U, ∀ y ∈ U, euclideanLength (f y-f x) ≤ L * euclideanLength (y-x))
    (x : Fin d → ℝ) (hx : x ∈ U) (y : Fin d → ℝ) (hy : y ∈ U) :
    differenceKernel s p (y-x) ≤ ENNReal.ofReal L ^ ((d : ℝ) + s * p.toReal) *
      differenceKernel s p (f y-f x) := by
  by_cases hxy : y=x
  · subst y
    simp [differenceKernel]
  · have ha : 0 < euclideanLength (y-x) := by
      apply norm_pos_iff.mpr
      simpa only [ne_eq, WithLp.toLp_eq_zero, sub_eq_zero] using hxy
    have hfxy : f y - f x ≠ 0 := by
      intro hz
      exact hxy (hinj hy hx (sub_eq_zero.mp hz))
    have hb : 0 < euclideanLength (f y-f x) := by
      apply norm_pos_iff.mpr
      simpa only [ne_eq, WithLp.toLp_eq_zero] using hfxy
    simp only [differenceKernel, ite_eq_right (sub_ne_zero.mpr hxy), ite_eq_right hfxy]
    exact reciprocal_rpow_comparison _ _ _ _ ha hb hL hq (hLip x hx y hy)

 theorem local_biLipschitz_energy_bound {𝕜 : Type*} [RCLike 𝕜] {d : ℕ}
    {f g : (Fin d → ℝ) → (Fin d → ℝ)} {U V : Set (Fin d → ℝ)}
    (hU : MeasurableSet U) (hV : MeasurableSet V)
    {K K' : ℝ≥0} (hf : LipschitzOnWith K f U) (hg : LipschitzOnWith K' g V)
    (hfg : ∀ x ∈ U, f x ∈ V ∧ g (f x) = x)
    (hgf : ∀ y ∈ V, g y ∈ U ∧ f (g y) = y)
    (s : ℝ) (hs : 0 < s) (p : ℝ≥0∞) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ u : (Fin d → ℝ) → 𝕜, Measurable u →
      rawDoubleEnergyOn s p U (u ∘ f) ≤ C * rawDoubleEnergyOn s p V u := by
  obtain ⟨L, hL, hLip⟩ := exists_euclidean_lipschitz_constant_on hf
  let q : ℝ := d + s * p.toReal
  have hq : 0 ≤ q := add_nonneg (Nat.cast_nonneg _) (mul_nonneg hs.le ENNReal.toReal_nonneg)
  let C : ℝ≥0∞ := (K' : ℝ≥0∞)^d
  let D : ℝ≥0∞ := ENNReal.ofReal L ^ q
  have hC : C ≠ ∞ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hD : D ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hq ENNReal.ofReal_ne_top
  have hvol : Measure.map f (volume.restrict U) ≤ C • volume.restrict V :=
    map_restrict_volume_le hU hV hf.continuousOn hg hfg hgf
  have hinj : Set.InjOn f U := by
    intro x hx y hy he
    calc x = g (f x) := (hfg x hx).2.symm
         _ = g (f y) := congrArg g he
         _ = y := (hfg y hy).2
  refine ⟨D * C^2, ENNReal.mul_ne_top hD (ENNReal.pow_ne_top hC), ?_⟩
  intro u hu
  exact rawDoubleEnergyOn_comp_le hU hf.continuousOn s p hC hD hvol
    (kernel_comparison_on f hinj L hL s p hq hLip) hu
end ExpandedFA.PartIV.FractionalSobolev.Transport

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

/-! Finite reconstruction estimate for comparing localized boundary norms.
This helper does not itself provide charts, cutoffs, or bounded transition maps.
Those are the remaining geometric and analytic obligations. -/

open scoped BigOperators

namespace ExpandedFA.PartIV.FractionalSobolev.BoundaryLocalization
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {V : Type*}
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Sum convention for a finite family of local full norms. -/
def localizedNorm (F : ι → V → W) (v : V) : ℝ := ∑ i, ‖F i v‖

/-- If localized pieces for the second atlas reconstruct from those of the
first through bounded linear overlap maps, their finite sum norms compare.
The constant is explicit and valid when an index family is empty. -/
theorem localizedNorm_le_of_reconstruction
    (F : ι → V → W) (G : κ → V → W)
    (T : κ → ι → W →L[𝕜] W)
    (hreconstruct : ∀ j v, G j v = ∑ i, T j i (F i v)) (v : V) :
    localizedNorm G v ≤ (∑ j, ∑ i, ‖T j i‖) * localizedNorm F v := by
  classical
  unfold localizedNorm
  calc
    _ ≤ ∑ j, ∑ i, ‖T j i‖ * ‖F i v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [hreconstruct]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (T j i).le_opNorm _)
    _ ≤ ∑ j, ∑ i, ‖T j i‖ * (∑ k, ‖F k v‖) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.single_le_sum (fun k _ => norm_nonneg (F k v)) (Finset.mem_univ i)
    _ = _ := by simp_rw [Finset.sum_mul]

/-- Applying the estimate in both directions supplies norm equivalence. -/
theorem localizedNorm_equivalent
    (F : ι → V → W) (G : κ → V → W)
    (T : κ → ι → W →L[𝕜] W) (S : ι → κ → W →L[𝕜] W)
    (hG : ∀ j v, G j v = ∑ i, T j i (F i v))
    (hF : ∀ i v, F i v = ∑ j, S i j (G j v)) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ v, localizedNorm G v ≤ C * localizedNorm F v ∧
        localizedNorm F v ≤ D * localizedNorm G v := by
  refine ⟨∑ j, ∑ i, ‖T j i‖, ∑ i, ∑ j, ‖S i j‖, ?_, ?_, ?_⟩
  · exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => norm_nonneg _
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  · intro v
    exact ⟨localizedNorm_le_of_reconstruction F G T hG v,
      localizedNorm_le_of_reconstruction G F S hF v⟩

end ExpandedFA.PartIV.FractionalSobolev.BoundaryLocalization

namespace ExpandedFA.PartIV.FractionalSobolev.BoundaryLocalization
open MeasureTheory Set
open scoped ENNReal
variable {E : Type*} [MeasurableSpace E] (μ : Measure E) [SFinite μ]

/-- Splitting a symmetric nonnegative two-point energy into the interior term
and the two equal cross-boundary terms. No integrability is assumed. -/
theorem symmetric_energy_split
    (A : E × E → ℝ≥0∞) (hA : Measurable A)
    (hsymm : ∀ x y, A (x, y) = A (y, x))
    (Ω : Set E) (hΩ : MeasurableSet Ω)
    (hzero : ∀ x ∉ Ω, ∀ y ∉ Ω, A (x, y) = 0) :
    (∫⁻ x, ∫⁻ y, A (x, y) ∂μ ∂μ) =
      (∫⁻ x in Ω, ∫⁻ y in Ω, A (x, y) ∂μ ∂μ) +
        2 * (∫⁻ x in Ω, ∫⁻ y in Ωᶜ, A (x, y) ∂μ ∂μ) := by
  have hinner : Measurable (fun x => ∫⁻ y in Ω, A (x, y) ∂μ) :=
    hA.lintegral_prod_right'
  have hout : (∫⁻ x in Ωᶜ, ∫⁻ y, A (x, y) ∂μ ∂μ) =
      ∫⁻ x in Ωᶜ, ∫⁻ y in Ω, A (x, y) ∂μ ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict hΩ.compl] with x hx
    rw [← lintegral_add_compl (fun y => A (x, y)) hΩ]
    suffices (∫⁻ y in Ωᶜ, A (x, y) ∂μ) = 0 by rw [this, add_zero]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [self_mem_ae_restrict hΩ.compl] with y hy
    exact hzero x hx y hy
  have hcross : (∫⁻ x in Ωᶜ, ∫⁻ y in Ω, A (x, y) ∂μ ∂μ) =
      ∫⁻ x in Ω, ∫⁻ y in Ωᶜ, A (x, y) ∂μ ∂μ := by
    rw [lintegral_lintegral_swap (f := fun x y => A (x, y)) hA.aemeasurable]
    apply lintegral_congr
    intro x
    apply lintegral_congr
    intro y
    exact hsymm y x
  calc
    _ = (∫⁻ x in Ω, ∫⁻ y, A (x, y) ∂μ ∂μ) +
        (∫⁻ x in Ωᶜ, ∫⁻ y, A (x, y) ∂μ ∂μ) :=
      (lintegral_add_compl _ hΩ).symm
    _ = ((∫⁻ x in Ω, ∫⁻ y in Ω, A (x, y) ∂μ ∂μ) +
          (∫⁻ x in Ω, ∫⁻ y in Ωᶜ, A (x, y) ∂μ ∂μ)) +
        (∫⁻ x in Ω, ∫⁻ y in Ωᶜ, A (x, y) ∂μ ∂μ) := by
      rw [hout, hcross, ← lintegral_add_left hinner]
      congr 1
      apply lintegral_congr
      intro x
      exact (lintegral_add_compl (fun y => A (x, y)) hΩ).symm
    _ = _ := by rw [two_mul, add_assoc]

end ExpandedFA.PartIV.FractionalSobolev.BoundaryLocalization

namespace ExpandedFA.PartIV.FractionalSobolev.BoundaryLocalization
open MeasureTheory Set
open scoped ENNReal
variable {E : Type*} [MeasurableSpace E] (μ : Measure E) [SFinite μ]
variable {𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
 

/-- The actual chart-edge estimate. A function vanishing outside Ω has full
Gagliardo energy at most its restricted energy plus two kernel tails times
its Lp mass. Uniform tails are needed only at points where f is nonzero. -/
theorem zero_extension_energy_le
    (K : E × E → ℝ≥0∞) (hK : Measurable K)
    (hsymm : ∀ x y, K (x, y) = K (y, x))
    (Ω : Set E) (hΩ : MeasurableSet Ω)
    (f : E → 𝕜) (hf : Measurable f) (r : ℝ) (hr : 0 < r)
    (hzero : ∀ x ∉ Ω, f x = 0) (T : ℝ≥0∞)
    (htail : ∀ x ∈ Ω, f x ≠ 0 → (∫⁻ y in Ωᶜ, K (x, y) ∂μ) ≤ T) :
    (∫⁻ x, ∫⁻ y, K (x, y) * ‖f y - f x‖ₑ ^ r ∂μ ∂μ) ≤
      (∫⁻ x in Ω, ∫⁻ y in Ω, K (x, y) * ‖f y - f x‖ₑ ^ r ∂μ ∂μ) +
        2 * T * (∫⁻ x in Ω, ‖f x‖ₑ ^ r ∂μ) := by
  let A : E × E → ℝ≥0∞ := fun z => K z * ‖f z.2 - f z.1‖ₑ ^ r
  have hA : Measurable A := hK.mul
    (((hf.comp measurable_snd).sub (hf.comp measurable_fst)).enorm.pow_const r)
  have hAsymm : ∀ x y, A (x, y) = A (y, x) := by
    intro x y
    simp only [A, hsymm x y, enorm_sub_rev]
  have hAzero : ∀ x ∉ Ω, ∀ y ∉ Ω, A (x, y) = 0 := by
    intro x hx y hy
    simp [A, hzero x hx, hzero y hy, ENNReal.zero_rpow_of_pos hr]
  have hcross : (∫⁻ x in Ω, ∫⁻ y in Ωᶜ, A (x, y) ∂μ ∂μ) ≤
      T * (∫⁻ x in Ω, ‖f x‖ₑ ^ r ∂μ) := by
    calc
      _ ≤ ∫⁻ x in Ω, T * ‖f x‖ₑ ^ r ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [self_mem_ae_restrict hΩ] with x hx
        calc
          _ = (∫⁻ y in Ωᶜ, K (x, y) ∂μ) * ‖f x‖ₑ ^ r := by
            rw [← lintegral_mul_const (μ := μ.restrict Ωᶜ) (f := fun y => K (x, y)) (‖f x‖ₑ ^ r)
              (hK.comp ((measurable_const (a := x)).prodMk measurable_id))]
            apply lintegral_congr_ae
            filter_upwards [self_mem_ae_restrict hΩ.compl] with y hy
            simp [A, hzero y hy]
          _ ≤ T * ‖f x‖ₑ ^ r := by
            by_cases hfx : f x = 0
            · simp [hfx, ENNReal.zero_rpow_of_pos hr]
            · exact mul_le_mul' (htail x hx hfx) le_rfl
      _ = _ := lintegral_const_mul _ (hf.enorm.pow_const r)
  change (∫⁻ x, ∫⁻ y, A (x, y) ∂μ ∂μ) ≤ _
  rw [symmetric_energy_split μ A hA hAsymm Ω hΩ hAzero]
  apply add_le_add le_rfl
  calc
    _ ≤ 2 * (T * ∫⁻ x in Ω, ‖f x‖ₑ ^ r ∂μ) := mul_le_mul' le_rfl hcross
    _ = _ := (mul_assoc _ _ _).symm

end ExpandedFA.PartIV.FractionalSobolev.BoundaryLocalization

namespace ExpandedFA.PartIV.FractionalSobolev

/-- Total difference-kernel mass away from a positive chart-edge distance. -/
def kernelTail {d : ℕ} (s : ℝ) (p : ℝ≥0∞) (δ : ℝ) : ℝ≥0∞ :=
  ∫⁻ h in {h : Fin d → ℝ | δ ≤ euclideanLength h}, differenceKernel s p h

lemma kernelTail_lt_top {d : ℕ} (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞) {δ : ℝ} (hδ : 0 < δ) :
    kernelTail (d := d) s p δ < ∞ := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hc : 0 < min δ 1 := lt_min hδ zero_lt_one
  have hfin := (incrementCutoff_memLp (d := d) s p hs0 hs1 hp).meas_ge_lt_top'_enorm
    hp0 hp (ε := ENNReal.ofReal (min δ 1)) (by positivity) (by simp)
  have hset : {h : Fin d → ℝ | δ ≤ euclideanLength h} ⊆
      {h | ENNReal.ofReal (min δ 1) ≤ ‖incrementCutoff h‖ₑ} := by
    intro h hh
    simp only [mem_ofPred_eq, Real.enorm_of_nonneg (incrementCutoff_nonneg h)]
    exact ENNReal.ofReal_le_ofReal (min_le_min hh le_rfl)
  have hm : MeasurableSet {h : Fin d → ℝ | δ ≤ euclideanLength h} :=
    measurableSet_le measurable_const euclideanLength_continuous.measurable
  change (∫⁻ h in {h : Fin d → ℝ | δ ≤ euclideanLength h}, differenceKernel s p h) < ∞
  rw [← withDensity_apply _ hm]
  exact lt_of_le_of_lt (measure_mono hset) hfin

lemma euclideanLength_neg {d : ℕ} (h : Fin d → ℝ) :
    euclideanLength (-h) = euclideanLength h := by simp [euclideanLength]

lemma differenceKernel_neg {d : ℕ} (s : ℝ) (p : ℝ≥0∞) (h : Fin d → ℝ) :
    differenceKernel s p (-h) = differenceKernel s p h := by
  simp [differenceKernel, euclideanLength_neg]

/-- A separated chart edge lies in the translated tail set. -/
lemma kernel_integral_compl_le_tail {d : ℕ} (s : ℝ) (p : ℝ≥0∞)
    (Ω : Set (Fin d → ℝ)) (hΩ : MeasurableSet Ω) (x : Fin d → ℝ) (δ : ℝ)
    (hsep : ∀ y ∉ Ω, δ ≤ euclideanLength (y - x)) :
    (∫⁻ y in Ωᶜ, differenceKernel s p (y - x)) ≤ kernelTail (d := d) s p δ := by
  let S : Set (Fin d → ℝ) := {h | δ ≤ euclideanLength h}
  have hS : MeasurableSet S :=
    measurableSet_le measurable_const euclideanLength_continuous.measurable
  have hm : Measurable (S.indicator (differenceKernel s p)) :=
    (differenceKernel_measurable s p).indicator hS
  calc
    _ = ∫⁻ y, Ωᶜ.indicator (fun y => differenceKernel s p (y-x)) y :=
      (lintegral_indicator hΩ.compl _).symm
    _ ≤ ∫⁻ y, S.indicator (differenceKernel s p) (y-x) := by
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ Ω
      · simp [hy]
      · have hs : y-x ∈ S := hsep y hy
        simp [hy, hs]
    _ = ∫⁻ h, S.indicator (differenceKernel s p) h :=
      (measurePreserving_sub_right volume x).lintegral_comp hm
    _ = _ := lintegral_indicator hS _

end ExpandedFA.PartIV.FractionalSobolev

namespace ExpandedFA.PartIV.FractionalSobolev

/-- Local zero-extension estimate at a chart edge with a positive support
separation. It applies in every dimension, including the zero convention. -/
lemma local_zeroExtension_energy_le {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (Ω : Set (Fin d → ℝ)) (hΩ : MeasurableSet Ω)
    (f : (Fin d → ℝ) → 𝕜) (hf : Measurable f)
    (hzero : ∀ x ∉ Ω, f x = 0) (δ : ℝ)
    (hsep : ∀ x ∈ Ω, f x ≠ 0 → ∀ y ∉ Ω, δ ≤ euclideanLength (y-x)) :
    (∫⁻ x, ∫⁻ y, differenceKernel s p (y-x) * ‖f y-f x‖ₑ ^ p.toReal) ≤
      (∫⁻ x in Ω, ∫⁻ y in Ω, differenceKernel s p (y-x) * ‖f y-f x‖ₑ ^ p.toReal) +
        2 * kernelTail (d := d) s p δ * (∫⁻ x in Ω, ‖f x‖ₑ ^ p.toReal) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  apply ExpandedFA.PartIV.FractionalSobolev.BoundaryLocalization.zero_extension_energy_le volume
    (fun z : (Fin d → ℝ) × (Fin d → ℝ) => differenceKernel s p (z.2-z.1))
    ((differenceKernel_measurable s p).comp (measurable_snd.sub measurable_fst))
    (fun x y => ?_) Ω hΩ f hf p.toReal hpr hzero (kernelTail s p δ)
  · intro x hx hfx
    exact kernel_integral_compl_le_tail s p Ω hΩ x δ (hsep x hx hfx)
  · rw [← neg_sub x y, differenceKernel_neg]

/-- Consequently an Lp function with finite restricted fractional energy and
support separated from the chart edge has a finite whole-space energy. -/
lemma local_zeroExtension_finite_energy {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞)
    (Ω : Set (Fin d → ℝ)) (hΩ : MeasurableSet Ω)
    (f : (Fin d → ℝ) → 𝕜) (hf : Measurable f)
    (hzero : ∀ x ∉ Ω, f x = 0) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ x ∈ Ω, f x ≠ 0 → ∀ y ∉ Ω, δ ≤ euclideanLength (y-x))
    (hmass : (∫⁻ x in Ω, ‖f x‖ₑ ^ p.toReal) < ∞)
    (henergy : (∫⁻ x in Ω, ∫⁻ y in Ω,
      differenceKernel s p (y-x) * ‖f y-f x‖ₑ ^ p.toReal) < ∞) :
    (∫⁻ x, ∫⁻ y, differenceKernel s p (y-x) * ‖f y-f x‖ₑ ^ p.toReal) < ∞ := by
  apply lt_of_le_of_lt
    (local_zeroExtension_energy_le s p hp Ω hΩ f hf hzero δ hsep)
  have htail := kernelTail_lt_top (d := d) s p hs0 hs1 hp hδ
  finiteness

end ExpandedFA.PartIV.FractionalSobolev

namespace ExpandedFA.PartIV.FractionalSobolev

/-- Compact chart supports inside open coordinate domains have a uniform
positive distance to every excluded point, in the intended Euclidean metric. -/
lemma compact_chart_support_separation {d : ℕ}
    (K Ω : Set (Fin d → ℝ)) (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y ∉ Ω, δ ≤ euclideanLength (y-x) := by
  let K' : Set (EuclideanSpace ℝ (Fin d)) := WithLp.toLp 2 '' K
  let Ω' : Set (EuclideanSpace ℝ (Fin d)) := WithLp.ofLp ⁻¹' Ω
  have hK' : IsCompact K' := hK.image (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))
  have hΩ' : IsOpen Ω' := hΩ.preimage (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ))
  have hsub : K' ⊆ Ω' := by
    rintro _ ⟨x, hx, rfl⟩
    exact hKΩ hx
  obtain ⟨δ, hδ, hthick⟩ := hK'.exists_cthickening_subset_open hΩ' hsub
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy
  by_contra! hlt
  have hmem : WithLp.toLp 2 y ∈ Metric.cthickening δ K' := by
    apply Metric.mem_cthickening_of_dist_le (WithLp.toLp 2 y) (WithLp.toLp 2 x) δ K'
      (mem_image_of_mem _ hx)
    simpa only [dist_eq_norm, ← WithLp.toLp_sub, euclideanLength] using hlt.le
  exact hy (hthick hmem)

/-- Chart-edge applicability stated directly with compact support, rather than
an extra distance assumption. This is the zero-extension lemma used between
restricted overlap estimates and whole-space atlas norms. -/
lemma compact_support_zeroExtension_finite_energy {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞)
    (Ω : Set (Fin d → ℝ)) (hΩ : IsOpen Ω)
    (f : (Fin d → ℝ) → 𝕜) (hf : Measurable f)
    (K : Set (Fin d → ℝ)) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hsupport : Function.support f ⊆ K)
    (hmass : (∫⁻ x in Ω, ‖f x‖ₑ ^ p.toReal) < ∞)
    (henergy : (∫⁻ x in Ω, ∫⁻ y in Ω,
      differenceKernel s p (y-x) * ‖f y-f x‖ₑ ^ p.toReal) < ∞) :
    (∫⁻ x, ∫⁻ y, differenceKernel s p (y-x) * ‖f y-f x‖ₑ ^ p.toReal) < ∞ := by
  obtain ⟨δ, hδ, hsep⟩ := compact_chart_support_separation K Ω hK hΩ hKΩ
  have hzero : ∀ x ∉ Ω, f x = 0 := by
    intro x hx
    by_contra hfx
    exact hx (hKΩ (hsupport hfx))
  apply local_zeroExtension_finite_energy s p hs0 hs1 hp Ω hΩ.measurableSet f hf hzero δ hδ
    (fun x _ hfx => hsep x (hsupport hfx)) hmass henergy

end ExpandedFA.PartIV.FractionalSobolev

namespace ExpandedFA.PartIV.FractionalSobolev

/-- The quantitative pth-root form of the chart-edge bound; its finite constant
is available for building the bounded overlap maps in the atlas comparison. -/
lemma local_zeroExtension_seminorm_le {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (Ω : Set (Fin d → ℝ)) (hΩ : MeasurableSet Ω)
    (f : (Fin d → ℝ) → 𝕜) (hf : Measurable f)
    (hzero : ∀ x ∉ Ω, f x = 0) (δ : ℝ)
    (hsep : ∀ x ∈ Ω, f x ≠ 0 → ∀ y ∉ Ω, δ ≤ euclideanLength (y-x)) :
    (∫⁻ x, ∫⁻ y, differenceKernel s p (y-x) * ‖f y-f x‖ₑ ^ p.toReal) ^ (1/p.toReal) ≤
      (∫⁻ x in Ω, ∫⁻ y in Ω,
        differenceKernel s p (y-x) * ‖f y-f x‖ₑ ^ p.toReal) ^ (1/p.toReal) +
        (2 * kernelTail (d := d) s p δ) ^ (1/p.toReal) *
          (∫⁻ x in Ω, ‖f x‖ₑ ^ p.toReal) ^ (1/p.toReal) := by
  have hpr : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
  have hq0 : 0 ≤ 1 / p.toReal := by positivity
  have hq1 : 1 / p.toReal ≤ 1 := (div_le_one (by positivity)).mpr hpr
  calc
    _ ≤ ((∫⁻ x in Ω, ∫⁻ y in Ω,
        differenceKernel s p (y-x) * ‖f y-f x‖ₑ ^ p.toReal) +
        2 * kernelTail (d := d) s p δ * (∫⁻ x in Ω, ‖f x‖ₑ ^ p.toReal)) ^ (1/p.toReal) :=
      ENNReal.rpow_le_rpow (local_zeroExtension_energy_le s p hp Ω hΩ f hf hzero δ hsep) hq0
    _ ≤ _ := by
      simpa only [ENNReal.mul_rpow_of_nonneg _ _ hq0] using
        ENNReal.rpow_add_le_add_rpow
          (∫⁻ x in Ω, ∫⁻ y in Ω,
            differenceKernel s p (y-x) * ‖f y-f x‖ₑ ^ p.toReal)
          (2 * kernelTail (d := d) s p δ * (∫⁻ x in Ω, ‖f x‖ₑ ^ p.toReal)) hq0 hq1

end ExpandedFA.PartIV.FractionalSobolev

namespace ExpandedFA.PartIV.FractionalSobolev

theorem biLipschitz_transport : Specs.ExpandedFA.PartIV.FractionalSobolev.BiLipschitzTransport := by
  intro 𝕜 _ d f K K' hf hg s hs _ p _ _
  exact Transport.biLipschitz_transport f hf hg s hs p

theorem local_biLipschitz_energy_bound :
    Specs.ExpandedFA.PartIV.FractionalSobolev.LocalBiLipschitzEnergy := by
  intro 𝕜 _ d f g U V hU hV K K' hf hg hfg hgf s hs _ p _ _
  exact Transport.local_biLipschitz_energy_bound hU hV hf hg hfg hgf s hs p

theorem compact_support_zero_extension :
    Specs.ExpandedFA.PartIV.FractionalSobolev.CompactSupportZeroExtension := by
  intro 𝕜 _ _ _ d s p _ hs0 hs1 hp Ω hΩ f hf K hK hKΩ hsupp hmass henergy
  exact compact_support_zeroExtension_finite_energy s p hs0 hs1 hp Ω hΩ f hf
    K hK hKΩ hsupp hmass henergy

end ExpandedFA.PartIV.FractionalSobolev

namespace ExpandedFA.PartIV.FractionalSobolev

abbrev BoundarySpace : Specs.ExpandedFA.PartIV.FractionalSobolev.BoundarySpaceType :=
  Specs.ExpandedFA.PartIV.FractionalSobolev.BoundarySpaceValue

def boundaryFullNorm : Specs.ExpandedFA.PartIV.FractionalSobolev.BoundaryNormType :=
  Specs.ExpandedFA.PartIV.FractionalSobolev.BoundaryNormValue

end ExpandedFA.PartIV.FractionalSobolev

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators

namespace ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : FiniteAtlas M d ι)

lemma chartMeasure_apply (i : ι) {s : Set M} (hs : MeasurableSet s) :
    A.chartMeasure i s = volume ((A.chart i) '' (s ∩ (A.chart i).source)) := by
  rw [chartMeasure, Measure.map_apply_of_aemeasurable
    ((A.chart i).continuousOn_symm.aemeasurable (A.chart i).open_target.measurableSet) hs,
    Measure.restrict_apply' (A.chart i).open_target.measurableSet]
  congr 1
  ext y
  constructor
  · rintro ⟨hyS, hyT⟩
    exact ⟨(A.chart i).symm y, ⟨hyS, (A.chart i).map_target hyT⟩, (A.chart i).right_inv hyT⟩
  · rintro ⟨x, ⟨hxS, hxU⟩, rfl⟩
    exact ⟨by simpa only [Set.mem_preimage, (A.chart i).left_inv hxU] using hxS, (A.chart i).map_source hxU⟩

lemma chartMeasure_le_hausdorff (i : ι) :
    A.chartMeasure i ≤ (A.chartLip i : ℝ≥0∞)^d •
      (MeasureTheory.Measure.hausdorffMeasure (d : ℝ) : Measure M).restrict (A.chart i).source := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [A.chartMeasure_apply i hs, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply' (A.chart i).open_source.measurableSet]
  have h := ((A.chart_lipschitz i).mono (s := s ∩ (A.chart i).source) inter_subset_right).hausdorffMeasure_image_le
    (d := (d : ℝ)) (Nat.cast_nonneg d)
  have hv : (MeasureTheory.Measure.hausdorffMeasure (d : ℝ) : Measure (Fin d → ℝ)) = volume := by
    simpa only [Fintype.card_fin] using (MeasureTheory.hausdorffMeasure_pi_real (ι := Fin d))
  simpa only [ENNReal.rpow_natCast, hv] using h

lemma hausdorff_restrict_le_chartMeasure (i : ι) :
    (MeasureTheory.Measure.hausdorffMeasure (d : ℝ) : Measure M).restrict (A.chart i).source ≤
      (A.chartSymmLip i : ℝ≥0∞)^d • A.chartMeasure i := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.restrict_apply' (A.chart i).open_source.measurableSet,
    Measure.smul_apply, smul_eq_mul, A.chartMeasure_apply i hs]
  have hsub : (A.chart i) '' (s ∩ (A.chart i).source) ⊆ (A.chart i).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (A.chart i).map_source hx.2
  have he : (A.chart i).symm '' ((A.chart i) '' (s ∩ (A.chart i).source)) = s ∩ (A.chart i).source := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      simpa only [(A.chart i).left_inv hy.2] using hy
    · intro hx
      exact ⟨(A.chart i) x, ⟨x, hx, rfl⟩, (A.chart i).left_inv hx.2⟩
  have h := ((A.chartSymm_lipschitz i).mono hsub).hausdorffMeasure_image_le
    (d := (d : ℝ)) (Nat.cast_nonneg d)
  rw [he] at h
  have hv : (MeasureTheory.Measure.hausdorffMeasure (d : ℝ) : Measure (Fin d → ℝ)) = volume := by
    simpa only [Fintype.card_fin] using (MeasureTheory.hausdorffMeasure_pi_real (ι := Fin d))
  simpa only [ENNReal.rpow_natCast, hv] using h
end ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas

namespace ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : FiniteAtlas M d ι)

lemma chartMeasure_absolutelyContinuous_hausdorff (i : ι) :
    A.chartMeasure i ≪ (MeasureTheory.Measure.hausdorffMeasure (d : ℝ) : Measure M) :=
  (Measure.absolutelyContinuous_of_le_smul (A.chartMeasure_le_hausdorff i)).trans
    Measure.restrict_le_self.absolutelyContinuous

lemma hausdorff_restrict_absolutelyContinuous_chartMeasure (i : ι) :
    (MeasureTheory.Measure.hausdorffMeasure (d : ℝ) : Measure M).restrict (A.chart i).source ≪
      A.chartMeasure i :=
  Measure.absolutelyContinuous_of_le_smul (A.hausdorff_restrict_le_chartMeasure i)

lemma atlasMeasure_absolutelyContinuous_hausdorff :
    A.atlasMeasure ≪ (MeasureTheory.Measure.hausdorffMeasure (d : ℝ) : Measure M) :=
  Measure.absolutelyContinuous_sum_left A.chartMeasure_absolutelyContinuous_hausdorff

lemma hausdorff_absolutelyContinuous_atlasMeasure :
    (MeasureTheory.Measure.hausdorffMeasure (d : ℝ) : Measure M) ≪ A.atlasMeasure := by
  intro s hs
  have hzero : ∀ i, (MeasureTheory.Measure.hausdorffMeasure (d : ℝ) : Measure M)
      (s ∩ (A.chart i).source) = 0 := by
    intro i
    have hchart : A.chartMeasure i s = 0 := (A.chartMeasure_le i).absolutelyContinuous hs
    have hrestrict := A.hausdorff_restrict_absolutelyContinuous_chartMeasure i hchart
    rwa [Measure.restrict_apply' (A.chart i).open_source.measurableSet] at hrestrict
  have he : s = ⋃ i, s ∩ (A.chart i).source := by
    ext x
    simp only [mem_iUnion, mem_inter_iff]
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := A.cover x
      exact ⟨i, hx, hi⟩
    · rintro ⟨i, hx, _⟩
      exact hx
  rw [he]
  exact measure_iUnion_null hzero

lemma atlasMeasure_absolutelyContinuous {κ : Type*} [Fintype κ] (B : FiniteAtlas M d κ) :
    A.atlasMeasure ≪ B.atlasMeasure :=
  A.atlasMeasure_absolutelyContinuous_hausdorff.trans B.hausdorff_absolutelyContinuous_atlasMeasure

lemma atlasMeasure_mutuallyAbsolutelyContinuous {κ : Type*} [Fintype κ] (B : FiniteAtlas M d κ) :
    A.atlasMeasure ≪ B.atlasMeasure ∧ B.atlasMeasure ≪ A.atlasMeasure :=
  ⟨A.atlasMeasure_absolutelyContinuous B, B.atlasMeasure_absolutelyContinuous A⟩

lemma atlasMeasure_ae_iff {κ : Type*} [Fintype κ] (B : FiniteAtlas M d κ) {P : M → Prop} :
    (∀ᵐ x ∂A.atlasMeasure, P x) ↔ ∀ᵐ x ∂B.atlasMeasure, P x :=
  ⟨fun h => (B.atlasMeasure_absolutelyContinuous A).ae_le h,
    fun h => (A.atlasMeasure_absolutelyContinuous B).ae_le h⟩

end ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas

namespace ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : FiniteAtlas M d ι)

lemma atlasMeasure_le_smul_hausdorff :
    A.atlasMeasure ≤ (∑ i, (A.chartLip i : ℝ≥0∞)^d) •
      (MeasureTheory.Measure.hausdorffMeasure (d : ℝ) : Measure M) := by
  classical
  apply Measure.le_iff.mpr
  intro s hs
  rw [atlasMeasure, Measure.sum_apply _ hs, tsum_fintype, Measure.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have h := Measure.le_iff'.mp (A.chartMeasure_le_hausdorff i) s
  rw [Measure.smul_apply, smul_eq_mul] at h
  exact h.trans (mul_le_mul_right (Measure.restrict_apply_le _ _) _)

lemma hausdorff_le_smul_atlasMeasure :
    (MeasureTheory.Measure.hausdorffMeasure (d : ℝ) : Measure M) ≤
      (∑ i, (A.chartSymmLip i : ℝ≥0∞)^d) • A.atlasMeasure := by
  classical
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.smul_apply, smul_eq_mul, Finset.sum_mul]
  have he : s = ⋃ i, s ∩ (A.chart i).source := by
    ext x
    simp only [mem_iUnion, mem_inter_iff]
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := A.cover x
      exact ⟨i, hx, hi⟩
    · rintro ⟨i, hx, _⟩
      exact hx
  calc
    _ = (MeasureTheory.Measure.hausdorffMeasure (d : ℝ) : Measure M)
        (⋃ i, s ∩ (A.chart i).source) := congrArg _ he
    _ ≤ ∑' i, (MeasureTheory.Measure.hausdorffMeasure (d : ℝ) : Measure M)
        (s ∩ (A.chart i).source) := measure_iUnion_le _
    _ = ∑ i, (MeasureTheory.Measure.hausdorffMeasure (d : ℝ) : Measure M)
        (s ∩ (A.chart i).source) := tsum_fintype _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      have h := Measure.le_iff'.mp (A.hausdorff_restrict_le_chartMeasure i) s
      rw [Measure.restrict_apply' (A.chart i).open_source.measurableSet,
        Measure.smul_apply, smul_eq_mul] at h
      exact h.trans (mul_le_mul_right (Measure.le_iff'.mp (A.chartMeasure_le i) s) _)

lemma atlasMeasure_le_smul_atlasMeasure {κ : Type*} [Fintype κ] (B : FiniteAtlas M d κ) :
    A.atlasMeasure ≤ ((∑ i, (A.chartLip i : ℝ≥0∞)^d) *
      (∑ j, (B.chartSymmLip j : ℝ≥0∞)^d)) • B.atlasMeasure := by
  calc
    _ ≤ (∑ i, (A.chartLip i : ℝ≥0∞)^d) •
        (MeasureTheory.Measure.hausdorffMeasure (d : ℝ) : Measure M) := A.atlasMeasure_le_smul_hausdorff
    _ ≤ (∑ i, (A.chartLip i : ℝ≥0∞)^d) •
        ((∑ j, (B.chartSymmLip j : ℝ≥0∞)^d) • B.atlasMeasure) :=
      by
        apply Measure.le_iff'.mpr
        intro s
        simp only [Measure.smul_apply, smul_eq_mul]
        gcongr
        exact Measure.le_iff'.mp B.hausdorff_le_smul_atlasMeasure s
    _ = _ := by rw [smul_smul]

lemma atlasMeasure_comparison_constant_finite {κ : Type*} [Fintype κ] (B : FiniteAtlas M d κ) :
    ((∑ i, (A.chartLip i : ℝ≥0∞)^d) * (∑ j, (B.chartSymmLip j : ℝ≥0∞)^d)) ≠ ∞ := by
  apply ENNReal.mul_ne_top
  · exact ENNReal.sum_ne_top.mpr (fun i _ => ENNReal.pow_ne_top ENNReal.coe_ne_top)
  · exact ENNReal.sum_ne_top.mpr (fun i _ => ENNReal.pow_ne_top ENNReal.coe_ne_top)
end ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas

namespace ExpandedFA.PartIV.FractionalSobolev

theorem boundary_measure_equivalence :
    Specs.ExpandedFA.PartIV.FractionalSobolev.BoundaryMeasureEquivalence := by
  intro M _ _ _ _ d ι κ _ _ A B
  refine ⟨A.atlasMeasure_absolutelyContinuous_hausdorff,
    A.hausdorff_absolutelyContinuous_atlasMeasure, A.atlasMeasure_absolutelyContinuous B,
    B.atlasMeasure_absolutelyContinuous A, _, _,
    A.atlasMeasure_comparison_constant_finite B, B.atlasMeasure_comparison_constant_finite A,
    A.atlasMeasure_le_smul_atlasMeasure B, B.atlasMeasure_le_smul_atlasMeasure A⟩

end ExpandedFA.PartIV.FractionalSobolev

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators
namespace ExpandedFA.PartIV.FractionalSobolev.Boundary

section ChangeMeasureLp
variable {X : Type*} [MeasurableSpace X] {𝕜 : Type*} [RCLike 𝕜]
variable {μ ν : Measure X} (p : ℝ≥0∞) [Fact (1 ≤ p)]
variable {C : ℝ≥0∞} (hC : C ≠ ∞) (hμν : μ ≤ C • ν)

def changeMeasureLpLinear : Lp 𝕜 p ν →ₗ[𝕜] Lp 𝕜 p μ where
  toFun u := ((Lp.memLp u).of_measure_le_smul hC hμν).toLp u
  map_add' u v := by
    apply Lp.ext
    grw [MemLp.coeFn_toLp, Lp.coeFn_add, MemLp.coeFn_toLp, MemLp.coeFn_toLp]
    have hac : μ ≪ ν := Measure.absolutelyContinuous_of_le_smul hμν
    apply hac.ae_eq
    grw [Lp.coeFn_add]
  map_smul' c u := by
    apply Lp.ext
    grw [MemLp.coeFn_toLp, Lp.coeFn_smul, MemLp.coeFn_toLp]
    have hac : μ ≪ ν := Measure.absolutelyContinuous_of_le_smul hμν
    apply hac.ae_eq
    grw [Lp.coeFn_smul]
    rfl

lemma changeMeasureLpLinear_representative (u : Lp 𝕜 p ν) :
    changeMeasureLpLinear p hC hμν u =ᵐ[μ] u :=
  ((Lp.memLp u).of_measure_le_smul hC hμν).coeFn_toLp

lemma changeMeasureLpLinear_enorm_le (u : Lp 𝕜 p ν) :
    ‖changeMeasureLpLinear p hC hμν u‖ₑ ≤ C ^ (1 / p).toReal * ‖u‖ₑ := by
  simp only [Lp.enorm_def]
  rw [eLpNorm_congr_ae (changeMeasureLpLinear_representative p hC hμν u)]
  exact eLpNorm_le_of_measure_le_smul hμν

lemma changeMeasureLpLinear_norm_le (u : Lp 𝕜 p ν) :
    ‖changeMeasureLpLinear p hC hμν u‖ ≤ C.toReal ^ (1 / p).toReal * ‖u‖ := by
  simp only [← toReal_enorm]
  rw [ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
  grw [changeMeasureLpLinear_enorm_le]
  simp [ENNReal.mul_eq_top, hC]

variable {D : ℝ≥0∞} (hD : D ≠ ∞) (hνμ : ν ≤ D • μ)

lemma changeMeasureLpLinear_inverse (u : Lp 𝕜 p ν) :
    changeMeasureLpLinear p hD hνμ (changeMeasureLpLinear p hC hμν u) = u := by
  apply Lp.ext
  have hac : ν ≪ μ := Measure.absolutelyContinuous_of_le_smul hνμ
  exact (changeMeasureLpLinear_representative p hD hνμ _).trans
    (hac.ae_eq (changeMeasureLpLinear_representative p hC hμν u))

def changeMeasureLpLinearEquiv : Lp 𝕜 p ν ≃ₗ[𝕜] Lp 𝕜 p μ where
  toLinearMap := changeMeasureLpLinear p hC hμν
  invFun := changeMeasureLpLinear p hD hνμ
  left_inv := changeMeasureLpLinear_inverse p hC hμν hD hνμ
  right_inv := changeMeasureLpLinear_inverse p hD hνμ hC hμν

def changeMeasureLpContinuousLinearEquiv : Lp 𝕜 p ν ≃L[𝕜] Lp 𝕜 p μ :=
  (changeMeasureLpLinearEquiv (𝕜 := 𝕜) p hC hμν hD hνμ).toContinuousLinearEquivOfBounds
    (C.toReal ^ (1 / p).toReal) (D.toReal ^ (1 / p).toReal)
    (changeMeasureLpLinear_norm_le p hC hμν) (changeMeasureLpLinear_norm_le p hD hνμ)
end ChangeMeasureLp

end ExpandedFA.PartIV.FractionalSobolev.Boundary


open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators

namespace ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : FiniteAtlas M d ι)
variable {𝕜 : Type} [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]

lemma localizedLp_add (i : ι) (u v : Lp 𝕜 p A.atlasMeasure) :
    A.localizedLp p i (u+v) = A.localizedLp p i u + A.localizedLp p i v := by
  apply Lp.ext
  have hlocal := A.localizedRepresentative_congr_ae i (Lp.coeFn_add u v)
  filter_upwards [A.localizedLp_representative p i (u+v), A.localizedLp_representative p i u,
    A.localizedLp_representative p i v, Lp.coeFn_add (A.localizedLp p i u) (A.localizedLp p i v),
    hlocal] with x huv hu hv hadd hsum
  rw [huv, hadd]
  simp only [Pi.add_apply]
  rw [hu, hv, hsum]
  by_cases hx : x ∈ (A.chart i).target
  · simp only [localizedRepresentative, indicator_of_mem hx, Pi.add_apply, mul_add]
  · simp only [localizedRepresentative, indicator_of_notMem hx, add_zero]

lemma localizedLp_smul (i : ι) (c : 𝕜) (u : Lp 𝕜 p A.atlasMeasure) :
    A.localizedLp p i (c • u) = c • A.localizedLp p i u := by
  apply Lp.ext
  have hlocal := A.localizedRepresentative_congr_ae i (Lp.coeFn_smul c u)
  filter_upwards [A.localizedLp_representative p i (c • u), A.localizedLp_representative p i u,
    Lp.coeFn_smul c (A.localizedLp p i u), hlocal] with x hcu hu hsmul hlocalx
  rw [hcu, hsmul]
  simp only [Pi.smul_apply]
  rw [hu, hlocalx]
  by_cases hx : x ∈ (A.chart i).target
  · simp only [localizedRepresentative, indicator_of_mem hx, Pi.smul_apply, smul_eq_mul]
    ring
  · simp only [localizedRepresentative, indicator_of_notMem hx, smul_zero]

def localizer (i : ι) : Lp 𝕜 p A.atlasMeasure →ₗ[𝕜]
    Lp 𝕜 p (volume : Measure (Fin d → ℝ)) where
  toFun := A.localizedLp p i
  map_add' := A.localizedLp_add p i
  map_smul' := A.localizedLp_smul p i

end ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas

namespace ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : FiniteAtlas M d ι)
variable {𝕜 : Type} [RCLike 𝕜] (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]

def finiteEnergySubmodule (hp : p ≠ ∞) : Submodule 𝕜 (Lp 𝕜 p A.atlasMeasure) where
  carrier := {u | ∀ i, differenceEnergy s p (A.localizedLp p i u) < ∞}
  zero_mem' := by
    intro i
    change differenceEnergy s p ((A.localizer p i) 0) < ∞
    rw [map_zero]
    exact finite_energy_zero s p hp
  add_mem' := by
    intro u v hu hv i
    rw [A.localizedLp_add]
    exact finite_energy_add s p hp _ _ (hu i) (hv i)
  smul_mem' := by
    intro c u hu i
    rw [A.localizedLp_smul]
    exact finite_energy_smul s p hp c _ (hu i)

lemma fractionalNorm_nonneg (u : A.FractionalSpace 𝕜 s p) : 0 ≤ A.fractionalNorm s p u :=
  Finset.sum_nonneg fun i _ => ExpandedFA.PartIV.FractionalSobolev.fractionalNorm_nonneg s p _

lemma fractionalNorm_add_le (hp : p ≠ ∞) (u v : A.FractionalSpace 𝕜 s p) :
    A.fractionalNorm s p ⟨u.val + v.val,
      (A.finiteEnergySubmodule s p hp).add_mem u.property v.property⟩ ≤
      A.fractionalNorm s p u + A.fractionalNorm s p v := by
  classical
  unfold fractionalNorm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simpa only [A.localizedLp_add] using
    ExpandedFA.PartIV.FractionalSobolev.fractionalNorm_add_le s p hp
      ⟨A.localizedLp p i u.val, u.property i⟩ ⟨A.localizedLp p i v.val, v.property i⟩

lemma fractionalNorm_smul (hp : p ≠ ∞) (c : 𝕜) (u : A.FractionalSpace 𝕜 s p) :
    A.fractionalNorm s p ⟨c • u.val,
      (A.finiteEnergySubmodule s p hp).smul_mem c u.property⟩ =
      ‖c‖ * A.fractionalNorm s p u := by
  classical
  unfold fractionalNorm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [A.localizedLp_smul] using
    ExpandedFA.PartIV.FractionalSobolev.fractionalNorm_smul s p hp c
      ⟨A.localizedLp p i u.val, u.property i⟩

end ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas

namespace ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : FiniteAtlas M d ι)
variable {𝕜 : Type} [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]

lemma cutoff_product_ae_zero_of_localizedLp_zero
    (i : ι) (u : Lp 𝕜 p A.atlasMeasure) (hz : A.localizedLp p i u = 0) :
    (fun x => (A.cutoff i x : 𝕜) * u x) =ᵐ[A.atlasMeasure] 0 := by
  let P : M → 𝕜 := fun x => (A.cutoff i x : 𝕜) * u x
  have hPm : Measurable P :=
    (RCLike.continuous_ofReal.comp (A.cutoff_lipschitz i).continuous).measurable.mul
      (Lp.stronglyMeasurable u).measurable
  have hraw : A.localizedRepresentative i u =ᵐ[volume] 0 := by
    have hrep := A.localizedLp_representative p i u
    rw [hz] at hrep
    exact hrep.symm.trans (Lp.coeFn_zero 𝕜 p volume)
  have hchart : P =ᵐ[A.chartMeasure i] 0 := by
    apply (ae_map_iff ((A.chart i).continuousOn_symm.aemeasurable
      (A.chart i).open_target.measurableSet) (hPm (measurableSet_singleton 0))).mpr
    filter_upwards [hraw.restrict,
      self_mem_ae_restrict (A.chart i).open_target.measurableSet] with x hx hxV
    simpa only [localizedRepresentative, indicator_of_mem hxV, P, Pi.zero_apply, Set.mem_singleton_iff] using hx
  have hHlocal := (A.hausdorff_restrict_absolutelyContinuous_chartMeasure i).ae_eq hchart
  have hH : P =ᵐ[(MeasureTheory.Measure.hausdorffMeasure (d : ℝ) : Measure M)] 0 := by
    have hlocal := (ae_restrict_iff' (A.chart i).open_source.measurableSet).mp hHlocal
    filter_upwards [hlocal] with x hx
    by_cases hxS : x ∈ (A.chart i).source
    · exact hx hxS
    · have hc : A.cutoff i x = 0 := by
        by_contra hc
        exact hxS (A.cutoff_subordinate i (subset_tsupport (A.cutoff i) hc))
      simp [P, hc]
  exact A.atlasMeasure_absolutelyContinuous_hausdorff.ae_eq hH

lemma localizedLp_jointly_injective (u : Lp 𝕜 p A.atlasMeasure)
    (hz : ∀ i, A.localizedLp p i u = 0) : u = 0 := by
  classical
  apply Lp.ext
  have hall := ae_all_iff.mpr fun i => A.cutoff_product_ae_zero_of_localizedLp_zero p i u (hz i)
  filter_upwards [hall, Lp.coeFn_zero 𝕜 p A.atlasMeasure] with x hx hzero
  rw [hzero]
  change u x = 0
  have hsum : (∑ i, (A.cutoff i x : 𝕜) * u x) = 0 := Finset.sum_eq_zero fun i _ => hx i
  have hpartition : (∑ i, (A.cutoff i x : 𝕜)) = 1 := by
    exact_mod_cast A.cutoff_sum x
  rw [← Finset.sum_mul, hpartition, one_mul] at hsum
  exact hsum

end ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas

namespace ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : FiniteAtlas M d ι)
variable {𝕜 : Type} [RCLike 𝕜] (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]

lemma fractionalNorm_eq_zero_iff (hp : p ≠ ∞) (u : A.FractionalSpace 𝕜 s p) :
    A.fractionalNorm s p u = 0 ↔ u.val = 0 := by
  classical
  constructor
  · intro hz
    apply A.localizedLp_jointly_injective p u.val
    intro i
    apply (ExpandedFA.PartIV.FractionalSobolev.fractionalNorm_eq_zero_iff s p hp
      ⟨A.localizedLp p i u.val, u.property i⟩).mp
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => ExpandedFA.PartIV.FractionalSobolev.fractionalNorm_nonneg s p
        ⟨A.localizedLp p j u.val, u.property j⟩)).mp hz i (Finset.mem_univ i)
  · intro hz
    apply Finset.sum_eq_zero
    intro i _
    apply (ExpandedFA.PartIV.FractionalSobolev.fractionalNorm_eq_zero_iff s p hp
      ⟨A.localizedLp p i u.val, u.property i⟩).mpr
    change (A.localizer p i) u.val = 0
    rw [hz, map_zero]

section NormedStructure
variable [Fact (p ≠ ∞)]

instance fractionalAddCommGroup : AddCommGroup (A.FractionalSpace 𝕜 s p) :=
  inferInstanceAs (AddCommGroup (A.finiteEnergySubmodule (𝕜 := 𝕜) s p Fact.out))

instance fractionalModule : Module 𝕜 (A.FractionalSpace 𝕜 s p) :=
  inferInstanceAs (Module 𝕜 (A.finiteEnergySubmodule (𝕜 := 𝕜) s p Fact.out))


private theorem fractionalNormCore : NormedSpace.Core 𝕜 (A.FractionalSpace 𝕜 s p) where
  norm_nonneg := A.fractionalNorm_nonneg s p
  norm_smul := fun c u => A.fractionalNorm_smul s p Fact.out c u
  norm_triangle := fun u v => A.fractionalNorm_add_le s p Fact.out u v
  norm_eq_zero_iff u := (A.fractionalNorm_eq_zero_iff s p Fact.out u).trans
    ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

instance fractionalNormedAddCommGroup : NormedAddCommGroup (A.FractionalSpace 𝕜 s p) :=
  NormedAddCommGroup.ofCore (A.fractionalNormCore s p)

instance fractionalMetricSpace : MetricSpace (A.FractionalSpace 𝕜 s p) :=
  (A.fractionalNormedAddCommGroup s p).toMetricSpace

instance fractionalPseudoMetricSpace : PseudoMetricSpace (A.FractionalSpace 𝕜 s p) :=
  (A.fractionalNormedAddCommGroup s p).toMetricSpace.toPseudoMetricSpace

instance fractionalUniformSpace : UniformSpace (A.FractionalSpace 𝕜 s p) :=
  (A.fractionalNormedAddCommGroup s p).toMetricSpace.toPseudoMetricSpace.toUniformSpace

instance fractionalBornology : Bornology (A.FractionalSpace 𝕜 s p) :=
  (A.fractionalNormedAddCommGroup s p).toMetricSpace.toPseudoMetricSpace.toBornology

instance fractionalTopologicalSpace : TopologicalSpace (A.FractionalSpace 𝕜 s p) :=
  (A.fractionalNormedAddCommGroup s p).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

instance fractionalEDist : EDist (A.FractionalSpace 𝕜 s p) :=
  (A.fractionalNormedAddCommGroup s p).toMetricSpace.toPseudoMetricSpace.toEDist

instance fractionalPseudoEMetricSpace : PseudoEMetricSpace (A.FractionalSpace 𝕜 s p) :=
  (A.fractionalNormedAddCommGroup s p).toMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace

instance fractionalEMetricSpace : EMetricSpace (A.FractionalSpace 𝕜 s p) :=
  (A.fractionalNormedAddCommGroup s p).toMetricSpace.toEMetricSpace

instance fractionalNNDist : NNDist (A.FractionalSpace 𝕜 s p) :=
  (A.fractionalNormedAddCommGroup s p).toMetricSpace.toPseudoMetricSpace.toNNDist

instance fractionalNormedSpace : NormedSpace 𝕜 (A.FractionalSpace 𝕜 s p) :=
  NormedSpace.ofCore (A.fractionalNormCore s p)

end NormedStructure
end ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas


namespace ExpandedFA.PartIV.FractionalSobolev

theorem boundary_norm_formula : Specs.ExpandedFA.PartIV.FractionalSobolev.BoundaryNormFormula := by
  intro M _ _ _ _ d ι _ A 𝕜 _ s p _ u
  rfl

theorem boundary_full_norm_axioms :
    Specs.ExpandedFA.PartIV.FractionalSobolev.BoundaryFullNormAxioms := by
  intro M _ _ _ _ d ι _ A 𝕜 _ s p _ hp
  refine ⟨(A.finiteEnergySubmodule (𝕜 := 𝕜) s p hp).zero_mem, ?_⟩
  intro u v
  exact ⟨A.fractionalNorm_nonneg s p u, A.fractionalNorm_eq_zero_iff s p hp u,
    ⟨(A.finiteEnergySubmodule s p hp).add_mem u.property v.property,
      A.fractionalNorm_add_le s p hp u v⟩,
    fun c => ⟨(A.finiteEnergySubmodule s p hp).smul_mem c u.property,
      A.fractionalNorm_smul s p hp c u⟩⟩

end ExpandedFA.PartIV.FractionalSobolev


open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators

namespace ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
variable (A : Boundary.FiniteAtlas M d ι) (B : Boundary.FiniteAtlas M d κ)

/-- The actual change from A coordinates to B coordinates on their overlap. -/
def overlapChart (i : ι) (j : κ) :
    OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ) :=
  (A.chart i).symm.trans (B.chart j)

/-- A single term in the B-partition reconstruction of the A-localized piece. -/
def overlapRepresentative {𝕜 : Type} [RCLike 𝕜] (i : ι) (j : κ) (f : M → 𝕜) :
    (Fin d → ℝ) → 𝕜 :=
  (A.chart i).target.indicator fun x =>
    (B.cutoff j ((A.chart i).symm x) : 𝕜) *
      ((A.cutoff i ((A.chart i).symm x) : 𝕜) * f ((A.chart i).symm x))

lemma localizedRepresentative_reconstruction {𝕜 : Type} [RCLike 𝕜]
    (i : ι) (f : M → 𝕜) :
    A.localizedRepresentative i f = ∑ j, A.overlapRepresentative B i j f := by
  classical
  funext x
  by_cases hx : x ∈ (A.chart i).target
  · simp only [localizedRepresentative, overlapRepresentative, Finset.sum_apply,
      indicator_of_mem hx]
    rw [← Finset.sum_mul]
    have hc : (∑ j, (B.cutoff j ((A.chart i).symm x) : 𝕜)) = 1 := by
      rw [← map_sum (algebraMap ℝ 𝕜), B.cutoff_sum]
      exact map_one _
    rw [hc, one_mul]
  · simp only [localizedRepresentative, overlapRepresentative, Finset.sum_apply,
      indicator_of_notMem hx, Finset.sum_const_zero]

lemma overlapRepresentative_support_subset {𝕜 : Type} [RCLike 𝕜]
    (i : ι) (j : κ) (f : M → 𝕜) :
    Function.support (A.overlapRepresentative B i j f) ⊆
      (A.chart i) '' (tsupport (A.cutoff i) ∩ tsupport (B.cutoff j)) := by
  intro x hx
  have hxV : x ∈ (A.chart i).target := by
    by_contra hxV
    simp [overlapRepresentative, hxV] at hx
  have hA : A.cutoff i ((A.chart i).symm x) ≠ 0 := by
    intro hz
    simp [overlapRepresentative, hxV, hz] at hx
  have hB : B.cutoff j ((A.chart i).symm x) ≠ 0 := by
    intro hz
    simp [overlapRepresentative, hxV, hz] at hx
  exact ⟨(A.chart i).symm x,
    ⟨subset_tsupport (A.cutoff i) hA, subset_tsupport (B.cutoff j) hB⟩,
    (A.chart i).right_inv hxV⟩

lemma overlapCutoffImage_subset_source (i : ι) (j : κ) :
    (A.chart i) '' (tsupport (A.cutoff i) ∩ tsupport (B.cutoff j)) ⊆
      (A.overlapChart B i j).source := by
  rintro _ ⟨x, hx, rfl⟩
  rw [overlapChart, OpenPartialHomeomorph.trans_source]
  change A.chart i x ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' (B.chart j).source
  have hAx := A.cutoff_subordinate i hx.1
  exact ⟨(A.chart i).map_source hAx, by
    change (A.chart i).symm ((A.chart i) x) ∈ (B.chart j).source
    rw [(A.chart i).left_inv hAx]
    exact B.cutoff_subordinate j hx.2⟩

lemma overlapCutoffImage_isCompact [CompactSpace M] (i : ι) (j : κ) :
    IsCompact ((A.chart i) '' (tsupport (A.cutoff i) ∩ tsupport (B.cutoff j))) := by
  apply ((HasCompactSupport.of_compactSpace (A.cutoff i)).isCompact.inter_right
    (isClosed_tsupport _)).image_of_continuousOn
  exact (A.chart i).continuousOn.mono (fun x hx => A.cutoff_subordinate i hx.1)

lemma overlapChart_lipschitz (i : ι) (j : κ) :
    LipschitzOnWith (B.chartLip j * A.chartSymmLip i)
      (A.overlapChart B i j) (A.overlapChart B i j).source := by
  change LipschitzOnWith _ (fun x => (B.chart j) ((A.chart i).symm x)) _
  apply (B.chart_lipschitz j).comp ((A.chartSymm_lipschitz i).mono ?_) ?_
  · intro x hx
    exact hx.1
  · intro x hx
    exact hx.2

lemma overlapChart_symm_lipschitz (i : ι) (j : κ) :
    LipschitzOnWith (A.chartLip i * B.chartSymmLip j)
      (A.overlapChart B i j).symm (A.overlapChart B i j).target := by
  change LipschitzOnWith _ (fun x => (A.chart i) ((B.chart j).symm x)) _
  apply (A.chart_lipschitz i).comp ((B.chartSymm_lipschitz j).mono ?_) ?_
  · intro x hx
    exact hx.1
  · intro x hx
    exact hx.2

/-- A bounded Lipschitz extension of the A cutoff in B coordinates. -/
lemma exists_overlapMultiplier (i : ι) (j : κ) :
    ∃ a : (Fin d → ℝ) → ℝ,
      LipschitzWith (A.cutoffLip i * B.chartSymmLip j) a ∧
      (∀ x, 0 ≤ a x ∧ a x ≤ 1) ∧
      EqOn (fun x => A.cutoff i ((B.chart j).symm x)) a (B.chart j).target := by
  have hLip := (A.cutoff_lipschitz i).comp_lipschitzOnWith (B.chartSymm_lipschitz j)
  obtain ⟨a,ha,hea⟩ := hLip.extend_real
  refine ⟨fun x => max 0 (min (a x) 1), ?_, ?_, ?_⟩
  · simpa only [max_self, max_eq_right (show (0:ℝ≥0) ≤ _ from bot_le),
      max_eq_left (show (0:ℝ≥0) ≤ _ from bot_le)] using
      (LipschitzWith.const (0:ℝ)).max (ha.min (LipschitzWith.const (1:ℝ)))
  · intro x
    exact ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  · intro x hx
    dsimp only
    rw [← hea hx]
    dsimp only [Function.comp_apply]
    rw [min_eq_left (A.cutoff_le_one i _), max_eq_right (A.cutoff_nonneg i _)]

end ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas

namespace ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
variable (A : Boundary.FiniteAtlas M d ι) (B : Boundary.FiniteAtlas M d κ)

lemma chart_indicator_comp_measurable {𝕜 : Type} [RCLike 𝕜]
    (e : OpenPartialHomeomorph M (Fin d → ℝ)) (f : M → 𝕜) (hf : Measurable f) :
    Measurable (e.target.indicator (fun x => f (e.symm x))) := by
  classical
  apply measurable_of_restrict_of_restrict_compl e.open_target.measurableSet
  · have hsymm : Measurable (e.target.domRestrict e.symm) :=
      (continuousOn_iff_continuous_domRestrict.mp e.continuousOn_symm).measurable
    convert hf.comp hsymm using 1
    funext x
    simp only [domRestrict_apply, Function.comp_apply, indicator_of_mem x.property]
  · have he : e.targetᶜ.domRestrict (e.target.indicator (fun x => f (e.symm x))) =
        fun _ => (0:𝕜) := by
      funext x
      simp only [domRestrict_apply, indicator_of_notMem x.property]
    rw [he]
    exact measurable_const

lemma localizedRepresentative_measurable {𝕜 : Type} [RCLike 𝕜]
    (i : ι) (f : M → 𝕜) (hf : Measurable f) :
    Measurable (A.localizedRepresentative i f) := by
  exact chart_indicator_comp_measurable (A.chart i) _
    ((RCLike.continuous_ofReal.measurable.comp (A.cutoff_lipschitz i).continuous.measurable).mul hf)

lemma overlapRepresentative_measurable {𝕜 : Type} [RCLike 𝕜]
    (i : ι) (j : κ) (f : M → 𝕜) (hf : Measurable f) :
    Measurable (A.overlapRepresentative B i j f) := by
  exact chart_indicator_comp_measurable (A.chart i) _
    ((RCLike.continuous_ofReal.measurable.comp (B.cutoff_lipschitz j).continuous.measurable).mul
      ((RCLike.continuous_ofReal.measurable.comp (A.cutoff_lipschitz i).continuous.measurable).mul hf))

lemma overlapRepresentative_eqOn {𝕜 : Type} [RCLike 𝕜]
    (i : ι) (j : κ) (f : M → 𝕜) (a : (Fin d → ℝ) → ℝ)
    (ha : EqOn (fun x => A.cutoff i ((B.chart j).symm x)) a (B.chart j).target) :
    EqOn (A.overlapRepresentative B i j f)
      ((fun y => (a y:𝕜) * B.localizedRepresentative j f y) ∘ (A.overlapChart B i j))
      (A.overlapChart B i j).source := by
  intro x hx
  have hxA : x ∈ (A.chart i).target := hx.1
  have hxB : (A.chart i).symm x ∈ (B.chart j).source := hx.2
  have hxBT : (B.chart j) ((A.chart i).symm x) ∈ (B.chart j).target :=
    (B.chart j).map_source hxB
  dsimp only [Function.comp_apply]
  change A.overlapRepresentative B i j f x =
    (a ((B.chart j) ((A.chart i).symm x)):𝕜) *
      B.localizedRepresentative j f ((B.chart j) ((A.chart i).symm x))
  rw [← ha hxBT]
  simp only [overlapRepresentative, localizedRepresentative, indicator_of_mem hxA,
    indicator_of_mem hxBT, (B.chart j).left_inv hxB]
  ring

end ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas

namespace ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas
open Transport

lemma rawDoubleEnergyOn_le_whole {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) (Ω : Set (Fin d → ℝ)) (f : (Fin d → ℝ) → 𝕜) :
    rawDoubleEnergyOn s p Ω f ≤ rawDoubleEnergy s p f := by
  apply lintegral_mono' Measure.restrict_le_self
  intro x
  exact lintegral_mono' Measure.restrict_le_self le_rfl

lemma rawDoubleEnergyOn_congr_eqOn {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) (Ω : Set (Fin d → ℝ)) (hΩ : MeasurableSet Ω)
    (f g : (Fin d → ℝ) → 𝕜) (he : EqOn f g Ω) :
    rawDoubleEnergyOn s p Ω f = rawDoubleEnergyOn s p Ω g := by
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hΩ] with x hx
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hΩ] with y hy
  rw [he hx, he hy]

/-- Compactly supported local coordinate pullback preserves finite energy.
Only geometric Lipschitz bounds and genuine inverse equations enter. -/
lemma compact_overlap_pullback_finite_energy {𝕜 : Type} [RCLike 𝕜]
    {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞)
    (e : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ))
    (K K' : ℝ≥0) (he : LipschitzOnWith K e e.source)
    (he' : LipschitzOnWith K' e.symm e.target)
    (F G : (Fin d → ℝ) → 𝕜) (hF : Measurable F) (hG : Measurable G)
    (heq : EqOn G (F ∘ e) e.source)
    (S : Set (Fin d → ℝ)) (hS : IsCompact S) (hSe : S ⊆ e.source)
    (hGS : Function.support G ⊆ S)
    (hmass : (∫⁻ x, ‖F x‖ₑ ^ p.toReal) < ∞)
    (henergy : rawDoubleEnergy s p F < ∞) :
    rawDoubleEnergy s p G < ∞ := by
  have hfg : ∀ x ∈ e.source, e x ∈ e.target ∧ e.symm (e x) = x :=
    fun x hx => ⟨e.map_source hx,e.left_inv hx⟩
  have hgf : ∀ y ∈ e.target, e.symm y ∈ e.source ∧ e (e.symm y) = y :=
    fun y hy => ⟨e.map_target hy,e.right_inv hy⟩
  obtain ⟨C,hC,hCE⟩ := Transport.local_biLipschitz_energy_bound (𝕜 := 𝕜)
    e.open_source.measurableSet e.open_target.measurableSet he he' hfg hgf s hs0 p
  have hE : rawDoubleEnergyOn s p e.source G < ∞ := by
    rw [rawDoubleEnergyOn_congr_eqOn s p _ e.open_source.measurableSet G (F ∘ e) heq]
    apply lt_of_le_of_lt (hCE F hF)
    apply ENNReal.mul_lt_top hC.lt_top
    exact (rawDoubleEnergyOn_le_whole s p e.target F).trans_lt henergy
  have hvol := map_restrict_volume_le e.open_source.measurableSet e.open_target.measurableSet
    e.continuousOn he' hfg hgf
  have hmass' : (∫⁻ x in e.source, ‖G x‖ₑ ^ p.toReal) < ∞ := by
    have hEq : (∫⁻ x in e.source, ‖G x‖ₑ ^ p.toReal) =
        ∫⁻ x in e.source, ‖F (e x)‖ₑ ^ p.toReal := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem e.open_source.measurableSet] with x hx
      rw [heq hx]
      rfl
    rw [hEq]
    apply lt_of_le_of_lt
      (lintegral_comp_le_of_measurable (e.continuousOn.aemeasurable e.open_source.measurableSet)
        hvol (hF.enorm.pow_const _))
    apply ENNReal.mul_lt_top (ENNReal.pow_ne_top ENNReal.coe_ne_top).lt_top
    exact (lintegral_mono' Measure.restrict_le_self le_rfl).trans_lt hmass
  exact compact_support_zeroExtension_finite_energy s p hs0 hs1 hp e.source e.open_source
    G hG S hS hSe hGS hmass' hE

end ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas

namespace ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
variable (A : Boundary.FiniteAtlas M d ι) (B : Boundary.FiniteAtlas M d κ)

/-- An actual overlap-localized boundary piece has finite Euclidean energy
whenever the source-atlas localized piece does. This includes both cutoff
multiplication and compactly supported zero extension across the overlap edge. -/
theorem overlapRepresentative_finite_energy {𝕜 : Type} [RCLike 𝕜]
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞)
    (i : ι) (j : κ) (u : B.FractionalSpace 𝕜 s p) :
    Transport.rawDoubleEnergy s p (A.overlapRepresentative B i j u.val) < ∞ := by
  obtain ⟨a,ha,hab,haeq⟩ := A.exists_overlapMultiplier B i j
  let L : ℝ≥0 := A.cutoffLip i * B.chartSymmLip j
  let aK : (Fin d → ℝ) → 𝕜 := fun x => a x
  have hbound : ∀ x, ‖aK x‖ ≤ (1:ℝ≥0) := by
    intro x
    simpa only [aK, RCLike.norm_ofReal, abs_of_nonneg (hab x).1, NNReal.coe_one] using (hab x).2
  have hLip : ∀ x y, ‖aK x-aK y‖ ≤ L * euclideanLength (x-y) := by
    intro x y
    change ‖(a x:𝕜)-(a y:𝕜)‖ ≤ _
    rw [← RCLike.ofReal_sub, RCLike.norm_ofReal]
    have hb := ha.norm_sub_le x y
    rw [Real.norm_eq_abs] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (norm_le_euclideanLength (x-y)) L.coe_nonneg)
  let vB : ExpandedFA.PartIV.FractionalSobolev.FractionalSpace 𝕜 d s p :=
    ⟨B.localizedLp p j u.val,u.property j⟩
  let v := fractionalMultiply s p hs0 hs1 hp aK 1 L hbound hLip vB
  let F := fun x => aK x * B.localizedRepresentative j u.val x
  have hrep : v.val =ᵐ[volume] F := by
    filter_upwards [fractionalMultiply_representative s p hs0 hs1 hp aK 1 L hbound hLip vB,
      B.localizedLp_representative p j u.val] with x hx hb
    dsimp [vB] at hx
    rw [hx,hb]
  have hFM : MemLp F p volume := (memLp_congr_ae hrep).mp (Lp.memLp v.val)
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hmass : (∫⁻ x, ‖F x‖ₑ ^ p.toReal) < ∞ :=
    lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp hFM.eLpNorm_lt_top
  have hFenergy : Transport.rawDoubleEnergy s p F < ∞ := by
    rw [← Transport.rawDoubleEnergy_congr s p hrep]
    change doubleEnergy s p v.val < ∞
    rw [← difference_energy_double_integral 𝕜 d s p v.val]
    exact v.property
  have hFmeas : Measurable F :=
    (RCLike.continuous_ofReal.comp ha.continuous).measurable.mul
      (B.localizedRepresentative_measurable j u.val (Lp.stronglyMeasurable u.val).measurable)
  exact compact_overlap_pullback_finite_energy s p hs0 hs1 hp (A.overlapChart B i j)
    _ _ (A.overlapChart_lipschitz B i j) (A.overlapChart_symm_lipschitz B i j)
    F (A.overlapRepresentative B i j u.val) hFmeas
    (A.overlapRepresentative_measurable B i j u.val (Lp.stronglyMeasurable u.val).measurable)
    (A.overlapRepresentative_eqOn B i j u.val a haeq)
    _ (A.overlapCutoffImage_isCompact B i j) (A.overlapCutoffImage_subset_source B i j)
    (A.overlapRepresentative_support_subset B i j u.val) hmass hFenergy

end ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas

namespace ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas
open Transport

/-- The extended full norm of a measurable Euclidean representative. -/
def rawFullNorm {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (s : ℝ) (p : ℝ≥0∞)
    (f : (Fin d → ℝ) → 𝕜) : ℝ≥0∞ :=
  (∫⁻ x, ‖f x‖ₑ ^ p.toReal) ^ (1 / p.toReal) +
    rawDoubleEnergy s p f ^ (1 / p.toReal)

/-- Quantitative overlap transport including the chart-edge zero extension.
The finite constant is fixed before either function is supplied. -/
theorem compact_overlap_pullback_rawNorm_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞)
    (e : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ))
    (K K' : ℝ≥0) (he : LipschitzOnWith K e e.source)
    (he' : LipschitzOnWith K' e.symm e.target)
    (S : Set (Fin d → ℝ)) (hS : IsCompact S) (hSe : S ⊆ e.source) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ F G : (Fin d → ℝ) → 𝕜,
      Measurable F → Measurable G → EqOn G (F ∘ e) e.source →
      Function.support G ⊆ S → rawFullNorm s p G ≤ C * rawFullNorm s p F := by
  have hfg : ∀ x ∈ e.source, e x ∈ e.target ∧ e.symm (e x) = x :=
    fun x hx => ⟨e.map_source hx,e.left_inv hx⟩
  have hgf : ∀ y ∈ e.target, e.symm y ∈ e.source ∧ e (e.symm y) = y :=
    fun y hy => ⟨e.map_target hy,e.right_inv hy⟩
  obtain ⟨CE,hCE,henergy⟩ := Transport.local_biLipschitz_energy_bound (𝕜 := 𝕜)
    e.open_source.measurableSet e.open_target.measurableSet he he' hfg hgf s hs0 p
  obtain ⟨δ,hδ,hsep⟩ := compact_chart_support_separation S e.source hS e.open_source hSe
  let q : ℝ := 1 / p.toReal
  have hq : 0 ≤ q := by dsimp [q]; positivity
  let CM : ℝ≥0∞ := (K' : ℝ≥0∞)^d
  let CT : ℝ≥0∞ := 2 * kernelTail (d := d) s p δ
  have hCM : CM ≠ ∞ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hCT : CT ≠ ∞ := by
    dsimp [CT]
    exact ENNReal.mul_ne_top (by norm_num) (kernelTail_lt_top s p hs0 hs1 hp hδ).ne
  let C : ℝ≥0∞ := CM^q + CE^q + CT^q*CM^q
  have hC : C ≠ ∞ := by
    dsimp [C]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
      ⟨ENNReal.rpow_ne_top_of_nonneg hq hCM, ENNReal.rpow_ne_top_of_nonneg hq hCE⟩,
      ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hq hCT)
        (ENNReal.rpow_ne_top_of_nonneg hq hCM)⟩
  refine ⟨C,hC,?_⟩
  intro F G hF hG heq hGS
  have hzero : ∀ x ∉ e.source, G x = 0 := by
    intro x hx
    by_contra hGx
    exact hx (hSe (hGS hGx))
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hmassEq : (∫⁻ x, ‖G x‖ₑ ^ p.toReal) = ∫⁻ x in e.source, ‖G x‖ₑ ^ p.toReal := by
    rw [← lintegral_add_compl (fun x => ‖G x‖ₑ ^ p.toReal) e.open_source.measurableSet]
    have hz : (∫⁻ x in e.sourceᶜ, ‖G x‖ₑ ^ p.toReal) = 0 := by
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [ae_restrict_mem e.open_source.measurableSet.compl] with x hx
      simp only [hzero x hx, enorm_zero, ENNReal.zero_rpow_of_pos hpr, Pi.zero_apply]
    rw [hz,add_zero]
  have hmassG : (∫⁻ x in e.source, ‖G x‖ₑ ^ p.toReal) ≤ CM * ∫⁻ x, ‖F x‖ₑ ^ p.toReal := by
    have hvol := map_restrict_volume_le e.open_source.measurableSet e.open_target.measurableSet
      e.continuousOn he' hfg hgf
    have hEq : (∫⁻ x in e.source, ‖G x‖ₑ ^ p.toReal) =
        ∫⁻ x in e.source, ‖F (e x)‖ₑ ^ p.toReal := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem e.open_source.measurableSet] with x hx
      rw [heq hx]
      rfl
    rw [hEq]
    exact (lintegral_comp_le_of_measurable
      (e.continuousOn.aemeasurable e.open_source.measurableSet) hvol (hF.enorm.pow_const _)).trans
        (mul_le_mul' le_rfl (lintegral_mono' Measure.restrict_le_self le_rfl))
  have henergyG : rawDoubleEnergyOn s p e.source G ≤ CE * rawDoubleEnergy s p F := by
    rw [rawDoubleEnergyOn_congr_eqOn s p _ e.open_source.measurableSet G (F ∘ e) heq]
    exact (henergy F hF).trans (mul_le_mul' le_rfl (rawDoubleEnergyOn_le_whole s p e.target F))
  have hmassPow : (∫⁻ x, ‖G x‖ₑ ^ p.toReal)^q ≤ CM^q * (∫⁻ x, ‖F x‖ₑ ^ p.toReal)^q := by
    rw [hmassEq]
    simpa only [ENNReal.mul_rpow_of_nonneg _ _ hq] using ENNReal.rpow_le_rpow hmassG hq
  have henergyPow : rawDoubleEnergy s p G ^ q ≤
      CE^q * rawDoubleEnergy s p F ^ q + CT^q*CM^q * (∫⁻ x, ‖F x‖ₑ ^ p.toReal)^q := by
    have hle := local_zeroExtension_seminorm_le s p hp e.source e.open_source.measurableSet
      G hG hzero δ (fun x _ hGx => hsep x (hGS hGx))
    change rawDoubleEnergy s p G ^ q ≤ _ at hle
    apply hle.trans
    have hepow := ENNReal.rpow_le_rpow henergyG hq
    have hmpow := ENNReal.rpow_le_rpow hmassG hq
    simp only [ENNReal.mul_rpow_of_nonneg _ _ hq] at hepow hmpow
    exact add_le_add hepow (by simpa only [mul_assoc] using mul_le_mul' le_rfl hmpow)
  unfold rawFullNorm
  change (∫⁻ x, ‖G x‖ₑ ^ p.toReal)^q + rawDoubleEnergy s p G ^ q ≤
    C * ((∫⁻ x, ‖F x‖ₑ ^ p.toReal)^q + rawDoubleEnergy s p F ^ q)
  calc
    _ ≤ CM^q * (∫⁻ x, ‖F x‖ₑ ^ p.toReal)^q +
        (CE^q * rawDoubleEnergy s p F ^ q + CT^q*CM^q * (∫⁻ x, ‖F x‖ₑ ^ p.toReal)^q) :=
      add_le_add hmassPow henergyPow
    _ = (CM^q+CT^q*CM^q)*(∫⁻ x, ‖F x‖ₑ ^ p.toReal)^q + CE^q*rawDoubleEnergy s p F^q := by ring
    _ ≤ C*(∫⁻ x, ‖F x‖ₑ ^ p.toReal)^q + C*rawDoubleEnergy s p F^q := by
      apply add_le_add <;> apply mul_le_mul' _ le_rfl
      · dsimp [C]
        calc
          _ ≤ (CM^q+CT^q*CM^q)+CE^q := le_self_add
          _ = _ := by ring
      · dsimp [C]
        exact le_trans (le_add_of_nonneg_left zero_le) le_self_add
    _ = _ := (mul_add _ _ _).symm

end ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas

namespace ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas
open Transport

lemma rawFullNorm_congr_ae {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) {f g : (Fin d → ℝ) → 𝕜} (hfg : f =ᵐ[volume] g) :
    rawFullNorm s p f = rawFullNorm s p g := by
  unfold rawFullNorm
  rw [rawDoubleEnergy_congr s p hfg]
  congr 2
  apply lintegral_congr_ae
  filter_upwards [hfg] with x hx
  rw [hx]

lemma rawFullNorm_eq_ofReal_fractionalNorm {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (v : ExpandedFA.PartIV.FractionalSobolev.FractionalSpace 𝕜 d s p) :
    rawFullNorm s p v.val = ENNReal.ofReal (ExpandedFA.PartIV.FractionalSobolev.fractionalNorm s p v) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hq : 0 ≤ 1 / p.toReal := by positivity
  have hm : (∫⁻ x, ‖v.val x‖ₑ ^ p.toReal) ^ (1/p.toReal) = ‖v.val‖ₑ := by
    rw [Lp.enorm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp (Lp.aestronglyMeasurable v.val)]
  have he : rawDoubleEnergy s p v.val = differenceEnergy s p v.val :=
    (difference_energy_double_integral 𝕜 d s p v.val).symm
  unfold rawFullNorm ExpandedFA.PartIV.FractionalSobolev.fractionalNorm
  rw [hm,he, ENNReal.ofReal_add (norm_nonneg _) (Real.rpow_nonneg ENNReal.toReal_nonneg _), ofReal_norm,
    ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hq,
    ENNReal.ofReal_toReal v.property.ne]

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
variable (A : Boundary.FiniteAtlas M d ι) (B : Boundary.FiniteAtlas M d κ)

/-- A genuine chart-overlap localization estimate. The finite constant depends
only on the two charts, their cutoffs, s and p, and is fixed before the input
boundary function is supplied. -/
theorem overlapRepresentative_rawNorm_bound {𝕜 : Type} [RCLike 𝕜]
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞)
    (i : ι) (j : κ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ u : B.FractionalSpace 𝕜 s p,
      rawFullNorm s p (A.overlapRepresentative B i j u.val) ≤ C *
        ENNReal.ofReal (ExpandedFA.PartIV.FractionalSobolev.fractionalNorm s p
          ⟨B.localizedLp p j u.val,u.property j⟩) := by
  obtain ⟨a,ha,hab,haeq⟩ := A.exists_overlapMultiplier B i j
  let L : ℝ≥0 := A.cutoffLip i * B.chartSymmLip j
  let aK : (Fin d → ℝ) → 𝕜 := fun x => a x
  have hbound : ∀ x, ‖aK x‖ ≤ (1:ℝ≥0) := by
    intro x
    simpa only [aK, RCLike.norm_ofReal, abs_of_nonneg (hab x).1, NNReal.coe_one] using (hab x).2
  have hLip : ∀ x y, ‖aK x-aK y‖ ≤ L * euclideanLength (x-y) := by
    intro x y
    change ‖(a x:𝕜)-(a y:𝕜)‖ ≤ _
    rw [← RCLike.ofReal_sub, RCLike.norm_ofReal]
    have hb := ha.norm_sub_le x y
    rw [Real.norm_eq_abs] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (norm_le_euclideanLength (x-y)) L.coe_nonneg)
  obtain ⟨C,hC,htrans⟩ := compact_overlap_pullback_rawNorm_bound (𝕜:=𝕜) s p hs0 hs1 hp
    (A.overlapChart B i j) _ _ (A.overlapChart_lipschitz B i j) (A.overlapChart_symm_lipschitz B i j)
    _ (A.overlapCutoffImage_isCompact B i j) (A.overlapCutoffImage_subset_source B i j)
  let CP := ENNReal.ofReal (multiplierBound (d:=d) s p 1 L)
  refine ⟨C*CP, ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top, ?_⟩
  intro u
  let vB : ExpandedFA.PartIV.FractionalSobolev.FractionalSpace 𝕜 d s p :=
    ⟨B.localizedLp p j u.val,u.property j⟩
  let v := fractionalMultiply s p hs0 hs1 hp aK 1 L hbound hLip vB
  let F := fun x => aK x * B.localizedRepresentative j u.val x
  have hrep : v.val =ᵐ[volume] F := by
    filter_upwards [fractionalMultiply_representative s p hs0 hs1 hp aK 1 L hbound hLip vB,
      B.localizedLp_representative p j u.val] with x hx hb
    dsimp [vB] at hx
    rw [hx,hb]
  have hFmeas : Measurable F :=
    (RCLike.continuous_ofReal.comp ha.continuous).measurable.mul
      (B.localizedRepresentative_measurable j u.val (Lp.stronglyMeasurable u.val).measurable)
  have hb := htrans F (A.overlapRepresentative B i j u.val) hFmeas
    (A.overlapRepresentative_measurable B i j u.val (Lp.stronglyMeasurable u.val).measurable)
    (A.overlapRepresentative_eqOn B i j u.val a haeq)
    (A.overlapRepresentative_support_subset B i j u.val)
  have hmul : rawFullNorm s p F ≤ CP * ENNReal.ofReal
      (ExpandedFA.PartIV.FractionalSobolev.fractionalNorm s p vB) := by
    rw [← rawFullNorm_congr_ae s p hrep, rawFullNorm_eq_ofReal_fractionalNorm s p hp]
    dsimp [CP]
    rw [← ENNReal.ofReal_mul (multiplierBound_nonneg s p 1 L)]
    exact ENNReal.ofReal_le_ofReal (fractionalMultiply_norm_le s p hs0 hs1 hp aK 1 L hbound hLip vB)
  exact hb.trans (by simpa only [mul_assoc] using mul_le_mul' le_rfl hmul)

end ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal
namespace ExpandedFA.PartIV.FractionalSobolev.Boundary
open ExpandedFA.Distributions
lemma test_lipschitz {n : ℕ} {Ω : Opens (Domain n)} (φ : Tests ℝ Ω) :
    ∃ L : ℝ≥0, LipschitzWith L φ := by
  obtain ⟨C,hC⟩ := (φ.contDiff.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (φ.hasCompactSupport.fderiv ℝ)
  let L : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  refine ⟨L, lipschitzWith_of_nnnorm_fderiv_le (φ.contDiff.differentiable (by simp)) ?_⟩
  intro x
  exact_mod_cast (hC x).trans (le_max_left C 0)
/-- A compact Euclidean set admits a finite family of globally smooth,
compactly supported, globally Lipschitz cutoffs subordinate to an open cover. -/
lemma finite_lipschitz_cutoffs {n : ℕ} (Ω : Opens (Domain n))
    (K : Set (Domain n)) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (ι : Type) (U : ι → Set (Domain n)) (hU : ∀ i, IsOpen (U i))
    (hcover : (Ω : Set (Domain n)) ⊆ ⋃ i, U i) :
    ∃ (κ : Type), Finite κ ∧ ∃ φ : κ → Tests ℝ Ω,
      (∀ k, ∃ L : ℝ≥0, LipschitzWith L (φ k)) ∧
      (∀ k x, 0 ≤ φ k x) ∧
      (∀ x ∈ K, ∑ᶠ k, φ k x = 1) ∧
      (∀ k, ∃ i, tsupport (φ k) ⊆ U i) := by
  classical
  obtain ⟨κ, _, φ, hnonneg, hlocal, hsum, hsub⟩ :=
    ExpandedFA.Distributions.smooth_partition_of_unity n Ω ι U hU hcover
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let c : K → Ω := fun x => ⟨x.val, hKΩ x.property⟩
  have hc : Continuous c := continuous_subtype_val.subtype_mk _
  have hfinite := hlocal.finite_nonempty_inter_compact (isCompact_range hc)
  let t := hfinite.toFinset
  let η : t → Tests ℝ Ω := fun k => φ k.val
  refine ⟨t, inferInstance, η, ?_, ?_, ?_, ?_⟩
  · intro k
    exact test_lipschitz (η k)
  · intro k x
    exact hnonneg k.val x
  · intro x hx
    have hsupport : Function.support (fun k => φ k x) ⊆ (t : Set κ) := by
      intro k hk
      apply hfinite.mem_toFinset.mpr
      refine ⟨⟨x, hKΩ hx⟩, subset_tsupport (φ k) hk, ?_⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    change (∑ᶠ k : t, φ k.val x) = 1
    rw [finsum_eq_sum_of_fintype]
    rw [Finset.sum_coe_sort t (fun k : κ => φ k x),
      ← finsum_eq_sum_of_support_subset _ hsupport]
    exact hsum x (hKΩ hx)
  · intro k
    exact hsub k.val

end ExpandedFA.PartIV.FractionalSobolev.Boundary

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators

namespace ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
variable (A : Boundary.FiniteAtlas M d ι) (B : Boundary.FiniteAtlas M d κ)

lemma localizedRepresentative_memLp_of_memLp {𝕜 : Type} [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : ι) {f : M → 𝕜} (hf : MemLp f p A.atlasMeasure) :
    MemLp (A.localizedRepresentative i f) p volume := by
  let u := hf.toLp f
  have hrep := A.localizedRepresentative_congr_ae i hf.coeFn_toLp
  exact (memLp_congr_ae hrep).mp (A.localizedRepresentative_memLp p i u)

lemma overlapRepresentative_memLp {𝕜 : Type} [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : ι) (j : κ)
    (u : Lp 𝕜 p B.atlasMeasure) : MemLp (A.overlapRepresentative B i j u) p volume := by
  have hMemA : MemLp u p A.atlasMeasure :=
    (Lp.memLp u).of_measure_le_smul (A.atlasMeasure_comparison_constant_finite B)
      (A.atlasMeasure_le_smul_atlasMeasure B)
  apply MemLp.of_le_mul (A.localizedRepresentative_memLp_of_memLp p i hMemA)
    (A.overlapRepresentative_measurable B i j u (Lp.stronglyMeasurable u).measurable).stronglyMeasurable.aestronglyMeasurable
    (c := 1)
  filter_upwards with x
  by_cases hx : x ∈ (A.chart i).target
  · simp only [overlapRepresentative, localizedRepresentative, indicator_of_mem hx, one_mul,
      norm_mul, RCLike.norm_ofReal, abs_of_nonneg (B.cutoff_nonneg j _),
      abs_of_nonneg (A.cutoff_nonneg i _)]
    exact mul_le_of_le_one_left (mul_nonneg (A.cutoff_nonneg i _) (norm_nonneg _))
      (B.cutoff_le_one j _)
  · simp [overlapRepresentative, localizedRepresentative, hx]

lemma localizedLp_finite_energy_of_atlas [CompactSpace M] {𝕜 : Type} [RCLike 𝕜]
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞)
    (u : B.FractionalSpace 𝕜 s p) (v : Lp 𝕜 p A.atlasMeasure)
    (hvu : v =ᵐ[A.atlasMeasure] u.val) (i : ι) :
    differenceEnergy s p (A.localizedLp p i v) < ∞ := by
  classical
  let hMem := fun j => A.overlapRepresentative_memLp B p i j u.val
  let w : κ → Lp 𝕜 p (volume : Measure (Fin d → ℝ)) :=
    fun j => (hMem j).toLp (A.overlapRepresentative B i j u.val)
  have hw (j : κ) : w j =ᵐ[volume] A.overlapRepresentative B i j u.val :=
    (hMem j).coeFn_toLp
  have hwenergy (j : κ) : differenceEnergy s p (w j) < ∞ := by
    rw [difference_energy_double_integral]
    change Transport.rawDoubleEnergy s p (w j) < ∞
    rw [Transport.rawDoubleEnergy_congr s p (hw j)]
    exact A.overlapRepresentative_finite_energy B s p hs0 hs1 hp i j u
  have hsumenergy : differenceEnergy s p (∑ j, w j) < ∞ :=
    (ExpandedFA.PartIV.FractionalSobolev.finiteEnergySubmodule s p hp).sum_mem
      (fun j _ => hwenergy j)
  have hsumrep : (∑ j, w j) =ᵐ[volume] A.localizedRepresentative i u.val := by
    have hall := ae_all_iff.mpr hw
    filter_upwards [Lp.coeFn_finsetSum Finset.univ w, hall] with x hx hallx
    rw [A.localizedRepresentative_reconstruction B]
    simp only [Finset.sum_apply] at hx ⊢
    rw [hx]
    exact Finset.sum_congr rfl fun j _ => hallx j
  have hEq : A.localizedLp p i v = ∑ j, w j := by
    apply Lp.ext
    exact (A.localizedLp_representative p i v).trans
      ((A.localizedRepresentative_congr_ae i hvu).trans hsumrep.symm)
  rwa [hEq]

end ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas

namespace ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
variable (A : Boundary.FiniteAtlas M d ι) (B : Boundary.FiniteAtlas M d κ)
variable {𝕜 : Type} [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Identity on boundary representatives, as a genuine equivalence of the
atlas Lp quotients. The hypotheses are proved geometric measure bounds. -/
def lpEquiv : Lp 𝕜 p B.atlasMeasure ≃ₗ[𝕜] Lp 𝕜 p A.atlasMeasure :=
  Boundary.changeMeasureLpLinearEquiv p
    (A.atlasMeasure_comparison_constant_finite B) (A.atlasMeasure_le_smul_atlasMeasure B)
    (B.atlasMeasure_comparison_constant_finite A) (B.atlasMeasure_le_smul_atlasMeasure A)

lemma lpEquiv_representative (u : Lp 𝕜 p B.atlasMeasure) :
    A.lpEquiv B p u =ᵐ[A.atlasMeasure] u :=
  Boundary.changeMeasureLpLinear_representative p
    (A.atlasMeasure_comparison_constant_finite B) (A.atlasMeasure_le_smul_atlasMeasure B) u

lemma lpEquiv_symm_representative (u : Lp 𝕜 p A.atlasMeasure) :
    (A.lpEquiv B p).symm u =ᵐ[B.atlasMeasure] u :=
  Boundary.changeMeasureLpLinear_representative p
    (B.atlasMeasure_comparison_constant_finite A) (B.atlasMeasure_le_smul_atlasMeasure A) u

lemma finite_energy_lpEquiv_iff [CompactSpace M] (s : ℝ)
    (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞) (u : Lp 𝕜 p B.atlasMeasure) :
    (∀ i, differenceEnergy s p (A.localizedLp p i (A.lpEquiv B p u)) < ∞) ↔
      (∀ j, differenceEnergy s p (B.localizedLp p j u) < ∞) := by
  constructor
  · intro hu j
    have hrep : u =ᵐ[B.atlasMeasure] A.lpEquiv B p u := by
      have h := A.lpEquiv_symm_representative B p (A.lpEquiv B p u)
      rwa [LinearEquiv.symm_apply_apply] at h
    exact B.localizedLp_finite_energy_of_atlas A s p hs0 hs1 hp
      ⟨A.lpEquiv B p u, hu⟩ u hrep j
  · intro hu i
    exact A.localizedLp_finite_energy_of_atlas B s p hs0 hs1 hp
      ⟨u, hu⟩ (A.lpEquiv B p u) (A.lpEquiv_representative B p u) i

section FractionalEquivalence
variable [CompactSpace M] [Fact (p ≠ ∞)] (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)

/-- The concrete identity identification of the boundary fractional spaces
for two finite atlases. Norm comparison is proved separately. -/
def fractionalLinearEquiv : B.FractionalSpace 𝕜 s p ≃ₗ[𝕜] A.FractionalSpace 𝕜 s p where
  toFun u := ⟨A.lpEquiv B p u.val, (A.finite_energy_lpEquiv_iff B p s hs0 hs1 Fact.out u.val).mpr u.property⟩
  invFun v := ⟨(A.lpEquiv B p).symm v.val, by
    apply (A.finite_energy_lpEquiv_iff B p s hs0 hs1 Fact.out _).mp
    simpa only [LinearEquiv.apply_symm_apply] using v.property⟩
  left_inv u := Subtype.ext ((A.lpEquiv B p).symm_apply_apply u.val)
  right_inv v := Subtype.ext ((A.lpEquiv B p).apply_symm_apply v.val)
  map_add' u v := Subtype.ext ((A.lpEquiv B p).map_add u.val v.val)
  map_smul' c u := Subtype.ext ((A.lpEquiv B p).map_smul c u.val)

lemma fractionalLinearEquiv_representative (u : B.FractionalSpace 𝕜 s p) :
    (A.fractionalLinearEquiv B p s hs0 hs1 u).val =ᵐ[A.atlasMeasure] u.val :=
  A.lpEquiv_representative B p u.val

end FractionalEquivalence
end ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas

namespace ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
variable (A : Boundary.FiniteAtlas M d ι) (B : Boundary.FiniteAtlas M d κ)
variable {𝕜 : Type} [RCLike 𝕜] (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
variable (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞)

def overlapLp (i : ι) (j : κ) (u : B.FractionalSpace 𝕜 s p) :
    Lp 𝕜 p (volume : Measure (Fin d → ℝ)) :=
  (A.overlapRepresentative_memLp B p i j u.val).toLp (A.overlapRepresentative B i j u.val)

lemma overlapLp_representative (i : ι) (j : κ) (u : B.FractionalSpace 𝕜 s p) :
    A.overlapLp B s p i j u =ᵐ[volume] A.overlapRepresentative B i j u.val :=
  (A.overlapRepresentative_memLp B p i j u.val).coeFn_toLp

include hs0 hs1 hp in
lemma overlapLp_finite_energy (i : ι) (j : κ) (u : B.FractionalSpace 𝕜 s p) :
    differenceEnergy s p (A.overlapLp B s p i j u) < ∞ := by
  rw [difference_energy_double_integral]
  change Transport.rawDoubleEnergy s p (A.overlapLp B s p i j u) < ∞
  rw [Transport.rawDoubleEnergy_congr s p (A.overlapLp_representative B s p i j u)]
  exact A.overlapRepresentative_finite_energy B s p hs0 hs1 hp i j u

def overlapFractional (i : ι) (j : κ) (u : B.FractionalSpace 𝕜 s p) :
    ExpandedFA.PartIV.FractionalSobolev.FractionalSpace 𝕜 d s p :=
  ⟨A.overlapLp B s p i j u, A.overlapLp_finite_energy B s p hs0 hs1 hp i j u⟩

lemma overlapFractional_norm_bound (i : ι) (j : κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : B.FractionalSpace 𝕜 s p,
      ExpandedFA.PartIV.FractionalSobolev.fractionalNorm s p
        (A.overlapFractional B s p hs0 hs1 hp i j u) ≤ C *
        ExpandedFA.PartIV.FractionalSobolev.fractionalNorm s p
          ⟨B.localizedLp p j u.val,u.property j⟩ := by
  obtain ⟨C,hC,hbound⟩ := A.overlapRepresentative_rawNorm_bound (𝕜 := 𝕜) B s p hs0 hs1 hp i j
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro u
  have hb := hbound u
  rw [← rawFullNorm_congr_ae s p (A.overlapLp_representative B s p i j u)] at hb
  change rawFullNorm s p (A.overlapFractional B s p hs0 hs1 hp i j u).val ≤ _ at hb
  rw [rawFullNorm_eq_ofReal_fractionalNorm s p hp] at hb
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) hb
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (ExpandedFA.PartIV.FractionalSobolev.fractionalNorm_nonneg s p _)] using hr

lemma localizedFractional_eq_sum_overlap [Fact (p ≠ ∞)]
    (u : B.FractionalSpace 𝕜 s p) (i : ι) :
    (⟨A.localizedLp p i (A.lpEquiv B p u.val),
      (A.finite_energy_lpEquiv_iff B p s hs0 hs1 Fact.out u.val).mpr u.property i⟩ :
      ExpandedFA.PartIV.FractionalSobolev.FractionalSpace 𝕜 d s p) =
      ∑ j, A.overlapFractional B s p hs0 hs1 Fact.out i j u := by
  classical
  apply Subtype.ext
  have hall := ae_all_iff.mpr fun j => A.overlapLp_representative B s p i j u
  have hval : (∑ j, A.overlapFractional B s p hs0 hs1 Fact.out i j u).val =
      ∑ j, A.overlapLp B s p i j u :=
    (ExpandedFA.PartIV.FractionalSobolev.finiteEnergySubmodule s p Fact.out).coe_sum
      (fun j => A.overlapFractional B s p hs0 hs1 Fact.out i j u) Finset.univ
  rw [hval]
  apply Lp.ext
  have hsum : (∑ j, A.overlapLp B s p i j u) =ᵐ[volume]
      A.localizedRepresentative i u.val := by
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j => A.overlapLp B s p i j u), hall]
      with x hx hallx
    rw [A.localizedRepresentative_reconstruction B]
    simp only [Finset.sum_apply] at hx ⊢
    rw [hx]
    exact Finset.sum_congr rfl fun j _ => hallx j
  have htarget := (A.localizedLp_representative p i (A.lpEquiv B p u.val)).trans
    ((A.localizedRepresentative_congr_ae i (A.lpEquiv_representative B p u.val)).trans hsum.symm)
  exact htarget

end ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas

namespace ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
variable (A : Boundary.FiniteAtlas M d ι) (B : Boundary.FiniteAtlas M d κ)
variable {𝕜 : Type} [RCLike 𝕜] (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (p ≠ ∞)]

lemma fractionalLinearEquiv_norm_bound (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : B.FractionalSpace 𝕜 s p,
      A.fractionalNorm s p (A.fractionalLinearEquiv B p s hs0 hs1 u) ≤
        C * B.fractionalNorm s p u := by
  classical
  choose C hC hb using fun i j =>
    A.overlapFractional_norm_bound (𝕜 := 𝕜) B s p hs0 hs1 Fact.out i j
  refine ⟨∑ i, ∑ j, C i j,
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hC i j)), ?_⟩
  intro u
  calc
    _ ≤ ∑ i, ∑ j, C i j * ExpandedFA.PartIV.FractionalSobolev.fractionalNorm s p
        ⟨B.localizedLp p j u.val,u.property j⟩ := by
      unfold fractionalNorm
      apply Finset.sum_le_sum
      intro i _
      change ExpandedFA.PartIV.FractionalSobolev.fractionalNorm s p
        (⟨A.localizedLp p i (A.lpEquiv B p u.val),
          (A.finite_energy_lpEquiv_iff B p s hs0 hs1 Fact.out u.val).mpr u.property i⟩ :
          ExpandedFA.PartIV.FractionalSobolev.FractionalSpace 𝕜 d s p) ≤ _
      rw [A.localizedFractional_eq_sum_overlap B s p hs0 hs1 u i]
      change ‖∑ j, A.overlapFractional B s p hs0 hs1 Fact.out i j u‖ ≤ _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      exact hb i j u
    _ ≤ ∑ i, ∑ j, C i j * B.fractionalNorm s p u := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (hC i j)
      exact Finset.single_le_sum
        (fun k _ => ExpandedFA.PartIV.FractionalSobolev.fractionalNorm_nonneg s p
          ⟨B.localizedLp p k u.val,u.property k⟩) (Finset.mem_univ j)
    _ = _ := by simp_rw [Finset.sum_mul]

lemma fractionalLinearEquiv_inverse (hs0 : 0 < s) (hs1 : s < 1)
    (u : B.FractionalSpace 𝕜 s p) :
    B.fractionalLinearEquiv A p s hs0 hs1 (A.fractionalLinearEquiv B p s hs0 hs1 u) = u := by
  apply Subtype.ext
  exact Boundary.changeMeasureLpLinear_inverse p
    (A.atlasMeasure_comparison_constant_finite B) (A.atlasMeasure_le_smul_atlasMeasure B)
    (B.atlasMeasure_comparison_constant_finite A) (B.atlasMeasure_le_smul_atlasMeasure A) u.val

lemma atlas_norm_equivalence (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ u : B.FractionalSpace 𝕜 s p,
      A.fractionalNorm s p (A.fractionalLinearEquiv B p s hs0 hs1 u) ≤ C * B.fractionalNorm s p u ∧
      B.fractionalNorm s p u ≤ D * A.fractionalNorm s p (A.fractionalLinearEquiv B p s hs0 hs1 u) := by
  obtain ⟨C,hC,hf⟩ := A.fractionalLinearEquiv_norm_bound (𝕜 := 𝕜) B s p hs0 hs1
  obtain ⟨D,hD,hg⟩ := B.fractionalLinearEquiv_norm_bound (𝕜 := 𝕜) A s p hs0 hs1
  refine ⟨C+1,D+1,by positivity,by positivity,?_⟩
  intro u
  constructor
  · have hb := hf u
    nlinarith [B.fractionalNorm_nonneg s p u]
  · have hb := hg (A.fractionalLinearEquiv B p s hs0 hs1 u)
    rw [A.fractionalLinearEquiv_inverse B s p hs0 hs1 u] at hb
    nlinarith [A.fractionalNorm_nonneg s p (A.fractionalLinearEquiv B p s hs0 hs1 u)]

/-- Atlas independence as an actual bounded scalar-linear equivalence of the
canonical quotient spaces, obtained from the two explicit overlap estimates. -/
def fractionalContinuousLinearEquiv (hs0 : 0 < s) (hs1 : s < 1) :
    B.FractionalSpace 𝕜 s p ≃L[𝕜] A.FractionalSpace 𝕜 s p where
  toLinearEquiv := A.fractionalLinearEquiv B p s hs0 hs1
  continuous_toFun := by
    obtain ⟨C,hC,hbound⟩ := A.fractionalLinearEquiv_norm_bound (𝕜 := 𝕜) B s p hs0 hs1
    exact ((A.fractionalLinearEquiv B p s hs0 hs1).toLinearMap.mkContinuous C hbound).continuous
  continuous_invFun := by
    obtain ⟨C,D,hC,hD,hbound⟩ := A.atlas_norm_equivalence (𝕜 := 𝕜) B s p hs0 hs1
    have hb : ∀ v : A.FractionalSpace 𝕜 s p, ‖(A.fractionalLinearEquiv B p s hs0 hs1).symm v‖ ≤ D * ‖v‖ := by
      intro v
      have h := (hbound ((A.fractionalLinearEquiv B p s hs0 hs1).symm v)).2
      change B.fractionalNorm s p ((A.fractionalLinearEquiv B p s hs0 hs1).symm v) ≤ D * A.fractionalNorm s p v
      simpa only [LinearEquiv.apply_symm_apply] using h
    exact ((A.fractionalLinearEquiv B p s hs0 hs1).symm.toLinearMap.mkContinuous D hb).continuous

end ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas

namespace ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
variable (A : Boundary.FiniteAtlas M d ι) (B : Boundary.FiniteAtlas M d κ)

/-- A statement exposing only the canonical independent atlas objects: identity
on representatives, equality of the fractional membership conditions, and
positive two-sided bounds for their actual full norms. -/
theorem atlas_independence {𝕜 : Type} [RCLike 𝕜] (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞) :
    ∃ e : Lp 𝕜 p B.atlasMeasure ≃ₗ[𝕜] Lp 𝕜 p A.atlasMeasure,
      (∀ u, e u =ᵐ[A.atlasMeasure] u) ∧
      (∀ u, (∀ i, differenceEnergy s p (A.localizedLp p i (e u)) < ∞) ↔
        (∀ j, differenceEnergy s p (B.localizedLp p j u) < ∞)) ∧
      ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ u : B.FractionalSpace 𝕜 s p,
        ∃ hu : ∀ i, differenceEnergy s p (A.localizedLp p i (e u.val)) < ∞,
          A.fractionalNorm s p ⟨e u.val,hu⟩ ≤ C * B.fractionalNorm s p u ∧
          B.fractionalNorm s p u ≤ D * A.fractionalNorm s p ⟨e u.val,hu⟩ := by
  letI : Fact (p ≠ ∞) := ⟨hp⟩
  refine ⟨A.lpEquiv B p, A.lpEquiv_representative B p,
    A.finite_energy_lpEquiv_iff B p s hs0 hs1 hp, ?_⟩
  obtain ⟨C,D,hC,hD,hbound⟩ := A.atlas_norm_equivalence (𝕜 := 𝕜) B s p hs0 hs1
  refine ⟨C,D,hC,hD,?_⟩
  intro u
  exact ⟨(A.finite_energy_lpEquiv_iff B p s hs0 hs1 hp u.val).mpr u.property, hbound u⟩

end ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas


open Set Metric
open scoped NNReal Topology
namespace ExpandedFA.PartIV.FractionalSobolev.C1Geometry

abbrev Graph {d : ℕ} (g : (Fin d → ℝ) → ℝ) := {z : (Fin d → ℝ) × ℝ // z.2 = g z.1}

/-- The coordinate projection on a genuine graph patch, with its graph inverse. -/
def graphChart {d : ℕ} (g : (Fin d → ℝ) → ℝ) (U : Set (Fin d → ℝ))
    (hU : IsOpen U) (hg : ContinuousOn g U) : OpenPartialHomeomorph (Graph g) (Fin d → ℝ) where
  toFun z := z.val.1
  invFun y := ⟨(y,g y),rfl⟩
  source := {z | z.val.1 ∈ U}
  target := U
  map_source' := fun _ hz => hz
  map_target' := fun _ hy => hy
  left_inv' := by
    intro z _
    apply Subtype.ext
    exact Prod.ext rfl z.property.symm
  right_inv' := fun _ _ => rfl
  open_source := hU.preimage (continuous_fst.comp continuous_subtype_val)
  open_target := hU
  continuousOn_toFun := (continuous_fst.comp continuous_subtype_val).continuousOn
  continuousOn_invFun := by
    apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    exact continuousOn_id.prodMk hg

lemma graphChart_lipschitz {d : ℕ} (g : (Fin d → ℝ) → ℝ) (U : Set (Fin d → ℝ))
    (hU : IsOpen U) (hg : ContinuousOn g U) :
    LipschitzWith 1 (graphChart g U hU hg) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist x.val.1 y.val.1 ≤ (1:ℝ≥0) * dist x y
  simp only [NNReal.coe_one, one_mul, Subtype.dist_eq, Prod.dist_eq]
  exact le_max_left _ _

lemma graphChart_symm_lipschitz {d : ℕ} (g : (Fin d → ℝ) → ℝ) (U : Set (Fin d → ℝ))
    (hU : IsOpen U) {L : ℝ≥0} (hg : LipschitzOnWith L g U) :
    LipschitzOnWith (max 1 L) (graphChart g U hU hg.continuousOn).symm U := by
  intro x hx y hy
  change edist (x,g x) (y,g y) ≤ _
  exact (LipschitzWith.id.lipschitzOnWith.prodMk hg) hx hy

/-- C1 regularity at a graph point yields a bounded coordinate ball carrying
an actual bi-Lipschitz graph chart, in every dimension including zero. -/
theorem exists_bounded_graphChart {d : ℕ} (g : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    (hg : ContDiffAt ℝ 1 g x) (U : Set (Fin d → ℝ)) (hUx : U ∈ 𝓝 x) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ U ∧ ∃ L : ℝ≥0,
      LipschitzOnWith L g (ball x r) := by
  obtain ⟨L,V,hV,hLip⟩ := hg.exists_lipschitzOnWith
  obtain ⟨r,hr,hrV⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hUx hV)
  exact ⟨r,hr,fun y hy => (hrV hy).1,L,hLip.mono fun y hy => (hrV hy).2⟩

/-- Ambient affine coordinate changes and their inverses have global Lipschitz
bounds given by their continuous linear parts. -/
lemma continuousAffineMap_lipschitz {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E →ᴬ[ℝ] F) :
    LipschitzWith ‖f.contLinear‖₊ f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm]
  change ‖f x-f y‖ ≤ ‖f.contLinear‖ * ‖x-y‖
  have he : f.contLinear (x-y) = f x-f y := f.contLinear_apply_vsub x y
  rw [← he]
  exact f.contLinear.le_opNorm (x-y)

lemma continuousAffineEquiv_biLipschitz {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E ≃ᴬ[ℝ] F) :
    LipschitzWith ‖f.toContinuousAffineMap.contLinear‖₊ f ∧
      LipschitzWith ‖f.symm.toContinuousAffineMap.contLinear‖₊ f.symm :=
  ⟨continuousAffineMap_lipschitz f.toContinuousAffineMap,
    continuousAffineMap_lipschitz f.symm.toContinuousAffineMap⟩
 
/-- Actual boundary chart produced from an exact local ambient graph
representation; the inverse is defined outside its target using a fixed point. -/
def graphPatchChart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ}
    (Γ : Set E) (x0 : Γ) (Q : E ≃ᴬ[ℝ] ((Fin d → ℝ) × ℝ))
    (U : Set (Fin d → ℝ)) (J : Set ℝ) (hU : IsOpen U) (hJ : IsOpen J)
    (g : (Fin d → ℝ) → ℝ) (hg : ContinuousOn g U)
    (hgraph : ∀ y ∈ U, Q.symm (y,g y) ∈ Γ ∧ g y ∈ J)
    (hback : ∀ z ∈ Γ, (Q z).1 ∈ U → (Q z).2 ∈ J → (Q z).2 = g (Q z).1) :
    OpenPartialHomeomorph Γ (Fin d → ℝ) := by
  classical
  exact {
    toFun := fun z => (Q z.val).1
    invFun := fun y => if hy : y∈U then ⟨Q.symm (y,g y),(hgraph y hy).1⟩ else x0
    source := {z | (Q z.val).1 ∈ U ∧ (Q z.val).2 ∈ J}
    target := U
    map_source' := fun _ hz => hz.1
    map_target' := by
      intro y hy
      simp only [dite_eq_left hy]
      change (Q (Q.symm (y,g y))).1 ∈ U ∧ (Q (Q.symm (y,g y))).2 ∈ J
      rw [Q.apply_symm_apply]
      exact ⟨hy,(hgraph y hy).2⟩
    left_inv' := by
      intro z hz
      simp only [dite_eq_left hz.1]
      apply Subtype.ext
      change Q.symm ((Q z.val).1,g (Q z.val).1) = z.val
      rw [← hback z.val z.property hz.1 hz.2]
      exact Q.symm_apply_apply z.val
    right_inv' := by
      intro y hy
      simp only [dite_eq_left hy, Q.apply_symm_apply]
    open_source :=
      (hU.preimage (continuous_fst.comp (Q.continuous.comp continuous_subtype_val))).inter
        (hJ.preimage (continuous_snd.comp (Q.continuous.comp continuous_subtype_val)))
    open_target := hU
    continuousOn_toFun := (continuous_fst.comp (Q.continuous.comp continuous_subtype_val)).continuousOn
    continuousOn_invFun := by
      apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
      apply (Q.symm.continuous.comp_continuousOn (continuousOn_id.prodMk hg)).congr
      intro y hy
      simp only [Function.comp_apply, dite_eq_left hy, id_eq]
  }

lemma graphPatchChart_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ}
    (Γ : Set E) (x0 : Γ) (Q : E ≃ᴬ[ℝ] ((Fin d → ℝ) × ℝ))
    (U : Set (Fin d → ℝ)) (J : Set ℝ) (hU : IsOpen U) (hJ : IsOpen J)
    (g : (Fin d → ℝ) → ℝ) (hg : ContinuousOn g U)
    (hgraph : ∀ y ∈ U, Q.symm (y,g y) ∈ Γ ∧ g y ∈ J)
    (hback : ∀ z ∈ Γ, (Q z).1 ∈ U → (Q z).2 ∈ J → (Q z).2 = g (Q z).1) :
    LipschitzWith ‖Q.toContinuousAffineMap.contLinear‖₊
      (graphPatchChart Γ x0 Q U J hU hJ g hg hgraph hback) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (Q x.val).1 (Q y.val).1 ≤ _
  exact (le_max_left _ _).trans ((continuousAffineMap_lipschitz Q.toContinuousAffineMap).dist_le_mul x.val y.val)

lemma graphPatchChart_symm_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ}
    (Γ : Set E) (x0 : Γ) (Q : E ≃ᴬ[ℝ] ((Fin d → ℝ) × ℝ))
    (U : Set (Fin d → ℝ)) (J : Set ℝ) (hU : IsOpen U) (hJ : IsOpen J)
    (g : (Fin d → ℝ) → ℝ) {L : ℝ≥0} (hg : LipschitzOnWith L g U)
    (hgraph : ∀ y ∈ U, Q.symm (y,g y) ∈ Γ ∧ g y ∈ J)
    (hback : ∀ z ∈ Γ, (Q z).1 ∈ U → (Q z).2 ∈ J → (Q z).2 = g (Q z).1) :
    LipschitzOnWith (‖Q.symm.toContinuousAffineMap.contLinear‖₊ * max 1 L)
      (graphPatchChart Γ x0 Q U J hU hJ g hg.continuousOn hgraph hback).symm U := by
  classical
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  change dist (if h : x∈U then _ else _) (if h : y∈U then _ else _) ≤ _
  simp only [dite_eq_left hx, dite_eq_left hy, Subtype.dist_eq]
  exact ((continuousAffineMap_lipschitz Q.symm.toContinuousAffineMap).comp_lipschitzOnWith
    (LipschitzWith.id.lipschitzOnWith.prodMk hg)).dist_le_mul x hx y hy
 
/-- A usual C1 local graph representation yields a genuine bi-Lipschitz
boundary chart with bounded target. No chart or Lipschitz conclusion is assumed
in the local graph hypotheses. -/
theorem exists_chart_of_localC1Graph {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ}
    (Γ : Set E) (x0 : Γ) (Q : E ≃ᴬ[ℝ] ((Fin d → ℝ) × ℝ))
    (V : Set (Fin d → ℝ)) (J : Set ℝ) (hV : IsOpen V) (hJ : IsOpen J)
    (g : (Fin d → ℝ) → ℝ)
    (hcenter : (Q x0.val).1 ∈ V ∧ (Q x0.val).2 ∈ J)
    (hg : ContDiffAt ℝ 1 g (Q x0.val).1)
    (hgraph : ∀ y ∈ V, Q.symm (y,g y) ∈ Γ ∧ g y ∈ J)
    (hback : ∀ z ∈ Γ, (Q z).1 ∈ V → (Q z).2 ∈ J → (Q z).2 = g (Q z).1) :
    ∃ e : OpenPartialHomeomorph Γ (Fin d → ℝ),
      x0 ∈ e.source ∧ Bornology.IsBounded e.target ∧
      ∃ L L' : ℝ≥0, LipschitzOnWith L e e.source ∧ LipschitzOnWith L' e.symm e.target := by
  obtain ⟨r,hr,hrV,L,hgLip⟩ := exists_bounded_graphChart g (Q x0.val).1 hg V
    (hV.mem_nhds hcenter.1)
  have hgraph' : ∀ y ∈ ball (Q x0.val).1 r, Q.symm (y,g y) ∈ Γ ∧ g y ∈ J :=
    fun y hy => hgraph y (hrV hy)
  have hback' : ∀ z ∈ Γ, (Q z).1 ∈ ball (Q x0.val).1 r → (Q z).2 ∈ J →
      (Q z).2 = g (Q z).1 := fun z hz hy hJz => hback z hz (hrV hy) hJz
  let e := graphPatchChart Γ x0 Q (ball (Q x0.val).1 r) J isOpen_ball hJ g hgLip.continuousOn
    hgraph' hback'
  refine ⟨e,?_,isBounded_ball,‖Q.toContinuousAffineMap.contLinear‖₊,
    ‖Q.symm.toContinuousAffineMap.contLinear‖₊ * max 1 L,?_,?_⟩
  · exact ⟨mem_ball_self hr,hcenter.2⟩
  · exact (graphPatchChart_lipschitz Γ x0 Q _ J isOpen_ball hJ g hgLip.continuousOn hgraph' hback').lipschitzOnWith
  · exact graphPatchChart_symm_lipschitz Γ x0 Q _ J isOpen_ball hJ g hgLip hgraph' hback'
 
/-- All local graph hypotheses are used to construct, rather than assume,
the bounded bi-Lipschitz coordinate chart. -/
theorem LocalC1GraphAt.exists_chart {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ}
    {Γ : Set E} {x : Γ} (hx : LocalC1GraphAt (d:=d) Γ x) :
    ∃ e : OpenPartialHomeomorph Γ (Fin d → ℝ),
      x ∈ e.source ∧ Bornology.IsBounded e.target ∧
      ∃ L L' : ℝ≥0, LipschitzOnWith L e e.source ∧ LipschitzOnWith L' e.symm e.target := by
  obtain ⟨Q,V,J,g,hV,hJ,hcenter,hg,hgraph,hback⟩ := hx
  exact exists_chart_of_localC1Graph Γ x Q V J hV hJ g hcenter
    (hg.contDiffAt (hV.mem_nhds hcenter.1)) hgraph hback

/-- Compactness extracts finitely many of the derived bounded graph charts.
The empty boundary and zero-dimensional coordinate cases are included. -/
theorem exists_finite_charts_of_compactC1Graph {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ}
    (Γ : Set E) (hΓ : IsCompact Γ) (hgraph : ∀ x : Γ, LocalC1GraphAt (d:=d) Γ x) :
    ∃ (N : ℕ) (e : Fin N → OpenPartialHomeomorph Γ (Fin d → ℝ))
      (L L' : Fin N → ℝ≥0),
      (∀ x : Γ, ∃ i, x ∈ (e i).source) ∧
      (∀ i, Bornology.IsBounded (e i).target) ∧
      (∀ i, LipschitzOnWith (L i) (e i) (e i).source) ∧
      (∀ i, LipschitzOnWith (L' i) (e i).symm (e i).target) := by
  classical
  let : CompactSpace Γ := isCompact_iff_compactSpace.mp hΓ
  choose e he hbounded L L' hLip hLip' using fun x => (hgraph x).exists_chart
  obtain ⟨t,ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : Γ => (e x).source) (fun x => (e x).open_source) (by
      intro x _
      exact mem_iUnion.mpr ⟨x,he x⟩)
  let T := {x : Γ // x ∈ t}
  let q := (Fintype.equivFin T).symm
  refine ⟨Fintype.card T,fun i => e (q i).val,fun i => L (q i).val,fun i => L' (q i).val,
    ?_,fun i => hbounded _,fun i => hLip _,fun i => hLip' _⟩
  intro x
  have hxcover := ht (mem_univ x)
  simp only [mem_iUnion] at hxcover
  obtain ⟨y,hyt,hxy'⟩ := hxcover
  refine ⟨(Fintype.equivFin T) ⟨y,hyt⟩,?_⟩
  simpa only [q, Equiv.symm_apply_apply] using hxy'

end ExpandedFA.PartIV.FractionalSobolev.C1Geometry

namespace ExpandedFA.PartIV.FractionalSobolev

theorem boundary_atlas_independence :
    Specs.ExpandedFA.PartIV.FractionalSobolev.BoundaryAtlasIndependence := by
  intro M _ _ _ _ d ι κ _ _ A B 𝕜 _ s p _ hs0 hs1 hp
  exact A.atlas_independence (𝕜 := 𝕜) B s p hs0 hs1 hp

end ExpandedFA.PartIV.FractionalSobolev


open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators

namespace ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas

/-- Reindexing an actual finite atlas preserves all geometric and partition
properties. -/
def reindex {M : Type*} [MetricSpace M] {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Boundary.FiniteAtlas M d ι) (q : κ ≃ ι) : Boundary.FiniteAtlas M d κ where
  chart k := A.chart (q k)
  cover x := by
    obtain ⟨i,hi⟩ := A.cover x
    exact ⟨q.symm i,by simpa using hi⟩
  chartLip k := A.chartLip (q k)
  chartSymmLip k := A.chartSymmLip (q k)
  chart_lipschitz k := A.chart_lipschitz (q k)
  chartSymm_lipschitz k := A.chartSymm_lipschitz (q k)
  bounded_target k := A.bounded_target (q k)
  cutoff k := A.cutoff (q k)
  cutoffLip k := A.cutoffLip (q k)
  cutoff_lipschitz k := A.cutoff_lipschitz (q k)
  cutoff_nonneg k := A.cutoff_nonneg (q k)
  cutoff_sum x := by
    exact (q.sum_comp (fun i => A.cutoff i x)).trans (A.cutoff_sum x)
  cutoff_subordinate k := A.cutoff_subordinate (q k)

end ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas

namespace ExpandedFA.PartIV.FractionalSobolev.C1Geometry
open ExpandedFA.Distributions

/-- Restricting an ambient function to a subset cannot enlarge its closed
support beyond the inverse image of the ambient closed support. -/
lemma tsupport_restrict_subset {E : Type*} [TopologicalSpace E] (Γ : Set E) (f : E → ℝ) :
    tsupport (fun x : Γ => f x.val) ⊆ Subtype.val ⁻¹' tsupport f := by
  apply closure_minimal
  · intro x hx
    exact subset_tsupport f hx
  · exact (isClosed_tsupport f).preimage continuous_subtype_val

/-- On a compact Euclidean boundary, actual finite bi-Lipschitz charts produce
an admissible atlas. The Lipschitz partition is constructed by ambient smooth
partitions; it is not supplied as data. -/
theorem exists_finiteAtlas_of_compact_charts {n d N : ℕ}
    (Γ : Set (Domain n)) (hΓ : IsCompact Γ)
    (e : Fin N → OpenPartialHomeomorph Γ (Domain d)) (L L' : Fin N → ℝ≥0)
    (hcover : ∀ x : Γ, ∃ i, x ∈ (e i).source)
    (hbounded : ∀ i, Bornology.IsBounded (e i).target)
    (hLip : ∀ i, LipschitzOnWith (L i) (e i) (e i).source)
    (hLip' : ∀ i, LipschitzOnWith (L' i) (e i).symm (e i).target) :
    ∃ K : ℕ, Nonempty (Boundary.FiniteAtlas Γ d (Fin K)) := by
  classical
  choose U hU heU using fun i =>
    (Topology.IsInducing.subtypeVal.isOpen_iff).mp (e i).open_source
  let Ω : Opens (Domain n) := ⟨⋃ i, U i,isOpen_iUnion hU⟩
  have hΓΩ : Γ ⊆ Ω := by
    intro x hx
    obtain ⟨i,hi⟩ := hcover ⟨x,hx⟩
    apply mem_iUnion.mpr
    refine ⟨i,?_⟩
    change (⟨x,hx⟩ : Γ) ∈ Subtype.val ⁻¹' U i
    rw [heU i]
    exact hi
  obtain ⟨κ,hκ,φ,hφLip,hφnonneg,hφsum,hφsub⟩ := Boundary.finite_lipschitz_cutoffs
    Ω Γ hΓ hΓΩ (Fin N) U hU (by exact Subset.rfl)
  let : Finite κ := hκ
  let : Fintype κ := Fintype.ofFinite κ
  choose P hP using hφLip
  choose i hi using hφsub
  let cutoff : κ → Γ → ℝ := fun k x => φ k x.val
  have hcutoffLip (k : κ) : LipschitzWith (P k) (cutoff k) := by
    simpa only [cutoff,Function.comp_def,mul_one] using (hP k).comp (LipschitzWith.subtype_val Γ)
  have hcutoffsub (k : κ) : tsupport (cutoff k) ⊆ (e (i k)).source := by
    rw [← heU (i k)]
    exact (tsupport_restrict_subset Γ (φ k)).trans (preimage_mono (hi k))
  have hcutoffsum (x : Γ) : ∑ k, cutoff k x = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using hφsum x.val x.property
  let A : Boundary.FiniteAtlas Γ d κ := {
    chart := fun k => e (i k)
    cover := by
      intro x
      have hnonzero : ∃ k, cutoff k x ≠ 0 := by
        by_contra hn
        push Not at hn
        have h := hcutoffsum x
        simp only [hn,Finset.sum_const_zero] at h
        exact zero_ne_one h
      obtain ⟨k,hk⟩ := hnonzero
      exact ⟨k,hcutoffsub k (subset_tsupport (cutoff k) hk)⟩
    chartLip := fun k => L (i k)
    chartSymmLip := fun k => L' (i k)
    chart_lipschitz := fun k => hLip (i k)
    chartSymm_lipschitz := fun k => hLip' (i k)
    bounded_target := fun k => hbounded (i k)
    cutoff := cutoff
    cutoffLip := P
    cutoff_lipschitz := hcutoffLip
    cutoff_nonneg := fun k x => hφnonneg k x.val
    cutoff_sum := hcutoffsum
    cutoff_subordinate := hcutoffsub
  }
  exact ⟨Fintype.card κ,⟨A.reindex (Fintype.equivFin κ).symm⟩⟩

end ExpandedFA.PartIV.FractionalSobolev.C1Geometry

namespace ExpandedFA.PartIV.FractionalSobolev.C1Geometry
open ExpandedFA.Distributions

/-- A compact C1 boundary admits an actual admissible finite atlas. -/
theorem compactC1GraphBoundary_has_finiteAtlas {n d : ℕ}
    (Γ : Set (Domain n)) (hΓ : IsCompact Γ) (hC1 : IsC1GraphBoundary (d:=d) Γ) :
    ∃ N : ℕ, Nonempty (Boundary.FiniteAtlas Γ d (Fin N)) := by
  obtain ⟨N,e,L,L',hcover,hbounded,hLip,hLip'⟩ := exists_finite_charts_of_compactC1Graph Γ hΓ hC1
  exact exists_finiteAtlas_of_compact_charts Γ hΓ e L L' hcover hbounded hLip hLip'

/-- Applied to the actual frontier of an open domain, this is the compact C1
boundary applicability required for the intrinsic order-s spaces. -/
theorem compactC1DomainBoundary_has_finiteAtlas {d : ℕ} (Ω : Opens (Domain (d+1)))
    (hcompact : IsCompact (frontier (Ω : Set (Domain (d+1)))))
    (hC1 : IsC1GraphBoundary (d:=d) (frontier (Ω : Set (Domain (d+1))))) :
    ∃ N : ℕ, Nonempty (Boundary.FiniteAtlas (frontier (Ω : Set (Domain (d+1)))) d (Fin N)) :=
  compactC1GraphBoundary_has_finiteAtlas _ hcompact hC1

end ExpandedFA.PartIV.FractionalSobolev.C1Geometry

namespace ExpandedFA.PartIV.FractionalSobolev

theorem compact_c1_graph_atlas : Specs.ExpandedFA.PartIV.FractionalSobolev.CompactC1GraphAtlas := by
  intro n d Γ hcompact hC1
  exact C1Geometry.compactC1GraphBoundary_has_finiteAtlas Γ hcompact hC1

theorem compact_c1_boundary_atlas :
    Specs.ExpandedFA.PartIV.FractionalSobolev.CompactC1BoundaryAtlas := by
  intro n Ω hcompact hC1
  exact C1Geometry.compactC1GraphBoundary_has_finiteAtlas _ hcompact hC1

end ExpandedFA.PartIV.FractionalSobolev

namespace ExpandedFA.PartIV.FractionalSobolev

/-- A relative first-difference bound and Lp integrability imply fractional finiteness. -/
theorem finite_energy_of_relative_increment {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞)
    (u : Lp 𝕜 p (volume : Measure (Fin d → ℝ)))
    (f : (Fin d → ℝ) → 𝕜) (hu : u =ᵐ[volume] f)
    (hf : ∀ x h, ‖f (x+h) - f x‖ ≤ euclideanLength h * ‖f x‖) :
    differenceEnergy s p u < ∞ := by
  have hnear (h : Fin d → ℝ) :
      ‖lpIncrement p h u‖ ≤ euclideanLength h * ‖u‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    have hshift := (measurePreserving_add_right (volume : Measure (Fin d → ℝ)) h).quasiMeasurePreserving.ae_eq_comp hu
    filter_upwards [lpIncrement_representative p u h, hu, hshift] with x hx hx0 hx1
    simp only [Function.comp_apply] at hx1
    rw [hx, hx0, hx1]
    exact hf x h
  have hfar (h : Fin d → ℝ) : ‖lpIncrement p h u‖ ≤ 2 * ‖u‖ := by
    change ‖Lp.compMeasurePreserving (fun x => x - (-h))
      (measurePreserving_sub_right volume (-h)) u - u‖ ≤ _
    calc
      _ ≤ ‖Lp.compMeasurePreserving (fun x => x - (-h))
        (measurePreserving_sub_right volume (-h)) u‖ + ‖u‖ := norm_sub_le _ _
      _ = 2 * ‖u‖ := by rw [Lp.norm_compMeasurePreserving]; ring
  have hbound (h : Fin d → ℝ) :
      ‖lpIncrement p h u‖ ≤ ‖(2 * ‖u‖) * incrementCutoff h‖ := by
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (incrementCutoff_nonneg h))]
    unfold incrementCutoff
    by_cases hh : euclideanLength h ≤ 1
    · rw [min_eq_left hh]
      exact (hnear h).trans (by nlinarith [mul_nonneg (show 0 ≤ euclideanLength h from norm_nonneg _) (norm_nonneg u)])
    · rw [min_eq_right (le_of_not_ge hh), mul_one]
      exact hfar h
  apply (finite_energy_iff_memLp s p hp u).mpr
  exact ((incrementCutoff_memLp (d:=d) s p hs0 hs1 hp).const_mul (2 * ‖u‖)).of_le
    (lpIncrement_continuous p hp u).stronglyMeasurable.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

end ExpandedFA.PartIV.FractionalSobolev

namespace ExpandedFA.PartIV.FractionalSobolev.NegativeMultiplier

def decay (x : (Fin 1 → ℝ)) : ℝ := 1 / (1 + ‖x‖)

lemma decay_pos (x : (Fin 1 → ℝ)) : 0 < decay x := by
  unfold decay
  positivity

lemma decay_le_one (x : (Fin 1 → ℝ)) : decay x ≤ 1 := by
  unfold decay
  exact (div_le_one (by positivity)).2 (by linarith [norm_nonneg x])

lemma decay_continuous : Continuous decay := by
  unfold decay
  exact continuous_const.div (continuous_const.add continuous_norm) (fun x => by positivity)

lemma decay_memLp : MemLp decay 2 (volume : Measure ((Fin 1 → ℝ))) := by
  apply (memLp_two_iff_integrable_sq decay_continuous.aestronglyMeasurable).2
  have hi := integrable_one_add_norm (E := (Fin 1 → ℝ)) (μ := volume) (r := 2) (by simp)
  convert hi using 1
  funext x
  simp [decay]

lemma decay_increment (x h : (Fin 1 → ℝ)) :
    |decay (x + h) - decay x| ≤ ‖h‖ * decay x := by
  have ha : 0 < 1 + ‖x + h‖ := by positivity
  have hb : 0 < 1 + ‖x‖ := by positivity
  have hn : |‖x‖ - ‖x + h‖| ≤ ‖h‖ := by
    simpa [sub_add_cancel_left, norm_neg] using abs_norm_sub_norm_le x (x + h)
  unfold decay
  rw [div_sub_div _ _ ha.ne' hb.ne']
  simp only [one_mul, mul_one, add_sub_add_left_eq_sub, abs_div,
    abs_of_pos (mul_pos ha hb)]
  apply (div_le_iff₀ (mul_pos ha hb)).2
  calc
    |‖x‖ - ‖x + h‖| ≤ ‖h‖ := hn
    _ ≤ ‖h‖ * (1 + ‖x + h‖) := by nlinarith [norm_nonneg h, norm_nonneg (x + h)]
    _ = ‖h‖ * (1 / (1 + ‖x‖)) * ((1 + ‖x + h‖) * (1 + ‖x‖)) := by field_simp

end ExpandedFA.PartIV.FractionalSobolev.NegativeMultiplier

namespace ExpandedFA.PartIV.FractionalSobolev.NegativeMultiplier

/-- A concrete whole-space finite-energy function used by the counterexample. -/
def decaySobolev : FractionalSpace ℝ 1 (1 / 2) 2 :=
  ⟨decay_memLp.toLp decay, by
    apply finite_energy_of_relative_increment (1/2) 2 (by norm_num) (by norm_num)
      (by norm_num) _ decay decay_memLp.coeFn_toLp
    intro x h
    rw [Real.norm_of_nonneg (decay_pos x).le]
    exact (decay_increment x h).trans
      (mul_le_mul_of_nonneg_right (norm_le_euclideanLength h) (decay_pos x).le)⟩

lemma decaySobolev_representative :
    decaySobolev.val =ᵐ[volume] decay := decay_memLp.coeFn_toLp

end ExpandedFA.PartIV.FractionalSobolev.NegativeMultiplier

open Filter
open scoped Topology

namespace ExpandedFA.PartIV.FractionalSobolev.NegativeGeometry

def count (n : ℕ) : ℕ := (n + 1)^4

def width (n : ℕ) : ℝ := 1 / (8 * (count n : ℝ))

def leftEnd (n : ℕ) (k : Fin (count n)) : ℝ :=
  4 * (n : ℝ) + 4 * (k : ℝ) * width n

def zeroInterval (n : ℕ) (k : Fin (count n)) : Set ℝ :=
  Icc (leftEnd n k) (leftEnd n k + width n)

def oneInterval (n : ℕ) (k : Fin (count n)) : Set ℝ :=
  Icc (leftEnd n k + 2 * width n) (leftEnd n k + 3 * width n)

def zeroBlock (n : ℕ) : Set ℝ := ⋃ k, zeroInterval n k

def oneBlock (n : ℕ) : Set ℝ := ⋃ k, oneInterval n k

def zeroSet : Set ℝ := ⋃ n, zeroBlock n

def oneSet : Set ℝ := ⋃ n, oneBlock n

lemma count_pos (n : ℕ) : 0 < count n := by unfold count; positivity
lemma width_pos (n : ℕ) : 0 < width n := by
  unfold width
  exact one_div_pos.mpr (mul_pos (by norm_num) (Nat.cast_pos.mpr (count_pos n)))

lemma width_mul_count (n : ℕ) : (count n : ℝ) * width n = 1 / 8 := by
  unfold width
  field_simp [Nat.ne_of_gt (count_pos n)]

lemma leftEnd_bounds (n : ℕ) (k : Fin (count n)) :
    4 * (n : ℝ) ≤ leftEnd n k ∧ leftEnd n k + 3 * width n ≤ 4 * (n : ℝ) + 1 := by
  have hw := width_pos n
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hk : (k : ℝ) + 1 ≤ count n := by exact_mod_cast k.isLt
  have hm := width_mul_count n
  dsimp [leftEnd]
  constructor
  · nlinarith [mul_nonneg hk0 hw.le]
  · nlinarith [mul_le_mul_of_nonneg_right hk hw.le]

lemma zeroInterval_subset_block (n : ℕ) (k : Fin (count n)) :
    zeroInterval n k ⊆ Icc (4 * (n : ℝ)) (4 * (n : ℝ) + 1) := by
  intro x hx
  have hb := leftEnd_bounds n k
  have hw := width_pos n
  exact ⟨hb.1.trans hx.1, by change _ ≤ x ∧ x ≤ _ at hx; linarith [hx.2, hb.2]⟩

lemma oneInterval_subset_block (n : ℕ) (k : Fin (count n)) :
    oneInterval n k ⊆ Icc (4 * (n : ℝ)) (4 * (n : ℝ) + 1) := by
  intro x hx
  have hb := leftEnd_bounds n k
  have hw := width_pos n
  exact ⟨by change _ ≤ x ∧ x ≤ _ at hx; linarith [hx.1, hb.1], hx.2.trans hb.2⟩

lemma zeroBlock_subset_block (n : ℕ) :
    zeroBlock n ⊆ Icc (4 * (n : ℝ)) (4 * (n : ℝ) + 1) := by
  intro x hx
  obtain ⟨k,hx⟩ := mem_iUnion.mp hx
  exact zeroInterval_subset_block n k hx

lemma oneBlock_subset_block (n : ℕ) :
    oneBlock n ⊆ Icc (4 * (n : ℝ)) (4 * (n : ℝ) + 1) := by
  intro x hx
  obtain ⟨k,hx⟩ := mem_iUnion.mp hx
  exact oneInterval_subset_block n k hx

lemma ambient_locallyFinite : LocallyFinite (fun n : ℕ => Icc (4 * (n : ℝ)) (4 * (n : ℝ) + 1)) := by
  intro x
  obtain ⟨N, hN⟩ := exists_nat_gt (x + 1)
  refine ⟨Iio (x+1), Iio_mem_nhds (by linarith), (finite_Iio N).subset ?_⟩
  rintro n ⟨y, hy, hyx⟩
  change 4 * (n : ℝ) ≤ y ∧ y ≤ 4 * (n : ℝ)+1 at hy
  change y < x+1 at hyx
  simp only [mem_Iio]
  have hn : (n : ℝ) < N := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    linarith [hy.1]
  exact_mod_cast hn

lemma zeroSet_isClosed : IsClosed zeroSet := by
  apply (ambient_locallyFinite.subset zeroBlock_subset_block).isClosed_iUnion
  intro n
  exact isClosed_iUnion_of_finite fun k => isClosed_Icc

lemma oneSet_isClosed : IsClosed oneSet := by
  apply (ambient_locallyFinite.subset oneBlock_subset_block).isClosed_iUnion
  intro n
  exact isClosed_iUnion_of_finite fun k => isClosed_Icc

lemma same_ambient_block {n m : ℕ} {x : ℝ}
    (hn : x ∈ Icc (4 * (n : ℝ)) (4 * (n : ℝ)+1))
    (hm : x ∈ Icc (4 * (m : ℝ)) (4 * (m : ℝ)+1)) : n = m := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have : (n : ℝ) + 1 ≤ m := by exact_mod_cast hlt
    linarith [hn.2, hm.1]
  · have : (m : ℝ) + 1 ≤ n := by exact_mod_cast hgt
    linarith [hm.2, hn.1]

lemma zero_one_disjoint_same (n : ℕ) (k l : Fin (count n)) :
    Disjoint (zeroInterval n k) (oneInterval n l) := by
  rw [Set.disjoint_left]
  intro x hx hy
  have hw := width_pos n
  simp only [zeroInterval, oneInterval, leftEnd, mem_Icc] at hx hy
  by_cases hkl : k.val ≤ l.val
  · have hkl' : (k : ℝ) ≤ l := by exact_mod_cast hkl
    nlinarith [mul_le_mul_of_nonneg_right hkl' hw.le]
  · have hkl' : (l : ℝ) + 1 ≤ k := by exact_mod_cast (Nat.lt_of_not_ge hkl)
    nlinarith [mul_le_mul_of_nonneg_right hkl' hw.le]

lemma zero_one_disjoint : Disjoint zeroSet oneSet := by
  rw [Set.disjoint_left]
  intro x hx hy
  obtain ⟨n,hx⟩ := mem_iUnion.mp hx
  obtain ⟨k,hx⟩ := mem_iUnion.mp hx
  obtain ⟨m,hy⟩ := mem_iUnion.mp hy
  obtain ⟨l,hy⟩ := mem_iUnion.mp hy
  have hnm := same_ambient_block (zeroInterval_subset_block n k hx) (oneInterval_subset_block m l hy)
  subst m
  exact Set.disjoint_left.mp (zero_one_disjoint_same n k l) hx hy

lemma oneInterval_pairwiseDisjoint (n : ℕ) :
    Pairwise (fun k l : Fin (count n) => Disjoint (oneInterval n k) (oneInterval n l)) := by
  intro k l hkl
  rw [Set.disjoint_left]
  intro x hx hy
  have hw := width_pos n
  simp only [oneInterval, leftEnd, mem_Icc] at hx hy
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hkl) with hlt | hgt
  · have hkl' : (k : ℝ) + 1 ≤ l := by exact_mod_cast hlt
    nlinarith [mul_le_mul_of_nonneg_right hkl' hw.le]
  · have hkl' : (l : ℝ) + 1 ≤ k := by exact_mod_cast hgt
    nlinarith [mul_le_mul_of_nonneg_right hkl' hw.le]

lemma zeroInterval_pairwiseDisjoint (n : ℕ) :
    Pairwise (fun k l : Fin (count n) => Disjoint (zeroInterval n k) (zeroInterval n l)) := by
  intro k l hkl
  rw [Set.disjoint_left]
  intro x hx hy
  have hw := width_pos n
  simp only [zeroInterval, leftEnd, mem_Icc] at hx hy
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hkl) with hlt | hgt
  · have hkl' : (k : ℝ) + 1 ≤ l := by exact_mod_cast hlt
    nlinarith [mul_le_mul_of_nonneg_right hkl' hw.le]
  · have hkl' : (l : ℝ) + 1 ≤ k := by exact_mod_cast hgt
    nlinarith [mul_le_mul_of_nonneg_right hkl' hw.le]

lemma rectangle_distance_bounds (n : ℕ) (k : Fin (count n)) {x y : ℝ}
    (hx : x ∈ oneInterval n k) (hy : y ∈ zeroInterval n k) :
    0 < x-y ∧ |y-x| ≤ 3 * width n := by
  have hw := width_pos n
  simp only [oneInterval, zeroInterval, mem_Icc] at hx hy
  constructor
  · linarith [hx.1, hy.2]
  · rw [abs_of_nonpos (by linarith [hx.1, hy.2])]
    linarith [hx.2, hy.1]

lemma reciprocal_lower_bound (n : ℕ) {x : ℝ}
    (hx : x ∈ Icc (4*(n : ℝ)) (4*(n : ℝ)+1)) :
    1 / (4*(n : ℝ)+2) ≤ 1 / (1+|x|) := by
  have hx0 : 0 ≤ x := le_trans (by positivity) hx.1
  rw [abs_of_nonneg hx0]
  exact one_div_le_one_div_of_le (by positivity) (by linarith [hx.2])


lemma zeroInterval_volume (n : ℕ) (k : Fin (count n)) :
    MeasureTheory.volume (zeroInterval n k) = ENNReal.ofReal (width n) := by
  simp [zeroInterval, Real.volume_Icc]

lemma oneInterval_volume (n : ℕ) (k : Fin (count n)) :
    MeasureTheory.volume (oneInterval n k) = ENNReal.ofReal (width n) := by
  simp only [oneInterval, Real.volume_Icc]
  congr 1
  ring


lemma block_ratio_lower_bound (n : ℕ) :
    ((n : ℝ)+1) / 144 ≤ (count n : ℝ) / (9 * (4*(n : ℝ)+2)^2) := by
  have hd : 0 < 9 * (4*(n : ℝ)+2)^2 := by positivity
  apply (le_div_iff₀ hd).mpr
  simp only [count, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have h1 : 0 ≤ (n : ℝ)^2 := sq_nonneg _
  have h2 : 0 ≤ (n : ℝ)^3 := pow_nonneg h0 _
  have h3 : 0 ≤ (n : ℝ)^4 := pow_nonneg h0 _
  nlinarith

lemma eq_top_of_block_lower_bounds (E : ℝ≥0∞)
    (hE : ∀ n : ℕ, ENNReal.ofReal ((count n : ℝ) / (9 * (4*(n : ℝ)+2)^2)) ≤ E) :
    E = ∞ := by
  by_contra hfin
  obtain ⟨n,hn⟩ := exists_nat_gt (144 * E.toReal)
  have hn' : E.toReal < ((n : ℝ)+1)/144 := by linarith
  have hb := (block_ratio_lower_bound n).trans
    ((ENNReal.ofReal_le_iff_le_toReal hfin).mp (hE n))
  linarith


lemma exists_smooth_separator :
    ∃ a : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a ∧
      (∀ x, 0 ≤ a x ∧ a x ≤ 1) ∧
      (∀ n k x, x ∈ zeroInterval n k → a x = 0) ∧
      (∀ n k x, x ∈ oneInterval n k → a x = 1) := by
  obtain ⟨a, ha, hb, hz, ho⟩ := exists_contDiff_zero_iff_one_iff_of_isClosed
    (n := (⊤ : ℕ∞)) zeroSet_isClosed oneSet_isClosed zero_one_disjoint
  refine ⟨a, ha, fun x => hb ⟨x, rfl⟩, ?_, ?_⟩
  · intro n k x hx
    exact (hz x).mp (mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨k,hx⟩⟩)
  · intro n k x hx
    exact (ho x).mp (mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨k,hx⟩⟩)

end ExpandedFA.PartIV.FractionalSobolev.NegativeGeometry

namespace ExpandedFA.PartIV.FractionalSobolev.NegativeMultiplier

private theorem euclideanLength_one (x : (Fin 1 → ℝ)) : euclideanLength x = |x 0| := by
  simp [euclideanLength, EuclideanSpace.norm_eq, Real.norm_eq_abs, Real.sqrt_sq_eq_abs]

lemma norm_one (x : (Fin 1 → ℝ)) : ‖x‖ = |x 0| := by
  rw [← Real.norm_eq_abs]
  refine le_antisymm ?_ (norm_le_pi_norm x 0)
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  simp [hi]

private theorem kernel_one (x y : (Fin 1 → ℝ)) :
    differenceKernel (1/2 : ℝ) 2 (y - x) =
      if y 0 = x 0 then 0 else ENNReal.ofReal |y 0 - x 0| ^ (-2 : ℝ) := by
  have heq : y - x = 0 ↔ y 0 = x 0 := by
    rw [sub_eq_zero]
    exact ⟨fun h => congrFun h 0, fun h => funext (fun i => by
      have hi : i = 0 := Subsingleton.elim _ _
      simpa [hi] using h)⟩
  simp [differenceKernel, heq, euclideanLength_one]
  norm_num

private theorem lintegral_eval_zero (f : ℝ → ℝ≥0∞) :
    ∫⁻ x : (Fin 1 → ℝ), f (x 0) = ∫⁻ t : ℝ, f t := by
  exact (volume_preserving_funUnique (Fin 1) ℝ).lintegral_comp_emb
    (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding f

private theorem lintegral_eval_zero_twice (f : ℝ → ℝ → ℝ≥0∞) :
    ∫⁻ x : (Fin 1 → ℝ), ∫⁻ y : (Fin 1 → ℝ), f (x 0) (y 0) =
      ∫⁻ s : ℝ, ∫⁻ t : ℝ, f s t := by
  calc
    _ = ∫⁻ x : (Fin 1 → ℝ), ∫⁻ t : ℝ, f (x 0) t :=
      lintegral_congr fun x => lintegral_eval_zero (f (x 0))
    _ = _ := lintegral_eval_zero (fun s => ∫⁻ t : ℝ, f s t)

private theorem half_two_integrand_one (x y : (Fin 1 → ℝ)) (f : ℝ → ℝ) :
    differenceKernel (1/2 : ℝ) 2 (y-x) * ‖f (y 0) - f (x 0)‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal ((f (y 0) - f (x 0))^2 / (y 0 - x 0)^2) := by
  by_cases hxy : y 0 = x 0
  · simp [hxy]
  · have hd : 0 < |y 0 - x 0| := abs_pos.mpr (sub_ne_zero.mpr hxy)
    rw [kernel_one, ite_eq_right hxy]
    rw [ENNReal.rpow_neg, ENNReal.rpow_two, Real.enorm_eq_ofReal_abs,
      ENNReal.rpow_two, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs,
      mul_comm, ← div_eq_mul_inv,
      ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs,
      ← ENNReal.ofReal_div_of_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hxy))]

lemma energy_one_representative (u : Lp ℝ 2 (volume : Measure ((Fin 1 → ℝ))))
    (f : ℝ → ℝ) (huf : u =ᵐ[volume] (fun x => f (x 0))) :
    differenceEnergy (1/2 : ℝ) 2 u =
      ∫⁻ x : ℝ, ∫⁻ y : ℝ, ENNReal.ofReal ((f y-f x)^2 / (y-x)^2) := by
  rw [difference_energy_double_integral ℝ 1 (1/2) 2 u]
  change Transport.rawDoubleEnergy (1/2) 2 (fun x => u x) = _
  rw [Transport.rawDoubleEnergy_congr (1/2) 2 huf]
  unfold Transport.rawDoubleEnergy
  norm_num only [ENNReal.toReal_ofNat]
  simp_rw [half_two_integrand_one]
  exact lintegral_eval_zero_twice (fun x y => ENNReal.ofReal ((f y-f x)^2 / (y-x)^2))

end ExpandedFA.PartIV.FractionalSobolev.NegativeMultiplier

namespace ExpandedFA.PartIV.FractionalSobolev.NegativeEnergy

lemma rectangle_lower_bound {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {A : Set α} {B : Set β}
    (F : α → β → ℝ≥0∞) (c : ℝ≥0∞) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hF : ∀ x ∈ A, ∀ y ∈ B, c ≤ F x y) :
    c * ν B * μ A ≤ ∫⁻ x in A, ∫⁻ y in B, F x y ∂ν ∂μ := by
  calc
    c * ν B * μ A = ∫⁻ x in A, ∫⁻ y in B, c ∂ν ∂μ := by simp
    _ ≤ _ := by
      apply setLIntegral_mono' hA
      intro x hx
      apply setLIntegral_mono' hB
      intro y hy
      exact hF x hx y hy

lemma finset_rectangles_lower_bound {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    (t : Finset ι) (A : ι → Set α) (B : ι → Set β) (F : α → β → ℝ≥0∞)
    (hA : ∀ i ∈ t, MeasurableSet (A i)) (hdisj : Set.PairwiseDisjoint (t : Set ι) A)
    (c : ι → ℝ≥0∞)
    (hbound : ∀ i ∈ t, c i ≤ ∫⁻ x in A i, ∫⁻ y in B i, F x y ∂ν ∂μ) :
    ∑ i ∈ t, c i ≤ ∫⁻ x, ∫⁻ y, F x y ∂ν ∂μ := by
  calc
    ∑ i ∈ t, c i ≤ ∑ i ∈ t, ∫⁻ x in A i, ∫⁻ y, F x y ∂ν ∂μ := by
      apply Finset.sum_le_sum
      intro i hi
      exact (hbound i hi).trans (lintegral_mono fun x => setLIntegral_le_lintegral _ _)
    _ = ∫⁻ x in ⋃ i ∈ t, A i, ∫⁻ y, F x y ∂ν ∂μ :=
      (lintegral_biUnion_finset hdisj hA _).symm
    _ ≤ _ := setLIntegral_le_lintegral _ _

open ExpandedFA.PartIV.FractionalSobolev.NegativeGeometry

lemma quotient_lower_three {d δ c z : ℝ} (hd : 0 < d) (hδ : 0 < δ) (hc : 0 ≤ c)
    (hdδ : d ≤ 3 * δ) (hcz : c ≤ |z|) :
    c^2 / (9 * δ^2) ≤ z^2 / d^2 := by
  have hd2 : d^2 ≤ 9 * δ^2 := by nlinarith
  have hc2 : c^2 ≤ z^2 := by nlinarith [sq_abs z]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 9 * δ^2) (sq_pos_of_pos hd)).2
  exact (mul_le_mul_of_nonneg_left hd2 (sq_nonneg c)).trans
    (mul_le_mul_of_nonneg_right hc2 (by positivity))

lemma rectangle_quotient_lower_bound (f : ℝ → ℝ) (n : ℕ) (k : Fin (count n))
    (c : ℝ) (hc : 0 ≤ c)
    (hzero : ∀ y ∈ zeroInterval n k, f y = 0)
    (hone : ∀ x ∈ oneInterval n k, c ≤ |f x|) :
    ENNReal.ofReal (c^2 / 9) ≤
      ∫⁻ x in oneInterval n k, ∫⁻ y in zeroInterval n k,
        ENNReal.ofReal ((f y-f x)^2 / (y-x)^2) := by
  have hbound := rectangle_lower_bound
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (A := oneInterval n k) (B := zeroInterval n k)
    (fun x y => ENNReal.ofReal ((f y-f x)^2 / (y-x)^2))
    (ENNReal.ofReal (c^2 / (9*(width n)^2))) measurableSet_Icc measurableSet_Icc ?_
  · have hw := width_pos n
    have hcoeff : 0 ≤ c^2 / (9*(width n)^2) := by positivity
    have hcancel : c^2 / (9*(width n)^2) * width n * width n = c^2 / 9 := by
      field_simp [hw.ne']
    calc
      ENNReal.ofReal (c^2 / 9) =
          ENNReal.ofReal (c^2 / (9*(width n)^2) * width n * width n) := congrArg _ hcancel.symm
      _ = ENNReal.ofReal (c^2 / (9*(width n)^2)) *
          ENNReal.ofReal (width n) * ENNReal.ofReal (width n) := by
        rw [ENNReal.ofReal_mul (mul_nonneg hcoeff hw.le), ENNReal.ofReal_mul hcoeff]
      _ ≤ _ := by simpa only [oneInterval_volume, zeroInterval_volume] using hbound
  · intro x hx y hy
    have hd := rectangle_distance_bounds n k hx hy
    apply ENNReal.ofReal_le_ofReal
    have hcz : c ≤ |f y-f x| := by rw [hzero y hy, zero_sub, abs_neg]; exact hone x hx
    simpa only [sq_abs] using quotient_lower_three
      (abs_pos.mpr (by linarith : y-x ≠ 0)) (width_pos n) hc hd.2 hcz

lemma block_quotient_lower_bound (f : ℝ → ℝ) (n : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hzero : ∀ k y, y ∈ zeroInterval n k → f y = 0)
    (hone : ∀ k x, x ∈ oneInterval n k → c ≤ |f x|) :
    ENNReal.ofReal ((count n : ℝ) * c^2 / 9) ≤
      ∫⁻ x, ∫⁻ y, ENNReal.ofReal ((f y-f x)^2 / (y-x)^2) := by
  have hbound := finset_rectangles_lower_bound
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    Finset.univ (oneInterval n) (zeroInterval n)
    (fun x y => ENNReal.ofReal ((f y-f x)^2 / (y-x)^2))
    (by intro k hk; exact measurableSet_Icc)
    (by intro k hk l hl hkl; exact oneInterval_pairwiseDisjoint n hkl)
    (fun _ => ENNReal.ofReal (c^2 / 9))
    (by intro k hk; exact rectangle_quotient_lower_bound f n k c hc (hzero k) (hone k))
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), mul_div_assoc]
    using hbound

lemma separator_block_energy_lower_bound (a : ℝ → ℝ) (n : ℕ)
    (hzero : ∀ k y, y ∈ zeroInterval n k → a y = 0)
    (hone : ∀ k x, x ∈ oneInterval n k → a x = 1) :
    ENNReal.ofReal ((count n : ℝ) / (9 * (4*(n:ℝ)+2)^2)) ≤
      ∫⁻ x, ∫⁻ y,
        ENNReal.ofReal (((a y / (1+|y|))-(a x / (1+|x|)))^2 / (y-x)^2) := by
  have hbound := block_quotient_lower_bound (fun x => a x / (1+|x|)) n
    (1 / (4*(n:ℝ)+2)) (by positivity) ?_ ?_
  · convert hbound using 1
    congr 1
    field_simp
  · intro k y hy
    simp [hzero k y hy]
  · intro k x hx
    have hb := oneInterval_subset_block n k hx
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
    have hx0 : 0 ≤ x := by linarith [hb.1]
    rw [hone k x hx, abs_of_nonneg hx0, abs_of_pos (by positivity : 0 < 1/(1+x))]
    exact one_div_le_one_div_of_le (by positivity) (by linarith [hb.2])


lemma separator_quotient_energy_eq_top (a : ℝ → ℝ)
    (hzero : ∀ n k y, y ∈ zeroInterval n k → a y = 0)
    (hone : ∀ n k x, x ∈ oneInterval n k → a x = 1) :
    (∫⁻ x, ∫⁻ y,
        ENNReal.ofReal (((a y / (1+|y|))-(a x / (1+|x|)))^2 / (y-x)^2)) = ∞ := by
  apply eq_top_of_block_lower_bounds
  intro n
  exact separator_block_energy_lower_bound a n (hzero n) (hone n)

end ExpandedFA.PartIV.FractionalSobolev.NegativeEnergy


namespace ExpandedFA.PartIV.FractionalSobolev

/-- Smoothness and a uniform scalar bound alone do not preserve whole-space
fractional Sobolev membership. The multiplier is smooth on every bounded set,
while its plateaus become increasingly fine at infinity. -/
theorem smooth_bounded_multiplier_failure :
    Specs.ExpandedFA.PartIV.FractionalSobolev.SmoothBoundedMultiplierFailure := by
  obtain ⟨a, ha, hb, hzero, hone⟩ := NegativeGeometry.exists_smooth_separator
  refine ⟨fun x => a (x 0), ha.comp (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) 0),
    ⟨1, ?_⟩, NegativeMultiplier.decaySobolev, ?_⟩
  · intro x
    rw [Real.norm_of_nonneg (hb (x 0)).1]
    exact (hb (x 0)).2
  · rintro ⟨v, hv⟩
    have hrep : v.val =ᵐ[volume] (fun x => a (x 0) / (1 + |x 0|)) := by
      filter_upwards [hv, NegativeMultiplier.decaySobolev_representative] with x hx hu
      rw [hx, hu]
      simp [NegativeMultiplier.decay, NegativeMultiplier.norm_one, div_eq_mul_inv]
    have he := NegativeMultiplier.energy_one_representative v.val
      (fun t => a t / (1 + |t|)) hrep
    have htop : (∫⁻ x : ℝ, ∫⁻ y : ℝ,
        ENNReal.ofReal (((a y / (1+|y|))-(a x / (1+|x|)))^2 / (y-x)^2)) = ∞ := by
      apply NegativeGeometry.eq_top_of_block_lower_bounds
      intro n
      exact NegativeEnergy.separator_block_energy_lower_bound a n (hzero n) (hone n)
    exact (ne_of_lt v.property) (he.trans htop)

end ExpandedFA.PartIV.FractionalSobolev
