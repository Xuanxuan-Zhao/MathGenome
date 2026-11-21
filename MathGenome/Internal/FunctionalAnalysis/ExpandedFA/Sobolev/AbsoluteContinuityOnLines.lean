import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.ContinuousMap.Compact

import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.SpecificCodomains.ContinuousMap
import Mathlib.Analysis.RCLike.Basic

import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.OneDimensionalSobolev
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.AbsoluteContinuityOnLines
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal Topology

namespace ExpandedFA.Sobolev.Lines
open ExpandedFA.Distributions

@[simp] theorem coordinateLine_self {d : ℕ} (i : Fin d) (y : Transverse i) (t : ℝ) :
    coordinateLine i y t i = t := by simp [coordinateLine]

@[simp] theorem coordinateLine_transverse {d : ℕ} (i : Fin d) (y : Transverse i)
    (t : ℝ) (j : {j : Fin d // j ≠ i}) : coordinateLine i y t j = y j := by
  simp [coordinateLine, j.property]

/-- Splitting one coordinate from the other d-1 coordinates. -/
def coordinateEquiv {d : ℕ} (i : Fin d) : Domain d ≃ᵐ ℝ × Transverse i :=
  (Homeomorph.funSplitAt ℝ i).toMeasurableEquiv

@[simp] theorem coordinateEquiv_apply {d : ℕ} (i : Fin d) (x : Domain d) :
    coordinateEquiv i x = (x i, fun j : {j : Fin d // j ≠ i} => x j) := rfl

@[simp] theorem coordinateEquiv_symm_apply {d : ℕ} (i : Fin d)
    (t : ℝ) (y : Transverse i) :
    (coordinateEquiv i).symm (t, y) = coordinateLine i y t := by
  ext j
  simp [coordinateEquiv, Homeomorph.funSplitAt, Homeomorph.piSplitAt,
    Equiv.piSplitAt, coordinateLine]

/-- There is no hidden scaling of Lebesgue measure in the coordinate split,
also when the transverse dimension is zero. -/
theorem coordinateEquiv_measurePreserving {d : ℕ} (i : Fin d) :
    MeasurePreserving (coordinateEquiv i) volume volume := by
  let : Unique {j : Fin d // j = i} :=
    ⟨⟨⟨i, rfl⟩⟩, fun j => Subtype.ext j.property⟩
  have h₁ := volume_preserving_piEquivPiSubtypeProd (fun _ : Fin d => ℝ) (fun j => j = i)
  have h₂ := (volume_preserving_funUnique {j : Fin d // j = i} ℝ).prod
    (MeasurePreserving.id (volume : Measure (Transverse i)))
  have h₁' : MeasurePreserving
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin d => ℝ) (fun j => j = i))
      volume ((volume : Measure ({j : Fin d // j = i} → ℝ)).prod
        (volume : Measure (Transverse i))) := by
    convert h₁ using 1
    congr
    exact Subsingleton.elim _ _
  exact h₂.comp h₁'

theorem coordinateLine_eq_update {d : ℕ} (i : Fin d) (y : Transverse i) :
    coordinateLine i y = Function.update (coordinateLine i y 0) i := by
  classical
  funext t
  ext j
  by_cases hj : j = i <;> simp [coordinateLine, hj]

theorem coordinateLine_contDiff {d : ℕ} (i : Fin d) (y : Transverse i) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (coordinateLine i y) := by
  apply contDiff_pi.mpr
  intro j
  dsimp only [coordinateLine]
  split_ifs <;> first | exact contDiff_id | exact contDiff_const

theorem coordinateLine_hasDerivAt {d : ℕ} (i : Fin d) (y : Transverse i) (t : ℝ) :
    HasDerivAt (coordinateLine i y) (coordinateVector i) t := by
  rw [coordinateLine_eq_update]
  exact hasDerivAt_update _ _ _

theorem coordinateLine_isClosedEmbedding {d : ℕ} (i : Fin d) (y : Transverse i) :
    Topology.IsClosedEmbedding (coordinateLine i y) := by
  rw [coordinateLine_eq_update]
  exact isClosedEmbedding_update _ _

/-- Restriction of the actual coordinate partial to a line is the ordinary
one-variable derivative of the restricted test. -/
theorem testPartial_on_coordinateLine {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} (φ : Tests 𝕜 Ω) (i : Fin d) (y : Transverse i) (t : ℝ) :
    testPartialCLM [i] φ (coordinateLine i y t) =
      deriv (fun s => φ (coordinateLine i y s)) t := by
  rw [testPartial_single_apply]
  exact ((φ.contDiff.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
    (coordinateLine_hasDerivAt i y t)).deriv.symm

/-- Compactly supported test/Lp pairings are integrable for ambient volume;
no global L1 hypothesis on the Lp class is needed. -/
theorem integrable_test_mul_lp {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (φ : Tests 𝕜 Ω) (u : DomainLp 𝕜 Ω p) :
    Integrable (fun x => φ x * u x) volume := by
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp
    (φ.integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜) (domainLp_locallyIntegrable u))
  intro x hx
  exact φ.tsupport_subset (subset_tsupport φ ((mul_ne_zero_iff.mp hx).1))

/-- Coordinate Fubini for integrable functions, with transverse variable first. -/
theorem integral_coordinateLines {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (i : Fin d) {h : Domain d → 𝕜} (hh : Integrable h volume) :
    (∫ x, h x) = ∫ y : Transverse i, ∫ t : ℝ, h (coordinateLine i y t) := by
  have hm := (coordinateEquiv_measurePreserving i).symm (coordinateEquiv i)
  have hi := hm.integrable_comp_of_integrable hh
  rw [← hm.integral_comp' h]
  exact (integral_prod_symm _ hi).trans (by simp only [Function.comp_apply, coordinateEquiv_symm_apply])

theorem integrable_coordinateLines {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (i : Fin d) {h : Domain d → 𝕜} (hh : Integrable h volume) :
    ∀ᵐ y : Transverse i ∂volume,
      Integrable (fun t => h (coordinateLine i y t)) volume := by
  have hm := (coordinateEquiv_measurePreserving i).symm (coordinateEquiv i)
  have hi := hm.integrable_comp_of_integrable hh
  simpa only [Function.comp_def, coordinateEquiv_symm_apply] using hi.prod_left_ae

/-- Ambient a.e. assertions restrict to a.e. point of a.e. coordinate fiber.
This applies to nonmeasurable predicates as well, by completed Fubini. -/
theorem ae_on_fibers {d : ℕ} {Ω : Opens (Domain d)} (i : Fin d)
    {P : Domain d → Prop} (hP : ∀ᵐ x ∂volume.restrict (Ω : Set (Domain d)), P x) :
    ∀ᵐ y : Transverse i ∂volume,
      ∀ᵐ t ∂volume.restrict (fiber Ω i y : Set ℝ), P (coordinateLine i y t) := by
  have h := (ae_restrict_iff' Ω.isOpen.measurableSet).mp hP
  have hc := (coordinateEquiv_measurePreserving i).symm
    (coordinateEquiv i) |>.quasiMeasurePreserving.ae h
  have hh := Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hc)
  filter_upwards [hh] with y hy
  apply (ae_restrict_iff' (fiber Ω i y).isOpen.measurableSet).mpr
  simpa [fiber] using hy

/-- Fubini on a countable compact exhaustion gives local integrability on
whole lines outside one transverse null set. -/
theorem locallyIntegrable_prod_right_ae {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (i : Fin d) {h : Transverse i × ℝ → 𝕜}
    (hh : LocallyIntegrable h volume) :
    ∀ᵐ y : Transverse i ∂volume, LocallyIntegrable (fun t => h (y, t)) volume := by
  let K := CompactExhaustion.choice (Transverse i)
  let J := CompactExhaustion.choice ℝ
  have hi (n : ℕ) : Integrable h
      ((volume.restrict (K n)).prod (volume.restrict (J n))) := by
    rw [Measure.prod_restrict]
    exact hh.integrableOn_isCompact ((K.isCompact n).prod (J.isCompact n))
  have ha (n : ℕ) : ∀ᵐ y : Transverse i ∂volume,
      y ∈ K n → IntegrableOn (fun t => h (y, t)) (J n) volume := by
    exact (ae_restrict_iff' (K.isCompact n).measurableSet).mp (hi n).prod_right_ae
  filter_upwards [ae_all_iff.mpr ha] with y hy
  intro t
  obtain ⟨n, hn⟩ := K.exists_mem y
  obtain ⟨m, hm⟩ := J.exists_mem_nhds t
  refine ⟨J (max n m), Filter.mem_of_superset hm (J.subset (le_max_right n m)), ?_⟩
  exact hy (max n m) (K.subset (le_max_left n m) hn)

/-- The zero extension of the original Lp class is locally integrable on
almost every entire coordinate line, including the endpoint p=∞. -/
theorem domainLp_zeroExtension_locallyIntegrable_on_lines {𝕜 : Type} [RCLike 𝕜]
    {d : ℕ} {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : DomainLp 𝕜 Ω p) (i : Fin d) :
    ∀ᵐ y : Transverse i ∂volume,
      LocallyIntegrable (fun t => (Ω : Set (Domain d)).indicator u (coordinateLine i y t))
        volume := by
  have hu : MemLp ((Ω : Set (Domain d)).indicator u) p volume :=
    (memLp_indicator_iff_restrict Ω.isOpen.measurableSet.nullMeasurableSet).mpr (Lp.memLp u)
  let e : Transverse i × ℝ ≃ᵐ Domain d :=
    (MeasurableEquiv.prodComm).trans (coordinateEquiv i).symm
  have he : MeasurePreserving e volume volume :=
    ((coordinateEquiv_measurePreserving i).symm (coordinateEquiv i)).comp
      Measure.measurePreserving_swap
  have hp := hu.comp_measurePreserving he
  have hl := locallyIntegrable_prod_right_ae i (hp.locallyIntegrable Fact.out)
  change ∀ᵐ y : Transverse i ∂volume,
    LocallyIntegrable (fun t => (Ω : Set (Domain d)).indicator u
      ((coordinateEquiv i).symm (t, y))) volume at hl
  simpa only [coordinateEquiv_symm_apply] using hl


/-- Simultaneous null-set removal for a countable dense family of tests.
Continuity is only required outside one null set. No uncountable intersection
of full-measure sets is used. -/
theorem ae_forall_of_dense_tests {X T E : Type*} [MeasurableSpace X]
    {μ : Measure X} [TopologicalSpace T] [TopologicalSpace E] [T2Space E]
    (tests : ℕ → T) (hdense : DenseRange tests) (F G : X → T → E)
    (hcont : ∀ᵐ x ∂μ, Continuous (F x) ∧ Continuous (G x))
    (htests : ∀ n, ∀ᵐ x ∂μ, F x (tests n) = G x (tests n)) :
    ∀ᵐ x ∂μ, ∀ t, F x t = G x t := by
  filter_upwards [hcont, ae_all_iff.mpr htests] with x hx hxt
  have hfg : F x = G x := hdense.equalizer hx.1 hx.2 (funext hxt)
  exact congrFun hfg

/-- Tensor testing reduces to scalar distributions in the transverse
variables. This is the countable-test step: all tests then hold on the same
full-measure transverse set, provided the slice defect is continuous in the
test topology. -/
theorem ae_forall_of_integral_test_eq_zero {T : Type*} [TopologicalSpace T]
    [SeparableSpace T] [Nonempty T] {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [SFinite (volume : Measure E)]
    (U : Opens (E)) (F : E → T → 𝕜)
    (hcont : ∀ᵐ y ∂volume.restrict (U : Set (E)), Continuous (F y))
    (hloc : ∀ t, LocallyIntegrableOn (fun y => F y t) U volume)
    (hzero : ∀ t (η : E → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) η →
      HasCompactSupport η → tsupport η ⊆ U → (∫ y, η y • F y t) = 0) :
    ∀ᵐ y ∂volume.restrict (U : Set (E)), ∀ t, F y t = 0 := by
  apply ae_forall_of_dense_tests (denseSeq T) (denseRange_denseSeq T) F (fun _ _ => 0)
  · filter_upwards [hcont] with y hy
    exact ⟨hy, continuous_const⟩
  · intro k
    exact (ae_restrict_iff' U.isOpen.measurableSet).mpr
      (U.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (hloc (denseSeq T k)) (hzero (denseSeq T k)))

section ContinuousSlices

variable {K : Type*} [MetricSpace K] [CompactSpace K] [SecondCountableTopology K]
  [MeasurableSpace K] [BorelSpace K] {μ : Measure K}
  [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
  {𝕜 : Type*} [RCLike 𝕜]

/-- The countable collection of L1 distances detects continuous functions. -/
def continuousSliceDistance (μ : Measure K) [IsFiniteMeasure μ] :
    C(K, 𝕜) → ℕ → ℝ :=
  fun f n => dist (ContinuousMap.toLp 1 μ 𝕜 f)
    (ContinuousMap.toLp 1 μ 𝕜 (denseSeq C(K, 𝕜) n))

omit [μ.IsOpenPosMeasure] in
theorem continuous_continuousSliceDistance :
    Continuous (continuousSliceDistance (𝕜 := 𝕜) μ) := by
  apply continuous_pi
  intro n
  exact (ContinuousMap.toLp 1 μ 𝕜).continuous.dist continuous_const

theorem injective_continuousSliceDistance :
    Function.Injective (continuousSliceDistance (𝕜 := 𝕜) μ) := by
  intro f g hfg
  let J : C(K, 𝕜) →L[𝕜] Lp 𝕜 1 μ := ContinuousMap.toLp 1 μ 𝕜
  have hdist : (fun z : C(K, 𝕜) => dist (J f) (J z)) =
      (fun z : C(K, 𝕜) => dist (J g) (J z)) := by
    apply (denseRange_denseSeq C(K, 𝕜)).equalizer
      (continuous_const.dist J.continuous) (continuous_const.dist J.continuous)
    funext n
    exact congrFun hfg n
  have hzero : dist (J g) (J f) = 0 := by
    simpa using (congrFun hdist f).symm
  exact (ContinuousMap.toLp_injective μ) (dist_eq_zero.mp hzero).symm

theorem measurableEmbedding_continuousSliceDistance :
    MeasurableEmbedding (continuousSliceDistance (𝕜 := 𝕜) μ) :=
  continuous_continuousSliceDistance.measurableEmbedding
    injective_continuousSliceDistance

omit [μ.IsOpenPosMeasure] in
/-- L1 distance of continuous functions is the integral of the pointwise distance. -/
theorem continuousSliceDistance_eq_integral (f : C(K, 𝕜)) (n : ℕ) :
    continuousSliceDistance μ f n =
      ∫ t, ‖f t - denseSeq C(K, 𝕜) n t‖ ∂μ := by
  let J : C(K, 𝕜) →L[𝕜] Lp 𝕜 1 μ := ContinuousMap.toLp 1 μ 𝕜
  rw [continuousSliceDistance, dist_eq_norm, ← map_sub]
  change ‖ContinuousMap.toLp 1 μ 𝕜 (f - denseSeq C(K, 𝕜) n)‖ = _
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 1) (𝕜 := 𝕜) μ (f - denseSeq C(K, 𝕜) n)] with t ht
  exact congrArg norm ht

/-- A chosen continuous representative of almost every jointly measurable slice
is an a.e. strongly measurable map into the uniform Banach space. -/
theorem aestronglyMeasurable_continuousSlices {Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} [SFinite ν] (u : Y × K → 𝕜)
    (hu : AEStronglyMeasurable u (ν.prod μ))
    (F : Y → C(K, 𝕜))
    (hF : ∀ᵐ y ∂ν, (fun t => F y t) =ᵐ[μ] (fun t => u (y, t))) :
    AEStronglyMeasurable F ν := by
  have hcoord (n : ℕ) :
      AEMeasurable (fun y => continuousSliceDistance μ (F y) n) ν := by
    let ψ := denseSeq C(K, 𝕜) n
    have hp : AEStronglyMeasurable (fun z : Y × K => ‖u z - ψ z.2‖) (ν.prod μ) := by
      exact (hu.sub (ψ.continuous.stronglyMeasurable.comp_measurable measurable_snd).aestronglyMeasurable).norm
    have hm := hp.integral_prod_right'
    apply hm.aemeasurable.congr
    filter_upwards [hF] with y hy
    rw [continuousSliceDistance_eq_integral]
    apply integral_congr_ae
    filter_upwards [hy] with t ht
    exact congrArg (fun z => ‖z - ψ t‖) ht.symm
  have hdist : AEMeasurable (continuousSliceDistance μ ∘ F) ν := by
    exact AEMeasurable.of_eval hcoord
  exact (measurableEmbedding_continuousSliceDistance.aemeasurable_comp_iff.mp hdist).aestronglyMeasurable

/-- The slice map is Bochner integrable once its uniform norm has an integrable bound. -/
theorem integrable_continuousSlices {Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} [SFinite ν] (u : Y × K → 𝕜)
    (hu : AEStronglyMeasurable u (ν.prod μ))
    (F : Y → C(K, 𝕜))
    (hF : ∀ᵐ y ∂ν, (fun t => F y t) =ᵐ[μ] (fun t => u (y, t)))
    (bound : Y → ℝ) (hbound : HasFiniteIntegral bound ν)
    (hboundF : ∀ᵐ y ∂ν, ∀ t, ‖F y t‖ ≤ bound y) :
    Integrable F ν :=
  ⟨aestronglyMeasurable_continuousSlices u hu F hF,
    ContinuousMap.hasFiniteIntegral_of_bound F bound hbound hboundF⟩


end ContinuousSlices

/-- The C¹ test topology on tests supported in a fixed compact interval.
Only the first jet is needed to control weak first-derivative pairings. -/
structure CompactLineTest (𝕜 : Type) [RCLike 𝕜] (a b : ℝ) where
  toTest : TestFunction (⊤ : Opens ℝ) 𝕜 ⊤
  support_subset : tsupport toTest ⊆ Icc a b

namespace CompactLineTest
variable {𝕜 : Type} [RCLike 𝕜] {a b : ℝ}

/-- Restrict the function and its classical first derivative to the compact interval. -/
def jet (ψ : CompactLineTest 𝕜 a b) : C(Icc a b, 𝕜) × C(Icc a b, 𝕜) :=
  (⟨fun t => ψ.toTest t, ψ.toTest.continuous.comp continuous_subtype_val⟩,
   ⟨fun t => deriv ψ.toTest t,
    (ψ.toTest.contDiff.continuous_deriv (by simp)).comp continuous_subtype_val⟩)

instance : TopologicalSpace (CompactLineTest 𝕜 a b) := TopologicalSpace.induced jet inferInstance

instance : SecondCountableTopology (CompactLineTest 𝕜 a b) :=
  TopologicalSpace.secondCountableTopology_induced _ _ jet

instance : Nonempty (CompactLineTest 𝕜 a b) := ⟨⟨0, by simp⟩⟩

theorem continuous_jet : Continuous (jet (𝕜 := 𝕜) (a := a) (b := b)) :=
  continuous_induced_dom

/-- In particular there is a countable dense family of actual smooth tests,
without assuming separability of the LF test topology. -/
theorem exists_dense_tests : ∃ ψ : ℕ → CompactLineTest 𝕜 a b, DenseRange ψ :=
  ⟨denseSeq _, denseRange_denseSeq _⟩

end CompactLineTest

/-- Pairing a continuous function on a compact space with an L¹ density is
continuous for the uniform norm. No boundedness of the density is assumed. -/
theorem continuous_integral_mul_continuousMap {A : Type*} [TopologicalSpace A]
    [CompactSpace A] [MeasurableSpace A] [OpensMeasurableSpace A]
    {𝕜 : Type} [RCLike 𝕜] {μ : Measure A} {g : A → 𝕜} (hg : Integrable g μ) :
    Continuous (fun φ : C(A, 𝕜) => ∫ x, φ x * g x ∂μ) := by
  have hi (φ : C(A, 𝕜)) : Integrable (fun x => φ x * g x) μ :=
    hg.bdd_mul φ.continuous.aestronglyMeasurable
      (ae_of_all _ fun x => φ.norm_coe_le_norm x)
  let L : C(A, 𝕜) →ₗ[𝕜] 𝕜 :=
    { toFun := fun φ => ∫ x, φ x * g x ∂μ
      map_add' := fun φ ψ => by
        simp only [ContinuousMap.add_apply, add_mul]
        exact integral_add (hi φ) (hi ψ)
      map_smul' := fun c φ => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
        exact integral_const_mul c _ }
  apply (L.mkContinuous (∫ x, ‖g x‖ ∂μ) ?_).continuous
  intro φ
  calc
    ‖∫ x, φ x * g x ∂μ‖ ≤ ∫ x, ‖φ x * g x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖φ‖ * ‖g x‖ ∂μ := by
      apply integral_mono (hi φ).norm (hg.norm.const_mul _)
      intro x
      dsimp only
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (φ.norm_coe_le_norm x) (norm_nonneg _)
    _ = (∫ x, ‖g x‖ ∂μ) * ‖φ‖ := by rw [integral_const_mul, mul_comm]

/-- The actual weak-derivative defect on a compact interval is continuous in
the C¹ test topology, including for merely L¹ densities. -/
theorem continuous_compactLineTest_defect {𝕜 : Type} [RCLike 𝕜] {a b : ℝ}
    {u g : ℝ → 𝕜} (hu : IntegrableOn u (Icc a b)) (hg : IntegrableOn g (Icc a b)) :
    Continuous (fun ψ : CompactLineTest 𝕜 a b =>
      ∫ t in Icc a b, ψ.toTest t * g t + deriv ψ.toTest t * u t) := by
  let μ : Measure (Icc a b) := volume.comap Subtype.val
  have hu' : Integrable (fun t : Icc a b => u t) μ :=
    (integrableOn_iff_comap_subtypeVal measurableSet_Icc).mp hu
  have hg' : Integrable (fun t : Icc a b => g t) μ :=
    (integrableOn_iff_comap_subtypeVal measurableSet_Icc).mp hg
  have h₁ := (continuous_integral_mul_continuousMap hg').comp
    (continuous_fst.comp CompactLineTest.continuous_jet)
  have h₂ := (continuous_integral_mul_continuousMap hu').comp
    (continuous_snd.comp CompactLineTest.continuous_jet)
  convert h₁.add h₂ using 1
  funext ψ
  rw [← integral_subtype_comap measurableSet_Icc]
  rw [integral_add]
  · rfl
  · exact hg'.bdd_mul (CompactLineTest.jet ψ).1.continuous.aestronglyMeasurable
      (ae_of_all _ fun x => (CompactLineTest.jet ψ).1.norm_coe_le_norm x)
  · exact hu'.bdd_mul (CompactLineTest.jet ψ).2.continuous.aestronglyMeasurable
      (ae_of_all _ fun x => (CompactLineTest.jet ψ).2.norm_coe_le_norm x)

/-- Fubini and countable tests yield the weak one-dimensional identity
simultaneously for every smooth test with support in a fixed compact interval.
The hypotheses are tensor integral identities, not the desired slice identity.
The L¹ hypothesis is local to the rectangle and makes no assertion of global
L¹ membership for the original Lp function. -/
theorem ae_line_identity_of_tensor_tests {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [SFinite (volume : Measure E)]
    (U : Opens (E)) (a b : ℝ) (u g : E × ℝ → 𝕜)
    (hu : Integrable u ((volume.restrict (U : Set (E))).prod
      (volume.restrict (Icc a b))))
    (hg : Integrable g ((volume.restrict (U : Set (E))).prod
      (volume.restrict (Icc a b))))
    (hzero : ∀ (ψ : CompactLineTest 𝕜 a b) (η : E → ℝ),
      ContDiff ℝ (↑(⊤ : ℕ∞)) η → HasCompactSupport η → tsupport η ⊆ U →
      (∫ z, η z.1 • (ψ.toTest z.2 * g z + deriv ψ.toTest z.2 * u z)
        ∂((volume.restrict (U : Set (E))).prod
          (volume.restrict (Icc a b)))) = 0) :
    ∀ᵐ y ∂volume.restrict (U : Set (E)), ∀ ψ : CompactLineTest 𝕜 a b,
      (∫ t in Icc a b, ψ.toTest t * g (y, t) + deriv ψ.toTest t * u (y, t)) = 0 := by
  let μ := volume.restrict (U : Set (E))
  let ν := volume.restrict (Icc a b)
  let D (ψ : CompactLineTest 𝕜 a b) (z : E × ℝ) :=
    ψ.toTest z.2 * g z + deriv ψ.toTest z.2 * u z
  have hi (ψ : CompactLineTest 𝕜 a b) : Integrable (D ψ) (μ.prod ν) := by
    obtain ⟨C, hC⟩ := ψ.toTest.continuous.bounded_above_of_compact_support
      ψ.toTest.hasCompactSupport
    obtain ⟨C', hC'⟩ := (ψ.toTest.contDiff.continuous_deriv (by simp)).bounded_above_of_compact_support
      ψ.toTest.hasCompactSupport.deriv
    exact (hg.bdd_mul (ψ.toTest.continuous.comp continuous_snd).aestronglyMeasurable
      (ae_of_all _ fun z => hC z.2)).add
        (hu.bdd_mul ((ψ.toTest.contDiff.continuous_deriv (by simp)).comp
          continuous_snd).aestronglyMeasurable (ae_of_all _ fun z => hC' z.2))
  apply ae_forall_of_integral_test_eq_zero U
    (fun y ψ => ∫ t in Icc a b, D ψ (y, t))
  · filter_upwards [hu.prod_right_ae, hg.prod_right_ae] with y hyu hyg
    exact continuous_compactLineTest_defect hyu hyg
  · intro ψ
    exact (show IntegrableOn (fun y => ∫ t in Icc a b, D ψ (y, t))
      (U : Set (E)) volume from (hi ψ).integral_prod_left).locallyIntegrableOn
  · intro ψ η hη hηc hηU
    obtain ⟨C, hC⟩ := hη.continuous.bounded_above_of_compact_support hηc
    have hηD : Integrable (fun z => η z.1 • D ψ z) (μ.prod ν) :=
      (hi ψ).bdd_smul C (hη.continuous.comp continuous_fst).aestronglyMeasurable
        (ae_of_all _ fun z => hC z.1)
    calc
      (∫ y, η y • ∫ t in Icc a b, D ψ (y, t)) =
          ∫ y in (U : Set (E)), η y • ∫ t in Icc a b, D ψ (y, t) := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro y hy
        have hηy : η y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hηU h))
        simp [hηy]
      _ = ∫ z, η z.1 • D ψ z ∂(μ.prod ν) := by
        rw [integral_prod _ hηD]
        congr 1
        funext y
        exact (integral_smul _ _).symm
      _ = 0 := hzero ψ η hη hηc hηU

theorem LocallyAbsolutelyContinuousOn.continuousOn {𝕜 : Type} [RCLike 𝕜]
    {f : ℝ → 𝕜} {U : Set ℝ} (hf : LocallyAbsolutelyContinuousOn f U)
    (hU : IsOpen U) : ContinuousOn f U := by
  intro x hx
  obtain ⟨a, b, hx', hn, hs⟩ := exists_Icc_mem_subset_of_mem_nhds (hU.mem_nhds hx)
  have hab : a ≤ b := hx'.1.trans hx'.2
  have he : uIcc a b = Icc a b := uIcc_of_le hab
  have hc := (hf a b (by rwa [he])).continuousOn
  exact ((hc x (by rwa [he])).continuousAt (by rwa [he])).continuousWithinAt

/-- Local absolute continuity at each point, together with the locally
integrable a.e. derivative, implies AC on every compact interior interval. -/
theorem locallyAbsolutelyContinuousOn_of_local {𝕜 : Type} [RCLike 𝕜]
    {U : Set ℝ} (hU : IsOpen U) {f g : ℝ → 𝕜}
    (hg : LocallyIntegrable g volume)
    (hf : ∀ x ∈ U, ∃ a b : ℝ, x ∈ uIcc a b ∧ uIcc a b ∈ 𝓝 x ∧
      uIcc a b ⊆ U ∧ AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ t ∂volume.restrict U, HasDerivAt f (g t) t) :
    LocallyAbsolutelyContinuousOn f U := by
  let P : ℝ → 𝕜 := fun t => ∫ s in (0 : ℝ)..t, g s
  have hgi (a b : ℝ) : IntervalIntegrable g volume a b :=
    (hg.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have he (x : ℝ) (hx : x ∈ U) :
      ∀ᶠ y in 𝓝 x, f y - P y = f x - P x := by
    obtain ⟨l, r, hxr, hn, hs, hac⟩ := hf x hx
    have hp := OneDimensional.integral_primitive_absolutelyContinuous hgi l r 0
    have hz : ∀ᵐ t ∂volume, t ∈ uIcc l r →
        HasDerivAt (fun t => f t - P t) 0 t := by
      filter_upwards [(ae_restrict_iff' hU.measurableSet).mp hd,
        _root_.LocallyIntegrable.ae_hasDerivAt_integral hg] with t ht hpt htr
      convert (ht (hs htr)).sub (hpt 0) using 1; simp
    obtain ⟨C, hC⟩ := (hac.sub hp).const_of_ae_hasDerivAt_zero hz
    filter_upwards [hn] with y hy
    exact (hC y hy).trans (hC x hxr).symm
  intro a b hab
  have hF : IsLocallyConstant (fun t : uIcc a b => f t - P t) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro t
    exact (continuous_subtype_val.tendsto t).eventually (he t (hab t.property))
  let : PreconnectedSpace (uIcc a b) := Subtype.preconnectedSpace isPreconnected_uIcc
  have hP := OneDimensional.integral_primitive_absolutelyContinuous hgi a b 0
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => f a - P a) a b :=
    (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  apply (hP.add hconst).congr
  intro t ht
  have heq := hF.apply_eq_of_preconnectedSpace ⟨t, ht⟩ ⟨a, left_mem_uIcc⟩
  dsimp only at heq
  change P t + (f a - P a) = f t
  linear_combination -heq


/-- An L1 bound for the uniform norm of a one-dimensional AC representative.
This estimate permits integration with values in the continuous-map space. -/
theorem norm_le_average_add_integral_derivative {𝕜 : Type} [RCLike 𝕜]
    {a b : ℝ} (hab : a < b) {f u g : ℝ → 𝕜}
    (hf : AbsolutelyContinuousOnInterval f a b) (hu : IntegrableOn u (Icc a b))
    (hg : LocallyIntegrable g volume)
    (hrep : u =ᵐ[volume.restrict (Icc a b)] f)
    (hd : ∀ᵐ t ∂volume, t ∈ Icc a b → HasDerivAt f (g t) t)
    {x : ℝ} (hx : x ∈ Icc a b) :
    ‖f x‖ ≤ (b - a)⁻¹ * (∫ t in Icc a b, ‖u t‖) +
      (∫ t in Icc a b, ‖g t‖) := by
  let C : ℝ := ∫ t in Icc a b, ‖g t‖
  have hgi := hg.integrableOn_isCompact (k := Icc a b) isCompact_Icc
  have hosc (y : ℝ) (hy : y ∈ Icc a b) : ‖f x - f y‖ ≤ C := by
    have hs : uIcc y x ⊆ uIcc a b := by
      rw [uIcc_of_le hab.le]
      exact uIcc_subset_Icc hy hx
    have hd' : ∀ᵐ t ∂volume, t ∈ uIcc y x → HasDerivAt f (g t) t := by
      filter_upwards [hd] with t ht hty
      exact ht (uIcc_subset_Icc hy hx hty)
    rw [← OneDimensional.integral_eq_sub_of_absolutelyContinuous_of_ae_hasDerivAt
      (hf.mono hs) hg hd']
    exact intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
      (setIntegral_mono_set hgi.norm (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        (Filter.Eventually.of_forall (uIoc_subset_uIcc.trans (uIcc_subset_Icc hy hx))))
  have hpoint : ∀ᵐ t ∂volume.restrict (Icc a b), ‖f x‖ ≤ ‖u t‖ + C := by
    filter_upwards [hrep, ae_restrict_mem measurableSet_Icc] with t ht hti
    rw [ht]
    calc
      ‖f x‖ = ‖(f x - f t) + f t‖ := by congr 1; abel
      _ ≤ ‖f x - f t‖ + ‖f t‖ := norm_add_le _ _
      _ ≤ ‖f t‖ + C := by linarith [hosc t hti]
  have hν : (volume.restrict (Icc a b)).real Set.univ = b - a := by
    simp [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
  have hi := integral_mono_ae (integrable_const ‖f x‖)
    (hu.norm.add (integrable_const C)) hpoint
  change (∫ _t in Icc a b, ‖f x‖) ≤ ∫ t in Icc a b, ‖u t‖ + C at hi
  rw [integral_add hu.norm (integrable_const C), integral_const, integral_const, hν, smul_eq_mul] at hi
  have hmain : (b-a) * ‖f x‖ ≤ (∫ t in Icc a b, ‖u t‖) + (b-a) * C := by
    simpa only [hν, smul_eq_mul] using hi
  apply (mul_le_mul_iff_right₀ (sub_pos.mpr hab)).mp
  calc
    (b-a) * ‖f x‖ ≤ (∫ t in Icc a b, ‖u t‖) + (b-a) * C := hmain
    _ = (b-a) * ((b-a)⁻¹ * (∫ t in Icc a b, ‖u t‖) + C) := by
      rw [mul_add, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt (sub_pos.mpr hab)), one_mul]


theorem intervalVolume_isOpenPosMeasure {a b : ℝ} (hab : a < b) :
    (volume.comap (Subtype.val : Icc a b → ℝ)).IsOpenPosMeasure := by
  constructor
  intro U hU hUn
  obtain ⟨V, hV, hVU⟩ := isOpen_induced_iff.mp hU
  obtain ⟨x, hx⟩ := hUn
  have hxV : (x : ℝ) ∈ V := by rw [← hVU] at hx; exact hx
  have hxcl : (x : ℝ) ∈ closure (Ioo a b) := by
    rw [closure_Ioo hab.ne]
    exact x.property
  have hVi : (V ∩ Ioo a b).Nonempty :=
    (mem_closure_iff_nhds.mp hxcl) V (hV.mem_nhds hxV)
  have hm : volume (V ∩ Ioo a b) ≠ 0 := (hV.inter isOpen_Ioo).measure_ne_zero volume hVi
  have hsub : V ∩ Ioo a b ⊆ Subtype.val '' U := by
    intro t ht
    refine ⟨⟨t, Ioo_subset_Icc_self ht.2⟩, ?_, rfl⟩
    rw [← hVU]
    exact ht.1
  rw [(MeasurableEmbedding.subtype_coe measurableSet_Icc).comap_apply volume U]
  exact ne_zero_of_lt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hm) (measure_mono hsub))


/-- Continuous representatives of almost every AC slice form an integrable
continuous-map-valued function. The uniform bound comes from the L1 norms of
the density and its one-dimensional derivative. -/
theorem exists_integrable_AC_slices {Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} [SFinite ν] {𝕜 : Type} [RCLike 𝕜]
    {a b : ℝ} (hab : a < b) (u g : Y × ℝ → 𝕜)
    (hu : Integrable u (ν.prod (volume.restrict (Icc a b))))
    (hg : Integrable g (ν.prod (volume.restrict (Icc a b))))
    (hlocal : ∀ᵐ y ∂ν, ∃ f : ℝ → 𝕜,
      AbsolutelyContinuousOnInterval f a b ∧
      (fun t => u (y, t)) =ᵐ[volume.restrict (Icc a b)] f ∧
      LocallyIntegrable (fun t => g (y, t)) volume ∧
      ∀ᵐ t ∂volume, t ∈ Icc a b → HasDerivAt f (g (y, t)) t) :
    ∃ F : Y → C(Icc a b, 𝕜),
      Integrable F ν ∧
      (∀ᵐ y ∂ν, (fun t => F y t) =ᵐ[volume.comap (Subtype.val : Icc a b → ℝ)]
        (fun t => u (y, t))) ∧
      ∀ᵐ y ∂ν, ∃ f : ℝ → 𝕜,
        AbsolutelyContinuousOnInterval f a b ∧
        (fun t => u (y, t)) =ᵐ[volume.restrict (Icc a b)] f ∧
        LocallyIntegrable (fun t => g (y, t)) volume ∧
        (∀ᵐ t ∂volume, t ∈ Icc a b → HasDerivAt f (g (y, t)) t) ∧
        ∀ t : Icc a b, F y t = f t := by
  classical
  let μ : Measure (Icc a b) := volume.comap Subtype.val
  let : IsFiniteMeasure μ := ⟨by
    change volume.comap (Subtype.val : Icc a b → ℝ) univ < ⊤
    rw [(MeasurableEmbedding.subtype_coe measurableSet_Icc).comap_apply volume univ]
    simp only [Set.image_univ, Subtype.range_val, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩
  let : μ.IsOpenPosMeasure := intervalVolume_isOpenPosMeasure hab
  let B : Y → ℝ := fun y => (b - a)⁻¹ * (∫ t in Icc a b, ‖u (y, t)‖) +
    ∫ t in Icc a b, ‖g (y, t)‖
  let Good (y : Y) : Prop := IntegrableOn (fun t => u (y, t)) (Icc a b) ∧
    ∃ f : ℝ → 𝕜, AbsolutelyContinuousOnInterval f a b ∧
      (fun t => u (y, t)) =ᵐ[volume.restrict (Icc a b)] f ∧
      LocallyIntegrable (fun t => g (y, t)) volume ∧
      ∀ᵐ t ∂volume, t ∈ Icc a b → HasDerivAt f (g (y, t)) t
  have hGood : ∀ᵐ y ∂ν, Good y := by
    filter_upwards [hu.prod_right_ae, hlocal] with y hy hl
    exact ⟨hy, hl⟩
  have hex : ∀ y, ∃ F : C(Icc a b, 𝕜), Good y →
      (fun t => F t) =ᵐ[μ] (fun t => u (y, t)) ∧ ∀ t, ‖F t‖ ≤ B y := by
    intro y
    by_cases hy : Good y
    · obtain ⟨hui, f, hfac, hrep, hgli, hd⟩ := hy
      let F : C(Icc a b, 𝕜) := ⟨fun t => f t,
        hfac.continuousOn.comp_continuous continuous_subtype_val
          (fun t => by simpa only [uIcc_of_le hab.le] using t.property)⟩
      refine ⟨F, fun _ => ⟨?_, ?_⟩⟩
      · exact (measurePreserving_subtype_coe measurableSet_Icc).quasiMeasurePreserving.ae hrep.symm
      · intro t
        exact norm_le_average_add_integral_derivative hab hfac hui hgli hrep hd t.property
    · exact ⟨0, fun h => False.elim (hy h)⟩
  choose F hF using hex
  have hFa : ∀ᵐ y ∂ν, (fun t => F y t) =ᵐ[μ] (fun t => u (y, t)) := by
    filter_upwards [hGood] with y hy
    exact (hF y hy).1
  have hFb : ∀ᵐ y ∂ν, ∀ t, ‖F y t‖ ≤ B y := by
    filter_upwards [hGood] with y hy
    exact (hF y hy).2
  have hBi : Integrable B ν :=
    ((hu.norm.integral_prod_left).const_mul (b - a)⁻¹).add (hg.norm.integral_prod_left)
  have hmp : MeasurePreserving (fun z : Y × Icc a b => (z.1, (z.2 : ℝ)))
      (ν.prod μ) (ν.prod (volume.restrict (Icc a b))) :=
    (MeasurePreserving.id ν).prod (measurePreserving_subtype_coe measurableSet_Icc)
  have hu' : AEStronglyMeasurable (fun z : Y × Icc a b => u (z.1, z.2)) (ν.prod μ) :=
    hu.aestronglyMeasurable.comp_measurePreserving hmp
  refine ⟨F, integrable_continuousSlices _ hu' F hFa B hBi.hasFiniteIntegral hFb, hFa, ?_⟩
  filter_upwards [hlocal, hFa] with y hy hFy
  obtain ⟨f, hfac, hrep, hgli, hd⟩ := hy
  have hfμ : (fun t : Icc a b => f t) =ᵐ[μ] (fun t => u (y, t)) :=
    (measurePreserving_subtype_coe measurableSet_Icc).quasiMeasurePreserving.ae hrep.symm
  have hfc : Continuous (fun t : Icc a b => f t) :=
    hfac.continuousOn.comp_continuous continuous_subtype_val
      (fun t => by simpa only [uIcc_of_le hab.le] using t.property)
  have heq := Measure.eq_of_ae_eq (hFy.trans hfμ.symm) (F y).continuous hfc
  exact ⟨f, hfac, hrep, hgli, hd, fun t => congrFun heq t⟩


/-- Countably many local representatives with continuous restrictions to almost
every coordinate line agree pointwise on their overlaps along almost every line.
They therefore glue to one ambient representative, with no extra measurability
assumption on the chosen local representatives. -/
theorem exists_glued_representative {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) (U : ℕ → Opens (Domain d))
    (hcover : (Ω : Set (Domain d)) = ⋃ n, (U n : Set (Domain d)))
    (u : Domain d → 𝕜) (f : ℕ → Domain d → 𝕜)
    (hrep : ∀ n, u =ᵐ[volume.restrict (U n : Set (Domain d))] f n)
    (hcont : ∀ n (i : Fin d), ∀ᵐ y : Transverse i ∂volume,
      ContinuousOn (fun t => f n (coordinateLine i y t)) (fiber (U n) i y)) :
    ∃ F : Domain d → 𝕜,
      u =ᵐ[volume.restrict (Ω : Set (Domain d))] F ∧
      ∀ i : Fin d, ∀ᵐ y : Transverse i ∂volume,
        ∀ n, EqOn (fun t => F (coordinateLine i y t))
          (fun t => f n (coordinateLine i y t)) (fiber (U n) i y) := by
  classical
  have hsub (n : ℕ) : (U n : Set (Domain d)) ⊆ (Ω : Set (Domain d)) := by
    rw [hcover]
    exact subset_iUnion (fun n => (U n : Set (Domain d))) n
  have hindex (x : Domain d) (hx : x ∈ (Ω : Set (Domain d))) :
      ∃ n, x ∈ (U n : Set (Domain d)) := by
    simpa only [hcover, mem_iUnion] using hx
  let index (x : Domain d) : ℕ := if hx : x ∈ (Ω : Set (Domain d)) then
    Nat.find (hindex x hx) else 0
  have hindex_mem (x : Domain d) (hx : x ∈ (Ω : Set (Domain d))) :
      x ∈ (U (index x) : Set (Domain d)) := by
    simpa only [index, dite_eq_left hx] using Nat.find_spec (hindex x hx)
  let F : Domain d → 𝕜 := fun x => f (index x) x
  have hpairs (i : Fin d) (n m : ℕ) :
      ∀ᵐ y : Transverse i ∂volume,
        EqOn (fun t => f n (coordinateLine i y t))
          (fun t => f m (coordinateLine i y t)) (fiber (U n ⊓ U m) i y) := by
    have hn : u =ᵐ[volume.restrict ((U n ⊓ U m : Opens (Domain d)) : Set (Domain d))] f n :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hrep n)
    have hm : u =ᵐ[volume.restrict ((U n ⊓ U m : Opens (Domain d)) : Set (Domain d))] f m :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hrep m)
    have hae : f n =ᵐ[volume.restrict ((U n ⊓ U m : Opens (Domain d)) : Set (Domain d))] f m :=
      hn.symm.trans hm
    filter_upwards [ae_on_fibers i hae, hcont n i, hcont m i] with y hy hny hmy
    apply Measure.eqOn_open_of_ae_eq hy (fiber (U n ⊓ U m) i y).isOpen
    · apply hny.mono
      exact preimage_mono inter_subset_left
    · apply hmy.mono
      exact preimage_mono inter_subset_right
  refine ⟨F, ?_, ?_⟩
  · have hrep' : ∀ᵐ x ∂volume, ∀ n, x ∈ (U n : Set (Domain d)) → u x = f n x := by
      apply ae_all_iff.mpr
      intro n
      exact (ae_restrict_iff' (U n).isOpen.measurableSet).mp (hrep n)
    apply (ae_restrict_iff' Ω.isOpen.measurableSet).mpr
    filter_upwards [hrep'] with x hx hxΩ
    exact hx (index x) (hindex_mem x hxΩ)
  · intro i
    have hp : ∀ᵐ y : Transverse i ∂volume, ∀ n m,
        EqOn (fun t => f n (coordinateLine i y t))
          (fun t => f m (coordinateLine i y t)) (fiber (U n ⊓ U m) i y) := by
      exact ae_all_iff.mpr (fun n => ae_all_iff.mpr (hpairs i n))
    filter_upwards [hp] with y hy
    intro n t htn
    let x := coordinateLine i y t
    have hxU : x ∈ (U n : Set (Domain d)) := htn
    have hxΩ : x ∈ (Ω : Set (Domain d)) := hsub n hxU
    have hxi : x ∈ (U (index x) : Set (Domain d)) := hindex_mem x hxΩ
    exact hy (index x) n (show t ∈ (fiber (U (index x) ⊓ U n) i y : Set ℝ) from ⟨hxi, hxU⟩)


/-- Globalization of countably many ACL representatives of one ambient function.
The derivative densities are the original functions on every member of the cover. -/
theorem exists_glued_acl_representative {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) (U : ℕ → Opens (Domain d))
    (hcover : (Ω : Set (Domain d)) = ⋃ n, (U n : Set (Domain d)))
    (u : Domain d → 𝕜) (g : Fin d → Domain d → 𝕜) (f : ℕ → Domain d → 𝕜)
    (hrep : ∀ n, u =ᵐ[volume.restrict (U n : Set (Domain d))] f n)
    (hlocal : ∀ n (i : Fin d), ∀ᵐ y : Transverse i ∂volume,
      LocallyAbsolutelyContinuousOn (fun t => f n (coordinateLine i y t)) (fiber (U n) i y) ∧
        ∀ᵐ t ∂volume.restrict (fiber (U n) i y : Set ℝ),
          HasDerivAt (fun s => f n (coordinateLine i y s)) (g i (coordinateLine i y t)) t)
    (hgli : ∀ i : Fin d, ∀ᵐ y : Transverse i ∂volume,
      LocallyIntegrable (fun t => (Ω : Set (Domain d)).indicator (g i) (coordinateLine i y t)) volume) :
    ∃ F : Domain d → 𝕜,
      u =ᵐ[volume.restrict (Ω : Set (Domain d))] F ∧
      ∀ i : Fin d, ∀ᵐ y : Transverse i ∂volume,
        LocallyAbsolutelyContinuousOn (fun t => F (coordinateLine i y t)) (fiber Ω i y) ∧
          ∀ᵐ t ∂volume.restrict (fiber Ω i y : Set ℝ),
            HasDerivAt (fun s => F (coordinateLine i y s)) (g i (coordinateLine i y t)) t := by
  have hcont (n : ℕ) (i : Fin d) : ∀ᵐ y : Transverse i ∂volume,
      ContinuousOn (fun t => f n (coordinateLine i y t)) (fiber (U n) i y) := by
    filter_upwards [hlocal n i] with y hy
    exact hy.1.continuousOn (fiber (U n) i y).isOpen
  obtain ⟨F, hFrep, hFeq⟩ := exists_glued_representative Ω U hcover u f hrep hcont
  have hsub (n : ℕ) : (U n : Set (Domain d)) ⊆ (Ω : Set (Domain d)) := by
    rw [hcover]
    exact subset_iUnion (fun n => (U n : Set (Domain d))) n
  refine ⟨F, hFrep, ?_⟩
  intro i
  filter_upwards [hFeq i, ae_all_iff.mpr (fun n => hlocal n i), hgli i] with y heq hy hg
  have hfib : (fiber Ω i y : Set ℝ) = ⋃ n, (fiber (U n) i y : Set ℝ) := by
    ext t
    change coordinateLine i y t ∈ (Ω : Set (Domain d)) ↔
      t ∈ ⋃ n, (fiber (U n) i y : Set ℝ)
    simp only [hcover, mem_iUnion, fiber, Opens.coe_mk, mem_preimage]
  have hd : ∀ᵐ t ∂volume.restrict (fiber Ω i y : Set ℝ),
      HasDerivAt (fun s => F (coordinateLine i y s)) (g i (coordinateLine i y t)) t := by
    rw [hfib]
    apply (ae_restrict_iUnion_iff _ _).mpr
    intro n
    filter_upwards [(hy n).2, ae_restrict_mem (fiber (U n) i y).isOpen.measurableSet] with t ht hti
    apply ht.congr_of_eventuallyEq
    filter_upwards [(fiber (U n) i y).isOpen.mem_nhds hti] with s hs
    exact heq n hs
  refine ⟨?_, hd⟩
  apply locallyAbsolutelyContinuousOn_of_local (fiber Ω i y).isOpen hg
  · intro t ht
    obtain ⟨n, htn⟩ : ∃ n, t ∈ (fiber (U n) i y : Set ℝ) := by
      simpa only [hfib, mem_iUnion] using ht
    obtain ⟨a, b, htab, hn, habU⟩ := exists_Icc_mem_subset_of_mem_nhds
      ((fiber (U n) i y).isOpen.mem_nhds htn)
    have hab : a ≤ b := htab.1.trans htab.2
    have hu : uIcc a b ⊆ (fiber (U n) i y : Set ℝ) := by
      simpa only [uIcc_of_le hab] using habU
    refine ⟨a, b, ?_, ?_, ?_, ?_⟩
    · simpa only [uIcc_of_le hab] using htab
    · simpa only [uIcc_of_le hab] using hn
    · exact hu.trans (fun _ hs => hsub n hs)
    · exact ((hy n).1 a b hu).congr (fun s hs => (heq n (hu hs)).symm)
  · filter_upwards [hd, ae_restrict_mem (fiber Ω i y).isOpen.measurableSet] with t ht hti
    simpa only [indicator_of_mem (show coordinateLine i y t ∈ (Ω : Set (Domain d)) from hti)] using ht


/-- A locally AC function with an integrable specified derivative satisfies
FTC globally. This avoids assuming a connectedness condition on an auxiliary
open set: the locality hypothesis here is on the whole real line. -/
theorem integral_eq_sub_of_locally_absolutelyContinuous {𝕜 : Type} [RCLike 𝕜]
    {f g : ℝ → 𝕜} (hg : Integrable g volume)
    (hf : ∀ x : ℝ, ∃ a b : ℝ, x ∈ uIcc a b ∧ uIcc a b ∈ 𝓝 x ∧
      AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ t ∂volume, HasDerivAt f (g t) t) (a b : ℝ) :
    (∫ t in a..b, g t) = f b - f a := by
  let F : ℝ → 𝕜 := fun x => f x - ∫ t in 0..x, g t
  have hF : IsLocallyConstant F := by
    apply (IsLocallyConstant.iff_eventually_eq F).mpr
    intro x
    obtain ⟨l, r, hx, hn, hac⟩ := hf x
    have hp := OneDimensional.integral_primitive_absolutelyContinuous
      (fun c d => hg.intervalIntegrable (a := c) (b := d)) l r 0
    have hz : ∀ᵐ t ∂volume, t ∈ uIcc l r → HasDerivAt F 0 t := by
      filter_upwards [hd, _root_.LocallyIntegrable.ae_hasDerivAt_integral hg.locallyIntegrable] with t ht hpt _
      convert ht.sub (hpt 0) using 1; simp
    obtain ⟨C, hC⟩ := (hac.sub hp).const_of_ae_hasDerivAt_zero hz
    filter_upwards [hn] with y hy
    exact (hC y hy).trans (hC x hx).symm
  have he := hF.apply_eq_of_preconnectedSpace b a
  dsimp [F] at he
  rw [← intervalIntegral.integral_interval_sub_left (a := 0) hg.intervalIntegrable
    hg.intervalIntegrable]
  linear_combination -he

/-- Integration by parts on any open subset of the line, including a
countable union of disjoint intervals. Only local AC inside U is required;
compact support of the test supplies zero neighborhoods outside U. The two
integrability hypotheses are exactly the pairings needed for Fubini. -/
theorem integral_test_mul_density_on_open {𝕜 : Type} [RCLike 𝕜]
    {U : Set ℝ} (hU : IsOpen U) {f g ψ : ℝ → 𝕜}
    (hf : LocallyAbsolutelyContinuousOn f U)
    (hd : ∀ᵐ t ∂volume.restrict U, HasDerivAt f (g t) t)
    (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ U)
    (h₁ : Integrable (fun t => deriv ψ t * f t) volume)
    (h₂ : Integrable (fun t => ψ t * g t) volume) :
    (∫ t, ψ t * g t) = -(∫ t, deriv ψ t * f t) := by
  let q : ℝ → 𝕜 := fun t => deriv ψ t * f t + ψ t * g t
  have hq : Integrable q volume := h₁.add h₂
  have hlocal : ∀ x : ℝ, ∃ a b : ℝ, x ∈ uIcc a b ∧ uIcc a b ∈ 𝓝 x ∧
      AbsolutelyContinuousOnInterval (fun t => ψ t * f t) a b := by
    intro x
    by_cases hx : x ∈ U
    · obtain ⟨a, b, hxab, hn, habU⟩ :=
        exists_Icc_mem_subset_of_mem_nhds (hU.mem_nhds hx)
      have hab : a ≤ b := hxab.1.trans hxab.2
      have hu : uIcc a b ⊆ U := by simpa [uIcc_of_le hab] using habU
      refine ⟨a, b, ?_, ?_, ?_⟩
      · simpa [uIcc_of_le hab] using hxab
      · simpa [uIcc_of_le hab] using hn
      · exact ((hψ.of_le (by simp) : ContDiff ℝ 1 ψ).contDiffOn.absolutelyContinuousOnInterval).smul
          (hf a b hu)
    · have hxψ : x ∈ (tsupport ψ)ᶜ := fun ht => hx (hsψ ht)
      obtain ⟨a, b, hxab, hn, habψ⟩ := exists_Icc_mem_subset_of_mem_nhds
        ((isClosed_tsupport ψ).isOpen_compl.mem_nhds hxψ)
      have hab : a ≤ b := hxab.1.trans hxab.2
      refine ⟨a, b, ?_, ?_, ?_⟩
      · simpa [uIcc_of_le hab] using hxab
      · simpa [uIcc_of_le hab] using hn
      · apply (show AbsolutelyContinuousOnInterval (fun _ : ℝ => (0 : 𝕜)) a b from
          (LipschitzWith.const 0).lipschitzOnWith.absolutelyContinuousOnInterval).congr
        intro t ht
        have ht' : t ∈ Icc a b := by simpa [uIcc_of_le hab] using ht
        simp [image_eq_zero_of_notMem_tsupport (habψ ht')]
  have hqd : ∀ᵐ t ∂volume, HasDerivAt (fun t => ψ t * f t) (q t) t := by
    filter_upwards [(ae_restrict_iff' hU.measurableSet).mp hd] with t ht
    by_cases htU : t ∈ U
    · exact (hψ.differentiable (by simp) t).hasDerivAt.mul (ht htU)
    · have htψ : t ∉ tsupport ψ := fun h => htU (hsψ h)
      have hz : (fun s => ψ s * f s) =ᶠ[𝓝 t] (fun _ => 0) := by
        filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds htψ] with s hs
        simp [image_eq_zero_of_notMem_tsupport hs]
      have hq0 : q t = 0 := by
        have hdz : deriv ψ t = 0 := by
          exact deriv_of_notMem_tsupport htψ
        simp [q, hdz, image_eq_zero_of_notMem_tsupport htψ]
      rw [hq0]
      exact (hasDerivAt_const t (0 : 𝕜)).congr_of_eventuallyEq hz
  obtain ⟨l, hl⟩ := hcψ.bddBelow
  obtain ⟨r, hr⟩ := hcψ.bddAbove
  let a := min l r - 1
  let b := max l r + 1
  have hab : a < b := by dsimp [a, b]; linarith [show min l r ≤ max l r from min_le_max]
  have hs : tsupport ψ ⊆ Ioo a b := by
    intro t ht
    have hlt := hl ht
    have htr := hr ht
    constructor <;> dsimp [a, b] <;> linarith [min_le_left l r, le_max_right l r]
  have hψa : ψ a = 0 := image_eq_zero_of_notMem_tsupport (fun ht => (hs ht).1.false)
  have hψb : ψ b = 0 := image_eq_zero_of_notMem_tsupport (fun ht => (hs ht).2.false)
  have he := integral_eq_sub_of_locally_absolutelyContinuous hq hlocal hqd a b
  have hs₁ : Function.support (fun t => deriv ψ t * f t) ⊆ Ioc a b := by
    intro t ht
    exact Ioo_subset_Ioc_self (hs (support_deriv_subset ((mul_ne_zero_iff.mp ht).1)))
  have hs₂ : Function.support (fun t => ψ t * g t) ⊆ Ioc a b := by
    intro t ht
    exact Ioo_subset_Ioc_self (hs (subset_tsupport ψ ((mul_ne_zero_iff.mp ht).1)))
  dsimp only [q] at he
  rw [intervalIntegral.integral_add h₁.intervalIntegrable h₂.intervalIntegrable,
    intervalIntegral.integral_eq_integral_of_support_subset hs₁,
    intervalIntegral.integral_eq_integral_of_support_subset hs₂, hψa, hψb] at he
  exact eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm] using he)

/-- A coordinate multi-index is represented by exactly one coordinate word. -/
theorem multiIndexWord_single {d : ℕ} (i : Fin d) :
    multiIndexWord (Pi.single i 1) = [i] := by
  classical
  have hl : (multiIndexWord (Pi.single i 1)).length = 1 := by simp
  obtain ⟨j, hj⟩ := List.length_eq_one_iff.mp hl
  have hc := multiIndexWord_count (Pi.single i 1) i
  rw [hj] at hc
  have hji : j = i := by simpa [List.count_singleton] using hc
  simpa [hji] using hj

/-- Every multi-index of order at most one is zero or one coordinate. -/
theorem multiIndex_order_one_cases {d : ℕ} (α : Fin d → ℕ)
    (hα : ∑ i, α i ≤ 1) : α = 0 ∨ ∃ i, α = Pi.single i 1 := by
  classical
  by_cases hz : α = 0
  · exact Or.inl hz
  · right
    obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
      by_contra! h
      exact hz (funext h)
    refine ⟨i, funext fun j => ?_⟩
    have h := Finset.sum_le_one_iff.mp hα
    by_cases hj : j = i
    · subst j
      simpa using (h i i (Finset.mem_univ _) (Finset.mem_univ _) hi hi).2
    · have hzj : α j = 0 := by
        by_contra hn
        exact hj (h j i (Finset.mem_univ _) (Finset.mem_univ _) hn hi).1
      simp [hj, hzj]

/-- First-order membership in the original graph is equivalent to existence
of its coordinate weak derivatives. This is independent of the ACL theorem. -/
theorem first_order_membership_iff {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : DomainLp 𝕜 Ω p) :
    (∃ v : SobolevSpace 𝕜 d Ω 1 p, v.val (zeroIndex d 1) = u) ↔
      ∃ g : Fin d → DomainLp 𝕜 Ω p, HasWeakCoordinateDerivatives u g := by
  classical
  rw [sobolev_membership 𝕜 d Ω 1 p u]
  constructor
  · intro h
    have hcoord (i : Fin d) := h (Pi.single i 1) (by simp)
    choose g hg using hcoord
    refine ⟨g, fun i => ?_⟩
    have he := hg i
    change lpDistribution (g i) = distributionDerivative 𝕜 d Ω
      (multiIndexWord (Pi.single i 1)) (lpDistribution u) at he
    simpa [multiIndexWord_single, distributionDerivative_cons,
      distributionDerivative_nil] using he
  · rintro ⟨g, hg⟩ α hα
    rcases multiIndex_order_one_cases α hα with rfl | ⟨i, rfl⟩
    · exact ⟨u, (derivative_zero (lpDistribution u)).symm⟩
    · refine ⟨g i, ?_⟩
      change lpDistribution (g i) = distributionDerivative 𝕜 d Ω
        (multiIndexWord (Pi.single i 1)) (lpDistribution u)
      simpa [multiIndexWord_single, distributionDerivative_cons,
        distributionDerivative_nil] using hg i

section LinePrimitives
open ExpandedFA.Sobolev.OneDimensional

private theorem primitive_real_test_identity {𝕜 : Type} [RCLike 𝕜]
    {g : ℝ → 𝕜} (hg : LocallyIntegrable g volume) (ψ : ℝ → ℝ)
    (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ) (hcψ : HasCompactSupport ψ) :
    (∫ t, ψ t • g t) = -(∫ t, deriv ψ t • (∫ s in (0 : ℝ)..t, g s)) := by
  let ψk : ℝ → 𝕜 := fun t => (ψ t : 𝕜)
  have hk : ContDiff ℝ (↑(⊤ : ℕ∞)) ψk :=
    (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp hψ
  have hck : HasCompactSupport ψk := hcψ.comp_left (by simp)
  have hd (t : ℝ) : deriv ψk t = ((deriv ψ t : ℝ) : 𝕜) := by
    exact ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).hasFDerivAt.comp_hasDerivAt t
      (hψ.differentiable (by simp) t).hasDerivAt).deriv
  have h := integral_test_mul_primitive hg 0 hk hck
  simp_rw [hd] at h
  simpa only [ψk, RCLike.real_smul_eq_coe_mul] using h

/-- A weak one-dimensional derivative on an arbitrary open set has a locally
absolutely continuous representative, provided the two functions are locally
integrable on the ambient line. No global slice Lp hypothesis is required. -/
theorem exists_locallyAC_of_integral_deriv {𝕜 : Type} [RCLike 𝕜]
    {U : Set ℝ} (hU : IsOpen U) {u g : ℝ → 𝕜}
    (hu : LocallyIntegrable u volume) (hg : LocallyIntegrable g volume)
    (hw : ∀ ψ : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ t, ψ t • g t) = -(∫ t, deriv ψ t • u t)) :
    ∃ f : ℝ → 𝕜, u =ᵐ[volume.restrict U] f ∧
      LocallyAbsolutelyContinuousOn f U ∧
      ∀ᵐ t ∂volume.restrict U, HasDerivAt f (g t) t := by
  classical
  let P : ℝ → 𝕜 := fun t => ∫ s in (0 : ℝ)..t, g s
  have hgi (a b : ℝ) : IntervalIntegrable g volume a b :=
    (hg.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have hPc : Continuous P := intervalIntegral.continuous_primitive hgi 0
  have hPli : LocallyIntegrable P volume := hPc.locallyIntegrable
  have hzero : ∀ ψ : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ t, deriv ψ t • (u t - P t)) = 0 := by
    intro ψ hψ hcψ hsψ
    have he := neg_injective ((hw ψ hψ hcψ hsψ).symm.trans
      (primitive_real_test_identity hg ψ hψ hcψ))
    have hiu := hu.integrable_smul_left_of_hasCompactSupport
      (hψ.continuous_deriv (by simp)) hcψ.deriv
    have hip := hPli.integrable_smul_left_of_hasCompactSupport
      (hψ.continuous_deriv (by simp)) hcψ.deriv
    simp_rw [smul_sub]
    rw [integral_sub hiu hip, he, sub_self]
  let good : Set (Set ℝ) := {C | IsOpen C ∧ OrdConnected C ∧ C ⊆ U}
  have hc : ∀ C : good, ∃ c : 𝕜,
      (fun t => u t - P t) =ᵐ[volume.restrict (C : Set ℝ)] fun _ => c := by
    intro C
    apply ae_eq_const_of_integral_deriv_eq_zero C.property.1 C.property.2.1
      (hu.sub hPli)
    intro ψ hψ hcψ hsψ
    exact hzero ψ hψ hcψ (hsψ.trans C.property.2.2)
  choose c hc using hc
  let c' (C : Set ℝ) : 𝕜 := if hC : C ∈ good then c ⟨C, hC⟩ else 0
  have hc' (C : Set ℝ) (hC : C ∈ good) :
      (fun t => u t - P t) =ᵐ[volume.restrict C] fun _ => c' C := by
    simpa only [c', dite_eq_left hC] using hc ⟨C, hC⟩
  have hcomp (x : ℝ) : connectedComponentIn U x ∈ good :=
    ⟨hU.connectedComponentIn, isPreconnected_connectedComponentIn.ordConnected,
      connectedComponentIn_subset U x⟩
  let f : ℝ → 𝕜 := fun t => P t + c' (connectedComponentIn U t)
  have hfeq (x t : ℝ) (ht : t ∈ connectedComponentIn U x) :
      f t = P t + c' (connectedComponentIn U x) := by
    dsimp [f]
    rw [← connectedComponentIn_eq ht]
  refine ⟨f, ?_, ?_, ?_⟩
  · obtain ⟨r, hrc, hrcover⟩ := (HereditarilyLindelofSpace.isLindelof U).elim_countable_subcover
      (connectedComponentIn U) (fun _ => hU.connectedComponentIn) (by
        intro t ht
        exact mem_iUnion.mpr ⟨t, mem_connectedComponentIn ht⟩)
    apply ae_restrict_of_ae_restrict_of_subset hrcover
    apply (ae_eq_restrict_biUnion_iff (connectedComponentIn U) hrc u f).mpr
    intro x _
    filter_upwards [hc' _ (hcomp x),
      ae_restrict_mem hU.connectedComponentIn.measurableSet] with t ht hti
    rw [hfeq x t hti]
    exact (sub_eq_iff_eq_add.mp ht).trans (add_comm _ _)
  · intro a b hab
    have hsub : uIcc a b ⊆ connectedComponentIn U a :=
      isPreconnected_uIcc.subset_connectedComponentIn left_mem_uIcc hab
    have hPa := integral_primitive_absolutelyContinuous hgi a b 0
    have hca : AbsolutelyContinuousOnInterval (fun _ : ℝ => c' (connectedComponentIn U a)) a b :=
      (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
    exact (hPa.add hca).congr (fun t ht => (hfeq a t (hsub ht)).symm)
  · filter_upwards [ae_restrict_of_ae (_root_.LocallyIntegrable.ae_hasDerivAt_integral hg),
      ae_restrict_mem hU.measurableSet] with t ht hti
    apply ((ht 0).add_const (c' (connectedComponentIn U t))).congr_of_eventuallyEq
    filter_upwards [hU.connectedComponentIn.mem_nhds (mem_connectedComponentIn hti)] with s hs
    exact hfeq t s hs


private theorem weakDerivative_real_test_identity {𝕜 : Type} [RCLike 𝕜]
    {I : Opens ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (v w : DomainLp 𝕜 (lineDomain I) p)
    (hw : lpDistribution w = -(lpDistribution v).comp (testPartialCLM [0]))
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ)
    (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ (I : Set ℝ)) :
    (∫ t, ψ t • extendedLineFunction w t) =
      -(∫ t, deriv ψ t • extendedLineFunction v t) := by
  let V := ofWeakDerivative v w hw
  let φ := realLineTest (𝕜 := 𝕜) ψ hψ hcψ hsψ
  have hi := weakDerivative_test_identity V φ
  simp only [V, ofWeakDerivative_base, ofWeakDerivative_derivative] at hi
  have he : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) ℝ).symm
      (volume : Measure ℝ) (volume : Measure (Domain 1)) :=
    MeasurePreserving.symm (MeasurableEquiv.funUnique (Fin 1) ℝ)
      (volume_preserving_funUnique (Fin 1) ℝ)
  rw [← he.integral_comp' (fun z : Domain 1 => φ z * lineFunction w (z 0)),
    ← he.integral_comp' (fun z : Domain 1 => testPartialCLM [0] φ z * lineFunction v (z 0))] at hi
  change (∫ t, (ψ t : 𝕜) * lineFunction w t) =
    -(∫ t, testPartialCLM [0] (realLineTest (𝕜 := 𝕜) ψ hψ hcψ hsψ) (linePoint t) *
      lineFunction v t) at hi
  simp only [testPartial_realLineTest] at hi
  have hie (a : DomainLp 𝕜 (lineDomain I) p) (χ : ℝ → ℝ)
      (hχ : Function.support χ ⊆ (I : Set ℝ)) :
      (fun t => χ t • extendedLineFunction a t) =
      (fun t => χ t • lineFunction a t) := by
    funext t
    by_cases ht : t ∈ (I : Set ℝ)
    · rw [extendedLineFunction, indicator_of_mem ht]
    · have hz : χ t = 0 := by
        by_contra hne
        exact ht (hχ hne)
      simp only [hz, zero_smul]
  rw [hie w ψ ((subset_tsupport ψ).trans hsψ),
    hie v (deriv ψ) (support_deriv_subset.trans hsψ)]
  simpa only [RCLike.real_smul_eq_coe_mul] using hi

/-- The forward ACL implication in dimension one, on arbitrary open domains. -/
theorem weak_to_acl_lineDomain {𝕜 : Type} [RCLike 𝕜]
    (I : Opens ℝ) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : DomainLp 𝕜 (lineDomain I) p)
    (g : Fin 1 → DomainLp 𝕜 (lineDomain I) p)
    (hweak : HasWeakCoordinateDerivatives u g) :
    ∃ f : Domain 1 → 𝕜,
      u =ᵐ[volume.restrict (lineDomain I : Set (Domain 1))] f ∧
      HasACLDerivatives (lineDomain I) f g := by
  obtain ⟨F, hrep, hAC, hd⟩ := exists_locallyAC_of_integral_deriv I.isOpen
    (extendedLineFunction_locallyIntegrable u)
    (extendedLineFunction_locallyIntegrable (g 0))
    (weakDerivative_real_test_identity u (g 0) (hweak 0))
  have hrep' : lineFunction u =ᵐ[volume.restrict (I : Set ℝ)] F := by
    filter_upwards [hrep, ae_restrict_mem I.isOpen.measurableSet] with t ht hti
    simpa only [extendedLineFunction, indicator_of_mem hti] using ht
  refine ⟨fun z => F (z 0), represents_of_lineFunction_ae u hrep', ?_⟩
  intro i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  have hline (y : Transverse (0 : Fin 1)) (t : ℝ) :
      coordinateLine 0 y t = linePoint t := by
    ext j
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst j
    simp
  have hfiber (y : Transverse (0 : Fin 1)) : fiber (lineDomain I) 0 y = I := by
    ext t
    change coordinateLine 0 y t 0 ∈ (I : Set ℝ) ↔ t ∈ (I : Set ℝ)
    simp
  apply ae_of_all
  intro y
  constructor
  · simpa only [hline, linePoint_apply, hfiber] using hAC
  · have hdeq : ∀ᵐ t ∂volume.restrict (I : Set ℝ),
        HasDerivAt F (lineFunction (g 0) t) t := by
      filter_upwards [hd, ae_restrict_mem I.isOpen.measurableSet] with t ht hti
      simpa only [extendedLineFunction, indicator_of_mem hti] using ht
    simpa only [hline, linePoint_apply, hfiber, lineFunction] using hdeq

theorem weak_to_acl_dimension_one {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Domain 1)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : DomainLp 𝕜 Ω p) (g : Fin 1 → DomainLp 𝕜 Ω p)
    (hweak : HasWeakCoordinateDerivatives u g) :
    ∃ f : Domain 1 → 𝕜,
      u =ᵐ[volume.restrict (Ω : Set (Domain 1))] f ∧ HasACLDerivatives Ω f g := by
  let I : Opens ℝ := ⟨linePoint ⁻¹' (Ω : Set (Domain 1)),
    Ω.isOpen.preimage (continuous_pi fun _ => continuous_id)⟩
  have hΩ : lineDomain I = Ω := by
    ext z
    change linePoint (z 0) ∈ (Ω : Set (Domain 1)) ↔ z ∈ (Ω : Set (Domain 1))
    simp
  have hgeneral : ∀ (Ω' : Opens (Domain 1)), lineDomain I = Ω' →
      ∀ (u' : DomainLp 𝕜 Ω' p) (g' : Fin 1 → DomainLp 𝕜 Ω' p),
        HasWeakCoordinateDerivatives u' g' →
          ∃ f : Domain 1 → 𝕜, u' =ᵐ[volume.restrict (Ω' : Set (Domain 1))] f ∧
            HasACLDerivatives Ω' f g' := by
    intro Ω' hΩ' u' g' hweak'
    subst Ω'
    exact weak_to_acl_lineDomain I u' g' hweak'
  exact hgeneral Ω hΩ u g hweak


end LinePrimitives

section TensorBridge

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Delete the distinguished coordinate. -/
def transverseProjection (i : Fin d) (x : Domain d) : Transverse i := fun j => x j

@[simp] theorem transverseProjection_coordinateLine (i : Fin d) (y : Transverse i) (t : ℝ) :
    transverseProjection i (coordinateLine i y t) = y := by
  ext j
  exact coordinateLine_transverse i y t j

theorem transverseProjection_contDiff (i : Fin d) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (transverseProjection i) := by
  exact contDiff_pi.mpr (fun j => contDiff_apply ℝ (fun _ : Fin d => ℝ) j.val)

/-- Tensor tests have compact support in the full ambient space. -/
theorem hasCompactSupport_tensor (i : Fin d) (η : Transverse i → ℝ)
    (hη : HasCompactSupport η) (ψ : ℝ → 𝕜) (hψ : HasCompactSupport ψ) :
    HasCompactSupport (fun x : Domain d => η (transverseProjection i x) • ψ (x i)) := by
  let e := Homeomorph.funSplitAt ℝ i
  have hs : tsupport (fun x : Domain d => η (transverseProjection i x) • ψ (x i)) ⊆
      e ⁻¹' (tsupport ψ ×ˢ tsupport η) := by
    apply closure_minimal
    · intro x hx
      change x i ∈ tsupport ψ ∧ transverseProjection i x ∈ tsupport η
      exact ⟨subset_tsupport ψ (fun hz => hx (by simp [hz])),
        subset_tsupport η (fun hz => hx (by simp [hz]))⟩
    · exact ((isClosed_tsupport ψ).prod (isClosed_tsupport η)).preimage e.continuous
  exact (e.isCompact_preimage.mpr (hψ.prod hη)).of_isClosed_subset
    (isClosed_tsupport _) hs

/-- Smooth tensor test supported in an interior rectangle. -/
def tensorTest (i : Fin d) (η : Transverse i → ℝ)
    (hη : ContDiff ℝ (↑(⊤ : ℕ∞)) η) (hcη : HasCompactSupport η)
    (ψ : ℝ → 𝕜) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ) (hcψ : HasCompactSupport ψ)
    (hs : ∀ y ∈ tsupport η, ∀ t ∈ tsupport ψ, coordinateLine i y t ∈ Ω) :
    Tests 𝕜 Ω where
  toFun x := η (transverseProjection i x) • ψ (x i)
  contDiff' := (hη.comp (transverseProjection_contDiff i)).smul
    (hψ.comp (contDiff_apply ℝ (fun _ : Fin d => ℝ) i))
  hasCompactSupport' := hasCompactSupport_tensor i η hcη ψ hcψ
  tsupport_subset' := by
    intro x hx
    have hηx : transverseProjection i x ∈ tsupport η := by
      exact tsupport_comp_subset_preimage η (transverseProjection_contDiff i).continuous
        (tsupport_smul_subset_left _ _ hx)
    have hψx : x i ∈ tsupport ψ := by
      exact tsupport_comp_subset_preimage ψ (show Continuous (fun x : Domain d => x i) from continuous_apply i)
        (tsupport_smul_subset_right _ _ hx)
    have he : coordinateLine i (transverseProjection i x) (x i) = x := by
      ext j
      by_cases h : j = i <;> simp [coordinateLine, transverseProjection, h]
    exact he ▸ hs _ hηx _ hψx

@[simp] theorem tensorTest_apply (i : Fin d) (η : Transverse i → ℝ) (hη hcη)
    (ψ : ℝ → 𝕜) (hψ hcψ)
    (hs : ∀ y ∈ tsupport η, ∀ t ∈ tsupport ψ, coordinateLine i y t ∈ Ω) (x : Domain d) :
    tensorTest i η hη hcη ψ hψ hcψ hs x = η (transverseProjection i x) • ψ (x i) := rfl

theorem tensorTest_partial (i : Fin d) (η : Transverse i → ℝ) (hη hcη)
    (ψ : ℝ → 𝕜) (hψ hcψ)
    (hs : ∀ y ∈ tsupport η, ∀ t ∈ tsupport ψ, coordinateLine i y t ∈ Ω) (x : Domain d) :
    testPartialCLM [i] (tensorTest i η hη hcη ψ hψ hcψ hs) x =
      η (transverseProjection i x) • deriv ψ (x i) := by
  have he : coordinateLine i (transverseProjection i x) (x i) = x := by
    ext j
    by_cases h : j = i <;> simp [coordinateLine, transverseProjection, h]
  rw [← he, testPartial_on_coordinateLine]
  simp only [tensorTest_apply, transverseProjection_coordinateLine, coordinateLine_self]
  exact deriv_const_smul (η (transverseProjection i x)) (hψ.differentiable (by simp) (x i))

/-- The original weak coordinate identity annihilates every test defect. -/
theorem weak_test_defect_eq_zero (u : DomainLp 𝕜 Ω p) (g : Fin d → DomainLp 𝕜 Ω p)
    (hweak : HasWeakCoordinateDerivatives u g) (i : Fin d) (φ : Tests 𝕜 Ω) :
    (∫ x, φ x * g i x + testPartialCLM [i] φ x * u x) = 0 := by
  have he := congrArg (fun T : ScalarDistribution 𝕜 Ω => T φ) (hweak i)
  simp only [neg_apply, ContinuousLinearMap.comp_apply, lpDistribution_apply] at he
  have he₁ : (∫ x in (Ω : Set (Domain d)), φ x * g i x) = ∫ x, φ x * g i x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      simp [φ.zero_on_compl hx]
  have he₂ : (∫ x in (Ω : Set (Domain d)), testPartialCLM [i] φ x * u x) =
      ∫ x, testPartialCLM [i] φ x * u x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      simp [(testPartialCLM [i] φ).zero_on_compl hx]
  rw [he₁, he₂] at he
  rw [integral_add (integrable_test_mul_lp φ (g i))
    (integrable_test_mul_lp (testPartialCLM [i] φ) u)]
  exact eq_neg_iff_add_eq_zero.mp he

/-- Genuine tensor identities follow from the original weak derivative,
without assuming a family of fiberwise identities. -/
theorem weak_tensor_defect_eq_zero (u : DomainLp 𝕜 Ω p) (g : Fin d → DomainLp 𝕜 Ω p)
    (hweak : HasWeakCoordinateDerivatives u g) (i : Fin d)
    (η : Transverse i → ℝ) (hη : ContDiff ℝ (↑(⊤ : ℕ∞)) η) (hcη : HasCompactSupport η)
    (ψ : ℝ → 𝕜) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ) (hcψ : HasCompactSupport ψ)
    (hs : ∀ y ∈ tsupport η, ∀ t ∈ tsupport ψ, coordinateLine i y t ∈ Ω) :
    (∫ y : Transverse i, ∫ t : ℝ,
      η y • (ψ t * g i (coordinateLine i y t) + deriv ψ t * u (coordinateLine i y t))) = 0 := by
  let φ := tensorTest i η hη hcη ψ hψ hcψ hs
  have hi : Integrable (fun x => φ x * g i x + testPartialCLM [i] φ x * u x) volume :=
    (integrable_test_mul_lp φ (g i)).add
      (integrable_test_mul_lp (testPartialCLM [i] φ) u)
  have he := weak_test_defect_eq_zero u g hweak i φ
  rw [integral_coordinateLines i hi] at he
  simpa only [φ, tensorTest_apply, tensorTest_partial,
    transverseProjection_coordinateLine, coordinateLine_self, smul_mul_assoc, smul_add] using he

/-- The transverse-first coordinate pullback preserves ambient integrability. -/
theorem integrable_product_coordinateLines (i : Fin d) {h : Domain d → 𝕜}
    (hh : Integrable h volume) :
    Integrable (fun z : Transverse i × ℝ => h (coordinateLine i z.1 z.2)) volume := by
  have hm := (coordinateEquiv_measurePreserving i).symm (coordinateEquiv i)
  have hi := hm.integrable_comp_of_integrable hh
  simpa only [Function.comp_def, ← coordinateEquiv_symm_apply, Prod.fst_swap,
    Prod.snd_swap, Prod.mk.eta, Prod.swap, Measure.volume_eq_prod] using hi.swap

/-- Local Lp data are L1 on each compact coordinate rectangle inside Ω. -/
theorem integrable_lp_coordinate_rectangle (u : DomainLp 𝕜 Ω p) (i : Fin d)
    (K : Set (Transverse i)) (hK : IsCompact K) (a b : ℝ)
    (hs : ∀ y ∈ K, ∀ t ∈ Icc a b, coordinateLine i y t ∈ Ω) :
    Integrable (fun z : Transverse i × ℝ => u (coordinateLine i z.1 z.2))
      ((volume.restrict K).prod (volume.restrict (Icc a b))) := by
  let e := coordinateEquiv i
  let C : Set (Domain d) := e.symm '' (Icc a b ×ˢ K)
  have hC : IsCompact C := (isCompact_Icc.prod hK).image
    (Homeomorph.funSplitAt ℝ i).symm.continuous
  have hCs : C ⊆ Ω := by
    rintro _ ⟨⟨t,y⟩, hty, rfl⟩
    change (coordinateEquiv i).symm (t, y) ∈ (Ω : Set (Domain d))
    rw [coordinateEquiv_symm_apply]
    exact hs y hty.2 t hty.1
  have hi := (domainLp_locallyIntegrable u).integrableOn_compact_subset hCs hC
  have hi' : IntegrableOn u C volume := by
    simpa only [IntegrableOn, Measure.restrict_restrict_of_subset hCs] using hi
  have hm := (coordinateEquiv_measurePreserving i).symm (coordinateEquiv i)
  have hp := (hm.integrableOn_image e.symm.measurableEmbedding).mp hi'
  have hp' : IntegrableOn (fun z : ℝ × Transverse i => u (coordinateLine i z.2 z.1))
      (Icc a b ×ˢ K) volume := by
    simpa only [e, Function.comp_def, ← coordinateEquiv_symm_apply, Prod.mk.eta] using hp
  have ht := hp'.swap
  simpa only [IntegrableOn, ← Measure.prod_restrict, Function.comp_def, Prod.fst_swap, Prod.snd_swap] using ht

/-- Tensor identity restricted to the rectangle supporting the tests. -/
theorem weak_tensor_rectangle_defect_eq_zero (u : DomainLp 𝕜 Ω p)
    (g : Fin d → DomainLp 𝕜 Ω p) (hweak : HasWeakCoordinateDerivatives u g)
    (i : Fin d) (U : Set (Transverse i)) (a b : ℝ)
    (η : Transverse i → ℝ) (hη : ContDiff ℝ (↑(⊤ : ℕ∞)) η)
    (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ U)
    (ψ : CompactLineTest 𝕜 a b)
    (hs : ∀ y ∈ U, ∀ t ∈ Icc a b, coordinateLine i y t ∈ Ω) :
    (∫ z : Transverse i × ℝ,
      η z.1 • (ψ.toTest z.2 * g i (coordinateLine i z.1 z.2) +
        deriv ψ.toTest z.2 * u (coordinateLine i z.1 z.2))
      ∂((volume.restrict U).prod (volume.restrict (Icc a b)))) = 0 := by
  have hsupport : ∀ y ∈ tsupport η, ∀ t ∈ tsupport ψ.toTest,
      coordinateLine i y t ∈ Ω := fun y hy t ht => hs y (hsη hy) t (ψ.support_subset ht)
  let φ := tensorTest i η hη hcη ψ.toTest ψ.toTest.contDiff ψ.toTest.hasCompactSupport hsupport
  have hi : Integrable (fun x => φ x * g i x + testPartialCLM [i] φ x * u x) volume :=
    (integrable_test_mul_lp φ (g i)).add
      (integrable_test_mul_lp (testPartialCLM [i] φ) u)
  have hp : Integrable (fun z : Transverse i × ℝ =>
      η z.1 • (ψ.toTest z.2 * g i (coordinateLine i z.1 z.2) +
        deriv ψ.toTest z.2 * u (coordinateLine i z.1 z.2))) volume := by
    simpa only [φ, tensorTest_apply, tensorTest_partial,
      transverseProjection_coordinateLine, coordinateLine_self, smul_mul_assoc, smul_add]
      using integrable_product_coordinateLines i hi
  rw [Measure.prod_restrict]
  calc
    _ = ∫ z : Transverse i × ℝ,
        η z.1 • (ψ.toTest z.2 * g i (coordinateLine i z.1 z.2) +
          deriv ψ.toTest z.2 * u (coordinateLine i z.1 z.2)) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      rintro ⟨y,t⟩ hyt
      by_cases hy : y ∈ U
      · have ht : t ∉ Icc a b := fun ht => hyt ⟨hy,ht⟩
        have hψt : t ∉ tsupport ψ.toTest := fun h => ht (ψ.support_subset h)
        simp only [image_eq_zero_of_notMem_tsupport hψt, deriv_of_notMem_tsupport hψt,
          zero_mul, add_zero, smul_zero]
      · have hηy : η y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hsη h))
        simp only [hηy, zero_smul]
    _ = 0 := by
      rw [Measure.volume_eq_prod] at hp ⊢
      rw [integral_prod _ hp]
      exact weak_tensor_defect_eq_zero u g hweak i η hη hcη ψ.toTest
        ψ.toTest.contDiff ψ.toTest.hasCompactSupport hsupport

/-- On any compact interior coordinate rectangle, one exceptional transverse
set suffices for the weak identity against every line test. -/
theorem ae_line_identity_of_weak (u : DomainLp 𝕜 Ω p)
    (g : Fin d → DomainLp 𝕜 Ω p) (hweak : HasWeakCoordinateDerivatives u g)
    (i : Fin d) (U : Opens (Transverse i)) (hU : IsCompact (closure (U : Set (Transverse i))))
    (a b : ℝ)
    (hs : ∀ y ∈ closure (U : Set (Transverse i)), ∀ t ∈ Icc a b,
      coordinateLine i y t ∈ Ω) :
    ∀ᵐ y ∂volume.restrict (U : Set (Transverse i)), ∀ ψ : CompactLineTest 𝕜 a b,
      (∫ t in Icc a b, ψ.toTest t * g i (coordinateLine i y t) +
        deriv ψ.toTest t * u (coordinateLine i y t)) = 0 := by
  have hl (v : DomainLp 𝕜 Ω p) :
      Integrable (fun z : Transverse i × ℝ => v (coordinateLine i z.1 z.2))
        ((volume.restrict (U : Set (Transverse i))).prod (volume.restrict (Icc a b))) := by
    have hv := integrable_lp_coordinate_rectangle v i _ hU a b hs
    rw [Measure.prod_restrict] at hv ⊢
    exact hv.mono_measure (Measure.restrict_mono
      (Set.prod_mono subset_closure Subset.rfl) le_rfl)
  apply ae_line_identity_of_tensor_tests U a b
    (fun z => u (coordinateLine i z.1 z.2))
    (fun z => g i (coordinateLine i z.1 z.2)) (hl u) (hl (g i))
  intro ψ η hη hcη hsη
  exact weak_tensor_rectangle_defect_eq_zero u g hweak i U a b η hη hcη hsη ψ
    (fun y hy t ht => hs y (subset_closure hy) t ht)

theorem coordinateLines_continuous {d : ℕ} (i : Fin d) :
    Continuous (fun z : Transverse i × ℝ => coordinateLine i z.1 z.2) := by
  apply continuous_pi
  intro j
  dsimp only [coordinateLine]
  split_ifs
  · exact continuous_snd
  · exact (continuous_apply _).comp continuous_fst

/-- Transverse parameters whose entire closed segment lies in the domain. -/
def lineTube {d : ℕ} (Ω : Opens (Domain d)) (i : Fin d) (a b : ℝ) :
    Opens (Transverse i) where
  carrier := {y | ∀ t ∈ Icc a b, coordinateLine i y t ∈ Ω}
  is_open' := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    exact (Ω.isOpen.preimage (coordinateLines_continuous i)).mem_nhds (hy t ht)

/-- Local a.e. assertions on open neighborhoods combine on a second-countable space. -/
theorem ae_on_set_of_locally_ae {E : Type*} [TopologicalSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] (μ : Measure E) (V : Set E) (P : E → Prop)
    (hloc : ∀ y ∈ V, ∃ U : Opens E, y ∈ U ∧ ∀ᵐ x ∂μ.restrict (U : Set E), P x) :
    ∀ᵐ y ∂μ.restrict V, P y := by
  classical
  choose U hmem hae using fun y : V => hloc y y.property
  have hcover : V ⊆ ⋃ y : V, (U y : Set E) := by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y,hy⟩, hmem ⟨y,hy⟩⟩
  obtain ⟨c,hcc,hc⟩ := (HereditarilyLindelofSpace.isLindelof V).elim_countable_subcover
    (fun y : V => (U y : Set E)) (fun y => (U y).isOpen) hcover
  apply ae_restrict_of_ae_restrict_of_subset hc
  exact (ae_restrict_biUnion_iff _ hcc _).mpr (fun y _ => hae y)

/-- The weak line identity holds throughout the transverse tube, with a
single exceptional set for all tests on the specified segment. -/
theorem ae_line_identity_on_tube {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : DomainLp 𝕜 Ω p) (g : Fin d → DomainLp 𝕜 Ω p)
    (hweak : HasWeakCoordinateDerivatives u g) (i : Fin d) (a b : ℝ) :
    ∀ᵐ y ∂volume.restrict (lineTube Ω i a b : Set (Transverse i)),
      ∀ ψ : CompactLineTest 𝕜 a b,
      (∫ t in Icc a b, ψ.toTest t * g i (coordinateLine i y t) +
        deriv ψ.toTest t * u (coordinateLine i y t)) = 0 := by
  apply ae_on_set_of_locally_ae
  intro y hy
  obtain ⟨ε,hε,hεV⟩ := Metric.isOpen_iff.mp (lineTube Ω i a b).isOpen y hy
  let U : Opens (Transverse i) := ⟨Metric.ball y (ε/2), Metric.isOpen_ball⟩
  have hUc : IsCompact (closure (U : Set (Transverse i))) :=
    (isCompact_closedBall y (ε/2)).of_isClosed_subset isClosed_closure
      Metric.closure_ball_subset_closedBall
  have hUV : closure (U : Set (Transverse i)) ⊆ lineTube Ω i a b :=
    Metric.closure_ball_subset_closedBall.trans
      ((Metric.closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεV)
  refine ⟨U, ?_, ?_⟩
  · exact Metric.mem_ball_self (by linarith)
  · exact ae_line_identity_of_weak u g hweak i U hUc a b (fun z hz t ht => hUV hz t ht)

/-- Countably many rational segments use a single exceptional transverse set. -/
theorem ae_all_rational_line_identity {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : DomainLp 𝕜 Ω p) (g : Fin d → DomainLp 𝕜 Ω p)
    (hweak : HasWeakCoordinateDerivatives u g) (i : Fin d) :
    ∀ᵐ y : Transverse i ∂volume, ∀ a b : ℚ,
      y ∈ lineTube Ω i (a : ℝ) (b : ℝ) → ∀ ψ : CompactLineTest 𝕜 (a : ℝ) (b : ℝ),
      (∫ t in Icc (a : ℝ) (b : ℝ), ψ.toTest t * g i (coordinateLine i y t) +
        deriv ψ.toTest t * u (coordinateLine i y t)) = 0 := by
  apply ae_all_iff.mpr
  intro a
  apply ae_all_iff.mpr
  intro b
  exact (ae_restrict_iff' (lineTube Ω i (a : ℝ) (b : ℝ)).isOpen.measurableSet).mp
    (ae_line_identity_on_tube u g hweak i (a : ℝ) (b : ℝ))


end TensorBridge

/-- A nonempty open Euclidean set is a countable union of open boxes whose
closed boxes are compact and lie inside the original set. The balls here use
the finite product sup metric, so they are actual coordinate rectangles. -/
theorem exists_countable_box_cover {d : ℕ} (Ω : Opens (Domain d))
    (hΩ : (Ω : Set (Domain d)).Nonempty) :
    ∃ (c : ℕ → Domain d) (r : ℕ → ℝ),
      (∀ n, 0 < r n) ∧
      (Ω : Set (Domain d)) = ⋃ n, Metric.ball (c n) (r n) ∧
      ∀ n, IsCompact (Metric.closedBall (c n) (r n)) ∧
        Metric.closedBall (c n) (r n) ⊆ (Ω : Set (Domain d)) ∧
        Metric.ball (c n) (r n) = Set.pi Set.univ
          (fun j => Ioo (c n j - r n) (c n j + r n)) := by
  classical
  have hnb : ∀ x : (Ω : Set (Domain d)), ∃ r : ℝ, 0 < r ∧
      Metric.closedBall (x : Domain d) r ⊆ (Ω : Set (Domain d)) := by
    intro x
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp Ω.isOpen x x.property
    refine ⟨ε / 2, by positivity, ?_⟩
    exact (Metric.closedBall_subset_ball (by linarith)).trans hsub
  choose r hr hs using hnb
  let : Nonempty (Ω : Set (Domain d)) := hΩ.to_subtype
  obtain ⟨v, hv⟩ := (HereditarilyLindelofSpace.isLindelof (Ω : Set (Domain d))).indexed_countable_subcover
    (fun x : (Ω : Set (Domain d)) => Metric.ball (x : Domain d) (r x))
    (fun _ => Metric.isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hr _)⟩)
  refine ⟨fun n => (v n : Domain d), fun n => r (v n), fun n => hr (v n), ?_, ?_⟩
  · exact hv.antisymm (iUnion_subset fun n => Metric.ball_subset_closedBall.trans (hs (v n)))
  · intro n
    refine ⟨isCompact_closedBall _ _, hs (v n), ?_⟩
    rw [ball_pi _ (hr (v n))]
    simp only [Real.ball_eq_Ioo]

/-- It suffices to construct the common ACL representative on every compactly
contained coordinate box; countability and overlap uniqueness globalize it. -/
theorem weak_to_acl_of_local_boxes {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : DomainLp 𝕜 Ω p) (g : Fin d → DomainLp 𝕜 Ω p)
    (hlocal : ∀ (c : Domain d) (r : ℝ), 0 < r →
      Metric.closedBall c r ⊆ (Ω : Set (Domain d)) →
      ∃ f : Domain d → 𝕜,
        u =ᵐ[volume.restrict (Metric.ball c r)] f ∧
        ∀ i : Fin d, ∀ᵐ y : Transverse i ∂volume,
          LocallyAbsolutelyContinuousOn (fun t => f (coordinateLine i y t))
            (fiber (⟨Metric.ball c r, Metric.isOpen_ball⟩ : Opens (Domain d)) i y) ∧
          ∀ᵐ t ∂volume.restrict
              (fiber (⟨Metric.ball c r, Metric.isOpen_ball⟩ : Opens (Domain d)) i y : Set ℝ),
            HasDerivAt (fun s => f (coordinateLine i y s)) (g i (coordinateLine i y t)) t) :
    ∃ f : Domain d → 𝕜,
      u =ᵐ[volume.restrict (Ω : Set (Domain d))] f ∧ HasACLDerivatives Ω f g := by
  classical
  by_cases hΩ : (Ω : Set (Domain d)).Nonempty
  · obtain ⟨c, r, hr, hcover, hclosed⟩ := exists_countable_box_cover Ω hΩ
    choose f hrep hacl using fun n => hlocal (c n) (r n) (hr n) (hclosed n).2.1
    let U : ℕ → Opens (Domain d) := fun n => ⟨Metric.ball (c n) (r n), Metric.isOpen_ball⟩
    exact exists_glued_acl_representative Ω U hcover u (fun i x => g i x) f hrep hacl
      (fun i => domainLp_zeroExtension_locallyIntegrable_on_lines (g i) i)
  · have he : (Ω : Set (Domain d)) = ∅ := Set.not_nonempty_iff_eq_empty.mp hΩ
    refine ⟨u, Filter.EventuallyEq.rfl, ?_⟩
    intro i
    apply ae_of_all
    intro y
    have hfiber : (fiber Ω i y : Set ℝ) = ∅ := by simp [fiber, he]
    constructor
    · intro a b hab
      have ha := hab left_mem_uIcc
      simpa only [hfiber, mem_empty_iff_false] using ha
    · simp only [hfiber, Measure.restrict_empty, ae_zero]
      exact Filter.eventually_bot


section CoordinatewiseRepresentatives
open ExpandedFA.Sobolev.OneDimensional

theorem exists_locallyAC_of_component_integral_deriv {𝕜 : Type} [RCLike 𝕜]
    {U : Set ℝ} (hU : IsOpen U) {u g : ℝ → 𝕜}
    (hu : LocallyIntegrable u volume) (hg : LocallyIntegrable g volume)
    (hw : ∀ C : Set ℝ, IsOpen C → OrdConnected C → C ⊆ U →
      ∀ ψ : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ C → (∫ t, ψ t • g t) = -(∫ t, deriv ψ t • u t)) :
    ∃ f : ℝ → 𝕜, u =ᵐ[volume.restrict U] f ∧
      LocallyAbsolutelyContinuousOn f U ∧
      ∀ᵐ t ∂volume.restrict U, HasDerivAt f (g t) t := by
  classical
  let P : ℝ → 𝕜 := fun t => ∫ s in (0 : ℝ)..t, g s
  have hgi (a b : ℝ) : IntervalIntegrable g volume a b :=
    (hg.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have hPc : Continuous P := intervalIntegral.continuous_primitive hgi 0
  have hPli : LocallyIntegrable P volume := hPc.locallyIntegrable
  have hzero : ∀ C : Set ℝ, IsOpen C → OrdConnected C → C ⊆ U →
      ∀ ψ : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ C → (∫ t, deriv ψ t • (u t - P t)) = 0 := by
    intro C hCo hCc hCU ψ hψ hcψ hsψ
    have he := neg_injective ((hw C hCo hCc hCU ψ hψ hcψ hsψ).symm.trans
      (primitive_real_test_identity hg ψ hψ hcψ))
    have hiu := hu.integrable_smul_left_of_hasCompactSupport
      (hψ.continuous_deriv (by simp)) hcψ.deriv
    have hip := hPli.integrable_smul_left_of_hasCompactSupport
      (hψ.continuous_deriv (by simp)) hcψ.deriv
    simp_rw [smul_sub]
    rw [integral_sub hiu hip, he, sub_self]
  let good : Set (Set ℝ) := {C | IsOpen C ∧ OrdConnected C ∧ C ⊆ U}
  have hc : ∀ C : good, ∃ c : 𝕜,
      (fun t => u t - P t) =ᵐ[volume.restrict (C : Set ℝ)] fun _ => c := by
    intro C
    apply ae_eq_const_of_integral_deriv_eq_zero C.property.1 C.property.2.1
      (hu.sub hPli)
    intro ψ hψ hcψ hsψ
    exact hzero C C.property.1 C.property.2.1 C.property.2.2 ψ hψ hcψ hsψ
  choose c hc using hc
  let c' (C : Set ℝ) : 𝕜 := if hC : C ∈ good then c ⟨C, hC⟩ else 0
  have hc' (C : Set ℝ) (hC : C ∈ good) :
      (fun t => u t - P t) =ᵐ[volume.restrict C] fun _ => c' C := by
    simpa only [c', dite_eq_left hC] using hc ⟨C, hC⟩
  have hcomp (x : ℝ) : connectedComponentIn U x ∈ good :=
    ⟨hU.connectedComponentIn, isPreconnected_connectedComponentIn.ordConnected,
      connectedComponentIn_subset U x⟩
  let f : ℝ → 𝕜 := fun t => P t + c' (connectedComponentIn U t)
  have hfeq (x t : ℝ) (ht : t ∈ connectedComponentIn U x) :
      f t = P t + c' (connectedComponentIn U x) := by
    dsimp [f]
    rw [← connectedComponentIn_eq ht]
  refine ⟨f, ?_, ?_, ?_⟩
  · obtain ⟨r, hrc, hrcover⟩ := (HereditarilyLindelofSpace.isLindelof U).elim_countable_subcover
      (connectedComponentIn U) (fun _ => hU.connectedComponentIn) (by
        intro t ht
        exact mem_iUnion.mpr ⟨t, mem_connectedComponentIn ht⟩)
    apply ae_restrict_of_ae_restrict_of_subset hrcover
    apply (ae_eq_restrict_biUnion_iff (connectedComponentIn U) hrc u f).mpr
    intro x _
    filter_upwards [hc' _ (hcomp x),
      ae_restrict_mem hU.connectedComponentIn.measurableSet] with t ht hti
    rw [hfeq x t hti]
    exact (sub_eq_iff_eq_add.mp ht).trans (add_comm _ _)
  · intro a b hab
    have hsub : uIcc a b ⊆ connectedComponentIn U a :=
      isPreconnected_uIcc.subset_connectedComponentIn left_mem_uIcc hab
    have hPa := integral_primitive_absolutelyContinuous hgi a b 0
    have hca : AbsolutelyContinuousOnInterval (fun _ : ℝ => c' (connectedComponentIn U a)) a b :=
      (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
    exact (hPa.add hca).congr (fun t ht => (hfeq a t (hsub ht)).symm)
  · filter_upwards [ae_restrict_of_ae (_root_.LocallyIntegrable.ae_hasDerivAt_integral hg),
      ae_restrict_mem hU.measurableSet] with t ht hti
    apply ((ht 0).add_const (c' (connectedComponentIn U t))).congr_of_eventuallyEq
    filter_upwards [hU.connectedComponentIn.mem_nhds (mem_connectedComponentIn hti)] with s hs
    exact hfeq t s hs




/-- A compact subset of an open interval is enclosed by a rational closed
interval which remains inside the open interval. -/
theorem rational_interval_enclosure {C K : Set ℝ} (hC : IsOpen C)
    (hCc : OrdConnected C) (hCn : C.Nonempty) (hK : IsCompact K) (hKC : K ⊆ C) :
    ∃ a b : ℚ, Icc (a : ℝ) (b : ℝ) ⊆ C ∧ K ⊆ Icc (a : ℝ) (b : ℝ) := by
  obtain ⟨x,hx,z,hz,hKxz⟩ := compact_interval_enclosure hC hCc hCn hK hKC
  obtain ⟨l,r,hxlr,hlrC⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hC.mem_nhds hx)
  obtain ⟨a,hla,hax⟩ := exists_rat_btwn hxlr.1
  obtain ⟨l',r',hzlr,hlrC'⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hC.mem_nhds hz)
  obtain ⟨b,hzb,hbr⟩ := exists_rat_btwn hzlr.2
  refine ⟨a,b,hCc.out (hlrC ⟨hla,hax.trans hxlr.2⟩)
    (hlrC' ⟨hzlr.1.trans hzb,hbr⟩), ?_⟩
  intro t ht
  exact ⟨(hax.trans (hKxz ht).1).le, ((hKxz ht).2.trans hzb).le⟩

/-- Rational compact-segment identities suffice on every open set of the line. -/
theorem exists_locallyAC_of_rational_line_identity {𝕜 : Type} [RCLike 𝕜]
    {U : Set ℝ} (hU : IsOpen U) {u g : ℝ → 𝕜}
    (hu : LocallyIntegrable u volume) (hg : LocallyIntegrable g volume)
    (hw : ∀ a b : ℚ, Icc (a : ℝ) (b : ℝ) ⊆ U →
      ∀ ψ : CompactLineTest 𝕜 (a : ℝ) (b : ℝ),
      (∫ t in Icc (a : ℝ) (b : ℝ), ψ.toTest t * g t + deriv ψ.toTest t * u t) = 0) :
    ∃ f : ℝ → 𝕜, u =ᵐ[volume.restrict U] f ∧
      LocallyAbsolutelyContinuousOn f U ∧
      ∀ᵐ t ∂volume.restrict U, HasDerivAt f (g t) t := by
  apply exists_locallyAC_of_component_integral_deriv hU hu hg
  intro C hC hCc hCU ψ hψ hcψ hsψ
  by_cases hCn : C.Nonempty
  · obtain ⟨a,b,habC,hψab⟩ := rational_interval_enclosure hC hCc hCn hcψ hsψ
    let ψk : ℝ → 𝕜 := fun t => (ψ t : 𝕜)
    have hk : ContDiff ℝ (↑(⊤ : ℕ∞)) ψk :=
      (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp hψ
    have hck : HasCompactSupport ψk := hcψ.comp_left (by simp)
    have hsk : tsupport ψk ⊆ Icc (a : ℝ) (b : ℝ) := by
      have he : Function.support ψk = Function.support ψ := by
        ext t
        simp [ψk, Function.mem_support]
      simpa only [tsupport, he] using hψab
    let φ : CompactLineTest 𝕜 (a : ℝ) (b : ℝ) :=
      ⟨⟨ψk, hk, hck, subset_univ _⟩,hsk⟩
    have hd (t : ℝ) : deriv ψk t = ((deriv ψ t : ℝ) : 𝕜) := by
      exact ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).hasFDerivAt.comp_hasDerivAt t
        (hψ.differentiable (by simp) t).hasDerivAt).deriv
    have he := hw a b (habC.trans hCU) φ
    change (∫ t in Icc (a : ℝ) (b : ℝ), (ψ t : 𝕜) * g t + deriv ψk t * u t) = 0 at he
    simp_rw [hd] at he
    have he' : (∫ t in Icc (a : ℝ) (b : ℝ), ψ t • g t + deriv ψ t • u t) = 0 := by
      simpa only [RCLike.real_smul_eq_coe_mul] using he
    have hig := hg.integrable_smul_left_of_hasCompactSupport hψ.continuous hcψ
    have hiu := hu.integrable_smul_left_of_hasCompactSupport
      (hψ.continuous_deriv (by simp)) hcψ.deriv
    rw [integral_add hig.integrableOn hiu.integrableOn] at he'
    have he₁ : (∫ t in Icc (a : ℝ) (b : ℝ), ψ t • g t) = ∫ t, ψ t • g t :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => by
        simp [image_eq_zero_of_notMem_tsupport (fun h => ht (hψab h))]
    have he₂ : (∫ t in Icc (a : ℝ) (b : ℝ), deriv ψ t • u t) = ∫ t, deriv ψ t • u t :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => by
        simp [deriv_of_notMem_tsupport (fun h => ht (hψab h))]
    rw [he₁,he₂] at he'
    exact eq_neg_iff_add_eq_zero.mpr he'
  · have hψzero : ψ = 0 := by
      funext t
      exact image_eq_zero_of_notMem_tsupport (fun h => hCn ⟨t,hsψ h⟩)
    simp only [hψzero, Pi.zero_apply, deriv_zero, zero_smul, integral_zero, neg_zero]

/-- Almost every coordinate fiber has a locally AC representative with the
specified actual weak derivative, on every component of the open fiber. -/
theorem ae_coordinate_line_representative {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : DomainLp 𝕜 Ω p) (g : Fin d → DomainLp 𝕜 Ω p)
    (hweak : HasWeakCoordinateDerivatives u g) (i : Fin d) :
    ∀ᵐ y : Transverse i ∂volume, ∃ f : ℝ → 𝕜,
      (fun t => u (coordinateLine i y t)) =ᵐ[volume.restrict (fiber Ω i y : Set ℝ)] f ∧
      LocallyAbsolutelyContinuousOn f (fiber Ω i y) ∧
      ∀ᵐ t ∂volume.restrict (fiber Ω i y : Set ℝ),
        HasDerivAt f (g i (coordinateLine i y t)) t := by
  filter_upwards [domainLp_zeroExtension_locallyIntegrable_on_lines u i,
    domainLp_zeroExtension_locallyIntegrable_on_lines (g i) i,
    ae_all_rational_line_identity u g hweak i] with y huy hgy hwy
  let u' : ℝ → 𝕜 := fun t => (Ω : Set (Domain d)).indicator u (coordinateLine i y t)
  let g' : ℝ → 𝕜 := fun t => (Ω : Set (Domain d)).indicator (g i) (coordinateLine i y t)
  have hw : ∀ a b : ℚ, Icc (a : ℝ) (b : ℝ) ⊆ (fiber Ω i y : Set ℝ) →
      ∀ ψ : CompactLineTest 𝕜 (a : ℝ) (b : ℝ),
      (∫ t in Icc (a : ℝ) (b : ℝ), ψ.toTest t * g' t + deriv ψ.toTest t * u' t) = 0 := by
    intro a b hab ψ
    have hyab : y ∈ lineTube Ω i (a : ℝ) (b : ℝ) := hab
    have he := hwy a b hyab ψ
    convert he using 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hΩ : coordinateLine i y t ∈ (Ω : Set (Domain d)) := hab ht
    simp only [u',g',indicator_of_mem hΩ]
  obtain ⟨f,hrep,hAC,hd⟩ := exists_locallyAC_of_rational_line_identity
    (fiber Ω i y).isOpen huy hgy hw
  refine ⟨f, ?_, hAC, ?_⟩
  · filter_upwards [hrep,ae_restrict_mem (fiber Ω i y).isOpen.measurableSet] with t ht hti
    have hΩ : coordinateLine i y t ∈ (Ω : Set (Domain d)) := hti
    simpa only [u',indicator_of_mem hΩ] using ht
  · filter_upwards [hd,ae_restrict_mem (fiber Ω i y).isOpen.measurableSet] with t ht hti
    have hΩ : coordinateLine i y t ∈ (Ω : Set (Domain d)) := hti
    simpa only [g',indicator_of_mem hΩ] using ht

end CoordinatewiseRepresentatives

section AverageConvergence
open Filter Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem norm_setAverage_le_of_norm_le_const {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {s : Set A} {f : A → E} {C : ℝ}
    (h0 : μ s ≠ 0) (hfin : μ s ≠ ∞) (hf : ∀ x ∈ s, ‖f x‖ ≤ C) :
    ‖⨍ x in s, f x ∂μ‖ ≤ C := by
  rw [setAverage_eq, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (measureReal_nonneg)]
  have hm : μ.real s ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨h0, hfin⟩
  calc
    (μ.real s)⁻¹ * ‖∫ x in s, f x ∂μ‖ ≤ (μ.real s)⁻¹ * (C * μ.real s) :=
      mul_le_mul_of_nonneg_left (norm_setIntegral_le_of_norm_le_const hfin.lt_top hf) (by positivity)
    _ = C := by field_simp

/-- Averages of a jointly convergent family over shrinking intervals converge.
The functions may vary along the same filter as the radius. -/
theorem tendsto_average_closedBall_of_tendsto {ι : Type*} {l : Filter ι}
    (v : ι → ℝ → E) (hvcont : ∀ n, Continuous (v n)) (t : ℝ) (z : E)
    (hv : Tendsto (Function.uncurry v) (l ×ˢ 𝓝 t) (𝓝 z))
    (r : ι → ℝ) (hr : Tendsto r l (𝓝 0)) (hrpos : ∀ᶠ n in l, 0 < r n) :
    Tendsto (fun n => ⨍ s in closedBall t (r n), v n s) l (𝓝 z) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := (Metric.tendsto_nhds.mp hv) (ε / 2) (half_pos hε)
  obtain ⟨P, hP, Q, hQ, hPQ⟩ := eventually_prod_iff.mp he
  have hball : ∀ᶠ n in l, closedBall t (r n) ⊆ {s | Q s} :=
    hr.eventually (eventually_closedBall_subset hQ)
  filter_upwards [hP, hball, hrpos] with n hn hnball hnpos
  have h0 : volume (closedBall t (r n)) ≠ 0 := (measure_closedBall_pos volume t hnpos).ne'
  have hfin : volume (closedBall t (r n)) ≠ ∞ := isCompact_closedBall t (r n) |>.measure_ne_top
  have hint : IntegrableOn (v n) (closedBall t (r n)) volume :=
    (hvcont n).continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  rw [dist_eq_norm, ← setAverage_const h0 hfin z, ← setAverage_sub hint (integrableOn_const hfin)]
  exact (norm_setAverage_le_of_norm_le_const h0 hfin (fun s hs =>
    by simpa [dist_eq_norm] using (hPQ hn (hnball hs)).le)).trans_lt (half_lt_self hε)

/-- If continuous maps converge uniformly, their clamped interval averages
converge at every point as the averaging radius shrinks. -/
theorem tendsto_average_compactInterval_of_tendsto {ι : Type*} {l : Filter ι}
    {a b : ℝ} (hab : a ≤ b) {F : ι → C(Icc a b, E)} {f : C(Icc a b, E)}
    (hF : Tendsto F l (𝓝 f)) (t : ℝ)
    (r : ι → ℝ) (hr : Tendsto r l (𝓝 0)) (hrpos : ∀ᶠ n in l, 0 < r n) :
    Tendsto (fun n => ⨍ s in closedBall t (r n), F n (projIcc a b hab s)) l
      (𝓝 (f (projIcc a b hab t))) := by
  apply tendsto_average_closedBall_of_tendsto _ (fun n => (F n).continuous.comp continuous_projIcc)
    t _ ?_ r hr hrpos
  exact (continuous_eval.tendsto (f, projIcc a b hab t)).comp
    ((hF.comp tendsto_fst).prodMk_nhds ((continuous_projIcc.tendsto t).comp tendsto_snd))

/-- The transverse Banach averages converge uniformly on the compact interval
at almost every transverse point. -/
theorem ae_tendsto_continuousSlice_averages {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [MeasureSpace Y] [BorelSpace Y]
    [Measure.IsAddHaarMeasure (volume : Measure Y)]
    {a b : ℝ} (F : Y → C(Icc a b, E)) (hF : LocallyIntegrable F volume)
    {ι : Type*} {l : Filter ι} (r : ι → ℝ)
    (hr : Tendsto r l (𝓝 0)) (hrpos : ∀ᶠ n in l, 0 < r n) :
    ∀ᵐ y ∂volume,
      Tendsto (fun n => ⨍ z in closedBall y (r n), F z) l (𝓝 (F y)) := by
  filter_upwards [(Besicovitch.vitaliFamily volume).ae_tendsto_average hF] with y hy
  exact (hy.comp (Besicovitch.tendsto_filterAt volume y)).comp
    (tendsto_nhdsWithin_iff.mpr ⟨hr, hrpos⟩)

/-- A.e. transverse line, followed by time averaging, recovers every value of
its continuous representative, through one and the same radius sequence. -/
theorem ae_tendsto_iterated_continuousSlice_averages {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [MeasureSpace Y] [BorelSpace Y]
    [Measure.IsAddHaarMeasure (volume : Measure Y)]
    {a b : ℝ} (hab : a ≤ b) (F : Y → C(Icc a b, E)) (hF : LocallyIntegrable F volume)
    {ι : Type*} {l : Filter ι} (r : ι → ℝ)
    (hr : Tendsto r l (𝓝 0)) (hrpos : ∀ᶠ n in l, 0 < r n) :
    ∀ᵐ y ∂volume, ∀ t : ℝ,
      Tendsto (fun n => ⨍ s in closedBall t (r n),
        (⨍ z in closedBall y (r n), F z) (projIcc a b hab s)) l
        (𝓝 (F y (projIcc a b hab t))) := by
  filter_upwards [ae_tendsto_continuousSlice_averages F hF r hr hrpos] with y hy
  intro t
  exact tendsto_average_compactInterval_of_tendsto hab hy t r hr hrpos


end AverageConvergence

section CoordinateBallAverages

/-- Coordinate splitting is an isometry for the Euclidean domain's sup norm. -/
def coordinateIsometryEquiv {d : ℕ} (i : Fin d) : Domain d ≃ᵢ ℝ × Transverse i where
  toEquiv := (coordinateEquiv i).toEquiv
  isometry_toFun := Isometry.of_dist_eq fun x z => by
    apply le_antisymm
    · change dist (x i, fun j : {j : Fin d // j ≠ i} => x j)
        (z i, fun j : {j : Fin d // j ≠ i} => z j) ≤ dist x z
      rw [Prod.dist_eq]
      exact max_le (dist_le_pi_dist _ _ i)
        ((dist_pi_le_iff dist_nonneg).mpr fun j => dist_le_pi_dist x z j.val)
    · apply (dist_pi_le_iff dist_nonneg).mpr
      intro j
      by_cases hj : j = i
      · subst j
        exact le_max_left _ _
      · exact (dist_le_pi_dist
          (fun k : {j : Fin d // j ≠ i} => x k)
          (fun k : {j : Fin d // j ≠ i} => z k) ⟨j,hj⟩).trans (le_max_right _ _)

/-- Measure-preserving measurable equivalences preserve the normalized integral. -/
theorem average_comp_of_measurePreserving {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] {μ : Measure A} {ν : Measure B} (e : A ≃ᵐ B)
    (he : MeasurePreserving e μ ν) {𝕜 : Type*} [RCLike 𝕜] (h : B → 𝕜) :
    (⨍ x, h (e x) ∂μ) = ⨍ y, h y ∂ν := by
  have hm : μ.real univ = ν.real univ := by
    exact he.measureReal_preimage (s := Set.univ) MeasurableSet.univ
  rw [average_eq, average_eq, he.integral_comp', hm]

/-- Product normalized integrals are iterated normalized integrals, with the
transverse factor first. Zero-measure factors are included. -/
theorem average_prod_symm {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {𝕜 : Type*} [RCLike 𝕜] (h : A × B → 𝕜) (hh : Integrable h (μ.prod ν)) :
    (⨍ z, h z ∂μ.prod ν) = ⨍ y, ⨍ t, h (t,y) ∂μ ∂ν := by
  have hm : (μ.prod ν).real univ = μ.real univ * ν.real univ := by
    rw [← univ_prod_univ, measureReal_prod_prod]
  simp_rw [average_eq]
  rw [hm, integral_prod_symm _ hh, integral_smul, smul_smul, mul_inv_rev, mul_comm]

/-- A sup-norm product ball average factors into the two coordinate averages. -/
theorem average_closedBall_prod {E : Type*} [NormedAddCommGroup E]
    [MeasureSpace E] [BorelSpace E] [IsLocallyFiniteMeasure (volume : Measure E)]
    [ProperSpace E] {𝕜 : Type*} [RCLike 𝕜] {h : ℝ × E → 𝕜}
    (hh : Integrable h volume) (t : ℝ) (y : E) (r : ℝ) :
    (⨍ z in Metric.closedBall (t,y) r, h z) =
      ⨍ y' in Metric.closedBall y r, ⨍ t' in Metric.closedBall t r, h (t',y') := by
  let : IsFiniteMeasure (volume.restrict (Metric.closedBall t r)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall t r).measure_ne_top
  let : IsFiniteMeasure (volume.restrict (Metric.closedBall y r)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall y r).measure_ne_top
  rw [← closedBall_prod_same, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hi : IntegrableOn h (Metric.closedBall (t,y) r) volume := hh.restrict
  exact average_prod_symm h (by simpa only [IntegrableOn, Measure.volume_eq_prod,
    Measure.prod_restrict, closedBall_prod_same] using hi)

/-- The same ambient ball average can be expressed in every coordinate split. -/
theorem average_coordinate_closedBall {𝕜 : Type*} [RCLike 𝕜] {d : ℕ}
    (i : Fin d) (h : Domain d → 𝕜) (x : Domain d) (r : ℝ) :
    (⨍ z in Metric.closedBall x r, h z) =
      ⨍ z in Metric.closedBall (coordinateEquiv i x) r,
        h (coordinateLine i z.2 z.1) := by
  have hp := (coordinateEquiv_measurePreserving i).restrict_image_emb
    (coordinateEquiv i).measurableEmbedding (Metric.closedBall x r)
  have hs : (coordinateEquiv i) '' Metric.closedBall x r =
      Metric.closedBall (coordinateEquiv i x) r :=
    (coordinateIsometryEquiv i).image_closedBall x r
  rw [hs] at hp
  have ha := average_comp_of_measurePreserving (coordinateEquiv i) hp
    (fun z => h ((coordinateEquiv i).symm z))
  have heq : (fun z : ℝ × Transverse i => h ((coordinateEquiv i).symm z)) =
      (fun z => h (coordinateLine i z.2 z.1)) := by
    funext z
    rw [← coordinateEquiv_symm_apply]
  rw [heq] at ha
  simpa only [MeasurableEquiv.symm_apply_apply] using ha


end CoordinateBallAverages

section CommonLimitAssembly
open Filter

/-- A single ambient approximation family with pointwise limits on every point
of almost every good line produces one common ACL representative. -/
theorem exists_common_acl_representative_of_limits_raw {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)}
    (u : Domain d → 𝕜) (g : Fin d → Domain d → 𝕜)
    {A : Type*} (l : Filter A) [NeBot l] (h : A → Domain d → 𝕜)
    (hambient : ∀ᵐ x ∂volume.restrict (Ω : Set (Domain d)),
      Tendsto (fun r => h r x) l (𝓝 (u x)))
    (hlines : ∀ i : Fin d, ∀ᵐ y : Transverse i ∂volume,
      ∃ F : ℝ → 𝕜,
        LocallyAbsolutelyContinuousOn F (fiber Ω i y) ∧
        (∀ᵐ t ∂volume.restrict (fiber Ω i y : Set ℝ),
          HasDerivAt F (g i (coordinateLine i y t)) t) ∧
        ∀ t ∈ (fiber Ω i y : Set ℝ),
          Tendsto (fun r => h r (coordinateLine i y t)) l (𝓝 (F t))) :
    ∃ f : Domain d → 𝕜,
      u =ᵐ[volume.restrict (Ω : Set (Domain d))] f ∧
        ∀ i : Fin d, ∀ᵐ y : Transverse i ∂volume,
          LocallyAbsolutelyContinuousOn (fun t => f (coordinateLine i y t)) (fiber Ω i y) ∧
          ∀ᵐ t ∂volume.restrict (fiber Ω i y : Set ℝ),
            HasDerivAt (fun s => f (coordinateLine i y s)) (g i (coordinateLine i y t)) t := by
  let f : Domain d → 𝕜 := fun x => limUnder l (fun r => h r x)
  refine ⟨f, ?_, ?_⟩
  · filter_upwards [hambient] with x hx
    exact hx.limUnder_eq.symm
  · intro i
    filter_upwards [hlines i] with y hy
    obtain ⟨F, hAC, hder, hlim⟩ := hy
    have heq : ∀ t ∈ (fiber Ω i y : Set ℝ),
        f (coordinateLine i y t) = F t := by
      intro t ht
      exact (hlim t ht).limUnder_eq
    refine ⟨?_, ?_⟩
    · intro a b hab
      exact (hAC a b hab).congr (fun t ht => (heq t (hab ht)).symm)
    · filter_upwards [hder, ae_restrict_mem (fiber Ω i y).isOpen.measurableSet] with t ht htm
      apply ht.congr_of_eventuallyEq
      filter_upwards [(fiber Ω i y).isOpen.mem_nhds htm] with s hs
      exact heq s hs


end CommonLimitAssembly

@[simp] theorem coordinateEquiv_coordinateLine {d : ℕ} (i : Fin d)
    (y : Transverse i) (t : ℝ) : coordinateEquiv i (coordinateLine i y t) = (t,y) := by
  simp only [coordinateEquiv_apply, coordinateLine_self]
  congr 1
  exact transverseProjection_coordinateLine i y t

theorem coordinateLine_mem_ball_iff {d : ℕ} (i : Fin d) (y : Transverse i)
    (t : ℝ) (c : Domain d) (r : ℝ) :
    coordinateLine i y t ∈ Metric.ball c r ↔
      t ∈ Metric.ball (c i) r ∧ y ∈ Metric.ball (transverseProjection i c) r := by
  simp only [Metric.mem_ball]
  rw [← (coordinateIsometryEquiv i).dist_eq]
  change dist (coordinateEquiv i (coordinateLine i y t)) (coordinateEquiv i c) < r ↔ _
  rw [coordinateEquiv_coordinateLine, coordinateEquiv_apply, Prod.dist_eq, max_lt_iff]
  rfl

theorem coordinateLine_mem_closedBall_iff {d : ℕ} (i : Fin d) (y : Transverse i)
    (t : ℝ) (c : Domain d) (r : ℝ) :
    coordinateLine i y t ∈ Metric.closedBall c r ↔
      t ∈ Metric.closedBall (c i) r ∧ y ∈ Metric.closedBall (transverseProjection i c) r := by
  simp only [Metric.mem_closedBall]
  rw [← (coordinateIsometryEquiv i).dist_eq]
  change dist (coordinateEquiv i (coordinateLine i y t)) (coordinateEquiv i c) ≤ r ↔ _
  rw [coordinateEquiv_coordinateLine, coordinateEquiv_apply, Prod.dist_eq, max_le_iff]
  rfl

/-- Restricting an Lp class to a compact interior box produces an ambient L1
function, even when the original domain is unbounded or p is infinity. -/
theorem integrable_lp_compact_indicator {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : DomainLp 𝕜 Ω p) {K : Set (Domain d)} (hK : IsCompact K) (hs : K ⊆ Ω) :
    Integrable (K.indicator u) volume := by
  have hi := (domainLp_locallyIntegrable u).integrableOn_compact_subset hs hK
  have hi' : IntegrableOn u K volume := by
    simpa only [IntegrableOn, Measure.restrict_restrict_of_subset hs] using hi
  exact (integrable_indicator_iff hK.measurableSet).mpr hi'


section LocalAverageAssembly
open Filter

/-- Local common-representative assembly from the scalar ball-average
identities and the integrable Banach spaces of continuous slices. -/
theorem exists_common_acl_of_slice_average_identities {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} (u : Domain d → 𝕜) (g : Fin d → Domain d → 𝕜)
    (φ : Domain d → 𝕜) (hφ : Integrable φ volume)
    (hφu : φ =ᵐ[volume.restrict (Ω : Set (Domain d))] u)
    (a b : Fin d → ℝ) (hab : ∀ i, a i ≤ b i)
    (F : ∀ i : Fin d, Transverse i → C(Icc (a i) (b i), 𝕜))
    (hF : ∀ i, Integrable (F i) volume)
    (hidentity : ∀ i : Fin d, ∀ᵐ y : Transverse i ∂volume,
      ∀ t ∈ (fiber Ω i y : Set ℝ),
        ∀ᶠ r in 𝓝[>] (0 : ℝ),
          (⨍ x in Metric.closedBall (coordinateLine i y t) r, φ x) =
          (⨍ s in Metric.closedBall t r,
            (⨍ z in Metric.closedBall y r, F i z) (projIcc (a i) (b i) (hab i) s)))
    (hlines : ∀ i : Fin d, ∀ᵐ y : Transverse i ∂volume,
      ∃ f : ℝ → 𝕜,
        LocallyAbsolutelyContinuousOn f (fiber Ω i y) ∧
        (∀ᵐ t ∂volume.restrict (fiber Ω i y : Set ℝ),
          HasDerivAt f (g i (coordinateLine i y t)) t) ∧
        ∀ t ∈ (fiber Ω i y : Set ℝ),
          F i y (projIcc (a i) (b i) (hab i) t) = f t) :
    ∃ f : Domain d → 𝕜,
      u =ᵐ[volume.restrict (Ω : Set (Domain d))] f ∧
        ∀ i : Fin d, ∀ᵐ y : Transverse i ∂volume,
          LocallyAbsolutelyContinuousOn (fun t => f (coordinateLine i y t)) (fiber Ω i y) ∧
          ∀ᵐ t ∂volume.restrict (fiber Ω i y : Set ℝ),
            HasDerivAt (fun s => f (coordinateLine i y s)) (g i (coordinateLine i y t)) t := by
  let l : Filter ℝ := 𝓝[>] (0 : ℝ)
  have hr : Tendsto (fun r : ℝ => r) l (𝓝 0) := tendsto_id.mono_right nhdsWithin_le_nhds
  have hrpos : ∀ᶠ r in l, 0 < r := self_mem_nhdsWithin
  have hambient : ∀ᵐ x ∂volume,
      Tendsto (fun r => ⨍ z in Metric.closedBall x r, φ z) l (𝓝 (φ x)) := by
    filter_upwards [(Besicovitch.vitaliFamily volume).ae_tendsto_average hφ.locallyIntegrable]
      with x hx
    exact hx.comp (Besicovitch.tendsto_filterAt volume x)
  apply exists_common_acl_representative_of_limits_raw u g l
    (fun r x => ⨍ z in Metric.closedBall x r, φ z)
  · filter_upwards [ae_restrict_of_ae hambient, hφu] with x hx hxφ
    simpa only [hxφ] using hx
  · intro i
    filter_upwards [ae_tendsto_iterated_continuousSlice_averages (hab i) (F i)
      (hF i).locallyIntegrable (fun r : ℝ => r) hr hrpos,
      hidentity i, hlines i] with y hyconv hyid hyline
    obtain ⟨f, hfAC, hfder, hfval⟩ := hyline
    refine ⟨f, hfAC, hfder, ?_⟩
    intro t ht
    have hid : (fun r => ⨍ x in Metric.closedBall (coordinateLine i y t) r, φ x) =ᶠ[l]
        (fun r => ⨍ s in Metric.closedBall t r,
          (⨍ z in Metric.closedBall y r, F i z) (projIcc (a i) (b i) (hab i) s)) := hyid t ht
    simpa only [hfval t ht] using (hyconv t).congr' hid.symm


end LocalAverageAssembly

section SliceAverageIdentification
open Metric

/-- The clamped compact-interval integral is a continuous real-linear functional. -/
def compactIntervalIntegralCLM {𝕜 : Type*} [RCLike 𝕜] {a b : ℝ} (hab : a ≤ b)
    (t r : ℝ) : C(Icc a b, 𝕜) →L[ℝ] 𝕜 := by
  have hi (φ : C(Icc a b, 𝕜)) : IntegrableOn
      (fun s => φ (projIcc a b hab s)) (closedBall t r) volume :=
    (φ.continuous.comp continuous_projIcc).continuousOn.integrableOn_compact
      (isCompact_closedBall t r)
  let L : C(Icc a b, 𝕜) →ₗ[ℝ] 𝕜 :=
    { toFun := fun φ => ∫ s in closedBall t r, φ (projIcc a b hab s)
      map_add' := fun φ ψ => by
        simp only [ContinuousMap.add_apply]
        exact integral_add (hi φ) (hi ψ)
      map_smul' := fun c φ => by
        simp only [ContinuousMap.smul_apply, RingHom.id_apply]
        exact integral_smul c _ }
  apply L.mkContinuous (volume.real (closedBall t r))
  intro φ
  change ‖∫ s in closedBall t r, φ (projIcc a b hab s)‖ ≤ _
  rw [mul_comm]
  exact norm_setIntegral_le_of_norm_le_const
    (isCompact_closedBall t r).measure_ne_top.lt_top
    (fun s _ => φ.norm_coe_le_norm _)

@[simp] theorem compactIntervalIntegralCLM_apply {𝕜 : Type*} [RCLike 𝕜]
    {a b : ℝ} (hab : a ≤ b) (t r : ℝ) (φ : C(Icc a b, 𝕜)) :
    compactIntervalIntegralCLM hab t r φ = ∫ s in closedBall t r, φ (projIcc a b hab s) := rfl

/-- Continuous real-linear maps commute with normalized integrals. -/
theorem average_comp_continuousLinearMap {A E G : Type*} [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] {μ : Measure A}
    (L : E →L[ℝ] G) {f : A → E} (hf : Integrable f μ) :
    (⨍ x, L (f x) ∂μ) = L (⨍ x, f x ∂μ) := by
  simp only [average_eq, L.map_smul]
  congr 1
  exact L.integral_comp_comm hf

/-- Time averaging commutes with a Banach-valued transverse average. -/
theorem continuousSlice_average_comm {𝕜 : Type*} [RCLike 𝕜]
    {Y : Type*} [MeasurableSpace Y] {μ : Measure Y}
    {a b : ℝ} (hab : a ≤ b) (F : Y → C(Icc a b, 𝕜)) (hF : Integrable F μ)
    (t r : ℝ) :
    (⨍ y, (⨍ s in closedBall t r, F y (projIcc a b hab s)) ∂μ) =
      ⨍ s in closedBall t r, (⨍ y, F y ∂μ) (projIcc a b hab s) := by
  let L : C(Icc a b, 𝕜) →L[ℝ] 𝕜 :=
    (volume.real (closedBall t r))⁻¹ • compactIntervalIntegralCLM hab t r
  have he (φ : C(Icc a b, 𝕜)) : L φ = ⨍ s in closedBall t r, φ (projIcc a b hab s) := by
    simp only [L, smul_apply, compactIntervalIntegralCLM_apply,
      setAverage_eq]
  simp_rw [← he]
  exact average_comp_continuousLinearMap L hF

/-- Scalar ambient averages are the same averages used by continuous-slice
Lebesgue differentiation, on every ball whose time factor lies in the interval. -/
theorem average_closedBall_eq_continuousSlice_average {𝕜 : Type*} [RCLike 𝕜]
    {Y : Type*} [NormedAddCommGroup Y] [MeasureSpace Y] [BorelSpace Y]
    [IsLocallyFiniteMeasure (volume : Measure Y)] [ProperSpace Y]
    {a b : ℝ} (hab : a ≤ b) (u : ℝ × Y → 𝕜) (F : Y → C(Icc a b, 𝕜))
    (hu : Integrable u volume) (hF : Integrable F volume)
    (hrep : ∀ᵐ y ∂volume, (fun s => u (s,y)) =ᵐ[volume.restrict (Icc a b)]
      (fun s => F y (projIcc a b hab s)))
    (t : ℝ) (y : Y) (r : ℝ) (hs : closedBall t r ⊆ Icc a b) :
    (⨍ z in closedBall (t,y) r, u z) =
      ⨍ s in closedBall t r, (⨍ z in closedBall y r, F z) (projIcc a b hab s) := by
  rw [average_closedBall_prod hu]
  calc
    _ = ⨍ z in closedBall y r, ⨍ s in closedBall t r,
        F z (projIcc a b hab s) := by
      apply average_congr
      filter_upwards [ae_restrict_of_ae hrep] with z hz
      apply average_congr
      exact ae_restrict_of_ae_restrict_of_subset hs hz
    _ = _ := continuousSlice_average_comm hab F hF.restrict t r


end SliceAverageIdentification

section SliceAverageGeometry
open Filter Metric

theorem eventually_closedBall_subset_Icc_of_mem_Ioo {ι : Type*} {l : Filter ι}
    {a b t : ℝ} (ht : t ∈ Ioo a b) (r : ι → ℝ) (hr : Tendsto r l (𝓝 0)) :
    ∀ᶠ n in l, closedBall t (r n) ⊆ Icc a b :=
  hr.eventually (eventually_closedBall_subset (Icc_mem_nhds ht.1 ht.2))

/-- On every interior point, shrinking ambient ball averages eventually equal
the clamped continuous-slice averages used in uniform line differentiation. -/
theorem eventually_average_closedBall_eq_continuousSlice_average
    {𝕜 : Type*} [RCLike 𝕜] {Y : Type*} [NormedAddCommGroup Y]
    [MeasureSpace Y] [BorelSpace Y] [IsLocallyFiniteMeasure (volume : Measure Y)] [ProperSpace Y]
    {a b : ℝ} (hab : a ≤ b) (u : ℝ × Y → 𝕜) (F : Y → C(Icc a b, 𝕜))
    (hu : Integrable u volume) (hF : Integrable F volume)
    (hrep : ∀ᵐ y ∂volume, (fun s => u (s,y)) =ᵐ[volume.restrict (Icc a b)]
      (fun s => F y (projIcc a b hab s)))
    {ι : Type*} {l : Filter ι} (r : ι → ℝ) (hr : Tendsto r l (𝓝 0))
    (t : ℝ) (ht : t ∈ Ioo a b) (y : Y) :
    ∀ᶠ n in l, (⨍ z in closedBall (t,y) (r n), u z) =
      ⨍ s in closedBall t (r n), (⨍ z in closedBall y (r n), F z) (projIcc a b hab s) := by
  filter_upwards [eventually_closedBall_subset_Icc_of_mem_Ioo ht r hr] with n hn
  exact average_closedBall_eq_continuousSlice_average hab u F hu hF hrep t y (r n) hn


end SliceAverageGeometry

/-- Compact box localization turns the coordinatewise AC representatives into
a globally integrable continuous-map-valued transverse function. -/
theorem exists_integrable_coordinate_AC_slices {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : DomainLp 𝕜 Ω p) (g : Fin d → DomainLp 𝕜 Ω p)
    (hweak : HasWeakCoordinateDerivatives u g) (c : Domain d) (r : ℝ) (hr : 0 < r)
    (hs : Metric.closedBall c r ⊆ (Ω : Set (Domain d))) (i : Fin d) :
    let a := c i - r
    let b := c i + r
    let φ := (Metric.closedBall c r).indicator u
    ∃ F : Transverse i → C(Icc a b, 𝕜),
      Integrable F volume ∧
      (∀ᵐ y : Transverse i ∂volume,
        (fun t => φ (coordinateLine i y t)) =ᵐ[volume.restrict (Icc a b)]
          (fun t => F y (projIcc a b (by dsimp [a,b]; linarith) t))) ∧
      ∀ᵐ y : Transverse i ∂volume,
        y ∈ Metric.closedBall (transverseProjection i c) r →
        ∃ f : ℝ → 𝕜, AbsolutelyContinuousOnInterval f a b ∧
          (∀ᵐ t ∂volume, t ∈ Icc a b → HasDerivAt f (g i (coordinateLine i y t)) t) ∧
          ∀ t : Icc a b, F y t = f t := by
  classical
  dsimp only
  let a := c i - r
  let b := c i + r
  have hab : a < b := by dsimp [a,b]; linarith
  let φ : Domain d → 𝕜 := (Metric.closedBall c r).indicator u
  let γ : Domain d → 𝕜 := (Metric.closedBall c r).indicator (g i)
  let U : Transverse i × ℝ → 𝕜 := fun z => φ (coordinateLine i z.1 z.2)
  let G : Transverse i × ℝ → 𝕜 := fun z => γ (coordinateLine i z.1 z.2)
  have hφ : Integrable φ volume := integrable_lp_compact_indicator u (isCompact_closedBall c r) hs
  have hγ : Integrable γ volume := integrable_lp_compact_indicator (g i) (isCompact_closedBall c r) hs
  let e : Transverse i × ℝ ≃ᵐ Domain d :=
    (MeasurableEquiv.prodComm).trans (coordinateEquiv i).symm
  have he : MeasurePreserving e volume volume :=
    ((coordinateEquiv_measurePreserving i).symm (coordinateEquiv i)).comp
      Measure.measurePreserving_swap
  have hU : Integrable U (volume.prod volume) := by
    have hi := he.integrable_comp_of_integrable hφ
    change Integrable (fun z : Transverse i × ℝ => φ ((coordinateEquiv i).symm (z.2,z.1))) volume at hi
    change Integrable (fun z : Transverse i × ℝ => φ (coordinateLine i z.1 z.2)) volume
    simpa only [coordinateEquiv_symm_apply] using hi
  have hG : Integrable G (volume.prod volume) := by
    have hi := he.integrable_comp_of_integrable hγ
    change Integrable (fun z : Transverse i × ℝ => γ ((coordinateEquiv i).symm (z.2,z.1))) volume at hi
    change Integrable (fun z : Transverse i × ℝ => γ (coordinateLine i z.1 z.2)) volume
    simpa only [coordinateEquiv_symm_apply] using hi
  have hUj : Integrable U (volume.prod (volume.restrict (Icc a b))) :=
    hU.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  have hGj : Integrable G (volume.prod (volume.restrict (Icc a b))) :=
    hG.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  have hmem (y : Transverse i) (hy : y ∈ Metric.closedBall (transverseProjection i c) r)
      {t : ℝ} (ht : t ∈ Icc a b) : coordinateLine i y t ∈ Metric.closedBall c r := by
    apply (coordinateLine_mem_closedBall_iff i y t c r).mpr
    exact ⟨by simpa only [Real.closedBall_eq_Icc] using ht, hy⟩
  have hlocal : ∀ᵐ y : Transverse i ∂volume, ∃ f : ℝ → 𝕜,
      AbsolutelyContinuousOnInterval f a b ∧
      (fun t => U (y,t)) =ᵐ[volume.restrict (Icc a b)] f ∧
      LocallyIntegrable (fun t => G (y,t)) volume ∧
      ∀ᵐ t ∂volume, t ∈ Icc a b → HasDerivAt f (G (y,t)) t := by
    filter_upwards [ae_coordinate_line_representative u g hweak i, hG.prod_right_ae] with y hy hGy
    by_cases hyV : y ∈ Metric.closedBall (transverseProjection i c) r
    · obtain ⟨f, hrep, hac, hd⟩ := hy
      have hjΩ : Icc a b ⊆ (fiber Ω i y : Set ℝ) := fun t ht => hs (hmem y hyV ht)
      have hfac : AbsolutelyContinuousOnInterval f a b :=
        hac a b (by simpa only [uIcc_of_le hab.le] using hjΩ)
      have hrepj : (fun t => U (y,t)) =ᵐ[volume.restrict (Icc a b)] f := by
        filter_upwards [ae_restrict_of_ae_restrict_of_subset hjΩ hrep,
          ae_restrict_mem measurableSet_Icc] with t ht hti
        simpa only [U, φ, indicator_of_mem (hmem y hyV hti)] using ht
      refine ⟨f, hfac, hrepj, hGy.locallyIntegrable, ?_⟩
      filter_upwards [(ae_restrict_iff' (fiber Ω i y).isOpen.measurableSet).mp hd] with t ht hti
      simpa only [G, γ, indicator_of_mem (hmem y hyV hti)] using ht (hjΩ hti)
    · have hzero (t : ℝ) : coordinateLine i y t ∉ Metric.closedBall c r :=
        fun h => hyV ((coordinateLine_mem_closedBall_iff i y t c r).mp h).2
      refine ⟨0, (LipschitzWith.const 0).lipschitzOnWith.absolutelyContinuousOnInterval, ?_,
        hGy.locallyIntegrable, ?_⟩
      · exact ae_of_all _ (fun t => by simp [U, φ, indicator_of_notMem (hzero t)])
      · exact ae_of_all _ (fun t _ => by simpa [G, γ, indicator_of_notMem (hzero t)] using hasDerivAt_const t (0:𝕜))
  obtain ⟨F, hFi, hFa, hFac⟩ := exists_integrable_AC_slices hab U G hUj hGj hlocal
  refine ⟨F, hFi, ?_, ?_⟩
  · filter_upwards [hFa] with y hy
    apply (ae_restrict_iff_subtype measurableSet_Icc).mpr
    filter_upwards [hy] with t ht
    have hproj : projIcc (c i - r) (c i + r) (by linarith) (t : ℝ) = t :=
      projIcc_of_mem (by linarith) t.property
    simpa only [hproj, U, φ] using ht.symm
  · filter_upwards [hFac] with y hy hyV
    obtain ⟨f, hac, _hrep, _hgli, hd, heq⟩ := hy
    refine ⟨f, hac, ?_, heq⟩
    filter_upwards [hd] with t ht hti
    simpa only [G, γ, indicator_of_mem (hmem y hyV hti)] using ht hti


section LocalBallAssembly
open Filter

/-- Local ball assembly, leaving only the product-average identity and the
integrable continuous-slice data as inputs. -/
theorem exists_acl_on_ball_of_continuousSlices {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u : Domain d → 𝕜) (g : Fin d → Domain d → 𝕜)
    (c : Domain d) (R : ℝ) (hR : 0 < R)
    (φ : Domain d → 𝕜) (hφ : Integrable φ volume)
    (hφu : ∀ x ∈ Metric.ball c R, φ x = u x)
    (F : ∀ i : Fin d, Transverse i → C(Icc (c i - R) (c i + R), 𝕜))
    (hF : ∀ i, Integrable (F i) volume)
    (hrep : ∀ i : Fin d, ∀ᵐ y : Transverse i ∂volume,
      (fun s => φ (coordinateLine i y s)) =ᵐ[volume.restrict (Icc (c i - R) (c i + R))]
        (fun s => F i y (projIcc (c i - R) (c i + R) (by linarith) s)))
    (hdata : ∀ i : Fin d, ∀ᵐ y : Transverse i ∂volume,
      y ∈ Metric.closedBall (transverseProjection i c) R →
      ∃ f : ℝ → 𝕜,
        AbsolutelyContinuousOnInterval f (c i - R) (c i + R) ∧
        (∀ᵐ t ∂volume, t ∈ Icc (c i - R) (c i + R) →
          HasDerivAt f (g i (coordinateLine i y t)) t) ∧
        ∀ t : Icc (c i - R) (c i + R), F i y t = f t) :
    ∃ f : Domain d → 𝕜,
      u =ᵐ[volume.restrict (Metric.ball c R)] f ∧
        ∀ i : Fin d, ∀ᵐ y : Transverse i ∂volume,
          LocallyAbsolutelyContinuousOn (fun t => f (coordinateLine i y t))
            (fiber (⟨Metric.ball c R, Metric.isOpen_ball⟩ : Opens (Domain d)) i y) ∧
          ∀ᵐ t ∂volume.restrict
              (fiber (⟨Metric.ball c R, Metric.isOpen_ball⟩ : Opens (Domain d)) i y : Set ℝ),
            HasDerivAt (fun s => f (coordinateLine i y s)) (g i (coordinateLine i y t)) t := by
  let B : Opens (Domain d) := ⟨Metric.ball c R, Metric.isOpen_ball⟩
  have havg (i : Fin d) (y : Transverse i) (t r : ℝ)
      (hs : Metric.closedBall t r ⊆ Icc (c i - R) (c i + R)) :
      (⨍ x in Metric.closedBall (coordinateLine i y t) r, φ x) =
      (⨍ s in Metric.closedBall t r,
        (⨍ z in Metric.closedBall y r, F i z)
          (projIcc (c i - R) (c i + R) (by linarith) s)) := by
    have hi : Integrable (fun z : ℝ × Transverse i => φ (coordinateLine i z.2 z.1)) volume := by
      have heq : (fun z : ℝ × Transverse i => φ ((coordinateEquiv i).symm z)) =
          (fun z : ℝ × Transverse i => φ (coordinateLine i z.2 z.1)) := by
        funext z
        rcases z with ⟨t, y⟩
        rw [coordinateEquiv_symm_apply]
      rw [← heq]
      exact ((coordinateEquiv_measurePreserving i).symm (coordinateEquiv i)).integrable_comp_of_integrable hφ
    rw [average_coordinate_closedBall i φ (coordinateLine i y t) r,
      coordinateEquiv_coordinateLine]
    exact average_closedBall_eq_continuousSlice_average (by linarith)
      (fun z : ℝ × Transverse i => φ (coordinateLine i z.2 z.1)) (F i)
      hi (hF i) (hrep i) t y r hs
  have hJ (i : Fin d) (y : Transverse i) (t : ℝ) (ht : t ∈ (fiber B i y : Set ℝ)) :
      t ∈ Ioo (c i - R) (c i + R) := by
    have ht' : coordinateLine i y t ∈ Metric.ball c R := ht
    have hh := (coordinateLine_mem_ball_iff i y t c R).mp ht'
    simpa only [Real.ball_eq_Ioo] using hh.1
  refine exists_common_acl_of_slice_average_identities (Ω := B) u g φ hφ ?_
    (fun i => c i - R) (fun i => c i + R) (fun i => by linarith) F hF ?_ ?_
  · exact (ae_restrict_iff' Metric.isOpen_ball.measurableSet).mpr
      (Eventually.of_forall hφu)
  · intro i
    apply Eventually.of_forall
    intro y t ht
    have htn := Icc_mem_nhds (hJ i y t ht).1 (hJ i y t ht).2
    filter_upwards [(eventually_closedBall_subset htn).filter_mono nhdsWithin_le_nhds]
      with r hr
    exact havg i y t r hr
  · intro i
    filter_upwards [hdata i] with y hy
    by_cases hyV : y ∈ Metric.closedBall (transverseProjection i c) R
    · obtain ⟨f, hfAC, hfder, hfeq⟩ := hy hyV
      refine ⟨f, ?_, ?_, ?_⟩
      · intro a b hab
        apply hfAC.mono
        rw [uIcc_of_le (by linarith : c i - R ≤ c i + R)]
        exact fun t ht => Ioo_subset_Icc_self (hJ i y t (hab ht))
      · apply (ae_restrict_iff' (fiber B i y).isOpen.measurableSet).mpr
        filter_upwards [hfder] with t ht htm
        exact ht (Ioo_subset_Icc_self (hJ i y t htm))
      · intro t ht
        rw [projIcc_of_mem _ (Ioo_subset_Icc_self (hJ i y t ht))]
        exact hfeq ⟨t, Ioo_subset_Icc_self (hJ i y t ht)⟩
    · have hfiber : (fiber B i y : Set ℝ) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro t ht
        have ht' : coordinateLine i y t ∈ Metric.ball c R := ht
        exact hyV (Metric.ball_subset_closedBall ((coordinateLine_mem_ball_iff i y t c R).mp ht').2)
      refine ⟨0, ?_, ?_, ?_⟩
      · intro a b hab
        exact contDiff_const.contDiffOn.absolutelyContinuousOnInterval
      · simp [hfiber]
      · intro t ht
        rw [hfiber] at ht
        exact ht.elim


end LocalBallAssembly

/-- The common ACL representative on a compactly contained coordinate box.
All coordinate directions use the limit of the same ambient ball averages. -/
theorem weak_to_acl_on_ball {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : DomainLp 𝕜 Ω p) (g : Fin d → DomainLp 𝕜 Ω p)
    (hweak : HasWeakCoordinateDerivatives u g) (c : Domain d) (r : ℝ) (hr : 0 < r)
    (hs : Metric.closedBall c r ⊆ (Ω : Set (Domain d))) :
    ∃ f : Domain d → 𝕜,
      u =ᵐ[volume.restrict (Metric.ball c r)] f ∧
      ∀ i : Fin d, ∀ᵐ y : Transverse i ∂volume,
        LocallyAbsolutelyContinuousOn (fun t => f (coordinateLine i y t))
          (fiber (⟨Metric.ball c r, Metric.isOpen_ball⟩ : Opens (Domain d)) i y) ∧
        ∀ᵐ t ∂volume.restrict
            (fiber (⟨Metric.ball c r, Metric.isOpen_ball⟩ : Opens (Domain d)) i y : Set ℝ),
          HasDerivAt (fun s => f (coordinateLine i y s)) (g i (coordinateLine i y t)) t := by
  classical
  choose F hFi hFa hFd using fun i =>
    exists_integrable_coordinate_AC_slices u g hweak c r hr hs i
  apply exists_acl_on_ball_of_continuousSlices u (fun i x => g i x) c r hr
    ((Metric.closedBall c r).indicator u)
    (integrable_lp_compact_indicator u (isCompact_closedBall c r) hs)
    ?_ F hFi hFa hFd
  intro x hx
  exact indicator_of_mem (Metric.ball_subset_closedBall hx) _

/-- Weak first derivatives give one ACL representative on every open domain. -/
theorem weak_to_acl {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : DomainLp 𝕜 Ω p) (g : Fin d → DomainLp 𝕜 Ω p)
    (hweak : HasWeakCoordinateDerivatives u g) :
    ∃ f : Domain d → 𝕜,
      u =ᵐ[volume.restrict (Ω : Set (Domain d))] f ∧ HasACLDerivatives Ω f g := by
  exact weak_to_acl_of_local_boxes u g
    (fun c r hr hs => weak_to_acl_on_ball u g hweak c r hr hs)

/-- The ACL representative implies the original coordinate distributional
identities. Compact tests are integrated on the whole ambient space, where their
supports remove the boundary; fiberwise integration never crosses a gap. -/
theorem acl_to_weak {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : DomainLp 𝕜 Ω p) (g : Fin d → DomainLp 𝕜 Ω p) (f : Domain d → 𝕜)
    (hrep : u =ᵐ[volume.restrict (Ω : Set (Domain d))] f)
    (hacl : HasACLDerivatives Ω f g) : HasWeakCoordinateDerivatives u g := by
  intro i
  ext φ
  simp only [neg_apply, ContinuousLinearMap.comp_apply,
    lpDistribution_apply]
  have h₁ := integrable_test_mul_lp (testPartialCLM [i] φ) u
  have h₂ := integrable_test_mul_lp φ (g i)
  have he : ∀ᵐ y : Transverse i ∂volume,
      (∫ t, φ (coordinateLine i y t) * g i (coordinateLine i y t)) =
        -(∫ t, testPartialCLM [i] φ (coordinateLine i y t) * u (coordinateLine i y t)) := by
    filter_upwards [hacl i, ae_on_fibers i hrep,
      integrable_coordinateLines i h₁, integrable_coordinateLines i h₂]
      with y hy hye h₁y h₂y
    let ψ : ℝ → 𝕜 := fun t => φ (coordinateLine i y t)
    have hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ := φ.contDiff.comp (coordinateLine_contDiff i y)
    have hcψ : HasCompactSupport ψ :=
      φ.hasCompactSupport.comp_isClosedEmbedding (coordinateLine_isClosedEmbedding i y)
    have hsψ : tsupport ψ ⊆ (fiber Ω i y : Set ℝ) :=
      (tsupport_comp_subset_preimage φ (coordinateLine_contDiff i y).continuous).trans
        (preimage_mono φ.tsupport_subset)
    have hsψ' : tsupport (deriv ψ) ⊆ (fiber Ω i y : Set ℝ) :=
      tsupport_deriv_subset.trans hsψ
    have hre : (fun t => deriv ψ t * f (coordinateLine i y t)) =ᵐ[volume]
        (fun t => deriv ψ t * u (coordinateLine i y t)) := by
      filter_upwards [(ae_restrict_iff' (fiber Ω i y).isOpen.measurableSet).mp hye] with t ht
      by_cases htU : t ∈ (fiber Ω i y : Set ℝ)
      · rw [ht htU]
      · have hdz : deriv ψ t = 0 := image_eq_zero_of_notMem_tsupport
          (fun h => htU (hsψ' h))
        simp [hdz]
    have hdint : Integrable (fun t => deriv ψ t * u (coordinateLine i y t)) volume := by
      simpa only [testPartial_on_coordinateLine] using h₁y
    have hdintf := hdint.congr hre.symm
    have hibp := integral_test_mul_density_on_open (fiber Ω i y).isOpen hy.1 hy.2
      hψ hcψ hsψ hdintf h₂y
    rw [integral_congr_ae hre] at hibp
    simpa only [ψ, testPartial_on_coordinateLine] using hibp
  calc
    (∫ x in (Ω : Set (Domain d)), φ x * g i x) = ∫ x, φ x * g i x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        simp [φ.zero_on_compl hx]
    _ = ∫ y : Transverse i, ∫ t : ℝ, φ (coordinateLine i y t) * g i (coordinateLine i y t) :=
      integral_coordinateLines i h₂
    _ = ∫ y : Transverse i, -(∫ t : ℝ,
        testPartialCLM [i] φ (coordinateLine i y t) * u (coordinateLine i y t)) :=
      integral_congr_ae he
    _ = -(∫ x, testPartialCLM [i] φ x * u x) := by
      rw [integral_neg, ← integral_coordinateLines i h₁]
    _ = -(∫ x in (Ω : Set (Domain d)), testPartialCLM [i] φ x * u x) := by
      congr 1
      symm
      exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        simp [(testPartialCLM [i] φ).zero_on_compl hx]

/-- The full ACL characterization, with the actual coordinate derivatives. -/
theorem acl_derivative_characterization :
    Specs.ExpandedFA.Sobolev.AbsoluteContinuityOnLines.DerivativeCharacterization := by
  intro 𝕜 _ d Ω p _ u g
  constructor
  · exact weak_to_acl u g
  · rintro ⟨f, hrep, hacl⟩
    exact acl_to_weak u g f hrep hacl

/-- The conclusion is stated for the original accepted Sobolev derivative graph. -/
theorem acl_membership_characterization :
    Specs.ExpandedFA.Sobolev.AbsoluteContinuityOnLines.MembershipCharacterization := by
  intro 𝕜 _ d Ω p _ u
  rw [first_order_membership_iff u]
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨f, hrep, hacl⟩ := (acl_derivative_characterization 𝕜 d Ω p u g).mp hg
    exact ⟨f, g, hrep, hacl⟩
  · rintro ⟨f, g, hrep, hacl⟩
    exact ⟨g, (acl_derivative_characterization 𝕜 d Ω p u g).mpr ⟨f, hrep, hacl⟩⟩

end ExpandedFA.Sobolev.Lines
