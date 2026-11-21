import Mathlib.Topology.Algebra.ContinuousAffineEquiv
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.AbsoluteContinuityOnLines
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.LpTranslationContinuity
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.WithDensity

/-! Independent fractional Sobolev objects for `fa2:p4:fractional-sobolev`.
The coordinate type carries product Lebesgue measure; the kernel uses Euclidean
length, not the supremum norm on the coordinate type. Extended nonnegative
integrals retain divergent energies. The intended range is 0 < s < 1 and finite
1 ≤ p. The definitions themselves also make sense outside this range.
-/
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

namespace ExpandedFA.PartIV.FractionalSobolev
open ExpandedFA.Distributions ExpandedFA.Sobolev

/-- Euclidean length of the existing product coordinates. -/
def euclideanLength {d : ℕ} (h : Domain d) : ℝ :=
  ‖WithLp.toLp 2 h‖

/-- The reciprocal difference weight is explicitly zero at the origin. -/
def differenceKernel {d : ℕ} (s : ℝ) (p : ℝ≥0∞) (h : Domain d) : ℝ≥0∞ :=
  if h = 0 then 0 else ENNReal.ofReal (euclideanLength h) ^ (-(d + s * p.toReal))

/-- The pth power of the difference seminorm. The Lp class supplies a measurable
representative; independence of this representative is a theorem below. -/
def differenceEnergy {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (s : ℝ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (u : Lp 𝕜 p (volume : Measure (Domain d))) : ℝ≥0∞ :=
  ∫⁻ h, differenceKernel s p h * ∫⁻ x, ‖u (x + h) - u x‖ₑ ^ p.toReal

/-- The equivalent Gagliardo double integral, with the diagonal assigned zero. -/
def doubleEnergy {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (s : ℝ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (u : Lp 𝕜 p (volume : Measure (Domain d))) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, differenceKernel s p (y - x) * ‖u y - u x‖ₑ ^ p.toReal

/-- The scalar-linear Lp-valued increment, as a function of the translation. -/
def lpIncrement {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (h : Domain d) : Lp 𝕜 p (volume : Measure (Domain d)) →ₗ[𝕜]
      Lp 𝕜 p (volume : Measure (Domain d)) :=
  Lp.compMeasurePreservingₗ 𝕜 (fun x => x - (-h))
    (measurePreserving_sub_right volume (-h)) - LinearMap.id

/-- The weighted translation measure for a Bochner-Lp realization of the
seminorm. It is not assumed to have finite total mass. -/
def differenceMeasure {d : ℕ} (s : ℝ) (p : ℝ≥0∞) : Measure (Domain d) :=
  volume.withDensity (differenceKernel s p)

/-- W^{s,p} consists of Lp classes of finite difference energy. -/
abbrev FractionalSpace (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (s : ℝ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :=
  {u : Lp 𝕜 p (volume : Measure (Domain d)) // differenceEnergy s p u < ∞}

/-- The full Lp-plus-difference norm, in the equivalent sum convention. On
members the extended energy is finite, so toReal loses no information. -/
def fractionalNorm {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (s : ℝ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (u : FractionalSpace 𝕜 d s p) : ℝ :=
  ‖u.val‖ + (differenceEnergy s p u.val).toReal ^ (1 / p.toReal)

/-- The norm on the fractional subtype is the full norm, rather than the
norm inherited from its inclusion in Lp. -/
instance fractionalNormInst {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (s : ℝ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] : Norm (FractionalSpace 𝕜 d s p) :=
  ⟨fractionalNorm s p⟩

/-- The multi-index for the ith first weak derivative, with no repeated copy
of the zero-order component. In dimension zero there are no such indices. -/
def firstIndex {d : ℕ} (i : Fin d) : DerivativeIndex d 1 :=
  ⟨fun j => if j = i then 1 else 0, by simp_rw [apply_ite]; simp⟩

/-- Removing restriction to the whole coordinate space is a linear isometry. -/
def wholeLpLI {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    DomainLp 𝕜 (⊤ : Opens (Domain d)) p →ₗᵢ[𝕜]
      Lp 𝕜 p (volume : Measure (Domain d)) :=
  Lp.compMeasurePreservingₗᵢ 𝕜 id (by
    change MeasurePreserving id volume (volume.restrict Set.univ)
    simpa using (MeasurePreserving.id (volume : Measure (Domain d))))

/-- The whole-space Lp class of the same scalar function. -/
def wholeLp {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : DomainLp 𝕜 (⊤ : Opens (Domain d)) p) : Lp 𝕜 p (volume : Measure (Domain d)) :=
  wholeLpLI u

/-- For 1 < s < 2, start with W^{1,p} and require each first weak derivative
to have finite order-(s-1) difference energy. -/
abbrev HigherFractionalSpace (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (s : ℝ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :=
  {u : Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.SpaceValue 𝕜 d ⊤ 1 p //
    ∀ i : Fin d, differenceEnergy (s - 1) p (wholeLp (u.val (firstIndex i))) < ∞}

/-- The natural full norm above order one: the Lp norm of the function plus
the full fractional norms of all its first weak derivatives. -/
def higherFractionalNorm {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (s : ℝ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (u : HigherFractionalSpace 𝕜 d s p) : ℝ :=
  ‖wholeLp (u.val.val (zeroIndex d 1))‖ + ∑ i : Fin d,
    fractionalNorm (s - 1) p ⟨wholeLp (u.val.val (firstIndex i)), u.property i⟩

/-- The higher space also uses its full fractional norm. -/
instance higherFractionalNormInst {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (s : ℝ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] : Norm (HigherFractionalSpace 𝕜 d s p) :=
  ⟨higherFractionalNorm s p⟩

end ExpandedFA.PartIV.FractionalSobolev


open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators

namespace ExpandedFA.PartIV.FractionalSobolev.Boundary

/-- Finite metric chart data and a subordinate Lipschitz partition. All fields
are geometric; Sobolev boundedness and atlas independence are conclusions
still to be proved from this data. -/
structure FiniteAtlas (M : Type*) [MetricSpace M] (d : ℕ) (ι : Type*) [Fintype ι] where
  chart : ι → OpenPartialHomeomorph M (Fin d → ℝ)
  cover : ∀ x : M, ∃ i, x ∈ (chart i).source
  chartLip : ι → ℝ≥0
  chartSymmLip : ι → ℝ≥0
  chart_lipschitz : ∀ i, LipschitzOnWith (chartLip i) (chart i) (chart i).source
  chartSymm_lipschitz : ∀ i, LipschitzOnWith (chartSymmLip i) (chart i).symm (chart i).target
  bounded_target : ∀ i, Bornology.IsBounded (chart i).target
  cutoff : ι → M → ℝ
  cutoffLip : ι → ℝ≥0
  cutoff_lipschitz : ∀ i, LipschitzWith (cutoffLip i) (cutoff i)
  cutoff_nonneg : ∀ i x, 0 ≤ cutoff i x
  cutoff_sum : ∀ x, ∑ i, cutoff i x = 1
  cutoff_subordinate : ∀ i, tsupport (cutoff i) ⊆ (chart i).source

namespace FiniteAtlas

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : FiniteAtlas M d ι)

lemma cutoff_le_one (i : ι) (x : M) : A.cutoff i x ≤ 1 := by
  classical
  rw [← A.cutoff_sum x]
  exact Finset.single_le_sum (fun j _ => A.cutoff_nonneg j x) (Finset.mem_univ i)

/-- Chart-coordinate Lebesgue measure pushed to the boundary. -/
def chartMeasure (i : ι) : Measure M :=
  Measure.map (A.chart i).symm (volume.restrict (A.chart i).target)

/-- A concrete common a.e. quotient for every chart in this atlas. Atlas
independence will subsequently identify this with the quotient of any other
admissible atlas (and with the usual boundary surface measure quotient). -/
def atlasMeasure : Measure M := Measure.sum A.chartMeasure

lemma chartMeasure_le (i : ι) : A.chartMeasure i ≤ A.atlasMeasure :=
  Measure.le_sum A.chartMeasure i

lemma chartMeasure_univ (i : ι) : A.chartMeasure i Set.univ = volume (A.chart i).target := by
  rw [chartMeasure, Measure.map_apply_of_aemeasurable
    ((A.chart i).continuousOn_symm.aemeasurable (A.chart i).open_target.measurableSet)
    MeasurableSet.univ]
  simp

lemma atlasMeasure_univ_lt_top : A.atlasMeasure Set.univ < ∞ := by
  classical
  rw [atlasMeasure, Measure.sum_apply _ MeasurableSet.univ, tsum_fintype]
  apply ENNReal.sum_lt_top.mpr
  intro i _
  rw [A.chartMeasure_univ]
  exact (A.bounded_target i).measure_lt_top

instance atlasMeasure_isFinite : IsFiniteMeasure A.atlasMeasure :=
  ⟨A.atlasMeasure_univ_lt_top⟩

/-- The actual zero-extended coordinate representative of a boundary piece. -/
def localizedRepresentative {𝕜 : Type} [RCLike 𝕜] (i : ι) (f : M → 𝕜) :
    (Fin d → ℝ) → 𝕜 :=
  (A.chart i).target.indicator fun x =>
    (A.cutoff i ((A.chart i).symm x) : 𝕜) * f ((A.chart i).symm x)

lemma localizedRepresentative_memLp {𝕜 : Type} [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : ι) (u : Lp 𝕜 p A.atlasMeasure) :
    MemLp (A.localizedRepresentative i u) p volume := by
  have htarget : MeasurableSet (A.chart i).target := (A.chart i).open_target.measurableSet
  have hu : MemLp (fun x => u ((A.chart i).symm x)) p
      (volume.restrict (A.chart i).target) := by
    exact ((Lp.memLp u).mono_measure (A.chartMeasure_le i)).comp_of_map
      ((A.chart i).continuousOn_symm.aemeasurable htarget)
  have hc : ContinuousOn (fun x => (A.cutoff i ((A.chart i).symm x) : 𝕜))
      (A.chart i).target := by
    exact (RCLike.continuous_ofReal.comp (A.cutoff_lipschitz i).continuous).comp_continuousOn
      (A.chart i).continuousOn_symm
  have hmul : MemLp (fun x => (A.cutoff i ((A.chart i).symm x) : 𝕜) *
      u ((A.chart i).symm x)) p (volume.restrict (A.chart i).target) := by
    apply MemLp.of_le_mul hu ((hc.aestronglyMeasurable htarget).mul hu.aestronglyMeasurable)
      (c := 1)
    filter_upwards with x
    simp only [Pi.mul_apply]
    rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg (A.cutoff_nonneg i _), one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (A.cutoff_le_one i _)
  exact (memLp_indicator_iff_restrict htarget.nullMeasurableSet).mpr hmul

/-- The common atlas measure makes every localized representative independent
of the chosen boundary representative. -/
lemma localizedRepresentative_congr_ae {𝕜 : Type} [RCLike 𝕜]
    (i : ι) {f g : M → 𝕜} (hfg : f =ᵐ[A.atlasMeasure] g) :
    A.localizedRepresentative i f =ᵐ[volume] A.localizedRepresentative i g := by
  have htarget : MeasurableSet (A.chart i).target := (A.chart i).open_target.measurableSet
  have hfg' : f =ᵐ[A.chartMeasure i] g := (ae_mono (A.chartMeasure_le i)) hfg
  have hcomp := ae_of_ae_map ((A.chart i).continuousOn_symm.aemeasurable htarget) hfg'
  have hfull := (ae_restrict_iff' htarget).mp hcomp
  filter_upwards [hfull] with x hx
  by_cases hxV : x ∈ (A.chart i).target
  · simp only [localizedRepresentative, indicator_of_mem hxV]
    rw [hx hxV]
  · simp only [localizedRepresentative, indicator_of_notMem hxV]

/-- Each local piece is supported on the chart image of the fixed cutoff
support. This compact subset is independent of the boundary function. -/
lemma localizedRepresentative_support_subset {𝕜 : Type} [RCLike 𝕜]
    (i : ι) (f : M → 𝕜) :
    Function.support (A.localizedRepresentative i f) ⊆
      (A.chart i) '' tsupport (A.cutoff i) := by
  intro x hx
  have hxV : x ∈ (A.chart i).target := by
    by_contra hxV
    simp [localizedRepresentative, hxV] at hx
  have hc : A.cutoff i ((A.chart i).symm x) ≠ 0 := by
    intro hz
    simp [localizedRepresentative, hxV, hz] at hx
  exact ⟨(A.chart i).symm x, subset_tsupport (A.cutoff i) hc, (A.chart i).right_inv hxV⟩

lemma cutoffImage_subset_target (i : ι) :
    (A.chart i) '' tsupport (A.cutoff i) ⊆ (A.chart i).target := by
  rintro _ ⟨x, hx, rfl⟩
  exact (A.chart i).map_source (A.cutoff_subordinate i hx)

lemma cutoffImage_isCompact [CompactSpace M] (i : ι) :
    IsCompact ((A.chart i) '' tsupport (A.cutoff i)) :=
  (HasCompactSupport.of_compactSpace (A.cutoff i)).isCompact.image_of_continuousOn
    ((A.chart i).continuousOn.mono (A.cutoff_subordinate i))

/-- The canonical localized Lp class. It is built from the boundary Lp quotient,
not provided as an assumed local Sobolev map. -/
def localizedLp {𝕜 : Type} [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (i : ι) (u : Lp 𝕜 p A.atlasMeasure) : Lp 𝕜 p (volume : Measure (Fin d → ℝ)) :=
  (A.localizedRepresentative_memLp p i u).toLp (A.localizedRepresentative i u)

lemma localizedLp_representative {𝕜 : Type} [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : ι) (u : Lp 𝕜 p A.atlasMeasure) :
    A.localizedLp p i u =ᵐ[volume] A.localizedRepresentative i u :=
  MemLp.coeFn_toLp _

/-- The boundary fractional space for this finite geometric atlas: each
localized Lp class must belong to the original Euclidean fractional space. -/
abbrev FractionalSpace (𝕜 : Type) [RCLike 𝕜] (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :=
  {u : Lp 𝕜 p A.atlasMeasure // ∀ i, differenceEnergy s p (A.localizedLp p i u) < ∞}

/-- The sum of full localized fractional norms, the natural atlas norm. -/
def fractionalNorm {𝕜 : Type} [RCLike 𝕜] (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : A.FractionalSpace 𝕜 s p) : ℝ :=
  ∑ i, ExpandedFA.PartIV.FractionalSobolev.fractionalNorm s p
    ⟨A.localizedLp p i u.val, u.property i⟩

/-- The boundary norm is the full sum of its localized fractional norms. -/
instance fractionalNormInst {𝕜 : Type} [RCLike 𝕜] (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Norm (A.FractionalSpace 𝕜 s p) := ⟨A.fractionalNorm s p⟩

end FiniteAtlas

end ExpandedFA.PartIV.FractionalSobolev.Boundary

namespace ExpandedFA.PartIV.FractionalSobolev.C1Geometry

/-- A genuine local C1 graph description of an embedded boundary, expressed
entirely in ambient affine coordinates. -/
def LocalC1GraphAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ}
    (Γ : Set E) (x : Γ) : Prop :=
  ∃ (Q : E ≃ᴬ[ℝ] ((Fin d → ℝ) × ℝ)) (V : Set (Fin d → ℝ)) (J : Set ℝ)
    (g : (Fin d → ℝ) → ℝ), IsOpen V ∧ IsOpen J ∧
    ((Q x.val).1 ∈ V ∧ (Q x.val).2 ∈ J) ∧ ContDiffOn ℝ 1 g V ∧
    (∀ y ∈ V, Q.symm (y,g y) ∈ Γ ∧ g y ∈ J) ∧
    (∀ z ∈ Γ, (Q z).1 ∈ V → (Q z).2 ∈ J → (Q z).2 = g (Q z).1)

open ExpandedFA.Distributions

/-- The usual local C1 graph condition on an embedded boundary. It contains
no atlas, Lipschitz bounds, partition or Sobolev mapping assumptions. -/
def IsC1GraphBoundary {n d : ℕ} (Γ : Set (Domain n)) : Prop :=
  ∀ x : Γ, LocalC1GraphAt (d:=d) Γ x

end ExpandedFA.PartIV.FractionalSobolev.C1Geometry

namespace Specs.ExpandedFA.PartIV.FractionalSobolev
open _root_.ExpandedFA.PartIV.FractionalSobolev _root_.ExpandedFA.Distributions

def SpaceType := ∀ (𝕜 : Type) [RCLike 𝕜] (_d : ℕ) (_s : ℝ)
  (p : ℝ≥0∞) [Fact (1 ≤ p)], Type

abbrev SpaceValue : SpaceType := fun 𝕜 _ d s p _ => FractionalSpace 𝕜 d s p
abbrev HigherSpaceValue : SpaceType := fun 𝕜 _ d s p _ => HigherFractionalSpace 𝕜 d s p

def EnergyType := ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (_s : ℝ)
  (p : ℝ≥0∞) [Fact (1 ≤ p)], Lp 𝕜 p (volume : Measure (Domain d)) → ℝ≥0∞

def EnergyValue : EnergyType := @differenceEnergy

def SeminormValue : EnergyType := fun {_} _ {_} s p _ u => (differenceEnergy s p u) ^ (1 / p.toReal)

def NormType := ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (s : ℝ)
  (p : ℝ≥0∞) [Fact (1 ≤ p)], FractionalSpace 𝕜 d s p → ℝ

def NormValue : NormType := @fractionalNorm

def HigherNormType := ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (s : ℝ)
  (p : ℝ≥0∞) [Fact (1 ≤ p)], HigherFractionalSpace 𝕜 d s p → ℝ

def HigherNormValue : HigherNormType := @higherFractionalNorm

/-- Off the origin the weight is precisely reciprocal Euclidean distance to
the power n+sp. -/
def KernelFormula : Prop := ∀ (d : ℕ) (s : ℝ) (p : ℝ≥0∞) (h : Domain d), h ≠ 0 →
  differenceKernel s p h = 1 / ENNReal.ofReal (euclideanLength h) ^ (d + s * p.toReal)

def SeminormFiniteIff : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (s : ℝ)
  (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
  ∀ u : Lp 𝕜 p (volume : Measure (Domain d)),
  SeminormValue s p u < ∞ ↔ differenceEnergy s p u < ∞

def NormFormula : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (s : ℝ)
  (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : FractionalSpace 𝕜 d s p),
  ‖u‖ = ‖u.val‖ + (differenceEnergy s p u.val).toReal ^ (1 / p.toReal)

/-- The numerator is exactly the power of the Lp norm of translation minus
identity, with translation x ↦ x+h and no conjugation of scalar values. -/
def TranslationFormula : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
  ∀ u : Lp 𝕜 p (volume : Measure (Domain d)),
  differenceEnergy s p u = ∫⁻ h, differenceKernel s p h *
    ‖_root_.ExpandedFA.Distributions.LpTranslationContinuitySpec.LpTranslationValue p (-h) u - u‖ₑ
      ^ p.toReal

def DoubleIntegralFormula : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
  (u : Lp 𝕜 p (volume : Measure (Domain d))),
  differenceEnergy s p u = doubleEnergy s p u

def RepresentativeFormula : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
  (u : Lp 𝕜 p (volume : Measure (Domain d))) (f : Domain d → 𝕜),
  u =ᵐ[volume] f → differenceEnergy s p u =
    ∫⁻ h, differenceKernel s p h * ∫⁻ x, ‖f (x + h) - f x‖ₑ ^ p.toReal

/-- The norm is realized by Lp of the Lp-valued increment with its weighted
translation measure. This also establishes all seminorm inequalities. -/
def WeightedLpFormula : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
  ∀ u : Lp 𝕜 p (volume : Measure (Domain d)),
  (differenceEnergy s p u) ^ (1 / p.toReal) =
    eLpNorm (fun h => lpIncrement p h u) p (differenceMeasure s p)

/-- The full sum norm has exactly the norm axioms on the vector subspace of
finite-energy Lp classes. Closure under addition and scalar multiplication is
part of the conclusion; no such closure is assumed. -/
def FullNormAxioms : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
  (differenceEnergy s p (0 : Lp 𝕜 p (volume : Measure (Domain d))) < ∞) ∧
  ∀ (u v : Lp 𝕜 p (volume : Measure (Domain d)))
    (hu : differenceEnergy s p u < ∞) (hv : differenceEnergy s p v < ∞),
    (0 ≤ fractionalNorm s p ⟨u, hu⟩) ∧
    (fractionalNorm s p ⟨u, hu⟩ = 0 ↔ u = 0) ∧
    (∃ huv : differenceEnergy s p (u + v) < ∞,
      fractionalNorm s p ⟨u + v, huv⟩ ≤ fractionalNorm s p ⟨u, hu⟩ +
        fractionalNorm s p ⟨v, hv⟩) ∧
    ∀ c : 𝕜, ∃ hcu : differenceEnergy s p (c • u) < ∞,
      fractionalNorm s p ⟨c • u, hcu⟩ = ‖c‖ * fractionalNorm s p ⟨u, hu⟩

/-- Above order one the extra condition is precisely fractional regularity
of the existing distributional coordinate derivatives. -/
def HigherMembership : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
  (u : _root_.ExpandedFA.Sobolev.DomainLp 𝕜 (⊤ : Opens (Domain d)) p),
  (∃ v : HigherFractionalSpace 𝕜 d s p,
    v.val.val (_root_.ExpandedFA.Sobolev.zeroIndex d 1) = u) ↔
  ∃ g : Fin d → _root_.ExpandedFA.Sobolev.DomainLp 𝕜 (⊤ : Opens (Domain d)) p,
    _root_.ExpandedFA.Sobolev.Lines.HasWeakCoordinateDerivatives u g ∧
    ∀ i, differenceEnergy (s - 1) p (wholeLp (g i)) < ∞

/-- The canonical norm above order one is the natural full norm. -/
def HigherNormFormula : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : HigherFractionalSpace 𝕜 d s p),
  ‖u‖ = higherFractionalNorm s p u

/-- The higher space is closed under the linear operations and its full norm
satisfies the norm axioms. First derivatives are the unique weak derivatives
from the accepted first-order graph. -/
def HigherFullNormAxioms : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
  (∀ i : Fin d, differenceEnergy (s - 1) p
    (wholeLp ((0 : _root_.ExpandedFA.Sobolev.derivativeGraph 𝕜 ⊤ 1 p).val
      (firstIndex i))) < ∞) ∧
  ∀ u v : HigherFractionalSpace 𝕜 d s p,
    (0 ≤ higherFractionalNorm s p u) ∧
    (higherFractionalNorm s p u = 0 ↔ u.val = 0) ∧
    (∃ h : ∀ i : Fin d, differenceEnergy (s - 1) p
      (wholeLp ((u.val + v.val).val (firstIndex i))) < ∞,
      higherFractionalNorm s p ⟨u.val + v.val, h⟩ ≤
        higherFractionalNorm s p u + higherFractionalNorm s p v) ∧
    ∀ c : 𝕜, ∃ h : ∀ i : Fin d, differenceEnergy (s - 1) p
      (wholeLp ((c • u.val).val (firstIndex i))) < ∞,
      higherFractionalNorm s p ⟨c • u.val, h⟩ = ‖c‖ * higherFractionalNorm s p u

/-- In dimension zero the higher norm reduces to the underlying Lp norm. -/
def HigherZeroDimensionNorm : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (s : ℝ)
  (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : HigherFractionalSpace 𝕜 0 s p),
  higherFractionalNorm s p u = ‖u.val.val (_root_.ExpandedFA.Sobolev.zeroIndex 0 1)‖

/-- Dimension zero is included, and its difference seminorm vanishes. -/
def ZeroDimension : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (s : ℝ)
  (p : ℝ≥0∞) [Fact (1 ≤ p)]
  (u : Lp 𝕜 p (volume : Measure (Domain 0))),
  differenceEnergy s p u = 0 ∧ differenceEnergy s p u < ∞

def ZeroDimensionNorm : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (s : ℝ)
  (p : ℝ≥0∞) [Fact (1 ≤ p)] (_hp : p ≠ ∞)
  (u : FractionalSpace 𝕜 0 s p), fractionalNorm s p u = ‖u.val‖

/-- Every bounded globally Lipschitz scalar multiplier is bounded. The
constant is uniform over both scalar fields and all multipliers with the given
supremum and Lipschitz bounds; in particular it retains the latter dependence. -/
def BoundedLipschitzMultiplication : Prop := ∀ (d : ℕ) (s : ℝ) (p : ℝ≥0∞)
  [Fact (1 ≤ p)], 0 < s → s < 1 → p ≠ ∞ → ∀ M L : ℝ≥0,
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (𝕜 : Type) [RCLike 𝕜] (a : (Fin d → ℝ) → 𝕜),
    (∀ x, ‖a x‖ ≤ M) →
    (∀ x y, ‖a x - a y‖ ≤ L * euclideanLength (x - y)) →
    ∀ u : FractionalSpace 𝕜 d s p, ∃ v : FractionalSpace 𝕜 d s p,
      v.val =ᵐ[volume] (fun x => a x * u.val x) ∧
      fractionalNorm s p v ≤ C * fractionalNorm s p u

/-- Bounded smooth functions with bounded first derivative are included. -/
def SmoothBoundedMultiplication : Prop := ∀ (d : ℕ) (s : ℝ) (p : ℝ≥0∞)
  [Fact (1 ≤ p)], 0 < s → s < 1 → p ≠ ∞ → ∀ M L : ℝ≥0,
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (𝕜 : Type) [RCLike 𝕜] (a : (Fin d → ℝ) → 𝕜),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → (∀ x, ‖a x‖ ≤ M) → (∀ x, ‖fderiv ℝ a x‖₊ ≤ L) →
    ∀ u : FractionalSpace 𝕜 d s p, ∃ v : FractionalSpace 𝕜 d s p,
      v.val =ᵐ[volume] (fun x => a x * u.val x) ∧
      fractionalNorm s p v ≤ C * fractionalNorm s p u

/-- Bi-Lipschitz coordinate pullback is an actual scalar-linear equivalence
of Lp classes, preserves finite fractional energy, and gives equivalent full
norms. Both directions retain their geometric measure-distortion bounds. -/
def BiLipschitzTransport : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (f : (Fin d → ℝ) ≃ₜ (Fin d → ℝ)) (K K' : ℝ≥0),
  LipschitzWith K f → LipschitzWith K' f.symm →
  ∀ (s : ℝ), 0 < s → s < 1 → ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
  ∃ e : Lp 𝕜 p (volume : Measure (Fin d → ℝ)) ≃ₗ[𝕜]
      Lp 𝕜 p (volume : Measure (Fin d → ℝ)),
    (∀ u, e u =ᵐ[volume] u ∘ f) ∧
    (∀ u, differenceEnergy s p (e u) < ∞ ↔ differenceEnergy s p u < ∞) ∧
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ u : FractionalSpace 𝕜 d s p,
        ∃ hu : differenceEnergy s p (e u.val) < ∞,
          fractionalNorm s p ⟨e u.val, hu⟩ ≤ A * fractionalNorm s p u ∧
          fractionalNorm s p u ≤ B * fractionalNorm s p ⟨e u.val, hu⟩

/-- The local version applies to chart overlaps without any global extension
assumption on the coordinate change. -/
def LocalBiLipschitzEnergy : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (f g : (Fin d → ℝ) → (Fin d → ℝ)) (U V : Set (Fin d → ℝ)),
  MeasurableSet U → MeasurableSet V → ∀ K K' : ℝ≥0,
  LipschitzOnWith K f U → LipschitzOnWith K' g V →
  (∀ x ∈ U, f x ∈ V ∧ g (f x) = x) →
  (∀ y ∈ V, g y ∈ U ∧ f (g y) = y) →
  ∀ (s : ℝ), 0 < s → s < 1 → ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
  ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ u : (Fin d → ℝ) → 𝕜, Measurable u →
    (∫⁻ x in U, ∫⁻ y in U,
      differenceKernel s p (y - x) * ‖u (f y) - u (f x)‖ₑ ^ p.toReal) ≤
    C * (∫⁻ x in V, ∫⁻ y in V,
      differenceKernel s p (y - x) * ‖u y - u x‖ₑ ^ p.toReal)

/-- A chart-supported scalar function of finite local Lp mass and fractional
energy has finite whole-space energy after zero extension. Compact containment
supplies the support separation; it is not an extra assumption. -/
def CompactSupportZeroExtension : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (d : ℕ) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)],
  0 < s → s < 1 → p ≠ ∞ → ∀ (Ω : Set (Fin d → ℝ)), IsOpen Ω →
  ∀ (f : (Fin d → ℝ) → 𝕜), Measurable f →
  ∀ (K : Set (Fin d → ℝ)), IsCompact K → K ⊆ Ω → Function.support f ⊆ K →
  (∫⁻ x in Ω, ‖f x‖ₑ ^ p.toReal) < ∞ →
  (∫⁻ x in Ω, ∫⁻ y in Ω,
    differenceKernel s p (y - x) * ‖f y - f x‖ₑ ^ p.toReal) < ∞ →
  (∫⁻ x, ∫⁻ y, differenceKernel s p (y - x) * ‖f y - f x‖ₑ ^ p.toReal) < ∞

/-- Boundary classes localized by a finite geometric atlas and its bounded
Lipschitz cutoffs. The chart measure is an actual finite Borel measure. -/
def BoundarySpaceType := ∀ (M : Type) [MetricSpace M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] (d : ℕ) (ι : Type) [Fintype ι]
  (A : _root_.ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas M d ι)
  (𝕜 : Type) [RCLike 𝕜] (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)], Type

abbrev BoundarySpaceValue : BoundarySpaceType :=
  fun _ _ _ _ _ _ _ _ A 𝕜 _ s p _ => A.FractionalSpace 𝕜 s p

def BoundaryNormType := ∀ (M : Type) [MetricSpace M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] (d : ℕ) (ι : Type) [Fintype ι]
  (A : _root_.ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas M d ι)
  (𝕜 : Type) [RCLike 𝕜] (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)],
  A.FractionalSpace 𝕜 s p → ℝ

def BoundaryNormValue : BoundaryNormType :=
  fun _ _ _ _ _ _ _ _ A _ _ s p _ u => A.fractionalNorm s p u

/-- Chart measure yields the intrinsic Hausdorff a.e. classes and is
independent of the chosen finite geometric atlas. -/
def BoundaryMeasureEquivalence : Prop := ∀ (M : Type) [MetricSpace M]
  [CompactSpace M] [MeasurableSpace M] [BorelSpace M] (d : ℕ)
  (ι κ : Type) [Fintype ι] [Fintype κ]
  (A : _root_.ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas M d ι)
  (B : _root_.ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas M d κ),
  (A.atlasMeasure ≪ Measure.hausdorffMeasure (d : ℝ)) ∧
  (Measure.hausdorffMeasure (d : ℝ) ≪ A.atlasMeasure) ∧
  (A.atlasMeasure ≪ B.atlasMeasure) ∧ (B.atlasMeasure ≪ A.atlasMeasure) ∧
  ∃ C D : ℝ≥0∞, C ≠ ∞ ∧ D ≠ ∞ ∧
    A.atlasMeasure ≤ C • B.atlasMeasure ∧ B.atlasMeasure ≤ D • A.atlasMeasure

/-- The boundary norm is the sum of full localized norms. -/
def BoundaryNormFormula : Prop := ∀ (M : Type) [MetricSpace M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] (d : ℕ) (ι : Type) [Fintype ι]
  (A : _root_.ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas M d ι)
  (𝕜 : Type) [RCLike 𝕜] (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
  (u : A.FractionalSpace 𝕜 s p), ‖u‖ = A.fractionalNorm s p u

/-- The finite atlas construction yields an actual norm on scalar a.e.
classes, with closure under the scalar-linear operations. Definiteness is
proved using chart null-set transport and the partition, not assumed. -/
def BoundaryFullNormAxioms : Prop := ∀ (M : Type) [MetricSpace M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] (d : ℕ) (ι : Type) [Fintype ι]
  (A : _root_.ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas M d ι)
  (𝕜 : Type) [RCLike 𝕜] (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
  (∀ i, differenceEnergy s p (A.localizedLp p i (0 : Lp 𝕜 p A.atlasMeasure)) < ∞) ∧
  ∀ u v : A.FractionalSpace 𝕜 s p,
    (0 ≤ A.fractionalNorm s p u) ∧
    (A.fractionalNorm s p u = 0 ↔ u.val = 0) ∧
    (∃ h : ∀ i, differenceEnergy s p (A.localizedLp p i (u.val + v.val)) < ∞,
      A.fractionalNorm s p ⟨u.val + v.val, h⟩ ≤
        A.fractionalNorm s p u + A.fractionalNorm s p v) ∧
    ∀ c : 𝕜, ∃ h : ∀ i, differenceEnergy s p (A.localizedLp p i (c • u.val)) < ∞,
      A.fractionalNorm s p ⟨c • u.val, h⟩ = ‖c‖ * A.fractionalNorm s p u

/-- The scalar a.e. spaces and their full norms are independent of the
admissible finite geometric atlas and subordinate Lipschitz cutoffs. -/
def BoundaryAtlasIndependence : Prop := ∀ (M : Type) [MetricSpace M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] (d : ℕ) (ι κ : Type) [Fintype ι] [Fintype κ]
  (A : _root_.ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas M d ι)
  (B : _root_.ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas M d κ)
  (𝕜 : Type) [RCLike 𝕜] (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)],
  0 < s → s < 1 → p ≠ ∞ →
  ∃ e : Lp 𝕜 p B.atlasMeasure ≃ₗ[𝕜] Lp 𝕜 p A.atlasMeasure,
    (∀ u, e u =ᵐ[A.atlasMeasure] u) ∧
    (∀ u, (∀ i, differenceEnergy s p (A.localizedLp p i (e u)) < ∞) ↔
      (∀ j, differenceEnergy s p (B.localizedLp p j u) < ∞)) ∧
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ u : B.FractionalSpace 𝕜 s p,
      ∃ hu : ∀ i, differenceEnergy s p (A.localizedLp p i (e u.val)) < ∞,
        A.fractionalNorm s p ⟨e u.val, hu⟩ ≤ C * B.fractionalNorm s p u ∧
        B.fractionalNorm s p u ≤ D * A.fractionalNorm s p ⟨e u.val, hu⟩

/-- Genuine local C1 graph geometry and compactness yield the finite atlas
and subordinate Lipschitz cutoffs used by the boundary spaces. -/
def CompactC1GraphAtlas : Prop := ∀ (n d : ℕ) (Γ : Set (Domain n)), IsCompact Γ →
  _root_.ExpandedFA.PartIV.FractionalSobolev.C1Geometry.IsC1GraphBoundary (d := d) Γ →
  ∃ N : ℕ, Nonempty (_root_.ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas Γ d (Fin N))

/-- The original compact boundary of an open Euclidean domain is included,
with its ordinary local C1 graph definition and all zero/empty cases. -/
def CompactC1BoundaryAtlas : Prop := ∀ (n : ℕ) (Ω : Opens (Domain n)),
  IsCompact (frontier (Ω : Set (Domain n))) →
  _root_.ExpandedFA.PartIV.FractionalSobolev.C1Geometry.IsC1GraphBoundary (d := n - 1)
    (frontier (Ω : Set (Domain n))) →
  ∃ N : ℕ, Nonempty (_root_.ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas
    (frontier (Ω : Set (Domain n))) (n - 1) (Fin N))

/-- Smoothness and boundedness alone do not suffice on the whole space.
Already for the valid parameters n=1, s=1/2, p=2 a smooth bounded real scalar
function can take a finite-energy Sobolev function outside the same space.
No particular multiplier or Sobolev witness is prescribed. -/
def SmoothBoundedMultiplierFailure : Prop :=
  ∃ a : Domain 1 → ℝ,
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a ∧
    (∃ M : ℝ, ∀ x, ‖a x‖ ≤ M) ∧
    ∃ u : FractionalSpace ℝ 1 (1 / 2) 2,
      ¬ ∃ v : FractionalSpace ℝ 1 (1 / 2) 2,
        v.val =ᵐ[volume] (fun x => a x * u.val x)


end Specs.ExpandedFA.PartIV.FractionalSobolev
