import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.Orientation
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.CellsChainsAndIntegrals
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.DirectedSubstitution
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.OrientedManifoldAndDensityIntegrals
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.JordanRegions
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.LowerDimensionalImagesHaveZeroContent
import Mathlib.Topology.Algebra.Support

/-! Canonical parameter patches for finite geometric integration.
The parameter region is an arbitrary bounded Jordan set. Its parametrization
is C¹ on an open neighborhood of its closure; no rank or injectivity is
required. Locally extendible parametrizations will be compared with these
representatives by equality of values, not by assuming uniqueness of derivatives
on an arbitrary Jordan set. All integral values are the shared Darboux values. -/
noncomputable section
open Set Function
open scoped ContDiff BigOperators Classical
namespace Specs.D04.C15.FiniteGeometricPatchIntegrals
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.PullbackCalculus.Model
open Specs.D04.C06.JordanRegions.Model
namespace Model

structure Patch (k : ℕ) {n : ℕ} (O : Set (E n)) where
  region : Set (E k)
  jordan : Jordan region
  map : E k → E n
  domain : Set (E k)
  open_domain : IsOpen domain
  contains : closure region ⊆ domain
  regular : ContDiffOn ℝ 1 map domain
  mapsTo : MapsTo map domain O

def coefficient {k n : ℕ} {O : Set (E n)} (P : Patch k O)
    (omega : FormField n k) (x : E k) : ℝ :=
  pullback P.map omega x (standardBasis k)

def weightedCoefficient {k n : ℕ} {O : Set (E n)} (P : Patch k O)
    (w : E n → ℝ) (omega : FormField n k) (x : E k) : ℝ :=
  w (P.map x) * coefficient P omega x

def patchIntegral {k n : ℕ} {O : Set (E n)} (P : Patch k O)
    (w : E n → ℝ) (omega : FormField n k) : ℝ :=
  regionIntegral (fun x : P.region => weightedCoefficient P w omega x)

/-- The weights in the interface are actual ambient functions. -/
structure AmbientPartition {n : ℕ} (K : Set (E n)) (m : ℕ) where
  weight : Fin m → E n → ℝ
  smooth : ∀ i, ContDiff ℝ ∞ (weight i)
  nonneg : ∀ i x, 0 ≤ weight i x
  compact : ∀ i, HasCompactSupport (weight i)
  sum_one : ∃ V : Set (E n), IsOpen V ∧ K ⊆ V ∧
    ∀ x ∈ V, ∑ i, weight i x = 1
  sum_le_one : ∀ x, ∑ i, weight i x ≤ 1

/-- Geometric seam data, with separate local C¹ extensions. No integral
identity is a field. In degree zero there are no nonempty lower-dimensional
seams, as the strict dimension inequality requires. -/
structure Seams (k : ℕ) where
  count : ℕ
  dim : Fin count → ℕ
  lower : ∀ i, dim i < k
  parameter : ∀ i, Set (E (dim i))
  compact : ∀ i, IsCompact (parameter i)
  map : ∀ i, E (dim i) → E k
  localC1 : ∀ i x, x ∈ parameter i →
    ∃ (U : Set (E (dim i))) (g : E (dim i) → E k),
      U ∈ nhds x ∧ ContDiffAt ℝ 1 g x ∧ EqOn g (map i) (parameter i ∩ U)

def Seams.carrier {k : ℕ} (s : Seams k) : Set (E k) :=
  ⋃ i, s.map i '' s.parameter i

/-- Separate local diffeomorphisms on the closed parameter region. The supplied
map is arbitrary off that closure. There is no single-neighborhood extension
assumption and no UniqueDiffOn assumption on the Jordan region. -/
structure LocalReparametrization {k : ℕ} (S T : Set (E k)) (sigma : ℝ) where
  map : E k → E k
  bijective : BijOn map S T
  localCharts : ∀ x ∈ closure S,
    ∃ e : OpenPartialHomeomorph (E k) (E k),
      x ∈ e.source ∧ ContDiffOn ℝ 1 e e.source ∧
      ContDiffOn ℝ 1 e.symm e.target ∧
      EqOn e map (closure S ∩ e.source) ∧
      ∀ y ∈ e.source, Real.sign ((fderiv ℝ e y).det) = sigma


def restrictPatch {k n : ℕ} {O : Set (E n)} (P : Patch k O)
    (S : Set (E k)) (hS : Jordan S) (hsub : S ⊆ P.region) : Patch k O where
  region := S
  jordan := hS
  map := P.map
  domain := P.domain
  open_domain := P.open_domain
  contains := (closure_mono hsub).trans P.contains
  regular := P.regular
  mapsTo := P.mapsTo

/-- Integer patch chains retain the actual ambient weights. -/
structure WeightedPatch (k : ℕ) {n : ℕ} (O : Set (E n)) where
  patch : Patch k O
  weight : E n → ℝ
  continuous : ContinuousOn weight O

abbrev PatchChain (k : ℕ) {n : ℕ} (O : Set (E n)) := WeightedPatch k O →₀ ℤ

def patchChainIntegral {k n} {O : Set (E n)} (omega : FormField n k) :
    PatchChain k O →+ ℝ :=
  Finsupp.liftAddHom (fun p => ({
    toFun := fun a : ℤ => a • patchIntegral p.patch p.weight omega
    map_zero' := by simp
    map_add' := fun a b => by simp [add_mul] } : ℤ →+ ℝ))

def restrictWeighted {k n} {O : Set (E n)} (p : WeightedPatch k O)
    (S : Set (E k)) (hS : Jordan S) (hsub : S ⊆ p.patch.region) : WeightedPatch k O :=
  ⟨restrictPatch p.patch S hS hsub,p.weight,p.continuous⟩

def multiplyWeight {k n} {O : Set (E n)} (p : WeightedPatch k O)
    (v : E n → ℝ) (hv : ContinuousOn v O) : WeightedPatch k O :=
  ⟨p.patch,fun x => p.weight x * v x,p.continuous.mul hv⟩

/-- Geometric generators and their additive equivalence closure. In particular,
none of the constructors is allowed to carry an assumed integral identity. -/
inductive GeometricEquivalent {k n} {O : Set (E n)} :
    PatchChain k O → PatchChain k O → Prop
  | reparam (p q : WeightedPatch k O) (s : ℤ) (hs : s = 1 ∨ s = -1)
      (h : LocalReparametrization p.patch.region q.patch.region (s : ℝ))
      (hmap : EqOn p.patch.map (q.patch.map ∘ h.map) p.patch.region)
      (hweight : EqOn p.weight q.weight (q.patch.map '' q.patch.region)) :
      GeometricEquivalent (Finsupp.single p 1) (s • Finsupp.single q 1)
  | representative (p q : WeightedPatch k O) (hregion : p.patch.region = q.patch.region)
      (hmap : EqOn p.patch.map q.patch.map p.patch.region)
      (hweight : EqOn p.weight q.weight (q.patch.map '' q.patch.region)) :
      GeometricEquivalent (Finsupp.single p 1) (Finsupp.single q 1)
  | cover (p : WeightedPatch k O) (m : ℕ) (S : Fin m → Set (E k))
      (hS : ∀ i, Jordan (S i)) (hsub : ∀ i, S i ⊆ p.patch.region)
      (hcover : p.patch.region = ⋃ i, S i) (seams : Seams k)
      (hpair : ∀ i j, i ≠ j → S i ∩ S j ⊆ seams.carrier) :
      GeometricEquivalent (Finsupp.single p 1)
        (∑ i, Finsupp.single (restrictWeighted p (S i) (hS i) (hsub i)) 1)
  | localization (p : WeightedPatch k O) (m : ℕ)
      (A : AmbientPartition (p.patch.map '' closure p.patch.region) m) :
      GeometricEquivalent (Finsupp.single p 1)
        (∑ i, Finsupp.single
          (multiplyWeight p (A.weight i) (A.smooth i).continuous.continuousOn) 1)
  | refl (C : PatchChain k O) : GeometricEquivalent C C
  | symm {C D} : GeometricEquivalent C D → GeometricEquivalent D C
  | trans {C D F} : GeometricEquivalent C D → GeometricEquivalent D F →
      GeometricEquivalent C F
  | add {C D F G} : GeometricEquivalent C D → GeometricEquivalent F G →
      GeometricEquivalent (C + F) (D + G)
  | zsmul (a : ℤ) {C D} : GeometricEquivalent C D → GeometricEquivalent (a • C) (a • D)

/-- Restriction of an ambient form to the upstream canonical tangent spaces. -/
def ambientRestriction {r : ℕ∞ω} {k n} {M : Set (E n)} (omega : FormField n k) :
    Specs.D04.C14.MetricTopFormsAndDensities.Model.TangentTopField r k M :=
  fun x => (omega x).compLinearMap
    (Specs.D04.C14.ChartIndependentTangentSpaces.Model.tangentSpace r k M x).subtype

end Model
open Model

abbrev PatchType := (k : ℕ) → {n : ℕ} → Set (E n) → Type
def PatchValue : PatchType := @Model.Patch
abbrev coefficientType := {k n : ℕ} → {O : Set (E n)} → Patch k O →
  FormField n k → E k → ℝ
def coefficientValue : coefficientType := @Model.coefficient
abbrev weightedCoefficientType := {k n : ℕ} → {O : Set (E n)} → Patch k O →
  (E n → ℝ) → FormField n k → E k → ℝ
def weightedCoefficientValue : weightedCoefficientType := @Model.weightedCoefficient
abbrev patchIntegralType := {k n : ℕ} → {O : Set (E n)} → Patch k O →
  (E n → ℝ) → FormField n k → ℝ
def patchIntegralValue : patchIntegralType := @Model.patchIntegral

abbrev AmbientPartitionType := {n : ℕ} → Set (E n) → ℕ → Type
def AmbientPartitionValue : AmbientPartitionType := @Model.AmbientPartition

abbrev SeamsType := ℕ → Type
def SeamsValue : SeamsType := @Model.Seams

abbrev LocalReparametrizationType := {k : ℕ} → Set (E k) → Set (E k) → ℝ → Type
def LocalReparametrizationValue : LocalReparametrizationType := @Model.LocalReparametrization

abbrev restrictPatchType := {k n : ℕ} → {O : Set (E n)} → (P : Patch k O) → (S : Set (E k)) → Jordan S → S ⊆ P.region → Patch k O
def restrictPatchValue : restrictPatchType := @Model.restrictPatch

abbrev WeightedPatchType := (k : ℕ) → {n : ℕ} → Set (E n) → Type
def WeightedPatchValue : WeightedPatchType := @Model.WeightedPatch

abbrev PatchChainType := (k : ℕ) → {n : ℕ} → Set (E n) → Type
def PatchChainValue : PatchChainType := @Model.PatchChain

abbrev patchChainIntegralType := {k n : ℕ} → {O : Set (E n)} → FormField n k → (PatchChain k O →+ ℝ)
def patchChainIntegralValue : patchChainIntegralType := @Model.patchChainIntegral

abbrev GeometricEquivalentType := {k n : ℕ} → {O : Set (E n)} → PatchChain k O → PatchChain k O → Prop
def GeometricEquivalentValue : GeometricEquivalentType := @Model.GeometricEquivalent

abbrev ambientRestrictionType := {r : ℕ∞ω} → {k n : ℕ} → {M : Set (E n)} → FormField n k → Specs.D04.C14.MetricTopFormsAndDensities.Model.TangentTopField r k M
def ambientRestrictionValue : ambientRestrictionType := @Model.ambientRestriction

def coefficient_continuousType : Prop :=
  ∀ {k n} {O : Set (E n)} (P : Patch k O) (omega : FormField n k),
    IsCrForm (some 0) O omega → ContinuousOn (coefficient P omega) (closure P.region)

def weighted_integrableType : Prop :=
  ∀ {k n} {O : Set (E n)} (P : Patch k O) (omega : FormField n k),
    IsCrForm (some 0) O omega → ∀ w : E n → ℝ, ContinuousOn w O →
      RegionIntegrable (fun x : P.region => weightedCoefficient P w omega x)

def patch_zero_dimensionType : Prop :=
  ∀ {n} {O : Set (E n)} (P : Patch 0 O) (w : E n → ℝ) (f : E n → ℝ),
    patchIntegral P w (fun y => scalarCovector (f y)) =
      if (0 : E 0) ∈ P.region then w (P.map 0) * f (P.map 0) else 0

def ambient_partition_existsType : Prop :=
  ∀ {n} (K : Set (E n)), IsCompact K → ∀ {ι : Type} (U : ι → Set (E n)),
    (∀ i, IsOpen (U i)) → K ⊆ ⋃ i, U i →
    ∃ (m : ℕ) (a : Fin m → ι) (p : AmbientPartition K m),
      ∀ i, tsupport (p.weight i) ⊆ U (a i)

def compact_local_extensionType : Prop :=
  ∀ {k n} (K : Set (E k)) (h : E k → E n), IsCompact K →
    (∀ x ∈ K, ∃ (U : Set (E k)) (g : E k → E n),
      IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ 1 g U ∧ EqOn g h (K ∩ U)) →
    ∃ F : E k → E n, ContDiff ℝ 1 F ∧ EqOn F h K

def seams_contentZeroType : Prop :=
  ∀ {k} (s : Seams k),
    Specs.D04.C06.NullCovers.Model.ContentZero s.carrier


def finite_weight_localizationType : Prop :=
  ∀ {k n} {O : Set (E n)} (P : Patch k O) (omega : FormField n k),
    IsCrForm (some 0) O omega → ∀ {ι : Type} [Fintype ι]
    (w : E n → ℝ) (v : ι → E n → ℝ), ContinuousOn w O →
    (∀ i, ContinuousOn (v i) O) →
    (∀ x ∈ P.region, ∑ i, v i (P.map x) = 1) →
    patchIntegral P w omega = ∑ i, patchIntegral P (fun y => w y * v i y) omega

def common_weight_refinementType : Prop :=
  ∀ {k n} {O : Set (E n)} (P : Patch k O) (omega : FormField n k),
    IsCrForm (some 0) O omega → ∀ {m l : ℕ}
    (A : AmbientPartition (P.map '' closure P.region) m)
    (B : AmbientPartition (P.map '' closure P.region) l),
    (∀ i, patchIntegral P (A.weight i) omega =
      ∑ j, patchIntegral P (fun y => A.weight i y * B.weight j y) omega) ∧
    (∀ j, patchIntegral P (B.weight j) omega =
      ∑ i, patchIntegral P (fun y => A.weight i y * B.weight j y) omega) ∧
    patchIntegral P (fun _ => 1) omega =
      ∑ i, ∑ j, patchIntegral P (fun y => A.weight i y * B.weight j y) omega


def finite_region_coverType : Prop :=
  ∀ {k n} {O : Set (E n)} (P : Patch k O) (omega : FormField n k),
    IsCrForm (some 0) O omega → ∀ w : E n → ℝ, ContinuousOn w O →
    ∀ {ι : Type} [Fintype ι] (S : ι → Set (E k))
    (hS : ∀ i, Jordan (S i)) (hsub : ∀ i, S i ⊆ P.region),
    P.region = ⋃ i, S i → ∀ seams : Seams k,
    (∀ i j, i ≠ j → S i ∩ S j ⊆ seams.carrier) →
    patchIntegral P w omega =
      ∑ i, patchIntegral (restrictPatch P (S i) (hS i) (hsub i)) w omega


def representative_independentType : Prop :=
  ∀ {k n} {O : Set (E n)} (P Q : Patch k O), P.region = Q.region →
    EqOn P.map Q.map P.region → ∀ (omega : FormField n k),
    IsCrForm (some 0) O omega → ∀ w : E n → ℝ, ContinuousOn w O →
      patchIntegral P w omega = patchIntegral Q w omega

def jordan_localizationType : Prop :=
  ∀ {k} (S : Set (E k)), Jordan S → ∀ {ι : Type} (U : ι → Set (E k)),
    (∀ i, IsOpen (U i)) → closure S ⊆ ⋃ i, U i →
    ∃ (m : ℕ) (a : Fin m → ι) (R : Fin m → Set (E k)),
      (∀ i, Jordan (R i)) ∧ (∀ i, R i ⊆ S) ∧
      (∀ i, closure (R i) ⊆ U (a i)) ∧
      Pairwise (Disjoint on R) ∧ S = ⋃ i, R i

/-- Signed substitution assumes a bijection and separate local diffeomorphism
extensions, with their actual determinant signs. -/
def local_reparametrizationType : Prop :=
  ∀ {k n} {O : Set (E n)} (P Q : Patch k O) (sigma : ℝ),
    (sigma = 1 ∨ sigma = -1) →
    ∀ h : LocalReparametrization P.region Q.region sigma,
    EqOn P.map (Q.map ∘ h.map) P.region →
    ∀ omega : FormField n k, IsCrForm (some 0) O omega →
    ∀ w : E n → ℝ, ContinuousOn w O →
      patchIntegral P w omega = sigma * patchIntegral Q w omega

/-- An arbitrary map given by locally C¹ representatives becomes a patch;
only its values on the closed Jordan region are prescribed. -/
def patch_of_local_extensionsType : Prop :=
  ∀ {k n} (O : Set (E n)), IsOpen O → ∀ (S : Set (E k)) (h : E k → E n),
    Jordan S → MapsTo h (closure S) O →
    (∀ x ∈ closure S, ∃ (U : Set (E k)) (g : E k → E n),
      IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ 1 g U ∧ EqOn g h (closure S ∩ U)) →
    ∃ P : Patch k O, P.region = S ∧ EqOn P.map h (closure S)

def region_coefficient_integralType : Prop :=
  ∀ {k} {S : Set (E k)} (hS : Jordan S) (f : S → ℝ), RegionIntegrable f →
    Specs.D04.C15.DirectedSubstitution.Model.ProperIntegrable f ∧
    regionIntegral f = Specs.D04.C15.DirectedSubstitution.Model.coefficientIntegral f

def cell_patch_existsType : Prop :=
  ∀ {r : ℕ∞} {k n} {O : Set (E n)}
    (c : Specs.D04.C15.CellsChainsAndIntegrals.Model.Cell r k O),
    ∃ P : Patch k O,
      P.region = Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k ∧
      P.map = Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension c ∧
      ∀ omega : FormField n k, IsCrForm (some 0) O omega →
        patchIntegral P (fun _ => 1) omega =
          Specs.D04.C15.CellsChainsAndIntegrals.Model.cellIntegral c omega

def matching_reparametrizationType : Prop :=
  ∀ {k n} {O : Set (E n)} (P Q : Patch k O) (sigma : ℝ),
    (sigma = 1 ∨ sigma = -1) →
    ∀ h : LocalReparametrization P.region Q.region sigma,
    EqOn P.map (Q.map ∘ h.map) P.region →
    ∀ omega : FormField n k, IsCrForm (some 0) O omega →
    ∀ w v : E n → ℝ, ContinuousOn w O → ContinuousOn v O →
    EqOn w v (Q.map '' Q.region) →
      patchIntegral P w omega = sigma * patchIntegral Q v omega

def geometric_equivalence_soundType : Prop :=
  ∀ {k n} {O : Set (E n)} (omega : FormField n k), IsCrForm (some 0) O omega →
    ∀ C D : PatchChain k O, GeometricEquivalent C D →
      patchChainIntegral omega C = patchChainIntegral omega D

def chain_zero_dimensionType : Prop :=
  ∀ {n} {O : Set (E n)} (C : PatchChain 0 O) (f : E n → ℝ),
    patchChainIntegral (fun y => scalarCovector (f y)) C =
      C.sum (fun p a => a • (if (0 : E 0) ∈ p.patch.region then
        p.weight (p.patch.map 0) * f (p.patch.map 0) else 0))

/-- Actual smooth common refinement, with the product weights and intersected
supports specified pointwise. -/
def ambient_partition_refinementType : Prop :=
  ∀ {n} (K : Set (E n)) {m l : ℕ} (A : AmbientPartition K m) (B : AmbientPartition K l),
    ∃ C : AmbientPartition K (m * l), ∀ ij : Fin m × Fin l,
      C.weight (finProdFinEquiv ij) = (fun y => A.weight ij.1 y * B.weight ij.2 y) ∧
      tsupport (C.weight (finProdFinEquiv ij)) ⊆
        tsupport (A.weight ij.1) ∩ tsupport (B.weight ij.2)

def finite_patch_partitionType : Prop :=
  ∀ {k n} {O : Set (E n)} {q : ℕ} (P : Fin q → Patch k O)
    {ι : Type} (U : ι → Set (E n)), (∀ i, IsOpen (U i)) →
    (⋃ j, (P j).map '' closure (P j).region) ⊆ ⋃ i, U i →
    ∃ (m : ℕ) (a : Fin m → ι)
      (A : AmbientPartition (⋃ j, (P j).map '' closure (P j).region) m),
      ∀ i, tsupport (A.weight i) ⊆ U (a i)

/-- A chart coefficient with the same ambient zero extension computes exactly
the patch integral. This includes restrictions of existing chart coefficients. -/
def chart_coefficient_bridgeType : Prop :=
  ∀ {k n} {O : Set (E n)} (P : Patch k O) (omega : FormField n k),
    IsCrForm (some 0) O omega → ∀ w : E n → ℝ, ContinuousOn w O →
    ∀ (T : Set (E k)) (f : T → ℝ),
      zeroExtension f = zeroExtension (fun x : P.region => weightedCoefficient P w omega x) →
      Specs.D04.C15.DirectedSubstitution.Model.ProperIntegrable f ∧
      Specs.D04.C15.DirectedSubstitution.Model.coefficientIntegral f = patchIntegral P w omega

def chart_patch_existsType : Prop :=
  ∀ {r : ℕ∞ω} {k n} {M : Set (E n)}
    (c : Specs.D04.C14.EmbeddedManifoldCharts.Model.EmbeddedChart r k n M),
    Specs.D04.C14.EmbeddedManifoldCharts.Model.ManifoldRegularity r →
    ∀ (O : Set (E n)), IsOpen O → ∀ S : Set (E k), Jordan S → closure S ⊆ c.source →
    MapsTo c.toFun (closure S) O → ∃ P : Patch k O,
      P.region = S ∧ EqOn P.map c.toFun (closure S) ∧
      ∀ x ∈ closure S, fderiv ℝ P.map x =
        Specs.D04.C14.ChartIndependentTangentSpaces.Model.chartDifferential c x

/-- An actual upstream localized tangent coefficient, restricted to a Jordan
subregion and extended by zero on the rest of the chart. -/
def chart_integral_bridgeType : Prop :=
  ∀ {r : ℕ∞ω} {k n} {M : Set (E n)}
    (c : Specs.D04.C14.EmbeddedManifoldCharts.Model.EmbeddedChart r k n M)
    {O : Set (E n)} (P : Patch k O) (hsource : P.region ⊆ c.source),
    EqOn P.map c.toFun P.region →
    (∀ x ∈ P.region, fderiv ℝ P.map x =
      Specs.D04.C14.ChartIndependentTangentSpaces.Model.chartDifferential c x) →
    ∀ omega : FormField n k, IsCrForm (some 0) O omega →
    ∀ w : E n → ℝ, ContinuousOn w O →
    let f : c.source → ℝ := fun u => if u.val ∈ P.region then
      Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.localizedTopCoefficient
        (ambientRestriction omega) c w u else 0
    Specs.D04.C15.DirectedSubstitution.Model.ProperIntegrable f ∧
      Specs.D04.C15.DirectedSubstitution.Model.coefficientIntegral f = patchIntegral P w omega

def common_region_refinementType : Prop :=
  ∀ {k n} {O : Set (E n)} (P : Patch k O) (omega : FormField n k),
    IsCrForm (some 0) O omega → ∀ w : E n → ℝ, ContinuousOn w O →
    ∀ {m l} (S : Fin m → Set (E k)) (T : Fin l → Set (E k))
      (hS : ∀ i, Jordan (S i)) (hT : ∀ j, Jordan (T j))
      (hSP : ∀ i, S i ⊆ P.region) (hTP : ∀ j, T j ⊆ P.region),
    P.region = ⋃ i, S i → P.region = ⋃ j, T j →
    ∀ A B : Seams k,
      (∀ i j, i ≠ j → S i ∩ S j ⊆ A.carrier) →
      (∀ i j, i ≠ j → T i ∩ T j ⊆ B.carrier) →
    ∃ hC : ∀ i j, Jordan (S i ∩ T j),
      (∀ i, patchIntegral (restrictPatch P (S i) (hS i) (hSP i)) w omega =
        ∑ j, patchIntegral (restrictPatch P (S i ∩ T j) (hC i j)
          (fun _ hx => hSP i hx.1)) w omega) ∧
      (∀ j, patchIntegral (restrictPatch P (T j) (hT j) (hTP j)) w omega =
        ∑ i, patchIntegral (restrictPatch P (S i ∩ T j) (hC i j)
          (fun _ hx => hSP i hx.1)) w omega) ∧
      patchIntegral P w omega =
        ∑ i, ∑ j, patchIntegral (restrictPatch P (S i ∩ T j) (hC i j)
          (fun _ hx => hSP i hx.1)) w omega

def common_localizationType : Prop :=
  ∀ {k n} {O : Set (E n)} (p : WeightedPatch k O) {m l : ℕ}
    (A : AmbientPartition (p.patch.map '' closure p.patch.region) m)
    (B : AmbientPartition (p.patch.map '' closure p.patch.region) l),
    let a : Fin m → WeightedPatch k O := fun i =>
      multiplyWeight p (A.weight i) (A.smooth i).continuous.continuousOn
    let b : Fin l → WeightedPatch k O := fun j =>
      multiplyWeight p (B.weight j) (B.smooth j).continuous.continuousOn
    let C : PatchChain k O := ∑ i, ∑ j, Finsupp.single
      (multiplyWeight (a i) (B.weight j) (B.smooth j).continuous.continuousOn) 1
    GeometricEquivalent (∑ i, Finsupp.single (a i) 1) C ∧
      GeometricEquivalent (∑ j, Finsupp.single (b j) 1) C

end Specs.D04.C15.FiniteGeometricPatchIntegrals
