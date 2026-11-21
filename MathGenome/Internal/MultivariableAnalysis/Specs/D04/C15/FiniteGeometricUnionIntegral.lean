import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.FiniteGeometricPatchIntegrals

/-! Independent interfaces for the geometric-union obligation of
`d04:15:piecewise` (paper.tex 4529–4567).

This continuation contains seam nullity, geometric germs, common-coordinate
refinements, the actual manifold-to-patch integral bridge, and the embedded
manifold structure and canonical tangent spaces of the seam complement.
It now includes actual cross-carrier integral comparison and construction of a
unique value for compact manifold decompositions with displayed ambient seams.
It also includes regular-cell interior charts and induced orientations, exact
face seam presentations, full-cube coordinate seam nullity, and convergence of
actual interior-manifold integrals to the actual cell integral. It now proves
global comparison and a unique value across finite regular-cell, compact-manifold
and mixed displays. Compact overlap carriers admit countable compact-image
coverings derived from arbitrary local-C¹ parameter pieces and embedded
manifolds, without compactness assumptions on their domains. Positive-dimensional orientation
gluing and its independence for compatible decompositions are included below. Seam cutoff convergence for the
actual single-manifold values is included below. In particular, no equivalence certificate
or assumed integral identity is used in the geometric data below. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Function Topology
open scoped ContDiff BigOperators
namespace Specs.D04.C15.FiniteGeometricUnionIntegral
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C06.NullCovers.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model

namespace Model
/-- One compact local C¹ parameter image of dimension strictly below k. -/
structure CompactSeam (k n : ℕ) where
  dim : ℕ
  lower : dim < k
  parameter : Set (E dim)
  compact : IsCompact parameter
  map : E dim → E n
  localC1 : ∀ x, x ∈ parameter →
    ∃ (U : Set (E dim)) (g : E dim → E n),
      U ∈ nhds x ∧ ContDiffAt ℝ 1 g x ∧ EqOn g map (parameter ∩ U)

/-- A compact exceptional carrier covered by countably many lower-dimensional
compact C¹ images. The covering images need not lie in the carrier, and no
finite-subcover assertion is made. This includes compact overlap sets contained
in noncompact C¹ pieces. Nullity and all integral identities are conclusions. -/
structure AmbientSeams (k n : ℕ) where
  carrier : Set (E n)
  isCompact : IsCompact carrier
  cover : ∃ P : Set (CompactSeam k n), P.Countable ∧
    carrier ⊆ ⋃ p : P, p.val.map '' p.val.parameter
end Model
open Model

abbrev AmbientSeamsType := ℕ → ℕ → Type
def AmbientSeamsValue : AmbientSeamsType := Model.AmbientSeams
abbrev seamCarrierType := {k n : ℕ} → AmbientSeams k n → Set (E n)
def seamCarrierValue : seamCarrierType := @Model.AmbientSeams.carrier

/-- Compact restriction is essential: arbitrary intersections with an open
chart need not be compact or have finite content. -/
def chart_seams_contentZeroType : Prop :=
  ∀ {k n : ℕ} {M : Set (E n)} (c : EmbeddedChart 1 k n M), k ≤ n →
    ∀ (s : AmbientSeams k n) (K : Set (E n)), IsCompact K →
      K ⊆ M ∩ c.ambient →
      IsCompact (c.invFun '' (s.carrier ∩ K)) ∧
      ContentZero (c.invFun '' (s.carrier ∩ K))

def ambient_seams_compactType : Prop :=
  ∀ {k n : ℕ} (s : AmbientSeams k n), IsCompact s.carrier

/-- Integrability of the modified coefficient is a conclusion, rather than
an additional hypothesis. All values are the actual Darboux region values. -/
def region_integral_unchangedType : Prop :=
  ∀ {k : ℕ} {S : Set (E k)}, Jordan S →
    ∀ (f g : S → ℝ), RegionIntegrable f → RegionBounded g →
    ∀ Z : Set (E k), ContentZero Z →
    (∀ x : S, x.val ∉ Z → f x = g x) →
      RegionIntegrable g ∧ regionIntegral g = regionIntegral f

def chart_seam_changesType : Prop :=
  ∀ {k n : ℕ} {M : Set (E n)} (c : EmbeddedChart 1 k n M), k ≤ n →
    ∀ (s : AmbientSeams k n) (K : Set (E n)), IsCompact K → K ⊆ M ∩ c.ambient →
    ∀ S : Set (E k), Jordan S → ∀ f g : S → ℝ,
    RegionIntegrable f → RegionBounded g →
    (∀ x : S, x.val ∉ c.invFun '' (s.carrier ∩ K) → f x = g x) →
      RegionIntegrable g ∧ regionIntegral g = regionIntegral f

/-- A geometric count at each point, without any integral hypothesis. -/
def multiplicity_oneType : Prop :=
  ∀ {n : ℕ} {ι : Type} [Fintype ι] (A : ι → Set (E n)) (Z : Set (E n)),
    (∀ i j, i ≠ j → A i ∩ A j ⊆ Z) →
    ∀ x : E n, x ∉ Z →
      (∑ i, (A i).indicator (fun _ => (1 : ℝ)) x) =
        (⋃ i, A i).indicator (fun _ => (1 : ℝ)) x

/-- Two different compact pieces cannot accumulate at a point outside their
stipulated overlaps. No smooth-manifold assumption on the union is used. -/
def isolated_pieceType : Prop :=
  ∀ {n : ℕ} {ι : Type} [Fintype ι] (A : ι → Set (E n)) (Z : Set (E n)),
    (∀ i, IsCompact (A i)) → (∀ i j, i ≠ j → A i ∩ A j ⊆ Z) →
    ∀ i x, x ∈ A i → x ∉ Z →
      ∃ U : Set (E n), IsOpen U ∧ x ∈ U ∧
        U ∩ (⋃ j, A j) = U ∩ A i

/-- The same geometric union admits identical piece germs off the seams of
two independent finite decompositions. The pieces may be distinct manifolds
and the union may have corners. -/
def common_piece_germType : Prop :=
  ∀ {n : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : ι → Set (E n)) (B : κ → Set (E n)) (Z W : Set (E n)),
    (∀ i, IsCompact (A i)) → (∀ j, IsCompact (B j)) →
    (∀ i j, i ≠ j → A i ∩ A j ⊆ Z) →
    (∀ i j, i ≠ j → B i ∩ B j ⊆ W) →
    (⋃ i, A i) = ⋃ j, B j →
    ∀ x, x ∈ ⋃ i, A i → x ∉ Z ∪ W →
      ∃ i j, ∃ U : Set (E n), x ∈ A i ∧ x ∈ B j ∧
        IsOpen U ∧ x ∈ U ∧ U ∩ A i = U ∩ B j ∧
        U ∩ (⋃ l, A l) = U ∩ A i

/-- The usual union integral in one coordinate space; overlaps are omitted
only after their zero content has been proved. -/
def coordinate_union_integralType : Prop :=
  ∀ {k : ℕ} {ι : Type} [Fintype ι] (A : ι → Set (E k)),
    (∀ i, Jordan (A i)) → ∀ Z : Set (E k), ContentZero Z →
    (∀ i j, i ≠ j → A i ∩ A j ⊆ Z) →
    ∀ f : E k → ℝ, ContinuousOn f (closure (⋃ i, A i)) →
      Jordan (⋃ i, A i) ∧
      RegionIntegrable (fun x : (⋃ i, A i) => f x) ∧
      regionIntegral (fun x : (⋃ i, A i) => f x) =
        ∑ i, regionIntegral (fun x : A i => f x)

/-- Common-refinement independence is a theorem about intersections of
geometric regions, not a generator postulated to preserve an integral. -/
def coordinate_common_refinementType : Prop :=
  ∀ {k : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : ι → Set (E k)) (B : κ → Set (E k)),
    (∀ i, Jordan (A i)) → (∀ j, Jordan (B j)) →
    ∀ Z W : Set (E k), ContentZero Z → ContentZero W →
    (∀ i j, i ≠ j → A i ∩ A j ⊆ Z) →
    (∀ i j, i ≠ j → B i ∩ B j ⊆ W) →
    (⋃ i, A i) = ⋃ j, B j →
    ∀ f : E k → ℝ, ContinuousOn f (closure (⋃ i, A i)) →
      (∀ i j, Jordan (A i ∩ B j)) ∧
      (∀ i, regionIntegral (fun x : A i => f x) =
        ∑ j, regionIntegral (fun x : ↥(A i ∩ B j) => f x)) ∧
      (∀ j, regionIntegral (fun x : B j => f x) =
        ∑ i, regionIntegral (fun x : ↥(A i ∩ B j) => f x)) ∧
      (∑ i, regionIntegral (fun x : A i => f x)) =
        ∑ j, regionIntegral (fun x : B j => f x)

/-- A genuinely geometric Jordan test: intersect a compact Jordan chart core
with the pieces of another finite compact decomposition. The pieces are not
assumed to belong to the same smooth manifold. The hypothesis on overlaps is
ambient geometric containment, from which the coordinate nullity is derived. -/
def chart_subregions_jordanType : Prop :=
  ∀ {k n : ℕ} {M : Set (E n)} (c : EmbeddedChart 1 k n M), k ≤ n →
    ∀ K : Set (E k), IsCompact K → Jordan K → K ⊆ c.source →
    ∀ {ι : Type} [Fintype ι] (B : ι → Set (E n)) (s : AmbientSeams k n),
    (∀ j, IsCompact (B j)) →
    (∀ i j, i ≠ j → B i ∩ B j ⊆ s.carrier) →
    c.toFun '' K ⊆ ⋃ j, B j →
    ∀ j, IsCompact (K ∩ c.toFun ⁻¹' B j) ∧
      frontier (K ∩ c.toFun ⁻¹' B j) ⊆ frontier K ∪
        c.invFun '' (s.carrier ∩ (c.toFun '' K)) ∧
      Jordan (K ∩ c.toFun ⁻¹' B j)

/-- Actual coordinate integral additivity for subregions obtained from a
second geometric decomposition, including regions adjoining a half-space
boundary. Both Jordan measurability and zero-content seams are conclusions
of the geometric argument. -/
def chart_geometric_decompositionType : Prop :=
  ∀ {k n : ℕ} {M : Set (E n)} (c : EmbeddedChart 1 k n M), k ≤ n →
    ∀ K : Set (E k), IsCompact K → Jordan K → K ⊆ c.source →
    ∀ {ι : Type} [Fintype ι] (B : ι → Set (E n)) (s : AmbientSeams k n),
    (∀ j, IsCompact (B j)) →
    (∀ i j, i ≠ j → B i ∩ B j ⊆ s.carrier) →
    c.toFun '' K ⊆ ⋃ j, B j →
    ∀ f : E k → ℝ, ContinuousOn f K →
      regionIntegral (fun x : K => f x) =
        ∑ j, regionIntegral (fun x : ↥(K ∩ c.toFun ⁻¹' B j) => f x)

/-- Retargeting a restricted chart uses equality of the embedded sets on an
open neighborhood, not an assumed transition map or integral equality. -/
def chart_retargetType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M N : Set (E n)}
    (c : EmbeddedChart r k n M) (U : Set (E n)), IsOpen U → U ∩ M = U ∩ N →
    ∃ d : EmbeddedChart r k n N,
      d.source = c.source ∩ c.toFun ⁻¹' U ∧
      d.ambient = c.ambient ∩ U ∧ d.toFun = c.toFun ∧ d.invFun = c.invFun ∧
      d.half = c.half

/-- Actual common charts for two decompositions of the same embedded union,
constructed from geometric equality off the seams. No chart correspondence
is assumed. -/
def common_piece_chartsType : Prop :=
  ∀ {k n : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : ι → Set (E n)) (B : κ → Set (E n)) (Z W : Set (E n)),
    (∀ i, IsCompact (A i)) → (∀ j, IsCompact (B j)) →
    (∀ i, IsEmbeddedManifold 1 k (A i)) →
    (∀ i j, i ≠ j → A i ∩ A j ⊆ Z) →
    (∀ i j, i ≠ j → B i ∩ B j ⊆ W) →
    (⋃ i, A i) = ⋃ j, B j →
    ∀ x, x ∈ ⋃ i, A i → x ∉ Z ∪ W →
      ∃ i j, ∃ (c : EmbeddedChart 1 k n (A i)) (d : EmbeddedChart 1 k n (B j))
        (u : E k), u ∈ c.source ∧ c.toFun u = x ∧
        d.source = c.source ∧ d.toFun = c.toFun ∧ d.invFun = c.invFun ∧
        d.ambient = c.ambient ∧ d.half = c.half

/-- Equality of actual restricted manifold-chart integrals on common local
charts of distinct pieces, with arbitrary continuous ambient weights.
This is a local comparison, not yet the whole-union independence theorem. -/
def common_chart_integralsType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M N : Set (E n)}
    (c : EmbeddedChart r k n M) (d : EmbeddedChart r k n N),
    ManifoldRegularity r → d.source = c.source → d.toFun = c.toFun →
    ∀ S : Set (E k), Jordan S → closure S ⊆ c.source →
    ∀ {O : Set (E n)}
      (omega : Specs.D04.C13.NormalizedFormsAndWedge.Model.FormField n k),
    Specs.D04.C13.NormalizedFormsAndWedge.Model.IsCrForm (some 0) O omega →
    MapsTo c.toFun (closure S) O → ∀ w : E n → ℝ, ContinuousOn w O →
    let f : c.source → ℝ := fun u => if u.val ∈ S then
      Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.localizedTopCoefficient
        (Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.ambientRestriction omega) c w u else 0
    let g : d.source → ℝ := fun u => if u.val ∈ S then
      Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.localizedTopCoefficient
        (Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.ambientRestriction omega) d w u else 0
    Specs.D04.C15.DirectedSubstitution.Model.ProperIntegrable f ∧
      Specs.D04.C15.DirectedSubstitution.Model.ProperIntegrable g ∧
      Specs.D04.C15.DirectedSubstitution.Model.coefficientIntegral f =
        Specs.D04.C15.DirectedSubstitution.Model.coefficientIntegral g


namespace Model
/-- A canonical parameter patch displaying a full localized chart coefficient.
All fields are geometric, differential, or pointwise support conditions. -/
structure ChartPatch {r : ℕ∞ω} {k n : ℕ} {M O : Set (E n)}
    (c : EmbeddedChart r k n M) (w : E n → ℝ) where
  patch : Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.Patch k O
  source : closure patch.region ⊆ c.source
  map_eq : EqOn patch.map c.toFun patch.region
  differential_eq : ∀ x ∈ patch.region, fderiv ℝ patch.map x =
    Specs.D04.C14.ChartIndependentTangentSpaces.Model.chartDifferential c x
  covers : ∀ u : c.source, w (c.toFun u) ≠ 0 → u.val ∈ patch.region
end Model

open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model

abbrev ChartPatchType := {r : ℕ∞ω} → {k n : ℕ} → {M O : Set (E n)} →
  EmbeddedChart r k n M → (E n → ℝ) → Type
def ChartPatchValue : ChartPatchType := @Model.ChartPatch

/-- Any compact subset of a chart domain can be enclosed in a compact Jordan
core inside that domain, including points on its genuine flat boundary. -/
def chart_jordan_coreType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (c : EmbeddedChart r k n M)
    (L : Set (E k)), IsCompact L → L ⊆ c.source →
    ∃ K : Set (E k), IsCompact K ∧ Jordan K ∧ L ⊆ K ∧ K ⊆ c.source

/-- Construction covers the entire support of each weight; no common global
extension of the given boundary chart is required. -/
def chart_patch_existsType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M O : Set (E n)}
    (c : EmbeddedChart r k n M), ManifoldRegularity r → IsOpen O → M ⊆ O →
    ∀ w : E n → ℝ, IsCompact (tsupport (fun x : M => w x)) →
    tsupport (fun x : M => w x) ⊆ Subtype.val ⁻¹' c.ambient →
    Nonempty (ChartPatch (O := O) c w)

/-- The full proper chart integral equals the actual canonical patch integral
for every geometric display, rather than only for a selected construction. -/
def chart_patch_integralType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M O : Set (E n)}
    (c : EmbeddedChart r k n M) (w : E n → ℝ) (P : ChartPatch (O := O) c w)
    (omega : FormField n k), IsCrForm (some 0) O omega → ContinuousOn w O →
    Specs.D04.C15.DirectedSubstitution.Model.ProperIntegrable
      (localizedTopCoefficient (ambientRestriction (r := r) (M := M) omega) c w) ∧
    Specs.D04.C15.DirectedSubstitution.Model.coefficientIntegral
      (localizedTopCoefficient (ambientRestriction (r := r) (M := M) omega) c w) =
        patchIntegral P.patch w omega

/-- Actual tangent restrictions of continuous ambient forms are continuous in
the upstream chart trivializations, with only C¹ charts required. -/
def ambient_restriction_continuousType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M O : Set (E n)}, ManifoldRegularity r → M ⊆ O →
    ∀ omega : FormField n k, IsCrForm (some 0) O omega →
    ContinuousTopField (ambientRestriction (r := r) (M := M) omega)

/-- Every prescribed signed chart partition has a finite canonical patch
expansion with its own weights and signs and the actual manifold value. -/
def manifold_patch_expansionType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M O : Set (E n)}
    (o : PositiveManifoldOrientation r k M), IsOpen O → M ⊆ O →
    ∀ omega : FormField n k, IsCrForm (some 0) O omega →
    ∀ P : SignedChartPartition o (topSupport (ambientRestriction (r := r) (M := M) omega)),
    ∃ C : ∀ i, ChartPatch (O := O) (P.chart i) (P.weight i),
      orientedIntegral (ambientRestriction (r := r) (M := M) omega) P =
        ∑ i, (P.sign i).val * patchIntegral (C i).patch (P.weight i) omega

/-- Independence of all patch representatives and all signed chart/weight
choices on a smooth piece. The values compared are actual Darboux integrals.
This does not claim decomposition independence on a cornered union. -/
def manifold_patch_independentType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M O : Set (E n)}
    (o : PositiveManifoldOrientation r k M), M ⊆ O →
    ∀ omega : FormField n k, IsCrForm (some 0) O omega →
    ∀ P Q : SignedChartPartition o (topSupport (ambientRestriction (r := r) (M := M) omega)),
    ∀ (C : ∀ i, ChartPatch (O := O) (P.chart i) (P.weight i))
      (D : ∀ j, ChartPatch (O := O) (Q.chart j) (Q.weight j)),
      (∑ i, (P.sign i).val * patchIntegral (C i).patch (P.weight i) omega) =
        ∑ j, (Q.sign j).val * patchIntegral (D j).patch (Q.weight j) omega


namespace Model
/-- The embedded regular part of a finite union, after removing its seams. -/
def regularLocus {n : ℕ} {ι : Type} (A : ι → Set (E n)) (Z : Set (E n)) :
    Set (E n) := (⋃ i, A i) \ Z
end Model

abbrev regularLocusType := {n : ℕ} → {ι : Type} → (ι → Set (E n)) → Set (E n) → Set (E n)
def regularLocusValue : regularLocusType := @Model.regularLocus

/-- Identical local parametrizations identify the actual canonical tangent
subspaces of two distinct carriers. -/
def common_chart_tangentSpacesType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M N : Set (E n)}
    (c : EmbeddedChart r k n M) (d : EmbeddedChart r k n N),
    ManifoldRegularity r → k ≤ n → d.source = c.source → d.toFun = c.toFun →
    ∀ u ∈ c.source,
      Specs.D04.C14.ChartIndependentTangentSpaces.Model.tangentSpace r k M (c.toFun u) =
        Specs.D04.C14.ChartIndependentTangentSpaces.Model.tangentSpace r k N (c.toFun u)

/-- Off any closed exceptional carrier containing pairwise intersections,
the finite union has the same charts as its unique piece. No manifold
structure is assumed on the whole union. -/
def regular_locus_chartsType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {ι : Type} [Fintype ι]
    (A : ι → Set (E n)) (Z : Set (E n)), IsClosed Z →
    (∀ i, IsCompact (A i)) → (∀ i, IsEmbeddedManifold r k (A i)) →
    (∀ i j, i ≠ j → A i ∩ A j ⊆ Z) →
    ∀ x ∈ regularLocus A Z,
      ∃ i, ∃ (c : EmbeddedChart r k n (A i))
        (d : EmbeddedChart r k n (regularLocus A Z)) (u : E k),
        CenteredAt c u ∧ c.toFun u = x ∧
        d.source = c.source ∧ d.toFun = c.toFun ∧ d.invFun = c.invFun ∧
        d.ambient = c.ambient ∧ d.half = c.half

/-- The actual seam complement is an embedded manifold (possibly noncompact
and with boundary), even when the full geometric union has corners. -/
def regular_locus_manifoldType : Prop :=
  ∀ {k n : ℕ} {ι : Type} [Fintype ι] (A : ι → Set (E n))
    (s : AmbientSeams k n), k ≤ n →
    (∀ i, IsCompact (A i)) → (∀ i, IsEmbeddedManifold 1 k (A i)) →
    (∀ i j, i ≠ j → A i ∩ A j ⊆ s.carrier) →
      IsEmbeddedManifold 1 k (regularLocus A s.carrier)


/-- The regular locus inherits the actual canonical tangent space of each
piece containing the point. This is derived from geometric charts. -/
def regular_locus_tangentSpaceType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {ι : Type} [Fintype ι]
    (A : ι → Set (E n)) (Z : Set (E n)), ManifoldRegularity r → k ≤ n → IsClosed Z →
    (∀ i, IsCompact (A i)) → (∀ i, IsEmbeddedManifold r k (A i)) →
    (∀ i j, i ≠ j → A i ∩ A j ⊆ Z) →
    ∀ x ∈ regularLocus A Z, ∀ i, x ∈ A i →
      Specs.D04.C14.ChartIndependentTangentSpaces.Model.tangentSpace r k
        (regularLocus A Z) x =
      Specs.D04.C14.ChartIndependentTangentSpaces.Model.tangentSpace r k (A i) x

/- Quantitative deletion of seam neighborhoods for the actual Darboux values.
These interfaces include construction of smooth ambient cutoffs and convergence
of proper chart and prescribed manifold integrals. -/
open Filter
open Specs.D04.C06.DarbouxIntegral.Model (Box Integrable carrier integral content)
open Specs.D04.C14.MetricTopFormsAndDensities.Model

def box_integral_small_near_nullType : Prop :=
  ∀ {k : ℕ} (Z : Set (E k))
    (_hZc : IsCompact Z) (_hZ : ContentZero Z)
    (M : ℝ) (_hM : 0 ≤ M) (ε : ℝ) (_hε : 0 < ε),
    ∃ U : Set (E k), IsOpen U ∧ Z ⊆ U ∧
      ∀ (Q : Box k) (f : E k → ℝ) (hf : Integrable f Q)
        (δ : ℝ), 0 ≤ δ →
        (∀ x ∈ carrier Q, |f x| ≤ M) →
        (∀ x ∈ carrier Q, x ∉ U → |f x| ≤ δ) →
        |integral f Q hf| < ε + δ * content Q

def region_integral_small_near_nullType : Prop :=
  ∀ {k : ℕ} (Z : Set (E k))
    (_hZc : IsCompact Z) (_hZ : ContentZero Z)
    (M : ℝ) (_hM : 0 ≤ M) (ε : ℝ) (_hε : 0 < ε),
    ∃ U : Set (E k), IsOpen U ∧ Z ⊆ U ∧
      ∀ (S : Set (E k)), Jordan S → ∀ (f : S → ℝ), RegionIntegrable f →
        ∀ δ : ℝ, 0 ≤ δ → (∀ x, |f x| ≤ M) →
        (∀ x : S, x.val ∉ U → |f x| ≤ δ) →
        |regionIntegral f| < ε + δ * content (enclosingBox S)

def region_seam_limitType : Prop :=
  ∀ {k : ℕ} {S : Set (E k)} (_hS : Jordan S)
    (Z : Set (E k)) (_hZc : IsCompact Z) (_hZ : ContentZero Z)
    (f : S → ℝ) (g : ℕ → S → ℝ) (_hf : RegionIntegrable f)
    (_hg : ∀ m, RegionIntegrable (g m)) (M : ℝ) (_hM : 0 ≤ M)
    (_hbound : ∀ m x, |g m x - f x| ≤ M)
    (_hconv : ∀ U : Set (E k), IsOpen U → Z ⊆ U → ∀ δ : ℝ, 0 < δ →
      ∀ᶠ m in atTop, ∀ x : S, x.val ∉ U → |g m x - f x| ≤ δ),
    Tendsto (fun m => regionIntegral (g m)) atTop (𝓝 (regionIntegral f))

def chart_seam_cutoffType : Prop :=
  ∀ {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart 1 k n M) (_hkn : k ≤ n) (s : AmbientSeams k n)
    (K : Set (E k)) (_hK : IsCompact K) (_hKJ : Jordan K) (_hKs : K ⊆ c.source)
    (f : E k → ℝ) (_hf : ContinuousOn f K) (ε : ℝ) (_hε : 0 < ε),
    ∃ χ : E n → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧
      (∃ V : Set (E n), IsOpen V ∧ s.carrier ⊆ V ∧ EqOn χ (fun _ => 0) V) ∧
      RegionIntegrable (fun x : K => χ (c.toFun x) * f x) ∧
      |regionIntegral (fun x : K => χ (c.toFun x) * f x) -
        regionIntegral (fun x : K => f x)| < ε

def smooth_seam_cutoff_sequenceType : Prop :=
  ∀ {n : ℕ} (Z : Set (E n)) (_hZ : IsCompact Z),
    ∃ χ : ℕ → E n → ℝ,
      (∀ m, ContDiff ℝ ∞ (χ m)) ∧
      (∀ m x, χ m x ∈ Icc (0 : ℝ) 1) ∧
      (∀ m, ∃ V : Set (E n), IsOpen V ∧ Z ⊆ V ∧ EqOn (χ m) (fun _ => 0) V) ∧
      (∀ A : Set (E n), IsCompact A → Disjoint A Z →
        ∀ᶠ m in atTop, EqOn (χ m) (fun _ => 1) A)

def chart_seam_cutoff_limitType : Prop :=
  ∀ {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart 1 k n M) (_hkn : k ≤ n) (s : AmbientSeams k n)
    (K : Set (E k)) (_hK : IsCompact K) (_hKJ : Jordan K) (_hKs : K ⊆ c.source)
    (f : E k → ℝ) (_hf : ContinuousOn f K)
    (χ : ℕ → E n → ℝ) (_hχ : ∀ m, ContDiff ℝ ∞ (χ m))
    (_hχv : ∀ m x, χ m x ∈ Icc (0 : ℝ) 1)
    (_hχone : ∀ A : Set (E n), IsCompact A → Disjoint A s.carrier →
      ∀ᶠ m in atTop, EqOn (χ m) (fun _ => 1) A),
    (∀ m, RegionIntegrable (fun x : K => χ m (c.toFun x) * f x)) ∧
      Tendsto (fun m => regionIntegral (fun x : K => χ m (c.toFun x) * f x))
        atTop (𝓝 (regionIntegral (fun x : K => f x)))

def coefficient_restrict_coreType : Prop :=
  ∀ {k : ℕ} {S K : Set (E k)} (hKS : K ⊆ S)
    (f : S → ℝ) (_hsupport : ∀ u, f u ≠ 0 → u.val ∈ K),
    (Specs.D04.C15.DirectedSubstitution.Model.ProperIntegrable f ↔
      Specs.D04.C15.DirectedSubstitution.Model.ProperIntegrable (fun x : K => f ⟨x,hKS x.property⟩)) ∧
    Specs.D04.C15.DirectedSubstitution.Model.coefficientIntegral f =
      Specs.D04.C15.DirectedSubstitution.Model.coefficientIntegral (fun x : K => f ⟨x,hKS x.property⟩)

def coefficient_seam_cutoff_limitType : Prop :=
  ∀ {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart 1 k n M) (_hkn : k ≤ n) (s : AmbientSeams k n)
    (f : c.source → ℝ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
    (χ : ℕ → E n → ℝ) (_hχ : ∀ m, ContDiff ℝ ∞ (χ m))
    (_hχv : ∀ m x, χ m x ∈ Icc (0 : ℝ) 1)
    (_hχone : ∀ A : Set (E n), IsCompact A → Disjoint A s.carrier →
      ∀ᶠ m in atTop, EqOn (χ m) (fun _ => 1) A),
    (∀ m, Specs.D04.C15.DirectedSubstitution.Model.ProperIntegrable (fun u => χ m (c.toFun u) * f u)) ∧
      Tendsto (fun m => Specs.D04.C15.DirectedSubstitution.Model.coefficientIntegral
        (fun u : c.source => χ m (c.toFun u) * f u))
        atTop (𝓝 (Specs.D04.C15.DirectedSubstitution.Model.coefficientIntegral f))

def manifold_seam_cutoff_limitType : Prop :=
  ∀ {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation 1 k M) (s : AmbientSeams k n)
    (η : TangentTopField 1 k M) (_hη : ContinuousTopField η)
    (χ : ℕ → E n → ℝ) (_hχ : ∀ m, ContDiff ℝ ∞ (χ m))
    (_hχv : ∀ m x, χ m x ∈ Icc (0 : ℝ) 1)
    (_hχone : ∀ A : Set (E n), IsCompact A → Disjoint A s.carrier →
      ∀ᶠ m in atTop, EqOn (χ m) (fun _ => 1) A)
    (P : SignedChartPartition o (topSupport η))
    (Q : ∀ m, SignedChartPartition o (topSupport (fun x : M => χ m x • η x))),
    Tendsto (fun m => orientedIntegral (fun x : M => χ m x • η x) (Q m))
      atTop (𝓝 (orientedIntegral η P))

def manifold_seam_cutoffsType : Prop :=
  ∀ {k n : ℕ} (s : AmbientSeams k n),
    ∃ χ : ℕ → E n → ℝ,
      (∀ m, ContDiff ℝ ∞ (χ m)) ∧
      (∀ m x, χ m x ∈ Icc (0 : ℝ) 1) ∧
      (∀ m, ∃ V : Set (E n), IsOpen V ∧ s.carrier ⊆ V ∧ EqOn (χ m) (fun _ => 0) V) ∧
      ∀ (M : Set (E n)), IsCompact M →
      ∀ (o : PositiveManifoldOrientation 1 k M) (η : TangentTopField 1 k M),
        ContinuousTopField η →
        (∀ m, IsCompact (Subtype.val '' topSupport (fun x : M => χ m x • η x)) ∧
          Disjoint (Subtype.val '' topSupport (fun x : M => χ m x • η x)) s.carrier) ∧
        ∀ (P : SignedChartPartition o (topSupport η))
          (Q : ∀ m, SignedChartPartition o (topSupport (fun x : M => χ m x • η x))),
          Tendsto (fun m => orientedIntegral (fun x : M => χ m x • η x) (Q m))
            atTop (𝓝 (orientedIntegral η P))


open Specs.D04.C14.ChartIndependentTangentSpaces.Model

namespace Model
/-- Transport by the linear equivalence that is the identity on ambient
vectors. The equality is established from geometric chart germs. -/
def transportOrientation {k n : ℕ} {P Q : Submodule ℝ (E n)} (h : P = Q) :
    Orientation ℝ P (Fin k) → Orientation ℝ Q (Fin k) :=
  Orientation.map (Fin k) (LinearEquiv.ofEq P Q h)
end Model

abbrev transportOrientationType := {k n : ℕ} → {P Q : Submodule ℝ (E n)} →
  P = Q → Orientation ℝ P (Fin k) → Orientation ℝ Q (Fin k)
def transportOrientationValue : transportOrientationType := @Model.transportOrientation

/-- Tangent transport preserves actual chart signs, including charts restricted
inside a half-space and charts with distinct target carriers. -/
def chart_sign_transportType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M N : Set (E n)}
    (c : EmbeddedChart r k n M) (d : EmbeddedChart r k n N)
    (_hr : ManifoldRegularity r) (hs : d.source ⊆ c.source) (_hf : d.toFun = c.toFun)
    (a : TangentOrientationField r k M) (b : TangentOrientationField r k N)
    (u : E k) (hu : u ∈ d.source)
    (ht : tangentSpace r k N (d.toFun u) = tangentSpace r k M (c.toFun u))
    (_ho : a (c.toFun u) (c.map_source (hs hu)).1 =
      transportOrientation ht (b (d.toFun u) (d.map_source hu).1)),
    chartSign a c u (hs hu) = chartSign b d u hu

/-- An actual continuous orientation on the regular locus is constructed from
arbitrary prescribed piece orientations. The tangent equalities and orientation
transport equations are conclusions. The entire union may have corners. -/
def regular_locus_orientationType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {ι : Type} [Fintype ι]
    (A : ι → Set (E n)) (Z : Set (E n)) (_hr : ManifoldRegularity r)
    (_hk : 0 < k) (_hkn : k ≤ n) (_hZ : IsClosed Z)
    (_hA : ∀ i, IsCompact (A i)) (o : ∀ i, PositiveManifoldOrientation r k (A i))
    (_hp : ∀ i j, i ≠ j → A i ∩ A j ⊆ Z),
    ∃ p : PositiveManifoldOrientation r k (regularLocus A Z),
      ∀ x (hx : x ∈ regularLocus A Z) i (hi : x ∈ A i),
        ∃ h : tangentSpace r k (A i) x = tangentSpace r k (regularLocus A Z) x,
          p.atPoint x hx = transportOrientation h ((o i).atPoint x hi)


/-- Unique inheritance of the prescribed actual orientations. -/
def regular_locus_orientation_uniqueType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {ι : Type} [Fintype ι]
    (A : ι → Set (E n)) (Z : Set (E n)) (_hr : ManifoldRegularity r)
    (_hk : 0 < k) (_hkn : k ≤ n) (_hZ : IsClosed Z)
    (_hA : ∀ i, IsCompact (A i)) (o : ∀ i, PositiveManifoldOrientation r k (A i))
    (_hp : ∀ i j, i ≠ j → A i ∩ A j ⊆ Z),
    ∃! p : PositiveManifoldOrientation r k (regularLocus A Z),
      ∀ x (hx : x ∈ regularLocus A Z) i (hi : x ∈ A i),
        ∃ h : tangentSpace r k (A i) x = tangentSpace r k (regularLocus A Z) x,
          p.atPoint x hx = transportOrientation h ((o i).atPoint x hi)

namespace Model
/-- Concatenating geometric seam displays preserves their strict dimension
bounds and separate local regularity, and represents their union. -/
def appendSeams {k n : ℕ} (s t : AmbientSeams k n) : AmbientSeams k n where
  carrier := s.carrier ∪ t.carrier
  isCompact := s.isCompact.union t.isCompact
  cover := by
    obtain ⟨P,hP,hs⟩ := s.cover
    obtain ⟨Q,hQ,ht⟩ := t.cover
    refine ⟨P ∪ Q,hP.union hQ,?_⟩
    rintro x (hx | hx)
    · obtain ⟨p,hp⟩ := Set.mem_iUnion.mp (hs hx)
      exact Set.mem_iUnion.mpr ⟨⟨p.val,Or.inl p.property⟩,hp⟩
    · obtain ⟨q,hq⟩ := Set.mem_iUnion.mp (ht hx)
      exact Set.mem_iUnion.mpr ⟨⟨q.val,Or.inr q.property⟩,hq⟩

end Model

abbrev appendSeamsType := {k n : ℕ} → AmbientSeams k n → AmbientSeams k n → AmbientSeams k n
def appendSeamsValue : appendSeamsType := @Model.appendSeams

def append_seams_carrierType : Prop :=
  ∀ {k n : ℕ} (s t : AmbientSeams k n),
    (appendSeams s t).carrier = s.carrier ∪ t.carrier


/-- The two admissible decompositions induce one and the same continuous
orientation on their common seam complement. Compatibility is pointwise
transport of the prescribed tangent orientations, not equality of integrals. -/
def common_regular_orientationType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : ι → Set (E n)) (B : κ → Set (E n)) (Z W : Set (E n))
    (_hr : ManifoldRegularity r) (_hk : 0 < k) (_hkn : k ≤ n)
    (_hZ : IsClosed Z) (_hW : IsClosed W)
    (_hA : ∀ i, IsCompact (A i)) (_hB : ∀ j, IsCompact (B j))
    (o : ∀ i, PositiveManifoldOrientation r k (A i))
    (p : ∀ j, PositiveManifoldOrientation r k (B j))
    (_hpA : ∀ i j, i ≠ j → A i ∩ A j ⊆ Z)
    (_hpB : ∀ i j, i ≠ j → B i ∩ B j ⊆ W)
    (_hcover : (⋃ i, A i) = ⋃ j, B j)
    (_hcompatible : ∀ x, x ∉ Z ∪ W → ∀ i j (hi : x ∈ A i) (hj : x ∈ B j),
      ∀ h : tangentSpace r k (A i) x = tangentSpace r k (B j) x,
        transportOrientation h ((o i).atPoint x hi) = (p j).atPoint x hj),
    ∃! q : PositiveManifoldOrientation r k (regularLocus A (Z ∪ W)),
      (∀ x (hx : x ∈ regularLocus A (Z ∪ W)) i (hi : x ∈ A i),
        ∃ h : tangentSpace r k (A i) x = tangentSpace r k (regularLocus A (Z ∪ W)) x,
          q.atPoint x hx = transportOrientation h ((o i).atPoint x hi)) ∧
      (∀ x (hx : x ∈ regularLocus A (Z ∪ W)) j (hj : x ∈ B j),
        ∃ h : tangentSpace r k (B j) x = tangentSpace r k (regularLocus A (Z ∪ W)) x,
          q.atPoint x hx = transportOrientation h ((p j).atPoint x hj))

/-- Full proper integrals of the same ambient form and weight in identical
charts agree even when the target carriers are different. This is an equality
of the actual zero-extension integrals, with integrability equivalent. -/
def common_chart_proper_integralsType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M N : Set (E n)}
    (c : EmbeddedChart r k n M) (d : EmbeddedChart r k n N),
    ManifoldRegularity r → d.source = c.source → d.toFun = c.toFun →
    ∀ (omega : FormField n k) (w : E n → ℝ),
    (Specs.D04.C15.DirectedSubstitution.Model.ProperIntegrable
      (localizedTopCoefficient (ambientRestriction omega) c w) ↔
      Specs.D04.C15.DirectedSubstitution.Model.ProperIntegrable
      (localizedTopCoefficient (ambientRestriction omega) d w)) ∧
    Specs.D04.C15.DirectedSubstitution.Model.coefficientIntegral
      (localizedTopCoefficient (ambientRestriction omega) c w) =
      Specs.D04.C15.DirectedSubstitution.Model.coefficientIntegral
      (localizedTopCoefficient (ambientRestriction omega) d w)

/-- Restricting an actual coefficient to a smaller common chart preserves its
integrability and value when its support is contained in that smaller source. -/
def restricted_chart_proper_integralsType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M N : Set (E n)}
    (c : EmbeddedChart r k n M) (d : EmbeddedChart r k n N),
    ManifoldRegularity r → (hs : d.source ⊆ c.source) → d.toFun = c.toFun →
    ∀ (omega : FormField n k) (w : E n → ℝ),
    (∀ u : c.source, localizedTopCoefficient (ambientRestriction omega) c w u ≠ 0 →
      u.val ∈ d.source) →
    (Specs.D04.C15.DirectedSubstitution.Model.ProperIntegrable
      (localizedTopCoefficient (ambientRestriction omega) c w) ↔
      Specs.D04.C15.DirectedSubstitution.Model.ProperIntegrable
      (localizedTopCoefficient (ambientRestriction omega) d w)) ∧
    Specs.D04.C15.DirectedSubstitution.Model.coefficientIntegral
      (localizedTopCoefficient (ambientRestriction omega) c w) =
      Specs.D04.C15.DirectedSubstitution.Model.coefficientIntegral
      (localizedTopCoefficient (ambientRestriction omega) d w)

/-- Equality of actual manifold values across two distinct carriers when the
weighted ambient form is compactly supported in a common chart. Every allowed
partition on each carrier gives the same answer. Orientations are compared by
the actual ambient-identity tangent transport, rather than by an integral axiom. -/
def common_single_chart_integralType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M N O : Set (E n)}
    (o : PositiveManifoldOrientation r k M) (p : PositiveManifoldOrientation r k N),
    M ⊆ O → N ⊆ O →
    ∀ omega : FormField n k, IsCrForm (some 0) O omega →
    ∀ w : E n → ℝ, Continuous w →
    ∀ (c : EmbeddedChart r k n M) (d : EmbeddedChart r k n N),
    d.source = c.source → d.toFun = c.toFun →
    ∀ s : PointSign,
    (∀ u : c.source, chartSign o.atPoint c u u.property = s.val) →
    (∀ (u : E k) (hu : u ∈ c.source) (hv : u ∈ d.source)
      (h : tangentSpace r k M (c.toFun u) = tangentSpace r k N (d.toFun u)),
      p.atPoint (d.toFun u) (d.map_source hv).1 =
        transportOrientation h (o.atPoint (c.toFun u) (c.map_source hu).1)) →
    let eta : TangentTopField r k M := fun x => w x • ambientRestriction omega x
    let xi : TangentTopField r k N := fun x => w x • ambientRestriction omega x
    IsCompact (topSupport eta) → IsCompact (topSupport xi) →
    topSupport eta ⊆ Subtype.val ⁻¹' c.ambient →
    topSupport xi ⊆ Subtype.val ⁻¹' d.ambient →
    ∀ (P : SignedChartPartition o (topSupport eta))
      (Q : SignedChartPartition p (topSupport xi)),
      Specs.D04.C15.DirectedSubstitution.Model.ProperIntegrable
        (localizedTopCoefficient (ambientRestriction omega) c w) ∧
      Specs.D04.C15.DirectedSubstitution.Model.ProperIntegrable
        (localizedTopCoefficient (ambientRestriction omega) d w) ∧
      orientedIntegral eta P = orientedIntegral xi Q

/-- Common constant-sign charts can be chosen inside the seam complement,
isolating one piece of each decomposition. The equal signs follow from the
prescribed tangent orientations; neither signs nor chart correspondences are
assumed as extra certificates. -/
def common_signed_chart_germsType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : ι → Set (E n)) (B : κ → Set (E n)) (Z W : Set (E n)),
    IsClosed Z → IsClosed W →
    (∀ i, IsCompact (A i)) → (∀ j, IsCompact (B j)) →
    ∀ (o : ∀ i, PositiveManifoldOrientation r k (A i))
      (p : ∀ j, PositiveManifoldOrientation r k (B j)),
    (∀ i j, i ≠ j → A i ∩ A j ⊆ Z) →
    (∀ i j, i ≠ j → B i ∩ B j ⊆ W) →
    (⋃ i, A i) = ⋃ j, B j →
    (∀ x, x ∉ Z ∪ W → ∀ i j (hi : x ∈ A i) (hj : x ∈ B j),
      ∀ h : tangentSpace r k (A i) x = tangentSpace r k (B j) x,
        transportOrientation h ((o i).atPoint x hi) = (p j).atPoint x hj) →
    ∀ x, x ∈ ⋃ i, A i → x ∉ Z ∪ W →
    ∃ i j, ∃ (c : EmbeddedChart r k n (A i)) (d : EmbeddedChart r k n (B j))
      (s : PointSign),
      x ∈ A i ∧ x ∈ B j ∧ x ∈ c.ambient ∧
      d.source = c.source ∧ d.toFun = c.toFun ∧ d.invFun = c.invFun ∧
      d.ambient = c.ambient ∧ d.half = c.half ∧
      c.ambient ⊆ (Z ∪ W)ᶜ ∧
      (∀ l, l ≠ i → Disjoint (A l) c.ambient) ∧
      (∀ l, l ≠ j → Disjoint (B l) c.ambient) ∧
      (∀ u : c.source, chartSign (o i).atPoint c u u.property = s.val) ∧
      (∀ u : d.source, chartSign (p j).atPoint d u u.property = s.val)


/-- Actual local comparison used in geometric decomposition independence. -/
def common_weighted_piece_integralsType : Prop :=
  ∀
    {r : ℕ∞ω} {k n : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : ι → Set (E n)) (B : κ → Set (E n))
    (hA : ∀ i, IsCompact (A i)) (hB : ∀ j, IsCompact (B j))
    (o : ∀ i, PositiveManifoldOrientation r k (A i))
    (p : ∀ j, PositiveManifoldOrientation r k (B j))
    {O : Set (E n)} (hAO : ∀ i, A i ⊆ O) (hBO : ∀ j, B j ⊆ O)
    (omega : FormField n k) (ho : IsCrForm (some 0) O omega)
    (i : ι) (j : κ) (c : EmbeddedChart r k n (A i)) (d : EmbeddedChart r k n (B j))
    (hs : d.source = c.source) (he : d.toFun = c.toFun) (s : PointSign)
    (hsc : ∀ u : c.source, chartSign (o i).atPoint c u u.property = s.val)
    (hsd : ∀ u : d.source, chartSign (p j).atPoint d u u.property = s.val)
    (hdisA : ∀ l, l ≠ i → Disjoint (A l) c.ambient)
    (hdisB : ∀ l, l ≠ j → Disjoint (B l) d.ambient)
    (w : E n → ℝ) (hw : Continuous w)
    (hwc : tsupport w ⊆ c.ambient) (hwd : tsupport w ⊆ d.ambient)
    (P : ∀ l, SignedChartPartition (o l)
      (topSupport (fun x : A l => w x • Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.ambientRestriction (r := r) omega x)))
    (Q : ∀ l, SignedChartPartition (p l)
      (topSupport (fun x : B l => w x • Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.ambientRestriction (r := r) omega x))),
    (∑ l, orientedIntegral (fun x : A l => w x • Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.ambientRestriction (r := r) omega x) (P l)) =
      ∑ l, orientedIntegral (fun x : B l => w x • Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.ambientRestriction (r := r) omega x) (Q l)


/-- Actual local comparison used in geometric decomposition independence. -/
def manifold_decomposition_away_seamsType : Prop :=
  ∀
    {r : ℕ∞ω} {k n : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : ι → Set (E n)) (B : κ → Set (E n)) (Z W : Set (E n))
    (hZ : IsClosed Z) (hW : IsClosed W)
    (hA : ∀ i, IsCompact (A i)) (hB : ∀ j, IsCompact (B j))
    (o : ∀ i, PositiveManifoldOrientation r k (A i))
    (p : ∀ j, PositiveManifoldOrientation r k (B j))
    (hpA : ∀ i j, i ≠ j → A i ∩ A j ⊆ Z)
    (hpB : ∀ i j, i ≠ j → B i ∩ B j ⊆ W)
    (hcover : (⋃ i, A i) = ⋃ j, B j)
    (hcompat : ∀ x, x ∉ Z ∪ W → ∀ i j (hi : x ∈ A i) (hj : x ∈ B j),
      ∀ h : tangentSpace r k (A i) x = tangentSpace r k (B j) x,
        transportOrientation h ((o i).atPoint x hi) = (p j).atPoint x hj)
    {O : Set (E n)} (hAO : ∀ i, A i ⊆ O) (hBO : ∀ j, B j ⊆ O)
    (omega : FormField n k) (ho : IsCrForm (some 0) O omega)
    (V : Set (E n)) (hV : IsOpen V) (hZW : Z ∪ W ⊆ V)
    (hzero : EqOn omega (fun _ => 0) V)
    (P : ∀ i, SignedChartPartition (o i)
      (topSupport (Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.ambientRestriction (r := r) omega)))
    (Q : ∀ j, SignedChartPartition (p j)
      (topSupport (Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.ambientRestriction (r := r) omega))),
    (∑ i, orientedIntegral (Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.ambientRestriction (r := r) omega) (P i)) =
      ∑ j, orientedIntegral (Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.ambientRestriction (r := r) omega) (Q j)


/-- Equality of actual piece integrals for arbitrary compatible compact C¹ decompositions. -/
def manifold_decomposition_independentType : Prop :=
  ∀
    {k n : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : ι → Set (E n)) (B : κ → Set (E n)) (s t : AmbientSeams k n)
    (hA : ∀ i, IsCompact (A i)) (hB : ∀ j, IsCompact (B j))
    (o : ∀ i, PositiveManifoldOrientation 1 k (A i))
    (p : ∀ j, PositiveManifoldOrientation 1 k (B j))
    (hpA : ∀ i j, i ≠ j → A i ∩ A j ⊆ s.carrier)
    (hpB : ∀ i j, i ≠ j → B i ∩ B j ⊆ t.carrier)
    (hcover : (⋃ i, A i) = ⋃ j, B j)
    (hcompat : ∀ x, x ∉ s.carrier ∪ t.carrier →
      ∀ i j (hi : x ∈ A i) (hj : x ∈ B j),
      ∀ h : tangentSpace 1 k (A i) x = tangentSpace 1 k (B j) x,
        transportOrientation h ((o i).atPoint x hi) = (p j).atPoint x hj)
    {O : Set (E n)} (hAO : ∀ i, A i ⊆ O) (hBO : ∀ j, B j ⊆ O)
    (omega : FormField n k) (ho : IsCrForm (some 0) O omega)
    (P : ∀ i, SignedChartPartition (o i)
      (topSupport (Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.ambientRestriction (r := 1) omega)))
    (Q : ∀ j, SignedChartPartition (p j)
      (topSupport (Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.ambientRestriction (r := 1) omega))),
    (∑ i, orientedIntegral (Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.ambientRestriction (r := 1) omega) (P i)) =
      ∑ j, orientedIntegral (Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.ambientRestriction (r := 1) omega) (Q j)


namespace Model
/-- Finite compact C¹ manifold pieces with prescribed actual orientations and
geometrically displayed lower-dimensional overlaps. The total carrier is allowed
corners and is not required to be an embedded manifold. -/
structure CompactManifoldDecomposition (k n : ℕ) where
  count : ℕ
  piece : Fin count → Set (E n)
  compact : ∀ i, IsCompact (piece i)
  orientation : ∀ i, PositiveManifoldOrientation 1 k (piece i)
  seams : AmbientSeams k n
  overlap : ∀ i j, i ≠ j → piece i ∩ piece j ⊆ seams.carrier

def CompactManifoldDecomposition.carrier {k n : ℕ}
    (D : CompactManifoldDecomposition k n) : Set (E n) := ⋃ i, D.piece i

/-- Equality of the geometric carrier and compatibility of its prescribed
orientations at all common regular points. All tangent identifications use the
ambient identity; there is no condition about integral values. -/
def CompatibleDecompositions {k n : ℕ} (D E : CompactManifoldDecomposition k n) : Prop :=
  D.carrier = E.carrier ∧
  ∀ x, x ∉ D.seams.carrier ∪ E.seams.carrier →
    ∀ i j (hi : x ∈ D.piece i) (hj : x ∈ E.piece j),
      ∀ h : tangentSpace 1 k (D.piece i) x = tangentSpace 1 k (E.piece j) x,
        transportOrientation h (D.orientation i |>.atPoint x hi) =
          (E.orientation j).atPoint x hj

/-- The usual multiplicity-one integral is characterized by all admissible
geometric displays and every allowed signed chart partition on every piece.
Existence and uniqueness of this property are proved, rather than postulated. -/
def HasCompactUnionIntegral {k n : ℕ} (D : CompactManifoldDecomposition k n)
    (omega : FormField n k) (v : ℝ) : Prop :=
  ∀ E : CompactManifoldDecomposition k n, CompatibleDecompositions D E →
    ∀ P : ∀ i, SignedChartPartition (E.orientation i)
      (topSupport (ambientRestriction (r := 1) (M := E.piece i) omega)),
      (∑ i, orientedIntegral (ambientRestriction (r := 1) omega) (P i)) = v

/-- The canonical value is chosen from the display-independent characterization.
For every continuous ambient form near the compact carrier the property is
proved to have exactly one witness, so the fallback branch is never used. -/
def compactUnionIntegral {k n : ℕ} (D : CompactManifoldDecomposition k n)
    (omega : FormField n k) : ℝ :=
  if h : ∃ v, HasCompactUnionIntegral D omega v then Classical.choose h else 0
end Model

abbrev CompactManifoldDecompositionType := ℕ → ℕ → Type
def CompactManifoldDecompositionValue : CompactManifoldDecompositionType := Model.CompactManifoldDecomposition
abbrev decompositionCarrierType := {k n : ℕ} → CompactManifoldDecomposition k n → Set (E n)
def decompositionCarrierValue : decompositionCarrierType := @Model.CompactManifoldDecomposition.carrier
abbrev CompatibleDecompositionsType := {k n : ℕ} → CompactManifoldDecomposition k n → CompactManifoldDecomposition k n → Prop
def CompatibleDecompositionsValue : CompatibleDecompositionsType := @Model.CompatibleDecompositions
abbrev HasCompactUnionIntegralType := {k n : ℕ} → CompactManifoldDecomposition k n → FormField n k → ℝ → Prop
def HasCompactUnionIntegralValue : HasCompactUnionIntegralType := @Model.HasCompactUnionIntegral
abbrev compactUnionIntegralType := {k n : ℕ} → CompactManifoldDecomposition k n → FormField n k → ℝ
def compactUnionIntegralValue : compactUnionIntegralType := @Model.compactUnionIntegral

/-- Construction and uniqueness of the value simultaneously represented by all
compatible decompositions and all actual chart partitions. -/
def compact_union_integral_existsType : Prop :=
  ∀ {k n : ℕ} (D : CompactManifoldDecomposition k n) {O : Set (E n)},
    D.carrier ⊆ O → ∀ omega : FormField n k, IsCrForm (some 0) O omega →
      ∃! v, HasCompactUnionIntegral D omega v

/-- The canonical value agrees with the sum of the actual prescribed piece
integrals for EVERY compatible geometric display and EVERY signed partition. -/
def compact_union_integral_eq_sumType : Prop :=
  ∀ {k n : ℕ} (D F : CompactManifoldDecomposition k n), CompatibleDecompositions D F →
    ∀ {O : Set (E n)}, D.carrier ⊆ O →
    ∀ omega : FormField n k, IsCrForm (some 0) O omega →
    ∀ P : ∀ i, SignedChartPartition (F.orientation i)
      (topSupport (ambientRestriction (r := 1) (M := F.piece i) omega)),
      compactUnionIntegral D omega =
        ∑ i, orientedIntegral (ambientRestriction (r := 1) omega) (P i)

/-- The construction itself, as well as its sum expressions, is independent of
admissible geometric decomposition. -/
def compact_union_integral_independentType : Prop :=
  ∀ {k n : ℕ} (D F : CompactManifoldDecomposition k n), CompatibleDecompositions D F →
    ∀ {O : Set (E n)}, D.carrier ⊆ O →
    ∀ omega : FormField n k, IsCrForm (some 0) O omega →
      compactUnionIntegral D omega = compactUnionIntegral F omega


namespace Model
/-- The one-piece geometric display uses the prescribed manifold orientation
and has an empty seam display. -/
def singleManifoldDecomposition {k n : ℕ} {M : Set (E n)}
    (hM : IsCompact M) (o : PositiveManifoldOrientation 1 k M) :
    CompactManifoldDecomposition k n where
  count := 1
  piece := fun _ => M
  compact := fun _ => hM
  orientation := fun _ => o
  seams :=
    { carrier := ∅
      isCompact := isCompact_empty
      cover := ⟨∅,Set.countable_empty,Set.empty_subset _⟩ }
  overlap := fun i j h => False.elim (h (Subsingleton.elim i j))
end Model

abbrev singleManifoldDecompositionType := {k n : ℕ} → {M : Set (E n)} →
  IsCompact M → PositiveManifoldOrientation 1 k M → CompactManifoldDecomposition k n
def singleManifoldDecompositionValue : singleManifoldDecompositionType := @Model.singleManifoldDecomposition

/-- On a smooth single carrier, the geometric-union value is exactly its usual
upstream manifold integral, with the given orientation and any chart partition. -/
def compact_union_integral_singleType : Prop :=
  ∀ {k n : ℕ} {M O : Set (E n)} (hM : IsCompact M)
    (o : PositiveManifoldOrientation 1 k M), M ⊆ O →
    ∀ omega : FormField n k, IsCrForm (some 0) O omega →
    ∀ P : SignedChartPartition o (topSupport (ambientRestriction (r := 1) omega)),
      compactUnionIntegral (singleManifoldDecomposition hM o) omega =
        orientedIntegral (ambientRestriction (r := 1) omega) P

/-- Any full canonical parameter-patch display of every localized piece chart
computes the same geometric value, using the actual Jordan/Darboux integrals. -/
def compact_union_integral_patch_expansionType : Prop :=
  ∀ {k n : ℕ} (D : CompactManifoldDecomposition k n) {O : Set (E n)},
    D.carrier ⊆ O → ∀ omega : FormField n k, IsCrForm (some 0) O omega →
    ∀ P : ∀ i, SignedChartPartition (D.orientation i)
      (topSupport (ambientRestriction (r := 1) (M := D.piece i) omega)),
    ∀ C : ∀ i j, ChartPatch (O := O) ((P i).chart j) ((P i).weight j),
      compactUnionIntegral D omega =
        ∑ i, ∑ j, ((P i).sign j).val * patchIntegral (C i j).patch ((P i).weight j) omega

/-- A continuous injective parametrization on a compact set is an embedding on
any open subset of that set. Its exterior parameter remainder is excluded by
an actual open ambient neighborhood; rank is required only on the open subset. -/
def compact_parameter_chartType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} (S V : Set (E k)) (f : E k → E n),
    IsCompact S → IsOpen V → V ⊆ S → ContinuousOn f S → InjOn f S →
    FullRankLocalExtension r V f →
    ∃ c : EmbeddedChart r k n (f '' V),
      c.half = false ∧ c.source = V ∧ c.toFun = f ∧
      c.invFun = Function.invFunOn f S ∧ c.ambient = (f '' (S \ V))ᶜ ∧
      f '' V ⊆ c.ambient

/-- A regular injective cell has an actual embedded interior, even though its
closed image may have corners. No smoothness of the closed cell is assumed. -/
def cell_interior_chartType : Prop :=
  ∀ {r : ℕ∞} {k n : ℕ} {O : Set (E n)}
    (a : Specs.D04.C15.CellsChainsAndIntegrals.Model.Cell r k O), k ≤ n →
    InjOn (Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension a)
      (Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k) →
    (∀ x ∈ interior (Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k),
      Function.Injective (fderiv ℝ (Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension a) x)) →
    let f := Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension a
    let S := Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k
    ∃ c : EmbeddedChart 1 k n (f '' interior S),
      c.half = false ∧ c.source = interior S ∧ c.toFun = f ∧
      c.invFun = Function.invFunOn f S ∧ c.ambient = (f '' frontier S)ᶜ ∧
      IsEmbeddedManifold 1 k (f '' interior S)

/-- The displayed faces of every cell are an actual finite ambient seam
presentation of strictly smaller dimension. This includes endpoints of curves
and does not assume that the faces themselves are regular or injective. -/
def cell_faces_seamsType : Prop :=
  ∀ {r : ℕ∞} {k n : ℕ} {O : Set (E n)}
    (a : Specs.D04.C15.CellsChainsAndIntegrals.Model.Cell r (k+1) O),
    ∃ s : AmbientSeams (k+1) n,
      s.carrier = ⋃ i : Fin (k+1), ⋃ ε : Bool,
        Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension
          (Specs.D04.C15.CellsChainsAndIntegrals.Model.cellFace a i ε) ''
          Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k

/-- Compact injectivity prevents other parameter branches from entering the
local graph neighborhood. Consequently the actual inverse on the whole compact
image has separate C¹ ambient extensions, including at corner parameters. -/
def compact_parameter_inverse_extensionsType : Prop :=
  ∀ {k n : ℕ} (S : Set (E k)) (f : E k → E n), k ≤ n →
    IsCompact S → ContinuousOn f S → InjOn f S → FullRankLocalExtension 1 S f →
    ∀ x ∈ S, ∃ (U : Set (E n)) (g : E n → E k),
      IsOpen U ∧ f x ∈ U ∧ ContDiffOn ℝ 1 g U ∧
      EqOn g (Function.invFunOn f S) ((f '' S) ∩ U)

/-- Lower-dimensional ambient seams pull back to compact sets of content zero
in the parameters of a compact embedded regular piece, with no smooth-boundary
condition on the parameter set. In particular this applies to closed cubes. -/
def compact_parameter_seams_contentZeroType : Prop :=
  ∀ {k n : ℕ} (S : Set (E k)) (f : E k → E n), k ≤ n →
    IsCompact S → ContinuousOn f S → InjOn f S → FullRankLocalExtension 1 S f →
    ∀ s : AmbientSeams k n,
      IsCompact (S ∩ f ⁻¹' s.carrier) ∧ ContentZero (S ∩ f ⁻¹' s.carrier)

/-- Quantitative seam deletion applies to actual compact Jordan parameter
regions, including cubes with corners, using the proved coordinate nullity. -/
def compact_parameter_cutoff_limitType : Prop :=
  ∀ {k n : ℕ} (S : Set (E k)) (f : E k → E n), k ≤ n →
    IsCompact S → Jordan S → ContinuousOn f S → InjOn f S →
    FullRankLocalExtension 1 S f → ∀ s : AmbientSeams k n,
    ∀ b : E k → ℝ, ContinuousOn b S →
    ∀ χ : ℕ → E n → ℝ, (∀ m, ContDiff ℝ ∞ (χ m)) →
    (∀ m x, χ m x ∈ Icc (0 : ℝ) 1) →
    (∀ A : Set (E n), IsCompact A → Disjoint A s.carrier →
      ∀ᶠ m in atTop, EqOn (χ m) (fun _ => 1) A) →
    (∀ m, RegionIntegrable (fun x : S => χ m (f x) * b x)) ∧
      Tendsto (fun m => regionIntegral (fun x : S => χ m (f x) * b x))
        atTop (𝓝 (regionIntegral (fun x : S => b x)))

/-- Source regular-cell hypotheses imply seam nullity on the entire closed
cube, rather than only compact cores of its interior. -/
def cell_seams_contentZeroType : Prop :=
  ∀ {r : ℕ∞} {k n : ℕ} {O : Set (E n)}
    (a : Specs.D04.C15.CellsChainsAndIntegrals.Model.Cell r k O), k ≤ n →
    InjOn (Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension a)
      (Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k) →
    (∀ x ∈ Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k,
      Function.Injective (fderiv ℝ (Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension a) x)) →
    ∀ s : AmbientSeams k n,
      let S := Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k
      let f := Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension a
      IsCompact (S ∩ f ⁻¹' s.carrier) ∧ ContentZero (S ∩ f ⁻¹' s.carrier)

/-- Cutting off ambient seams converges to the actual upstream cell integral.
All truncation integrals here are the original Jordan/Darboux values. -/
def cell_seam_cutoff_limitType : Prop :=
  ∀ {r : ℕ∞} {k n : ℕ} {O : Set (E n)}
    (a : Specs.D04.C15.CellsChainsAndIntegrals.Model.Cell r k O), k ≤ n →
    InjOn (Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension a)
      (Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k) →
    (∀ x ∈ Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k,
      Function.Injective (fderiv ℝ (Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension a) x)) →
    ∀ s : AmbientSeams k n, ∀ omega : FormField n k, IsCrForm (some 0) O omega →
    ∀ χ : ℕ → E n → ℝ, (∀ m, ContDiff ℝ ∞ (χ m)) →
    (∀ m x, χ m x ∈ Icc (0 : ℝ) 1) →
    (∀ A : Set (E n), IsCompact A → Disjoint A s.carrier →
      ∀ᶠ m in atTop, EqOn (χ m) (fun _ => 1) A) →
    (∀ m, RegionIntegrable (fun x : Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k =>
      χ m (Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension a x) *
        Specs.D04.C15.CellsChainsAndIntegrals.Model.cellCoefficient a omega x)) ∧
    Tendsto (fun m => regionIntegral
      (fun x : Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k =>
        χ m (Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension a x) *
          Specs.D04.C15.CellsChainsAndIntegrals.Model.cellCoefficient a omega x))
      atTop (𝓝 (Specs.D04.C15.CellsChainsAndIntegrals.Model.cellIntegral a omega))

/-- The derivative basis of a single global interior chart induces an actual
continuous manifold orientation, with positive sign in that chart. Continuity
in every other chart is proved from the transition determinant. -/
def global_chart_orientationType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart r k n M), ManifoldRegularity r → 0 < k → k ≤ n →
    c.half = false → M ⊆ c.ambient →
    ∃ o : PositiveManifoldOrientation r k M,
      ∀ u (hu : u ∈ c.source), chartSign o.atPoint c u hu = 1

/-- Parameter orientation on the embedded open interior of a regular cell.
No orientation or smooth manifold structure is imposed at its corners. -/
def cell_interior_orientationType : Prop :=
  ∀ {r : ℕ∞} {k n : ℕ} {O : Set (E n)}
    (a : Specs.D04.C15.CellsChainsAndIntegrals.Model.Cell r k O), 0 < k → k ≤ n →
    InjOn (Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension a)
      (Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k) →
    (∀ x ∈ interior (Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k),
      Function.Injective (fderiv ℝ (Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension a) x)) →
    let f := Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension a
    let S := Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k
    ∃ (c : EmbeddedChart 1 k n (f '' interior S))
      (o : PositiveManifoldOrientation 1 k (f '' interior S)),
      c.half = false ∧ c.source = interior S ∧ c.toFun = f ∧
      c.invFun = Function.invFunOn f S ∧ c.ambient = (f '' frontier S)ᶜ ∧
      ∀ u (hu : u ∈ c.source), chartSign o.atPoint c u hu = 1

/-- The seam display of the cell faces is exactly the image of the parameter
cube frontier. This supplies the source's face presentation at corners. -/
def cell_frontier_seamsType : Prop :=
  ∀ {r : ℕ∞} {k n : ℕ} {O : Set (E n)}
    (a : Specs.D04.C15.CellsChainsAndIntegrals.Model.Cell r (k+1) O),
    ∃ s : AmbientSeams (k+1) n,
      s.carrier = Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension a ''
        frontier (Specs.D04.C15.CellsChainsAndIntegrals.Model.cube (k+1))

/-- Actual cell/interior-manifold comparison after deleting an open neighborhood
of the parameter faces. Compact support and existence of chart partitions are
conclusions. Every allowed partition gives the original weighted cube value. -/
def cell_interior_integralType : Prop :=
  ∀ {r : ℕ∞} {k n : ℕ} {O : Set (E n)}
    (a : Specs.D04.C15.CellsChainsAndIntegrals.Model.Cell r k O),
    let f := Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension a
    let S := Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k
    let M := f '' interior S
    ∀ (c : EmbeddedChart 1 k n M) (o : PositiveManifoldOrientation 1 k M),
    c.source = interior S → c.toFun = f →
    (∀ u (hu : u ∈ c.source), chartSign o.atPoint c u hu = 1) →
    ∀ omega : FormField n k, IsCrForm (some 0) O omega →
    ∀ (w : E n → ℝ) (V : Set (E n)), Continuous w → IsOpen V →
    f '' frontier S ⊆ V → EqOn w (fun _ => 0) V →
    let eta : TangentTopField 1 k M := fun x => w x • ambientRestriction omega x
    IsCompact (topSupport eta) ∧ Nonempty (SignedChartPartition o (topSupport eta)) ∧
      ∀ P : SignedChartPartition o (topSupport eta),
        orientedIntegral eta P = regionIntegral (fun x : S =>
          w (f x) * Specs.D04.C15.CellsChainsAndIntegrals.Model.cellCoefficient a omega x)

/-- A regular cell's usual integral is the limit of actual compactly supported
manifold integrals on its oriented open interior. The same smooth sequence
removes any prescribed ambient seams and every displayed face, and all choices
of signed chart partitions give the asserted limit. -/
def cell_interior_manifold_limitType : Prop :=
  ∀ {r : ℕ∞} {d n : ℕ} {O : Set (E n)}
    (a : Specs.D04.C15.CellsChainsAndIntegrals.Model.Cell r (d+1) O), d+1 ≤ n →
    InjOn (Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension a)
      (Specs.D04.C15.CellsChainsAndIntegrals.Model.cube (d+1)) →
    (∀ x ∈ Specs.D04.C15.CellsChainsAndIntegrals.Model.cube (d+1),
      Function.Injective (fderiv ℝ (Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension a) x)) →
    ∀ s : AmbientSeams (d+1) n, ∀ omega : FormField n (d+1), IsCrForm (some 0) O omega →
    let f := Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension a
    let S := Specs.D04.C15.CellsChainsAndIntegrals.Model.cube (d+1)
    let M := f '' interior S
    ∃ (c : EmbeddedChart 1 (d+1) n M) (o : PositiveManifoldOrientation 1 (d+1) M)
      (χ : ℕ → E n → ℝ),
      c.half = false ∧ c.source = interior S ∧ c.toFun = f ∧
      (∀ u (hu : u ∈ c.source), chartSign o.atPoint c u hu = 1) ∧
      (∀ m, ContDiff ℝ ∞ (χ m)) ∧ (∀ m x, χ m x ∈ Icc (0 : ℝ) 1) ∧
      (∀ m, ∃ V : Set (E n), IsOpen V ∧ s.carrier ∪ f '' frontier S ⊆ V ∧
        EqOn (χ m) (fun _ => 0) V) ∧
      (∀ A : Set (E n), IsCompact A → Disjoint A (s.carrier ∪ f '' frontier S) →
        ∀ᶠ m in atTop, EqOn (χ m) (fun _ => 1) A) ∧
      (∀ m, IsCompact (topSupport (fun x : M => χ m x • ambientRestriction (r := 1) omega x)) ∧
        Nonempty (SignedChartPartition o
          (topSupport (fun x : M => χ m x • ambientRestriction (r := 1) omega x)))) ∧
      ∀ Q : ∀ m, SignedChartPartition o
          (topSupport (fun x : M => χ m x • ambientRestriction (r := 1) omega x)),
        Tendsto (fun m => orientedIntegral
          (fun x : M => χ m x • ambientRestriction (r := 1) omega x) (Q m))
          atTop (𝓝 (Specs.D04.C15.CellsChainsAndIntegrals.Model.cellIntegral a omega))


namespace Model
/-- A finite compact geometric assembly with oriented regular parts. The
removed parts and pairwise intersections are contained in displayed seams.
There are no integral values or integral identities among the data. -/
structure RegularDecomposition (k n : ℕ) where
  count : ℕ
  piece : Fin count → Set (E n)
  compact : ∀ i, IsCompact (piece i)
  regular : Fin count → Set (E n)
  subset : ∀ i, regular i ⊆ piece i
  orientation : ∀ i, PositiveManifoldOrientation 1 k (regular i)
  seams : AmbientSeams k n
  singular : ∀ i, piece i \ regular i ⊆ seams.carrier
  overlap : ∀ i j, i ≠ j → piece i ∩ piece j ⊆ seams.carrier

def RegularDecomposition.carrier {k n : ℕ} (D : RegularDecomposition k n) : Set (E n) :=
  ⋃ i, D.piece i

def CompatibleRegularDecompositions {k n : ℕ}
    (D F : RegularDecomposition k n) : Prop :=
  D.carrier = F.carrier ∧
  ∀ x, x ∉ D.seams.carrier ∪ F.seams.carrier →
    ∀ i j (hi : x ∈ D.regular i) (hj : x ∈ F.regular j),
    ∀ h : tangentSpace 1 k (D.regular i) x = tangentSpace 1 k (F.regular j) x,
      transportOrientation h ((D.orientation i).atPoint x hi) =
        (F.orientation j).atPoint x hj
end Model

abbrev RegularDecompositionType := ℕ → ℕ → Type
def RegularDecompositionValue : RegularDecompositionType := Model.RegularDecomposition
abbrev CompatibleRegularDecompositionsType := {k n : ℕ} →
  RegularDecomposition k n → RegularDecomposition k n → Prop
def CompatibleRegularDecompositionsValue : CompatibleRegularDecompositionsType :=
  @Model.CompatibleRegularDecompositions

/-- The regular parts need not be compact. Vanishing near the seams supplies
compact support, and equality is proved for arbitrary independent partitions. -/
def regular_decomposition_away_seamsType : Prop :=
  ∀ {k n : ℕ} (D F : RegularDecomposition k n), CompatibleRegularDecompositions D F →
  ∀ {O : Set (E n)}, D.carrier ⊆ O →
  ∀ omega : FormField n k, IsCrForm (some 0) O omega →
  ∀ V : Set (E n), IsOpen V → D.seams.carrier ∪ F.seams.carrier ⊆ V →
  EqOn omega (fun _ => 0) V →
  (∀ i, IsCompact (topSupport (ambientRestriction (r := 1) (M := D.regular i) omega))) ∧
  (∀ j, IsCompact (topSupport (ambientRestriction (r := 1) (M := F.regular j) omega))) ∧
  ∀ (P : ∀ i, SignedChartPartition (D.orientation i)
      (topSupport (ambientRestriction (r := 1) (M := D.regular i) omega)))
    (Q : ∀ j, SignedChartPartition (F.orientation j)
      (topSupport (ambientRestriction (r := 1) (M := F.regular j) omega))),
    (∑ i, orientedIntegral (ambientRestriction (r := 1) omega) (P i)) =
      ∑ j, orientedIntegral (ambientRestriction (r := 1) omega) (Q j)

namespace Model
/-- A geometric description of a regular piece by either one original regular
cell, with its parameter orientation, or one compact oriented manifold. Chart
and orientation data contain no analytic equality and their existence for every
regular cell is proved separately. -/
inductive PieceRepresentation {k n : ℕ} (K M : Set (E n))
    (o : PositiveManifoldOrientation 1 k M) (O : Set (E n)) : Type
  | manifold (same : K = M) (inside : K ⊆ O)
  | cell (a : Specs.D04.C15.CellsChainsAndIntegrals.Model.Cell 1 k O)
      (injective : InjOn (Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension a)
        (Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k))
      (rank : ∀ x ∈ Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k,
        Function.Injective (fderiv ℝ (Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension a) x))
      (carrier_eq : K = Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension a ''
        Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k)
      (regular_eq : M = Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension a ''
        interior (Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k))
      (chart : EmbeddedChart 1 k n M)
      (source_eq : chart.source = interior (Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k))
      (map_eq : chart.toFun = Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension a)
      (positive : ∀ u (hu : u ∈ chart.source), chartSign o.atPoint chart u hu = 1)

/-- This relation specifies the actual original value in either case. It
contains no comparison with another display or with a geometric union. -/
def PieceRepresentation.HasIntegral {k n : ℕ} {K M O : Set (E n)}
    {o : PositiveManifoldOrientation 1 k M} (R : PieceRepresentation K M o O)
    (omega : FormField n k) (v : ℝ) : Prop :=
  match R with
  | .manifold _ _ => ∀ P : SignedChartPartition o
      (topSupport (ambientRestriction (r := 1) (M := M) omega)),
      orientedIntegral (ambientRestriction (r := 1) omega) P = v
  | .cell a _ _ _ _ _ _ _ _ =>
      Specs.D04.C15.CellsChainsAndIntegrals.Model.cellIntegral a omega = v

structure GeometricDecomposition (k n : ℕ) (O : Set (E n)) extends RegularDecomposition k n where
  representation : ∀ i, PieceRepresentation (piece i) (regular i) (orientation i) O

def HasGeometricUnionIntegral {k n : ℕ} {O : Set (E n)}
    (D : GeometricDecomposition k n O) (omega : FormField n k) (v : ℝ) : Prop :=
  ∀ F : GeometricDecomposition k n O,
    CompatibleRegularDecompositions D.toRegularDecomposition F.toRegularDecomposition →
    ∀ values : Fin F.count → ℝ,
      (∀ i, (F.representation i).HasIntegral omega (values i)) → (∑ i, values i) = v

def geometricUnionIntegral {k n : ℕ} {O : Set (E n)}
    (D : GeometricDecomposition k n O) (omega : FormField n k) : ℝ :=
  if h : ∃ v, HasGeometricUnionIntegral D omega v then Classical.choose h else 0
end Model

abbrev PieceRepresentationType := {k n : ℕ} → (K M : Set (E n)) →
  PositiveManifoldOrientation 1 k M → Set (E n) → Type
def PieceRepresentationValue : PieceRepresentationType := @Model.PieceRepresentation
abbrev PieceHasIntegralType := {k n : ℕ} → {K M O : Set (E n)} →
  {o : PositiveManifoldOrientation 1 k M} → PieceRepresentation K M o O → FormField n k → ℝ → Prop
def PieceHasIntegralValue : PieceHasIntegralType := @Model.PieceRepresentation.HasIntegral
abbrev GeometricDecompositionType := (k n : ℕ) → Set (E n) → Type
def GeometricDecompositionValue : GeometricDecompositionType := Model.GeometricDecomposition
abbrev HasGeometricUnionIntegralType := {k n : ℕ} → {O : Set (E n)} →
  GeometricDecomposition k n O → FormField n k → ℝ → Prop
def HasGeometricUnionIntegralValue : HasGeometricUnionIntegralType := @Model.HasGeometricUnionIntegral
abbrev geometricUnionIntegralType := {k n : ℕ} → {O : Set (E n)} →
  GeometricDecomposition k n O → FormField n k → ℝ
def geometricUnionIntegralValue : geometricUnionIntegralType := @Model.geometricUnionIntegral

/-- Both branches retain the original cell or manifold values. -/
def geometric_piece_integral_existsType : Prop :=
  ∀ {k n : ℕ} {O : Set (E n)} (D : GeometricDecomposition k n O),
  ∀ omega : FormField n k, IsCrForm (some 0) O omega →
  ∀ i, ∃ v, (D.representation i).HasIntegral omega v

/-- Comparison allows arbitrary mixtures of regular cells and compact manifold
pieces. All chart, parameterization and localization choices may differ. -/
def geometric_decomposition_independentType : Prop :=
  ∀ {k n : ℕ} {O : Set (E n)} (D F : GeometricDecomposition k n O),
    CompatibleRegularDecompositions D.toRegularDecomposition F.toRegularDecomposition →
  ∀ omega : FormField n k, IsCrForm (some 0) O omega →
  ∀ (a : Fin D.count → ℝ) (b : Fin F.count → ℝ),
    (∀ i, (D.representation i).HasIntegral omega (a i)) →
    (∀ j, (F.representation j).HasIntegral omega (b j)) → (∑ i, a i) = ∑ j, b j

def geometric_union_integral_existsType : Prop :=
  ∀ {k n : ℕ} {O : Set (E n)} (D : GeometricDecomposition k n O),
  ∀ omega : FormField n k, IsCrForm (some 0) O omega →
    ∃! v, HasGeometricUnionIntegral D omega v

def geometric_union_integral_eq_sumType : Prop :=
  ∀ {k n : ℕ} {O : Set (E n)} (D F : GeometricDecomposition k n O),
    CompatibleRegularDecompositions D.toRegularDecomposition F.toRegularDecomposition →
  ∀ omega : FormField n k, IsCrForm (some 0) O omega →
  ∀ a : Fin F.count → ℝ, (∀ i, (F.representation i).HasIntegral omega (a i)) →
    geometricUnionIntegral D omega = ∑ i, a i

def geometric_union_integral_independentType : Prop :=
  ∀ {k n : ℕ} {O : Set (E n)} (D F : GeometricDecomposition k n O),
    CompatibleRegularDecompositions D.toRegularDecomposition F.toRegularDecomposition →
  ∀ omega : FormField n k, IsCrForm (some 0) O omega →
    geometricUnionIntegral D omega = geometricUnionIntegral F omega

/-- Finitely many compact seam carriers with countable geometric coverings
have one such presentation, with their exact union as carrier. -/
def finite_seamsType : Prop :=
  ∀ {k n N : ℕ} (s : Fin N → AmbientSeams k n),
    ∃ t : AmbientSeams k n, t.carrier = ⋃ i, (s i).carrier

/-- Every finite assembly of original regular cells has a geometric display.
Its only exceptional points added to the prescribed overlaps are its actual
faces, and its orientations are the parameter-induced orientations. -/
def cell_family_displayType : Prop :=
  ∀ {k n N : ℕ} {O : Set (E n)}, 0 < k → k ≤ n →
  ∀ a : Fin N → Specs.D04.C15.CellsChainsAndIntegrals.Model.Cell 1 k O,
    (∀ i, InjOn (Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension (a i))
      (Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k)) →
    (∀ i, ∀ x ∈ Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k,
      Function.Injective (fderiv ℝ (Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension (a i)) x)) →
  ∀ s : AmbientSeams k n,
    (∀ i j, i ≠ j →
      (Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension (a i) ''
        Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k) ∩
      (Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension (a j) ''
        Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k) ⊆ s.carrier) →
  ∃ D : GeometricDecomposition k n O, ∃ e : Fin D.count ≃ Fin N,
    D.carrier = ⋃ i, Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension (a i) ''
      Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k ∧
    D.seams.carrier = s.carrier ∪ ⋃ i,
      Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension (a i) ''
        frontier (Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k) ∧
    (∀ i, D.piece i = Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension (a (e i)) ''
        Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k ∧
      D.regular i = Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension (a (e i)) ''
        interior (Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k)) ∧
    (∀ i, ∃ c : EmbeddedChart 1 k n (D.regular i),
      c.source = interior (Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k) ∧
      c.toFun = Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension (a (e i)) ∧
      ∀ u (hu : u ∈ c.source), chartSign (D.orientation i).atPoint c u hu = 1) ∧
    ∀ omega : FormField n k, IsCrForm (some 0) O omega →
      geometricUnionIntegral D omega =
        ∑ i, Specs.D04.C15.CellsChainsAndIntegrals.Model.cellIntegral (a i) omega

namespace Model
/-- Compact-manifold assemblies are genuine instances of the same display
space which also contains cell assemblies and mixtures. -/
def manifoldGeometricDecomposition {k n : ℕ} {O : Set (E n)}
    (D : CompactManifoldDecomposition k n) (hDO : D.carrier ⊆ O) :
    GeometricDecomposition k n O where
  count := D.count
  piece := D.piece
  compact := D.compact
  regular := D.piece
  subset := fun _ => Subset.rfl
  orientation := D.orientation
  seams := D.seams
  singular := fun _ _ hx => (hx.2 hx.1).elim
  overlap := D.overlap
  representation := fun i => .manifold rfl (fun x hx => hDO (mem_iUnion.mpr ⟨i,hx⟩))
end Model

abbrev manifoldGeometricDecompositionType := {k n : ℕ} → {O : Set (E n)} →
  (D : CompactManifoldDecomposition k n) → D.carrier ⊆ O → GeometricDecomposition k n O
def manifoldGeometricDecompositionValue : manifoldGeometricDecompositionType :=
  @Model.manifoldGeometricDecomposition

def geometric_union_integral_manifoldType : Prop :=
  ∀ {k n : ℕ} {O : Set (E n)} (D : CompactManifoldDecomposition k n)
    (hDO : D.carrier ⊆ O), ∀ omega : FormField n k, IsCrForm (some 0) O omega →
    geometricUnionIntegral (manifoldGeometricDecomposition D hDO) omega = compactUnionIntegral D omega


abbrev CompactSeamType := ℕ → ℕ → Type
def CompactSeamValue : CompactSeamType := Model.CompactSeam

/-- Arbitrary parameter subsets with separate local C¹ extensions admit a
countable compact-image cover; their domains need not be compact. -/
def local_parameter_compact_coverType : Prop :=
  ∀ {d k n : ℕ}, d < k → ∀ (S : Set (E d)) (f : E d → E n),
  (∀ x ∈ S, ∃ (U : Set (E d)) (g : E d → E n),
    U ∈ nhds x ∧ ContDiffAt ℝ 1 g x ∧ EqOn g f (S ∩ U)) →
  ∃ P : Set (Model.CompactSeam k n), P.Countable ∧
    f '' S ⊆ ⋃ p : P, p.val.map '' p.val.parameter

/-- Compact exceptional sets contained in any countable family of local-C¹
parameter images have exact admissible carriers. -/
def parameter_seamsType : Prop :=
  ∀ {k n : ℕ} {ι : Type} [Countable ι]
    (d : ι → ℕ), (∀ i, d i < k) → ∀ (S : ∀ i, Set (E (d i)))
    (f : ∀ i, E (d i) → E n),
  (∀ i x, x ∈ S i → ∃ (U : Set (E (d i))) (g : E (d i) → E n),
    U ∈ nhds x ∧ ContDiffAt ℝ 1 g x ∧ EqOn g (f i) (S i ∩ U)) →
  ∀ Z : Set (E n), IsCompact Z → (Z ⊆ ⋃ i, f i '' S i) →
    ∃ s : AmbientSeams k n, s.carrier = Z

/-- Includes noncompact manifolds and half-space charts. -/
def embedded_compact_coverType : Prop :=
  ∀ {d k n : ℕ}, d < k → ∀ M : Set (E n), IsEmbeddedManifold 1 d M →
    ∃ P : Set (Model.CompactSeam k n), P.Countable ∧
      M ⊆ ⋃ p : P, p.val.map '' p.val.parameter

def embedded_seamsType : Prop :=
  ∀ {k n : ℕ} {ι : Type} [Countable ι]
    (d : ι → ℕ), (∀ i, d i < k) → ∀ M : ι → Set (E n),
  (∀ i, IsEmbeddedManifold 1 (d i) (M i)) →
  ∀ Z : Set (E n), IsCompact Z → (Z ⊆ ⋃ i, M i) →
    ∃ s : AmbientSeams k n, s.carrier = Z

def finite_overlap_parameter_seamsType : Prop :=
  ∀ {k n : ℕ} {ι κ : Type} [Fintype ι] [Countable κ]
    (A : ι → Set (E n)) (hA : ∀ i, IsCompact (A i))
    (d : κ → ℕ) (hd : ∀ l, d l < k) (S : ∀ l, Set (E (d l)))
    (f : ∀ l, E (d l) → E n)
    (hf : ∀ l x, x ∈ S l → ∃ (U : Set (E (d l))) (g : E (d l) → E n),
      U ∈ 𝓝 x ∧ ContDiffAt ℝ 1 g x ∧ EqOn g (f l) (S l ∩ U))
    (hover : ∀ i j, i ≠ j → A i ∩ A j ⊆ ⋃ l, f l '' S l),
  ∃ s : AmbientSeams k n,
      s.carrier = (⋃ i, ⋃ j : {j : ι // j ≠ i}, A i ∩ A j.val) ∧
      ∀ i j, i ≠ j → A i ∩ A j ⊆ s.carrier

def finite_overlap_embedded_seamsType : Prop :=
  ∀ {k n : ℕ} {ι κ : Type} [Fintype ι] [Countable κ]
    (A : ι → Set (E n)) (hA : ∀ i, IsCompact (A i))
    (d : κ → ℕ) (hd : ∀ l, d l < k) (M : κ → Set (E n))
    (hM : ∀ l, IsEmbeddedManifold 1 (d l) (M l))
    (hover : ∀ i j, i ≠ j → A i ∩ A j ⊆ ⋃ l, M l),
  ∃ s : AmbientSeams k n,
      s.carrier = (⋃ i, ⋃ j : {j : ι // j ≠ i}, A i ∩ A j.val) ∧
      ∀ i j, i ≠ j → A i ∩ A j ⊆ s.carrier

def cell_family_from_lower_parametersType : Prop :=
  ∀ {k n N : ℕ} {O : Set (E n)}
    (hk : 0 < k) (hkn : k ≤ n) (a : Fin N → Specs.D04.C15.CellsChainsAndIntegrals.Model.Cell 1 k O)
    (hi : ∀ i, InjOn (Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension (a i)) (Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k))
    (hr : ∀ i, ∀ x ∈ Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k, Function.Injective (fderiv ℝ (Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension (a i)) x))
    {κ : Type} [Countable κ] (d : κ → ℕ) (hd : ∀ l, d l < k)
    (S : ∀ l, Set (E (d l))) (f : ∀ l, E (d l) → E n)
    (hf : ∀ l x, x ∈ S l → ∃ (U : Set (E (d l))) (g : E (d l) → E n),
      U ∈ 𝓝 x ∧ ContDiffAt ℝ 1 g x ∧ EqOn g (f l) (S l ∩ U))
    (hover : ∀ i j, i ≠ j →
      (Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension (a i) '' Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k) ∩
      (Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension (a j) '' Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k) ⊆ ⋃ l, f l '' S l),
  ∃ D : GeometricDecomposition k n O,
      D.carrier = ⋃ i, Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension (a i) '' Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k ∧
      ∀ omega : FormField n k, IsCrForm (some 0) O omega →
        geometricUnionIntegral D omega = ∑ i, Specs.D04.C15.CellsChainsAndIntegrals.Model.cellIntegral (a i) omega

def cell_family_from_lower_manifoldsType : Prop :=
  ∀ {k n N : ℕ} {O : Set (E n)}
    (hk : 0 < k) (hkn : k ≤ n) (a : Fin N → Specs.D04.C15.CellsChainsAndIntegrals.Model.Cell 1 k O)
    (hi : ∀ i, InjOn (Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension (a i)) (Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k))
    (hr : ∀ i, ∀ x ∈ Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k, Function.Injective (fderiv ℝ (Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension (a i)) x))
    {κ : Type} [Countable κ] (d : κ → ℕ) (hd : ∀ l, d l < k)
    (M : κ → Set (E n)) (hM : ∀ l, IsEmbeddedManifold 1 (d l) (M l))
    (hover : ∀ i j, i ≠ j →
      (Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension (a i) '' Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k) ∩
      (Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension (a j) '' Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k) ⊆ ⋃ l, M l),
  ∃ D : GeometricDecomposition k n O,
      D.carrier = ⋃ i, Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension (a i) '' Specs.D04.C15.CellsChainsAndIntegrals.Model.cube k ∧
      ∀ omega : FormField n k, IsCrForm (some 0) O omega →
        geometricUnionIntegral D omega = ∑ i, Specs.D04.C15.CellsChainsAndIntegrals.Model.cellIntegral (a i) omega

def manifold_family_from_lower_parametersType : Prop :=
  ∀ {k n N : ℕ} {O : Set (E n)}
    (A : Fin N → Set (E n)) (hA : ∀ i, IsCompact (A i))
    (o : ∀ i, PositiveManifoldOrientation 1 k (A i)) (hAO : ∀ i, A i ⊆ O)
    {κ : Type} [Countable κ] (d : κ → ℕ) (hd : ∀ l, d l < k)
    (S : ∀ l, Set (E (d l))) (f : ∀ l, E (d l) → E n)
    (hf : ∀ l x, x ∈ S l → ∃ (U : Set (E (d l))) (g : E (d l) → E n),
      U ∈ 𝓝 x ∧ ContDiffAt ℝ 1 g x ∧ EqOn g (f l) (S l ∩ U))
    (hover : ∀ i j, i ≠ j → A i ∩ A j ⊆ ⋃ l, f l '' S l),
  ∃ D : GeometricDecomposition k n O,
      D.carrier = ⋃ i, A i ∧
      ∀ (omega : FormField n k) (ho : IsCrForm (some 0) O omega)
        (Q : ∀ i, SignedChartPartition (o i)
          (topSupport (Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.ambientRestriction (r := 1) (M := A i) omega))),
        geometricUnionIntegral D omega =
          ∑ i, orientedIntegral (Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.ambientRestriction (r := 1) (M := A i) omega) (Q i)

def manifold_family_from_lower_manifoldsType : Prop :=
  ∀ {k n N : ℕ} {O : Set (E n)}
    (A : Fin N → Set (E n)) (hA : ∀ i, IsCompact (A i))
    (o : ∀ i, PositiveManifoldOrientation 1 k (A i)) (hAO : ∀ i, A i ⊆ O)
    {κ : Type} [Countable κ] (d : κ → ℕ) (hd : ∀ l, d l < k)
    (M : κ → Set (E n)) (hM : ∀ l, IsEmbeddedManifold 1 (d l) (M l))
    (hover : ∀ i j, i ≠ j → A i ∩ A j ⊆ ⋃ l, M l),
  ∃ D : GeometricDecomposition k n O,
      D.carrier = ⋃ i, A i ∧
      ∀ (omega : FormField n k) (ho : IsCrForm (some 0) O omega)
        (Q : ∀ i, SignedChartPartition (o i)
          (topSupport (Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.ambientRestriction (r := 1) (M := A i) omega))),
        geometricUnionIntegral D omega =
          ∑ i, orientedIntegral (Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.ambientRestriction (r := 1) (M := A i) omega) (Q i)

end Specs.D04.C15.FiniteGeometricUnionIntegral
