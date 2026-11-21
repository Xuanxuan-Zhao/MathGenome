import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.GeneralizedStokes
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.FiniteGeometricPatchIntegrals

/-! The manifold branch of d04:15:piecewise: finite ambient localization,
regular boundary decomposition, signed-point boundaries and integer assembly.
Decomposition identities and cancellation of integrals are conclusions. -/
noncomputable section
open Set Function
open scoped ContDiff BigOperators Classical
namespace Specs.D04.C15.FiniteManifoldBoundaryAssembly
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.ExteriorDerivative.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.MetricTopFormsAndDensities.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model
open Specs.D04.C15.GeneralizedStokes.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model
namespace Model

/-- Geometric summands, without assumed integral or cancellation identities. -/
structure CompactManifold (d n : ℕ) (O : Set (E n)) where
  carrier : Set (E n)
  orientation : PositiveManifoldOrientation 1 (d+1) carrier
  compact : IsCompact carrier
  subset_domain : carrier ⊆ O

/-- A regular displayed piece uses canonical Jordan patch integrals and is
locally a signed embedded chart of the manifold. Only geometric values on the
closed parameter region are fixed; its separate ambient extension is arbitrary.
A display separately controls repeated points by its lower-dimensional seams. -/
def RegularPiece {k n} {O M : Set (E n)}
    (o : PositiveManifoldOrientation 1 k M) (P : Patch k O) (s : PointSign) : Prop :=
  ∀ u ∈ closure P.region,
    ∃ (U : Set (E k)) (c : EmbeddedChart 1 k n M),
      IsOpen U ∧ u ∈ U ∧ closure P.region ∩ U ⊆ c.source ∧
      EqOn P.map c.toFun (closure P.region ∩ U) ∧
      ∀ v : c.source, chartSign o.atPoint c v v.property = s.val

end Model
open Model
abbrev CompactManifoldType := (d n : ℕ) → Set (E n) → Type
def CompactManifoldValue : CompactManifoldType := Model.CompactManifold

abbrev RegularPieceType := {k n : ℕ} → {O M : Set (E n)} →
  PositiveManifoldOrientation 1 k M → Patch k O → PointSign → Prop
def RegularPieceValue : RegularPieceType := @Model.RegularPiece

/-- Localization is proved for the actual whole-manifold integral, including
zero-dimensional signed evaluation. The partition need only cover the support. -/
def manifold_localizationType : Prop :=
  ∀ {r : ℕ∞ω} {k n} {M : Set (E n)} (hM : IsEmbeddedManifold r k M)
    (o : ManifoldOrientation r k M) (eta : TangentTopField r k M),
    ContinuousTopField eta → ∀ {I : ℝ}, HasManifoldIntegral r k o eta I →
    ∀ {m} (w : Fin m → E n → ℝ), (∀ i, Continuous (w i)) →
    (∀ x : M, eta x ≠ 0 → ∑ i, w i x = 1) →
    ∃ J : Fin m → ℝ,
      (∀ i, HasManifoldIntegral r k o (fun x => w i x • eta x) (J i)) ∧ I = ∑ i, J i

/-- Choose one smooth ambient partition for all boundaries, then derive its
compatibility with every whole-boundary integral and every bulk Stokes value. -/
def common_boundary_localizationType : Prop :=
  ∀ {d n q} {O : Set (E n)} (M : Fin q → CompactManifold d n O)
    (omega : FormField n d), IsCrForm (some 1) O omega →
    ∀ {ι : Type} (U : ι → Set (E n)), (∀ a, IsOpen (U a)) →
    (⋃ j, intrinsicBoundary 1 (d+1) (M j).carrier) ⊆ ⋃ a, U a →
    ∃ (m : ℕ) (a : Fin m → ι)
      (A : AmbientPartition (⋃ j, intrinsicBoundary 1 (d+1) (M j).carrier) m)
      (bO : (j : Fin q) → ManifoldOrientation 1 d (intrinsicBoundary 1 (d+1) (M j).carrier))
      (I : Fin q → ℝ) (J : Fin q → Fin m → ℝ),
      (∀ i, tsupport (A.weight i) ⊆ U (a i)) ∧
      (∀ j, OutwardFirst d (M j).orientation (bO j)) ∧
      (∀ j, HasPositiveIntegral (M j).orientation
        (tangentRestriction 1 (d+1) (M j).carrier (exteriorDerivative omega)) (I j)) ∧
      (∀ j, HasManifoldIntegral 1 d (bO j)
        (tangentRestriction 1 d (intrinsicBoundary 1 (d+1) (M j).carrier) omega) (I j)) ∧
      (∀ j i, HasManifoldIntegral 1 d (bO j)
        (fun x => A.weight i x •
          tangentRestriction 1 d (intrinsicBoundary 1 (d+1) (M j).carrier) omega x) (J j i)) ∧
      (∀ j, I j = ∑ i, J j i) ∧
      ∀ multiplicity : Fin q → ℤ,
        ∑ j, multiplicity j • I j = ∑ i, ∑ j, multiplicity j • J j i

/-- One common partition works simultaneously for any finite displayed patch
family and any finite manifold family, with compatibility for their actual
integral values. No Jordan hypothesis is imposed on the ambient union. -/
def common_boundary_patch_localizationType : Prop :=
  ∀ {d n q l} {O : Set (E n)} (M : Fin q → CompactManifold d n O)
    (P : Fin l → Patch d O) (omega : FormField n d), IsCrForm (some 1) O omega →
    ∀ {ι : Type} (U : ι → Set (E n)), (∀ a, IsOpen (U a)) →
    ((⋃ j, intrinsicBoundary 1 (d+1) (M j).carrier) ∪
      (⋃ t, (P t).map '' closure (P t).region)) ⊆ ⋃ a, U a →
    ∃ (m : ℕ) (a : Fin m → ι)
      (A : AmbientPartition
        ((⋃ j, intrinsicBoundary 1 (d+1) (M j).carrier) ∪
          (⋃ t, (P t).map '' closure (P t).region)) m),
      (∀ i, tsupport (A.weight i) ⊆ U (a i)) ∧
      (∀ t, patchIntegral (P t) (fun _ => 1) omega =
        ∑ i, patchIntegral (P t) (A.weight i) omega) ∧
      ∀ j, ∃ (bO : ManifoldOrientation 1 d (intrinsicBoundary 1 (d+1) (M j).carrier))
        (I : ℝ) (J : Fin m → ℝ),
        OutwardFirst d (M j).orientation bO ∧
        HasPositiveIntegral (M j).orientation
          (tangentRestriction 1 (d+1) (M j).carrier (exteriorDerivative omega)) I ∧
        HasManifoldIntegral 1 d bO
          (tangentRestriction 1 d (intrinsicBoundary 1 (d+1) (M j).carrier) omega) I ∧
        (∀ i, HasManifoldIntegral 1 d bO
          (fun x => A.weight i x • tangentRestriction 1 d
            (intrinsicBoundary 1 (d+1) (M j).carrier) omega x) (J i)) ∧ I = ∑ i, J i

/-- Directed cancellation is derived from the actual local parameter
bijection, determinant sign, orientation signs and integer multiplicities. -/
def paired_patch_cancellationType : Prop :=
  ∀ {d n} {O : Set (E n)} (P Q : Patch d O) (delta : ℝ),
    (delta = 1 ∨ delta = -1) →
    ∀ h : LocalReparametrization P.region Q.region delta,
    EqOn P.map (Q.map ∘ h.map) P.region →
    ∀ (s t : ℝ), s * delta = -t → ∀ (a b : ℤ), a = b →
    ∀ omega : FormField n d, IsCrForm (some 0) O omega →
    ∀ w : E n → ℝ, ContinuousOn w O →
      a • (s * patchIntegral P w omega) + b • (t * patchIntegral Q w omega) = 0

/-- The entire k=1 branch. A display enumerates boundary occurrences by
unpaired outer points and paired internal points. The outer patches and signs
are prescribed independently and matched geometrically to those occurrences. -/
def signed_point_boundary_assemblyType : Prop :=
  ∀ {n q} {O : Set (E n)} (M : Fin q → CompactManifold 0 n O)
    (bO : (j : Fin q) → ZeroManifoldOrientation (intrinsicBoundary 1 1 (M j).carrier)),
    (∀ j, OutwardFirst 0 (M j).orientation (bO j)) → ∀ (a : Fin q → ℤ)
    {l p : ℕ}
    (e : (Fin l ⊕ (Fin p × Bool)) ≃ (j : Fin q) × intrinsicBoundary 1 1 (M j).carrier)
    (P : Fin l → Patch 0 O) (s : Fin l → PointSign) (c : Fin l → ℤ),
    (∀ t, (0 : E 0) ∈ (P t).region ∧
      (P t).map 0 = (e (Sum.inl t)).2.val ∧
      s t = bO (e (Sum.inl t)).1 (e (Sum.inl t)).2 ∧ c t = a (e (Sum.inl t)).1) →
    (∀ i, (e (Sum.inr (i,false))).2.val = (e (Sum.inr (i,true))).2.val ∧
      a (e (Sum.inr (i,false))).1 = a (e (Sum.inr (i,true))).1 ∧
      (bO (e (Sum.inr (i,false))).1 (e (Sum.inr (i,false))).2).val =
        -(bO (e (Sum.inr (i,true))).1 (e (Sum.inr (i,true))).2).val) →
    ∀ omega : FormField n 0, IsCrForm (some 1) O omega →
    ∃ I : Fin q → ℝ,
      (∀ j, HasPositiveIntegral (M j).orientation
        (tangentRestriction 1 1 (M j).carrier (exteriorDerivative omega)) (I j)) ∧
      (∀ j, HasManifoldIntegral 1 0 (bO j)
        (tangentRestriction 1 0 (intrinsicBoundary 1 1 (M j).carrier) omega) (I j)) ∧
      ∑ j, a j • I j = ∑ t, c t • (s t).val * patchIntegral (P t) (fun _ => 1) omega

/-- Local geometric bridge for positive-dimensional boundary charts. A Jordan
patch containing the scalar weight's support computes the actual whole-manifold
integral of that weighted field. The hypotheses are about charts, regions and
supports; coefficient integrability and equality of integrals are conclusions. -/
def weighted_chart_patch_integralType : Prop :=
  ∀ {k n} {O M : Set (E n)} (o : PositiveManifoldOrientation 1 k M),
    IsCompact M → M ⊆ O → ∀ (c : EmbeddedChart 1 k n M) (P : Patch k O),
    P.region ⊆ c.source → EqOn P.map c.toFun P.region →
    (∀ u ∈ P.region, fderiv ℝ P.map u =
      Specs.D04.C14.ChartIndependentTangentSpaces.Model.chartDifferential c u) →
    ∀ omega : FormField n k, IsCrForm (some 0) O omega →
    ∀ (w : E n → ℝ), Continuous w → ∀ s : PointSign,
    (∀ u : c.source, chartSign o.atPoint c u u.property = s.val) →
    tsupport (fun x : M => w x) ⊆ Subtype.val ⁻¹' c.ambient →
    (∀ x ∈ tsupport (fun x : M => w x), c.invFun x ∈ P.region) →
    HasPositiveIntegral o (fun x => w x • tangentRestriction 1 k M omega x)
      (s.val * patchIntegral P w omega)

/-- A finite lower-dimensional seam may be omitted from the region covering
the scalar support. Its coefficient contribution is proved to be zero. -/
def weighted_chart_patch_integral_off_seamsType : Prop :=
  ∀ {k n} {O M : Set (E n)} (o : PositiveManifoldOrientation 1 k M),
    IsCompact M → M ⊆ O → ∀ (c : EmbeddedChart 1 k n M) (P : Patch k O),
    P.region ⊆ c.source → EqOn P.map c.toFun P.region →
    (∀ u ∈ P.region, fderiv ℝ P.map u =
      Specs.D04.C14.ChartIndependentTangentSpaces.Model.chartDifferential c u) →
    ∀ seams : Seams k,
    ∀ omega : FormField n k, IsCrForm (some 0) O omega →
    ∀ (w : E n → ℝ), Continuous w → ∀ s : PointSign,
    (∀ u : c.source, chartSign o.atPoint c u u.property = s.val) →
    tsupport (fun x : M => w x) ⊆ Subtype.val ⁻¹' c.ambient →
    (∀ x ∈ tsupport (fun x : M => w x), c.invFun x ∈ P.region ∪ seams.carrier) →
    HasPositiveIntegral o (fun x => w x • tangentRestriction 1 k M omega x)
      (s.val * patchIntegral P w omega)

/-- A finite family of Jordan regions in one chart may cover a localized
support, meeting only along finite lower-dimensional seams. All integral values
are conclusions, and the input patches may have separate C¹ extensions. -/
def weighted_chart_patch_coverType : Prop :=
  ∀ {k n l} {O M : Set (E n)} (o : PositiveManifoldOrientation 1 k M),
    IsCompact M → M ⊆ O → IsOpen O →
    ∀ (c : EmbeddedChart 1 k n M) (P : Fin l → Patch k O),
    (∀ t, closure (P t).region ⊆ c.source) →
    (∀ t, EqOn (P t).map c.toFun (P t).region) →
    ∀ seams : Seams k,
    (∀ i j, i ≠ j → (P i).region ∩ (P j).region ⊆ seams.carrier) →
    ∀ omega : FormField n k, IsCrForm (some 0) O omega →
    ∀ (w : E n → ℝ), Continuous w → ∀ s : PointSign,
    (∀ u : c.source, chartSign o.atPoint c u u.property = s.val) →
    tsupport (fun x : M => w x) ⊆ Subtype.val ⁻¹' c.ambient →
    (∀ x ∈ tsupport (fun x : M => w x), c.invFun x ∈ (⋃ t, (P t).region) ∪ seams.carrier) →
    HasPositiveIntegral o (fun x => w x • tangentRestriction 1 k M omega x)
      (∑ t, s.val * patchIntegral (P t) w omega)

/-- A chart-supported integral computed on independently parametrized pieces.
The regions in the reference chart, their cover off seams, actual local parameter
diffeomorphisms and determinant signs are geometric hypotheses. The signed
identity of actual integrals is a conclusion. -/
def transported_chart_patch_coverType : Prop :=
  ∀ {k n l} {O M : Set (E n)} (o : PositiveManifoldOrientation 1 k M),
    IsCompact M → M ⊆ O → IsOpen O →
    ∀ (c : EmbeddedChart 1 k n M) (S : Fin l → Set (E k)),
    (∀ t, Specs.D04.C06.JordanRegions.Model.Jordan (S t)) →
    (∀ t, closure (S t) ⊆ c.source) →
    ∀ seams : Seams k,
    (∀ i j, i ≠ j → S i ∩ S j ⊆ seams.carrier) →
    ∀ (P : Fin l → Patch k O) (delta : Fin l → ℝ),
    (∀ t, delta t = 1 ∨ delta t = -1) →
    ∀ h : (t : Fin l) → LocalReparametrization (S t) (P t).region (delta t),
    (∀ t, EqOn c.toFun ((P t).map ∘ (h t).map) (S t)) →
    ∀ (s : PointSign) (tSign : Fin l → PointSign),
    (∀ u : c.source, chartSign o.atPoint c u u.property = s.val) →
    (∀ t, s.val * delta t = (tSign t).val) →
    ∀ omega : FormField n k, IsCrForm (some 0) O omega →
    ∀ w : E n → ℝ, Continuous w →
    tsupport (fun x : M => w x) ⊆ Subtype.val ⁻¹' c.ambient →
    (∀ x ∈ tsupport (fun x : M => w x), c.invFun x ∈ (⋃ t, S t) ∪ seams.carrier) →
    HasPositiveIntegral o (fun x => w x • tangentRestriction 1 k M omega x)
      (∑ t, (tSign t).val * patchIntegral (P t) w omega)

/-- Chart transitions restricted to displayed regions supply the canonical
local reparametrization data, including extensions across genuine boundaries.
Only the actual parameter bijection and determinant signs are hypotheses. -/
def chart_region_reparametrizationType : Prop :=
  ∀ {k n} {M : Set (E n)} (c d : EmbeddedChart 1 k n M), k ≤ n →
    ∀ (S T : Set (E k)) (delta : ℝ),
    closure S ⊆ chartOverlap c d → BijOn (chartTransition c d) S T →
    (∀ x ∈ closure S, Real.sign ((fderivWithin ℝ (chartTransition c d)
      (chartOverlap c d) x).det) = delta) →
    ∃ h : LocalReparametrization S T delta, h.map = chartTransition c d

/-- Jordan measurability and closure transport follow from the actual separate
local diffeomorphisms. No regularity of the representative off the closed
region and no unique-derivative condition on the Jordan set are imposed. -/
def local_reparametrization_imageType : Prop :=
  ∀ {k} {S T : Set (E k)} {delta : ℝ},
    Specs.D04.C06.JordanRegions.Model.Jordan S →
    ∀ h : LocalReparametrization S T delta,
      Specs.D04.C06.JordanRegions.Model.Jordan T ∧
      IsCompact (closure T) ∧ closure T = h.map '' closure S

/-- Transport a Jordan region between actual embedded charts. The target
region, its Jordan property, reverse parameter bijection and both determinant
signs are derived from the two chart signs and the original region. -/
def chart_region_transportType : Prop :=
  ∀ {k n} {M : Set (E n)} (o : PositiveManifoldOrientation 1 k M)
    (c d : EmbeddedChart 1 k n M) (s t : PointSign),
    (∀ u : c.source, chartSign o.atPoint c u u.property = s.val) →
    (∀ u : d.source, chartSign o.atPoint d u u.property = t.val) →
    ∀ R : Set (E k), Specs.D04.C06.JordanRegions.Model.Jordan R →
    closure R ⊆ chartOverlap d c →
    ∃ S : Set (E k), S = chartTransition d c '' R ∧
      Specs.D04.C06.JordanRegions.Model.Jordan S ∧
      closure S ⊆ chartOverlap c d ∧
      ∃ h : LocalReparametrization S R (s.val * t.val),
        h.map = chartTransition c d ∧
        EqOn c.toFun (d.toFun ∘ h.map) S ∧ s.val * (s.val * t.val) = t.val

/-- One ambient partition is simultaneously subordinate to signed charts
of every member of a finite compact manifold family. For a member not meeting
a weight, the restriction is zero. An arbitrary ambient open cover is refined
at the same time. All chart and partition choices are conclusions. -/
def simultaneous_chart_localizationType : Prop :=
  ∀ {k n q} (B : Fin q → Set (E n))
    (o : (j : Fin q) → PositiveManifoldOrientation 1 k (B j)),
    (∀ j, IsCompact (B j)) →
    ∀ {ι : Type} (U : ι → Set (E n)), (∀ a, IsOpen (U a)) →
    (⋃ j, B j) ⊆ ⋃ a, U a →
    ∃ (m : ℕ) (a : Fin m → ι) (A : AmbientPartition (⋃ j, B j) m),
      (∀ i, tsupport (A.weight i) ⊆ U (a i)) ∧
      ∀ i j, (∀ x ∈ B j, A.weight i x = 0) ∨
        ∃ (c : EmbeddedChart 1 k n (B j)) (s : PointSign),
          (∀ u : c.source, chartSign (o j).atPoint c u u.property = s.val) ∧
          tsupport (fun x : B j => A.weight i x) ⊆ Subtype.val ⁻¹' c.ambient

/-- A localized manifold integral is computed from independently parametrized
chart patches using only their ambient cover and ambient seam intersections.
The Jordan regions in the reference chart and their parameter diffeomorphisms
are derived, rather than supplied as additional hypotheses. -/
def chart_patches_ambient_coverType : Prop :=
  ∀ {k n l} {O M : Set (E n)} (o : PositiveManifoldOrientation 1 k M),
    IsCompact M → M ⊆ O → IsOpen O →
    ∀ (c : EmbeddedChart 1 k n M) (s : PointSign),
    (∀ u : c.source, chartSign o.atPoint c u u.property = s.val) →
    ∀ (P : Fin l → Patch k O) (d : Fin l → EmbeddedChart 1 k n M)
      (tSign : Fin l → PointSign),
    (∀ t, closure (P t).region ⊆ chartOverlap (d t) c) →
    (∀ t, EqOn (P t).map (d t).toFun (P t).region) →
    (∀ t (u : (d t).source), chartSign o.atPoint (d t) u u.property = (tSign t).val) →
    ∀ seams : Seams k,
    (∀ i j, i ≠ j → ((P i).map '' (P i).region) ∩ ((P j).map '' (P j).region) ⊆
      c.toFun '' (c.source ∩ seams.carrier)) →
    ∀ omega : FormField n k, IsCrForm (some 0) O omega →
    ∀ w : E n → ℝ, Continuous w →
    tsupport (fun x : M => w x) ⊆ Subtype.val ⁻¹' c.ambient →
    (∀ x ∈ tsupport (fun x : M => w x),
      x.val ∈ (⋃ t, (P t).map '' (P t).region) ∪
        c.toFun '' (c.source ∩ seams.carrier)) →
    HasPositiveIntegral o (fun x => w x • tangentRestriction 1 k M omega x)
      (∑ t, (tSign t).val * patchIntegral (P t) w omega)

/-- Refine a displayed Jordan region against the reference chart and the
complement of the scalar support. No Jordan property of that support is used.
Every retained region has compact closure in the actual chart overlap, and
all other pieces miss the support on the manifold. -/
def chart_region_weight_localizationType : Prop :=
  ∀ {k n} {M : Set (E n)} (c d : EmbeddedChart 1 k n M)
    (R : Set (E k)), Specs.D04.C06.JordanRegions.Model.Jordan R →
    closure R ⊆ d.source → ∀ w : E n → ℝ,
    tsupport (fun x : M => w x) ⊆ Subtype.val ⁻¹' c.ambient →
    ∃ (m : ℕ) (S : Fin m → Set (E k)),
      (∀ i, Specs.D04.C06.JordanRegions.Model.Jordan (S i)) ∧
      (∀ i, S i ⊆ R) ∧ Pairwise (Disjoint on S) ∧ R = ⋃ i, S i ∧
      ∀ i, closure (S i) ⊆ chartOverlap d c ∨
        Disjoint (d.toFun '' closure (S i)) (Subtype.val '' tsupport (fun x : M => w x))

/-- Actual ambient lower-dimensional seams lift to canonical parameter seams
when their images lie in the reference chart. Local ambient inverse extensions
prove the required local C¹ regularity of the lift. -/
def chart_seams_liftType : Prop :=
  ∀ {k n} {M : Set (E n)} (c : EmbeddedChart 1 k n M), k ≤ n →
    ∀ Z : Seams n, (∀ i, Z.dim i < k) → Z.carrier ⊆ M ∩ c.ambient →
    ∃ A : Seams k, A.carrier = c.invFun '' Z.carrier

/-- Restrict ambient seam parameters to a closed ambient set, retaining their
actual dimensions, compactness and separate local C¹ representatives. -/
def seams_closed_restrictionType : Prop :=
  ∀ {k n} (Z : Seams n), (∀ i, Z.dim i < k) →
    ∀ H : Set (E n), IsClosed H →
    ∃ A : Seams n, (∀ i, A.dim i < k) ∧ A.carrier = Z.carrier ∩ H

/-- A displayed patch has a finite Jordan refinement into regions contained
in a reference-chart overlap and regions with zero weight. The original
integral is proved equal to the retained sum; no integral certificate is input. -/
def weighted_patch_chart_refinementType : Prop :=
  ∀ {k n} {O M : Set (E n)} (c d : EmbeddedChart 1 k n M) (P : Patch k O),
    closure P.region ⊆ d.source → EqOn P.map d.toFun (closure P.region) →
    ∀ w : E n → ℝ, Continuous w →
    tsupport (fun x : M => w x) ⊆ Subtype.val ⁻¹' c.ambient →
    ∃ (m : ℕ) (S : Fin m → Set (E k))
      (hS : ∀ i, Specs.D04.C06.JordanRegions.Model.Jordan (S i))
      (hSP : ∀ i, S i ⊆ P.region),
      Pairwise (Disjoint on S) ∧ P.region = ⋃ i, S i ∧
      (∀ i, closure (S i) ⊆ chartOverlap d c ∨
        ∀ u ∈ closure (S i), w (P.map u) = 0) ∧
      ∀ omega : FormField n k, IsCrForm (some 0) O omega →
        patchIntegral P w omega = ∑ i,
          if closure (S i) ⊆ chartOverlap d c then
            patchIntegral (restrictPatch P (S i) (hS i) (hSP i)) w omega else 0

/-- A finite display of chart patches computes a chart-supported whole-manifold
integral, even though the original patches need not lie in the reference chart.
Only the finite lower-dimensional ambient seams are ignored. -/
def weighted_chart_displayType : Prop :=
  ∀ {k n l} {O M : Set (E n)} (o : PositiveManifoldOrientation 1 k M),
    IsCompact M → M ⊆ O → IsOpen O →
    ∀ (P : Fin l → Patch k O) (d : Fin l → EmbeddedChart 1 k n M)
      (s : Fin l → PointSign),
    (∀ t, closure (P t).region ⊆ (d t).source) →
    (∀ t, EqOn (P t).map (d t).toFun (closure (P t).region)) →
    (∀ t (u : (d t).source), chartSign o.atPoint (d t) u u.property = (s t).val) →
    ∀ Z : Seams n, (∀ i, Z.dim i < k) →
    (∀ i j, i ≠ j → ((P i).map '' (P i).region) ∩ ((P j).map '' (P j).region) ⊆ Z.carrier) →
    M ⊆ (⋃ t, (P t).map '' (P t).region) ∪ Z.carrier →
    ∀ (c : EmbeddedChart 1 k n M) (cs : PointSign),
    (∀ u : c.source, chartSign o.atPoint c u u.property = cs.val) →
    ∀ omega : FormField n k, IsCrForm (some 0) O omega →
    ∀ w : E n → ℝ, Continuous w →
    tsupport (fun x : M => w x) ⊆ Subtype.val ⁻¹' c.ambient →
    HasPositiveIntegral o (fun x => w x • tangentRestriction 1 k M omega x)
      (∑ t, (s t).val * patchIntegral (P t) w omega)

/-- An arbitrary finite chart-patch decomposition of a compact oriented
manifold computes its actual integral. Charts may overlap and the manifold may
be disconnected. Intersections and uncovered points lie in displayed seams. -/
def chart_display_integralType : Prop :=
  ∀ {k n l} {O M : Set (E n)} (o : PositiveManifoldOrientation 1 k M),
    IsCompact M → M ⊆ O →
    ∀ (P : Fin l → Patch k O) (d : Fin l → EmbeddedChart 1 k n M)
      (s : Fin l → PointSign),
    (∀ t, closure (P t).region ⊆ (d t).source) →
    (∀ t, EqOn (P t).map (d t).toFun (closure (P t).region)) →
    (∀ t (u : (d t).source), chartSign o.atPoint (d t) u u.property = (s t).val) →
    ∀ Z : Seams n, (∀ i, Z.dim i < k) →
    (∀ i j, i ≠ j → ((P i).map '' (P i).region) ∩ ((P j).map '' (P j).region) ⊆ Z.carrier) →
    M ⊆ (⋃ t, (P t).map '' (P t).region) ∪ Z.carrier →
    ∀ omega : FormField n k, IsCrForm (some 0) O omega →
    HasPositiveIntegral o (tangentRestriction 1 k M omega)
      (∑ t, (s t).val * patchIntegral (P t) (fun _ => 1) omega)


/-- The boundary decomposition theorem accepts locally charted regular pieces,
not a choice of one chart per original piece or any integral certificate. -/
def regular_display_integralType : Prop :=
  ∀ {k n l} {O M : Set (E n)} (o : PositiveManifoldOrientation 1 k M),
    IsCompact M → M ⊆ O → ∀ (P : Fin l → Patch k O) (s : Fin l → PointSign),
    (∀ t, RegularPiece o (P t) (s t)) →
    ∀ Z : Seams n, (∀ i, Z.dim i < k) →
    (∀ t u, u ∈ (P t).region → ∀ v, v ∈ (P t).region → u ≠ v →
      (P t).map u = (P t).map v → (P t).map u ∈ Z.carrier) →
    (∀ i j, i ≠ j → ((P i).map '' (P i).region) ∩ ((P j).map '' (P j).region) ⊆ Z.carrier) →
    M ⊆ (⋃ t, (P t).map '' (P t).region) ∪ Z.carrier →
    ∀ omega : FormField n k, IsCrForm (some 0) O omega →
    HasPositiveIntegral o (tangentRestriction 1 k M omega)
      (∑ t, (s t).val * patchIntegral (P t) (fun _ => 1) omega)

/-- The same regular display computes every actual continuously weighted
whole-manifold integral. This identifies individual localized contributions,
not only their total sum. -/
def regular_display_weighted_integralType : Prop :=
  ∀ {k n l} {O M : Set (E n)} (o : PositiveManifoldOrientation 1 k M),
    IsCompact M → M ⊆ O → ∀ (P : Fin l → Patch k O) (s : Fin l → PointSign),
    (∀ t, RegularPiece o (P t) (s t)) →
    ∀ Z : Seams n, (∀ i, Z.dim i < k) →
    (∀ t u, u ∈ (P t).region → ∀ v, v ∈ (P t).region → u ≠ v →
      (P t).map u = (P t).map v → (P t).map u ∈ Z.carrier) →
    (∀ i j, i ≠ j → ((P i).map '' (P i).region) ∩ ((P j).map '' (P j).region) ⊆ Z.carrier) →
    M ⊆ (⋃ t, (P t).map '' (P t).region) ∪ Z.carrier →
    ∀ omega : FormField n k, IsCrForm (some 0) O omega →
    ∀ w : E n → ℝ, Continuous w →
    HasPositiveIntegral o (fun x => w x • tangentRestriction 1 k M omega x)
      (∑ t, (s t).val * patchIntegral (P t) w omega)

/-- One ambient partition simultaneously localizes all regular boundary pieces.
Each weighted whole-boundary value is identified with its displayed weighted
patch sum, and their sum is the actual bulk Stokes value. -/
def regular_boundary_localizationType : Prop :=
  ∀ {d n q} {O : Set (E n)} (M : Fin q → CompactManifold (d+1) n O)
    (bO : (j : Fin q) → PositiveManifoldOrientation 1 (d+1)
      (intrinsicBoundary 1 (d+2) (M j).carrier)),
    (∀ j, OutwardFirst (d+1) (M j).orientation (bO j)) →
    ∀ (m : Fin q → ℕ) (P : (j : Fin q) → Fin (m j) → Patch (d+1) O)
      (s : (j : Fin q) → Fin (m j) → PointSign),
    (∀ j t, RegularPiece (bO j) (P j t) (s j t)) →
    ∀ Z : Fin q → Seams n, (∀ j i, (Z j).dim i < d+1) →
    (∀ j t u, u ∈ (P j t).region → ∀ v, v ∈ (P j t).region → u ≠ v →
      (P j t).map u = (P j t).map v → (P j t).map u ∈ (Z j).carrier) →
    (∀ j t u, t ≠ u → ((P j t).map '' (P j t).region) ∩
      ((P j u).map '' (P j u).region) ⊆ (Z j).carrier) →
    (∀ j, intrinsicBoundary 1 (d+2) (M j).carrier ⊆
      (⋃ t, (P j t).map '' (P j t).region) ∪ (Z j).carrier) →
    ∀ omega : FormField n (d+1), IsCrForm (some 1) O omega →
    ∀ {ι : Type} (U : ι → Set (E n)), (∀ a, IsOpen (U a)) →
    ((⋃ j, intrinsicBoundary 1 (d+2) (M j).carrier) ∪
      (⋃ z : (j : Fin q) × Fin (m j), (P z.1 z.2).map '' closure (P z.1 z.2).region)) ⊆
      ⋃ a, U a →
    ∃ (L : ℕ) (a : Fin L → ι)
      (A : AmbientPartition
        ((⋃ j, intrinsicBoundary 1 (d+2) (M j).carrier) ∪
          (⋃ z : (j : Fin q) × Fin (m j), (P z.1 z.2).map '' closure (P z.1 z.2).region)) L),
      (∀ i, tsupport (A.weight i) ⊆ U (a i)) ∧
      (∀ j t, patchIntegral (P j t) (fun _ => 1) omega =
        ∑ i, patchIntegral (P j t) (A.weight i) omega) ∧
      ∀ j, ∃ (I : ℝ) (J : Fin L → ℝ),
        HasPositiveIntegral (M j).orientation
          (tangentRestriction 1 (d+2) (M j).carrier (exteriorDerivative omega)) I ∧
        HasManifoldIntegral 1 (d+1) (bO j)
          (tangentRestriction 1 (d+1) (intrinsicBoundary 1 (d+2) (M j).carrier) omega) I ∧
        (∀ i, HasManifoldIntegral 1 (d+1) (bO j)
          (fun x => A.weight i x • tangentRestriction 1 (d+1)
            (intrinsicBoundary 1 (d+2) (M j).carrier) omega x) (J i)) ∧
        (∀ i, J i = ∑ t, (s j t).val * patchIntegral (P j t) (A.weight i) omega) ∧
        I = ∑ i, J i

/-- Higher-dimensional manifold branch of finite piecewise Stokes. Each actual
boundary has a finite regular Jordan display. An equivalence enumerates all
boundary occurrences by prescribed outer pieces and paired internal pieces.
All matching conditions concern maps, parameter diffeomorphisms, induced signs
and integer multiplicities. Integral existence and cancellation are conclusions. -/
def positive_boundary_assemblyType : Prop :=
  ∀ {d n q} {O : Set (E n)} (M : Fin q → CompactManifold (d+1) n O)
    (bO : (j : Fin q) → PositiveManifoldOrientation 1 (d+1)
      (intrinsicBoundary 1 (d+2) (M j).carrier)),
    (∀ j, OutwardFirst (d+1) (M j).orientation (bO j)) →
    ∀ (m : Fin q → ℕ) (P : (j : Fin q) → Fin (m j) → Patch (d+1) O)
      (s : (j : Fin q) → Fin (m j) → PointSign),
    (∀ j t, RegularPiece (bO j) (P j t) (s j t)) →
    ∀ Z : Fin q → Seams n, (∀ j i, (Z j).dim i < d+1) →
    (∀ j t u, u ∈ (P j t).region → ∀ v, v ∈ (P j t).region → u ≠ v →
      (P j t).map u = (P j t).map v → (P j t).map u ∈ (Z j).carrier) →
    (∀ j t u, t ≠ u → ((P j t).map '' (P j t).region) ∩
      ((P j u).map '' (P j u).region) ⊆ (Z j).carrier) →
    (∀ j, intrinsicBoundary 1 (d+2) (M j).carrier ⊆
      (⋃ t, (P j t).map '' (P j t).region) ∪ (Z j).carrier) →
    ∀ (a : Fin q → ℤ) {l p : ℕ}
      (e : (Fin l ⊕ (Fin p × Bool)) ≃ ((j : Fin q) × Fin (m j)))
      (Q : Fin l → Patch (d+1) O) (tSign : Fin l → PointSign) (b : Fin l → ℤ)
      (deltaOut : Fin l → ℝ),
    (∀ t, deltaOut t = 1 ∨ deltaOut t = -1) →
    ∀ hOut : (t : Fin l) → LocalReparametrization
      (P (e (Sum.inl t)).1 (e (Sum.inl t)).2).region (Q t).region (deltaOut t),
    (∀ t, EqOn (P (e (Sum.inl t)).1 (e (Sum.inl t)).2).map
      ((Q t).map ∘ (hOut t).map) (P (e (Sum.inl t)).1 (e (Sum.inl t)).2).region ∧
      (s (e (Sum.inl t)).1 (e (Sum.inl t)).2).val * deltaOut t = (tSign t).val ∧
      b t = a (e (Sum.inl t)).1) →
    ∀ deltaPair : Fin p → ℝ, (∀ i, deltaPair i = 1 ∨ deltaPair i = -1) →
    ∀ hPair : (i : Fin p) → LocalReparametrization
      (P (e (Sum.inr (i,false))).1 (e (Sum.inr (i,false))).2).region
      (P (e (Sum.inr (i,true))).1 (e (Sum.inr (i,true))).2).region (deltaPair i),
    (∀ i, EqOn (P (e (Sum.inr (i,false))).1 (e (Sum.inr (i,false))).2).map
      ((P (e (Sum.inr (i,true))).1 (e (Sum.inr (i,true))).2).map ∘ (hPair i).map)
      (P (e (Sum.inr (i,false))).1 (e (Sum.inr (i,false))).2).region ∧
      (s (e (Sum.inr (i,false))).1 (e (Sum.inr (i,false))).2).val * deltaPair i =
        -(s (e (Sum.inr (i,true))).1 (e (Sum.inr (i,true))).2).val ∧
      a (e (Sum.inr (i,false))).1 = a (e (Sum.inr (i,true))).1) →
    ∀ omega : FormField n (d+1), IsCrForm (some 1) O omega →
    ∃ I : Fin q → ℝ,
      (∀ j, HasPositiveIntegral (M j).orientation
        (tangentRestriction 1 (d+2) (M j).carrier (exteriorDerivative omega)) (I j)) ∧
      (∀ j, HasManifoldIntegral 1 (d+1) (bO j)
        (tangentRestriction 1 (d+1) (intrinsicBoundary 1 (d+2) (M j).carrier) omega) (I j)) ∧
      ∑ j, a j • I j = ∑ t, b t • ((tSign t).val * patchIntegral (Q t) (fun _ => 1) omega)

end Specs.D04.C15.FiniteManifoldBoundaryAssembly
