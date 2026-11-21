import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Corners.StructureAndFaces
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.LocalStokes

/-! Analytic interface for M10.06, paper.tex:2028–2046.
The analytic corner objects below use chartwise alternating covectors with the
actual transition derivative law. The global target includes construction of coordinate-compatible integration,
exterior differentiation, resolved-face restriction and the Stokes identity. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SmoothManifolds.CornerStokesData
open ModelData LocalStokesData Set MeasureTheory

/-- The full coordinate face, retaining all its intersections with other faces. -/
def orthantFaceSet {n : ℕ} (k : Fin (n+2)) (i : Fin (n+1)) : Set (Euclidean n) :=
  {y | i.insertNth (0 : ℝ) y ∈ orthantSet (n+1) k}

/-- Exterior differentiation within the closed orthant; local ambient C¹
extensions determine this derivative also at a multiple corner. -/
def orthantBulkCoefficient {n : ℕ} (k : Fin (n+2))
    (ω : CoordinateForm (n+1) n) (x : Euclidean (n+1)) : ℝ :=
  extDerivWithin ω (orthantSet (n+1) k) x (frame (n+1))

/-- Zero-based coordinate i has outward-first sign (-1)^(i+1).
The alternating covector is evaluated on the increasing omitted frame. -/
def orthantBoundaryCoefficient {n : ℕ} (ω : CoordinateForm (n+1) n)
    (i : Fin (n+1)) (y : Euclidean n) : ℝ :=
  (-1 : ℝ)^(i.val+1) * ω (i.insertNth 0 y) (i.removeNth (frame (n+1)))


open CornerData CornerOrientationData OrientationData
universe u

/-- A differential form in every chart of the fixed maximal corner atlas. -/
abbrev ChartField {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold n M) (r : ℕ) :=
  ∀ c : CornerChart n M, c ∈ S.atlas → c.2.source →
    (Euclidean n) [⋀^Fin r]→L[ℝ] ℝ

/-- Alternating covectors glued by the genuine smooth coordinate transitions.
The extension represents a coordinate transition, not an assumed derivative
or Stokes certificate. This is the chart representation of a corner form. -/
structure Form {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold n M) (r : ℕ) where
  field : ChartField S r
  compatible : ∀ (c d : CornerChart n M) (hc : c ∈ S.atlas) (hd : d ∈ S.atlas)
    (p : M) (hp : p ∈ c.2.source) (hq : p ∈ d.2.source)
    (H : OrthantExtension (c.2.symm.trans d.2).source (c.2.symm.trans d.2) (c.2 p)),
    field c hc ⟨p,hp⟩ = (field d hd ⟨p,hq⟩).compContinuousLinearMap
      (fderiv ℝ H.map (c.2 p).val)

/-- Closed support is taken in the full manifold, including multiple corners. -/
def formSupport {n r : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold n M} (ω : Form S r) : Set M :=
  closure {p | ∃ (c : CornerChart n M) (hc : c ∈ S.atlas) (hp : p ∈ c.2.source),
    ω.field c hc ⟨p,hp⟩ ≠ 0}

/-- The source regularity is local ambient extendibility in each chart. -/
def IsRegularForm {n r : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold n M} (s : ℕ∞) (ω : Form S r) : Prop :=
  ∀ (c : CornerChart n M) (hc : c ∈ S.atlas),
    LocallyContDiffAlong s (fun p : c.2.source => (c.2 p.val).val) (ω.field c hc)

structure CompactTopForm {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold n M) where
  form : Form S n
  continuous : ∀ (c : CornerChart n M) (hc : c ∈ S.atlas), Continuous (form.field c hc)
  compact_support : IsCompact (formSupport form)

/-- Zero extension of the entire alternating coordinate form. Derivatives
are taken only within the chart image, so artificial chart edges play no role. -/
def ambientForm {n r : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold n M} (ω : Form S r)
    (c : CornerChart n M) (hc : c ∈ S.atlas) (x : Euclidean n) :
    (Euclidean n) [⋀^Fin r]→L[ℝ] ℝ :=
  if hx : x ∈ orthantSet n c.1 then
    if ht : (⟨x,hx⟩ : Orthant n c.1) ∈ c.2.target then
      ω.field c hc ⟨c.2.symm ⟨x,hx⟩, c.2.map_target ht⟩ else 0
  else 0

/-- The usual exterior derivative formula on the full chart image. -/
def HasDerivative {n r : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold n M} (ω : Form S r) (η : Form S (r+1)) : Prop :=
  ∀ (c : CornerChart n M) (hc : c ∈ S.atlas) (p : c.2.source),
    η.field c hc p = extDerivWithin (ambientForm ω c hc)
      (Subtype.val '' c.2.target) (c.2 p.val).val

/-- Signed coordinate coefficient extended by zero into ambient space.
All hyperplanes are retained with their ordinary Lebesgue null measure. -/
def chartCoefficient {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold n M} (o : CornerOrientation S)
    (c : CornerChart n M) (hc : c ∈ S.atlas) (ω : Form S n) (x : Euclidean n) : ℝ :=
  if hx : x ∈ orthantSet n c.1 then
    if ht : (⟨x,hx⟩ : Orthant n c.1) ∈ c.2.target then
      signValue (o.sign c hc ⟨c.2.symm ⟨x,hx⟩, c.2.map_target ht⟩) *
        ω.field c hc ⟨c.2.symm ⟨x,hx⟩, c.2.map_target ht⟩ (frame n)
    else 0
  else 0

/-- Signed Lebesgue integration, with the empty-product measure in dimension zero. -/
def chartIntegral {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold n M} (o : CornerOrientation S)
    (c : CornerChart n M) (hc : c ∈ S.atlas) (ω : Form S n) : ℝ :=
  ∫ x : Euclidean n, chartCoefficient o c hc ω x

/-- A linear integral compatible with the genuine coordinate integrals.
Linearity is expressed by equations on coordinate fields, as for the supplied
ordinary-manifold integral, and imposes no Stokes identity. -/
def IsIntegral {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold n M} (o : CornerOrientation S)
    (I : CompactTopForm S → ℝ) : Prop :=
  (∀ α β γ : CompactTopForm S,
    (∀ c hc p, γ.form.field c hc p = α.form.field c hc p + β.form.field c hc p) →
      I γ = I α + I β) ∧
  (∀ (a : ℝ) (α β : CompactTopForm S),
    (∀ c hc p, β.form.field c hc p = a • α.form.field c hc p) → I β = a * I α) ∧
  ∀ (c : CornerChart n M) (hc : c ∈ S.atlas) (ω : CompactTopForm S),
    formSupport ω.form ⊆ c.2.source → I ω = chartIntegral o c hc ω.form

/-- Actual restriction to every local face sheet, including its deeper
corners, expressed using the derivative (zero insertion) of face inclusion.
No compactness on the open depth-one stratum is assumed. -/
def IsFaceRestriction {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold (n+1) M} {T : CornerManifold n (ResolvedFaceSpace S)}
    (ω : Form S n) (β : Form T n) : Prop :=
  ∀ (c : CornerChart (n+1) M) (hc : c ∈ S.atlas)
    (i : Fin (n+1)) (_hi : i.val < c.1.val)
    (e : CornerChart n (ResolvedFaceSpace S)) (he : e ∈ T.atlas),
    e.1 = faceConstraintCount c.1 → e.2.source = faceSheet S c i univ →
    (∀ q ∈ e.2.source, (e.2 q).val = i.removeNth ((c.2 q.1).val)) →
    ∀ (q : ResolvedFaceSpace S) (hq : q ∈ e.2.source) (hp : q.1 ∈ c.2.source)
      (v : Fin n → Euclidean n),
      β.field e he ⟨q,hq⟩ v =
        ω.field c hc ⟨q.1,hp⟩ (fun j => faceInsertion i (v j))

end SmoothManifolds.CornerStokesData

namespace Specs.SmoothManifolds.Corners.Stokes
open _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.LocalStokesData
  _root_.SmoothManifolds.CornerStokesData MeasureTheory Set

/-- The actual two signs multiply to the negative coefficient on every face. -/
def face_coefficientType : Prop :=
  ∀ (n : ℕ) (ω : CoordinateForm (n+1) n) (i : Fin (n+1)) (y : Euclidean n),
    orthantBoundaryCoefficient ω i y =
      - signedOmittedCoefficient ω i (i.insertNth 0 y)

/-- Local Stokes with every constrained coordinate face counted once.
The only support assumption is compactness relative to the closed orthant.
Integrability, including on the faces, is a conclusion. k=0 and n=0 are retained.
No additional integrals over higher-codimension intersections occur. -/
def local_orthant_stokesType : Prop :=
  ∀ (n : ℕ) (k : Fin (n+2)) (ω : CoordinateForm (n+1) n),
    LocallyContDiffOn 1 (orthantSet (n+1) k) (fun x => ω x.val) →
    HasCompactSupport (fun x : Orthant (n+1) k => ω x.val) →
    IntegrableOn (orthantBulkCoefficient k ω) (orthantSet (n+1) k) ∧
    (∀ i : Fin (n+1), i.val < k.val →
      IntegrableOn (orthantBoundaryCoefficient ω i) (orthantFaceSet k i)) ∧
    (∫ x in orthantSet (n+1) k, orthantBulkCoefficient k ω x) =
      ∑ i : Fin (n+1), if i.val < k.val then
        ∫ y in orthantFaceSet k i, orthantBoundaryCoefficient ω i y else 0


open _root_.SmoothManifolds.CornerData _root_.SmoothManifolds.CornerOrientationData
universe u

/-- Signed coordinate integration agrees on every corner-chart overlap. -/
def chart_independenceType : Prop :=
  ∀ {d : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold d M) (o : CornerOrientation S)
    (c e : CornerChart d M) (hc : c ∈ S.atlas) (he : e ∈ S.atlas)
    (ω : Form S d), formSupport ω ⊆ c.2.source → formSupport ω ⊆ e.2.source →
      chartIntegral o c hc ω = chartIntegral o e he ω

/-- Coordinate integrability is proved for compact continuous top forms,
including forms supported at a true boundary of a chart model. -/
def coordinate_integrableType : Prop :=
  ∀ {d : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold d M) (o : CornerOrientation S)
    (c : CornerChart d M) (hc : c ∈ S.atlas) (ω : CompactTopForm S),
    formSupport ω.form ⊆ c.2.source → Integrable (chartCoefficient o c hc ω.form)

/-- Existence and uniqueness of coordinate-compatible integration for every
oriented corner manifold, including zero-dimensional resolved boundaries. -/
def exists_integralType : Prop :=
  ∀ {d : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold d M) (o : CornerOrientation S),
    ∃! I : CompactTopForm S → ℝ, IsIntegral o I

/-- The coordinate and linearity laws determine a unique integral whenever an
integral has been constructed. Existence is a separate part of the obligation. -/
def unique_integralType : Prop :=
  ∀ {d : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold d M) (o : CornerOrientation S)
    (I J : CompactTopForm S → ℝ), IsIntegral o I → IsIntegral o J → I = J

/-- Finite localization is consistent with the coordinate construction.
Only continuity is needed for the localizing weights of a continuous top form. -/
def finite_localizationType : Prop :=
  ∀ {d : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold d M) (o : CornerOrientation S)
    (I : CompactTopForm S → ℝ), IsIntegral o I →
    ∀ (m : ℕ) (c : Fin m → CornerChart d M)
      (hc : ∀ i, c i ∈ S.atlas) (ρ : Fin m → M → ℝ),
      (∀ i, Continuous (ρ i)) →
      (∀ i, sectionSupport (ρ i) ⊆ (c i).2.source) →
      ∀ ω : CompactTopForm S, (∀ p ∈ formSupport ω.form, ∑ i, ρ i p = 1) →
      ∃ α : Fin m → CompactTopForm S,
        (∀ i e he p, (α i).form.field e he p = ρ i p.val • ω.form.field e he p) ∧
        (∀ i, formSupport (α i).form ⊆ (c i).2.source) ∧
        I ω = ∑ i, chartIntegral o (c i) (hc i) (α i).form

/-- Exterior differentiation and restriction are compact continuous top forms.
These are conclusions for all C¹ inputs, not extra representation hypotheses. -/
def top_formsType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold (n+1) M) (o : CornerOrientation S)
    (T : CornerManifold n (ResolvedFaceSpace S)) (b : CornerOrientation T),
    IsResolvedOrientation o b → ∀ ω : Form S n,
    IsRegularForm 1 ω → IsCompact (formSupport ω) →
    ∃ (η : CompactTopForm S) (β : CompactTopForm T),
      HasDerivative ω η.form ∧ formSupport η.form ⊆ formSupport ω ∧
      IsFaceRestriction ω β.form ∧
      formSupport β.form ⊆ faceProjection S ⁻¹' formSupport ω

/-- The original global Stokes target, without conditional proof parameters.
The domain is an arbitrary oriented positive-dimensional corner manifold;
resolved face orientation and the two integrals use their canonical interfaces.
The existence claims above ensure these interfaces can always be instantiated. -/
def stokesType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold (n+1) M) (o : CornerOrientation S)
    (T : CornerManifold n (ResolvedFaceSpace S)) (b : CornerOrientation T),
    IsResolvedOrientation o b →
    ∀ (I : CompactTopForm S → ℝ) (J : CompactTopForm T → ℝ),
      IsIntegral o I → IsIntegral b J → ∀ ω : Form S n,
      IsRegularForm 1 ω → IsCompact (formSupport ω) →
      ∃ (η : CompactTopForm S) (β : CompactTopForm T),
        HasDerivative ω η.form ∧ formSupport η.form ⊆ formSupport ω ∧
        IsFaceRestriction ω β.form ∧
        formSupport β.form ⊆ faceProjection S ⁻¹' formSupport ω ∧ I η = J β

/-- Direct source statement: the resolved oriented faces and the two genuine
coordinate-compatible integrals exist for every oriented corner manifold. -/
def canonical_stokesType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold (n+1) M) (o : CornerOrientation S)
    (ω : Form S n), IsRegularForm 1 ω → IsCompact (formSupport ω) →
    ∃ (T : CornerManifold n (ResolvedFaceSpace S)) (b : CornerOrientation T),
      IsResolvedOrientation o b ∧
      ∃ (I : CompactTopForm S → ℝ) (J : CompactTopForm T → ℝ),
        IsIntegral o I ∧ IsIntegral b J ∧
        ∃ (η : CompactTopForm S) (β : CompactTopForm T),
          HasDerivative ω η.form ∧ formSupport η.form ⊆ formSupport ω ∧
          IsFaceRestriction ω β.form ∧
          formSupport β.form ⊆ faceProjection S ⁻¹' formSupport ω ∧ I η = J β

end Specs.SmoothManifolds.Corners.Stokes
