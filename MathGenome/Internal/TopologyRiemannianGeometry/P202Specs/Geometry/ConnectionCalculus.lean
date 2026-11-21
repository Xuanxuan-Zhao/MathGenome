import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.MetricFoundation
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ConnectionForms
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PullbackConnections
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.CurveCovariantDerivative

/-! Independent assembly specification for paper.tex 3017--3054.
Canonical connection objects are shared with ConnectionForms; the propositions
below retain the complete local, pullback, and C¹ curve statements. No metric
or torsion hypothesis is imposed. Dual/tensor constructions are allocated to
InducedConnections, and the subsequent torsion identities to TorsionAndMetric. -/
set_option autoImplicit false

namespace P202Specs.Geometry.ConnectionCalculus
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleData P202.ConnectionData
universe u v w

def connectionType := {n r : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n a M} → {ι : Type v} → {E : M → Type w} →
  [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)] →
  SmoothVectorBundle S r ι E → Type (max u w)

def connectionValue : connectionType := @Connection

def frameMemberType := {n r : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n a M} → {ι : Type v} → {E : M → Type w} →
  [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)] →
  {B : SmoothVectorBundle S r ι E} →
  LocalFrame B Set.univ isOpen_univ → Fin r → Section B

def frameMemberValue : frameMemberType := @P202.ConnectionData.frameMember

def frameCoefficientType := {n r : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n a M} → {ι : Type v} → {E : M → Type w} →
  [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)] →
  {B : SmoothVectorBundle S r ι E} →
  LocalFrame B Set.univ isOpen_univ → Section B → Fin r → GlobalSmooth S

noncomputable def frameCoefficientValue : frameCoefficientType :=
  @P202.ConnectionData.frameCoefficient

def frameMatrixType := {n r : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n a M} → {ι : Type v} → {E : M → Type w} →
  [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)] →
  {B : SmoothVectorBundle S r ι E} →
  Connection B → LocalFrame B Set.univ isOpen_univ → Field S → M → Matrix (Fin r) (Fin r) ℝ

noncomputable def frameMatrixValue : frameMatrixType := @P202.ConnectionData.frameMatrix

def frameTransitionType := {n r : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n a M} → {ι : Type v} → {E : M → Type w} →
  [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)] →
  {B : SmoothVectorBundle S r ι E} →
  LocalFrame B Set.univ isOpen_univ → LocalFrame B Set.univ isOpen_univ →
  M → Matrix (Fin r) (Fin r) ℝ

noncomputable def frameTransitionValue : frameTransitionType :=
  @P202.ConnectionData.frameTransition

def frameTransitionDerivativeType := {n r : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n a M} → {ι : Type v} → {E : M → Type w} →
  [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)] →
  {B : SmoothVectorBundle S r ι E} →
  Field S → LocalFrame B Set.univ isOpen_univ → LocalFrame B Set.univ isOpen_univ →
  M → Matrix (Fin r) (Fin r) ℝ

noncomputable def frameTransitionDerivativeValue : frameTransitionDerivativeType :=
  @P202.ConnectionData.frameTransitionDerivative


/-- Germ-locality is a theorem, rather than an additional connection axiom. -/
def locality_sectionType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)] ,
  ∀ (B : SmoothVectorBundle S r ι E) (C : Connection B)
    (X : Field S) (s t : Section B) (p : M),
    (∀ᶠ q in nhds p, s.val q = t.val q) → (C.cov X s).val p = (C.cov X t).val p

def locality_fieldType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)] ,
  ∀ (B : SmoothVectorBundle S r ι E) (C : Connection B)
    (X Y : Field S) (s : Section B) (p : M),
    (∀ᶠ q in nhds p, X.val q = Y.val q) → (C.cov X s).val p = (C.cov Y s).val p

/-- The finite frame-expansion calculation, prior to choosing a local frame. -/
def finite_expansionType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)] ,
  ∀ (B : SmoothVectorBundle S r ι E) (C : Connection B)
    (X : Field S) (k : ℕ) (f : Fin k → GlobalSmooth S) (e : Fin k → Section B),
    C.cov X (∑ j, mulSection (f j) (e j)) =
      ∑ j, (mulSection (act S X (f j)) (e j) + mulSection (f j) (C.cov X (e j)))


def global_frame_formulaType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)],
  ∀ (B : SmoothVectorBundle S r ι E) (C : Connection B)
    (b : LocalFrame B Set.univ isOpen_univ) (X : Field S) (s : Section B)
    (p : M) (i : Fin r),
    (frameCoefficient b (C.cov X s) i).val p =
      (act S X (frameCoefficient b s i)).val p +
        ∑ j, frameMatrix C b X p i j * (frameCoefficient b s j).val p

/-- The global-frame specialization of the gauge law. The reverse transition
is the actual inverse, as asserted independently in transition_inverseType. -/
def global_frame_transformationType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)],
  ∀ (B : SmoothVectorBundle S r ι E) (C : Connection B)
    (b c : LocalFrame B Set.univ isOpen_univ) (X : Field S) (p : M),
    frameMatrix C c X p =
      frameTransition c b p * frameMatrix C b X p * frameTransition b c p +
        frameTransition c b p * frameTransitionDerivative X b c p

def transition_inverseType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)],
  ∀ (B : SmoothVectorBundle S r ι E)
    (b c : LocalFrame B Set.univ isOpen_univ) (p : M),
    frameTransition b c p * frameTransition c b p = 1 ∧
      frameTransition c b p * frameTransition b c p = 1


def SectionType := P202Specs.Geometry.ConnectionForms.SectionType.{u,v,w}

noncomputable def SectionValue : SectionType := @P202.ConnectionData.Section

def mulSectionType := P202Specs.Geometry.ConnectionForms.mulSectionType.{u,v,w}

noncomputable def mulSectionValue : mulSectionType := @P202.ConnectionData.mulSection

def LocalSectionType := P202Specs.Geometry.ConnectionForms.LocalSectionType.{u,v,w}

noncomputable def LocalSectionValue : LocalSectionType := @P202.ConnectionData.LocalSection

def covOnType := P202Specs.Geometry.ConnectionForms.covOnType.{u,v,w}

noncomputable def covOnValue : covOnType := @P202.ConnectionData.covOn

def pointDerivativeType := P202Specs.Geometry.ConnectionForms.pointDerivativeType.{u,v,w}

noncomputable def pointDerivativeValue : pointDerivativeType := @P202.ConnectionData.pointDerivative

def connectionFormType := P202Specs.Geometry.ConnectionForms.connectionFormType.{u,v,w}

noncomputable def connectionFormValue : connectionFormType := @P202.ConnectionData.connectionForm

def connectionMatrixType := P202Specs.Geometry.ConnectionForms.connectionMatrixType.{u,v,w}

noncomputable def connectionMatrixValue : connectionMatrixType := @P202.ConnectionData.connectionMatrix

def localTransitionType := P202Specs.Geometry.ConnectionForms.localTransitionType.{u,v,w}

noncomputable def localTransitionValue : localTransitionType := @P202.ConnectionData.localTransition

def localTransitionDerivativeType := P202Specs.Geometry.ConnectionForms.localTransitionDerivativeType.{u,v,w}

noncomputable def localTransitionDerivativeValue : localTransitionDerivativeType := @P202.ConnectionData.localTransitionDerivative

def frameSectionType := P202Specs.Geometry.ConnectionForms.frameSectionType.{u,v,w}

noncomputable def frameSectionValue : frameSectionType := @P202.ConnectionData.frameSection

def restrictFrameType := P202Specs.Geometry.ConnectionForms.restrictFrameType.{u,v,w}

noncomputable def restrictFrameValue : restrictFrameType := @P202.ConnectionData.restrictFrame

def restrictLocalSectionType := P202Specs.Geometry.ConnectionForms.restrictLocalSectionType.{u,v,w}

noncomputable def restrictLocalSectionValue : restrictLocalSectionType := @P202.ConnectionData.restrictLocalSection

def restrictGlobalSectionType := P202Specs.Geometry.ConnectionForms.restrictGlobalSectionType.{u,v,w}

noncomputable def restrictGlobalSectionValue : restrictGlobalSectionType := @P202.ConnectionData.restrictGlobalSection

def FieldType := P202Specs.Geometry.ConnectionForms.FieldType.{u}

noncomputable def FieldValue : FieldType := @P202.ConnectionData.Field

def actType := P202Specs.Geometry.ConnectionForms.actType.{u}

noncomputable def actValue : actType := @P202.ConnectionData.act

def scalarDerivativeType := P202Specs.Geometry.ConnectionForms.scalarDerivativeType.{u}

noncomputable def scalarDerivativeValue : scalarDerivativeType := @P202.ConnectionData.scalarDerivative

def pullbackBundleType := P202Specs.Geometry.PullbackConnections.bundleType.{u,v,w}

noncomputable def pullbackBundleValue : pullbackBundleType := @P202.PullbackData.bundle

def coefficientsAlongType := P202Specs.Geometry.CurveCovariantDerivative.coefficientsAlongType.{u,v,w}

noncomputable def coefficientsAlongValue : coefficientsAlongType := @P202.CurveConnectionData.coefficientsAlong

def frameFieldAlongType := P202Specs.Geometry.CurveCovariantDerivative.frameFieldAlongType.{u,v,w}

noncomputable def frameFieldAlongValue : frameFieldAlongType := @P202.CurveConnectionData.frameFieldAlong

def frameDerivativeType := P202Specs.Geometry.CurveCovariantDerivative.frameDerivativeType.{u,v,w}

noncomputable def frameDerivativeValue : frameDerivativeType := @P202.CurveConnectionData.frameDerivative

def C1FieldOnType := P202Specs.Geometry.CurveCovariantDerivative.C1FieldOnType.{u,v,w}

noncomputable def C1FieldOnValue : C1FieldOnType := @P202.CurveConnectionData.C1FieldOn

def HasCovariantDerivativeWithinAtType := P202Specs.Geometry.CurveCovariantDerivative.HasCovariantDerivativeWithinAtType.{u,v,w}

noncomputable def HasCovariantDerivativeWithinAtValue : HasCovariantDerivativeWithinAtType := @P202.CurveConnectionData.HasCovariantDerivativeWithinAt

def covariantDerivativeWithinType := P202Specs.Geometry.CurveCovariantDerivative.covariantDerivativeWithinType.{u,v,w}

noncomputable def covariantDerivativeWithinValue : covariantDerivativeWithinType := @P202.CurveConnectionData.covariantDerivativeWithin

def HasCovariantDerivativeAtType := P202Specs.Geometry.CurveCovariantDerivative.HasCovariantDerivativeAtType.{u,v,w}

noncomputable def HasCovariantDerivativeAtValue : HasCovariantDerivativeAtType := @P202.CurveConnectionData.HasCovariantDerivativeAt

def covariantDerivativeType := P202Specs.Geometry.CurveCovariantDerivative.covariantDerivativeType.{u,v,w}

noncomputable def covariantDerivativeValue : covariantDerivativeType := @P202.CurveConnectionData.covariantDerivative

def HasVelocityWithinAtType := P202Specs.Geometry.CurveCovariantDerivative.HasVelocityWithinAtType.{u}

noncomputable def HasVelocityWithinAtValue : HasVelocityWithinAtType := @P202.CurveConnectionData.HasVelocityWithinAt

def pointwise_fieldType : Prop :=
  P202Specs.Geometry.ConnectionForms.pointwise_fieldType.{u,v,w}

def covOn_smoothType : Prop :=
  P202Specs.Geometry.ConnectionForms.covOn_smoothType.{u,v,w}

def covOn_globalType : Prop :=
  P202Specs.Geometry.ConnectionForms.covOn_globalType.{u,v,w}

def covOn_restrictionType : Prop :=
  P202Specs.Geometry.ConnectionForms.covOn_restrictionType.{u,v,w}

def pointDerivative_globalType : Prop :=
  P202Specs.Geometry.ConnectionForms.pointDerivative_globalType.{u,v,w}

def covOn_pointDerivativeType : Prop :=
  P202Specs.Geometry.ConnectionForms.covOn_pointDerivativeType.{u,v,w}

def connectionForm_smoothType : Prop :=
  P202Specs.Geometry.ConnectionForms.connectionForm_smoothType.{u,v,w}

def connectionForm_characterizationType : Prop :=
  P202Specs.Geometry.ConnectionForms.connectionForm_characterizationType.{u,v,w}

def connectionForm_restrictionType : Prop :=
  P202Specs.Geometry.ConnectionForms.connectionForm_restrictionType.{u,v,w}

def local_frame_formulaType : Prop :=
  P202Specs.Geometry.ConnectionForms.local_frame_formulaType.{u,v,w}

def local_frame_formula_coefficientsType : Prop :=
  P202Specs.Geometry.ConnectionForms.local_frame_formula_coefficientsType.{u,v,w}

def local_transition_inverseType : Prop :=
  P202Specs.Geometry.ConnectionForms.local_transition_inverseType.{u,v,w}

def localTransition_smoothType : Prop :=
  P202Specs.Geometry.ConnectionForms.localTransition_smoothType.{u,v,w}

def local_frame_transformationType : Prop :=
  P202Specs.Geometry.ConnectionForms.local_frame_transformationType.{u,v,w}

def pullback_exists_uniqueType : Prop :=
  P202Specs.Geometry.PullbackConnections.exists_uniqueType.{u,v,w}

def canonical_pullback_exists_uniqueType : Prop :=
  P202Specs.Geometry.PullbackConnections.canonical_exists_uniqueType.{u,v,w}

def pullback_uniqueType : Prop :=
  P202Specs.Geometry.PullbackConnections.uniquenessType.{u,v,w}

def pullback_frame_existsType : Prop :=
  P202Specs.Geometry.PullbackConnections.frame_existsType.{u,v,w}

def pullback_frame_changeType : Prop :=
  P202Specs.Geometry.PullbackConnections.frame_changeType.{u,v,w}

def pullback_local_formulas_agreeType : Prop :=
  P202Specs.Geometry.PullbackConnections.local_formulas_agreeType.{u,v,w}

def frameDerivative_independentType : Prop :=
  P202Specs.Geometry.CurveCovariantDerivative.frameDerivative_independentType.{u,v,w}

def covariantDerivative_uniqueType : Prop :=
  P202Specs.Geometry.CurveCovariantDerivative.covariantDerivative_uniqueType.{u,v,w}

def exists_coefficients_derivType : Prop :=
  P202Specs.Geometry.CurveCovariantDerivative.exists_coefficients_derivType.{u,v,w}

def local_formulaType : Prop :=
  P202Specs.Geometry.CurveCovariantDerivative.local_formulaType.{u,v,w}

def exists_covariantDerivativeType : Prop :=
  P202Specs.Geometry.CurveCovariantDerivative.exists_covariantDerivativeType.{u,v,w}

def covariantDerivativeWithin_specType : Prop :=
  P202Specs.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_specType.{u,v,w}

def covariantDerivativeWithin_eqType : Prop :=
  P202Specs.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_eqType.{u,v,w}

def segment_derivativeType : Prop :=
  P202Specs.Geometry.CurveCovariantDerivative.segment_derivativeType.{u,v,w}

def derivative_addType : Prop :=
  P202Specs.Geometry.CurveCovariantDerivative.derivative_addType.{u,v,w}

def derivative_smulType : Prop :=
  P202Specs.Geometry.CurveCovariantDerivative.derivative_smulType.{u,v,w}

def derivative_reparamType : Prop :=
  P202Specs.Geometry.CurveCovariantDerivative.derivative_reparamType.{u,v,w}

def covariantDerivativeWithin_reparamType : Prop :=
  P202Specs.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_reparamType.{u,v,w}

def ordinary_reparamType : Prop :=
  P202Specs.Geometry.CurveCovariantDerivative.ordinary_reparamType.{u,v,w}

def derivative_sectionType : Prop :=
  P202Specs.Geometry.CurveCovariantDerivative.derivative_sectionType.{u,v,w}

def derivative_section_fieldType : Prop :=
  P202Specs.Geometry.CurveCovariantDerivative.derivative_section_fieldType.{u,v,w}

def derivative_frame_expansionType : Prop :=
  P202Specs.Geometry.CurveCovariantDerivative.derivative_frame_expansionType.{u,v,w}

def covariantDerivativeWithin_addType : Prop :=
  P202Specs.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_addType.{u,v,w}

def covariantDerivativeWithin_smulType : Prop :=
  P202Specs.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_smulType.{u,v,w}


/-- The local formula as equality in the original bundle fiber. -/
def local_frame_synthesisType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E) (C : Connection B),
  ∀ {U : Set M} {hU : IsOpen U} (b : LocalFrame B U hU)
    (s : LocalSection B U hU) (p : U) (v : TangentSpace S p.val),
    pointDerivative C (SmoothManifolds.SectionExtension.totalSection s.val) p.val v =
      (b.basis p).equivFun.symm (fun i =>
        scalarDerivative S (SmoothManifolds.FrameData.totalize
          (fun q : U => SmoothManifolds.FrameData.coefficients b s.val q i)) p.val v +
        (connectionMatrix C b p v).mulVec
          (SmoothManifolds.FrameData.coefficients b s.val p) i)

/-- The constructed C¹ derivative satisfies the displayed row-frame formula,
including on one-sided parameter germs. -/
def curve_frame_formulaType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E) (C : Connection B),
  ∀ {U : Set M} {hU : IsOpen U} (b : LocalFrame B U hU)
    {c : ℝ → M} {f : ℝ → Euclidean r} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t) (hp : c t ∈ U)
    {V : TangentSpace S (c t)} (hV : P202.CurveConnectionData.HasVelocityWithinAt S c J t V)
    {f' : Euclidean r} (hf : HasDerivWithinAt f f' J t),
    P202.CurveConnectionData.covariantDerivativeWithin C c
        (P202.CurveConnectionData.frameFieldAlong b c f) J t =
      (b.basis ⟨c t, hp⟩).equivFun.symm
        (f' + (connectionMatrix C b ⟨c t, hp⟩ V).mulVec (f t))

/-- Agreement with the original connection on smooth sections in the actual
curve tangent direction, including endpoints. -/
def curve_derivative_sectionType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E) (C : Connection B),
  ∀ (s : Section B) {c : ℝ → M} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t)
    {V : TangentSpace S (c t)} (hV : P202.CurveConnectionData.HasVelocityWithinAt S c J t V),
    P202.CurveConnectionData.covariantDerivativeWithin C c (fun z => s.val (c z)) J t =
      pointDerivative C s.val (c t) V

/-- The reparametrization formula for the ordinary constructed derivative. -/
def ordinary_derivative_reparamType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E) (C : Connection B),
  ∀ {c : ℝ → M} {f : (t : ℝ) → E (c t)} {φ : ℝ → ℝ} {s k : ℝ}
    {D : E (c (φ s))}
    (hD : P202.CurveConnectionData.HasCovariantDerivativeAt C c f (φ s) D)
    (hφ : HasDerivAt φ k s),
    P202.CurveConnectionData.covariantDerivative C (c ∘ φ) (fun z => f (φ z)) s =
      k • P202.CurveConnectionData.covariantDerivative C c f (φ s)

/-- The ordinary curve velocity is exactly the MetricFoundation curve model. -/
def ordinary_velocity_iffType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {c : ℝ → M} {t : ℝ} {V : TangentSpace S (c t)},
    P202.CurveConnectionData.HasVelocityWithinAt S c Set.univ t V ↔
      P202.CurveData.HasVelocityAt S c t V

end P202Specs.Geometry.ConnectionCalculus
