import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.SmoothMetrics
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch06.VectorFieldDerivations

/-! Independent connection interfaces for paper.tex 3017--3045.

Sections are smooth sections of the actual P104 bundles. Vector fields and
one-forms use the tangent realization fixed by MetricFoundation and its actual
linear dual. Connections have only the original algebraic axioms. Germ and
pointwise restriction, smooth one-form matrices, local formulas and gauge laws
are theorem obligations, rather than extra connection data. -/
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

namespace P202.ConnectionData
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapData SmoothManifolds.PartitionData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  SmoothManifolds.SectionExtensionData
universe u v w

section Sections
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]

/-- The real vector space of smooth sections of the given bundle. -/
def sectionModule (B : SmoothVectorBundle S r ι E) :
    Submodule ℝ ((p : M) → E p) where
  carrier := {s | SmoothSection B s}
  zero_mem' := B.zero_smooth
  add_mem' hs ht := fun p => SmoothManifolds.SectionExtension.section_add_smoothAt B (hs p) (ht p)
  smul_mem' c _ hs := fun p => SmoothManifolds.SectionExtension.section_smul_smoothAt B
    (SmoothManifolds.scalarContDiff_const (⊤ : ℕ∞) S.smoothStructure.val c p) (hs p)

abbrev Section (B : SmoothVectorBundle S r ι E) := ↥(sectionModule B)

/-- Multiplication by an actual globally smooth scalar function. -/
def mulSection {B : SmoothVectorBundle S r ι E} (f : GlobalSmooth S)
    (s : Section B) : Section B :=
  ⟨fun p => f.val p • s.val p, fun p => SmoothManifolds.SectionExtension.section_smul_smoothAt B
    ((SmoothManifolds.mem_globalSmoothAlgebra_iff S _).mp f.property p) (s.property p)⟩

end Sections

section Fields
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : SmoothManifold n a M)

noncomputable abbrev tangentBundle := (P202.MetricData.tangentRealization S).space.bundle
noncomputable abbrev Field := Section (tangentBundle S)

/-- The canonical bridge to the original sigma-total-space tangent model. -/
def originalField (X : Field S) :
    SmoothManifolds.VectorFieldData.SmoothField (P202.MetricData.tangentStructure S) where
  val := X.val
  smooth := by
    let R := P202.MetricData.tangentRealization S
    letI := R.space.topology
    letI := (P202.MetricData.tangentStructure S).topology
    exact fun p => SmoothManifolds.manifoldContDiffAt_comp R.space.bundle.totalManifold.smoothStructure.property.1.1
      (X.property p) (R.smooth_to_original ⟨p, X.val p⟩)

/-- X(f) is the intrinsic action of X on smooth scalar germs, with its
smoothness proved by P104's vector-field/derivation correspondence. -/
noncomputable def act (X : Field S) : SmoothManifolds.VectorFieldData.RealDerivation S :=
  SmoothManifolds.VectorFields.derivationOfField S (P202.MetricData.tangentStructure S) (originalField S X)

/-- Cotangent fibers are actual linear duals of the fixed tangent realization. -/
noncomputable def cotangentDual :=
  Classical.choice (SmoothManifolds.BundleOperations.exists_dual (tangentBundle S))

noncomputable instance cotangentTopology :
    TopologicalSpace (Bundle.TotalSpace (Euclidean n)
      (fun p => Module.Dual ℝ (TangentSpace S p))) := (cotangentDual S).space.topology

noncomputable abbrev cotangentBundle := (cotangentDual S).space.bundle

/-- The actual smooth scalar germ, with an irrelevant fallback for nonsmooth data. -/
noncomputable def scalarGerm (f : M → ℝ) (p : M) : SmoothGerm S p := by
  classical
  exact if h : SmoothManifolds.PartitionData.ScalarContDiffAt (⊤ : ℕ∞)
      S.smoothStructure.val f p then
    ⟨Filter.Germ.ofFun f, Algebra.subset_adjoin ⟨f, h, rfl⟩⟩ else 0

/-- Intrinsic differential of a local scalar representative. -/
noncomputable def scalarDerivative (f : M → ℝ) (p : M) :
    TangentSpace S p →ₗ[ℝ] ℝ :=
  SmoothManifolds.CovectorData.germDifferential S p (scalarGerm S f p)

end Fields

section Connections
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]

/-- A general connection, real-bilinear on smooth vector fields and smooth
sections, C∞-linear in the vector field and Leibniz in the section.
The axioms are precisely the defining connection laws, with no local-formula,
pullback, metric-compatibility or torsion certificate as extra data. -/
structure Connection (B : SmoothVectorBundle S r ι E) where
  cov : Field S →ₗ[ℝ] Section B →ₗ[ℝ] Section B
  linear_field : ∀ (f : GlobalSmooth S) (X : Field S) (s : Section B),
    cov (mulSection f X) s = mulSection f (cov X s)
  leibniz : ∀ (X : Field S) (f : GlobalSmooth S) (s : Section B),
    cov X (mulSection f s) =
      mulSection (act S X f) s + mulSection f (cov X s)

/-- A frame on the whole base, using the library's actual local-frame object.
This construction is also needed after localizing a connection to an open set. -/
def frameMember {B : SmoothVectorBundle S r ι E}
    (b : LocalFrame B Set.univ isOpen_univ) (j : Fin r) : Section B := by
  refine ⟨fun p => b.section_ j ⟨p, Set.mem_univ p⟩, ?_⟩
  have h := (SmoothManifolds.manifoldContDiff_restrict_open (⊤ : ℕ∞)
    S.smoothStructure.val B.totalManifold.smoothStructure.val
    (fun p => (⟨p, b.section_ j ⟨p, Set.mem_univ p⟩⟩ :
      Bundle.TotalSpace (Euclidean r) E)) Set.univ isOpen_univ).mpr (b.smooth j)
  exact fun p => h p (Set.mem_univ p)

/-- The unique smooth coefficients of a smooth section in a global frame. -/
noncomputable def frameCoefficient {B : SmoothVectorBundle S r ι E}
    (b : LocalFrame B Set.univ isOpen_univ) (s : Section B) (j : Fin r) :
    GlobalSmooth S := by
  let f : Set.univ (α := M) → ℝ := fun p =>
    SmoothManifolds.FrameData.coefficients b (fun q => s.val q.val) p j
  have hs := (SmoothManifolds.manifoldContDiff_restrict_open (⊤ : ℕ∞)
    S.smoothStructure.val B.totalManifold.smoothStructure.val
    (fun p => (⟨p, s.val p⟩ : Bundle.TotalSpace (Euclidean r) E))
    Set.univ isOpen_univ).mp (fun p _ => s.property p)
  have hf := (SmoothManifolds.Frames.smooth_section_iff_coefficients
    B Set.univ isOpen_univ b (fun q => s.val q.val)).mp hs j
  refine ⟨fun p => f ⟨p, Set.mem_univ p⟩,
    (SmoothManifolds.mem_globalSmoothAlgebra_iff S _).mpr (fun p => ?_)⟩
  have ht := SmoothManifolds.FrameData.VectorSmoothAt.totalize isOpen_univ
    (hf ⟨p, Set.mem_univ p⟩)
  apply (SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mpr
  apply ht.congr
  exact Filter.Eventually.of_forall (fun q =>
    SmoothManifolds.FrameData.totalize_of_mem f q (Set.mem_univ q))

/-- Row-frame convention: column j consists of the coefficients of ∇e_j.
This preliminary global interface is supplemented below by genuine tangent-
linear one-forms on arbitrary open frame domains. -/
noncomputable def frameMatrix {B : SmoothVectorBundle S r ι E}
    (C : Connection B) (b : LocalFrame B Set.univ isOpen_univ)
    (X : Field S) (p : M) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => (frameCoefficient b (C.cov X (frameMember b j)) i).val p

/-- The change-of-frame matrix, with e' = e A, determined by actual frames. -/
noncomputable def frameTransition {B : SmoothVectorBundle S r ι E}
    (b c : LocalFrame B Set.univ isOpen_univ) (p : M) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => (frameCoefficient b (frameMember c j) i).val p

/-- The directional derivative of the transition entries, using X on germs. -/
noncomputable def frameTransitionDerivative {B : SmoothVectorBundle S r ι E}
    (X : Field S) (b c : LocalFrame B Set.univ isOpen_univ) (p : M) :
    Matrix (Fin r) (Fin r) ℝ :=
  fun i j => (act S X (frameCoefficient b (frameMember c j) i)).val p

/-- Ambient representatives of local sections are used only through their germs.
The fallback is irrelevant wherever a smooth global representative exists. -/
noncomputable def germRepresentative {B : SmoothVectorBundle S r ι E}
    (s : (p : M) → E p) (p : M) : Section B := by
  classical
  exact if h : ∃ t : Section B, ∀ᶠ q in nhds p, t.val q = s q then
    Classical.choose h else 0

/-- Pointwise restriction of the original global connection to section germs. -/
noncomputable def localCov {B : SmoothVectorBundle S r ι E} (C : Connection B)
    (X : (p : M) → TangentSpace S p) (s : (p : M) → E p) (p : M) : E p :=
  (C.cov (germRepresentative (B := tangentBundle S) X p)
    (germRepresentative (B := B) s p)).val p

/-- A local section has its actual open domain and smooth total-space map. -/
def LocalSection (B : SmoothVectorBundle S r ι E) (U : Set M) (hU : IsOpen U) :=
  {s : (p : U) → E p.val //
    ManifoldSmooth (openSubsetAtlas S.smoothStructure.val U hU)
      B.totalManifold.smoothStructure.val
      (fun p => (⟨p.val, s p⟩ : Bundle.TotalSpace (Euclidean r) E))}

/-- Restriction of a global smooth section to its actual local domain. -/
def restrictGlobalSection {B : SmoothVectorBundle S r ι E}
    (s : Section B) (U : Set M) (hU : IsOpen U) : LocalSection B U hU :=
  ⟨fun p => s.val p.val,
    (SmoothManifolds.manifoldContDiff_restrict_open (⊤ : ℕ∞) _ _ _ U hU).mp
      (fun p _ => s.property p)⟩

/-- Restriction of actual local sections to any smaller open domain. -/
noncomputable def restrictLocalSection {B : SmoothVectorBundle S r ι E}
    {U V : Set M} {hU : IsOpen U} {hV : IsOpen V}
    (s : LocalSection B V hV) (hUV : U ⊆ V) : LocalSection B U hU := by
  let t := SmoothManifolds.SectionExtension.totalSection s.val
  have ht := SmoothManifolds.SectionExtension.totalSection_smooth B hV s.val s.property
  refine ⟨fun p => s.val ⟨p.val, hUV p.property⟩, ?_⟩
  have h := (SmoothManifolds.manifoldContDiff_restrict_open (⊤ : ℕ∞)
    _ _ (fun p => (⟨p, t p⟩ : Bundle.TotalSpace (Euclidean r) E)) U hU).mp
      (fun p hp => ht p (hUV hp))
  have heq : (fun p : U => (⟨p.val, s.val ⟨p.val, hUV p.property⟩⟩ :
      Bundle.TotalSpace (Euclidean r) E)) =
      (fun p : U => (⟨p.val, t p.val⟩ : Bundle.TotalSpace (Euclidean r) E)) := by
    funext p
    simp only [t, SmoothManifolds.SectionExtension.totalSection_of_mem _ p.val (hUV p.property)]
  rw [heq]
  exact h

/-- A local frame restricts to every smaller open subset, in the same fibers. -/
noncomputable def restrictFrame {B : SmoothVectorBundle S r ι E}
    {U V : Set M} {hU : IsOpen U} {hV : IsOpen V}
    (b : LocalFrame B V hV) (hUV : U ⊆ V) : LocalFrame B U hU where
  section_ j p := b.section_ j ⟨p.val, hUV p.property⟩
  basis p := b.basis ⟨p.val, hUV p.property⟩
  basis_eq p j := b.basis_eq _ j
  smooth j := (restrictLocalSection (hU := hU) (hV := hV) (⟨b.section_ j, b.smooth j⟩ : LocalSection B V hV) hUV).property

/-- Synthesis of a smooth local coefficient column in a row frame. -/
noncomputable def frameSection {B : SmoothVectorBundle S r ι E}
    {U : Set M} {hU : IsOpen U} (b : LocalFrame B U hU)
    (v : U → Euclidean r)
    (hv : SmoothManifolds.FrameData.VectorSmooth
      (openSubsetAtlas S.smoothStructure.val U hU) v) : LocalSection B U hU := by
  refine ⟨fun p => (b.basis p).equivFun.symm (v p), ?_⟩
  apply (SmoothManifolds.Frames.smooth_section_iff_coefficients B U hU b _).mpr
  intro j p
  have h := (hv p).postcomp (ContinuousLinearMap.proj j).contDiff
  apply h.congr
  exact Filter.Eventually.of_forall (fun q => by
    simp only [SmoothManifolds.FrameData.coefficients, LinearEquiv.apply_symm_apply]
    rfl)

/-- Restriction evaluated on arbitrary smooth local sections and local fields. -/
noncomputable def covOn {B : SmoothVectorBundle S r ι E} (C : Connection B)
    (U : Set M) (hU : IsOpen U)
    (X : LocalSection (tangentBundle S) U hU) (s : LocalSection B U hU)
    (p : U) : E p.val :=
  localCov C (SmoothManifolds.SectionExtension.totalSection X.val)
    (SmoothManifolds.SectionExtension.totalSection s.val) p.val

/-- The intrinsic linear derivative of a section germ. Its characterization,
including existence for smooth germs, is a theorem in the implementation. -/
noncomputable def pointDerivative {B : SmoothVectorBundle S r ι E}
    (C : Connection B) (s : (p : M) → E p) (p : M) :
    TangentSpace S p →ₗ[ℝ] E p := by
  classical
  exact if h : ∃ D : TangentSpace S p →ₗ[ℝ] E p,
      ∀ X : Field S, D (X.val p) = localCov C X.val s p then Classical.choose h else 0

/-- Genuine linear forms on the shared tangent fibers, with column j = ∇e_j. -/
noncomputable def connectionForm {B : SmoothVectorBundle S r ι E}
    (C : Connection B) {U : Set M} {hU : IsOpen U}
    (b : LocalFrame B U hU) (p : U) (i j : Fin r) :
    TangentSpace S p.val →ₗ[ℝ] ℝ :=
  (LinearMap.proj i).comp ((b.basis p).equivFun.toLinearMap.comp
    (pointDerivative C (SmoothManifolds.SectionExtension.totalSection (b.section_ j)) p.val))

/-- Evaluation of the one-form matrix on an intrinsic tangent vector. -/
noncomputable def connectionMatrix {B : SmoothVectorBundle S r ι E}
    (C : Connection B) {U : Set M} {hU : IsOpen U}
    (b : LocalFrame B U hU) (p : U) (v : TangentSpace S p.val) :
    Matrix (Fin r) (Fin r) ℝ := fun i j => connectionForm C b p i j v

/-- The actual transition e' = e A on an arbitrary common open frame domain. -/
noncomputable def localTransition {B : SmoothVectorBundle S r ι E}
    {U : Set M} {hU : IsOpen U} (b c : LocalFrame B U hU) (p : U) :
    Matrix (Fin r) (Fin r) ℝ := fun i j => (b.basis p).equivFun (c.section_ j p) i

/-- The genuine differential dA, evaluated on the shared tangent fiber. -/
noncomputable def localTransitionDerivative {B : SmoothVectorBundle S r ι E}
    {U : Set M} {hU : IsOpen U} (b c : LocalFrame B U hU) (p : U)
    (v : TangentSpace S p.val) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => scalarDerivative S
    (SmoothManifolds.FrameData.totalize (fun q : U => localTransition b c q i j)) p.val v

end Connections
end P202.ConnectionData

namespace P202Specs.Geometry.ConnectionForms
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.MapData P202.ConnectionData
open Filter
open scoped Topology
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

/-- A preliminary global-frame version of the gauge law. The reverse transition
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






/-! Public expected interfaces. -/


def SectionType := {n r : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n a M} → {ι : Type v} → {E : M → Type w} →
  [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)] →
  SmoothVectorBundle S r ι E → Type (max u w)

noncomputable def SectionValue : SectionType := @P202.ConnectionData.Section


def sectionModuleType := {n r : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n a M} → {ι : Type v} → {E : M → Type w} →
  [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)] →
  SmoothVectorBundle S r ι E → Submodule ℝ ((p : M) → E p)

noncomputable def sectionModuleValue : sectionModuleType := @P202.ConnectionData.sectionModule


def mulSectionType := {n r : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n a M} → {ι : Type v} → {E : M → Type w} →
  [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)] →
  {B : SmoothVectorBundle S r ι E} → GlobalSmooth S → Section B → Section B

noncomputable def mulSectionValue : mulSectionType := @P202.ConnectionData.mulSection


def FieldType := {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
  (S : SmoothManifold n a M) → Type u

noncomputable def FieldValue : FieldType := @P202.ConnectionData.Field


def originalFieldType := {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
  (S : SmoothManifold n a M) → Field S → SmoothManifolds.VectorFieldData.SmoothField (P202.MetricData.tangentStructure S)

noncomputable def originalFieldValue : originalFieldType := @P202.ConnectionData.originalField


def actType := {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
  (S : SmoothManifold n a M) → Field S → SmoothManifolds.VectorFieldData.RealDerivation S

noncomputable def actValue : actType := @P202.ConnectionData.act


def scalarDerivativeType := {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
  (S : SmoothManifold n a M) → (M → ℝ) → (p : M) → TangentSpace S p →ₗ[ℝ] ℝ

noncomputable def scalarDerivativeValue : scalarDerivativeType := @P202.ConnectionData.scalarDerivative


def LocalSectionType := {n r : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n a M} → {ι : Type v} → {E : M → Type w} →
  [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)] →
  (B : SmoothVectorBundle S r ι E) → (U : Set M) → IsOpen U → Type (max u w)

noncomputable def LocalSectionValue : LocalSectionType := @P202.ConnectionData.LocalSection


def localCovType := {n r : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n a M} → {ι : Type v} → {E : M → Type w} →
  [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)] →
  {B : SmoothVectorBundle S r ι E} → Connection B → ((p : M) → TangentSpace S p) → ((p : M) → E p) → (p : M) → E p

noncomputable def localCovValue : localCovType := @P202.ConnectionData.localCov


def covOnType := {n r : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n a M} → {ι : Type v} → {E : M → Type w} →
  [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)] →
  {B : SmoothVectorBundle S r ι E} → Connection B → (U : Set M) → (hU : IsOpen U) → LocalSection (tangentBundle S) U hU → LocalSection B U hU → (p : U) → E p.val

noncomputable def covOnValue : covOnType := @P202.ConnectionData.covOn


def pointDerivativeType := {n r : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n a M} → {ι : Type v} → {E : M → Type w} →
  [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)] →
  {B : SmoothVectorBundle S r ι E} → Connection B → ((p : M) → E p) → (p : M) → TangentSpace S p →ₗ[ℝ] E p

noncomputable def pointDerivativeValue : pointDerivativeType := @P202.ConnectionData.pointDerivative


def connectionFormType := {n r : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n a M} → {ι : Type v} → {E : M → Type w} →
  [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)] →
  {B : SmoothVectorBundle S r ι E} → Connection B → {U : Set M} → {hU : IsOpen U} → LocalFrame B U hU → (p : U) → Fin r → Fin r → TangentSpace S p.val →ₗ[ℝ] ℝ

noncomputable def connectionFormValue : connectionFormType := @P202.ConnectionData.connectionForm


def connectionMatrixType := {n r : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n a M} → {ι : Type v} → {E : M → Type w} →
  [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)] →
  {B : SmoothVectorBundle S r ι E} → Connection B → {U : Set M} → {hU : IsOpen U} → LocalFrame B U hU → (p : U) → TangentSpace S p.val → Matrix (Fin r) (Fin r) ℝ

noncomputable def connectionMatrixValue : connectionMatrixType := @P202.ConnectionData.connectionMatrix


def localTransitionType := {n r : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n a M} → {ι : Type v} → {E : M → Type w} →
  [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)] →
  {B : SmoothVectorBundle S r ι E} → {U : Set M} → {hU : IsOpen U} → LocalFrame B U hU → LocalFrame B U hU → U → Matrix (Fin r) (Fin r) ℝ

noncomputable def localTransitionValue : localTransitionType := @P202.ConnectionData.localTransition


def localTransitionDerivativeType := {n r : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n a M} → {ι : Type v} → {E : M → Type w} →
  [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)] →
  {B : SmoothVectorBundle S r ι E} → {U : Set M} → {hU : IsOpen U} → LocalFrame B U hU → LocalFrame B U hU → (p : U) → TangentSpace S p.val → Matrix (Fin r) (Fin r) ℝ

noncomputable def localTransitionDerivativeValue : localTransitionDerivativeType := @P202.ConnectionData.localTransitionDerivative


def frameSectionType := {n r : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n a M} → {ι : Type v} → {E : M → Type w} →
  [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)] →
  {B : SmoothVectorBundle S r ι E} → {U : Set M} → {hU : IsOpen U} → (b : LocalFrame B U hU) → (v : U → Euclidean r) → SmoothManifolds.FrameData.VectorSmooth (openSubsetAtlas S.smoothStructure.val U hU) v → LocalSection B U hU

noncomputable def frameSectionValue : frameSectionType := @P202.ConnectionData.frameSection


def restrictGlobalSectionType := {n r : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n a M} → {ι : Type v} → {E : M → Type w} →
  [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)] →
  {B : SmoothVectorBundle S r ι E} → Section B → (U : Set M) → (hU : IsOpen U) → LocalSection B U hU

noncomputable def restrictGlobalSectionValue : restrictGlobalSectionType := @P202.ConnectionData.restrictGlobalSection


def restrictLocalSectionType := {n r : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n a M} → {ι : Type v} → {E : M → Type w} →
  [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)] →
  {B : SmoothVectorBundle S r ι E} → {U V : Set M} → {hU : IsOpen U} → {hV : IsOpen V} → LocalSection B V hV → U ⊆ V → LocalSection B U hU

noncomputable def restrictLocalSectionValue : restrictLocalSectionType := @P202.ConnectionData.restrictLocalSection


def restrictFrameType := {n r : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n a M} → {ι : Type v} → {E : M → Type w} →
  [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)] →
  {B : SmoothVectorBundle S r ι E} → {U V : Set M} → {hU : IsOpen U} → {hV : IsOpen V} → LocalFrame B V hV → U ⊆ V → LocalFrame B U hU

noncomputable def restrictFrameValue : restrictFrameType := @P202.ConnectionData.restrictFrame



def exists_section_representativeType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E),
  ∀ (U : Set M) (hU : IsOpen U)
    (s : (q : M) → E q)
    (hs : SmoothManifolds.MapData.ManifoldSmoothOn S.smoothStructure.val
      B.totalManifold.smoothStructure.val
      (fun q => (⟨q, s q⟩ : Bundle.TotalSpace (Euclidean r) E)) U)
    (p : M) (hp : p ∈ U),
  ∃ t : Section B, ∀ᶠ q in 𝓝 p, t.val q = s q


def section_evaluation_surjectiveType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E),
  ∀ (p : M) (v : E p),
  ∃ s : Section B, s.val p = v


def covOn_pointDerivativeType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B),
  ∀ {U : Set M} {hU : IsOpen U}
    (X : LocalSection (tangentBundle S) U hU) (s : LocalSection B U hU) (p : U),
  covOn C U hU X s p =
      pointDerivative C (SmoothManifolds.SectionExtension.totalSection s.val) p.val (X.val p)


def connectionForm_restrictionType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B),
  ∀ {U V : Set M} {hU : IsOpen U} {hV : IsOpen V}
    (hUV : U ⊆ V) (b : LocalFrame B V hV) (p : U) (i j : Fin r),
  connectionForm C (restrictFrame (hU := hU) b hUV) p i j =
      connectionForm C b ⟨p.val, hUV p.property⟩ i j


def localCov_smoothType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B),
  ∀ (U : Set M) (hU : IsOpen U)
    (X : (q : M) → TangentSpace S q) (s : (q : M) → E q)
    (hX : SmoothManifolds.MapData.ManifoldSmoothOn S.smoothStructure.val
      (tangentBundle S).totalManifold.smoothStructure.val
      (fun q => (⟨q, X q⟩ : Bundle.TotalSpace (Euclidean n) (TangentSpace S))) U)
    (hs : SmoothManifolds.MapData.ManifoldSmoothOn S.smoothStructure.val
      B.totalManifold.smoothStructure.val
      (fun q => (⟨q, s q⟩ : Bundle.TotalSpace (Euclidean r) E)) U),
  SmoothManifolds.MapData.ManifoldSmoothOn S.smoothStructure.val
      B.totalManifold.smoothStructure.val
      (fun q => (⟨q, localCov C X s q⟩ : Bundle.TotalSpace (Euclidean r) E)) U


def pointwise_fieldType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B),
  ∀ (X Y : Field S) (s : Section B) (p : M)
    (hXY : X.val p = Y.val p),
  (C.cov X s).val p = (C.cov Y s).val p


def localCov_eqType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B),
  ∀ (X : (q : M) → TangentSpace S q) (s : (q : M) → E q)
    (p : M) (Y : Field S) (t : Section B)
    (hX : ∀ᶠ q in 𝓝 p, Y.val q = X q)
    (hs : ∀ᶠ q in 𝓝 p, t.val q = s q),
  localCov C X s p = (C.cov Y t).val p


def localCov_globalType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B),
  ∀ (X : Field S) (s : Section B) (p : M),
  localCov C X.val s.val p = (C.cov X s).val p


def localCov_congrType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B),
  ∀ (X Y : (q : M) → TangentSpace S q) (s t : (q : M) → E q)
    (p : M) (hX : ∃ Z : Field S, ∀ᶠ q in 𝓝 p, Z.val q = X q)
    (hs : ∃ u : Section B, ∀ᶠ q in 𝓝 p, u.val q = s q)
    (hXY : ∀ᶠ q in 𝓝 p, X q = Y q) (hst : ∀ᶠ q in 𝓝 p, s q = t q),
  localCov C X s p = localCov C Y t p


def localCov_add_fieldType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B),
  ∀ (X Y : (q : M) → TangentSpace S q) (s : (q : M) → E q)
    (p : M) (hX : ∃ Z : Field S, ∀ᶠ q in 𝓝 p, Z.val q = X q)
    (hY : ∃ Z : Field S, ∀ᶠ q in 𝓝 p, Z.val q = Y q)
    (hs : ∃ u : Section B, ∀ᶠ q in 𝓝 p, u.val q = s q),
  localCov C (fun q => X q + Y q) s p = localCov C X s p + localCov C Y s p


def localCov_add_sectionType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B),
  ∀ (X : (q : M) → TangentSpace S q) (s t : (q : M) → E q)
    (p : M) (hX : ∃ Z : Field S, ∀ᶠ q in 𝓝 p, Z.val q = X q)
    (hs : ∃ u : Section B, ∀ᶠ q in 𝓝 p, u.val q = s q)
    (ht : ∃ u : Section B, ∀ᶠ q in 𝓝 p, u.val q = t q),
  localCov C X (fun q => s q + t q) p = localCov C X s p + localCov C X t p


def localCov_smul_sectionType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B),
  ∀ (X : (q : M) → TangentSpace S q) (s : (q : M) → E q)
    (c : ℝ) (p : M) (hX : ∃ Z : Field S, ∀ᶠ q in 𝓝 p, Z.val q = X q)
    (hs : ∃ u : Section B, ∀ᶠ q in 𝓝 p, u.val q = s q),
  localCov C X (fun q => c • s q) p = c • localCov C X s p


def localCov_mul_fieldType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B),
  ∀ (X : (q : M) → TangentSpace S q) (s : (q : M) → E q)
    (f : M → ℝ) (p : M)
    (hX : ∃ Z : Field S, ∀ᶠ q in 𝓝 p, Z.val q = X q)
    (hs : ∃ u : Section B, ∀ᶠ q in 𝓝 p, u.val q = s q)
    (hf : ∃ g : GlobalSmooth S, g.val =ᶠ[𝓝 p] f),
  localCov C (fun q => f q • X q) s p = f p • localCov C X s p


def localCov_leibnizType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B),
  ∀ (X : (q : M) → TangentSpace S q) (s : (q : M) → E q)
    (f : M → ℝ) (p : M)
    (hX : ∃ Z : Field S, ∀ᶠ q in 𝓝 p, Z.val q = X q)
    (hs : ∃ u : Section B, ∀ᶠ q in 𝓝 p, u.val q = s q)
    (hf : ∃ g : GlobalSmooth S, g.val =ᶠ[𝓝 p] f),
  localCov C X (fun q => f q • s q) p =
      scalarDerivative S f p (X p) • s p + f p • localCov C X s p


def exists_pointDerivativeType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B),
  ∀ (s : (q : M) → E q) (p : M)
    (hs : ∃ t : Section B, ∀ᶠ q in 𝓝 p, t.val q = s q),
  ∃! D : TangentSpace S p →ₗ[ℝ] E p,
      ∀ X : Field S, D (X.val p) = localCov C X.val s p


def pointDerivative_applyType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B),
  ∀ (s : (q : M) → E q) (p : M)
    (hs : ∃ t : Section B, ∀ᶠ q in 𝓝 p, t.val q = s q) (X : Field S),
  pointDerivative C s p (X.val p) = localCov C X.val s p


def pointDerivative_globalType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B),
  ∀ (s : Section B) (p : M) (X : Field S),
  pointDerivative C s.val p (X.val p) = (C.cov X s).val p


def pointDerivative_congrType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B),
  ∀ (s t : (q : M) → E q) (p : M)
    (hs : ∃ u : Section B, ∀ᶠ q in 𝓝 p, u.val q = s q)
    (hst : ∀ᶠ q in 𝓝 p, s q = t q),
  pointDerivative C s p = pointDerivative C t p


def pointDerivative_localType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B),
  ∀ (X : (q : M) → TangentSpace S q)
    (s : (q : M) → E q) (p : M)
    (hX : ∃ Y : Field S, ∀ᶠ q in 𝓝 p, Y.val q = X q)
    (hs : ∃ t : Section B, ∀ᶠ q in 𝓝 p, t.val q = s q),
  pointDerivative C s p (X p) = localCov C X s p


def localCov_pointwise_fieldType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B),
  ∀ (X Y : (q : M) → TangentSpace S q)
    (s : (q : M) → E q) (p : M)
    (hX : ∃ Z : Field S, ∀ᶠ q in 𝓝 p, Z.val q = X q)
    (hY : ∃ Z : Field S, ∀ᶠ q in 𝓝 p, Z.val q = Y q)
    (hs : ∃ t : Section B, ∀ᶠ q in 𝓝 p, t.val q = s q) (hXY : X p = Y p),
  localCov C X s p = localCov C Y s p


def pointDerivative_add_sectionType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B),
  ∀ (s t : Section B) (p : M) (v : TangentSpace S p),
  pointDerivative C (s + t).val p v =
      pointDerivative C s.val p v + pointDerivative C t.val p v


def pointDerivative_smul_sectionType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B),
  ∀ (s : Section B) (c : ℝ) (p : M) (v : TangentSpace S p),
  pointDerivative C (c • s).val p v = c • pointDerivative C s.val p v


def pointDerivative_leibnizType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B),
  ∀ (s : Section B) (f : GlobalSmooth S)
    (p : M) (v : TangentSpace S p),
  pointDerivative C (mulSection f s).val p v =
      scalarDerivative S f.val p v • s.val p + f.val p • pointDerivative C s.val p v


def covOn_smoothType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B),
  ∀ (U : Set M) (hU : IsOpen U)
    (X : LocalSection (tangentBundle S) U hU) (s : LocalSection B U hU),
  SmoothManifolds.MapData.ManifoldSmooth (openSubsetAtlas S.smoothStructure.val U hU)
      B.totalManifold.smoothStructure.val
      (fun p : U => (⟨p.val, covOn C U hU X s p⟩ : Bundle.TotalSpace (Euclidean r) E))


def covOn_globalType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B),
  ∀ (U : Set M) (hU : IsOpen U) (X : Field S) (s : Section B) (p : U),
  covOn C U hU (restrictGlobalSection X U hU) (restrictGlobalSection s U hU) p =
      (C.cov X s).val p.val


def covOn_restrictionType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B),
  ∀ {U V : Set M} {hU : IsOpen U} {hV : IsOpen V}
    (hUV : U ⊆ V) (X : LocalSection (tangentBundle S) V hV)
    (s : LocalSection B V hV) (p : U),
  covOn C U hU (restrictLocalSection X hUV) (restrictLocalSection s hUV) p =
      covOn C V hV X s ⟨p.val, hUV p.property⟩


def connectionForm_smoothType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B),
  ∀ {U : Set M} (hU : IsOpen U)
    (b : LocalFrame B U hU) (i j : Fin r),
  ManifoldSmoothOn S.smoothStructure.val (cotangentBundle S).totalManifold.smoothStructure.val
      (fun q => (⟨q, SmoothManifolds.SectionExtension.totalSection
        (E := fun p => Module.Dual ℝ (TangentSpace S p))
        (fun p : U => connectionForm C b p i j) q⟩ :
        Bundle.TotalSpace (Euclidean n) (fun p => Module.Dual ℝ (TangentSpace S p)))) U


def connectionForm_characterizationType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B),
  ∀ {U : Set M} {hU : IsOpen U}
    (b : LocalFrame B U hU) (X : LocalSection (tangentBundle S) U hU)
    (p : U) (i j : Fin r),
  connectionForm C b p i j (X.val p) =
      (b.basis p).equivFun (covOn C U hU X ⟨b.section_ j, b.smooth j⟩ p) i


def local_frame_formulaType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B),
  ∀ {U : Set M} {hU : IsOpen U}
    (b : LocalFrame B U hU) (s : LocalSection B U hU) (p : U)
    (v : TangentSpace S p.val) (i : Fin r),
  (b.basis p).equivFun
      (pointDerivative C (SmoothManifolds.SectionExtension.totalSection s.val) p.val v) i =
    scalarDerivative S (SmoothManifolds.FrameData.totalize
      (fun q : U => SmoothManifolds.FrameData.coefficients b s.val q i)) p.val v +
      ∑ j, connectionForm C b p i j v *
        SmoothManifolds.FrameData.coefficients b s.val p j


def local_frame_formula_coefficientsType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B),
  ∀ {U : Set M} {hU : IsOpen U}
    (b : LocalFrame B U hU) (f : U → Euclidean r)
    (hf : SmoothManifolds.FrameData.VectorSmooth (openSubsetAtlas S.smoothStructure.val U hU) f)
    (p : U) (v : TangentSpace S p.val) (i : Fin r),
  (b.basis p).equivFun
      (pointDerivative C (SmoothManifolds.SectionExtension.totalSection
        (frameSection b f hf).val) p.val v) i =
      scalarDerivative S (SmoothManifolds.FrameData.totalize (fun q : U => f q i)) p.val v +
        ∑ j, connectionForm C b p i j v * f p j


def local_transition_inverseType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) {U : Set M} {hU : IsOpen U} (b c : LocalFrame B U hU),
  ∀ (p : U),
  localTransition b c p * localTransition c b p = 1 ∧
      localTransition c b p * localTransition b c p = 1


def localTransition_smoothType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) {U : Set M} {hU : IsOpen U} (b c : LocalFrame B U hU),
  ∀ (i j : Fin r),
  SmoothManifolds.FrameData.VectorSmooth (openSubsetAtlas S.smoothStructure.val U hU)
      (fun p => localTransition b c p i j)


def local_frame_transformationType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B) {U : Set M} {hU : IsOpen U} (b c : LocalFrame B U hU),
  ∀ (p : U) (v : TangentSpace S p.val),
  connectionMatrix C c p v =
      localTransition c b p * connectionMatrix C b p v * localTransition b c p +
        localTransition c b p * localTransitionDerivative b c p v


def act_applyType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M] {S : SmoothManifold n a M},
  ∀ (X : Field S) (f : GlobalSmooth S) (p : M),
  (act S X f).val p = (X.val p).val (SmoothManifolds.globalToGerm S p f)


def scalarDerivative_representativeType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M] {S : SmoothManifold n a M},
  ∀ (f : M → ℝ) (g : GlobalSmooth S)
    (p : M) (h : g.val =ᶠ[𝓝 p] f) (v : TangentSpace S p),
  scalarDerivative S f p v = v.val (SmoothManifolds.globalToGerm S p g)


def scalarDerivative_globalType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M] {S : SmoothManifold n a M},
  ∀ (f : GlobalSmooth S) (X : Field S) (p : M),
  scalarDerivative S f.val p (X.val p) = (act S X f).val p

end P202Specs.Geometry.ConnectionForms
