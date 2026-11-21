import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch07.ExteriorAlgebra
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.LocallyConstant.Basic

/-! Independent objects and full statements for M09.01, paper.tex 1696--1720.

The determinant fibers are the actual top exterior powers of the intrinsic
`tangentSpace` fibers. A ray is a quotient of nonzero determinant vectors by
positive rescaling. Continuity is tested in local determinant trivializations:
the ray space of a real line is discrete. The test uses every intrinsic system
of tangent coordinates, so no choice of a tangent bundle is part of an
orientation. All model kinds, dimension zero and empty bases are allowed.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SmoothManifolds.OrientationData
open ModelData AtlasData TangentData TangentBundleData BundleOperationsData
  FrameData MapData PartitionData Set Module
universe u

abbrev DeterminantLine {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (p : M) := ⋀[ℝ]^n (TangentSpace S p)

abbrev DeterminantRay {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (p : M) := Module.Ray ℝ (DeterminantLine S p)

abbrev RayField {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) := (p : M) → DeterminantRay S p

/-- Strict positivity excludes the zero determinant vector. -/
def IsPositive {V : Type u} [AddCommGroup V] [Module ℝ V]
    (r : Module.Ray ℝ V) (v : V) : Prop :=
  ∃ hv : v ≠ 0, rayOfNeZero ℝ v hv = r

/-- Actual exterior-power transport of intrinsic chart coordinates. -/
def determinantCoordinates {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    DeterminantLine S p.val ≃ₗ[ℝ] (⋀[ℝ]^n (Euclidean n)) :=
  LinearEquiv.ofBijective (exteriorPower.map n (K.equiv c hc p.val p.property).toLinearMap)
    ⟨exteriorPower.map_injective_field (K.equiv c hc p.val p.property).injective,
      exteriorPower.map_surjective (K.equiv c hc p.val p.property).surjective⟩

/-- This is continuity into the two-point ray space in each local trivialization. -/
def IsContinuousRayField {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (r : RayField S) : Prop :=
  ∀ (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val),
    IsLocallyConstant (fun p : c.source =>
      Module.Ray.map (determinantCoordinates K c hc p) (r p.val))

abbrev Orientation {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) := {r : RayField S // IsContinuousRayField r}

/-- The ordered coordinate frame, also when the index set is empty. -/
def coordinateVector {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    DeterminantLine S p.val :=
  exteriorPower.ιMulti ℝ n (fun j =>
    (K.equiv c hc p.val p.property).symm ((Pi.basisFun ℝ (Fin n)) j))

/-- Determinant coordinate of an arbitrary determinant vector. -/
def determinantCoefficient {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    DeterminantLine S p.val →ₗ[ℝ] ℝ :=
  let b : Basis (Fin n) ℝ (TangentSpace S p.val) :=
    (Pi.basisFun ℝ (Fin n)).map (K.equiv c hc p.val p.property).symm
  let A : AlternatingMap ℝ (TangentSpace S p.val) ℝ (Fin n) :=
    @Module.Basis.det ℝ _ (TangentSpace S p.val) inferInstance inferInstance (Fin n) _ _ b
  exteriorPower.alternatingMapLinearEquiv A

/-- Smoothness of a local determinant section in the induced determinant atlas.
This uses actual scalar coefficients with the ambient extension convention at
boundary points. It is not an assumed certificate of triviality. -/
def IsSmoothDeterminantSection {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (U : Set M) (hU : IsOpen U)
    (g : (p : U) → DeterminantLine S p.val) : Prop :=
  ∀ (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val),
    VectorSmooth (openSubsetAtlas S.smoothStructure.val (U ∩ c.source) (hU.inter c.open_source))
      (fun p => determinantCoefficient K c hc ⟨p.val, p.property.2⟩
        (g ⟨p.val, p.property.1⟩))

/-- Smooth generators on an open cover, with smooth positive overlap factors.
No generator or preferred positive frame is required globally. -/
structure LocalGenerators {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) where
  index : Type u
  domain : index → Set M
  isOpen_domain : ∀ i, IsOpen (domain i)
  cover : ∀ p, ∃ i, p ∈ domain i
  generator : ∀ i (p : domain i), DeterminantLine S p.val
  nonzero : ∀ i p, generator i p ≠ 0
  smooth : ∀ i, IsSmoothDeterminantSection (domain i) (isOpen_domain i) (generator i)
  overlap : ∀ i j, ∃ f : ↥(domain i ∩ domain j) → ℝ,
    VectorSmooth (openSubsetAtlas S.smoothStructure.val (domain i ∩ domain j)
      ((isOpen_domain i).inter (isOpen_domain j))) f ∧
    ∀ p, 0 < f p ∧ generator j ⟨p.val, p.property.2⟩ =
      f p • generator i ⟨p.val, p.property.1⟩

def RepresentsGenerators {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (r : RayField S) (G : LocalGenerators S) : Prop :=
  ∀ i (p : G.domain i), IsPositive (r p.val) (G.generator i p)

/-- A sign is retained even in dimension zero and in a fixed half-space model. -/
def signValue (s : Bool) : ℝ := if s then 1 else -1

/-- Derivative transition from c-coordinates to d-coordinates. -/
def transitionDeterminant {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (c d : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (p : ↥(c.source ∩ d.source)) : ℝ :=
  LinearMap.det (((K.equiv c hc p.val p.property.1).symm.trans
    (K.equiv d hd p.val p.property.2)).toLinearMap)

structure SignedCharts {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) where
  sign : ∀ c : ModelChart n a M, c ∈ S.smoothStructure.val → c.source → Bool
  locallyConstant : ∀ c hc, IsLocallyConstant (sign c hc)
  compatible : ∀ (K : FiberCoordinates S) (c d : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
    (p : ↥(c.source ∩ d.source)),
    signValue (sign d hd ⟨p.val, p.property.2⟩) =
      signValue (sign c hc ⟨p.val, p.property.1⟩) *
        SignType.sign (transitionDeterminant K c d hc hd p)

/-- Relating signed charts to the original intrinsic rays, not choosing positive
boundary charts or reflecting the half-space model. -/
def RepresentsSignedCharts {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (r : RayField S) (s : SignedCharts S) : Prop :=
  ∀ K c hc (p : c.source), IsPositive (r p.val)
    (signValue (s.sign c hc p) • coordinateVector K c hc p)

/-- Determinant-normalized dual pairing on the actual exterior powers. -/
def pairing {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (p : M) (ω : ExteriorData.Fiber (TangentSpace S p) n)
    (v : DeterminantLine S p) : ℝ := exteriorPower.pairingDual ℝ (TangentSpace S p) n ω v

def IsPositiveTopForm {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (r : RayField S) (ω : ExteriorData.Field S n) : Prop :=
  ∀ p v, IsPositive (r p) v → 0 < pairing p (ω p) v

abbrev NonvanishingTopForm {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} (D : ExteriorData.FormBundle C n) :=
  {ω : ExteriorData.Form D // ∀ p, ω.field p ≠ 0}

/-- The original quotient relation: the multiplier must be globally smooth and
strictly positive, including on the boundary. -/
def PositiveMultiple {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {D : ExteriorData.FormBundle C n}
    (α β : NonvanishingTopForm D) : Prop :=
  ∃ f : M → ℝ, VectorSmooth S.smoothStructure.val f ∧ (∀ p, 0 < f p) ∧
    ∀ p, β.val.field p = f p • α.val.field p

/-- Pointwise comparison. The theorem below proves this sign is locally constant
and reconstructs the second orientation from the first. -/
def comparison {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (o q : Orientation S) (p : M) : Bool :=
  if o.val p = q.val p then true else false

end SmoothManifolds.OrientationData

namespace Specs.SmoothManifolds.Orientations.Equivalences
open _root_.SmoothManifolds _root_.SmoothManifolds.OrientationData
  _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.AtlasData
  _root_.SmoothManifolds.TangentData _root_.SmoothManifolds.TangentBundleData
  _root_.SmoothManifolds.BundleOperationsData _root_.SmoothManifolds.FrameData
  _root_.SmoothManifolds.ExteriorData Set
universe u

/-- (a) ↔ (b), for each specified ray field, with no orientability assumption. -/
def smooth_generatorsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (r : RayField S),
    IsContinuousRayField r ↔ ∃ G : LocalGenerators S, RepresentsGenerators r G

/-- Conversely arbitrary positive-overlap generators determine a unique intrinsic
continuous ray field. This is the reconstruction direction for (b). -/
def generators_orientationType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (G : LocalGenerators S),
    ∃! o : Orientation S, RepresentsGenerators o.val G

/-- (a) ↔ (c), including uniqueness of the signed-coordinate description. -/
def signed_chartsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (r : RayField S),
    IsContinuousRayField r ↔ ∃! s : SignedCharts S, RepresentsSignedCharts r s

/-- Arbitrary compatible signed charts reconstruct a unique intrinsic
orientation. Signs are never required to come from reflected boundary charts. -/
def signed_orientationType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (s : SignedCharts S),
    ∃! o : Orientation S, RepresentsSignedCharts o.val s

/-- The sign in (c) is the sign of the actual ambient transition Jacobian. -/
def transition_jacobianType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (K : FiberCoordinates S)
    (c d : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (p : ↥(c.source ∩ d.source))
    (U : Set (Euclidean n)) (F : Euclidean n → Euclidean n),
    IsOpen U → (c p.val).val ∈ U → ContDiffOn ℝ (⊤ : ℕ∞) F U →
    (fun q => F (c q).val) =ᶠ[nhds p.val] (fun q => (d q).val) →
    transitionDeterminant K c d hc hd p = (fderiv ℝ F (c p.val).val).toLinearMap.det

/-- Every continuous ray field has a smooth positive top form, and positivity of
a smooth top form detects continuity of the ray field. -/
def positive_top_formType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (D : FormBundle C n)
    (r : RayField S),
    IsContinuousRayField r ↔ ∃ ω : NonvanishingTopForm D, IsPositiveTopForm r ω.val.field

/-- (a) ↔ (d) as an equivalence of data, with its positivity characterization.
`Quot` is the quotient generated by the displayed relation; the following
`positive_multipleType` asserts that its equality is exactly that relation. -/
def top_form_quotientType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (D : FormBundle C n),
    ∃ e : Quot (@PositiveMultiple n a M _ S C D) ≃ Orientation S,
      ∀ (ω : NonvanishingTopForm D) (p : M) (v : DeterminantLine S p),
        IsPositive ((e (Quot.mk _ ω)).val p) v ↔ 0 < pairing p (ω.val.field p) v

/-- Same orientation iff the smooth pointwise ratio is everywhere positive. -/
def positive_multipleType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (D : FormBundle C n)
    (α β : NonvanishingTopForm D),
    (Quot.mk PositiveMultiple α = Quot.mk PositiveMultiple β) ↔ PositiveMultiple α β

def comparisonType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (o q : Orientation S),
    IsLocallyConstant (comparison o q) ∧
    ∀ p, q.val p = if comparison o q p then o.val p else -o.val p

/-- Exactly two orientations on a connected nonempty orientable manifold.
The bijection is explicitly characterized as an orientation and its opposite. -/
def connected_twoType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n a M) (o : Orientation S),
    ∃ e : Bool ≃ Orientation S, e true = o ∧ ∀ p, (e false).val p = -o.val p

/-- In dimension zero the canonical Λ⁰ = ℝ identification allows an arbitrary
independent sign at each point, including an empty set of points. -/
def zero_dimensionType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M] (S : SmoothManifold 0 a M),
    ∃ e : Orientation S ≃ (M → Bool),
      ∀ (o : Orientation S) (p : M),
        (e o p = true ↔ IsPositive (o.val p)
          ((exteriorPower.zeroEquiv ℝ (TangentSpace S p)).symm 1))

/-- The empty choice exists and is unique, without a dimension restriction. -/
def emptyType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M] [IsEmpty M]
    (S : SmoothManifold n a M), Nonempty (Orientation S) ∧ Subsingleton (Orientation S)

end Specs.SmoothManifolds.Orientations.Equivalences
