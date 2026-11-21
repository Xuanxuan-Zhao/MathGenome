import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch07.ExteriorDerivative
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.BracketFromFlow
import Mathlib.LinearAlgebra.Alternating.Curry

/-! Independent draft of M07.04, paper.tex 1533--1570.
The fibers, evaluation, smooth forms, vector fields, and bracket are those of
Chapters 5--7. All operators below are actual functions; none of their correctness
or regularity properties is included as assumed construction data.

The exterior derivative is selected from its coordinate characterization, with
zero as a default if no derivative exists. Its correctness on smooth forms is
an explicit obligation, not a certificate assumed in the Cartan statements.
The same convention makes the flow derivative a total operator. Its existence,
coordinate derivative property, and agreement with the Cartan extension are
explicit conclusions. No flow is selected for a nontangent boundary field.
-/
set_option autoImplicit false
noncomputable section

namespace SmoothManifolds.CartanData
open ModelData AtlasData TangentData TangentBundleData DifferentialData
  BundleOperationsData CovectorData ExteriorData ExteriorDerivativeData
  VectorFieldData LieBracketData MaximalFlowData Set Filter
open scoped Topology
universe u

/-- The canonical determinant-normalized identification, on the original fiber.
Finite dimensionality follows from a chart through p. -/
def evaluationEquiv {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (K : FiberCoordinates S) (p : M) (k : ℕ) :
    Fiber (TangentSpace S p) k ≃ₗ[ℝ]
      AlternatingMap ℝ (TangentSpace S p) ℝ (Fin k) := by
  let h := S.smoothStructure.property.1.1 p
  let c := Classical.choose h
  let hc := (Classical.choose_spec h).1
  let hp := (Classical.choose_spec h).2
  let e := K.equiv c hc p hp
  letI : FiniteDimensional ℝ (TangentSpace S p) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  letI : Module.Free ℝ (TangentSpace S p) :=
    Module.Free.of_basis ((Pi.basisFun ℝ (Fin n)).map e.symm)
  exact LinearEquiv.ofBijective (evaluate (TangentSpace S p) k)
    (exteriorPower.alternatingMapLinearEquiv.symm.bijective.comp
      (exteriorPower.bijective_pairingDual ℝ (TangentSpace S p) k))

/-- First-slot contraction, with the degree-zero component defined to be zero.
The natural-number degree `k-1` records the vanishing negative degree. -/
def contraction {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (X : Section S) :
    (k : ℕ) → Field S k → Field S (k-1)
  | 0, _ => 0
  | k+1, ω => fun p => (evaluationEquiv C.tangent.fiberCoordinates p k).symm
      ((evaluate (TangentSpace S p) (k+1) (ω p)).curryLeft (X p))

/-- A total selection of the coordinate exterior derivative. The zero branch
is irrelevant only once existence has been proved for the field in question. -/
def exteriorDerivative {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ) (ω : Field S k) :
    Field S (k+1) := by
  classical
  exact if h : ∃ η, HasExteriorDerivative C ω η then Classical.choose h else 0

/-- Cartan's coordinate extension to arbitrary smooth fields, including fields
not tangent to the boundary. Agreement with flow differentiation is a theorem
obligation below. Degree zero has only the `i_X d` summand. -/
def lieDerivative {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (X : Section S) :
    (k : ℕ) → Field S k → Field S k
  | 0, ω => contraction C X 1 (exteriorDerivative C 0 ω)
  | k+1, ω => exteriorDerivative C k (contraction C X (k+1) ω) +
      (by simpa only [Nat.add_sub_cancel] using
        contraction C X (k+1+1) (exteriorDerivative C (k+1) ω))

/-- Choice of the genuine forward time-map differential. This has the moving
point in its target fiber, as required for pullback of covariant tensors. -/
def timeDifferential {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (F : CurveFamily M) (t : ℝ) (p : M) :
    TangentSpace S p →ₗ[ℝ] TangentSpace S (F.curve p t) := by
  classical
  exact if h : ∃ L, IsDifferential S S (fun q => F.curve q t) p L then
    Classical.choose h else 0

/-- Actual pullback of a form by a time map. -/
def flowPullback {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (F : CurveFamily M) (t : ℝ)
    (k : ℕ) (ω : Field S k) : Field S k :=
  FormPullbackData.pullbackField S S (fun q => F.curve q t)
    (timeDifferential S F t) ω

/-- Time derivative in the fixed exterior fiber over the initial point,
tested in every chart and every ordered-wedge coefficient. -/
def HasFlowLieDerivativeOn {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (F : CurveFamily M) (k : ℕ) (ω η : Field S k) (O : Set M) : Prop :=
  ∀ (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source), p ∈ O → ∀ I : Index n k,
    HasDerivAt (fun t => coefficients C k c hc (flowPullback S F t k ω) ⟨p, hp⟩ I)
      (coefficients C k c hc η ⟨p, hp⟩ I) 0

/-- The Lie derivative as the actual derivative at zero of local-flow pullback.
The existence assertion below makes this definition independent of its default. -/
def flowLieDerivative {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (F : CurveFamily M)
    (k : ℕ) (ω : Field S k) : Field S k := by
  classical
  exact if h : ∃ η, HasFlowLieDerivativeOn C F k ω η univ then Classical.choose h else 0

/-- Evaluation on vector fields is an ordinary scalar function. -/
def fieldEvaluation {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (k : ℕ) (ω : Field S k)
    (Y : Fin k → Section S) : M → ℝ :=
  fun p => evaluate (TangentSpace S p) k (ω p) (fun i => Y i p)

/-- Intrinsic action on a locally smooth scalar function. A zero default makes
it a total definition; the evaluation theorem explicitly proves existence of
the represented smooth germ before using its action. -/
def scalarAction {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (X : Section S) (f : M → ℝ) (p : M) : ℝ := by
  classical
  exact if h : ∃ g : SmoothGerm S p, g.val = Germ.ofFun f then
    (X p).val (Classical.choose h) else 0

/-- Local flow hypotheses near time zero over O, without demanding that the
field have a two-sided flow at points outside O. In particular O may be an open
subset of the ordinary interior for a nontangent boundary field. -/
def IsLocalFlowOn {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {B : TangentBundleStructure S} (X : SmoothField B)
    (F : CurveFamily M) (O : Set M) : Prop :=
  IsOpen O ∧ ∀ p ∈ O,
    0 ∈ (F.interval p).carrier ∧ F.curve p 0 = p ∧
    BoundaryFlowData.IsIntegralCurveOn X (F.interval p).carrier (F.curve p) ∧
    ∀ t ∈ (F.interval p).carrier, BoundaryFlowData.FlowSmoothAt S F (t, p)

end SmoothManifolds.CartanData

namespace Specs.SmoothManifolds.Ch07.Cartan
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.TangentData
  _root_.SmoothManifolds.TangentBundleData _root_.SmoothManifolds.CovectorData
  _root_.SmoothManifolds.BundleOperationsData _root_.SmoothManifolds.ExteriorData
  _root_.SmoothManifolds.ExteriorDerivativeData _root_.SmoothManifolds.VectorFieldData
  _root_.SmoothManifolds.LieBracketData _root_.SmoothManifolds.MaximalFlowData
  _root_.SmoothManifolds.CartanData Set
universe u

/-- The first-slot convention in every positive degree, with no smoothness or
boundary hypothesis needed for this fiberwise statement. -/
def contraction_applyType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (X : Section S)
    (k : ℕ) (ω : Field S (k+1)) (p : M) (v : Fin k → TangentSpace S p),
    evaluate (TangentSpace S p) k (contraction C X (k+1) ω p) v =
      evaluate (TangentSpace S p) (k+1) (ω p) (Matrix.vecCons (X p) v)

def contraction_zeroType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (X : Section S)
    (ω : Field S 0), contraction C X 0 ω = 0

/-- Anticommutation includes degrees zero and one via the truncated negative
degree convention. It holds for all fields, including nontangent ones. -/
def contraction_anticommType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (X Y : Section S)
    (k : ℕ) (ω : Field S k),
    contraction C X (k-1) (contraction C Y k ω) +
      contraction C Y (k-1) (contraction C X k ω) = 0

/-- Real linearity of contraction in its form argument. -/
def contraction_linearType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (X : Section S)
    (k : ℕ) (α β : Field S k) (r : ℝ),
    contraction C X k (α+β) = contraction C X k α + contraction C X k β ∧
      contraction C X k (r • α) = r • contraction C X k α

/-- The selected derivative agrees with every actual coordinate derivative.
No global existence assertion is hidden in this bridge. -/
def exteriorDerivative_eqType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (ω : Field S k) (η : Field S (k+1)), HasExteriorDerivative C ω η →
    exteriorDerivative C k ω = η

def exteriorDerivative_zeroType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ),
    exteriorDerivative C k (0 : Field S k) = 0

/-- Regularity and the coordinate meaning of the selected d on smooth forms.
This is a bridge obligation, never an extra hypothesis of a Cartan identity. -/
def operators_smoothType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (X : SmoothField C.tangent) (k : ℕ) (ω : Field S k), IsForm (B k) ω →
      HasExteriorDerivative C ω (exteriorDerivative C k ω) ∧
      IsForm (B (k+1)) (exteriorDerivative C k ω) ∧
      IsForm (B (k-1)) (contraction C X.val k ω) ∧
      IsForm (B k) (lieDerivative C X.val k ω)

/-- Genuine flow differentiation and the Cartan formula, boundaryless case. -/
def flow_boundarylessType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (C : CotangentBundle S)
    (B : ∀ k, FormBundle C k) (X : SmoothField C.tangent) (F : CurveFamily M),
    MaximalFlowData.IsMaximalFamily X F → ∀ k ω, IsForm (B k) ω →
      HasFlowLieDerivativeOn C F k ω (flowLieDerivative C F k ω) univ ∧
      flowLieDerivative C F k ω = lieDerivative C X.val k ω

/-- A bridge for the choice definition: an actually established flow
pullback derivative uniquely determines the selected derivative. -/
def flowLieDerivative_eqType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (F : CurveFamily M)
    (k : ℕ) (ω η : Field S k), HasFlowLieDerivativeOn C F k ω η univ →
      flowLieDerivative C F k ω = η

/-- Precisely tangency of X is needed for its flow; no tangency hypothesis is
imposed on the form or on vector fields in its evaluation. -/
def flow_boundaryType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S)
    (B : ∀ k, FormBundle C k) (X : SmoothField C.tangent),
    BoundaryFlowData.IsTangentToBoundary X → ∀ F : CurveFamily M,
    BoundaryFlowData.IsMaximalFamily X F → ∀ k ω, IsForm (B k) ω →
      HasFlowLieDerivativeOn C F k ω (flowLieDerivative C F k ω) univ ∧
      flowLieDerivative C F k ω = lieDerivative C X.val k ω

/-- Local flow interpretation over any actual flow neighborhood. Thus for
arbitrary boundary fields it applies on the ordinary interior without assuming
that their flows exist at boundary points. -/
def local_flowType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S)
    (B : ∀ k, FormBundle C k) (X : SmoothField C.tangent)
    (F : CurveFamily M) (O : Set M), IsLocalFlowOn X F O →
    ∀ k ω, IsForm (B k) ω →
      HasFlowLieDerivativeOn C F k ω (lieDerivative C X.val k ω) O

/-- Ordinary commutator with d, on all smooth fields. This is also its smooth
coordinate extension to boundary points for nontangent fields. -/
def lie_commutes_dType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S)
    (B : ∀ k, FormBundle C k) (X : SmoothField C.tangent)
    (k : ℕ) (ω : Field S k), IsForm (B k) ω →
    lieDerivative C X.val (k+1) (exteriorDerivative C k ω) -
      exteriorDerivative C k (lieDerivative C X.val k ω) = 0

/-- Ordinary commutator with contraction, including functions. -/
def lie_commutes_contractionType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S)
    (B : ∀ k, FormBundle C k)
    (b : SmoothField C.tangent → SmoothField C.tangent → SmoothField C.tangent),
    BracketOperation b → ∀ (X Y : SmoothField C.tangent) (k : ℕ) (ω : Field S k),
    IsForm (B k) ω →
    lieDerivative C X.val (k-1) (contraction C Y.val k ω) -
      contraction C Y.val k (lieDerivative C X.val k ω) = contraction C (b X Y).val k ω

/-- Ordinary commutator of degree-zero Lie derivatives. -/
def lie_commutes_lieType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S)
    (B : ∀ k, FormBundle C k)
    (b : SmoothField C.tangent → SmoothField C.tangent → SmoothField C.tangent),
    BracketOperation b → ∀ (X Y : SmoothField C.tangent) (k : ℕ) (ω : Field S k),
    IsForm (B k) ω →
    lieDerivative C X.val k (lieDerivative C Y.val k ω) -
      lieDerivative C Y.val k (lieDerivative C X.val k ω) = lieDerivative C (b X Y).val k ω

/-- Full invariant evaluation formula, on all smooth fields and all ordinary
models. Smoothness of the evaluated scalar is asserted, rather than assumed. -/
def lie_evaluationType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S)
    (B : ∀ k, FormBundle C k)
    (b : SmoothField C.tangent → SmoothField C.tangent → SmoothField C.tangent),
    BracketOperation b → ∀ (X : SmoothField C.tangent) (k : ℕ)
    (ω : Field S k) (Y : Fin k → SmoothField C.tangent), IsForm (B k) ω →
    PartitionData.ScalarSmooth S.smoothStructure.val
      (fieldEvaluation k ω (fun i => (Y i).val)) ∧
    ∀ p, fieldEvaluation k (lieDerivative C X.val k ω) (fun i => (Y i).val) p =
      scalarAction X.val (fieldEvaluation k ω (fun i => (Y i).val)) p -
      ∑ i : Fin k, fieldEvaluation k ω
        (fun j => (Function.update Y i (b X (Y i)) j).val) p

end Specs.SmoothManifolds.Ch07.Cartan
