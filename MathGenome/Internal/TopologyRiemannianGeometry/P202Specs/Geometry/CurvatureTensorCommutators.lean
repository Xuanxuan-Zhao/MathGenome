import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.InducedConnections
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.SecondBianchi

/-! Theorem 7.1, paper.tex 3545–3562 and 3600–3606. The mixed word
uses the actual tangent bundle and its algebraic dual; `false` is a vector
slot and `true` is a covector slot. The empty word is the scalar unit.
No metric or torsion hypothesis is needed for the commutator formulas. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace P202.TensorCommutatorData
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleData SmoothManifolds.BundleOperationsData
  P202.ConnectionData P202.InducedConnectionData
universe u v w
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  {B : SmoothVectorBundle S r ι E}

/-- The actual iterated covariant derivative commutator. -/
noncomputable def commutator (C : Connection B) (X Y : Field S) :
    Section B →ₗ[ℝ] Section B :=
  (C.cov X).comp (C.cov Y) - (C.cov Y).comp (C.cov X) -
    C.cov (P202.TorsionMetricData.bracket X Y)

/-- The negative transpose acts on covectors. -/
noncomputable def dualAction {V : Type*} [AddCommGroup V] [Module ℝ V]
    (R : V →ₗ[ℝ] V) : Module.Dual ℝ V →ₗ[ℝ] Module.Dual ℝ V := -R.dualMap

/-- A sum with exactly one curvature action in each slot. Recursive tensor
maps extend this formula linearly to every tensor, not only pure tensors. -/
noncomputable def mixedAction (E : M → Type w) [∀ p, AddCommGroup (E p)]
    [∀ p, Module ℝ (E p)] (p : M) (R : E p →ₗ[ℝ] E p) :
    (l : List Bool) → MixedFiber E l p →ₗ[ℝ] MixedFiber E l p
  | [] => 0
  | false :: l => TensorProduct.map R LinearMap.id +
      TensorProduct.map LinearMap.id (mixedAction E p R l)
  | true :: l => TensorProduct.map (dualAction R) LinearMap.id +
      TensorProduct.map LinearMap.id (mixedAction E p R l)
end P202.TensorCommutatorData

namespace P202Specs.Geometry.CurvatureTensorCommutators
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleData SmoothManifolds.BundleOperationsData
  P202.ConnectionData P202.InducedConnectionData P202.CurvatureData
  P202.TensorCommutatorData
universe u

def dual_commutatorType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : Connection (tangentBundle S))
    (T : CurvatureTensor S), RepresentsCurvature C T →
    ∀ (D : DualBundle (tangentBundle S)), letI := D.space.topology
    ∀ (K : Connection D.space.bundle), DualRule C D K →
    ∀ (X Y : Field S) (lam : Section D.space.bundle) (p : M)
      (z : TangentSpace S p),
      ((commutator K X Y lam).val p) z =
        -lam.val p (T.val p (X.val p) (Y.val p) z)

/-- Universal statement for every induced mixed family and every smooth
section, in all finite dimensions and including the empty tensor word. -/
def mixed_commutatorType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : Connection (tangentBundle S))
    (T : CurvatureTensor S), RepresentsCurvature C T →
    let B := tangentBundle S
    letI := (mixedDualBundle B).space.topology
    ∀ (D : Connection (mixedDualBundle B).space.bundle) (K : MixedConnections B),
    MixedFamilyRule B C D K →
    ∀ (l : List Bool), letI := (mixedBundle B l).topology
    ∀ (X Y : Field S) (s : Section (mixedBundle B l).bundle) (p : M),
      (commutator (K l) X Y s).val p =
        mixedAction (TangentSpace S) p (T.val p (X.val p) (Y.val p)) l (s.val p)

/-- Contraction compatibility of the commutator on arbitrary sections at
any selected dual/primal pair. The hypothesis is compatibility of the first
derivative, supplied by the upstream induced-connection construction. -/
def mixed_contractionType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (K : MixedConnections (tangentBundle S)),
    MixedContractionRule (tangentBundle S) K →
    ∀ {l k j : List Bool} (hd : TensorSlot true l k) (hp : TensorSlot false k j),
    letI := (mixedBundle (tangentBundle S) l).topology
    letI := (mixedBundle (tangentBundle S) j).topology
    ∀ (X Y : Field S) (s : Section (mixedBundle (tangentBundle S) l).bundle)
      (u : Section (mixedBundle (tangentBundle S) j).bundle),
      (∀ p, u.val p = tensorContractSlots (TangentSpace S) hd hp p (s.val p)) →
      ∀ p, (commutator (K j) X Y u).val p =
        tensorContractSlots (TangentSpace S) hd hp p ((commutator (K l) X Y s).val p)

/-- Existence with the full commutator and contraction rules, so the
universal formulas above are realized for every original connection. -/
def induced_calculusType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : Connection (tangentBundle S))
    (T : CurvatureTensor S), RepresentsCurvature C T →
    let B := tangentBundle S
    letI := (mixedDualBundle B).space.topology
    ∃ D : Connection (mixedDualBundle B).space.bundle,
    ∃ K : MixedConnections B,
      MixedFamilyRule B C D K ∧ MixedContractionRule B K ∧
      (∀ (l : List Bool), letI := (mixedBundle B l).topology
       ∀ (X Y : Field S) (s : Section (mixedBundle B l).bundle) (p : M),
        (commutator (K l) X Y s).val p =
          mixedAction (TangentSpace S) p (T.val p (X.val p) (Y.val p)) l (s.val p))


/-- The signed curvature action itself commutes with every natural slot
contraction on every tensor in every fiber. -/
def curvature_contractionType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : Connection (tangentBundle S))
    (T : CurvatureTensor S), RepresentsCurvature C T →
    ∀ {l k j : List Bool} (hd : TensorSlot true l k) (hp : TensorSlot false k j)
      (p : M) (x y : TangentSpace S p) (t : MixedFiber (TangentSpace S) l p),
      tensorContractSlots (TangentSpace S) hd hp p (mixedAction (TangentSpace S) p (T.val p x y) l t) =
        mixedAction (TangentSpace S) p (T.val p x y) j
          (tensorContractSlots (TangentSpace S) hd hp p t)

/-- The complete curvature theorem, all clauses using the same connection,
curvature convention, actual tangent fibers and induced tensor calculus. -/
def complete_curvatureType : Prop :=
  P202Specs.Geometry.CurvatureAlgebra.tensorialType.{u} ∧
  P202Specs.Geometry.CurvatureAlgebra.tensor_exists_uniqueType.{u} ∧
  P202Specs.Geometry.CurvatureAlgebra.symmetriesType.{u} ∧
  P202Specs.Geometry.CurvatureAlgebra.first_bianchiType.{u} ∧
  P202Specs.Geometry.SecondBianchi.second_bianchiType.{u} ∧
  dual_commutatorType.{u} ∧ mixed_commutatorType.{u} ∧
  mixed_contractionType.{u} ∧ induced_calculusType.{u} ∧ curvature_contractionType.{u}
end P202Specs.Geometry.CurvatureTensorCommutators
