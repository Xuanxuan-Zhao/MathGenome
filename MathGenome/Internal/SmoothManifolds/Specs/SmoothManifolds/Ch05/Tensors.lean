import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.BundleOperations
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.Covectors
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.PiTensorProduct.Dual
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-! Independent working interface for M05.07, paper.tex 1331--1336.

The fibers are actual algebraic tensor products. The first r factors are tangent
vectors; the last s factors are covectors. Evaluation takes r covectors and s
vectors. The declarations here cover the algebraic interpretation and transport
laws, induced bundle structures, smooth tensor operations and pullbacks.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

namespace SmoothManifolds.TensorData
open ModelData AtlasData MapData TangentData DifferentialData
open scoped TensorProduct
universe u v

abbrev Power (V : Type u) [AddCommMonoid V] [Module ℝ V] (k : ℕ) :=
  ⨂[ℝ] (_ : Fin k), V

/-- The source's (TM)^⊗r ⊗ (T*M)^⊗s, including the scalar zeroth powers. -/
abbrev Fiber (V : Type u) [AddCommMonoid V] [Module ℝ V] (r s : ℕ) :=
  Power V r ⊗[ℝ] Power (Module.Dual ℝ V) s

/-- Negation is scalar multiplication by -1; this instance preserves the
original additive monoid used by the algebraic tensor construction. -/
instance fiberAddCommGroup (V : Type u) [AddCommMonoid V] [Module ℝ V] (r s : ℕ) :
    AddCommGroup (Fiber V r s) := Module.addCommMonoidToAddCommGroup ℝ

abbrev Factor (V : Type u) [AddCommMonoid V] [Module ℝ V] (r s : ℕ)
    (i : Fin r ⊕ Fin s) : Type u :=
  match i with
  | .inl _ => V
  | .inr _ => Module.Dual ℝ V

abbrev Argument (V : Type u) [AddCommMonoid V] [Module ℝ V] (r s : ℕ)
    (i : Fin r ⊕ Fin s) : Type u :=
  match i with
  | .inl _ => Module.Dual ℝ V
  | .inr _ => V

instance factorAddCommMonoid (V : Type u) [AddCommMonoid V] [Module ℝ V]
    (r s : ℕ) (i : Fin r ⊕ Fin s) : AddCommMonoid (Factor V r s i) :=
  match i with
  | .inl _ => inferInstanceAs (AddCommMonoid V)
  | .inr _ => inferInstanceAs (AddCommMonoid (Module.Dual ℝ V))
instance factorModule (V : Type u) [AddCommMonoid V] [Module ℝ V]
    (r s : ℕ) (i : Fin r ⊕ Fin s) : Module ℝ (Factor V r s i) :=
  match i with
  | .inl _ => inferInstanceAs (Module ℝ V)
  | .inr _ => inferInstanceAs (Module ℝ (Module.Dual ℝ V))
instance argumentAddCommMonoid (V : Type u) [AddCommMonoid V] [Module ℝ V]
    (r s : ℕ) (i : Fin r ⊕ Fin s) : AddCommMonoid (Argument V r s i) :=
  match i with
  | .inl _ => inferInstanceAs (AddCommMonoid (Module.Dual ℝ V))
  | .inr _ => inferInstanceAs (AddCommMonoid V)
instance argumentModule (V : Type u) [AddCommMonoid V] [Module ℝ V]
    (r s : ℕ) (i : Fin r ⊕ Fin s) : Module ℝ (Argument V r s i) :=
  match i with
  | .inl _ => inferInstanceAs (Module ℝ (Module.Dual ℝ V))
  | .inr _ => inferInstanceAs (Module ℝ V)

noncomputable def pure {V : Type u} [AddCommMonoid V] [Module ℝ V] {r s : ℕ}
    (v : Fin r → V) (lam : Fin s → Module.Dual ℝ V) : Fiber V r s :=
  (PiTensorProduct.tprod ℝ v) ⊗ₜ[ℝ] (PiTensorProduct.tprod ℝ lam)

/-- Evaluation on individual factors uses the canonical double-dual map. -/
def factorEvaluation (V : Type u) [AddCommMonoid V] [Module ℝ V] (r s : ℕ) :
    (i : Fin r ⊕ Fin s) → Factor V r s i →ₗ[ℝ] Module.Dual ℝ (Argument V r s i) :=
  fun i => by
    cases i with
    | inl _ => exact Module.Dual.eval ℝ V
    | inr _ => exact LinearMap.id

/-- This map needs no finite-dimensionality assumption. Its bijectivity on the
manuscript's tangent fibers is a theorem, rather than a certificate in the data. -/
noncomputable def evaluate (V : Type u) [AddCommMonoid V] [Module ℝ V] (r s : ℕ) :
    Fiber V r s →ₗ[ℝ] MultilinearMap ℝ (Argument V r s) ℝ :=
  (PiTensorProduct.lift.symm : Module.Dual ℝ (⨂[ℝ] i, Argument V r s i) ≃ₗ[ℝ]
      MultilinearMap ℝ (Argument V r s) ℝ).toLinearMap ∘ₗ
    PiTensorProduct.dualDistrib ∘ₗ PiTensorProduct.map (factorEvaluation V r s) ∘ₗ
      (PiTensorProduct.tmulEquivDep ℝ (Factor V r s)).toLinearMap

/-- Evaluation of a covariant tensor on its vector arguments. -/
noncomputable def covariantEvaluate (V : Type u) [AddCommMonoid V] [Module ℝ V]
    (s : ℕ) : Power (Module.Dual ℝ V) s →ₗ[ℝ]
      MultilinearMap ℝ (fun _ : Fin s => V) ℝ :=
  PiTensorProduct.lift.symm.toLinearMap.comp PiTensorProduct.dualDistrib

/-- The scalar zeroth contravariant power is a genuine tensor unit. -/
noncomputable def covariantEquiv (V : Type u) [AddCommMonoid V] [Module ℝ V]
    (s : ℕ) : Fiber V 0 s ≃ₗ[ℝ] Power (Module.Dual ℝ V) s :=
  (TensorProduct.congr (PiTensorProduct.isEmptyEquiv (R := ℝ) (s := fun _ : Fin 0 => V) (Fin 0))
    (LinearEquiv.refl ℝ _)).trans (TensorProduct.lid ℝ _)

/-- Covariant pullback exists for any linear differential, without an inverse. -/
noncomputable def covariantTransport {V : Type u} {W : Type v}
    [AddCommMonoid V] [Module ℝ V] [AddCommMonoid W] [Module ℝ W]
    (s : ℕ) (L : V →ₗ[ℝ] W) : Power (Module.Dual ℝ W) s →ₗ[ℝ]
      Power (Module.Dual ℝ V) s :=
  PiTensorProduct.map (fun _ => L.dualMap)

/-- Mixed transport uses the inverse on tangent factors and the dual on
cotangent factors. Thus its input is an equivalence, not an arbitrary map. -/
noncomputable def mixedTransport {V : Type u} {W : Type v}
    [AddCommMonoid V] [Module ℝ V] [AddCommMonoid W] [Module ℝ W]
    (r s : ℕ) (e : V ≃ₗ[ℝ] W) : Fiber W r s →ₗ[ℝ] Fiber V r s :=
  TensorProduct.map (PiTensorProduct.map (fun _ => e.symm.toLinearMap))
    (PiTensorProduct.map (fun _ => e.toLinearMap.dualMap))

/-- Like-slot permutations act on the homogeneous tensor powers. -/
noncomputable def permute (V : Type u) [AddCommMonoid V] [Module ℝ V]
    (k : ℕ) (σ : Equiv.Perm (Fin k)) : Power V k →ₗ[ℝ] Power V k :=
  (PiTensorProduct.reindex ℝ (fun _ : Fin k => V) σ).toLinearMap

/-- The real sign character, without a choice of coordinates. -/
def signScalar (k : ℕ) : Equiv.Perm (Fin k) →* ℝ :=
  (Int.castRingHom ℝ).toMonoidHom.comp ((Units.coeHom ℤ).comp Equiv.Perm.sign)

noncomputable def symmetrize (V : Type u) [AddCommMonoid V] [Module ℝ V]
    (k : ℕ) : Power V k →ₗ[ℝ] Power V k :=
  (k.factorial : ℝ)⁻¹ • ∑ σ : Equiv.Perm (Fin k), permute V k σ

noncomputable def alternate (V : Type u) [AddCommMonoid V] [Module ℝ V]
    (k : ℕ) : Power V k →ₗ[ℝ] Power V k :=
  (k.factorial : ℝ)⁻¹ • ∑ σ : Equiv.Perm (Fin k), signScalar k σ • permute V k σ

abbrev Field {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (r s : ℕ) := (p : M) → Fiber (TangentSpace S p) r s

abbrev CovariantField {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (s : ℕ) := (p : M) → Power (Module.Dual ℝ (TangentSpace S p)) s

noncomputable def covariantPullback {n m : ℕ} {a b : ModelKind} {M P : Type u}
    [TopologicalSpace M] [TopologicalSpace P]
    (S : SmoothManifold n a M) (T : SmoothManifold m b P) (f : P → M)
    (L : (p : P) → TangentSpace T p →ₗ[ℝ] TangentSpace S (f p))
    {s : ℕ} (A : CovariantField S s) : CovariantField T s :=
  fun p => covariantTransport s (L p) (A (f p))

noncomputable def mixedPullback {n m : ℕ} {a b : ModelKind} {M P : Type u}
    [TopologicalSpace M] [TopologicalSpace P]
    (S : SmoothManifold n a M) (T : SmoothManifold m b P) (f : P → M)
    (e : (p : P) → TangentSpace T p ≃ₗ[ℝ] TangentSpace S (f p))
    {r s : ℕ} (A : Field S r s) : Field T r s :=
  fun p => mixedTransport r s (e p) (A (f p))

/-- Coordinate labels for a homogeneous power, including the empty tuple. -/
noncomputable def powerIndex (d k : ℕ) : (Fin k → Fin d) ≃ Fin (d ^ k) :=
  Fintype.equivOfCardEq (by simp)

/-- The basis induced by the specified frame; no independent basis is chosen. -/
noncomputable def powerBasis {V : Type u} [AddCommMonoid V] [Module ℝ V]
    {d : ℕ} (e : V ≃ₗ[ℝ] Euclidean d) (k : ℕ) :
    Module.Basis (Fin (d ^ k)) ℝ (Power V k) :=
  (Basis.piTensorProduct (fun _ : Fin k =>
    (Pi.basisFun ℝ (Fin d)).map e.symm)).reindex (powerIndex d k)

noncomputable def powerCoordinates {V : Type u} [AddCommMonoid V] [Module ℝ V]
    {d : ℕ} (e : V ≃ₗ[ℝ] Euclidean d) (k : ℕ) :
    Power V k ≃ₗ[ℝ] Euclidean (d ^ k) := (powerBasis e k).equivFun

/-- An induced power bundle on the actual finite tensor products, using the
original chart cover. The pure-tensor formula determines each trivialization. -/
structure PowerBundle {n d : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type u}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean d) E)]
    (B : BundleData.SmoothVectorBundle S d ι E) (k : ℕ) where
  space : BundleOperationsData.BundleSpace S (d ^ k) ι (fun p => Power (E p) k)
  baseSet : letI := space.topology; ∀ i, space.bundle.baseSet i = B.baseSet i
  coordinates : letI := space.topology; ∀ i p, p ∈ B.baseSet i →
    ∀ (v : Fin k → E p) (j : Fin k → Fin d),
    ((space.bundle.trivialization i) ⟨p, PiTensorProduct.tprod ℝ v⟩).2
      (powerIndex d k j) = ∏ l, ((B.trivialization i) ⟨p, v l⟩).2 (j l)

/-- The mixed tensor bundle is formed on the original derivation fibers and
is tied to the induced tangent and cotangent tensor coordinates. -/
structure TensorBundle {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (r s : ℕ) where
  cotangent : BundleOperationsData.CotangentBundle S
  upper : letI := cotangent.realization.space.topology;
    PowerBundle cotangent.realization.space.bundle r
  lower : letI := cotangent.realization.space.topology; letI := cotangent.dual.space.topology;
    PowerBundle cotangent.dual.space.bundle s
  mixed : letI := cotangent.realization.space.topology; letI := cotangent.dual.space.topology;
    letI := upper.space.topology; letI := lower.space.topology;
    BundleOperationsData.TensorBundle upper.space.bundle lower.space.bundle

/-- The actual tensor bundle space, with its induced topology made explicit. -/
def tensorSpace {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {r s : ℕ} (B : TensorBundle S r s) :
    BundleOperationsData.BundleSpace S (n^r * n^s)
      (BundleOperationsData.TangentIndex S × BundleOperationsData.TangentIndex S)
      (fun p => Fiber (TangentSpace S p) r s) :=
  letI := B.cotangent.realization.space.topology
  letI := B.cotangent.dual.space.topology
  letI := B.upper.space.topology
  letI := B.lower.space.topology
  B.mixed.space

/-- Tensor fields are smooth sections of this induced tensor bundle. -/
def IsSmoothField {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {r s : ℕ} (B : TensorBundle S r s)
    (A : Field S r s) : Prop :=
  letI := (tensorSpace B).topology
  IsSmoothMap S (tensorSpace B).bundle.totalManifold
    (fun p => (⟨p, A p⟩ : Bundle.TotalSpace (Euclidean (n^r * n^s))
      (fun p => Fiber (TangentSpace S p) r s)))

noncomputable def optionSlotIndex (k : ℕ) : Option (Fin k) ≃ Fin 1 ⊕ Fin k where
  toFun := Option.elim' (.inl 0) (fun i => .inr i)
  invFun := Sum.elim (fun _ => none) some
  left_inv i := by cases i <;> rfl
  right_inv i := by
    cases i with
    | inl i => have hi : i = 0 := Subsingleton.elim _ _; subst i; rfl
    | inr i => rfl

noncomputable def slotIndex {k : ℕ} (p : Fin (k+1)) : Fin (k+1) ≃ Fin 1 ⊕ Fin k :=
  (finSuccEquiv' p).trans (optionSlotIndex k)

noncomputable def splitPowerAt (V : Type u) [AddCommMonoid V] [Module ℝ V]
    {k : ℕ} (p : Fin (k+1)) : Power V (k+1) ≃ₗ[ℝ] V ⊗[ℝ] Power V k :=
  (PiTensorProduct.reindex ℝ (fun _ : Fin (k+1) => V) (slotIndex p)).trans
    ((PiTensorProduct.tmulEquiv ℝ V).symm.trans
      (TensorProduct.congr (PiTensorProduct.subsingletonEquiv (R := ℝ) (s := fun _ : Fin 1 => V) 0)
        (LinearEquiv.refl ℝ _)))

noncomputable def contract (V : Type u) [AddCommMonoid V] [Module ℝ V] {r s : ℕ}
    (i : Fin (r+1)) (j : Fin (s+1)) : Fiber V (r+1) (s+1) →ₗ[ℝ] Fiber V r s :=
  (TensorProduct.lid ℝ (Fiber V r s)).toLinearMap ∘ₗ
    TensorProduct.map (TensorProduct.lift (Module.Dual.eval ℝ V)) LinearMap.id ∘ₗ
      (TensorProduct.tensorTensorTensorComm ℝ V (Power V r) (Module.Dual ℝ V)
        (Power (Module.Dual ℝ V) s)).toLinearMap ∘ₗ
        (TensorProduct.congr (splitPowerAt V i) (splitPowerAt (Module.Dual ℝ V) j)).toLinearMap

noncomputable def joinPower (V : Type u) [AddCommMonoid V] [Module ℝ V] (r s : ℕ) :
    Power V r ⊗[ℝ] Power V s ≃ₗ[ℝ] Power V (r+s) :=
  (PiTensorProduct.tmulEquiv ℝ V).trans
    (PiTensorProduct.reindex ℝ (fun _ : Fin r ⊕ Fin s => V) finSumFinEquiv)

noncomputable def tensorProductMap (V : Type u) [AddCommMonoid V] [Module ℝ V]
    (r s r' s' : ℕ) : Fiber V r s ⊗[ℝ] Fiber V r' s' →ₗ[ℝ] Fiber V (r+r') (s+s') :=
  (TensorProduct.congr (joinPower V r r') (joinPower (Module.Dual ℝ V) s s')).toLinearMap ∘ₗ
    (TensorProduct.tensorTensorTensorComm ℝ (Power V r) (Power (Module.Dual ℝ V) s)
      (Power V r') (Power (Module.Dual ℝ V) s')).toLinearMap

noncomputable def tensorMultiply (V : Type u) [AddCommMonoid V] [Module ℝ V]
    (r s r' s' : ℕ) : Fiber V r s →ₗ[ℝ] Fiber V r' s' →ₗ[ℝ] Fiber V (r+r') (s+s') :=
  TensorProduct.curry (tensorProductMap V r s r' s')

open Filter Set
open scoped Topology

/-- A smooth map with a smooth local inverse germ at every source point.
The two inverse equations hold on neighborhoods, so these are genuine local
inverse maps; continuity makes the neighborhoods open after shrinking. -/
def IsLocalDiffeomorphism {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (f : M → N) : Prop :=
  IsSmoothMap S T f ∧ ∀ p : M, ∃ g : N → M,
    ManifoldSmoothAt T.smoothStructure.val S.smoothStructure.val g (f p) ∧
      g (f p) = p ∧ (g ∘ f) =ᶠ[𝓝 p] id ∧ (f ∘ g) =ᶠ[𝓝 (f p)] id


noncomputable def mixedPermute (V : Type u) [AddCommMonoid V] [Module ℝ V]
    (r s : ℕ) (σ : Equiv.Perm (Fin r)) (τ : Equiv.Perm (Fin s)) :
    Fiber V r s →ₗ[ℝ] Fiber V r s :=
  TensorProduct.map (permute V r σ) (permute (Module.Dual ℝ V) s τ)

noncomputable def mixedSymmetrizeUpper (V : Type u) [AddCommMonoid V] [Module ℝ V]
    (r s : ℕ) : Fiber V r s →ₗ[ℝ] Fiber V r s :=
  TensorProduct.map (symmetrize V r) LinearMap.id
noncomputable def mixedAlternateUpper (V : Type u) [AddCommMonoid V] [Module ℝ V]
    (r s : ℕ) : Fiber V r s →ₗ[ℝ] Fiber V r s :=
  TensorProduct.map (alternate V r) LinearMap.id
noncomputable def mixedSymmetrizeLower (V : Type u) [AddCommMonoid V] [Module ℝ V]
    (r s : ℕ) : Fiber V r s →ₗ[ℝ] Fiber V r s :=
  TensorProduct.map LinearMap.id (symmetrize (Module.Dual ℝ V) s)
noncomputable def mixedAlternateLower (V : Type u) [AddCommMonoid V] [Module ℝ V]
    (r s : ℕ) : Fiber V r s →ₗ[ℝ] Fiber V r s :=
  TensorProduct.map LinearMap.id (alternate (Module.Dual ℝ V) s)

/-- The actual covariant-power factor in an induced mixed tensor bundle. -/
def covariantSpace {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {s : ℕ} (B : TensorBundle S 0 s) :
    BundleOperationsData.BundleSpace S (n^s) (BundleOperationsData.TangentIndex S)
      (fun p => Power (Module.Dual ℝ (TangentSpace S p)) s) :=
  letI := B.cotangent.realization.space.topology
  letI := B.cotangent.dual.space.topology
  B.lower.space
/-- Covariant pullback on the manuscript's full tensor fibers, using the
canonical tensor-unit equivalence rather than dropping a factor by definition. -/
noncomputable def covariantTensorPullback
    {n m : ℕ} {a b : ModelKind} {M P : Type u}
    [TopologicalSpace M] [TopologicalSpace P]
    (S : SmoothManifold n a M) (T : SmoothManifold m b P) (f : P → M)
    (L : (p : P) → TangentSpace T p →ₗ[ℝ] TangentSpace S (f p))
    {s : ℕ} (A : Field S 0 s) : Field T 0 s :=
  fun p => (covariantEquiv (TangentSpace T p) s).symm
    (covariantPullback S T f L (fun q => covariantEquiv (TangentSpace S q) s (A q)) p)


end SmoothManifolds.TensorData

namespace Specs.SmoothManifolds.Ch05.Tensors
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.TangentData _root_.SmoothManifolds.DifferentialData
  _root_.SmoothManifolds.TensorData
open _root_.SmoothManifolds.BundleData _root_.SmoothManifolds.CovectorData
open scoped TensorProduct
universe u v w z t q

/-- The usual multilinear interpretation is an isomorphism on every full tangent
fiber, also at boundary points and in dimension zero. -/
def fiber_interpretationType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (p : M) (r s : ℕ),
    Function.Bijective (evaluate (TangentSpace S p) r s)

/-- Pure tensors evaluate by the product of the indicated canonical pairings. -/
def pure_evaluationType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (p : M) (r s : ℕ)
    (v : Fin r → TangentSpace S p) (lam : Fin s → Module.Dual ℝ (TangentSpace S p))
    (α : Fin r → Module.Dual ℝ (TangentSpace S p)) (w : Fin s → TangentSpace S p),
    evaluate (TangentSpace S p) r s (pure v lam) (Sum.rec α w) =
      (∏ i, α i (v i)) * ∏ j, lam j (w j)

/-- Pointwise identity law for the genuine differential, for arbitrary tensor
fields; it will in particular apply to smooth fields once smoothness is proved. -/
def covariant_pullback_idType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (s : ℕ)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace S p),
    (∀ p, IsDifferential S S id p (L p)) → ∀ A : CovariantField S s,
      covariantPullback S S id L A = A

def covariant_pullback_compType : Prop :=
  ∀ {n m k : ℕ} {a b c : ModelKind} {M P Q : Type u}
    [TopologicalSpace M] [TopologicalSpace P] [TopologicalSpace Q]
    (S : SmoothManifold n a M) (T : SmoothManifold m b P)
    (U : SmoothManifold k c Q) (f : P → M) (g : Q → P),
    IsSmoothMap T S f → IsSmoothMap U T g → ∀ (s : ℕ)
    (L : (p : P) → TangentSpace T p →ₗ[ℝ] TangentSpace S (f p))
    (K : (q : Q) → TangentSpace U q →ₗ[ℝ] TangentSpace T (g q))
    (H : (q : Q) → TangentSpace U q →ₗ[ℝ] TangentSpace S (f (g q))),
    (∀ p, IsDifferential T S f p (L p)) →
    (∀ q, IsDifferential U T g q (K q)) →
    (∀ q, IsDifferential U S (f ∘ g) q (H q)) → ∀ A : CovariantField S s,
    covariantPullback S U (f ∘ g) H A =
      covariantPullback T U g K (covariantPullback S T f L A)

/-- The defining formula on arbitrary covariant tensors, with no assumption
that a differential is invertible. -/
def covariant_pullback_applyType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M P : Type u}
    [TopologicalSpace M] [TopologicalSpace P]
    (S : SmoothManifold n a M) (T : SmoothManifold m b P) (f : P → M)
    (L : (p : P) → TangentSpace T p →ₗ[ℝ] TangentSpace S (f p))
    (s : ℕ) (A : CovariantField S s) (p : P) (v : Fin s → TangentSpace T p),
    covariantEvaluate (TangentSpace T p) s (covariantPullback S T f L A p) v =
      covariantEvaluate (TangentSpace S (f p)) s (A (f p)) (fun i => L p (v i))

/-- No arbitrary vector-space isomorphism is treated as a differential. -/
def mixed_pullback_idType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (r s : ℕ)
    (e : (p : M) → TangentSpace S p ≃ₗ[ℝ] TangentSpace S p),
    (∀ p, IsDifferential S S id p (e p).toLinearMap) → ∀ A : Field S r s,
      mixedPullback S S id e A = A

def mixed_pullback_compType : Prop :=
  ∀ {n m k : ℕ} {a b c : ModelKind} {M P Q : Type u}
    [TopologicalSpace M] [TopologicalSpace P] [TopologicalSpace Q]
    (S : SmoothManifold n a M) (T : SmoothManifold m b P)
    (U : SmoothManifold k c Q) (f : P → M) (g : Q → P),
    IsSmoothMap T S f → IsSmoothMap U T g → ∀ (r s : ℕ)
    (e : (p : P) → TangentSpace T p ≃ₗ[ℝ] TangentSpace S (f p))
    (d : (q : Q) → TangentSpace U q ≃ₗ[ℝ] TangentSpace T (g q))
    (h : (q : Q) → TangentSpace U q ≃ₗ[ℝ] TangentSpace S (f (g q))),
    (∀ p, IsDifferential T S f p (e p).toLinearMap) →
    (∀ q, IsDifferential U T g q (d q).toLinearMap) →
    (∀ q, IsDifferential U S (f ∘ g) q (h q).toLinearMap) → ∀ A : Field S r s,
    mixedPullback S U (f ∘ g) h A =
      mixedPullback T U g d (mixedPullback S T f e A)

/-- The normalized averages project onto exactly the symmetric and
alternating subspaces; this statement includes k=0 and k=1. Smoothness of the associated bundle maps is specified separately below. -/
def averaging_projectionsType : Prop :=
  ∀ (V : Type u) [AddCommMonoid V] [Module ℝ V] (k : ℕ),
    (∀ x, (∀ σ, permute V k σ (symmetrize V k x) = symmetrize V k x) ∧
      (∀ σ, permute V k σ (alternate V k x) = signScalar k σ • alternate V k x) ∧
      symmetrize V k (symmetrize V k x) = symmetrize V k x ∧
      alternate V k (alternate V k x) = alternate V k x) ∧
    (∀ x, (∀ σ, permute V k σ x = x) → symmetrize V k x = x) ∧
    (∀ x, (∀ σ, permute V k σ x = signScalar k σ • x) → alternate V k x = x)

/-- Induced tensor powers exist for every degree, with no positive rank
or nonempty-base hypothesis. -/
def exists_powerBundleType : Prop :=
  ∀ {n d : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type u} {E : M → Type u}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean d) E)]
    (B : BundleData.SmoothVectorBundle S d ι E) (k : ℕ), Nonempty (PowerBundle B k)

def exists_tensorBundleType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (r s : ℕ), Nonempty (TensorBundle S r s)


/-- Canonical contraction evaluates the chosen tangent/cotangent pair and keeps
all residual factors in their original order. -/
def contraction_evaluationType : Prop :=
  ∀ (V : Type u) [AddCommMonoid V] [Module ℝ V] {r s : ℕ}
    (i : Fin (r+1)) (j : Fin (s+1)) (v : Fin (r+1) → V)
    (lam : Fin (s+1) → Module.Dual ℝ V),
    contract V i j (pure v lam) =
      lam j (v i) • pure (fun k => v (i.succAbove k)) (fun l => lam (j.succAbove l))

/-- Tensor multiplication concatenates both ordered lists of factors. -/
def tensor_product_evaluationType : Prop :=
  ∀ (V : Type u) [AddCommMonoid V] [Module ℝ V] (r s r' s' : ℕ)
    (v : Fin r → V) (lam : Fin s → Module.Dual ℝ V)
    (w : Fin r' → V) (mu : Fin s' → Module.Dual ℝ V),
    tensorMultiply V r s r' s' (pure v lam) (pure w mu) =
      pure (Fin.append v w) (Fin.append lam mu)

/-- These laws hold for every linear equivalence; specializing to the actual
differential equivalences below gives naturality along local diffeomorphisms. -/
def mixed_transport_naturalityType : Prop :=
  ∀ (V : Type u) (W : Type u) [AddCommMonoid V] [Module ℝ V]
    [AddCommMonoid W] [Module ℝ W] (e : V ≃ₗ[ℝ] W),
    (∀ (r s : ℕ) (i : Fin (r+1)) (j : Fin (s+1)) (A : Fiber W (r+1) (s+1)),
      contract V i j (mixedTransport (r+1) (s+1) e A) =
        mixedTransport r s e (contract W i j A)) ∧
    (∀ (r s r' s' : ℕ) (A : Fiber W r s) (B : Fiber W r' s'),
      mixedTransport (r+r') (s+s') e (tensorMultiply W r s r' s' A B) =
        tensorMultiply V r s r' s' (mixedTransport r s e A) (mixedTransport r' s' e B))

/-- A local diffeomorphism supplies genuine differential equivalences, without
requiring them among its hypotheses. -/
def local_diffeomorphism_differentialType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (f : M → N),
    IsLocalDiffeomorphism S T f →
      ∃ e : (p : M) → TangentSpace S p ≃ₗ[ℝ] TangentSpace T (f p),
        ∀ p, IsDifferential S T f p (e p).toLinearMap

/-- Permutations and the two averaging operators are smooth on the actual
induced power bundles, including the scalar zeroth power. -/
def power_operations_smoothType : Prop :=
  ∀ {n d : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type u} {E : M → Type u}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean d) E)]
    (B : SmoothVectorBundle S d ι E) {k : ℕ} (P : PowerBundle B k),
    letI := P.space.topology
    (∀ σ, IsSmoothMap P.space.bundle.totalManifold P.space.bundle.totalManifold
      (fun q => (⟨q.proj, permute (E q.proj) k σ q.snd⟩ :
        Bundle.TotalSpace (Euclidean (d^k)) (fun p => Power (E p) k)))) ∧
    IsSmoothMap P.space.bundle.totalManifold P.space.bundle.totalManifold
      (fun q => (⟨q.proj, symmetrize (E q.proj) k q.snd⟩ :
        Bundle.TotalSpace (Euclidean (d^k)) (fun p => Power (E p) k))) ∧
    IsSmoothMap P.space.bundle.totalManifold P.space.bundle.totalManifold
      (fun q => (⟨q.proj, alternate (E q.proj) k q.snd⟩ :
        Bundle.TotalSpace (Euclidean (d^k)) (fun p => Power (E p) k)))

/-- Every smooth map has the ordinary pullback bundle with the original tensor
fibers at its image, without a hypothesis of differential invertibility. -/
def exists_tensorPullbackBundleType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M P : Type u}
    [TopologicalSpace M] [TopologicalSpace P]
    (S : SmoothManifold n a M) (T : SmoothManifold m b P) (f : P → M),
    IsSmoothMap T S f → ∀ (r s : ℕ) (B : TensorBundle S r s),
    letI := B.cotangent.realization.space.topology
    letI := B.cotangent.dual.space.topology
    letI := B.upper.space.topology
    letI := B.lower.space.topology
    letI := B.mixed.space.topology
    Nonempty (BundleOperationsData.PullbackBundle B.mixed.space.bundle T f)

def tensor_operation_smoothType : Prop :=
  ∀     {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {κ : Type t}
    {E : M → Type w} {F : M → Type z}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean s) F)]
    (B : SmoothVectorBundle S r ι E) (D : SmoothVectorBundle S s κ F)
    (P : BundleOperationsData.TensorBundle B D)
    {m : ℕ} {b : ModelKind} {X : Type q} [TopologicalSpace X]
    (U : SmoothManifold m b X) (f : X → M)
    (v : (x : X) → E (f x)) (w : (x : X) → F (f x))
    (hv : IsSmoothMap U B.totalManifold (fun x => ⟨f x, v x⟩))
    (hw : IsSmoothMap U D.totalManifold (fun x => ⟨f x, w x⟩)),
    letI := P.space.topology
    IsSmoothMap U P.space.bundle.totalManifold
      (fun x => (⟨f x, (v x) ⊗ₜ[ℝ] (w x)⟩ :
        Bundle.TotalSpace (Euclidean (r*s)) (fun p => E p ⊗[ℝ] F p)))

def contraction_smoothType : Prop :=
  ∀ {n r s : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (B : TensorData.TensorBundle S (r+1) (s+1)) (D : TensorData.TensorBundle S r s)
    (i : Fin (r+1)) (j : Fin (s+1)),
    letI := (tensorSpace B).topology
    letI := (tensorSpace D).topology
    IsSmoothMap (tensorSpace B).bundle.totalManifold (tensorSpace D).bundle.totalManifold
      (fun q => (⟨q.proj, contract (TangentSpace S q.proj) i j q.snd⟩ :
        Bundle.TotalSpace (Euclidean (n^r * n^s))
          (fun p => Fiber (TangentSpace S p) r s)))

def tensor_multiplication_smoothType : Prop :=
  ∀     {n r s r' s' : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M}
    (A : TensorData.TensorBundle S r s) (B : TensorData.TensorBundle S r' s')
    (C : TensorData.TensorBundle S (r+r') (s+s'))
    {m : ℕ} {b : ModelKind} {X : Type v} [TopologicalSpace X]
    (U : SmoothManifold m b X) (f : X → M)
    (x : (t : X) → Fiber (TangentSpace S (f t)) r s)
    (y : (t : X) → Fiber (TangentSpace S (f t)) r' s')
    (hx : letI := (tensorSpace A).topology
      IsSmoothMap U (tensorSpace A).bundle.totalManifold (fun t => ⟨f t, x t⟩))
    (hy : letI := (tensorSpace B).topology
      IsSmoothMap U (tensorSpace B).bundle.totalManifold (fun t => ⟨f t, y t⟩)),
    letI := (tensorSpace C).topology
    IsSmoothMap U (tensorSpace C).bundle.totalManifold
      (fun t => (⟨f t, tensorMultiply (TangentSpace S (f t)) r s r' s' (x t) (y t)⟩ :
        Bundle.TotalSpace (Euclidean (n^(r+r')*n^(s+s')))
          (fun p => Fiber (TangentSpace S p) (r+r') (s+s'))))

def covariant_pullback_smoothType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M P : Type u}
    [TopologicalSpace M] [TopologicalSpace P]
    (S : SmoothManifold n a M) (T : SmoothManifold m b P)
    (C : _root_.SmoothManifolds.BundleOperationsData.CotangentBundle S)
    (D : _root_.SmoothManifolds.BundleOperationsData.CotangentBundle T) (s : ℕ)
    (U : letI := (cotangentSpace C).topology; PowerBundle (cotangentSpace C).bundle s)
    (V : letI := (cotangentSpace D).topology; PowerBundle (cotangentSpace D).bundle s)
    (f : P → M) (hf : IsSmoothMap T S f)
    (L : (p : P) → TangentSpace T p →ₗ[ℝ] TangentSpace S (f p))
    (hL : ∀ p, IsDifferential T S f p (L p)),
    letI := (cotangentSpace C).topology
    letI := (cotangentSpace D).topology
    letI := U.space.topology
    letI := V.space.topology
    ∀ A : CovariantField S s,
      IsSmoothMap S U.space.bundle.totalManifold
        (fun p => (⟨p,A p⟩ : Bundle.TotalSpace (Euclidean (n^s))
          (fun p => Power (Module.Dual ℝ (TangentSpace S p)) s))) →
      IsSmoothMap T V.space.bundle.totalManifold
        (fun p => (⟨p,covariantPullback S T f L A p⟩ : Bundle.TotalSpace (Euclidean (m^s))
          (fun p => Power (Module.Dual ℝ (TangentSpace T p)) s)))

def mixed_pullback_smoothType : Prop :=
  ∀ {n m r s : ℕ} {a b : ModelKind} {M P : Type u}
    [TopologicalSpace M] [TopologicalSpace P]
    (S : SmoothManifold n a M) (T : SmoothManifold m b P)
    (B : TensorData.TensorBundle S r s) (C : TensorData.TensorBundle T r s)
    (f : P → M) (hf : IsLocalDiffeomorphism T S f)
    (F : (p : P) → TangentSpace T p ≃ₗ[ℝ] TangentSpace S (f p))
    (hF : ∀ p, IsDifferential T S f p (F p).toLinearMap)
    (A : Field S r s) (hA : IsSmoothField B A),
    IsSmoothField C (mixedPullback S T f F A)



/-- Smooth bundle endomorphisms on both kinds of like slots. -/
def mixed_operations_smoothType : Prop :=
  ∀ {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TensorBundle S r s),
    letI := (tensorSpace B).topology
    (∀ (σ : Equiv.Perm (Fin r)) (τ : Equiv.Perm (Fin s)), IsSmoothMap (tensorSpace B).bundle.totalManifold (tensorSpace B).bundle.totalManifold
      (fun q => (⟨q.proj, mixedPermute (TangentSpace S q.proj) r s σ τ q.snd⟩ :
        Bundle.TotalSpace (Euclidean (n^r*n^s)) (fun p => Fiber (TangentSpace S p) r s)))) ∧
    (IsSmoothMap (tensorSpace B).bundle.totalManifold (tensorSpace B).bundle.totalManifold
      (fun q => (⟨q.proj, mixedSymmetrizeUpper (TangentSpace S q.proj) r s q.snd⟩ :
        Bundle.TotalSpace (Euclidean (n^r*n^s)) (fun p => Fiber (TangentSpace S p) r s)))) ∧
    (IsSmoothMap (tensorSpace B).bundle.totalManifold (tensorSpace B).bundle.totalManifold
      (fun q => (⟨q.proj, mixedAlternateUpper (TangentSpace S q.proj) r s q.snd⟩ :
        Bundle.TotalSpace (Euclidean (n^r*n^s)) (fun p => Fiber (TangentSpace S p) r s)))) ∧
    (IsSmoothMap (tensorSpace B).bundle.totalManifold (tensorSpace B).bundle.totalManifold
      (fun q => (⟨q.proj, mixedSymmetrizeLower (TangentSpace S q.proj) r s q.snd⟩ :
        Bundle.TotalSpace (Euclidean (n^r*n^s)) (fun p => Fiber (TangentSpace S p) r s)))) ∧
    (IsSmoothMap (tensorSpace B).bundle.totalManifold (tensorSpace B).bundle.totalManifold
      (fun q => (⟨q.proj, mixedAlternateLower (TangentSpace S q.proj) r s q.snd⟩ :
        Bundle.TotalSpace (Euclidean (n^r*n^s)) (fun p => Fiber (TangentSpace S p) r s))))

/-- The mixed pullback itself exists and preserves smooth fields, with the
differential equivalences constructed from the local diffeomorphism. -/
def mixed_pullback_existsType : Prop :=
  ∀ {n m r s : ℕ} {a b : ModelKind} {M P : Type u}
    [TopologicalSpace M] [TopologicalSpace P]
    (S : SmoothManifold n a M) (T : SmoothManifold m b P)
    (B : TensorBundle S r s) (C : TensorBundle T r s) (f : P → M),
    IsLocalDiffeomorphism T S f →
      ∃ F : (p : P) → TangentSpace T p ≃ₗ[ℝ] TangentSpace S (f p),
        (∀ p, IsDifferential T S f p (F p).toLinearMap) ∧
        ∀ A : Field S r s, IsSmoothField B A → IsSmoothField C (mixedPullback S T f F A)


def covariant_tensor_evaluationType : Prop :=
  ∀ {V : Type u} [AddCommMonoid V] [Module ℝ V] (s : ℕ)
    (A : Fiber V 0 s) (w : Fin s → V),
    evaluate V 0 s A (Sum.rec Fin.elim0 w) =
      covariantEvaluate V s (covariantEquiv V s A) w

def covariant_mixed_transportType : Prop :=
  ∀ {V : Type u} {W : Type v} [AddCommMonoid V] [Module ℝ V]
    [AddCommMonoid W] [Module ℝ W] (s : ℕ) (e : V ≃ₗ[ℝ] W),
    (covariantEquiv V s).toLinearMap.comp (mixedTransport 0 s e) =
      (covariantTransport s e.toLinearMap).comp (covariantEquiv W s).toLinearMap

def local_diffeomorphism_idType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M), IsLocalDiffeomorphism S S id

def local_diffeomorphism_compType : Prop :=
  ∀ {n m k : ℕ} {a b c : ModelKind} {M N Q : Type u}
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace Q]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (U : SmoothManifold k c Q)
    (f : M → N) (g : N → Q),
    IsLocalDiffeomorphism S T f → IsLocalDiffeomorphism T U g →
      IsLocalDiffeomorphism S U (g ∘ f)

def covariant_tensor_pullback_smoothType : Prop :=
  ∀     {n m s : ℕ} {a b : ModelKind} {M P : Type u}
    [TopologicalSpace M] [TopologicalSpace P]
    (S : SmoothManifold n a M) (T : SmoothManifold m b P)
    (B : TensorData.TensorBundle S 0 s) (C : TensorData.TensorBundle T 0 s)
    (f : P → M) (hf : IsSmoothMap T S f)
    (L : (p : P) → TangentSpace T p →ₗ[ℝ] TangentSpace S (f p))
    (hL : ∀ p, IsDifferential T S f p (L p))
    (A : Field S 0 s) (hA : IsSmoothField B A),
    IsSmoothField C (covariantTensorPullback S T f L A)

def covariant_unit_smoothType : Prop :=
  ∀ {n s : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TensorData.TensorBundle S 0 s),
    letI := (tensorSpace B).topology
    letI := (covariantSpace B).topology
    IsSmoothMap (tensorSpace B).bundle.totalManifold (covariantSpace B).bundle.totalManifold
      (fun q => (⟨q.proj, covariantEquiv (TangentSpace S q.proj) s q.snd⟩ :
        Bundle.TotalSpace (Euclidean (n^s))
          (fun p => Power (Module.Dual ℝ (TangentSpace S p)) s)))

def covariant_unit_inverse_smoothType : Prop :=
  ∀ {n s : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TensorData.TensorBundle S 0 s),
    letI := (tensorSpace B).topology
    letI := (covariantSpace B).topology
    IsSmoothMap (covariantSpace B).bundle.totalManifold (tensorSpace B).bundle.totalManifold
      (fun q => (⟨q.proj, (covariantEquiv (TangentSpace S q.proj) s).symm q.snd⟩ :
        Bundle.TotalSpace (Euclidean (n^0*n^s))
          (fun p => Fiber (TangentSpace S p) 0 s)))


def covariant_tensor_pullback_applyType : Prop :=
  ∀ {n m s : ℕ} {a b : ModelKind} {M P : Type u}
    [TopologicalSpace M] [TopologicalSpace P]
    (S : SmoothManifold n a M) (T : SmoothManifold m b P) (f : P → M)
    (L : (p : P) → TangentSpace T p →ₗ[ℝ] TangentSpace S (f p))
    (A : Field S 0 s) (p : P) (v : Fin s → TangentSpace T p) ,
    evaluate (TangentSpace T p) 0 s (covariantTensorPullback S T f L A p)
      (Sum.rec Fin.elim0 v) =
    evaluate (TangentSpace S (f p)) 0 s (A (f p))
      (Sum.rec Fin.elim0 (fun i => L p (v i)))

def covariant_tensor_pullback_idType : Prop :=
  ∀ {n s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace S p)
    (hL : ∀ p, IsDifferential S S id p (L p)) (A : Field S 0 s) ,
    covariantTensorPullback S S id L A = A

def covariant_tensor_pullback_compType : Prop :=
  ∀ {n m k s : ℕ} {a b c : ModelKind} {M P Q : Type u}
    [TopologicalSpace M] [TopologicalSpace P] [TopologicalSpace Q]
    (S : SmoothManifold n a M) (T : SmoothManifold m b P) (U : SmoothManifold k c Q)
    (f : P → M) (g : Q → P) (hf : IsSmoothMap T S f) (hg : IsSmoothMap U T g)
    (L : (p : P) → TangentSpace T p →ₗ[ℝ] TangentSpace S (f p))
    (K : (q : Q) → TangentSpace U q →ₗ[ℝ] TangentSpace T (g q))
    (H : (q : Q) → TangentSpace U q →ₗ[ℝ] TangentSpace S (f (g q)))
    (hL : ∀ p, IsDifferential T S f p (L p))
    (hK : ∀ q, IsDifferential U T g q (K q))
    (hH : ∀ q, IsDifferential U S (f ∘ g) q (H q)) (A : Field S 0 s) ,
    covariantTensorPullback S U (f ∘ g) H A =
      covariantTensorPullback T U g K (covariantTensorPullback S T f L A)

def covariant_tensor_pullback_mixedType : Prop :=
  ∀ {n m s : ℕ} {a b : ModelKind} {M P : Type u}
    [TopologicalSpace M] [TopologicalSpace P]
    (S : SmoothManifold n a M) (T : SmoothManifold m b P) (f : P → M)
    (e : (p : P) → TangentSpace T p ≃ₗ[ℝ] TangentSpace S (f p)) (A : Field S 0 s) ,
    covariantTensorPullback S T f (fun p => (e p).toLinearMap) A = mixedPullback S T f e A

def covariant_tensor_pullback_existsType : Prop :=
  ∀ {n m s : ℕ} {a b : ModelKind} {M P : Type u}
    [TopologicalSpace M] [TopologicalSpace P]
    (S : SmoothManifold n a M) (T : SmoothManifold m b P)
    (B : TensorData.TensorBundle S 0 s) (C : TensorData.TensorBundle T 0 s)
    (f : P → M) (hf : IsSmoothMap T S f) ,
    ∃ L : (p : P) → TangentSpace T p →ₗ[ℝ] TangentSpace S (f p),
      (∀ p, IsDifferential T S f p (L p)) ∧
      ∀ A : Field S 0 s, IsSmoothField B A → IsSmoothField C (covariantTensorPullback S T f L A)

end Specs.SmoothManifolds.Ch05.Tensors
