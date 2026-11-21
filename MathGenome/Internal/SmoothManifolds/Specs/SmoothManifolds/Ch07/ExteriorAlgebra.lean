import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.Tensors
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.Covectors
import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing

/-! Independent interface for M07.01 (paper.tex 1454--1469).
The exterior fibers are homogeneous parts of the actual exterior algebra of the
cotangent fibers. Smoothness is smoothness of a section into its bundle total
space, with the supplied ambient-extension convention at boundary points. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace SmoothManifolds.ExteriorData
open ModelData AtlasData MapData TangentData BundleData BundleOperationsData
  CovectorData FrameData Module Set
universe u

abbrev Fiber (V : Type u) [AddCommGroup V] [Module ℝ V] (k : ℕ) :=
  ⋀[ℝ]^k (Module.Dual ℝ V)

/-- Determinant-normalized evaluation, not normalized alternation by 1/k!. -/
def evaluate (V : Type u) [AddCommGroup V] [Module ℝ V] (k : ℕ) :
    Fiber V k →ₗ[ℝ] AlternatingMap ℝ V ℝ (Fin k) :=
  (exteriorPower.alternatingMapLinearEquiv.symm :
    Module.Dual ℝ (⋀[ℝ]^k V) ≃ₗ[ℝ] AlternatingMap ℝ V ℝ (Fin k)).toLinearMap.comp
      (exteriorPower.pairingDual ℝ V k)

/-- Multiplication of homogeneous elements of the exterior algebra. -/
abbrev wedge {V : Type u} [AddCommGroup V] [Module ℝ V] {k l : ℕ} :
    Fiber V k →ₗ[ℝ] Fiber V l →ₗ[ℝ] Fiber V (k + l) :=
  exteriorPower.wedge ℝ (Module.Dual ℝ V) k l

abbrev Index (n k : ℕ) := Set.powersetCard (Fin n) k

abbrev Field {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (k : ℕ) := (p : M) → Fiber (TangentSpace S p) k

/-- The induced exterior bundle, with its original cotangent fibers. -/
abbrev FormBundle {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ) :=
  letI := (cotangentSpace C).topology
  ExteriorBundle (cotangentSpace C).bundle k

def IsForm {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {k : ℕ}
    (D : FormBundle C k) (ω : Field S k) : Prop :=
  letI := (cotangentSpace C).topology
  letI := D.space.topology
  IsSmoothMap S D.space.bundle.totalManifold
    (fun p => (⟨p, ω p⟩ : Bundle.TotalSpace (Euclidean (n.choose k)) (fun q => Fiber (TangentSpace S q) k)))

/-- Ω^k(M), realized as the smooth sections of Λ^kT*M. -/
structure Form {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {k : ℕ} (D : FormBundle C k) where
  field : Field S k
  smooth : IsForm D field

def fieldWedge {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {k l : ℕ} (α : Field S k) (β : Field S l) : Field S (k+l) :=
  fun p => wedge (V := TangentSpace S p) (α p) (β p)

/-- Actual increasing-coordinate-wedge coefficients, on their open chart domain. -/
def coefficients {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (ω : Field S k) (p : c.source) (I : Index n k) : ℝ :=
  let b := ((Pi.basisFun ℝ (Fin n)).map
    (C.tangent.fiberCoordinates.equiv c hc p.val p.property).symm).dualBasis.exteriorPower k
  b.repr (ω p.val) I

end SmoothManifolds.ExteriorData

namespace Specs.SmoothManifolds.Ch07.ExteriorAlgebra
open _root_.SmoothManifolds _root_.SmoothManifolds.ExteriorData
  _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.AtlasData
  _root_.SmoothManifolds.MapData _root_.SmoothManifolds.TangentData
  _root_.SmoothManifolds.BundleData _root_.SmoothManifolds.BundleOperationsData
  _root_.SmoothManifolds.CovectorData _root_.SmoothManifolds.FrameData Module Set
universe u

def alternating_interpretationType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] (k : ℕ),
    Function.Bijective (evaluate V k)

/-- The same identification expressed on the actual covariant tensor powers of
M05.07, with alternation imposed on their multilinear evaluations. -/
def tensor_interpretationType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] (k : ℕ),
    Function.Bijective (TensorData.covariantEvaluate V k) ∧
    ∀ t : TensorData.Power (Module.Dual ℝ V) k,
      (∃ A : AlternatingMap ℝ V ℝ (Fin k),
        A.toMultilinearMap = TensorData.covariantEvaluate V k t) ↔
      ∃! x : Fiber V k,
        (evaluate V k x).toMultilinearMap = TensorData.covariantEvaluate V k t

def determinant_normalizationType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℝ V] (k : ℕ)
    (α : Fin k → Module.Dual ℝ V) (v : Fin k → V),
    evaluate V k (exteriorPower.ιMulti ℝ k α) v =
      (Matrix.of (fun i j => α i (v j))).det

/-- Every dual basis gives exactly the increasing-wedge basis. -/
def increasing_basisType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℝ V] (n k : ℕ)
    (b : Basis (Fin n) ℝ (Module.Dual ℝ V)),
    ∃ B : Basis (Index n k) ℝ (Fiber V k),
      ∀ I, B I = exteriorPower.ιMulti ℝ k
        (fun j => b (Set.powersetCard.ofFinEmbEquiv.symm I j))

def wedge_decomposableType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℝ V] (k l : ℕ)
    (α : Fin k → Module.Dual ℝ V) (β : Fin l → Module.Dual ℝ V),
    wedge (exteriorPower.ιMulti ℝ k α) (exteriorPower.ιMulti ℝ l β) =
      exteriorPower.ιMulti ℝ (k+l) (Fin.append α β)

/-- Coercion into the exterior algebra avoids inessential degree casts. -/
def wedge_assocType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℝ V] (k l m : ℕ)
    (α : Fiber V k) (β : Fiber V l) (γ : Fiber V m),
    (wedge (wedge α β) γ : ExteriorAlgebra ℝ (Module.Dual ℝ V)) =
      (wedge α (wedge β γ) : ExteriorAlgebra ℝ (Module.Dual ℝ V))

def wedge_commType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℝ V] (k l : ℕ)
    (α : Fiber V k) (β : Fiber V l),
    (wedge α β : ExteriorAlgebra ℝ (Module.Dual ℝ V)) =
      (-1 : ℝ)^(k*l) • (wedge β α : ExteriorAlgebra ℝ (Module.Dual ℝ V))

def degree_zeroType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℝ V], Nonempty (Fiber V 0 ≃ₗ[ℝ] ℝ)

def above_dimensionType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (k : ℕ), Module.finrank ℝ V < k → ∀ α : Fiber V k, α = 0

/-- High-degree fields vanish on every n-manifold, with no interior or
positive-dimension assumption. -/
def fields_above_dimensionType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ),
    n < k → ∀ ω : Field S k, ∀ p, ω p = 0

def exists_formBundleType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ),
    Nonempty (FormBundle C k)

def coefficient_expansionType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (ω : Field S k) (p : c.source),
    ω p.val = ∑ I : Index n k, coefficients C k c hc ω p I •
      exteriorPower.ιMulti ℝ k (fun j => coordinateCovector C.tangent.fiberCoordinates
        c hc p.val p.property (Set.powersetCard.ofFinEmbEquiv.symm I j))

def coefficients_uniqueType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (α β : Field S k),
    (∀ p I, coefficients C k c hc α p I = coefficients C k c hc β p I) →
      ∀ p : c.source, α p.val = β p.val

def smooth_iff_coefficientsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (D : FormBundle C k) (ω : Field S k),
    IsForm D ω ↔ ∀ (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (I : Index n k),
      VectorSmooth (openSubsetAtlas S.smoothStructure.val c.source c.open_source)
        (fun p => coefficients C k c hc ω p I)

def wedge_smoothType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k l : ℕ)
    (D : FormBundle C k) (E : FormBundle C l) (F : FormBundle C (k+l))
    (α : Field S k) (β : Field S l),
    IsForm D α → IsForm E β → IsForm F (fieldWedge α β)

end Specs.SmoothManifolds.Ch07.ExteriorAlgebra
