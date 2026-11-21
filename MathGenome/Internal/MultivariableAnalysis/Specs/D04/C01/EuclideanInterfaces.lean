import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Defs.Sequences
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.ClusterPt
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Independent reference objects for the D04 interface. Public `D04` declarations
are owned by the candidate module, and are checked against these objects by value.
The expected propositions below are ordinary definitions of Prop, not axioms. -/
noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace Specs.D04.C01.EuclideanInterfaces.Model

/-- The single ambient representation, including dimension zero. -/
abbrev E : ℕ → Type :=
  fun n => EuclideanSpace ℝ (Fin n)
def coordinates : (n : ℕ) → E n ≃ₗ[ℝ] (Fin n → ℝ) :=
  fun n => WithLp.linearEquiv 2 ℝ (Fin n → ℝ)
def standardBasis : (n : ℕ) → Module.Basis (Fin n) ℝ (E n) :=
  fun n => (EuclideanSpace.basisFun (Fin n) ℝ).toBasis

/-- The finite maximum of absolute coordinates; the empty maximum is zero. -/
def maxNorm : {n : ℕ} → E n → ℝ :=
  fun {n} x => ↑((Finset.univ : Finset (Fin n)).sup (fun i => ‖x i‖₊) : NNReal)
def matrixLinearEquiv : (m n : ℕ) → Matrix (Fin m) (Fin n) ℝ ≃ₗ[ℝ] (E n →ₗ[ℝ] E m) :=
  fun m n => Matrix.toEuclideanLin
def matrixOfLinearMap : {m n : ℕ} → (E n →ₗ[ℝ] E m) → Matrix (Fin m) (Fin n) ℝ :=
  fun {m n} A => (matrixLinearEquiv m n).symm A

/-- Complex coordinates are explicitly a real linear pair of coordinates. -/
def complexCoordinates : ℂ ≃ₗ[ℝ] E 2 :=
  { toFun := fun z => WithLp.toLp 2 ![z.re, z.im]
    invFun := fun x => ⟨x 0, x 1⟩
    left_inv := by intro z; rfl
    right_inv := by intro x; ext i; fin_cases i <;> rfl
    map_add' := by intro z w; ext i; fin_cases i <;> rfl
    map_smul' := by intro r z; ext i; fin_cases i <;> simp }
def ball : {n : ℕ} → E n → ℝ → Set (E n) :=
  fun a r => {x | ‖x - a‖ < r}
def Open : {n : ℕ} → Set (E n) → Prop :=
  fun U => ∀ a ∈ U, ∃ r > 0, ball a r ⊆ U
def Closed : {n : ℕ} → Set (E n) → Prop :=
  fun F => Open Fᶜ
def Interior : {n : ℕ} → Set (E n) → Set (E n) :=
  fun A => {a | ∃ r > 0, ball a r ⊆ A}
def Closure : {n : ℕ} → Set (E n) → Set (E n) :=
  fun A => {a | ∀ r > 0, ∃ x ∈ A, x ∈ ball a r}

/-- Ambient boundary, distinct from a manifold boundary. -/
def Boundary : {n : ℕ} → Set (E n) → Set (E n) :=
  fun A => Closure A \ Interior A
def relativeBall : {n : ℕ} → Set (E n) → E n → ℝ → Set (E n) :=
  fun A a r => A ∩ ball a r
def RelativeNeighborhood : {n : ℕ} → (A : Set (E n)) → A → Set (E n) → Prop :=
  fun A a N => ∃ r > 0, relativeBall A a r ⊆ N
def RelativelyOpen : {n : ℕ} → Set (E n) → Set (E n) → Prop :=
  fun A U => ∃ V, Open V ∧ U = A ∩ V
def AccumulationPoint : {n : ℕ} → Set (E n) → E n → Prop :=
  fun A a => ∀ r > 0, ∃ x ∈ A, x ≠ a ∧ x ∈ ball a r
def IsolatedPoint : {n : ℕ} → (A : Set (E n)) → A → Prop :=
  fun A a => ∃ r > 0, ∀ x ∈ A, x ∈ ball a r → x = a

/-- Accumulation is part of the assertion, so isolated points have no asserted punctured limit. -/
def RelativeLimit : {n m : ℕ} → (A : Set (E n)) → (A → E m) → E n → E m → Prop :=
  fun A f a b => AccumulationPoint A a ∧
    ∀ ε > 0, ∃ δ > 0, ∀ x : A,
      0 < ‖(x : E _) - a‖ → ‖(x : E _) - a‖ < δ → ‖f x - b‖ < ε
def RelativeContinuousAt : {n m : ℕ} → (A : Set (E n)) → (A → E m) → A → Prop :=
  fun A f a => ∀ ε > 0, ∃ δ > 0, ∀ x : A,
    ‖x.val - a.val‖ < δ → ‖f x - f a‖ < ε
def RelativeContinuous : {n m : ℕ} → (A : Set (E n)) → (A → E m) → Prop :=
  fun A f => ∀ a, RelativeContinuousAt A f a
def RelativeUniformContinuous : {n m : ℕ} → (A : Set (E n)) → (A → E m) → Prop :=
  fun A f => ∀ ε > 0, ∃ δ > 0, ∀ x y : A,
    ‖x.val - y.val‖ < δ → ‖f x - f y‖ < ε
def Compact : {n : ℕ} → Set (E n) → Prop :=
  fun K => ∀ (ι : Type) (U : ι → Set (E _)), (∀ i, Open (U i)) →
    K ⊆ ⋃ i, U i → ∃ t : Finset ι, K ⊆ ⋃ i ∈ t, U i
def SequentiallyCompact : {n : ℕ} → Set (E n) → Prop :=
  fun K => ∀ x : ℕ → E _, (∀ j, x j ∈ K) →
    ∃ a ∈ K, ∃ s : ℕ → ℕ, StrictMono s ∧ Filter.Tendsto (x ∘ s) Filter.atTop (𝓝 a)

/-- The empty-set-compatible connectedness convention. See connected_iff_no_separation. -/
def Connected : {n : ℕ} → Set (E n) → Prop :=
  fun A => IsPreconnected A
abbrev DomainPath : {n : ℕ} → (A : Set (E n)) → A → A → Type :=
  fun _ a b => Path a b
def PathConnected : {n : ℕ} → Set (E n) → Prop :=
  fun A => ∀ a b : A, Nonempty (DomainPath A a b)

/-- A finite ordered chain of segments in A, including the zero-segment constant path. -/
abbrev PolygonalPath : {n : ℕ} → (A : Set (E n)) → A → A → Type :=
  fun A a b => {p : Σ N : ℕ, Fin (N + 1) → E _ //
    p.2 0 = a ∧ p.2 (Fin.last p.1) = b ∧
    ∀ i : Fin p.1, segment ℝ (p.2 i.castSucc) (p.2 i.succ) ⊆ A}
def PolygonallyConnected : {n : ℕ} → Set (E n) → Prop :=
  fun A => ∀ a b : A, Nonempty (PolygonalPath A a b)
def ConvexSet : {n : ℕ} → Set (E n) → Prop :=
  fun A => Convex ℝ A

/-- All loops contract through loops with their basepoint fixed; path connectedness uses universal pairs. -/
def SimplyConnected : {n : ℕ} → Set (E n) → Prop :=
  fun A => PathConnected A ∧ ∀ a : A, ∀ γ : DomainPath A a a,
    Nonempty (Path.Homotopy γ (Path.refl a))
def linearOperatorNorm : {n m : ℕ} → (E n →ₗ[ℝ] E m) → ℝ :=
  fun A => sSup ((fun v => ‖A v‖) '' {v | ‖v‖ ≤ 1})
def multilinearOperatorNorm : {n m k : ℕ} → MultilinearMap ℝ (fun _ : Fin k => E n) (E m) → ℝ :=
  fun T => sSup ((fun v => ‖T v‖) '' {v | ∀ i, ‖v i‖ ≤ 1})

end Specs.D04.C01.EuclideanInterfaces.Model

namespace Specs.D04.C01.EuclideanInterfaces
open Model

def EType := ℕ → Type
def EValue : EType :=
  fun n => EuclideanSpace ℝ (Fin n)

def coordinatesType := (n : ℕ) → E n ≃ₗ[ℝ] (Fin n → ℝ)
def coordinatesValue : coordinatesType :=
  fun n => WithLp.linearEquiv 2 ℝ (Fin n → ℝ)

def standardBasisType := (n : ℕ) → Module.Basis (Fin n) ℝ (E n)
def standardBasisValue : standardBasisType :=
  fun n => (EuclideanSpace.basisFun (Fin n) ℝ).toBasis

def maxNormType := {n : ℕ} → E n → ℝ
def maxNormValue : maxNormType :=
  fun {n} x => ↑((Finset.univ : Finset (Fin n)).sup (fun i => ‖x i‖₊) : NNReal)

def matrixLinearEquivType := (m n : ℕ) → Matrix (Fin m) (Fin n) ℝ ≃ₗ[ℝ] (E n →ₗ[ℝ] E m)
def matrixLinearEquivValue : matrixLinearEquivType :=
  fun m n => Matrix.toEuclideanLin

def matrixOfLinearMapType := {m n : ℕ} → (E n →ₗ[ℝ] E m) → Matrix (Fin m) (Fin n) ℝ
def matrixOfLinearMapValue : matrixOfLinearMapType :=
  fun {m n} A => (matrixLinearEquiv m n).symm A

def complexCoordinatesType := ℂ ≃ₗ[ℝ] E 2
def complexCoordinatesValue : complexCoordinatesType :=
  { toFun := fun z => WithLp.toLp 2 ![z.re, z.im]
    invFun := fun x => ⟨x 0, x 1⟩
    left_inv := by intro z; rfl
    right_inv := by intro x; ext i; fin_cases i <;> rfl
    map_add' := by intro z w; ext i; fin_cases i <;> rfl
    map_smul' := by intro r z; ext i; fin_cases i <;> simp }

def ballType := {n : ℕ} → E n → ℝ → Set (E n)
def ballValue : ballType :=
  fun a r => {x | ‖x - a‖ < r}

def OpenType := {n : ℕ} → Set (E n) → Prop
def OpenValue : OpenType :=
  fun U => ∀ a ∈ U, ∃ r > 0, ball a r ⊆ U

def ClosedType := {n : ℕ} → Set (E n) → Prop
def ClosedValue : ClosedType :=
  fun F => Open Fᶜ

def InteriorType := {n : ℕ} → Set (E n) → Set (E n)
def InteriorValue : InteriorType :=
  fun A => {a | ∃ r > 0, ball a r ⊆ A}

def ClosureType := {n : ℕ} → Set (E n) → Set (E n)
def ClosureValue : ClosureType :=
  fun A => {a | ∀ r > 0, ∃ x ∈ A, x ∈ ball a r}

def BoundaryType := {n : ℕ} → Set (E n) → Set (E n)
def BoundaryValue : BoundaryType :=
  fun A => Closure A \ Interior A

def relativeBallType := {n : ℕ} → Set (E n) → E n → ℝ → Set (E n)
def relativeBallValue : relativeBallType :=
  fun A a r => A ∩ ball a r

def RelativeNeighborhoodType := {n : ℕ} → (A : Set (E n)) → A → Set (E n) → Prop
def RelativeNeighborhoodValue : RelativeNeighborhoodType :=
  fun A a N => ∃ r > 0, relativeBall A a r ⊆ N

def RelativelyOpenType := {n : ℕ} → Set (E n) → Set (E n) → Prop
def RelativelyOpenValue : RelativelyOpenType :=
  fun A U => ∃ V, Open V ∧ U = A ∩ V

def AccumulationPointType := {n : ℕ} → Set (E n) → E n → Prop
def AccumulationPointValue : AccumulationPointType :=
  fun A a => ∀ r > 0, ∃ x ∈ A, x ≠ a ∧ x ∈ ball a r

def IsolatedPointType := {n : ℕ} → (A : Set (E n)) → A → Prop
def IsolatedPointValue : IsolatedPointType :=
  fun A a => ∃ r > 0, ∀ x ∈ A, x ∈ ball a r → x = a

def RelativeLimitType := {n m : ℕ} → (A : Set (E n)) → (A → E m) → E n → E m → Prop
def RelativeLimitValue : RelativeLimitType :=
  fun A f a b => AccumulationPoint A a ∧
    ∀ ε > 0, ∃ δ > 0, ∀ x : A,
      0 < ‖(x : E _) - a‖ → ‖(x : E _) - a‖ < δ → ‖f x - b‖ < ε

def RelativeContinuousAtType := {n m : ℕ} → (A : Set (E n)) → (A → E m) → A → Prop
def RelativeContinuousAtValue : RelativeContinuousAtType :=
  fun A f a => ∀ ε > 0, ∃ δ > 0, ∀ x : A,
    ‖x.val - a.val‖ < δ → ‖f x - f a‖ < ε

def RelativeContinuousType := {n m : ℕ} → (A : Set (E n)) → (A → E m) → Prop
def RelativeContinuousValue : RelativeContinuousType :=
  fun A f => ∀ a, RelativeContinuousAt A f a

def RelativeUniformContinuousType := {n m : ℕ} → (A : Set (E n)) → (A → E m) → Prop
def RelativeUniformContinuousValue : RelativeUniformContinuousType :=
  fun A f => ∀ ε > 0, ∃ δ > 0, ∀ x y : A,
    ‖x.val - y.val‖ < δ → ‖f x - f y‖ < ε

def CompactType := {n : ℕ} → Set (E n) → Prop
def CompactValue : CompactType :=
  fun K => ∀ (ι : Type) (U : ι → Set (E _)), (∀ i, Open (U i)) →
    K ⊆ ⋃ i, U i → ∃ t : Finset ι, K ⊆ ⋃ i ∈ t, U i

def SequentiallyCompactType := {n : ℕ} → Set (E n) → Prop
def SequentiallyCompactValue : SequentiallyCompactType :=
  fun K => ∀ x : ℕ → E _, (∀ j, x j ∈ K) →
    ∃ a ∈ K, ∃ s : ℕ → ℕ, StrictMono s ∧ Filter.Tendsto (x ∘ s) Filter.atTop (𝓝 a)

def ConnectedType := {n : ℕ} → Set (E n) → Prop
def ConnectedValue : ConnectedType :=
  fun A => IsPreconnected A

def DomainPathType := {n : ℕ} → (A : Set (E n)) → A → A → Type
def DomainPathValue : DomainPathType :=
  fun _ a b => Path a b

def PathConnectedType := {n : ℕ} → Set (E n) → Prop
def PathConnectedValue : PathConnectedType :=
  fun A => ∀ a b : A, Nonempty (DomainPath A a b)

def PolygonalPathType := {n : ℕ} → (A : Set (E n)) → A → A → Type
def PolygonalPathValue : PolygonalPathType :=
  fun A a b => {p : Σ N : ℕ, Fin (N + 1) → E _ //
    p.2 0 = a ∧ p.2 (Fin.last p.1) = b ∧
    ∀ i : Fin p.1, segment ℝ (p.2 i.castSucc) (p.2 i.succ) ⊆ A}

def PolygonallyConnectedType := {n : ℕ} → Set (E n) → Prop
def PolygonallyConnectedValue : PolygonallyConnectedType :=
  fun A => ∀ a b : A, Nonempty (PolygonalPath A a b)

def ConvexSetType := {n : ℕ} → Set (E n) → Prop
def ConvexSetValue : ConvexSetType :=
  fun A => Convex ℝ A

def SimplyConnectedType := {n : ℕ} → Set (E n) → Prop
def SimplyConnectedValue : SimplyConnectedType :=
  fun A => PathConnected A ∧ ∀ a : A, ∀ γ : DomainPath A a a,
    Nonempty (Path.Homotopy γ (Path.refl a))

def linearOperatorNormType := {n m : ℕ} → (E n →ₗ[ℝ] E m) → ℝ
def linearOperatorNormValue : linearOperatorNormType :=
  fun A => sSup ((fun v => ‖A v‖) '' {v | ‖v‖ ≤ 1})

def multilinearOperatorNormType := {n m k : ℕ} → MultilinearMap ℝ (fun _ : Fin k => E n) (E m) → ℝ
def multilinearOperatorNormValue : multilinearOperatorNormType :=
  fun T => sSup ((fun v => ‖T v‖) '' {v | ∀ i, ‖v i‖ ≤ 1})

end Specs.D04.C01.EuclideanInterfaces

-- Expected bridge propositions. Independent of the candidate implementation.
namespace Specs.D04.C01.EuclideanInterfaces
open Model

def coordinates_applyType : Prop :=
  ∀ {n : ℕ} (x : E n) (i : Fin n),
    coordinates n x i = x i

def standardBasis_applyType : Prop :=
  ∀ {n : ℕ} (i j : Fin n),
    standardBasis n i j = if j = i then 1 else 0

def inner_coordinatesType : Prop :=
  ∀ {n : ℕ} (x y : E n),
    inner ℝ x y = ∑ i, x i * y i

def norm_coordinatesType : Prop :=
  ∀ {n : ℕ} (x : E n),
    ‖x‖ = Real.sqrt (∑ i, x i ^ 2)

def maxNorm_eq_coordinate_normType : Prop :=
  ∀ {n : ℕ} (x : E n),
    maxNorm x = ‖coordinates n x‖

def norm_dimension_zeroType : Prop :=
  ∀ (x : E 0),
    ‖x‖ = 0

def maxNorm_dimension_zeroType : Prop :=
  ∀ (x : E 0),
    maxNorm x = 0

def vector_dimension_zeroType : Prop :=
  ∀ (x : E 0),
    x = 0

def matrix_applyType : Prop :=
  ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (x : E n) (i : Fin m),
    matrixLinearEquiv m n M x i = ∑ j, M i j * x j

def matrix_columnType : Prop :=
  ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n),
    matrixLinearEquiv m n M (standardBasis n j) i = M i j

def matrixOfLinearMap_applyType : Prop :=
  ∀ {m n : ℕ} (A : E n →ₗ[ℝ] E m) (i : Fin m) (j : Fin n),
    matrixOfLinearMap A i j = A (standardBasis n j) i

def matrix_linear_roundtripType : Prop :=
  ∀ {m n : ℕ} (A : E n →ₗ[ℝ] E m),
    matrixLinearEquiv m n (matrixOfLinearMap A) = A

def matrix_compositionType : Prop :=
  ∀ {m n p : ℕ} (A : Matrix (Fin p) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin n) ℝ),
    matrixLinearEquiv p n (A * B) =
      (matrixLinearEquiv p m A).comp (matrixLinearEquiv m n B)

def linearMap_from_zeroType : Prop :=
  ∀ {m : ℕ} (A : E 0 →ₗ[ℝ] E m),
    A = 0

def linearMap_to_zeroType : Prop :=
  ∀ {n : ℕ} (A : E n →ₗ[ℝ] E 0),
    A = 0

def empty_matrix_determinantType : Prop :=
  ∀ (M : Matrix (Fin 0) (Fin 0) ℝ),
    Matrix.det M = 1

def complexCoordinates_reType : Prop :=
  ∀ (z : ℂ),
    complexCoordinates z 0 = z.re

def complexCoordinates_imType : Prop :=
  ∀ (z : ℂ),
    complexCoordinates z 1 = z.im

def ball_eq_metricType : Prop :=
  ∀ {n : ℕ} (a : E n) (r : ℝ),
    ball a r = Metric.ball a r

def open_iff_isOpenType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)),
    Open U ↔ IsOpen U

def closed_iff_isClosedType : Prop :=
  ∀ {n : ℕ} (F : Set (E n)),
    Closed F ↔ IsClosed F

def interior_eqType : Prop :=
  ∀ {n : ℕ} (A : Set (E n)),
    Interior A = interior A

def closure_eqType : Prop :=
  ∀ {n : ℕ} (A : Set (E n)),
    Closure A = closure A

def boundary_eq_frontierType : Prop :=
  ∀ {n : ℕ} (A : Set (E n)),
    Boundary A = frontier A

def relativeNeighborhood_iffType : Prop :=
  ∀ {n : ℕ} (A : Set (E n)) (a : A) (N : Set (E n)),
    RelativeNeighborhood A a N ↔ N ∈ 𝓝[A] (a : E n)

def relativelyOpen_iffType : Prop :=
  ∀ {n : ℕ} (A U : Set (E n)),
    RelativelyOpen A U ↔ ∃ V, IsOpen V ∧ U = A ∩ V

def relativelyOpen_subtype_iffType : Prop :=
  ∀ {n : ℕ} (A U : Set (E n)),
    RelativelyOpen A U ↔ U ⊆ A ∧ IsOpen ((Subtype.val : A → E n) ⁻¹' U)

def accumulationPoint_iff_accPtType : Prop :=
  ∀ {n : ℕ} (A : Set (E n)) (a : E n),
    AccumulationPoint A a ↔ AccPt a (𝓟 A)

def relativeContinuousAt_iffType : Prop :=
  ∀ {n m : ℕ} (A : Set (E n)) (f : A → E m) (a : A),
    RelativeContinuousAt A f a ↔ ContinuousAt f a

def relativeContinuous_iffType : Prop :=
  ∀ {n m : ℕ} (A : Set (E n)) (f : A → E m),
    RelativeContinuous A f ↔ Continuous f

def relativeUniformContinuous_iffType : Prop :=
  ∀ {n m : ℕ} (A : Set (E n)) (f : A → E m),
    RelativeUniformContinuous A f ↔ UniformContinuous f

def isolated_not_accumulationType : Prop :=
  ∀ {n : ℕ} (A : Set (E n)) (a : A) (ha : IsolatedPoint A a),
    ¬ AccumulationPoint A a

def continuousAt_isolatedType : Prop :=
  ∀ {n m : ℕ} (A : Set (E n)) (f : A → E m) (a : A)
    (ha : IsolatedPoint A a),
    RelativeContinuousAt A f a

def no_limit_at_isolatedType : Prop :=
  ∀ {n m : ℕ} (A : Set (E n)) (f : A → E m) (a : A)
    (ha : IsolatedPoint A a) (b : E m),
    ¬ RelativeLimit A f a b

def compact_iff_isCompactType : Prop :=
  ∀ {n : ℕ} (K : Set (E n)),
    Compact K ↔ IsCompact K

def sequentiallyCompact_iff_isSeqCompactType : Prop :=
  ∀ {n : ℕ} (K : Set (E n)),
    SequentiallyCompact K ↔ IsSeqCompact K

def connected_iff_no_separationType : Prop :=
  ∀ {n : ℕ} (A : Set (E n)),
    Connected A ↔ ¬ ∃ U V : Set (E n),
      RelativelyOpen A U ∧ RelativelyOpen A V ∧ U.Nonempty ∧ V.Nonempty ∧
      Disjoint U V ∧ A = U ∪ V

def connected_iff_isPreconnectedType : Prop :=
  ∀ {n : ℕ} (A : Set (E n)),
    Connected A ↔ IsPreconnected A

def connected_nonempty_iff_isConnectedType : Prop :=
  ∀ {n : ℕ} (A : Set (E n)) (hA : A.Nonempty),
    Connected A ↔ IsConnected A

def connected_emptyType : Prop :=
  ∀ {n : ℕ},
    Connected (∅ : Set (E n))

def pathConnected_emptyType : Prop :=
  ∀ {n : ℕ},
    PathConnected (∅ : Set (E n))

def path_propertiesType : Prop :=
  ∀ {n : ℕ} (A : Set (E n)) (a b : A) (γ : DomainPath A a b),
    Continuous γ ∧ γ 0 = a ∧ γ 1 = b

def polygonalPath_has_pathType : Prop :=
  ∀ {n : ℕ} (A : Set (E n)) (a b : A)
    (p : PolygonalPath A a b),
    Nonempty (DomainPath A a b)

def contraction_propertiesType : Prop :=
  ∀ {n : ℕ} (A : Set (E n)) (a : A) (γ : DomainPath A a a)
    (H : Path.Homotopy γ (Path.refl a)),
    Continuous H ∧ (∀ t, H (0, t) = γ t) ∧ (∀ t, H (1, t) = a) ∧
      (∀ s, H (s, 0) = a ∧ H (s, 1) = a)

def convexSet_iff_segmentType : Prop :=
  ∀ {n : ℕ} (A : Set (E n)),
    ConvexSet A ↔ ∀ x ∈ A, ∀ y ∈ A, segment ℝ x y ⊆ A

def linearOperatorNorm_eq_standardType : Prop :=
  ∀ {n m : ℕ} (A : E n →L[ℝ] E m),
    linearOperatorNorm A.toLinearMap = ‖A‖

def multilinearOperatorNorm_eq_standardType : Prop :=
  ∀ {n m k : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => E n) (E m)),
    multilinearOperatorNorm T.toMultilinearMap = ‖T‖

def linearOperatorNorm_from_zeroType : Prop :=
  ∀ {m : ℕ} (A : E 0 →ₗ[ℝ] E m),
    linearOperatorNorm A = 0

def multilinearOperatorNorm_order_zeroType : Prop :=
  ∀ {n m : ℕ}
    (T : MultilinearMap ℝ (fun _ : Fin 0 => E n) (E m)),
    multilinearOperatorNorm T = ‖T (fun i => Fin.elim0 i)‖

def multilinearMap_from_zeroType : Prop :=
  ∀ {m k : ℕ} (hk : 0 < k)
    (T : MultilinearMap ℝ (fun _ : Fin k => E 0) (E m)),
    T = 0

def multilinearOperatorNorm_from_zeroType : Prop :=
  ∀ {m k : ℕ} (hk : 0 < k)
    (T : MultilinearMap ℝ (fun _ : Fin k => E 0) (E m)),
    multilinearOperatorNorm T = 0

end Specs.D04.C01.EuclideanInterfaces
