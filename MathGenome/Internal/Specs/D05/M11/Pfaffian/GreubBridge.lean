import MathGenome.Internal.Specs.D05.M11.Pfaffian.Identities
import MathGenome.Internal.Specs.D05.M15.WedgeSign.Bivectors
import MathGenome.Internal.Specs.D05.M15.InnerTensor.ExteriorMetric

/-! The real Euclidean convention bridge of paper.tex:1854–1864.
All wedges, powers, and metrics are on the canonical exterior quotient.
The matrix convention is columns of images. The factorial in `dividedPower`
is part of its definition; the scalar is defined by the exterior metric,
not by the matrix Pfaffian whose relation to it is to be proved. -/
noncomputable section
namespace Specs.D05.M11.Pfaffian.GreubBridge
open scoped BigOperators
open Specs.D05.M15.WedgeSign.BivectorNormalForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- In an orthonormal basis this is the metric identification with the algebraic dual. -/
def metricIdentification {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ V) :
    V ≃ₗ[ℝ] Module.Dual ℝ V :=
  b.toBasis.equiv b.toBasis.dualBasis (Equiv.refl _)

/-- Recover the operator represented by the alternating form of the bivector. -/
def phi {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ V) (z : ⋀[ℝ]^2 V) : V →ₗ[ℝ] V :=
  let e := metricIdentification b
  e.symm.toLinearMap.comp ((form z).compl₁₂ e.toLinearMap e.toLinearMap)

/-- The negative sign is Greub's operator convention. -/
def bivector {m : ℕ} (b : OrthonormalBasis (Fin (2*m)) ℝ V)
    (A : Matrix (Fin (2*m)) (Fin (2*m)) ℝ) : ⋀[ℝ]^2 V :=
  -(∑ i, ∑ j ∈ Finset.Ioi i, A i j • wedge (b i) (b j))

def volume {m : ℕ} (b : OrthonormalBasis (Fin (2*m)) ℝ V) : ⋀[ℝ]^(2*m) V :=
  exteriorPower.ιMulti ℝ (2*m) b

/-- The ordinary m-fold product divided by m!, including m = 0. -/
def dividedPower (m : ℕ) (z : ⋀[ℝ]^2 V) : ⋀[ℝ]^(2*m) V :=
  (Nat.factorial m : ℝ)⁻¹ •
    ⟨(z : ExteriorAlgebra ℝ V)^m, by
      simpa only [smul_eq_mul, Nat.mul_comm] using
        (SetLike.pow_mem_graded (A := fun p : ℕ => ⋀[ℝ]^p V) m z.property)⟩

/-- The induced Euclidean metric, with the determinant Gram rule. -/
abbrev exteriorMetric (p : ℕ) : LinearMap.BilinForm ℝ (⋀[ℝ]^p V) :=
  Specs.D05.M15.InnerTensor.ExteriorMetric.bilinear_value (innerₗ V) p

def greubPfaffian {m : ℕ} (b : OrthonormalBasis (Fin (2*m)) ℝ V)
    (A : Matrix (Fin (2*m)) (Fin (2*m)) ℝ) (c : ℝ) : ℝ :=
  exteriorMetric (2*m) (dividedPower m (bivector b A)) (c • volume b)

/-- Agreement with the canonical positive exterior metric in the real case. -/
def metric_agreement : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (p : ℕ) (u v : ⋀[ℝ]^p V),
    exteriorMetric p u v =
      Specs.D05.M15.InnerTensor.ExteriorMetric.metric_value p u v

def generator_formula : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ V) (u v x : V),
    phi b (wedge u v) x = D05.firstInner (F := ℝ) u x • v -
      D05.firstInner (F := ℝ) v x • u

def generator_matrix : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ V) (i j r s : Fin n),
    LinearMap.toMatrix b.toBasis b.toBasis (phi b (wedge (b i) (b j))) r s =
      (if r = j ∧ s = i then 1 else 0) - (if r = i ∧ s = j then 1 else 0)

def inverse_image : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {m : ℕ} (b : OrthonormalBasis (Fin (2*m)) ℝ V)
    (T : V →ₗ[ℝ] V),
    (∀ i j, LinearMap.toMatrix b.toBasis b.toBasis T i j =
      -LinearMap.toMatrix b.toBasis b.toBasis T j i) →
    ∀ z : ⋀[ℝ]^2 V,
      phi b z = T ↔ z = bivector b (LinearMap.toMatrix b.toBasis b.toBasis T)

def matrix_inverse : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {m : ℕ} (b : OrthonormalBasis (Fin (2*m)) ℝ V)
    (A : Matrix (Fin (2*m)) (Fin (2*m)) ℝ), (∀ i j, A i j = -A j i) →
    LinearMap.toMatrix b.toBasis b.toBasis (phi b (bivector b A)) = A

def divided_power_normalization : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {m : ℕ} (b : OrthonormalBasis (Fin (2*m)) ℝ V)
    (A : Matrix (Fin (2*m)) (Fin (2*m)) ℝ), (∀ i j, A i j = -A j i) →
    dividedPower m (bivector b A) =
      ((-1 : ℝ)^m * pfaffian_value A) • volume b

def volume_unit : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {m : ℕ} (b : OrthonormalBasis (Fin (2*m)) ℝ V),
    exteriorMetric (2*m) (volume b) (volume b) = 1

def volume_norm : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {m : ℕ} (b : OrthonormalBasis (Fin (2*m)) ℝ V) (c : ℝ),
    exteriorMetric (2*m) (c • volume b) (c • volume b) = c^2

def scalar_bridge : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {m : ℕ} (b : OrthonormalBasis (Fin (2*m)) ℝ V)
    (A : Matrix (Fin (2*m)) (Fin (2*m)) ℝ), (∀ i j, A i j = -A j i) →
    ∀ c : ℝ, c ≠ 0 → greubPfaffian b A c = c * (-1 : ℝ)^m * pfaffian_value A

def square_bridge : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {m : ℕ} (b : OrthonormalBasis (Fin (2*m)) ℝ V)
    (A : Matrix (Fin (2*m)) (Fin (2*m)) ℝ), (∀ i j, A i j = -A j i) →
    ∀ c : ℝ, c ≠ 0 →
      greubPfaffian b A c ^ 2 = c^2 * D05.M05.determinant A ∧
      greubPfaffian b A c ^ 2 =
        exteriorMetric (2*m) (c • volume b) (c • volume b) * D05.M05.determinant A

end Specs.D05.M11.Pfaffian.GreubBridge
