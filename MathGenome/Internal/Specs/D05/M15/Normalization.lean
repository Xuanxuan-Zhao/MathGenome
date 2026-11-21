import MathGenome.Internal.Specs.D05.M15.Symmetric
import MathGenome.Internal.Specs.D05.M15.Exterior
import MathGenome.Internal.Specs.D05.M15.Symmetrizers
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Cast

/-! Quotient–averaging bridges, paper.tex:3040–3054. All degrees, including
zero, and arbitrary-dimensional spaces are retained. Products below are tensor
concatenation, followed by the normalized projector. The associativity equations
are written in the tensor algebra to compare the two parenthesized degrees
without hiding a dependent-type cast. Its homogeneous inclusions are injective.
No decomposition or section is assumed. -/
noncomputable section
namespace Specs.D05.M15.Normalization
open scoped TensorProduct
universe u v w
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [CharZero K]

abbrev symQ (p : ℕ) := (Symmetric.adjacentRelations K V p).mkQ
abbrev extQ (p : ℕ) := Exterior.tensorProjection_value K V p
abbrev symP (p : ℕ) := Symmetrizers.symmetricProjector (K := K) (V := V) p
  (Nat.cast_ne_zero.mpr p.factorial_ne_zero)
abbrev altP (p : ℕ) := Symmetrizers.alternatingProjector (K := K) (V := V) p
  (Nat.cast_ne_zero.mpr p.factorial_ne_zero)
abbrev symH (p : ℕ) := Symmetric.homogeneousMap K V p
abbrev extH (p : ℕ) : TensorPower K p V →ₗ[K] _root_.ExteriorAlgebra K V :=
  (⋀[K]^p V).subtype.comp (extQ p)

abbrev concat {p q : ℕ} (x : TensorPower K p V) (y : TensorPower K q V) :
    TensorPower K (p + q) V := TensorPower.mulEquiv (x ⊗ₜ[K] y)

def symmetric_permutation : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [CharZero K] (p : ℕ) (σ : Equiv.Perm (Fin p)),
    (symQ (K := K) (V := V) p).comp (PermutationActions.permutationOperator p σ) = symQ p

def exterior_permutation : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [CharZero K] (p : ℕ) (σ : Equiv.Perm (Fin p)),
    (extQ (K := K) (V := V) p).comp (PermutationActions.permutationOperator p σ) =
      (D05.Foundations.permutationSign σ : K) • extQ p

def quotient_averages : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [CharZero K] (p : ℕ),
    (symQ (K := K) (V := V) p).comp (symP p) = symQ p ∧
    (extQ (K := K) (V := V) p).comp (altP p) = extQ p

def repeated_slots : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [CharZero K] (p : ℕ) (x : Fin p → V) (i j : Fin p),
    x i = x j → i ≠ j → altP p (PiTensorProduct.tprod K x) = 0

def annihilates_relations : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [CharZero K] (p : ℕ),
    Symmetric.adjacentRelations K V p ≤ LinearMap.ker (symP p) ∧
    Exterior.degreeRelations_value K V p ≤ LinearMap.ker (altP p)

def symmetric_bridge : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [CharZero K] (p : ℕ),
    ∃ e : Symmetric.symmetricPower K V p ≃ₗ[K] LinearMap.range (symP p),
      ((LinearMap.range (symP p)).subtype.comp e.toLinearMap).comp (symQ p) = symP p ∧
      (symQ p).comp ((LinearMap.range (symP p)).subtype.comp e.toLinearMap) = LinearMap.id

def exterior_bridge : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [CharZero K] (p : ℕ),
    ∃ e : (⋀[K]^p V) ≃ₗ[K] LinearMap.range (altP p),
      ((LinearMap.range (altP p)).subtype.comp e.toLinearMap).comp (extQ p) = altP p ∧
      (extQ p).comp ((LinearMap.range (altP p)).subtype.comp e.toLinearMap) = LinearMap.id

/-- Applying the ordinary algebra quotient to the averaged product gives exactly
its ordinary quotient product. Together with the bridges this determines the
product on each projector image uniquely. This stronger identity allows arbitrary
input tensors; it in particular covers invariant and sign-invariant inputs. -/
def products : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [CharZero K] (p q : ℕ) (x : TensorPower K p V) (y : TensorPower K q V),
    symH (p + q) (symP (p + q) (concat x y)) = symH p x * symH q y ∧
    extH (p + q) (altP (p + q) (concat x y)) = extH p x * extH q y

/-- The inverse quotient maps send the ordinary quotient product to the
averaged concatenation itself, as an equality of tensors. The next two equations
verify that these quotient classes represent the ordinary algebra products. -/
def product_transport : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [CharZero K] (p q : ℕ),
    ∃ es : Symmetric.symmetricPower K V (p + q) ≃ₗ[K]
      LinearMap.range (symP (K := K) (V := V) (p + q)),
    ∃ ea : (⋀[K]^(p + q) V) ≃ₗ[K]
      LinearMap.range (altP (K := K) (V := V) (p + q)),
      (∀ t, (es (symQ (K := K) (V := V) (p + q) t) : TensorPower K (p + q) V) =
        symP (K := K) (V := V) (p + q) t) ∧
      (∀ t, (ea (extQ (K := K) (V := V) (p + q) t) : TensorPower K (p + q) V) =
        altP (K := K) (V := V) (p + q) t) ∧
      (∀ (x : TensorPower K p V) (y : TensorPower K q V),
        symH (K := K) (V := V) (p + q)
          (es (symQ (K := K) (V := V) (p + q) (concat x y)) : TensorPower K (p + q) V) =
          symH p x * symH q y) ∧
      (∀ (x : TensorPower K p V) (y : TensorPower K q V),
        extH (K := K) (V := V) (p + q)
          (ea (extQ (K := K) (V := V) (p + q) (concat x y)) : TensorPower K (p + q) V) =
          extH p x * extH q y)

def associativity : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [CharZero K] (p q r : ℕ) (x : TensorPower K p V) (y : TensorPower K q V)
    (z : TensorPower K r V),
    TensorPower.toTensorAlgebra (symP (p + q + r) (concat (symP (p + q) (concat x y)) z)) =
      TensorPower.toTensorAlgebra (symP (p + (q + r)) (concat x (symP (q + r) (concat y z)))) ∧
    TensorPower.toTensorAlgebra (altP (p + q + r) (concat (altP (p + q) (concat x y)) z)) =
      TensorPower.toTensorAlgebra (altP (p + (q + r)) (concat x (altP (q + r) (concat y z))))

/-- The source divided power uses ordinary algebra powers and an inverse factorial.
This definition also specifies degree zero as the unit, with no division by zero. -/
def dividedPower_type :=
  ∀ (K : Type u) {B : Type w} [Field K] [Ring B] [Algebra K B], B → ℕ → B

def dividedPower_value : dividedPower_type.{u,w} :=
  fun K _ _ _ _ x n => (n.factorial : K)⁻¹ • x ^ n

def dividedPower_mul : Prop :=
  ∀ {K : Type u} {B : Type w} [Field K] [CharZero K] [Ring B] [Algebra K B]
    (x : B) (r s : ℕ),
    dividedPower_value K x r * dividedPower_value K x s =
      ((r + s).choose r : K) • dividedPower_value K x (r + s)

def dividedPower_add : Prop :=
  ∀ {K : Type u} {B : Type w} [Field K] [CharZero K] [Ring B] [Algebra K B]
    (x y : B), Commute x y → ∀ n : ℕ,
    dividedPower_value K (x + y) n =
      ∑ rs ∈ Finset.antidiagonal n,
        dividedPower_value K x rs.1 * dividedPower_value K y rs.2

end Specs.D05.M15.Normalization
