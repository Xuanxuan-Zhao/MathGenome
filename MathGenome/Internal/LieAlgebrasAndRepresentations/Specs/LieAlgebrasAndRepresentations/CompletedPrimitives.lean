import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.FreeLie
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.EnvelopingHopf
import Mathlib.LinearAlgebra.TensorAlgebra.Grading
import Mathlib.RingTheory.PowerSeries.Basic

/-! The primitive part of LA A08, notes/005, lines 493–537.
The formal parameter below records tensor degree; it is not an extra generator.
Coefficients of degree n are constrained to the actual nth homogeneous subspace.
Thus the subalgebra of power series is the product of the tensor-degree pieces,
with its usual Cauchy multiplication. The tensor square is completed in total
degree, using the degree-one generators from both factors (no Koszul signs).
There is no finiteness restriction on V. -/
noncomputable section

namespace LieAlgebrasAndRepresentations.CompletedPrimitives
open scoped TensorProduct
open TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing
universe u v

/-- Completion of an algebra with respect to its homogeneous generator submodule.
For the applications below these powers are the homogeneous pieces, not the
increasing word-length filtration. -/
def degreeSeries {k A : Type*} [CommRing k] [Ring A] [Algebra k A]
    (G : Submodule k A) : Subalgebra k (PowerSeries A) where
  carrier := {p | ∀ n, PowerSeries.coeff n p ∈ G ^ n}
  zero_mem' := by intro n; simp
  add_mem' := by
    intro p q hp hq n
    simpa only [map_add] using (G ^ n).add_mem (hp n) (hq n)
  one_mem' := by
    intro n
    rw [PowerSeries.coeff_one]
    split_ifs with h
    · subst n; simpa using (Submodule.algebraMap_mem (1 : k) : algebraMap k A 1 ∈ (1 : Submodule k A))
    · exact (G ^ n).zero_mem
  mul_mem' := by
    intro p q hp hq n
    rw [PowerSeries.coeff_mul]
    apply Submodule.sum_mem
    intro ij hij
    have h : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
    rw [← h, pow_add]
    exact Submodule.mul_mem_mul (hp ij.1) (hq ij.2)
  algebraMap_mem' := by
    intro r n
    rw [PowerSeries.algebraMap_apply]
    rw [PowerSeries.coeff_C]
    split_ifs with h
    · subst n; simpa using (Submodule.algebraMap_mem r : algebraMap k A r ∈ (1 : Submodule k A))
    · exact (G ^ n).zero_mem

variable (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V]

abbrev A := TensorAlgebra k V
abbrev generators : Submodule k (A k V) := LinearMap.range (TensorAlgebra.ι k)
abbrev degree (n : ℕ) : Submodule k (A k V) := generators k V ^ n
abbrev Completion := degreeSeries (generators k V)

/-- Both factors carry the ordinary tensor grading. -/
def squareGenerators : Submodule k (A k V ⊗[k] A k V) :=
  (generators k V).map (Algebra.TensorProduct.includeLeft : A k V →ₐ[k] _).toLinearMap ⊔
  (generators k V).map (Algebra.TensorProduct.includeRight : A k V →ₐ[k] _).toLinearMap
abbrev squareDegree (n : ℕ) := squareGenerators k V ^ n
abbrev CompletedSquare := degreeSeries (squareGenerators k V)

/-- The usual total-degree piece of the tensor square, described by pure tensors. -/
def totalSquareDegree (n : ℕ) : Submodule k (A k V ⊗[k] A k V) :=
  Submodule.span k {t | ∃ i j : ℕ, i+j=n ∧ ∃ a ∈ degree k V i,
    ∃ b ∈ degree k V j, a ⊗ₜ[k] b = t}

/-- The ordinary coproduct on T(V), fixed by its values on V. -/
def tensorCoproduct : A k V →ₐ[k] A k V ⊗[k] A k V :=
  TensorAlgebra.lift k
    ((Algebra.TensorProduct.includeLeft : A k V →ₐ[k] _).toLinearMap.comp (TensorAlgebra.ι k) +
     (Algebra.TensorProduct.includeRight : A k V →ₐ[k] _).toLinearMap.comp (TensorAlgebra.ι k))

def IsPrimitive (p : A k V) : Prop :=
  tensorCoproduct k V p = p ⊗ₜ[k] 1 + 1 ⊗ₜ[k] p

/-- The free Lie algebra inside the tensor algebra, using the shared A07 interface. -/
abbrev tensorLie : LieSubalgebra k (A k V) :=
  LieSubalgebra.lieSpan k (A k V) (Set.range (TensorAlgebra.ι k : V →ₗ[k] _))

/-- The canonical ordinary-to-completed inclusion is tensor-degree decomposition. -/
def ordinarySeries (p : A k V) : Completion k V :=
  ⟨PowerSeries.mk (fun n => (DirectSum.decompose (degree k V) p n : A k V)),
    fun n => by simpa using (DirectSum.decompose (degree k V) p n).property⟩

/-- All coefficients have positive tensor degree precisely when the constant
coefficient vanishes; zero is included. -/
def Positive (p : Completion k V) : Prop := PowerSeries.coeff 0 p.val = 0

/-- Finite jets of a completed Lie series are jets of ordinary free Lie elements.
This defines the degree completion as a closure, without presupposing that the
Lie subalgebra is homogeneous (that property is part of the intended bridge). -/
def InCompletedLie (p : Completion k V) : Prop :=
  ∀ N : ℕ, ∃ x : A k V, x ∈ tensorLie k V ∧
    ∀ n ≤ N, PowerSeries.coeff n (ordinarySeries k V x).val = PowerSeries.coeff n p.val

/-- Completed primitivity written coefficientwise in the total-degree tensor
square. The construction theorem below identifies this with equality of the
actual completed coproduct and the two canonical tensor inclusions. -/
def IsCompletedPrimitive (p : Completion k V) : Prop :=
  ∀ n, IsPrimitive k V (PowerSeries.coeff n p.val)

end LieAlgebrasAndRepresentations.CompletedPrimitives

namespace Specs.LieAlgebrasAndRepresentations.CompletedPrimitives
open _root_.LieAlgebrasAndRepresentations.CompletedPrimitives
open _root_.LieAlgebrasAndRepresentations.FreeLie
open scoped TensorProduct
universe u v

/-- Actual completed maps, with all their coefficients fixed. This includes the
ordinary-to-completed injective algebra map, so the construction is connected to
T(V), not an unrelated product of coefficient spaces. -/
def constructionExpected : Prop :=
  ∀ (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V],
  ∃ (j : A k V →ₐ[k] Completion k V)
    (Δ : Completion k V →ₐ[k] CompletedSquare k V)
    (l r : Completion k V →ₐ[k] CompletedSquare k V),
    (∀ x, j x = ordinarySeries k V x) ∧ Function.Injective j ∧
    (∀ p n, PowerSeries.coeff n (Δ p).val =
      tensorCoproduct k V (PowerSeries.coeff n p.val)) ∧
    (∀ p n, PowerSeries.coeff n (l p).val = PowerSeries.coeff n p.val ⊗ₜ[k] 1) ∧
    (∀ p n, PowerSeries.coeff n (r p).val = 1 ⊗ₜ[k] PowerSeries.coeff n p.val) ∧
    (∀ p, IsCompletedPrimitive k V p ↔ Δ p = l p + r p) ∧
    (∀ n, squareDegree k V n = totalSquareDegree k V n) ∧
    (∀ s : ∀ n, degree k V n, ∃ p : Completion k V,
      ∀ n, PowerSeries.coeff n p.val = (s n : A k V))

/-- Ordinary primitives have exactly the A07 free Lie image, with no scalar part.
The coproduct is also explicitly transported across the A07 enveloping–tensor
isomorphism, to record the assertion about U(L(V)). -/
def ordinaryExpected : Prop :=
  ∀ (k : Type u) (V : Type v) [Field k] [CharZero k] [AddCommGroup V] [Module k V],
    (∀ p : A k V, IsPrimitive k V p ↔ p ∈ tensorLie k V) ∧
    (∀ p : A k V, IsPrimitive k V p →
      PowerSeries.coeff 0 (ordinarySeries k V p).val = 0) ∧
    (∀ x : Shared.Lie.U k (Free k V),
      IsPrimitive k V (tensorMap k V x) ↔
        ∃ y : Free k V, Shared.Lie.inclusion k (Free k V) y = x) ∧
    (∀ (Δ : Shared.Lie.U k (Free k V) →ₐ[k] _)
      (ε : Shared.Lie.U k (Free k V) →ₐ[k] k)
      (S : Shared.Lie.U k (Free k V) ≃ₗ[k] Shared.Lie.U k (Free k V)),
      Specs.LieAlgebrasAndRepresentations.EnvelopingHopf.HopfLaws k (Free k V) Δ ε S →
      ∀ x, tensorCoproduct k V (tensorMap k V x) =
        Algebra.TensorProduct.map (tensorMap k V) (tensorMap k V) (Δ x))

/-- The whole positive-degree primitive space, including infinite series in
arbitrary-dimensional V, equals the degree completion of the original free Lie
subalgebra. Scalar removal is asserted separately, rather than assumed. -/
def completedExpected : Prop :=
  ∀ (k : Type u) (V : Type v) [Field k] [CharZero k] [AddCommGroup V] [Module k V],
    (∀ p : Completion k V, IsCompletedPrimitive k V p → Positive k V p) ∧
    (∀ p : Completion k V,
      IsCompletedPrimitive k V p ↔ Positive k V p ∧ InCompletedLie k V p) ∧
    (∀ p : Completion k V,
      InCompletedLie k V p ↔ ∀ n, PowerSeries.coeff n p.val ∈ tensorLie k V)

/-- The remaining ordinary recognition assertion, separated from its completed
and enveloping consequences. This is a proof obligation, not an axiom. -/
def recognitionExpected : Prop :=
  ∀ (k : Type u) (V : Type v) [Field k] [CharZero k] [AddCommGroup V] [Module k V],
    ∀ p : A k V, IsPrimitive k V p ↔ p ∈ tensorLie k V

/-- Explicit proof reduction; no recognition certificate is installed as an
instance or assumed in any of the definitions above. -/
def reductionExpected : Prop :=
  recognitionExpected.{u,v} → ordinaryExpected.{u,v} ∧ completedExpected.{u,v}

end Specs.LieAlgebrasAndRepresentations.CompletedPrimitives
