import MathGenome.Internal.Specs.D07.Ch16.MapsSubmodules
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Quotient.Defs

/-!
Independent specification of K07.22.free_direct_sums, paper.tex:6699–6725.
Scalars are commutative unital rings, including the zero ring. Index types
are arbitrary; targets and summands are arbitrary unital modules.

`E →₀ R` is Mathlib's type of finitely supported functions. `DirectSum E M`
is definitionally the dependent finitely supported function type `Π₀ i, M i`.
The model statements identify their images in the full function types with
exactly the finite-support functions. The pointwise laws identify operations.
Delta functions are `Finsupp.single e 1`, and coordinate inclusions are the
linear maps `DirectSum.lof`. No freeness or finiteness is assumed of the M i.

Unique coefficients mean uniqueness of a finitely supported coefficient
function, not uniqueness of a choice of finite summation set (which can
contain extra zero terms). Universal properties specify extension on every
generator/inclusion; separate formula statements apply to every extension.
The empty cases require no nonzero scalars. The infinite-product boundary
uses nontrivial scalars solely to exhibit a product element of infinite
support; it does not assert failure for families of zero modules.
-/

universe u v w t

namespace Specs.D07.Ch22.FreeDirectSums

open scoped BigOperators

/-- The free module consists of exactly all finite-support functions. -/
def FreeFunctions : Prop :=
  ∀ (R : Type u) [CommRing R] (E : Type v) (f : E → R),
    (∃ a : E →₀ R, ∀ i, a i = f i) ↔ Set.Finite {i | f i ≠ 0}

/-- Its operations are pointwise. -/
def FreePointwise : Prop :=
  ∀ (R : Type u) [CommRing R] (E : Type v) (a b : E →₀ R) (r : R) (i : E),
    (0 : E →₀ R) i = 0 ∧ (a + b) i = a i + b i ∧
      (-a) i = -a i ∧ (r • a) i = r * a i

/-- Delta has value one at its index and zero elsewhere, also over the zero ring. -/
def DeltaCoordinates : Prop := by
  classical
  exact ∀ (R : Type u) [CommRing R] (E : Type v) (e i : E),
    (Finsupp.single e (1 : R)) i = if e = i then 1 else 0

/-- Every vector is the finite linear combination given by its coordinates. -/
def FreeExpansion : Prop :=
  ∀ (R : Type u) [CommRing R] (E : Type v) (a : E →₀ R),
    ∑ e ∈ a.support, a e • Finsupp.single e (1 : R) = a

/-- The finitely supported coefficients in a delta expansion are unique. -/
def FreeCoefficientsUnique : Prop :=
  ∀ (R : Type u) [CommRing R] (E : Type v) (a : E →₀ R),
    ∃! c : E →₀ R, ∑ e ∈ c.support, c e • Finsupp.single e (1 : R) = a

/-- Every function on E extends uniquely to a linear map. -/
def FreeUniversalProperty : Prop :=
  ∀ (R : Type u) [CommRing R] (E : Type v) (N : Type w)
    [AddCommGroup N] [Module R N] (h : E → N),
    ∃! F : (E →₀ R) →ₗ[R] N, ∀ e, F (Finsupp.single e 1) = h e

/-- The extension has the source's explicit finite-sum formula. -/
def FreeMapFormula : Prop :=
  ∀ (R : Type u) [CommRing R] (E : Type v) (N : Type w)
    [AddCommGroup N] [Module R N] (h : E → N) (F : (E →₀ R) →ₗ[R] N),
    (∀ e, F (Finsupp.single e 1) = h e) →
      ∀ a, F a = ∑ e ∈ a.support, a e • h e

/-- The direct sum consists of exactly the finite-support tuples in the product. -/
def DirectSumFunctions : Prop :=
  ∀ (R : Type u) [CommRing R] (E : Type v) (M : E → Type w)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (f : ∀ i, M i),
    (∃ a : DirectSum E M, ∀ i, a i = f i) ↔ Set.Finite {i | f i ≠ 0}

/-- Direct-sum operations are the product's pointwise operations. -/
def DirectSumPointwise : Prop :=
  ∀ (R : Type u) [CommRing R] (E : Type v) (M : E → Type w)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (a b : DirectSum E M) (r : R) (i : E),
    (0 : DirectSum E M) i = 0 ∧ (a + b) i = a i + b i ∧
      (-a) i = -a i ∧ (r • a) i = r • a i

/-- The linear coordinate inclusions retain their coordinate and vanish elsewhere. -/
def CoordinateInclusions : Prop := by
  classical
  exact ∀ (R : Type u) [CommRing R] (E : Type v) (M : E → Type w)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (i : E) (x : M i),
    (DirectSum.lof R E M i x) i = x ∧
      ∀ j, j ≠ i → (DirectSum.lof R E M i x) j = 0

/-- Every tuple is a finite sum of its included coordinates. -/
def DirectSumExpansion : Prop := by
  classical
  exact ∀ (R : Type u) [CommRing R] (E : Type v) (M : E → Type w)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (a : DirectSum E M),
    ∑ i ∈ a.support, DirectSum.lof R E M i (a i) = a

/-- Arbitrary families of linear maps extend uniquely across the direct sum. -/
def DirectSumUniversalProperty : Prop := by
  classical
  exact ∀ (R : Type u) [CommRing R] (E : Type v) (M : E → Type w)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (N : Type t)
    [AddCommGroup N] [Module R N] (h : ∀ i, M i →ₗ[R] N),
    ∃! F : DirectSum E M →ₗ[R] N, ∀ i x, F (DirectSum.lof R E M i x) = h i x

/-- The extension sums only over the tuple's finite support. -/
def DirectSumMapFormula : Prop := by
  classical
  exact ∀ (R : Type u) [CommRing R] (E : Type v) (M : E → Type w)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (N : Type t)
    [AddCommGroup N] [Module R N] (h : ∀ i, M i →ₗ[R] N)
    (F : DirectSum E M →ₗ[R] N),
    (∀ i x, F (DirectSum.lof R E M i x) = h i x) →
      ∀ a, F a = ∑ i ∈ a.support, h i (a i)

/-- Free modules on an empty set are zero. -/
def EmptyFree : Prop :=
  ∀ (R : Type u) [CommRing R] (E : Type v) [IsEmpty E] (a : E →₀ R), a = 0

/-- Empty direct sums are zero. -/
def EmptyDirectSum : Prop :=
  ∀ (R : Type u) [CommRing R] (E : Type v) [IsEmpty E] (M : E → Type w)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (a : DirectSum E M), a = 0

/-- The infinite product contains the all-one tuple, outside the direct sum.
Nontriviality is needed only for this boundary example. -/
def InfiniteProduct : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] (E : Type v) [Infinite E],
    (fun _ : E => (1 : R)) ∉ Set.range
      (DirectSum.coeFnLinearMap R : DirectSum E (fun _ => R) →ₗ[R] (E → R))

/-- For infinite copies of a nonzero ring, the product fails the uniqueness
part of the direct-sum universal property. The quotient by finite-support
tuples and the zero map agree on every included coordinate but differ. -/
def ProductNotCoproduct : Prop := by
  classical
  exact ∀ (R : Type u) [CommRing R] [Nontrivial R] (E : Type v) [Infinite E],
    let P : Submodule R (E → R) := LinearMap.range
      (DirectSum.coeFnLinearMap R : DirectSum E (fun _ => R) →ₗ[R] (E → R))
    ∃ F G : (E → R) →ₗ[R] ((E → R) ⧸ P),
      F ≠ G ∧ ∀ (i : E) (x : R), F (Pi.single i x) = G (Pi.single i x)

end Specs.D07.Ch22.FreeDirectSums
