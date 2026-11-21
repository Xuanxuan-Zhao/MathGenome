import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! Independent interface for the inseparable covering step of Theorem 6.8.
All rings and fields are represented by their actual images in the common
algebraically closed ambient field. No perfection assumption is made on `k`.
The empty family `Fin 0` is permitted. -/
namespace P103.Ch06.AffineCover

universe u v w
variable (k : Type u) {Ω : Type v} [Field k] [Field Ω] [Algebra k Ω]

def polynomialRing {d : ℕ} (t : Fin d → Ω) : Subalgebra k Ω :=
  Algebra.adjoin k (Set.range t)

def rationalField {d : ℕ} (t : Fin d → Ω) : IntermediateField k Ω :=
  IntermediateField.adjoin k (Set.range t)

def coveringRing {d : ℕ} (c : IntermediateField k Ω) (z : Fin d → Ω) : Subalgebra k Ω :=
  (Algebra.adjoin c (Set.range z)).restrictScalars k

def coveringField {d : ℕ} (c : IntermediateField k Ω) (z : Fin d → Ω) :
    IntermediateField k Ω :=
  (IntermediateField.adjoin c (Set.range z)).restrictScalars k

/-- Module finiteness for the inclusion of the indicated rings. -/
def FiniteRingExtension (B C : Subalgebra k Ω) : Prop :=
  ∃ h : B ≤ C, letI := (Subalgebra.inclusion h).toAlgebra; Module.Finite B C

/-- Finiteness and separability for the inclusion of the indicated fields. -/
def FiniteSeparableExtension (K N : IntermediateField k Ω) : Prop :=
  ∃ h : K ≤ N, letI := (IntermediateField.inclusion h).toAlgebra;
    Module.Finite K N ∧ Algebra.IsSeparable K N

/-- The full required inseparable affine cover, in any common algebraically
closed overfield (and hence in the chosen algebraic closure of `k(t)`). -/
def InseparableAffineCover : Prop :=
  ∀ (Ω : Type v) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (d : ℕ) (t : Fin d → Ω), AlgebraicIndependent k t →
    ∀ (L : IntermediateField (rationalField k t) Ω),
    Module.Finite (rationalField k t) L →
    ∃ (e : ℕ) (c : IntermediateField k Ω) (z : Fin d → Ω)
      (N : IntermediateField k Ω),
      Module.Finite k c ∧ IsPurelyInseparable k c ∧
      (∀ a : c, (a : Ω) ^ (p ^ e) ∈ (algebraMap k Ω).range) ∧
      (∀ i, z i ^ (p ^ e) = t i) ∧ AlgebraicIndependent c z ∧
      L.restrictScalars k ≤ N ∧
      FiniteSeparableExtension k (coveringField k c z) N ∧
      FiniteRingExtension k (polynomialRing k t) (coveringRing k c z)

/-- Independence of the roots, without any finiteness or nonemptiness restriction
on the index set. -/
def RootIndependence : Prop :=
  ∀ (Ω : Type v) [Field Ω] [Algebra k Ω]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (ι : Type w) (t z : ι → Ω) (e : ℕ),
    AlgebraicIndependent k t → (∀ i, z i ^ (p ^ e) = t i) →
    ∀ (c : IntermediateField k Ω), Module.Finite k c → AlgebraicIndependent c z

/-- Ring-theoretic part of the cover, once the finite constant extension and
coordinate roots have been constructed. Independence is not needed here. -/
def RootRingFiniteness : Prop :=
  ∀ (Ω : Type v) [Field Ω] [Algebra k Ω]
    (d q : ℕ) (_hq : 0 < q) (t z : Fin d → Ω),
    (∀ i, z i ^ q = t i) → ∀ (c : IntermediateField k Ω),
    Module.Finite k c →
    FiniteRingExtension k (polynomialRing k t) (coveringRing k c z)

/-- The maximal separable subextension has a common purely inseparable
exponent, including exponent zero for an already separable extension. -/
def CommonSeparableExponent : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (p : ℕ) [Fact p.Prime] [CharP K p], Module.Finite K L →
    ∃ e : ℕ, ∀ x : L, x ^ (p ^ e) ∈ separableClosure K L

/-- Full quantified type of the requested theorem. -/
def inseparableAffineCoverType : Prop :=
  ∀ (k : Type u) [Field k], InseparableAffineCover.{u,v} k

def rootIndependenceType : Prop :=
  ∀ (k : Type u) [Field k], RootIndependence.{u,v,w} k

def rootRingFinitenessType : Prop :=
  ∀ (k : Type u) [Field k], RootRingFiniteness.{u,v} k

end P103.Ch06.AffineCover
