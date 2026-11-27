import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.OperatorRing
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Order.Preorder.Finite

/-! Independent specification of the projection arguments in PV13 and PV19. -/

open scoped BigOperators nonZeroDivisors

namespace GaloisFormalization.PV.ProjectionKernels

universe u v

variable {ι : Type u} {K : ι → Type v} [∀ i, Field (K i)]

/-- The restriction of a field projection to the unital subring. -/
def coordinate (S : Subring (∀ i, K i)) (i : ι) : S →+* K i :=
  (Pi.evalRingHom K i).comp S.subtype

def kernel (S : Subring (∀ i, K i)) (i : ι) : Ideal S :=
  RingHom.ker (coordinate S i)

/-- The index type counts each distinct projection kernel once. -/
def Index (S : Subring (∀ i, K i)) := Set.range (kernel S)

def ofCoordinate (S : Subring (∀ i, K i)) (i : ι) : Index S :=
  ⟨kernel S i, ⟨i, rfl⟩⟩

instance (S : Subring (∀ i, K i)) : PartialOrder (Index S) :=
  inferInstanceAs (PartialOrder {P : Ideal S // P ∈ Set.range (kernel S)})

instance (S : Subring (∀ i, K i)) [Finite ι] : Finite (Index S) :=
  Finite.Set.finite_range (kernel S)

noncomputable instance (S : Subring (∀ i, K i)) [Finite ι] : Fintype (Index S) :=
  Fintype.ofFinite _

/-- A factor and its image under the operator have the same vanishing condition
after application of the operator. This expresses transport of the factor kernels. -/
def PermutesFactors (σ : (∀ i, K i) ≃+* (∀ i, K i)) (p : Equiv.Perm ι) : Prop :=
  ∀ (x : ∀ i, K i) (i : ι), σ x (p i) = 0 ↔ x i = 0

def Transitive {α : Type*} (p : Equiv.Perm α) : Prop :=
  ∀ i j, ∃ n : ℕ, (p^[n]) i = j

/-- The induced automorphism of the operator subring. -/
def restrict (σ : (∀ i, K i) ≃+* (∀ i, K i))
    (S : PV.Specs.subring (PV.Specs.difference σ)) : S.val ≃+* S.val where
  toFun x := ⟨σ x.val, S.property.1 x.property⟩
  invFun x := ⟨σ.symm x.val, S.property.2 x.property⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply x.val)
  right_inv x := Subtype.ext (σ.apply_symm_apply x.val)
  map_mul' x y := Subtype.ext (map_mul σ x.val y.val)
  map_add' x y := Subtype.ext (map_add σ x.val y.val)

def IsTest {S : Subring (∀ i, K i)} (P : Index S) (x : S) : Prop :=
  x ∉ P.val ∧ ∀ T : Index S, T ≠ P → x ∈ T.val

def RegularElementsAreUnits (R : Type*) [CommRing R] : Prop :=
  ∀ x : R, x ∈ R⁰ → IsUnit x

end GaloisFormalization.PV.ProjectionKernels

namespace GaloisFormalization.PV.ProjectionKernels.Specs
universe u v

set_option linter.checkUnivs false

def permuted :=
  ∀ {ι : Type u} {K : ι → Type v} [∀ i, Field (K i)] [Finite ι] [Nonempty ι]
      (σ : (∀ i, K i) ≃+* (∀ i, K i)) (p : Equiv.Perm ι),
    PermutesFactors σ p → Transitive p → ∀ S : PV.Specs.subring (PV.Specs.difference σ),
    ∃ q : Equiv.Perm (Index S.val), Transitive q ∧
      (∀ i, q (ofCoordinate S.val i) = ofCoordinate S.val (p i)) ∧
      ∀ P, (q P).val = P.val.map (restrict σ S).toRingHom

def incomparable :=
  ∀ {ι : Type u} {K : ι → Type v} [∀ i, Field (K i)] [Finite ι] [Nonempty ι]
      (σ : (∀ i, K i) ≃+* (∀ i, K i)) (p : Equiv.Perm ι),
    PermutesFactors σ p → Transitive p → ∀ S : PV.Specs.subring (PV.Specs.difference σ),
    ∀ P T : Index S.val, P ≠ T → ¬ P.val ≤ T.val

def existsTest :=
  ∀ {ι : Type u} {K : ι → Type v} [∀ i, Field (K i)] [Finite ι] [Nonempty ι]
      (σ : (∀ i, K i) ≃+* (∀ i, K i)) (p : Equiv.Perm ι),
    PermutesFactors σ p → Transitive p → ∀ S : PV.Specs.subring (PV.Specs.difference σ),
    ∀ P : Index S.val, ∃ t : S.val, IsTest P t

def regularIffCoordinates :=
  ∀ {ι : Type u} {K : ι → Type v} [∀ i, Field (K i)] [Finite ι] [Nonempty ι]
      (σ : (∀ i, K i) ≃+* (∀ i, K i)) (p : Equiv.Perm ι),
    PermutesFactors σ p → Transitive p → ∀ (S : PV.Specs.subring (PV.Specs.difference σ))
      (x : S.val), x ∈ (S.val : Type _)⁰ ↔ ∀ i, coordinate S.val i x ≠ 0

def regularIffUnitInProduct :=
  ∀ {ι : Type u} {K : ι → Type v} [∀ i, Field (K i)] [Finite ι] [Nonempty ι]
      (σ : (∀ i, K i) ≃+* (∀ i, K i)) (p : Equiv.Perm ι),
    PermutesFactors σ p → Transitive p → ∀ (S : PV.Specs.subring (PV.Specs.difference σ))
      (x : S.val), x ∈ (S.val : Type _)⁰ ↔ IsUnit x.val

def orthogonalIdempotents := by
  classical
  exact
    ∀ {ι : Type u} {K : ι → Type v} [∀ i, Field (K i)] [Finite ι] [Nonempty ι]
      (σ : (∀ i, K i) ≃+* (∀ i, K i)) (p : Equiv.Perm ι),
      PermutesFactors σ p → Transitive p → ∀ S : PV.Specs.subring (PV.Specs.difference σ),
      RegularElementsAreUnits (S.val : Type _) →
      ∃ (t : Index S.val → S.val) (s : (S.val : Type _)ˣ) (e : Index S.val → S.val),
        (∀ P, IsTest P (t P)) ∧
        (s : S.val) = ∑ P, t P ∧
        (∀ P, e P = t P * (↑s⁻¹ : S.val)) ∧
        (∀ P i, coordinate S.val i (e P) = if ofCoordinate S.val i = P then 1 else 0) ∧
        (∀ P, e P * e P = e P) ∧
        (∀ P T, P ≠ T → e P * e T = 0) ∧
        ∑ P, e P = 1

def decomposition :=
  ∀ {ι : Type u} {K : ι → Type v} [∀ i, Field (K i)] [Finite ι] [Nonempty ι]
      (σ : (∀ i, K i) ≃+* (∀ i, K i)) (p : Equiv.Perm ι),
    PermutesFactors σ p → Transitive p → ∀ S : PV.Specs.subring (PV.Specs.difference σ),
    RegularElementsAreUnits (S.val : Type _) →
    ∃ (q : Equiv.Perm (Index S.val)) (g : (S.val : Type _) ≃+* (∀ P : Index S.val, S.val ⧸ P.val))
      (τ : ∀ P : Index S.val, (S.val ⧸ P.val) ≃+* (S.val ⧸ (q P).val)),
      Transitive q ∧
      (∀ i, q (ofCoordinate S.val i) = ofCoordinate S.val (p i)) ∧
      (∀ P : Index S.val, IsField (S.val ⧸ P.val)) ∧
      (∀ (x : S.val) (P : Index S.val), g x P = Ideal.Quotient.mk P.val x) ∧
      ∀ (x : S.val) (P : Index S.val), g (restrict σ S x) (q P) = τ P (g x P)


def subringIsField :=
  ∀ {L : Type v} [Field L] (S : Subring L),
    RegularElementsAreUnits (S : Type v) → IsField (S : Type v)

end GaloisFormalization.PV.ProjectionKernels.Specs
