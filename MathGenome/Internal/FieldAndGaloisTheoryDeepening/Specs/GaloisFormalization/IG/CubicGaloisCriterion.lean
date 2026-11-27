import Mathlib.Algebra.CubicDiscriminant
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-! The root action and discriminant criterion used in the proof of IG13. -/

open Polynomial
open scoped Polynomial

namespace GaloisFormalization.IG

noncomputable section

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The coefficient discriminant of a degree-three polynomial. -/
def cubicDiscriminant (p : K[X]) : K :=
  (⟨p.coeff 3, p.coeff 2, p.coeff 1, p.coeff 0⟩ : Cubic K).discr

/-- The product over pairs of indices, with the earlier root first in each difference. -/
def cubicVandermonde {R : Type*} [Ring R] (r : Fin 3 → R) : R :=
  (r 0 - r 1) * (r 0 - r 2) * (r 1 - r 2)

/-- The root permutation associated with a field automorphism, in the chosen ordering. -/
def cubicRootAction {p : K[X]} [p.IsSplittingField K L]
    (e : Fin 3 ≃ p.rootSet L) : (L ≃ₐ[K] L) →* Equiv.Perm (Fin 3) :=
  letI : Fact (p.map (algebraMap K L)).Splits := ⟨IsSplittingField.splits L p⟩
  e.symm.permCongrHom.toMonoidHom.comp
    ((Polynomial.Gal.galActionHom p L).comp (Polynomial.Gal.restrict p L))

/-- An ordering of the distinct roots that can be used with the cubic criterion. -/
abbrev CubicRootOrdering (p : K[X]) (L : Type*) [Field L] [Algebra K L] :=
  Fin 3 ≃ p.rootSet L

end

namespace CubicCriterionSpec

universe u v

def Ordering : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (p : K[X]) [p.IsSplittingField K L],
    p.natDegree = 3 → p.Separable → Nonempty (CubicRootOrdering p L)

def ActionEvaluation : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {p : K[X]} [p.IsSplittingField K L]
    (e : CubicRootOrdering p L) (σ : L ≃ₐ[K] L) (i : Fin 3),
    (e (cubicRootAction e σ i)).val = σ (e i).val

def FaithfulTransitive : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {p : K[X]} [p.IsSplittingField K L] (e : CubicRootOrdering p L),
    Irreducible p →
      Function.Injective (cubicRootAction e) ∧
        ∀ i j : Fin 3, ∃ σ : L ≃ₐ[K] L, cubicRootAction e σ i = j

def DiscriminantOfRoots : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (p : K[X]) (r : Fin 3 → L),
    p.Monic → p.natDegree = 3 →
      (p.map (algebraMap K L)).roots = {r 0, r 1, r 2} →
        cubicVandermonde r ^ 2 = algebraMap K L (cubicDiscriminant p)

def Discriminant : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {p : K[X]} (e : CubicRootOrdering p L),
    p.Monic → p.natDegree = 3 → p.Separable →
      cubicVandermonde (fun i => (e i).val) ^ 2 = algebraMap K L (cubicDiscriminant p)

def PermutationSign : Prop :=
  ∀ {R : Type u} [CommRing R] (r : Fin 3 → R) (π : Equiv.Perm (Fin 3)),
    cubicVandermonde (r ∘ π) = ((Equiv.Perm.sign π : ℤ) : R) * cubicVandermonde r

def Sign : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {p : K[X]} [p.IsSplittingField K L] (e : CubicRootOrdering p L) (σ : L ≃ₐ[K] L),
    σ (cubicVandermonde (fun i => (e i).val)) =
      ((Equiv.Perm.sign (cubicRootAction e σ) : ℤ) : L) *
        cubicVandermonde (fun i => (e i).val)

def SquareInBase : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {p : K[X]} (e : CubicRootOrdering p L),
    p.Monic → p.natDegree = 3 → p.Separable →
      (cubicVandermonde (fun i => (e i).val) ∈ Set.range (algebraMap K L) ↔
        IsSquare (cubicDiscriminant p))

def AlternatingIffBase : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {p : K[X]} [p.IsSplittingField K L] (e : CubicRootOrdering p L) [CharZero K],
    p.Separable →
      ((cubicRootAction e).range ≤ alternatingGroup (Fin 3) ↔
        cubicVandermonde (fun i => (e i).val) ∈ Set.range (algebraMap K L))

def AlternatingIffSquare : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {p : K[X]} [p.IsSplittingField K L] (e : CubicRootOrdering p L) [CharZero K],
    p.Monic → p.natDegree = 3 → p.Separable →
      ((cubicRootAction e).range ≤ alternatingGroup (Fin 3) ↔ IsSquare (cubicDiscriminant p))

def FullGroup : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {p : K[X]} [p.IsSplittingField K L] (e : CubicRootOrdering p L) [CharZero K],
    p.Monic → p.natDegree = 3 → p.Separable → Irreducible p → ¬ IsSquare (cubicDiscriminant p) →
      ∃ φ : (L ≃ₐ[K] L) ≃* Equiv.Perm (Fin 3), φ.toMonoidHom = cubicRootAction e

def NonsquareCriterion : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {p : K[X]} [p.IsSplittingField K L] [CharZero K],
    p.Monic → p.natDegree = 3 → p.Separable → Irreducible p → ¬ IsSquare (cubicDiscriminant p) →
      ∃ (e : CubicRootOrdering p L) (φ : (L ≃ₐ[K] L) ≃* Equiv.Perm (Fin 3)),
        φ.toMonoidHom = cubicRootAction e

end CubicCriterionSpec
end GaloisFormalization.IG
