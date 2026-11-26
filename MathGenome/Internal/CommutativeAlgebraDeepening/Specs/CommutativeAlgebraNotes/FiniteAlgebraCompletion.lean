import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Algebra.Pi

open scoped TensorProduct
open Ideal IsLocalRing

namespace Specs.CommutativeAlgebraNotes.FiniteAlgebraCompletion

section CompletionMap

variable {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)

theorem factorPow_eval (x : AdicCompletion I R) {m n : ℕ} (hmn : m ≤ n) :
    Ideal.Quotient.factorPow I hmn (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I R x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
  exact AdicCompletion.Ideal.mk_eq_mk I hmn a

def quotientPowMap (f : R →+* S) (h : I.map f ≤ J) (n : ℕ) :
    (R ⧸ I ^ n) →+* S ⧸ J ^ n :=
  Ideal.quotientMap (J ^ n) f
    (Ideal.map_le_iff_le_comap.mp (by rw [Ideal.map_pow]; exact Ideal.pow_right_mono h n))

private theorem quotientPowMap_compatible (f : R →+* S) (h : I.map f ≤ J)
    {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow J hmn).comp
        ((quotientPowMap I J f h n).comp (AdicCompletion.evalₐ I n).toRingHom) =
      (quotientPowMap I J f h m).comp (AdicCompletion.evalₐ I m).toRingHom := by
  ext1 x
  have e := factorPow_eval I x hmn
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← hr] at e
  change Ideal.Quotient.mk (I ^ m) r = _ at e
  change Ideal.Quotient.factorPow J hmn
    (quotientPowMap I J f h n (AdicCompletion.evalₐ I n x)) =
      quotientPowMap I J f h m (AdicCompletion.evalₐ I m x)
  rw [← hr, ← e]
  rfl

/-- The map of adic completions induced by a ring homomorphism sending one ideal
into the other. -/
noncomputable def completionMap (f : R →+* S) (h : I.map f ≤ J) :
    AdicCompletion I R →+* AdicCompletion J S :=
  AdicCompletion.liftRingHom J
    (fun n ↦ (quotientPowMap I J f h n).comp (AdicCompletion.evalₐ I n).toRingHom)
    (quotientPowMap_compatible I J f h)

@[simp]
theorem eval_completionMap (f : R →+* S) (h : I.map f ≤ J)
    (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ J n (completionMap I J f h x) =
      quotientPowMap I J f h n (AdicCompletion.evalₐ I n x) := by
  exact AdicCompletion.evalₐ_liftRingHom J _ (quotientPowMap_compatible I J f h) n x

@[simp]
theorem quotientPowMap_mk (f : R →+* S) (h : I.map f ≤ J) (n : ℕ) (r : R) :
    quotientPowMap I J f h n (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ (f r) := rfl

@[simp]
theorem completionMap_of (f : R →+* S) (h : I.map f ≤ J) (r : R) :
    completionMap I J f h (AdicCompletion.of I R r) = AdicCompletion.of J S (f r) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  simp

end CompletionMap

universe u v

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- The primes of the finite algebra whose contraction is the specified prime. -/
abbrev PrimesOver (p : Ideal A) (B : Type v) [CommRing B] [Algebra A B] :=
  {q : PrimeSpectrum B // Ideal.comap (algebraMap A B) q.asIdeal = p}

instance {p : Ideal A} (q : PrimesOver p B) : q.1.asIdeal.IsPrime := q.1.isPrime

instance {p : Ideal A} (q : PrimesOver p B) : q.1.asIdeal.LiesOver p := ⟨q.2.symm⟩

variable (p : Ideal A) [p.IsPrime]

abbrev LocalCompletion (R : Type*) [CommRing R] [IsLocalRing R] :=
  AdicCompletion (maximalIdeal R) R

abbrev Factor (q : PrimesOver p B) := LocalCompletion (Localization.AtPrime q.1.asIdeal)

noncomputable instance (q : PrimesOver p B) :
    Algebra (Localization.AtPrime p) (Localization.AtPrime q.1.asIdeal) :=
  Localization.AtPrime.algebraOfLiesOver p q.1.asIdeal

instance (q : PrimesOver p B) :
    IsScalarTower A (Localization.AtPrime p) (Localization.AtPrime q.1.asIdeal) :=
  inferInstanceAs (letI := Localization.AtPrime.algebraOfLiesOver p q.1.asIdeal
    IsScalarTower A (Localization.AtPrime p) (Localization.AtPrime q.1.asIdeal))

theorem map_maximal_le (q : PrimesOver p B) :
    (maximalIdeal (Localization.AtPrime p)).map
      (algebraMap (Localization.AtPrime p) (Localization.AtPrime q.1.asIdeal)) ≤
        maximalIdeal (Localization.AtPrime q.1.asIdeal) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal (I := p), Ideal.map_map,
    ← IsScalarTower.algebraMap_eq A (Localization.AtPrime p),
    IsScalarTower.algebraMap_eq A B (Localization.AtPrime q.1.asIdeal), ← Ideal.map_map,
    ← Localization.AtPrime.map_eq_maximalIdeal (I := q.1.asIdeal)]
  exact Ideal.map_mono (Ideal.map_le_iff_le_comap.mpr q.2.ge)

noncomputable def fromBaseCompletion (q : PrimesOver p B) :
    LocalCompletion (Localization.AtPrime p) →ₐ[Localization.AtPrime p] Factor p q where
  __ := completionMap _ _ (algebraMap _ _) (map_maximal_le p q)
  commutes' r := completionMap_of _ _ _ _ r

/-- The canonical product map extends the local base maps on adic quotients
and uses the canonical maps from the finite algebra to its completed stalks. -/
noncomputable def comparison :
    (LocalCompletion (Localization.AtPrime p) ⊗[A] B) →ₐ[Localization.AtPrime p]
      ((q : PrimesOver p B) → Factor p q) :=
  AlgHom.pi fun q ↦ Algebra.TensorProduct.lift (fromBaseCompletion p q)
    (IsScalarTower.toAlgHom A B (Factor p q)) (fun _ _ ↦ Commute.all _ _)

def FinitePrimes : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    (p : Ideal A) [p.IsPrime], Finite (PrimesOver p B)

def CanonicalDecomposition : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    [IsNoetherianRing A] [IsNoetherianRing B] (p : Ideal A) [p.IsPrime],
    Function.Bijective (comparison (B := B) p)

end Specs.CommutativeAlgebraNotes.FiniteAlgebraCompletion
