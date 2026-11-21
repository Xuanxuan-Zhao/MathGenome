import MathGenome.Internal.AlgebraCore.Specs.P103.Ch05.AssociatedPrimesInterface
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch02.FiniteLength
import Mathlib.RingTheory.Spectrum.Prime.Module

/-!
Independent statements for the finite-colength part of Theorem 6.2,
paper.tex:1056–1061. `Q • ⊤` is the submodule QM, finite means finitely
generated, and support is the shared localization-defined support.
`IsFiniteLength` means existence of a finite composition series; both the
extended and natural-number lengths of the zero module are recorded.
The proper-ideal hypothesis in the radical criterion is explicit.
-/
namespace P103.Specs.Ch06.FiniteColength

universe u v
open P103.Specs.Ch05.AssociatedPrimesInterface
open P103.Specs.Ch02.FiniteLength

/-- The support formula also holds without the local or Noetherian hypotheses. -/
def support_quotientType : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (Q : Ideal R),
    supportValue R (M ⧸ (Q • (⊤ : Submodule R M))) =
      PrimeSpectrum.zeroLocus ((Q ⊔ Module.annihilator R M : Ideal R) : Set R)

def quotient_nontrivialType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (Q : Ideal R), Q ≤ IsLocalRing.maximalIdeal R →
    Nontrivial (M ⧸ (Q • (⊤ : Submodule R M)))

def support_singleton_iff_finite_lengthType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M],
    supportValue R M = {IsLocalRing.closedPoint R} ↔ IsFiniteLength R M

/-- A positive power of the maximal ideal annihilates a module of this support. -/
def maximalIdeal_pow_annihilatesType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M],
    supportValue R M = {IsLocalRing.closedPoint R} →
    ∃ n : ℕ, 0 < n ∧ (IsLocalRing.maximalIdeal R) ^ n ≤ Module.annihilator R M

def finite_colength_iffType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (Q : Ideal R), Q ≤ IsLocalRing.maximalIdeal R →
    (IsFiniteLength R (M ⧸ (Q • (⊤ : Submodule R M))) ↔
      (Q ⊔ Module.annihilator R M).radical = IsLocalRing.maximalIdeal R)

def zero_moduleType : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    [Subsingleton M],
    IsFiniteLength R M ∧ Module.length R M = 0 ∧ lengthValue R M = 0 ∧
      supportValue R M = ∅

/-- For Q = R the quotient is zero, including when R itself is the zero ring. -/
def top_quotientType : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    let T := M ⧸ ((⊤ : Ideal R) • (⊤ : Submodule R M))
    Subsingleton T ∧ IsFiniteLength R T ∧ Module.length R T = 0 ∧
      lengthValue R T = 0 ∧ supportValue R T = ∅

end P103.Specs.Ch06.FiniteColength
