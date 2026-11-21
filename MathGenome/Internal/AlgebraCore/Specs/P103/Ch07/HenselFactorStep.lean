import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Jacobson.Ideal

/-! Independent one-power factor improvement, paper.tex:1313–1320.
All coefficient rings are commutative and unital; the zero ring is allowed. -/
universe u
namespace P103.Specs.Ch07.HenselFactorStep
open Polynomial

/-- Every linear map from bounded coefficient vectors preserves each coefficient ideal. -/
def bounded_linearMap_preserves_coefficientsType : Prop :=
  ∀ {R : Type u} [CommRing R] (J : Ideal R) (d : ℕ)
    (T : degreeLT R d →ₗ[R] R[X]) (p : degreeLT R d),
    (∀ k, p.val.coeff k ∈ J) → ∀ k, (T p).coeff k ∈ J

/-- Improve a monic approximate factorization by one power, without changing degrees. -/
def factor_stepType : Prop :=
  ∀ {R : Type u} [CommRing R] (I : Ideal R)
    (_hI : I ≤ Ideal.jacobson ⊥) (n : ℕ) (f g h : R[X]),
    f.Monic → g.Monic → h.Monic →
    f.natDegree = g.natDegree + h.natDegree →
    IsCoprime (g.map (Ideal.Quotient.mk I)) (h.map (Ideal.Quotient.mk I)) →
    (∀ k, (f - g * h).coeff k ∈ I ^ (n + 1)) →
    ∃ g' h' : R[X], g'.Monic ∧ h'.Monic ∧
      g'.natDegree = g.natDegree ∧ h'.natDegree = h.natDegree ∧
      (∀ k, (g' - g).coeff k ∈ I ^ (n + 1)) ∧
      (∀ k, (h' - h).coeff k ∈ I ^ (n + 1)) ∧
      (∀ k, (f - g' * h').coeff k ∈ I ^ (n + 2))

end P103.Specs.Ch07.HenselFactorStep
