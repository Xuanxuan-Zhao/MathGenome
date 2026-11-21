import MathGenome.Internal.Specs.D07.Ch10.PidDefinition

/-!
Independent specification for `lem:dedekind-hasse-sufficient`, paper.tex:2079–2090.
The norm is only a natural-number-valued function, zero at zero and positive
away from zero. Neither multiplicativity nor a division algorithm is assumed.
-/

universe u

namespace Specs.D07.Ch10.DedekindHasseSufficient

/-- The sufficient Dedekind–Hasse criterion, including all ideals, with the
commutative nontrivial domain hypothesis retained. -/
def EveryIdealPrincipal : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (N : R → ℕ),
    N 0 = 0 →
    (∀ x : R, x ≠ 0 → 0 < N x) →
    (∀ a b : R, a ≠ 0 → b ≠ 0 → ¬ b ∣ a →
      ∃ s t : R, 0 < N (s * a - t * b) ∧ N (s * a - t * b) < N b) →
    ∀ I : Ideal R, ∃ b : R, I = Ideal.span {b}

/-- The same criterion expressed with the shared definition of a PID. -/
def DedekindHassePID : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (N : R → ℕ),
    N 0 = 0 →
    (∀ x : R, x ≠ 0 → 0 < N x) →
    (∀ a b : R, a ≠ 0 → b ≠ 0 → ¬ b ∣ a →
      ∃ s t : R, 0 < N (s * a - t * b) ∧ N (s * a - t * b) < N b) →
    Specs.D07.Ch10.PidDefinition.pidPredicateValue R

end Specs.D07.Ch10.DedekindHasseSufficient
