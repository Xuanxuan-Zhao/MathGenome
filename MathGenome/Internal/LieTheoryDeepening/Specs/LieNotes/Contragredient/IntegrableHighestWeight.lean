import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.SimpleHighestWeight

/-! The rank-one identity and integrability criterion for contragredient highest weights. -/

namespace Specs.LieNotes.Contragredient.IntegrableHighestWeight

open CartanData CartanQuotient
open SimpleHighestWeight (L)
open VermaModules (IsHighestVector IsWeightCharacter)
open _root_.RepTheorySurvey.CategoryO.BorelInduction (U scalarModule)
open UniversalEnvelopingAlgebra (ι)

universe u v w

/-- The raising operator on the `(n + 1)`st lowering power of a highest vector. -/
def RankOneIdentity : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I],
    IsGeneralizedCartanMatrix A → ∀ (R : Realization A H) (Λ : Module.Dual ℂ H)
      (V : Type w) [AddCommGroup V] [Module (U (Algebra R)) V],
      letI := scalarModule (B := U (Algebra R)) V
      ∀ (z : V), IsHighestVector R Λ z → ∀ (i : I) (n : ℕ),
        ι ℂ (e R i) • ((ι ℂ (f R i) : U (Algebra R)) ^ (n + 1) • z) =
          (((n : ℂ) + 1) * (Λ (R.h i) - (n : ℂ))) •
            ((ι ℂ (f R i) : U (Algebra R)) ^ n • z)

/-- The simple highest-weight quotient is integrable precisely at dominant integral weights. -/
def IntegrabilityCriterion : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I],
    IsGeneralizedCartanMatrix A → ∀ (R : Realization A H) (Λ : Module.Dual ℂ H)
      (hχ : ∃! χ, IsWeightCharacter R Λ χ),
      ((∀ (i : I) (z : L R Λ hχ), ∃ n : ℕ, (ι ℂ (e R i) : U (Algebra R)) ^ n • z = 0) ∧
       (∀ (i : I) (z : L R Λ hχ), ∃ n : ℕ, (ι ℂ (f R i) : U (Algebra R)) ^ n • z = 0)) ↔
      ∀ i : I, ∃ m : ℕ, Λ (R.h i) = (m : ℂ)

end Specs.LieNotes.Contragredient.IntegrableHighestWeight
