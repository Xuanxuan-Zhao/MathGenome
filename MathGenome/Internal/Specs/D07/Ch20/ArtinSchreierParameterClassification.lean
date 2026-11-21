import MathGenome.Internal.Specs.D07.Ch20.ArtinSchreierTranslationDichotomy
import Mathlib.FieldTheory.AlgebraicClosure

/-! Independent statements for the parameter assertion in
K07.20.artin_schreier, paper.tex:6031–6040. The prime-field scalar is
explicitly nonzero. The first two statements allow any common overfield;
the final statement constructs both root fields in one algebraic closure. -/

noncomputable section
universe u v
namespace Specs.D07.Ch20.ArtinSchreierParameterClassification

/-- Equality of the two actual intermediate fields, for any choices of roots. -/
def RootFieldsEqualIff : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    (p : ℕ) [Fact p.Prime] [CharP K p] (a b : K) (θ η : Ω),
    (¬ ∃ u : K, u ^ p - u = a) → (¬ ∃ u : K, u ^ p - u = b) →
    θ ^ p - θ = algebraMap K Ω a → η ^ p - η = algebraMap K Ω b →
    (IntermediateField.adjoin K {θ} = IntermediateField.adjoin K {η} ↔
      ∃ (c : ZMod p) (u : K), c ≠ 0 ∧ b = ZMod.cast c * a + (u ^ p - u))

/-- Isomorphism is over K and equality is in the specified common overfield. -/
def RootFieldsIsomorphicIffEqual : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    (p : ℕ) [Fact p.Prime] [CharP K p] (a b : K) (θ η : Ω),
    (¬ ∃ u : K, u ^ p - u = a) → (¬ ∃ u : K, u ^ p - u = b) →
    θ ^ p - θ = algebraMap K Ω a → η ^ p - η = algebraMap K Ω b →
    (Nonempty (IntermediateField.adjoin K {θ} ≃ₐ[K]
      IntermediateField.adjoin K {η}) ↔
      IntermediateField.adjoin K {θ} = IntermediateField.adjoin K {η})

/-- Both root fields are constructed in the same algebraic closure. The
three equivalent conditions include the scaling by any nonzero F_p scalar. -/
def CommonClosureClassification : Prop :=
  ∀ (K : Type u) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (a b : K),
    (¬ ∃ u : K, u ^ p - u = a) → (¬ ∃ u : K, u ^ p - u = b) →
    ∃ θ η : AlgebraicClosure K,
      θ ^ p - θ = algebraMap K (AlgebraicClosure K) a ∧
      η ^ p - η = algebraMap K (AlgebraicClosure K) b ∧
      (IntermediateField.adjoin K {θ} = IntermediateField.adjoin K {η} ↔
        Nonempty (IntermediateField.adjoin K {θ} ≃ₐ[K]
          IntermediateField.adjoin K {η})) ∧
      (Nonempty (IntermediateField.adjoin K {θ} ≃ₐ[K]
        IntermediateField.adjoin K {η}) ↔
        ∃ (c : ZMod p) (u : K), c ≠ 0 ∧ b = ZMod.cast c * a + (u ^ p - u))

end Specs.D07.Ch20.ArtinSchreierParameterClassification
