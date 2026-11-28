import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.BabyVermaQuotients
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! The nonzero semisimple case of the classification of reduced `sl₂`-modules. -/

namespace Specs.LieNotes.SuperRestricted.BabyVermaSemisimple

open _root_.Specs.LieAlgebrasAndRepresentations.Sl2Model (Model E F H)
open _root_.Specs.LieNotes.SuperRestricted.RestrictedLie (restrictedPowerValue)
open _root_.Specs.LieNotes.SuperRestricted.BabyVermaInduction

universe u w

/-- The Artin–Schreier labels for the baby Verma modules at `χ`. -/
abbrev Weights {k : Type u} [Field k] (p : ℕ) (χ : Model k →ₗ[k] k) :=
  {weight : k // weight ^ p - weight = χ (H k) ^ p}

/-- The kernel of the raising generator is the nonzero highest line,
on which the diagonal generator has the indicated weight. -/
def HighestWeightLine {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
    {P : restrictedPowerValue k p (Model k)} {Q : restrictedPowerValue k p (Borel k)}
    {χ : Model k →ₗ[k] k} (j : BorelAlgebra Q χ →ₐ[k] Ambient P χ)
    (θ : BorelAlgebra Q χ →ₐ[k] k) (weight : k) : Prop :=
  highest j θ ≠ 0 ∧
  (∀ v : BabyVerma j θ, generator P χ (E k) • v = 0 ↔
    ∃ c : k, v = c • highest j θ) ∧
  generator P χ (H k) • highest j θ = weight • highest j θ

/-- There are exactly `p` distinct labels. The actual modules induced from the
reduced upper triangular Borel are simple of dimension `p`, and their labels
parametrize all simple modules of the reduced algebra up to isomorphism. -/
def babyVermaSemisimpleType : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] {p : ℕ} [CharP k p] (hp : 2 < p),
    letI : NeZero p := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hp)⟩
    ∀ (P : restrictedPowerValue k p (Model k)), MatrixPower P →
    ∀ (χ : Model k →ₗ[k] k), χ (E k) = 0 → χ (F k) = 0 → χ (H k) ≠ 0 →
      Nonempty (Weights p χ ≃ Fin p) ∧
      ∃ (Q : restrictedPowerValue k p (Borel k))
        (j : BorelAlgebra Q χ →ₐ[k] Ambient P χ),
        InheritedPower P Q ∧ CanonicalInclusion P Q χ j ∧ Function.Injective j ∧
        ∃ θ : Weights p χ → (BorelAlgebra Q χ →ₐ[k] k),
          (∀ weight, LineCharacter Q χ weight.val (θ weight) ∧
            IsSimpleModule (Ambient P χ) (BabyVerma j (θ weight)) ∧
            Module.finrank k (BabyVerma j (θ weight)) = p ∧
            HighestWeightLine j (θ weight) weight.val) ∧
          (∀ weight weight', Nonempty
            (BabyVerma j (θ weight) ≃ₗ[Ambient P χ] BabyVerma j (θ weight')) ↔
            weight = weight') ∧
          ∀ (V : Type w) [AddCommGroup V] [Module (Ambient P χ) V]
            [IsSimpleModule (Ambient P χ) V],
            ∃ weight, Nonempty (BabyVerma j (θ weight) ≃ₗ[Ambient P χ] V)

end Specs.LieNotes.SuperRestricted.BabyVermaSemisimple
