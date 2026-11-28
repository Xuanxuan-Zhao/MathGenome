import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.BabyVermaSemisimple
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.BabyVermaNilpotent
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.SlTwoCharacterNormalForms

/-! Classification at an arbitrary nonzero character of restricted matrix `sl₂`. -/

namespace Specs.LieNotes.SuperRestricted.BabyVermaNonzero

open _root_.Specs.LieAlgebrasAndRepresentations.Sl2Model (Model E F H)
open _root_.Specs.LieNotes.SuperRestricted.RestrictedLie (restrictedPowerValue)
open _root_.Specs.LieNotes.SuperRestricted.SlTwoCharacterNormalForms
  (Mat₂ IsMatrixConjugation tracePairingValue)
open _root_.Specs.LieNotes.SuperRestricted.BabyVermaInduction
open _root_.Specs.LieNotes.SuperRestricted.BabyVermaSemisimple (Weights HighestWeightLine)
open _root_.Specs.LieNotes.SuperRestricted.BabyVermaNilpotent
  (primeFieldEmbedding labelSetoid labelInvolution)

universe u w v

section Classification

variable {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
variable {P : restrictedPowerValue k p (Model k)} {χ ψ : Model k →ₗ[k] k}
variable (f : Ambient P χ ≃ₐ[k] Ambient P ψ)
variable {Q : restrictedPowerValue k p (Borel k)}
variable (j : BorelAlgebra Q ψ →ₐ[k] Ambient P ψ)
variable {ι : Type v} (θ : ι → BorelAlgebra Q ψ →ₐ[k] k)

/-- The induced modules at the normalized character, pulled back to the original
reduced algebra via `f`, are simple of dimension `p`. They exhaust the simple modules
and two of them are isomorphic exactly for the specified relation on the labels. -/
def Classifies (r : ι → ι → Prop) : Prop :=
  (∀ i,
    letI : Module (Ambient P χ) (BabyVerma j (θ i)) :=
      Module.compHom (BabyVerma j (θ i)) f.toRingHom
    IsSimpleModule (Ambient P χ) (BabyVerma j (θ i)) ∧
      IsScalarTower k (Ambient P χ) (BabyVerma j (θ i)) ∧
      Module.finrank k (BabyVerma j (θ i)) = p) ∧
  (∀ i i',
    letI : Module (Ambient P χ) (BabyVerma j (θ i)) :=
      Module.compHom (BabyVerma j (θ i)) f.toRingHom
    letI : Module (Ambient P χ) (BabyVerma j (θ i')) :=
      Module.compHom (BabyVerma j (θ i')) f.toRingHom
    Nonempty (BabyVerma j (θ i) ≃ₗ[Ambient P χ] BabyVerma j (θ i')) ↔ r i i') ∧
  (∀ (V : Type w) [AddCommGroup V] [Module (Ambient P χ) V]
      [IsSimpleModule (Ambient P χ) V],
    ∃ i,
      letI : Module (Ambient P χ) (BabyVerma j (θ i)) :=
        Module.compHom (BabyVerma j (θ i)) f.toRingHom
      Nonempty (BabyVerma j (θ i) ≃ₗ[Ambient P χ] V))

end Classification

/-- After conjugation, the nonzero semisimple case has the Artin–Schreier labels,
and the nilpotent case has the prime-field labels modulo `m ↦ -m - 2`.
The resulting families classify simple modules over the original reduced algebra. -/
def babyVermaNonzeroType : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] {p : ℕ} [CharP k p] (hp : 2 < p),
    letI : NeZero p := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hp)⟩
    ∃ P : restrictedPowerValue k p (Model k), MatrixPower P ∧
      ∀ χ : Model k →ₗ[k] k, χ ≠ 0 →
        ∃ (X : Model k) (U : (Mat₂ k)ˣ) (c : Model k ≃ₗ⁅k⁆ Model k),
          χ = tracePairingValue X ∧ IsMatrixConjugation U c ∧
          let ψ := χ.comp c.symm.toLinearEquiv.toLinearMap
          ψ = tracePairingValue (c X) ∧
          ∃ f : Ambient P χ ≃ₐ[k] Ambient P ψ,
            (∀ Y, f (generator P χ Y) = generator P ψ (c Y)) ∧
            ((∃ a : k, a ≠ 0 ∧ a ≠ -a ∧ (c X).val = Matrix.diagonal ![a, -a] ∧
              X.val.charpoly =
                (Polynomial.X (R := k) - Polynomial.C a) * (Polynomial.X (R := k) - Polynomial.C (-a)) ∧
              ψ (E k) = 0 ∧ ψ (F k) = 0 ∧ ψ (H k) = 2 * a ∧ ψ (H k) ≠ 0 ∧
              Nonempty (Weights p ψ ≃ Fin p) ∧
              ∃ (Q : restrictedPowerValue k p (Borel k))
                (j : BorelAlgebra Q ψ →ₐ[k] Ambient P ψ),
                InheritedPower P Q ∧ CanonicalInclusion P Q ψ j ∧ Function.Injective j ∧
                ∃ θ : Weights p ψ → BorelAlgebra Q ψ →ₐ[k] k,
                  (∀ weight, LineCharacter Q ψ weight.val (θ weight) ∧
                    HighestWeightLine j (θ weight) weight.val) ∧
                  Classifies.{u, w, u} f j θ Eq) ∨
            ((c X) = E k ∧ X.val.charpoly = Polynomial.X (R := k) ^ 2 ∧
              ψ (E k) = 0 ∧ ψ (H k) = 0 ∧ ψ (F k) = 1 ∧
              ∃ (Q : restrictedPowerValue k p (Borel k))
                (j : BorelAlgebra Q ψ →ₐ[k] Ambient P ψ),
                InheritedPower P Q ∧ CanonicalInclusion P Q ψ j ∧ Function.Injective j ∧
                ∃ θ : ZMod p → BorelAlgebra Q ψ →ₐ[k] k,
                  (∀ m, LineCharacter Q ψ (primeFieldEmbedding k p m) (θ m)) ∧
                  Classifies.{u, w, 0} f j θ (labelSetoid p).r ∧
                  (∀ m : ZMod p, labelInvolution m = m ↔ m = -1) ∧
                  Nat.card (Quotient (labelSetoid p)) = (p + 1) / 2))

end Specs.LieNotes.SuperRestricted.BabyVermaNonzero
