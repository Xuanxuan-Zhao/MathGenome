import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.BabyVermaInduction
import Mathlib.RingTheory.SimpleModule.Basic

/-! Simple quotients of the induced baby Verma modules for restricted `sl₂`. -/

namespace Specs.LieNotes.SuperRestricted.BabyVermaQuotients

open _root_.Specs.LieAlgebrasAndRepresentations.Sl2Model (Model E F H)
open _root_.Specs.LieNotes.SuperRestricted.RestrictedLie (restrictedPowerValue)
open _root_.Specs.LieNotes.SuperRestricted.BabyVermaInduction

universe u w

/-- The induced modules for the Artin–Schreier weights have the stated bases
and actions, and every simple module is a quotient of a member of this family. -/
def babyVermaQuotientsType : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] {p : ℕ} [CharP k p] (hp : 2 < p),
    letI : NeZero p := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hp)⟩
    ∀ (P : restrictedPowerValue k p (Model k)), MatrixPower P →
    ∀ (χ : Model k →ₗ[k] k), χ (E k) = 0 →
      ∃ (Q : restrictedPowerValue k p (Borel k))
        (j : BorelAlgebra Q χ →ₐ[k] Ambient P χ),
        InheritedPower P Q ∧ CanonicalInclusion P Q χ j ∧ Function.Injective j ∧
        RightBasis j (fun i : Fin p => generator P χ (F k) ^ i.val) ∧
        ∃ θ : {weight : k // weight ^ p - weight = χ (H k) ^ p} → (BorelAlgebra Q χ →ₐ[k] k),
          (∀ weight, LineCharacter Q χ weight.val (θ weight) ∧
            BasisAndActions j (θ weight) weight.val ∧
            InductionProperty.{u, w} j (θ weight) weight.val) ∧
          ∀ (V : Type w) [AddCommGroup V] [Module (Ambient P χ) V]
            [IsSimpleModule (Ambient P χ) V],
            ∃ weight, ∃ f : BabyVerma j (θ weight) →ₗ[Ambient P χ] V, Function.Surjective f

end Specs.LieNotes.SuperRestricted.BabyVermaQuotients
