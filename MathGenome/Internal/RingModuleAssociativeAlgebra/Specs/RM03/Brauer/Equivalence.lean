import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.Defs
import Mathlib.Algebra.Central.Basic
import Mathlib.Algebra.Field.ULift
import Mathlib.RingTheory.SimpleRing.Basic

/-! The equivalence and division representative assertions of RM03-C04.11. -/

-- The types of the expected definitions quantify over independent universes.
set_option linter.checkUnivs false

universe u v w x y

namespace Specs.RM03.Brauer

def EquivalentType :=
  ∀ (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A]
    (B : Type w) [Ring B] [Algebra k B], Prop

def equivalent (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A]
    (B : Type w) [Ring B] [Algebra k B] : Prop :=
  ∃ p q : ℕ, 0 < p ∧ 0 < q ∧
    Nonempty (Matrix (Fin p) (Fin p) A ≃ₐ[k] Matrix (Fin q) (Fin q) B)

def EquivalentIffIsBrauerEquivalent : Prop :=
  ∀ (k : Type u) [Field k] (A B : _root_.CSA.{u, v} k),
    equivalent k A B ↔ IsBrauerEquivalent A B

def EquivalenceOnCSA : Prop :=
  ∀ (k : Type u) [Field k],
    Equivalence (fun A B : _root_.CSA.{u, v} k => equivalent k A B)

def EquivalentIffDivisionFactors : Prop :=
  ∀ (k : Type u) [Field k]
    (A : Type v) [Ring A] [Algebra k A] (B : Type w) [Ring B] [Algebra k B],
    CSA.isCentralSimple k A → CSA.isCentralSimple k B →
    ∀ (D : Type x) [DivisionRing D] [Algebra k D]
      (E : Type y) [DivisionRing E] [Algebra k E],
      CSA.isCentralDivision k D → CSA.isCentralDivision k E →
      ∀ (r s : ℕ), 0 < r → 0 < s →
        (A ≃ₐ[k] Matrix (Fin r) (Fin r) D) →
        (B ≃ₐ[k] Matrix (Fin s) (Fin s) E) →
        (equivalent k A B ↔ Nonempty (D ≃ₐ[k] E))

def ClassOfType :=
  ∀ {k : Type u} [Field k], _root_.CSA.{u, v} k → BrauerGroup.{u, v} k

def classOf {k : Type u} [Field k] (A : _root_.CSA.{u, v} k) : BrauerGroup.{u, v} k :=
  Quotient.mk (Brauer.CSA_Setoid k) A

def ClassOfEqIff : Prop :=
  ∀ (k : Type u) [Field k] (A B : _root_.CSA.{u, v} k),
    classOf A = classOf B ↔ equivalent k A B

def DivisionCSAType :=
  ∀ {k : Type u} [Field k] {D : Type v} [DivisionRing D] [Algebra k D],
    CSA.isCentralDivision k D → _root_.CSA.{u, v} k

def divisionCSA {k : Type u} [Field k] {D : Type v} [DivisionRing D] [Algebra k D]
    (h : CSA.isCentralDivision k D) : _root_.CSA.{u, v} k :=
  CSA.toCSA ⟨inferInstance, h.1, h.2⟩

def ExistsDivisionRepresentative : Prop :=
  ∀ (k : Type u) [Field k] (c : BrauerGroup.{u, v} k),
    ∃ (D : Type v) (_ : DivisionRing D) (_ : Algebra k D)
      (h : CSA.isCentralDivision k D), classOf (divisionCSA h) = c

def ClassOfDivisionEqIff : Prop :=
  ∀ (k : Type u) [Field k] (D E : Type v)
    [DivisionRing D] [Algebra k D] [DivisionRing E] [Algebra k E]
    (hD : CSA.isCentralDivision k D) (hE : CSA.isCentralDivision k E),
    classOf (divisionCSA hD) = classOf (divisionCSA hE) ↔ Nonempty (D ≃ₐ[k] E)

def EquivalentIffSplit : Prop :=
  ∀ (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A],
    CSA.isCentralSimple k A → (equivalent k A k ↔ CSA.isSplit k A)

def ScalarCSAType :=
  ∀ (k : Type u) [Field k], _root_.CSA.{u, max u v} k

/-- Represent the base field in any carrier universe that contains its lift. -/
def scalarCSA (k : Type u) [Field k] : _root_.CSA.{u, max u v} k :=
  CSA.toCSA (A := ULift.{v} k)
    ⟨inferInstance, ⟨fun x _ => Algebra.mem_bot.mpr ⟨x.down, rfl⟩⟩,
      FiniteDimensional.of_injective (ULift.algEquiv (R := k)).toLinearEquiv.toLinearMap
        (ULift.algEquiv (R := k)).injective⟩

def ClassOfEqScalarIffSplit : Prop :=
  ∀ (k : Type u) [Field k] (A : _root_.CSA.{u, max u v} k),
    classOf A = classOf (scalarCSA.{u, v} k) ↔ CSA.isSplit k A

end Specs.RM03.Brauer
