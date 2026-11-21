import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Extensions.H2Classification

/-! Example GR02-C04.04 in paper.tex, with the inhomogeneous (H^2) and fixed ends
from the preceding classification theorem. -/

namespace Specs.ALG02GroupTheory.Extensions.CyclicTwo

open _root_.ALG02GroupTheory.Extensions.NormalizedCohomology
open Specs.ALG02GroupTheory.Extensions.H2Classification

universe u

/-- The additive kernel. -/
abbrev A := ZMod 2

/-- The quotient, written multiplicatively. -/
abbrev C2 := Multiplicative (ZMod 2)

/-- The nonidentity element of the quotient. -/
def t : C2 := Multiplicative.ofAdd (1 : ZMod 2)

/-- The quotient acts trivially on the additive kernel. -/
scoped instance trivialAction : DistribMulAction C2 A where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- The direct product as an extension with its specified inclusion and projection. -/
def productExtension : GroupExtension (Multiplicative A) (Multiplicative A × C2) C2 where
  inl := MonoidHom.inl (Multiplicative A) C2
  rightHom := MonoidHom.snd (Multiplicative A) C2
  inl_injective := fun _ _ h => congrArg Prod.fst h
  range_inl_eq_ker_rightHom := by
    ext x
    change (∃ a : Multiplicative A, (a, 1) = x) ↔ x.2 = 1
    constructor
    · rintro ⟨_, rfl⟩
      rfl
    · intro hx
      exact ⟨x.1, Prod.ext rfl hx.symm⟩
  rightHom_surjective := fun q => ⟨(1, q), rfl⟩

/-- The crossed product belonging to a normalized cocycle for these end groups. -/
abbrev Middle (c : NormalizedCocycle C2 A) := crossedProductValue (cocycleFactorSystem c)

/-- The canonical lift `(0,t)` in the cocycle's crossed product. -/
abbrev lift (c : NormalizedCocycle C2 A) : Middle c :=
  (crossedProductSectionValue (cocycleFactorSystem c)).val t

def NormalizedCocycles : Prop :=
  ∀ a : A, ∃! c : NormalizedCocycle C2 A, c.val.val (t, t) = a

def NormalizedCoboundaries : Prop :=
  ∀ a : C2 → A, a 1 = 0 → differential a (t, t) = 0

def EvaluationEquivalence : Prop :=
  ∃ e : H2 C2 A ≃+ A, ∀ c : NormalizedCocycle C2 A,
    e (classOf C2 A c.val) = c.val.val (t, t)

def ExtensionCorrespondence : Prop :=
  (∃ e : ExtensionClasses C2 A ≃ A,
    ∀ (c : NormalizedCocycle C2 A) (h : InducesAction (cocycleExtension c)),
      e (Quotient.mk (extensionSetoid C2 A) (cocycleRepresentative c h)) = c.val.val (t, t)) ∧
  (∀ {E : Type u} [Group E] (S : GroupExtension (Multiplicative A) E C2), InducesAction S →
    ∃! c : NormalizedCocycle C2 A, Nonempty ((cocycleExtension c).Equiv S))

def SplitCase : Prop :=
  ∀ c : NormalizedCocycle C2 A, c.val.val (t, t) = 0 →
    classOf C2 A c.val = 0 ∧ Nonempty (cocycleExtension c).Splitting ∧
      Nonempty ((cocycleExtension c).Equiv productExtension)

def CyclicCase : Prop :=
  ∀ c : NormalizedCocycle C2 A, c.val.val (t, t) ≠ 0 →
    classOf C2 A c.val ≠ 0 ∧
    (cocycleExtension c).rightHom (lift c) = t ∧
    (lift c) ^ 2 = (cocycleExtension c).inl (Multiplicative.ofAdd (1 : A)) ∧
    orderOf (lift c) = 4 ∧ Subgroup.zpowers (lift c) = ⊤ ∧
    ∃ e : Multiplicative (ZMod 4) ≃* Middle c,
      e (Multiplicative.ofAdd (1 : ZMod 4)) = lift c

def DistinctExtensions : Prop :=
  ∀ c d : NormalizedCocycle C2 A, c.val.val (t, t) = 0 → d.val.val (t, t) ≠ 0 →
    InducesAction (cocycleExtension c) ∧ InducesAction (cocycleExtension d) ∧
      classOf C2 A c.val ≠ classOf C2 A d.val ∧
      ¬ Nonempty ((cocycleExtension c).Equiv (cocycleExtension d))

end Specs.ALG02GroupTheory.Extensions.CyclicTwo
