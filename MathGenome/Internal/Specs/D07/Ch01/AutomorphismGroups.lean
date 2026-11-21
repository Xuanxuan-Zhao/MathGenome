import MathGenome.Internal.Specs.D07.Ch01.IsomorphismDefinition
import MathGenome.Internal.Specs.D07.Ch01.KernelImage
import MathGenome.Internal.Specs.D07.Ch01.GroupNormalQuotient
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.GroupTheory.Subgroup.Center

/-!
Independent specification of `K07.01.automorphism_groups`, paper.tex:410–420.
Automorphisms are the canonical multiplication-preserving equivalences.
Their product is composition in the source order. Conjugation is a bundled
homomorphism and its range is the subgroup of inner automorphisms.
All groups, including trivial and infinite groups, are allowed.

The quotient assertion specifies the induced map on every representative,
in addition to requiring a group isomorphism. The integer example uses the
additive operation explicitly, with inner maps `x ↦ g + x + -g`.
-/

namespace Specs.D07.Ch01.AutomorphismGroups

universe u

def AutType : Type (u + 1) := ∀ (G : Type u) [Group G], Type u

def autValue : AutType.{u} := fun G _ => MulAut G

def ConjugationType : Type (u + 1) := ∀ (G : Type u) [Group G], G →* MulAut G

def conjugationValue : ConjugationType.{u} := fun _ _ => MulAut.conj

def InnerType : Type (u + 1) := ∀ (G : Type u) [Group G], Subgroup (MulAut G)

def innerValue : InnerType.{u} := fun _ _ => MulAut.conj.range

def AutomorphismGroupLaws : Prop :=
  ∀ (G : Type u) [Group G],
    GroupDefinition.groupAxiomsValue (MulAut G) (· * ·) 1 Inv.inv

def AutomorphismOperations : Prop :=
  ∀ (G : Type u) [Group G],
    (∀ f g : MulAut G, ((f * g : MulAut G) : G → G) = f ∘ g) ∧
    (1 : MulAut G) = MulEquiv.refl G ∧
    (∀ f : MulAut G, f⁻¹ = f.symm)

def ConjugationFormula : Prop :=
  ∀ (G : Type u) [Group G] (g x : G), conjugationValue G g x = g * x * g⁻¹

def ConjugationMultiplicative : Prop :=
  ∀ (G : Type u) [Group G] (g h : G),
    conjugationValue G (g * h) = conjugationValue G g * conjugationValue G h

def CenterCarrier : Prop :=
  ∀ (G : Type u) [Group G],
    (Subgroup.center G : Set G) = {z : G | ∀ x : G, z * x = x * z}

def ConjugationKernel : Prop :=
  ∀ (G : Type u) [Group G], (conjugationValue G).ker = Subgroup.center G

def CenterNormal : Prop :=
  ∀ (G : Type u) [Group G], (Subgroup.center G).Normal

def InnerCarrier : Prop :=
  ∀ (G : Type u) [Group G],
    (innerValue G : Set (MulAut G)) = {f : MulAut G | ∃ g : G, conjugationValue G g = f}

def QuotientCenterIsoInner : Prop :=
  ∀ (G : Type u) [Group G],
    ∃ e : G ⧸ Subgroup.center G ≃* innerValue G,
      ∀ g : G, (e (QuotientGroup.mk' (Subgroup.center G) g) : MulAut G) =
        conjugationValue G g

def InnerOfAbelian : Prop :=
  ∀ (G : Type u) [Group G], GroupDefinition.abelianPredicateValue G →
    ∀ g : G, conjugationValue G g = 1

def InnerEqBotOfAbelian : Prop :=
  ∀ (G : Type u) [Group G], GroupDefinition.abelianPredicateValue G →
    innerValue G = ⊥

/-- Negation itself is an additive automorphism, differs from the identity,
and cannot be an inner automorphism of the additive integer group. -/
def IntegerNegationOuter : Prop :=
  ∃ e : ℤ ≃+ ℤ,
    (∀ x : ℤ, e x = -x) ∧ e ≠ AddEquiv.refl ℤ ∧
      ¬ ∃ g : ℤ, ∀ x : ℤ, e x = g + x + -g

end Specs.D07.Ch01.AutomorphismGroups
