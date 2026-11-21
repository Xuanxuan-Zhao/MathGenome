import MathGenome.Internal.AlgebraCore.Specs.P103.Ch09.InductionModels
import Mathlib.RepresentationTheory.Coinduced

/-! Coinduction in the source's right-coset convention. No index or dimension
hypothesis is imposed until the finite-index comparison. -/
noncomputable section
universe u v w x y
namespace P103.Ch09.Coinduction
open scoped MonoidAlgebra
variable {k : Type u} {G : Type v} [Field k] [Group G]
variable (H : Subgroup G)
variable {V : Type w} [AddCommGroup V] [Module k V]

/-- The subgroup acts on the group algebra by left multiplication. -/
abbrev regular := restrict H (Representation.leftRegular k G)

/-- The algebra-linear Hom definition. Both type synonyms retain their original
additive groups and coefficient-field actions. -/
abbrev Hom (ρ : Representation k H V) :=
  (regular (k := k) H).asModule →ₗ[k[H]] ρ.asModule

/-- Evaluation on the original vector spaces. -/
def eval (ρ : Representation k H V) (F : Hom H ρ) (a : k[G]) : V :=
  ρ.asModuleEquiv (F ((regular H).asModuleEquiv.symm a))

abbrev Functions (ρ : Representation k H V) := Representation.coindV H.subtype ρ
abbrev action (ρ : Representation k H V) := Representation.coind H.subtype ρ

/-- A Hom/function comparison and the action on the Hom model, with their
literal formulas. -/
structure Data (ρ : Representation k H V) where
  representation : Representation k G (Hom H ρ)
  equivalence : Hom H ρ ≃ₗ[k] Functions H ρ
  evaluation : ∀ F x, (equivalence F).1 x = eval H ρ F (MonoidAlgebra.single x 1)
  action_eval : ∀ g F a,
    eval H ρ (representation g F) a = eval H ρ F (a * MonoidAlgebra.single g 1)
  equivariant : ∀ g F, equivalence (representation g F) = action H ρ g (equivalence F)

/-- The quotient by the right-coset relation, with no normality assumption. -/
abbrev RightCosets := Quotient (QuotientGroup.rightRel H)
def rightCoset (x : G) : RightCosets H := @Quotient.mk' G (QuotientGroup.rightRel H) x

def FiniteSupport (ρ : Representation k H V) (f : Functions H ρ) : Prop :=
  (rightCoset H '' Function.support f.1).Finite

/-- All and only the functions with finite support modulo right cosets. -/
def finiteFunctions (ρ : Representation k H V) : Submodule k (Functions H ρ) where
  carrier := {f | FiniteSupport H ρ f}
  zero_mem' := by simp [FiniteSupport, Function.support]
  add_mem' := by
    intro f g hf hg
    apply (hf.union hg).subset
    rintro q ⟨x, hx, rfl⟩
    by_cases hfx : f.1 x = 0
    · right; exact ⟨x, by simpa [Function.mem_support, hfx] using hx, rfl⟩
    · left; exact ⟨x, hfx, rfl⟩
  smul_mem' := by
    intro c f hf
    apply hf.subset
    rintro q ⟨x, hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    change c • f.1 x ≠ 0 at hx
    change f.1 x ≠ 0
    intro hz
    exact hx (by simp [hz])

namespace Specs

def constructionType : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G] (H : Subgroup G)
    {V : Type w} [AddCommGroup V] [Module k V] (ρ : Representation k H V),
    Nonempty (Data H ρ) ∧
      ∀ (b : k[H]) (a : k[G]),
        (regular H).asModuleEquiv (b • (regular H).asModuleEquiv.symm a) =
          subgroupAlgebra H b * a

/-- The right adjunction is k-linear, with evaluation at 1 and its full inverse
formula on arbitrary group-algebra inputs. -/
def adjunctionType : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G] (H : Subgroup G)
    {V : Type w} [AddCommGroup V] [Module k V] (ρ : Representation k H V)
    (C : Data H ρ) {W : Type x} [AddCommGroup W] [Module k W]
    (τ : Representation k G W),
    ∃ A : τ.IntertwiningMap C.representation ≃ₗ[k] (restrict H τ).IntertwiningMap ρ,
      (∀ Φ z, A Φ z = eval H ρ (Φ z) 1) ∧
      (∀ ψ z a, eval H ρ (A.symm ψ z) a =
        a.coeff.sum (fun x c => c • ψ (τ x z)))

/-- Naturality in both variables, stated on the evaluation formulas so it
preserves the actual underlying maps in all the models. -/
def adjunctionNaturalityType : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G] (H : Subgroup G)
    {V : Type w} [AddCommGroup V] [Module k V] (ρ : Representation k H V)
    {V' : Type x} [AddCommGroup V'] [Module k V'] (ρ' : Representation k H V')
    (C : Data H ρ) (C' : Data H ρ') (f : ρ.IntertwiningMap ρ'),
    ∃ Q : C.representation.IntertwiningMap C'.representation,
      (∀ F a, eval H ρ' (Q F) a = f (eval H ρ F a)) ∧
      ∀ {W : Type y} [AddCommGroup W] [Module k W] (τ : Representation k G W),
      ∃ A : τ.IntertwiningMap C.representation ≃ₗ[k] (restrict H τ).IntertwiningMap ρ,
      ∃ A' : τ.IntertwiningMap C'.representation ≃ₗ[k] (restrict H τ).IntertwiningMap ρ',
        (∀ Φ z, A Φ z = eval H ρ (Φ z) 1) ∧
        (∀ Φ z, A' Φ z = eval H ρ' (Φ z) 1) ∧
        (∀ Φ, A' (Q.comp Φ) = f.comp (A Φ)) ∧
        (∀ {W' : Type y} [AddCommGroup W'] [Module k W']
          (τ' : Representation k G W') (p : τ'.IntertwiningMap τ),
          ∃ B : τ'.IntertwiningMap C.representation ≃ₗ[k] (restrict H τ').IntertwiningMap ρ,
            (∀ Φ z, B Φ z = eval H ρ (Φ z) 1) ∧
            ∀ Φ, (B (Φ.comp p)).toLinearMap = (A Φ).toLinearMap.comp p.toLinearMap)

/-- Inversion identifies induction with precisely the finite-right-coset
subrepresentation of coinduction, for every supplied tensor/function model. -/
def comparisonType : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G] (H : Subgroup G)
    {V : Type w} [AddCommGroup V] [Module k V] (ρ : Representation k H V)
    (C : Data H ρ) (D : InductionData H ρ) (E : FunctionModelData H ρ D),
    letI := D.module
    ∃ J : D.representation.IntertwiningMap C.representation,
      Function.Injective J ∧
      (∀ z x, (C.equivalence (J z)).1 x = (E.equivalence z).1 x⁻¹) ∧
      (∀ F, (∃ z, J z = F) ↔ FiniteSupport H ρ (C.equivalence F)) ∧
      (∀ g F, FiniteSupport H ρ (C.equivalence F) →
        FiniteSupport H ρ (C.equivalence (C.representation g F))) ∧
      (∀ [H.FiniteIndex], Function.Surjective J ∧
        ∃ L : Induced H ρ ≃ₗ[k] Hom H ρ, ∀ z, L z = J z)

/-- Naturality of the actual induction-to-coinduction inclusions, for every
choice of models with the specified formulas. At finite index these inclusions
are the comparison isomorphisms. -/
def comparisonNaturalityType : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G] (H : Subgroup G)
    {V : Type w} [AddCommGroup V] [Module k V] (ρ : Representation k H V)
    {W : Type x} [AddCommGroup W] [Module k W] (σ : Representation k H W)
    (f : ρ.IntertwiningMap σ) (C : Data H ρ) (C' : Data H σ)
    (D : InductionData H ρ) (D' : InductionData H σ)
    (E : FunctionModelData H ρ D) (E' : FunctionModelData H σ D'),
    letI := D.module
    letI := D'.module
    ∀ (F : Induced H ρ →ₗ[k] Induced H σ),
      (∀ a z, F (tensor H ρ a z) = tensor H σ a (f z)) →
      ∀ (J : D.representation.IntertwiningMap C.representation)
        (J' : D'.representation.IntertwiningMap C'.representation)
        (Q : C.representation.IntertwiningMap C'.representation),
        (∀ z x, (C.equivalence (J z)).1 x = (E.equivalence z).1 x⁻¹) →
        (∀ z x, (C'.equivalence (J' z)).1 x = (E'.equivalence z).1 x⁻¹) →
        (∀ F a, eval H σ (Q F) a = f (eval H ρ F a)) →
        ∀ z, J' (F z) = Q (J z)

end Specs
end P103.Ch09.Coinduction
