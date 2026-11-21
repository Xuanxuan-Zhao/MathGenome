import MathGenome.Internal.AlgebraCore.Specs.P103.Ch09.InductionModels
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.CharacterConstructions
import Mathlib.Basic.Complex.Basic

noncomputable section
open scoped BigOperators
universe u v w
namespace P103.Ch09.InducedCharacterSpecs

/-- Ordinary complex class functions, with their usual pointwise vector space. -/
def classFunctions (G : Type u) [Group G] : Submodule ℂ (G → ℂ) where
  carrier := {ψ | ∀ a g, ψ (a * g * a⁻¹) = ψ g}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg a x; simp [hf a x, hg a x]
  smul_mem' := by intro c f hf a x; simp [hf a x]

variable {G : Type u} [Group G] [Fintype G] (H : Subgroup G)

/-- The finite conjugacy sum; terms outside H are zero. This is defined on all
functions, and restricts to the usual induction of ordinary class functions. -/
def inductionValue : (H → ℂ) →ₗ[ℂ] (G → ℂ) := by
  classical
  exact
    { toFun := fun ψ g => (Nat.card H : ℂ)⁻¹ *
        ∑ x : G, if h : x⁻¹ * g * x ∈ H then ψ ⟨x⁻¹ * g * x, h⟩ else 0
      map_add' := by
        intro f g; funext a
        simp only [Pi.add_apply, ← mul_add, ← Finset.sum_add_distrib]
        congr 1; apply Finset.sum_congr rfl; intro x hx
        split_ifs <;> simp
      map_smul' := by
        intro c f; funext a
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        have hs : (∑ x : G, if h : x⁻¹ * a * x ∈ H then c * f ⟨x⁻¹ * a * x, h⟩ else 0) =
            c * ∑ x : G, if h : x⁻¹ * a * x ∈ H then f ⟨x⁻¹ * a * x, h⟩ else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro x hx
          split_ifs <;> simp
        rw [hs]; ring }

def inductionType := ∀ {G : Type u} [Group G] [Fintype G] (H : Subgroup G),
  (H → ℂ) →ₗ[ℂ] (G → ℂ)

def classFunctionType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (H : Subgroup G) (ψ : classFunctions H),
    inductionValue H ψ ∈ classFunctions G

def characterFormulaType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (H : Subgroup G)
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ H V) (D : InductionData H ρ) (E : FunctionModelData H ρ D),
    letI := D.module
    FiniteDimensional ℂ (Induced H ρ) ∧
    (∀ g, Ch08.CharacterSpecs.characterValue D.representation g =
      inductionValue H (Ch08.CharacterSpecs.characterValue ρ) g) ∧
    Ch08.CharacterSpecs.characterValue D.representation 1 =
      (H.index : ℂ) * (Module.finrank ℂ V : ℂ) ∧
    (∀ g, (∀ x : G, x⁻¹ * g * x ∉ H) →
      Ch08.CharacterSpecs.characterValue D.representation g = 0)

/-- The character theorem applies to an actual construction of the original
balanced tensor induction, including its function-model comparison. -/
def realizationType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (H : Subgroup G)
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ H V),
    ∃ (D : InductionData H ρ) (_E : FunctionModelData H ρ D),
      letI := D.module
      FiniteDimensional ℂ (Induced H ρ)

/-- Agreement with linear extension from representation characters, stated
for every finite linear combination and arbitrary (possibly zero) spaces. -/
def linearExtensionType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (H : Subgroup G)
    {ι : Type w} [Fintype ι] (V : ι → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)]
    (ρ : ∀ i, Representation ℂ H (V i))
    (D : ∀ i, InductionData H (ρ i)) (E : ∀ i, FunctionModelData H (ρ i) (D i))
    (c : ι → ℂ),
    inductionValue H (∑ i, c i • Ch08.CharacterSpecs.characterValue (ρ i)) =
      ∑ i, c i • (letI := (D i).module; Ch08.CharacterSpecs.characterValue (D i).representation)

end P103.Ch09.InducedCharacterSpecs
