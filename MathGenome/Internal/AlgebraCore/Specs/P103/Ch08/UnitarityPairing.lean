import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.CharacterConstructions
import Mathlib.Analysis.Complex.Basic

/-! The source convention is linearity in the first variable. No topology or
chosen norm on the original representation space is assumed. -/
noncomputable section
universe u v w
namespace P103.Ch08

/-- A positive definite Hermitian form, linear in its first variable. -/
structure PositiveHermitianForm (V : Type v) [AddCommGroup V] [Module ℂ V] where
  toFun : V → V → ℂ
  add_left : ∀ x y z, toFun (x + y) z = toFun x z + toFun y z
  smul_left : ∀ (c : ℂ) x y, toFun (c • x) y = c * toFun x y
  conj_symm : ∀ x y, star (toFun y x) = toFun x y
  nonneg : ∀ x, 0 ≤ (toFun x x).re
  positive : ∀ x, x ≠ 0 → 0 < (toFun x x).re

namespace UnitaritySpecs

def functionPairingValue {G : Type u} [Fintype G] (f h : G → ℂ) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ g : G, f g * star (h g)

def functionPairingType :=
  ∀ {G : Type u} [Fintype G], (G → ℂ) → (G → ℂ) → ℂ

def existsInvariantHermitianType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V),
    ∃ h : PositiveHermitianForm V, ∀ g x y, h.toFun (ρ g x) (ρ g y) = h.toFun x y

def characterInverseConjugateType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G),
    CharacterSpecs.characterValue ρ g⁻¹ = star (CharacterSpecs.characterValue ρ g)

/-- The pairing on all functions, with its full positive Hermitian structure. -/
def functionPairingPositiveType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G],
    ∃ h : PositiveHermitianForm (G → ℂ), h.toFun = functionPairingValue

def characterPairingType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type w} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W),
    functionPairingValue (CharacterSpecs.characterValue ρ) (CharacterSpecs.characterValue σ) =
      (Module.finrank ℂ (σ.IntertwiningMap ρ) : ℂ) ∧
    (Module.finrank ℂ (σ.IntertwiningMap ρ) : ℂ) =
      (Module.finrank ℂ (ρ.IntertwiningMap σ) : ℂ)

end UnitaritySpecs
end P103.Ch08
