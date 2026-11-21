import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.Defs

/-! Specifications for RM03-C04.07. -/

namespace Specs.RM03.CSA

universe u v w

/-- Two embeddings of a simple algebra into a central simple algebra are conjugate. -/
def SkolemNoether : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {B : Type w} [Ring B] [Algebra k B],
    isCentralSimple k A → IsSimpleRing B →
    ∀ (f g : B →ₐ[k] A), Function.Injective f → Function.Injective g →
      ∃ u : Aˣ, ∀ b : B, f b * (u : A) = (u : A) * g b

/-- The pointwise conjugation formulation of Skolem–Noether. -/
def SkolemNoetherConj : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {B : Type w} [Ring B] [Algebra k B],
    isCentralSimple k A → IsSimpleRing B →
    ∀ (f g : B →ₐ[k] A), Function.Injective f → Function.Injective g →
      ∃ u : Aˣ, ∀ b : B, g b = (↑u⁻¹ : A) * f b * (u : A)

/-- Every base-field algebra automorphism of a central simple algebra is inner. -/
def AlgEquivIsInner : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A],
    isCentralSimple k A →
    ∀ e : A ≃ₐ[k] A, ∃ u : Aˣ, ∀ a : A, e a = (u : A) * a * (↑u⁻¹ : A)

end Specs.RM03.CSA
