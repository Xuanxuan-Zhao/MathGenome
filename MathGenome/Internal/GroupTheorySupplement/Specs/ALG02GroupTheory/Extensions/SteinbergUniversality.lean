import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Extensions.SteinbergCentrality

/-! The universal property of the stable Steinberg extension in the application at
paper.tex:708–710. -/

namespace Specs.ALG02GroupTheory.Extensions.SteinbergUniversality

open _root_.ALG02GroupTheory.Extensions.StableSteinberg.Spec

universe u v w t

/-- The central extension with classical kernel and canonical elementary projection is
universal in every comparison universe. -/
def SteinbergExtensionUniversal : Prop :=
  ∀ (R : Type u) [Ring R],
    isUniversalCentralExtensionValue.{u, u, u, t} (SteinbergCentrality.extensionValue R)

/-- A target can have its kernel and middle group in independent universes. -/
def ExistsUniqueSteinbergHomOver : Prop :=
  ∀ (R : Type u) [Ring R] {N : Type v} {D : Type w} [Group N] [Group D]
    (T : GroupExtension N D (Elementary R)), isCentralExtensionValue T →
      ∃! f : Steinberg R →* D, T.rightHom.comp f = toElementary

end Specs.ALG02GroupTheory.Extensions.SteinbergUniversality
