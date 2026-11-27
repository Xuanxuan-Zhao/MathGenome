import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainTensor

/-! The K-projective implies K-flat assertion of Result U03. -/

namespace Specs.DerivedFormalization.KProjectiveFlatness

open Cochains (compValue)
open CochainModels (isKProjectiveValue)
open CochainTensor (isKFlat)

universe u v

/-- K-projectivity and K-flatness are tested in the same cochain category,
with independent ring and module universes. -/
def IsKProjectiveIsKFlat : Prop :=
  ∀ {R : Type u} [CommRing R] (P : compValue.{v} R),
    isKProjectiveValue P → isKFlat P

end Specs.DerivedFormalization.KProjectiveFlatness
