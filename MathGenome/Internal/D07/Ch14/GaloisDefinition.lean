import MathGenome.Internal.Specs.D07.Ch14.GaloisDefinition
import MathGenome.Internal.D07.Ch14.AutomorphismBound
import MathGenome.Internal.D07.Ch14.AutomorphismGroup

/-!
Galois extensions and the finite convention, K07.14.galois_definition.

We retain the canonical normal-and-separable predicate and the upstream
base-fixing automorphism group. Algebraicity follows from normality, so it
is explicit in the characterization without imposing finite degree. The
finite automorphism-count equivalence is exactly the preceding entry,
used in both directions.
-/

universe u v

namespace D07.Ch14.GaloisDefinition

open Specs.D07.Ch14.GaloisDefinition

/-- A Galois extension is algebraic, normal, and separable; it may be infinite. -/
abbrev GaloisExtension (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] : Prop :=
  IsGalois K L

/-- The Galois group consists of the existing base-fixing field automorphisms. -/
abbrev Gal (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] :=
  AutomorphismGroup.Aut K L

theorem galois_characterization : GaloisCharacterization.{u, v} := by
  intro K L _ _ _
  constructor
  · intro h
    exact ⟨h.to_normal.toIsAlgebraic, h.to_normal, h.to_isSeparable⟩
  · rintro ⟨_, hn, hs⟩
    exact { to_normal := hn, to_isSeparable := hs }

theorem gal_operations : GaloisGroupOperations.{u, v} :=
  AutomorphismGroup.operations

theorem finite_iff_automorphism_count : FiniteIffAutomorphismCount.{u, v} := by
  intro K L _ _ _ _
  exact (AutomorphismBound.equality_iff_galois K L).symm

end D07.Ch14.GaloisDefinition
