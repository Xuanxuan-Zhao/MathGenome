import MathGenome.Internal.Specs.D07.Ch12.MinpolyExistence
import Mathlib.FieldTheory.Minpoly.Field

/-!
# Minimal polynomial existence and uniqueness

K07.12.minpoly_existence, paper.tex:3583–3592.

Over a field, normalizing a nonzero annihilator by its leading coefficient
proves integrality. Mathlib's least-degree monic annihilator is therefore
available; minimality proves its irreducibility and positive degree.
For uniqueness, polynomial division makes it divide any other annihilator.
An irreducible annihilator is then associated to it, and monicity removes
the unit factor. The library uniqueness lemma implements that argument.
-/

universe u v

namespace D07.Ch12.MinpolyExistence

open Specs.D07.Ch12.MinpolyExistence

theorem minimalPolynomialProperties : MinimalPolynomialProperties.{u, v} := by
  intro K L _ _ _ α hα
  have hIntegral : IsIntegral K α := hα.isIntegral
  exact ⟨minpoly.monic hIntegral, minpoly.irreducible hIntegral,
    minpoly.aeval K α, minpoly.degree_pos hIntegral⟩

theorem minimalPolynomialUniqueness : MinimalPolynomialUniqueness.{u, v} := by
  intro K L _ _ _ α _ p hMonic hIrreducible hRoot
  exact minpoly.eq_of_irreducible_of_monic hIrreducible hRoot hMonic

theorem uniqueMonicIrreducibleAnnihilator : UniqueMonicIrreducibleAnnihilator.{u, v} := by
  intro K L _ _ _ α hα
  obtain ⟨hMonic, hIrreducible, hRoot, _⟩ := minimalPolynomialProperties K L α hα
  refine ⟨minpoly K α, ⟨hMonic, hIrreducible, hRoot⟩, ?_⟩
  intro p hp
  exact minimalPolynomialUniqueness K L α hα p hp.1 hp.2.1 hp.2.2

end D07.Ch12.MinpolyExistence
