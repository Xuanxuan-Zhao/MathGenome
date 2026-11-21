import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.FormalCharacterDefinitions

/-! Formal character rings and characters of finite-dimensional modules. -/

noncomputable section

namespace LieAlgebrasAndRepresentations.FormalCharacters

/-- Integer Hahn series supported in a finite union of translates of `-Q₊`. -/
abbrev boundedRing := @Specs.LieAlgebrasAndRepresentations.FormalCharacters.boundedRing

/-- The subring of the completion supported on the integral weight lattice. -/
abbrev integralRing := @Specs.LieAlgebrasAndRepresentations.FormalCharacters.integralRing

/-- The formal monomial indexed by a complex Cartan weight. -/
abbrev monomial := @Specs.LieAlgebrasAndRepresentations.FormalCharacters.monomial

/-- The coefficient of a complex Cartan weight in a bounded series. -/
abbrev coeff := @Specs.LieAlgebrasAndRepresentations.FormalCharacters.coeff

/-- The finite character with coefficients indexed by the full complex Cartan dual. -/
abbrev finiteCharacter := @Specs.LieAlgebrasAndRepresentations.FormalCharacters.finiteCharacter

/-- The finite character restricted to the integral weight lattice, as an element of ℤ[P]. -/
abbrev character := @Specs.LieAlgebrasAndRepresentations.FormalCharacters.character

end LieAlgebrasAndRepresentations.FormalCharacters
