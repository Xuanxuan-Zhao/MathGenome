import Specs.LinearAlgebraicGroups.RootData.BorelPairs
import LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
import LinearAlgebraicGroups.Reductive.MaximalToriConjugate
import LinearAlgebraicGroups.Reductive.BorelProper
import LinearAlgebraicGroups.RootData.BorelPositivity
import LinearAlgebraicGroups.Classification.Pinning
import Batteries.Tactic.OpenPrivate

universe u

namespace LinearAlgebraicGroups.RootData.BorelPairs

open _root_.LinearAlgebraicGroups.Specs
open private geometricSmooth geometricConnected from LinearAlgebraicGroups.Reductive.BorelProper
open private solvable_maximal_torus_iff from LinearAlgebraicGroups.Reductive.MaximalToriConjugate

/-- Borel subgroups and Borel pairs are conjugate over the algebraic closure. -/
theorem geometricConjugacy : Specs.BorelPairs.GeometricConjugacy.{u} := by
  intro k _ G hs hc
  let Gbar := GeometricRadicals.GeometricGroup G
  have hsbar := geometricSmooth G hs
  have hcbar := geometricConnected G hc
  obtain ⟨B, hB⟩ := LinearAlgebraicGroups.GeometricBorelConjugacy.borelExists Gbar hsbar hcbar
  let B₀ := Unipotent.closedSubgroupAlgebraicGroup B
  obtain ⟨_, _, _, _, _, _, ⟨T, hT⟩, _⟩ :=
    LinearAlgebraicGroups.GeometricTorusSplitting.splitting B₀ hB.1.1 hB.1.2.1 hB.1.2.2
  refine ⟨⟨B, hB, T, (solvable_maximal_torus_iff B₀ T).mp hT⟩, ?_⟩
  intro B₁ B₂ h₁ h₂
  exact ⟨LinearAlgebraicGroups.GeometricBorelConjugacy.borelsConjugate Gbar hsbar hcbar B₁ B₂ h₁ h₂,
    LinearAlgebraicGroups.MaximalToriConjugate.borelPairsConjugate Gbar hsbar hcbar B₁ B₂ h₁ h₂⟩

/-- Properness of the canonical right quotient detects containment of a geometric Borel. -/
theorem propernessCriterion : Specs.BorelPairs.PropernessCriterion.{u} := by
  intro k _ G hs hc P hp
  exact ⟨(LinearAlgebraicGroups.HomogeneousQuotient.homogeneousQuotient k G P).1,
    LinearAlgebraicGroups.BorelProper.quotientProperIff G hs hc P hp⟩

/-- The split Borel classification, Weyl action, and radical factorization. -/
theorem splitBorels : Specs.BorelPairs.SplitBorels.{u} :=
  BorelPositivity.borelPositivity

/-- Equivariant additive coordinates on the simple root groups. -/
abbrev Pinning : Specs.Pinning.PinningType.{u} :=
  LinearAlgebraicGroups.Classification.Pinning.Pinning

/-- The pinning is equivalent to nonzero vectors in the simple root lines. -/
theorem pinningAndRootVectors : Specs.BorelPairs.PinningAndRootVectors.{u} :=
  ⟨Classification.Pinning.additiveLineExists, Classification.Pinning.pinningsExist,
    Classification.Pinning.pinningVectors, Classification.Pinning.coordinateChanges⟩

/-- Quasi-splitness over the given ground field. -/
abbrev IsQuasiSplit : Specs.GeometricRadicals.GroupPredicateType.{u} :=
  @Specs.GeometricBorelConjugacy.IsQuasiSplit

end LinearAlgebraicGroups.RootData.BorelPairs
