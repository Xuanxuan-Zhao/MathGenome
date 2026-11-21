import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.CompactFlagOrbit
import Mathlib.Algebra.Lie.Normalizer

/-! LA-F06, notes/005/lie-algebras-and-representations.tex, lines 2983–3018.
The standard Borel uses the original Cartan and ordinary root spaces.
Inner conjugacy uses the matrix exponential group of the compact flag lemma.
The compact Hermitian norm is supplied by the theorem. -/

noncomputable section

universe u

namespace Specs.LieAlgebrasAndRepresentations.BorelSubalgebras

open CompactFlagOrbit RootDecomposition

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

def isBorelType :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L], LieSubalgebra ℂ L → Prop

/-- A Borel subalgebra is maximal among solvable Lie subalgebras. -/
def IsBorel (A : LieSubalgebra ℂ L) : Prop :=
  Maximal (fun B : LieSubalgebra ℂ L => LieAlgebra.IsSolvable B) A

/-- The Lie subalgebra with the prescribed root-space sum is Borel and self-normalizing. -/
def standardBorelType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H →
      ∀ (φ : Module.Dual ℂ H →ₗ[ℝ] ℝ), (∀ α ∈ rootSet_value H, φ α ≠ 0) →
        ∃ B : LieSubalgebra ℂ L, B.toSubmodule = borel H φ ∧
          IsBorel B ∧ B.normalizer = B

/-- Containment in an inner conjugate of the standard Borel, and pairwise
inner conjugacy of maximal solvable subalgebras. -/
def borelConjugacyType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H →
      ∀ (φ : Module.Dual ℂ H →ₗ[ℝ] ℝ), (∀ α ∈ rootSet_value H, φ α ≠ 0) →
        ∃ (τ : CompactConjugation.ConjugateMap L)
          (hs : HermitianSymmetric τ) (hp : HermitianPositive τ),
          letI c := hermitianCore τ hs hp
          letI := c.toNormedAddCommGroup
          letI := InnerProductSpace.Core.toNormedSpace (𝕜 := ℂ) (F := L)
          letI : NormedAlgebra ℝ (End L) := NormedAlgebra.restrictScalars ℝ ℂ _
          (∀ A : LieSubalgebra ℂ L, LieAlgebra.IsSolvable A →
            ∃ g ∈ (innerGroup : Subgroup (End L)ˣ),
              A.toSubmodule ≤ (borel H φ).map g.val.toLinearMap) ∧
          (∀ A₁ A₂ : LieSubalgebra ℂ L, IsBorel A₁ → IsBorel A₂ →
            ∃ g ∈ (innerGroup : Subgroup (End L)ˣ),
              A₂.toSubmodule = A₁.toSubmodule.map g.val.toLinearMap)

/-- Any two Borel subalgebras are inner conjugate, with no choices of
Cartan subalgebra or positive roots required as input. -/
def allBorelsConjugateType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∃ (τ : CompactConjugation.ConjugateMap L)
      (hs : HermitianSymmetric τ) (hp : HermitianPositive τ),
      letI c := hermitianCore τ hs hp
      letI := c.toNormedAddCommGroup
      letI := InnerProductSpace.Core.toNormedSpace (𝕜 := ℂ) (F := L)
      letI : NormedAlgebra ℝ (End L) := NormedAlgebra.restrictScalars ℝ ℂ _
      ∀ A₁ A₂ : LieSubalgebra ℂ L, IsBorel A₁ → IsBorel A₂ →
        ∃ g ∈ (innerGroup : Subgroup (End L)ˣ),
          A₂.toSubmodule = A₁.toSubmodule.map g.val.toLinearMap

end Specs.LieAlgebrasAndRepresentations.BorelSubalgebras
