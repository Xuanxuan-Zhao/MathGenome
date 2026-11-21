import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.HighestWeightCasimir
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.WeightStringsConvexity
import Mathlib.Order.WellFoundedSet

/-! LA-H05, Chapter 8. The squares and pairings are for the positive real form
induced by the same invariant bilinear form as the quadratic Casimir. -/

noncomputable section
universe u v

namespace Specs.LieAlgebrasAndRepresentations.FreudenthalRecursion

open SolvableRadical (IsSemisimple_value)
open VermaModules VermaWeightsUniversal HighestWeightCasimir HighestWeightData
open SimpleHighestWeightQuotient FiniteModuleWeights
open IntegrableHighestWeightQuotient (IsDominant coroots)
open SerreRelations (simple)

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

/-- Finite rank is zero for an absent weight, since its weight space is bottom. -/
abbrev multiplicity (V : Type v) [AddCommGroup V] [Module ℂ V]
    [LieRingModule L V] [LieModule ℂ L V] (H : LieSubalgebra ℂ L)
    (μ : Module.Dual ℂ H) : ℕ :=
  Module.finrank ℂ (weightSpace_value V H μ)

abbrev squaredNorm [FiniteDimensional ℂ L] (H : LieSubalgebra ℂ L)
    (B : Form (L := L)) (μ : Module.Dual ℂ H) : ℝ :=
  (weightForm_value H B μ μ).re

abbrev denominator [FiniteDimensional ℂ L] (H : LieSubalgebra ℂ L)
    (φ : Direction H) (B : Form (L := L)) (lam μ : Module.Dual ℂ H) : ℝ :=
  squaredNorm H B (lam + rho_value H φ) - squaredNorm H B (μ + rho_value H φ)

abbrev inCone (H : LieSubalgebra ℂ L) (φ : Direction H)
    (lam μ : Module.Dual ℂ H) : Prop :=
  lam - μ ∈ positiveRootCone_value (fun i : simple H φ => i.val)

abbrev polytope [FiniteDimensional ℂ L] (H : LieSubalgebra ℂ L)
    (lam : Module.Dual ℂ H) : Set (Module.Dual ℂ H) :=
  convexHull ℝ (Set.range fun w : weightWeylGroup H => w.val lam)

def candidates [FiniteDimensional ℂ L] (H : LieSubalgebra ℂ L) (φ : Direction H)
    (lam : Module.Dual ℂ H) : Set (Module.Dual ℂ H) :=
  {μ | μ - lam ∈ integralRootLattice_value (fun i : simple H φ => i.val) ∧ μ ∈ polytope H lam}

def raises (H : LieSubalgebra ℂ L) (φ : Direction H) (ν μ : Module.Dual ℂ H) : Prop :=
  ∃ (α : PositiveRoot H φ) (n : ℕ), ν = μ + (n + 1) • α.val

abbrev recursionSum [FiniteDimensional ℂ L] (H : LieSubalgebra ℂ L) (φ : Direction H)
    (B : Form (L := L)) (m : Module.Dual ℂ H → ℕ) (μ : Module.Dual ℂ H) : ℝ :=
  2 * ∑ᶠ α : PositiveRoot H φ, ∑ᶠ n : ℕ,
    (weightForm_value H B (μ + (n + 1) • α.val) α.val).re *
      (m (μ + (n + 1) • α.val) : ℝ)

/-- The identity is valid on the full dual, hence in particular at every
integral weight, including those of multiplicity zero. -/
def recursion_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ →
    ∀ (B : Form (L := L)), B.Nondegenerate → B.lieInvariant L → PositiveOnRealRoots H B →
    ∀ (lam : Module.Dual ℂ H) (χ : U (borel_value H φ) →ₐ[ℂ] ℂ),
    IsWeightCharacter H φ lam χ → IsDominant H φ lam →
    letI := inducedLieRingModule H φ χ
    letI := inducedLieModule H φ χ
    let m := multiplicity (simpleQuotient_value H φ χ) H
    Finite (PositiveRoot H φ) ∧
    ∀ μ : Module.Dual ℂ H,
      (∀ α : PositiveRoot H φ, Set.Finite {n : ℕ | m (μ + (n + 1) • α.val) ≠ 0}) ∧
      denominator H φ B lam μ * (m μ : ℝ) = recursionSum H φ B m μ

def termination_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ →
    ∀ (B : Form (L := L)), B.Nondegenerate → B.lieInvariant L → PositiveOnRealRoots H B →
    ∀ (lam : Module.Dual ℂ H) (χ : U (borel_value H φ) →ₐ[ℂ] ℂ),
    IsWeightCharacter H φ lam χ → IsDominant H φ lam →
    letI := inducedLieRingModule H φ χ
    letI := inducedLieModule H φ χ
    let m := multiplicity (simpleQuotient_value H φ χ) H
    m lam = 1 ∧
    (∀ μ, ¬ (inCone H φ lam μ ∧ μ ∈ candidates H φ lam) → m μ = 0) ∧
    (∀ μ ∈ candidates H φ lam, inCone H φ lam μ → μ ≠ lam → 0 < denominator H φ B lam μ) ∧
    (candidates H φ lam).Finite ∧ (candidates H φ lam).WellFoundedOn (raises H φ)

/-- The recursion and the initial and boundary values determine the whole
multiplicity function. The step equation is imposed only where division
is needed. -/
def unique_solution_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ →
    ∀ (B : Form (L := L)), B.Nondegenerate → B.lieInvariant L → PositiveOnRealRoots H B →
    ∀ (lam : Module.Dual ℂ H) (χ : U (borel_value H φ) →ₐ[ℂ] ℂ),
    IsWeightCharacter H φ lam χ → IsDominant H φ lam →
    ∃! m : Module.Dual ℂ H → ℕ, m lam = 1 ∧
      (∀ μ, ¬ (inCone H φ lam μ ∧ μ ∈ candidates H φ lam) → m μ = 0) ∧
      (∀ μ ∈ candidates H φ lam, inCone H φ lam μ → μ ≠ lam →
        denominator H φ B lam μ * (m μ : ℝ) = recursionSum H φ B m μ)

end Specs.LieAlgebrasAndRepresentations.FreudenthalRecursion
