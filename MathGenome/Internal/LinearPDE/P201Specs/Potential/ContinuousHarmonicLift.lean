import MathGenome.Internal.LinearPDE.P201Specs.Potential.MeanValues
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! Independent statements for the continuous-data part of
`lem:pde-harmonic-lift`, paper.tex:1024–1094. The smooth-data weak/H²
identification is a separate obligation. A total function represents an
extension; uniqueness concerns its restriction to the closure only. -/
noncomputable section
open Set
open scoped Topology ContDiff

namespace P201Specs.ContinuousHarmonicLift

/-- A classical harmonic extension with the prescribed continuous trace.
There is no differentiability requirement at boundary points. -/
def IsExtension {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Domain n)
    (g : C(frontier (Ω : Set (Space n)), 𝕜)) (h : Space n → 𝕜) : Prop :=
  MeanValues.IsHarmonic Ω h ∧ ContinuousOn h (closure (Ω : Set _)) ∧
    ∀ z : frontier (Ω : Set (Space n)), h z = g z

/-- Uniqueness needs boundedness, but no boundary regularity or connectedness. -/
def UniquenessStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜] (Ω : Domain n),
    Bornology.IsBounded (Ω : Set (Space n)) →
    ∀ (g : C(frontier (Ω : Set (Space n)), 𝕜)) (u v : Space n → 𝕜),
      IsExtension Ω g u → IsExtension Ω g v → EqOn u v (closure (Ω : Set _))

/-- The real existence obligation, with exactly the source's geometric assumptions.
Writing n=m+1 matches the shared boundary-chart interface; m≥1 means n≥2. -/
def RealExistenceStatement : Prop :=
  ∀ {m : ℕ}, 1 ≤ m → ∀ (Ω : Domain (m + 1)),
    Bornology.IsBounded (Ω : Set (Space (m + 1))) → HasCkBoundary Ω 2 →
    ∀ g : C(frontier (Ω : Set (Space (m + 1))), ℝ),
      ∃ h : Space (m + 1) → ℝ, IsExtension Ω g h

/-- The full assigned conclusion: real or complex data, all bounded C² open
sets, and uniqueness on the closure. Empty and disconnected sets are included. -/
def HarmonicLiftStatement : Prop :=
  ∀ {m : ℕ}, 1 ≤ m → ∀ {𝕜 : Type} [RCLike 𝕜] (Ω : Domain (m + 1)),
    Bornology.IsBounded (Ω : Set (Space (m + 1))) → HasCkBoundary Ω 2 →
    ∀ g : C(frontier (Ω : Set (Space (m + 1))), 𝕜),
      ∃ h : Space (m + 1) → 𝕜, IsExtension Ω g h ∧
        ∀ v : Space (m + 1) → 𝕜, IsExtension Ω g v →
          EqOn v h (closure (Ω : Set _))

/-- A field-independent reduction for the existence part only. This helper
does not assert that real extensions exist on any particular domain. -/
def ComplexificationStatement : Prop :=
  ∀ {n : ℕ} (Ω : Domain n),
    (∀ g : C(frontier (Ω : Set (Space n)), ℝ),
      ∃ h : Space n → ℝ, IsExtension Ω g h) →
    ∀ {𝕜 : Type} [RCLike 𝕜] (g : C(frontier (Ω : Set (Space n)), 𝕜)),
      ∃ h : Space n → 𝕜, IsExtension Ω g h

/-- Assembly of the full theorem from real continuous-data existence. -/
def LiftOfRealExistenceStatement : Prop :=
  RealExistenceStatement → HarmonicLiftStatement

/-- Abstract interior Perron theorem. The family is closed under maxima and
every member admits a harmonic majorant in the family on each compactly
contained ball. These closure properties are sufficient for harmonicity of
its actual finite pointwise supremum. There is no boundary or existence
conclusion in the assumptions. -/
def PerronInteriorStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ (Ω : Domain n) (F : Set (Space n → ℝ)),
    F.Nonempty →
    (∀ x ∈ Ω, BddAbove ((fun u : Space n → ℝ => u x) '' F)) →
    (∀ u ∈ F, ∀ v ∈ F, (fun x => max (u x) (v x)) ∈ F) →
    (∀ (a : Space n) (r : ℝ), 0 < r → Metric.closedBall a r ⊆ (Ω : Set _) →
      ∀ u ∈ F, ∃ v ∈ F, u ≤ v ∧
        MeanValues.IsHarmonic ⟨Metric.ball a r, Metric.isOpen_ball⟩ v) →
    MeanValues.IsHarmonic Ω
      (fun x => sSup ((fun u : Space n → ℝ => u x) '' F))

end P201Specs.ContinuousHarmonicLift
