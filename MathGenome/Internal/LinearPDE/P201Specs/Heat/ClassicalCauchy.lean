import MathGenome.Internal.LinearPDE.P201Specs.Heat.GaussianSemigroup
import MathGenome.Internal.LinearPDE.P201Specs.Heat.ClassicalMaximum
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Independent statements for paper.tex, Theorem `pde:heat-cauchy`.
The initial datum is in C_b, not BUC. The forcing topology controls the
suprema of its value and its first two derivatives. No derivative at time
zero is imposed on a solution. Time derivatives at T are taken from the left.
-/
noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
namespace P201Specs.HeatCauchy

abbrev Jet (n : ℕ) :=
  BoundedContinuousFunction (Space n) ℝ ×
  BoundedContinuousFunction (Space n) (Space n →L[ℝ] ℝ) ×
  BoundedContinuousFunction (Space n) (Space n →L[ℝ] Space n →L[ℝ] ℝ)

/-- C_b² with the subspace topology of the three bounded continuous jets.
The product norm is the maximum of the three supremum norms. On the finite
dimensional spatial space this is equivalent to taking the supremum of all
coordinate derivatives through order two, and imposes no spatial uniform
continuity on second derivatives. The jet equations are definitions of the
space, not hypotheses about heat evolution. -/
abbrev BoundedC2 (n : ℕ) := {J : Jet n //
  (∀ x, HasFDerivAt J.1 (J.2.1 x) x) ∧
  (∀ x, HasFDerivAt J.2.1 (J.2.2 x) x)}

abbrev BoundedC2Type := ℕ → Type
abbrev Forcing (n : ℕ) := ℝ → BoundedC2 n

abbrev value {n : ℕ} (f : BoundedC2 n) : Space n → ℝ := f.val.1

/-- Extension of the same heat action to real time; only nonnegative times
are used in the theorem. -/
def action {n : ℕ} (t : ℝ) (g : Space n → ℝ) : Space n → ℝ :=
  if t = 0 then g else Heat.heatConvolution t g

abbrev actionType := {n : ℕ} → ℝ → (Space n → ℝ) → Space n → ℝ

abbrev Point (n : ℕ) := HeatMaximum.Point n
abbrev Function (n : ℕ) := HeatMaximum.Function n
abbrev cylinder (n : ℕ) (T : ℝ) : Set (Point n) := univ ×ˢ Icc 0 T
abbrev positiveCylinder (n : ℕ) (T : ℝ) : Set (Point n) := univ ×ˢ Ioc 0 T
abbrev Classical {n : ℕ} (T : ℝ) (u : Function n) : Prop :=
  HeatMaximum.Classical (⊤ : Domain n) T u

/-- The zero-initial-data term; this is a scalar Bochner integral at each x. -/
def duhamel {n : ℕ} (f : Forcing n) : Function n := fun z =>
  ∫ s in 0..z.2, action (z.2 - s) (value (f s)) z.1

abbrev duhamelType := {n : ℕ} → Forcing n → Function n

def freeEvolution {n : ℕ} (g : Space n → ℝ) : Function n :=
  fun z => action z.2 g z.1

abbrev freeEvolutionType := {n : ℕ} → (Space n → ℝ) → Function n

def cauchySolution {n : ℕ} (g : Space n → ℝ) (f : Forcing n) : Function n :=
  fun z => freeEvolution g z + duhamel f z

abbrev cauchySolutionType := {n : ℕ} → (Space n → ℝ) → Forcing n → Function n

/-- Classical equation using the shared coordinate Laplacian. -/
def Equation {n : ℕ} (T : ℝ) (f : ℝ → Space n → ℝ) (u : Function n) : Prop :=
  ∀ z ∈ positiveCylinder n T,
    HeatMaximum.timeDerivative T u z - laplacian (fun x => u (x,z.2)) z.1 = f z.2 z.1

def BoundedOnCylinder {n : ℕ} (T : ℝ) (u : Function n) : Prop :=
  ∃ M : ℝ, ∀ z ∈ cylinder n T, ‖u z‖ ≤ M

def IsSolution {n : ℕ} (T : ℝ) (g : Space n → ℝ)
    (f : ℝ → Space n → ℝ) (u : Function n) : Prop :=
  Classical T u ∧ (∀ x, u (x,0) = g x) ∧ Equation T f u ∧ BoundedOnCylinder T u

def initialValueStatement : Prop :=
  ∀ (n : ℕ) (g : Space n → ℝ) (f : Forcing n) (x : Space n),
    cauchySolution g f (x,0) = g x

def boundednessStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ T : ℝ, 0 < T →
    ∀ (g : BoundedContinuousFunction (Space n) ℝ) (f : Forcing n),
      ContinuousOn f (Icc 0 T) → BoundedOnCylinder T (cauchySolution g f)

def initialContinuityStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ T : ℝ, 0 < T →
    ∀ (g : BoundedContinuousFunction (Space n) ℝ) (f : Forcing n),
      ContinuousOn f (Icc 0 T) → ∀ x : Space n,
        ContinuousWithinAt (cauchySolution g f) (cylinder n T) (x,0)

def freeContinuityStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ g : BoundedContinuousFunction (Space n) ℝ,
    ContinuousOn (freeEvolution g) (univ ×ˢ Ici (0 : ℝ))

def uniquenessStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ T : ℝ, 0 < T →
    ∀ (g : Space n → ℝ) (f : ℝ → Space n → ℝ) (u v : Function n),
      IsSolution T g f u → IsSolution T g f v → EqOn u v (cylinder n T)

/-- The two analytic components used to assemble the explicit solution.
These are propositions to prove, not certificates included in the data. -/
def freeClassicalStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ T : ℝ, 0 < T →
    ∀ g : BoundedContinuousFunction (Space n) ℝ,
      Classical T (freeEvolution g) ∧ Equation T (fun _ _ => 0) (freeEvolution g)

def duhamelClassicalStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ T : ℝ, 0 < T →
    ∀ f : Forcing n, ContinuousOn f (Icc 0 T) →
      Classical T (duhamel f) ∧ Equation T (fun t => value (f t)) (duhamel f)

/-- Complete assigned conclusion, including the explicit formula, boundedness,
joint C^{2,1} regularity at positive times, joint continuity through time zero,
the left derivative at T, and uniqueness in the globally bounded class. -/
def classicalCauchyStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ T : ℝ, 0 < T →
    ∀ (g : BoundedContinuousFunction (Space n) ℝ) (f : Forcing n),
      ContinuousOn f (Icc 0 T) →
      IsSolution T g (fun t => value (f t)) (cauchySolution g f) ∧
      ∀ u : Function n, IsSolution T g (fun t => value (f t)) u →
        EqOn u (cauchySolution g f) (cylinder n T)

end P201Specs.HeatCauchy
