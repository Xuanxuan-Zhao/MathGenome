import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap

/-!
Independent specification of `fa2:p4:singular-weight-minimizer`,
current paper.tex:21522–21558. The chapter convention at paper.tex:21389–21390
explicitly makes all functions in its convex statements real valued. All functions are modulo Lebesgue almost-everywhere equality.

We realize L¹ ∩ L² as the compatible pairs in the ℓ¹ product L¹ × L².
Compatibility identifies the two representatives a.e.; the inherited norm is
exactly the sum, rather than the maximum, of the two Lp norms.
-/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace ExpandedFA.PartIV.IntersectionMinimizer

abbrev RealL1 : Type := Lp ℝ 1 (volume : Measure ℝ)
abbrev RealL2 : Type := Lp ℝ 2 (volume : Measure ℝ)
abbrev Ambient := WithLp 1 (RealL1 × RealL2)

/-- Equality in the common space of measurable functions modulo a.e. equality. -/
def compatiblePairs : Submodule ℝ Ambient where
  carrier := {p | (p.fst : ℝ →ₘ[volume] ℝ) = (p.snd : ℝ →ₘ[volume] ℝ)}
  zero_mem' := rfl
  add_mem' {p q} hp hq := by
    change (p.fst : ℝ →ₘ[volume] ℝ) + (q.fst : ℝ →ₘ[volume] ℝ) =
      (p.snd : ℝ →ₘ[volume] ℝ) + (q.snd : ℝ →ₘ[volume] ℝ)
    rw [hp, hq]
  smul_mem' c p hp := by
    change c • (p.fst : ℝ →ₘ[volume] ℝ) = c • (p.snd : ℝ →ₘ[volume] ℝ)
    rw [hp]

abbrev E := ↥compatiblePairs

/-- An ordinary function lying in both Lp classes gives the compatible pair. -/
def ofFunction (f : ℝ → ℝ) (h1 : MemLp f 1 (volume : Measure ℝ))
    (h2 : MemLp f 2 (volume : Measure ℝ)) : E :=
  ⟨WithLp.toLp 1 (h1.toLp f, h2.toLp f), AEEqFun.mk_eq_mk.mpr Filter.EventuallyEq.rfl⟩

/-- The canonical continuous inclusion in L¹. -/
def toL1 : E →L[ℝ] RealL1 :=
  (WithLp.fstL 1 ℝ RealL1 RealL2).comp compatiblePairs.subtypeL

/-- The canonical continuous inclusion in L². -/
def toL2 : E →L[ℝ] RealL2 :=
  (WithLp.sndL 1 ℝ RealL1 RealL2).comp compatiblePairs.subtypeL

/-- We evaluate the L¹ representative; all conclusions are invariant under a.e. equality. -/
def representative (u : E) : ℝ → ℝ := toL1 u

/-- The continuous mass functional, without absolute values. -/
def mass (u : E) : ℝ := ∫ x, representative u x

/-- The feasible set in the original intersection space. -/
def Feasible (u : E) : Prop := (∀ᵐ x, 0 ≤ representative u x) ∧ mass u ≤ 1

/-- `Real.rpow` assigns zero at the singular point when α > 0; that point is null. -/
def weight (α x : ℝ) : ℝ := |x| ^ (-α)

def pairing (α : ℝ) (u : E) : ℝ := ∫ x, weight α x * representative u x

def energy (α : ℝ) (u : E) : ℝ := ‖toL2 u‖ ^ 2 - pairing α u

/-- The same constraint expressed in L²; integrability must be proved, not assumed
of an arbitrary L² weak limit. -/
def L2Feasible (v : RealL2) : Prop :=
  (∀ᵐ x, 0 ≤ v x) ∧ Integrable (fun x => v x) ∧ (∫ x, v x) ≤ 1

/-- Weak convergence uses all continuous real-linear L² tests. -/
def WeakL2Converges (v : ℕ → RealL2) (z : RealL2) : Prop :=
  ∀ f : RealL2 →L[ℝ] ℝ, Tendsto (fun n => f (v n)) atTop (𝓝 (f z))

namespace Spec

def SumNorm : Prop := ∀ u : E, ‖u‖ = ‖toL1 u‖ + ‖toL2 u‖
def Completeness : Prop := CompleteSpace E

def Nonreflexivity : Prop :=
  ¬ ExpandedFA.P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ E

def PairingContinuity : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 / 2 →
    (∀ u : E, Integrable (fun x => weight α x * representative u x)) ∧
    ∃ L : E →L[ℝ] ℝ, ∀ u, L u = pairing α u

/-- The truncated singularity is genuinely in L² for every finite radius. -/
def LocalWeight : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 / 2 → ∀ R : ℝ, 0 < R →
    MemLp ((Set.Icc (-R) R).indicator (weight α)) 2 (volume : Measure ℝ)

/-- This bound is uniform on the full feasible set and tends to zero as R → ∞. -/
def UniformTail : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 / 2 → ∀ R : ℝ, 0 < R → ∀ u : E, Feasible u →
    IntegrableOn (fun x => weight α x * representative u x) (Set.Icc (-R) R)ᶜ ∧
    0 ≤ (∫ x in (Set.Icc (-R) R)ᶜ, weight α x * representative u x) ∧
    (∫ x in (Set.Icc (-R) R)ᶜ, weight α x * representative u x) ≤ R ^ (-α)

/-- Positivity and total mass survive L² weak convergence. -/
def WeakFeasibility : Prop :=
  ∀ (v : ℕ → RealL2) (z : RealL2), (∀ n, L2Feasible (v n)) →
    WeakL2Converges v z → L2Feasible z

/-- The far-tail estimate allows the full singular linear term to pass to
weak limits of feasible sequences. It is not asserted on arbitrary L² sequences. -/
def WeakPairing : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 / 2 → ∀ (u : ℕ → E) (z : E),
    (∀ n, Feasible (u n)) → Feasible z →
    WeakL2Converges (fun n => toL2 (u n)) (toL2 z) →
    Tendsto (fun n => pairing α (u n)) atTop (𝓝 (pairing α z))

def UniqueMinimizer : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 / 2 →
    ∃! u : E, Feasible u ∧ ∀ v : E, Feasible v → energy α u ≤ energy α v

end Spec
end ExpandedFA.PartIV.IntersectionMinimizer
