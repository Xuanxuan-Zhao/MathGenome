import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch01.SolutionConcepts

/-! Independent statement of paper.tex, d13:02:riccati (lines 465–479).
Coefficients need only be continuous on their actual open time interval.
Theorems quantify over all its subintervals, including included endpoints.
The shared endpoint-aware solution predicate is used throughout. -/

noncomputable section
open Set

namespace D13Unified.Riccati

/-- The three continuous real coefficients on the prescribed interval. -/
structure Coefficients (I : OpenTimeInterval) where
  a : ℝ → ℝ
  b : ℝ → ℝ
  c : ℝ → ℝ
  continuous_a : ContinuousOn a I.carrier
  continuous_b : ContinuousOn b I.carrier
  continuous_c : ContinuousOn c I.carrier

variable {I : OpenTimeInterval}

/-- The original equation, with time-state domain exactly `I × ℝ`. -/
def Coefficients.ode (P : Coefficients I) : ODE ℝ where
  domain := {p | p.1 ∈ I.carrier}
  isOpen_domain := I.isOpen.preimage continuous_fst
  field := fun p => P.a p.val.1 * p.val.2 ^ 2 + P.b p.val.1 * p.val.2 + P.c p.val.1
  continuous_field := by
    have ht : Continuous (fun p : {p : ℝ × ℝ | p.1 ∈ I.carrier} =>
        (⟨p.val.1, p.property⟩ : I.carrier)) :=
      (continuous_fst.comp continuous_subtype_val).subtype_mk _
    have ha := (continuousOn_iff_continuous_domRestrict.mp P.continuous_a).comp ht
    have hb := (continuousOn_iff_continuous_domRestrict.mp P.continuous_b).comp ht
    have hc := (continuousOn_iff_continuous_domRestrict.mp P.continuous_c).comp ht
    exact ((ha.mul ((continuous_snd.comp continuous_subtype_val).pow 2)).add
      (hb.mul (continuous_snd.comp continuous_subtype_val))).add hc

/-- The inhomogeneous linear equation after substitution; its domain is the
same time interval times the whole real state space. -/
def Coefficients.linearODE (P : Coefficients I) (v : ℝ → ℝ)
    (hv : ContinuousOn v I.carrier) : ODE ℝ where
  domain := {p | p.1 ∈ I.carrier}
  isOpen_domain := I.isOpen.preimage continuous_fst
  field := fun p => -(2 * P.a p.val.1 * v p.val.1 + P.b p.val.1) * p.val.2 - P.a p.val.1
  continuous_field := by
    have ht : Continuous (fun p : {p : ℝ × ℝ | p.1 ∈ I.carrier} =>
        (⟨p.val.1, p.property⟩ : I.carrier)) :=
      (continuous_fst.comp continuous_subtype_val).subtype_mk _
    have ha := (continuousOn_iff_continuous_domRestrict.mp P.continuous_a).comp ht
    have hb := (continuousOn_iff_continuous_domRestrict.mp P.continuous_b).comp ht
    have hv' := (continuousOn_iff_continuous_domRestrict.mp hv).comp ht
    exact (((((continuous_const.mul ha).mul hv').add hb).neg).mul
      (continuous_snd.comp continuous_subtype_val)).sub ha

end D13Unified.Riccati

namespace Specs.D13Unified.Ch02.Riccati
open _root_.D13Unified _root_.D13Unified.Riccati
open Specs.D13Unified.Ch01.SolutionConcepts

/-- Full forward and reverse reduction on any actual subinterval. Neither
continuity nor differentiability of `x` is assumed in the reverse direction. -/
def reductionExpected : Prop :=
  ∀ (I : OpenTimeInterval) (P : Coefficients I) (v : ℝ → ℝ)
    (hv : solutionOnValue P.ode I.toTimeInterval v)
    (J : TimeInterval), J.carrier ⊆ I.carrier → ∀ x : ℝ → ℝ,
    (∀ t ∈ J.carrier, x t - v t ≠ 0) →
    (solutionOnValue P.ode J x ↔
      solutionOnValue (P.linearODE v hv.1) J (fun t => (x t - v t)⁻¹) ∧
      (∀ t ∈ J.carrier, (x t - v t)⁻¹ ≠ 0) ∧
      (∀ t ∈ J.carrier, x t = v t + ((x t - v t)⁻¹)⁻¹))

/-- Every nowhere-zero linear solution yields a Riccati solution by the stated
inverse; applying the forward substitution recovers that solution on all of J. -/
def reconstructionExpected : Prop :=
  ∀ (I : OpenTimeInterval) (P : Coefficients I) (v : ℝ → ℝ)
    (hv : solutionOnValue P.ode I.toTimeInterval v)
    (J : TimeInterval), J.carrier ⊆ I.carrier → ∀ u : ℝ → ℝ,
    (∀ t ∈ J.carrier, u t ≠ 0) →
    solutionOnValue (P.linearODE v hv.1) J u →
    solutionOnValue P.ode J (fun t => v t + (u t)⁻¹) ∧
    (∀ t ∈ J.carrier, (v t + (u t)⁻¹) - v t ≠ 0) ∧
    (∀ t ∈ J.carrier, ((v t + (u t)⁻¹) - v t)⁻¹ = u t)

/-- The initial time and interval are unchanged, and the initial value is
transformed to `1/(ξ-v(s))`, in both directions. -/
def ivpExpected : Prop :=
  ∀ (I : OpenTimeInterval) (P : Coefficients I) (v : ℝ → ℝ)
    (hv : solutionOnValue P.ode I.toTimeInterval v)
    (J : TimeInterval), J.carrier ⊆ I.carrier → ∀ (x : ℝ → ℝ),
    (∀ t ∈ J.carrier, x t - v t ≠ 0) → ∀ s ξ : ℝ,
    (ivpOnValue P.ode J x s ξ ↔
      ivpOnValue (P.linearODE v hv.1) J (fun t => (x t - v t)⁻¹)
        s ((ξ - v s)⁻¹))

/-- On open subintervals these are exactly the shared classical C¹ solutions. -/
def classicalReductionExpected : Prop :=
  ∀ (I : OpenTimeInterval) (P : Coefficients I) (v : ℝ → ℝ)
    (hv : solutionOnValue P.ode I.toTimeInterval v)
    (J : OpenTimeInterval), J.carrier ⊆ I.carrier → ∀ (x : ℝ → ℝ),
    (∀ t ∈ J.carrier, x t - v t ≠ 0) →
    (classicalSolutionOnValue P.ode J x ↔
      classicalSolutionOnValue (P.linearODE v hv.1) J (fun t => (x t - v t)⁻¹))

/-- The known solution survives separately and is excluded by the division
hypothesis. This also records its arbitrary initial time on the subinterval. -/
def knownSolutionExpected : Prop :=
  ∀ (I : OpenTimeInterval) (P : Coefficients I) (v : ℝ → ℝ)
    (_hv : solutionOnValue P.ode I.toTimeInterval v)
    (J : TimeInterval), J.carrier ⊆ I.carrier →
    solutionOnValue P.ode J v ∧
    (∀ s ∈ J.carrier, ivpOnValue P.ode J v s (v s)) ∧
    ¬ (∀ t ∈ J.carrier, v t - v t ≠ 0)

/-- The formula-level correspondence also works on an arbitrary interval,
without requiring an open enlargement of its coefficient domain. `R` and `L`
are the analytic conditions for the two displayed equations; their identification
with the common ODE predicates on an open coefficient domain is proved in the
implementation's `solution_iff` and `linear_solution_iff`. -/
def intervalCorrespondenceExpected : Prop :=
  ∀ (I : TimeInterval) (a b c v : ℝ → ℝ),
    ContinuousOn a I.carrier → ContinuousOn b I.carrier → ContinuousOn c I.carrier →
    ContinuousOn v I.carrier →
    (∀ t ∈ I.carrier, HasDerivWithinAt v
      (a t * (v t)^2 + b t * v t + c t) I.carrier t) →
    let R := fun x : ℝ → ℝ => ContinuousOn x I.carrier ∧
      ∀ t ∈ I.carrier, HasDerivWithinAt x
        (a t * (x t)^2 + b t * x t + c t) I.carrier t
    let L := fun u : ℝ → ℝ => ContinuousOn u I.carrier ∧
      ∀ t ∈ I.carrier, HasDerivWithinAt u
        (-(2*a t*v t+b t)*u t-a t) I.carrier t
    (∀ x : ℝ → ℝ, (∀ t ∈ I.carrier, x t-v t ≠ 0) →
      (R x ↔ L (fun t => (x t-v t)⁻¹) ∧
        (∀ t ∈ I.carrier, (x t-v t)⁻¹ ≠ 0) ∧
        (∀ t ∈ I.carrier, x t = v t+((x t-v t)⁻¹)⁻¹))) ∧
    (∀ u : ℝ → ℝ, (∀ t ∈ I.carrier, u t ≠ 0) → L u →
      R (fun t => v t+(u t)⁻¹) ∧
        (∀ t ∈ I.carrier, (v t+(u t)⁻¹)-v t ≠ 0) ∧
        (∀ t ∈ I.carrier, ((v t+(u t)⁻¹)-v t)⁻¹ = u t))

/-- Initial values are also preserved under the inverse construction. -/
def inverseIVPExpected : Prop :=
  ∀ (I : OpenTimeInterval) (P : Coefficients I) (v : ℝ → ℝ)
    (hv : solutionOnValue P.ode I.toTimeInterval v)
    (J : TimeInterval), J.carrier ⊆ I.carrier → ∀ (u : ℝ → ℝ),
    (∀ t ∈ J.carrier, u t ≠ 0) → ∀ s η : ℝ,
    ivpOnValue (P.linearODE v hv.1) J u s η →
    ivpOnValue P.ode J (fun t => v t+(u t)⁻¹) s (v s+η⁻¹)

end Specs.D13Unified.Ch02.Riccati
