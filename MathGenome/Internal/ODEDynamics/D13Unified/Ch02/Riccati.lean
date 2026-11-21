import MathGenome.Internal.ODEDynamics.D13Unified.Ch01.SolutionConcepts
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch02.Riccati
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Reversible Riccati reduction, paper.tex d13:02:riccati.
The proof uses the derivative of a reciprocal and two field identities.
All comparisons and substitutions are on the recorded actual interval. -/

noncomputable section
open Set

namespace D13Unified.Riccati
open Specs.D13Unified.Ch02.Riccati

variable {I : OpenTimeInterval} (P : Coefficients I)

@[simp] theorem ode_eval {t : ℝ} (ht : t ∈ I.carrier) (z : ℝ) :
    P.ode.eval t z = P.a t * z ^ 2 + P.b t * z + P.c t := by
  rw [ODE.eval_of_mem P.ode (show (t, z) ∈ P.ode.domain from ht)]
  rfl

@[simp] theorem linearODE_eval (v : ℝ → ℝ) (hv : ContinuousOn v I.carrier)
    {t : ℝ} (ht : t ∈ I.carrier) (z : ℝ) :
    (P.linearODE v hv).eval t z = -(2 * P.a t * v t + P.b t) * z - P.a t := by
  rw [ODE.eval_of_mem (P.linearODE v hv) (show (t, z) ∈ (P.linearODE v hv).domain from ht)]
  rfl

/-- Unpack the common solution concept for this field. -/
theorem solution_iff (J : TimeInterval) (hJ : J.carrier ⊆ I.carrier) (x : ℝ → ℝ) :
    IsSolutionOn P.ode J x ↔ ContinuousOn x J.carrier ∧
      ∀ t ∈ J.carrier, HasDerivWithinAt x
        (P.a t * (x t) ^ 2 + P.b t * x t + P.c t) J.carrier t := by
  constructor
  · intro h
    exact ⟨h.1, fun t ht => by simpa only [ode_eval P (hJ ht)] using h.2.2 t ht⟩
  · rintro ⟨hc, hd⟩
    exact ⟨hc, fun t ht => hJ ht,
      fun t ht => by simpa only [ode_eval P (hJ ht)] using hd t ht⟩

theorem linear_solution_iff (v : ℝ → ℝ) (hv : ContinuousOn v I.carrier)
    (J : TimeInterval) (hJ : J.carrier ⊆ I.carrier) (u : ℝ → ℝ) :
    IsSolutionOn (P.linearODE v hv) J u ↔ ContinuousOn u J.carrier ∧
      ∀ t ∈ J.carrier, HasDerivWithinAt u
        (-(2 * P.a t * v t + P.b t) * u t - P.a t) J.carrier t := by
  constructor
  · intro h
    exact ⟨h.1, fun t ht => by
      simpa only [linearODE_eval P v hv (hJ ht)] using h.2.2 t ht⟩
  · rintro ⟨hc, hd⟩
    exact ⟨hc, fun t ht => hJ ht, fun t ht => by
      simpa only [linearODE_eval P v hv (hJ ht)] using hd t ht⟩

/-- The forward chain-rule calculation. -/
private theorem reciprocal_difference_derivative {S : Set ℝ} {t : ℝ}
    {a b c : ℝ} {x v : ℝ → ℝ}
    (hx : HasDerivWithinAt x (a * (x t)^2 + b * x t + c) S t)
    (hv : HasDerivWithinAt v (a * (v t)^2 + b * v t + c) S t)
    (hne : x t - v t ≠ 0) :
    HasDerivWithinAt (fun r => (x r - v r)⁻¹)
      (-(2*a*v t+b)*(x t-v t)⁻¹-a) S t := by
  convert (hx.sub hv).inv hne using 1
  simp only [Pi.sub_apply]
  field_simp
  ring

/-- The inverse chain-rule calculation, with no division by a possible zero. -/
private theorem add_reciprocal_derivative {S : Set ℝ} {t : ℝ}
    {a b c : ℝ} {u v : ℝ → ℝ}
    (hv : HasDerivWithinAt v (a * (v t)^2 + b * v t + c) S t)
    (hu : HasDerivWithinAt u (-(2*a*v t+b)*u t-a) S t)
    (hne : u t ≠ 0) :
    HasDerivWithinAt (fun r => v r + (u r)⁻¹)
      (a*(v t+(u t)⁻¹)^2+b*(v t+(u t)⁻¹)+c) S t := by
  convert hv.add (hu.inv hne) using 1
  field_simp
  ring

/-- Construct the inverse solution with its nonzero difference and inverse
identity on the whole chosen subinterval. -/
theorem reconstruction : reconstructionExpected := by
  intro I P v hv J hJ u hne hu
  have hvd := ((solution_iff P I.toTimeInterval (fun _ h => h) v).mp hv).2
  have hud := (linear_solution_iff P v hv.1 J hJ u).mp hu
  refine ⟨(solution_iff P J hJ _).mpr ⟨?_, ?_⟩, ?_, ?_⟩
  · exact (hv.1.mono hJ).add (hud.1.inv₀ hne)
  · intro t ht
    exact add_reciprocal_derivative ((hvd t (hJ ht)).mono hJ) (hud.2 t ht) (hne t ht)
  · intro t ht
    simpa only [add_sub_cancel_left] using inv_ne_zero (hne t ht)
  · intro t ht
    simp only [add_sub_cancel_left, inv_inv]

/-- The source equivalence, including the nonvanishing and inverse formula. -/
theorem reduction : reductionExpected := by
  intro I P v hv J hJ x hne
  constructor
  · intro hx
    have hxd := (solution_iff P J hJ x).mp hx
    have hvd := ((solution_iff P I.toTimeInterval (fun _ h => h) v).mp hv).2
    refine ⟨(linear_solution_iff P v hv.1 J hJ _).mpr ⟨?_, ?_⟩,
      fun t ht => inv_ne_zero (hne t ht), ?_⟩
    · exact (hx.1.sub (hv.1.mono hJ)).inv₀ hne
    · intro t ht
      exact reciprocal_difference_derivative (hxd.2 t ht)
        ((hvd t (hJ ht)).mono hJ) (hne t ht)
    · intro t ht
      simp only [inv_inv]
      ring
  · rintro ⟨hu, hnu, _⟩
    have hr := (reconstruction I P v hv J hJ _ hnu hu).1
    apply (solutionOn_congr P.ode J _ x ?_).mp hr
    intro t ht
    simp only [inv_inv]
    ring

/-- Initial values transform by the same reciprocal formula on the same domain. -/
theorem ivp : ivpExpected := by
  intro I P v hv J hJ x hne s ξ
  have hr := reduction I P v hv J hJ x hne
  constructor
  · rintro ⟨hx, hs, hξ⟩
    exact ⟨(hr.mp hx).1, hs, by simp only [hξ]⟩
  · rintro ⟨hu, hs, hξ⟩
    refine ⟨hr.mpr ⟨hu, fun t ht => inv_ne_zero (hne t ht), ?_⟩, hs, ?_⟩
    · intro t ht
      simp only [inv_inv]
      ring
    · have he : x s - v s = ξ - v s := inv_injective hξ
      exact sub_left_injective he

/-- The shared classical C¹ formulation on every open subinterval. -/
theorem classical_reduction : classicalReductionExpected := by
  intro I P v hv J hJ x hne
  rw [classical_iff_solutionOn, classical_iff_solutionOn]
  have hr := reduction I P v hv J.toTimeInterval hJ x hne
  constructor
  · intro hx
    exact (hr.mp hx).1
  · intro hu
    apply hr.mpr
    refine ⟨hu, fun t ht => inv_ne_zero (hne t ht), ?_⟩
    intro t ht
    simp only [inv_inv]
    ring

/-- The known solution was excluded before dividing and remains a solution. -/
theorem known_solution : knownSolutionExpected := by
  intro I P v hv J hJ
  have hj : IsSolutionOn P.ode J v :=
    ⟨hv.1.mono hJ, fun t ht => hv.2.1 t (hJ ht),
      fun t ht => (hv.2.2 t (hJ ht)).mono hJ⟩
  refine ⟨hj, fun s hs => ⟨hj, hs, rfl⟩, ?_⟩
  intro h
  obtain ⟨t, ht⟩ := J.nonempty
  exact h t ht (sub_self _)

/-- An arbitrary interval needs no extension of its coefficient functions.
This is the same calculation with the field formulas written out. -/
theorem interval_correspondence : intervalCorrespondenceExpected := by
  intro I a b c v _ha _hb _hc hvc hvd
  dsimp only
  constructor
  · intro x hne
    have hr (t : ℝ) : v t + ((x t - v t)⁻¹)⁻¹ = x t := by
      simp only [inv_inv]
      ring
    constructor
    · rintro ⟨hxc, hxd⟩
      refine ⟨⟨(hxc.sub hvc).inv₀ hne, ?_⟩,
        fun t ht => inv_ne_zero (hne t ht), fun t _ => (hr t).symm⟩
      intro t ht
      exact reciprocal_difference_derivative (hxd t ht) (hvd t ht) (hne t ht)
    · rintro ⟨⟨huc, hud⟩, hnu, _⟩
      constructor
      · have hcont := hvc.add (huc.inv₀ hnu)
        exact hcont.congr (fun t _ => (hr t).symm)
      · intro t ht
        have hd := add_reciprocal_derivative (hvd t ht) (hud t ht) (hnu t ht)
        simpa only [hr] using hd
  · intro u hne hu
    refine ⟨⟨hvc.add (hu.1.inv₀ hne), ?_⟩, ?_, ?_⟩
    · intro t ht
      exact add_reciprocal_derivative (hvd t ht) (hu.2 t ht) (hne t ht)
    · intro t ht
      simpa only [add_sub_cancel_left] using inv_ne_zero (hne t ht)
    · intro t ht
      simp only [add_sub_cancel_left, inv_inv]

/-- The inverse formula transforms the initial value in the same interval. -/
theorem inverse_ivp : inverseIVPExpected := by
  intro I P v hv J hJ u hne s η hu
  exact ⟨(reconstruction I P v hv J hJ u hne hu.1).1, hu.2.1,
    by simp only [hu.2.2]⟩

end D13Unified.Riccati
