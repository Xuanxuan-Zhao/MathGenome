import MathGenome.Internal.MultivariableAnalysis.D04CornerCompletion.BoxGeometry
import MathGenome.Internal.MultivariableAnalysis.Specs.D04CornerCompletion.IntervalEndpointCharts
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.Linarith

noncomputable section
open Set Topology
open scoped ContDiff
namespace D04CornerCompletion
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model

private lemma coordinate_continuous : Continuous (fun x : E 1 => x (0 : Fin 1)) := by
  fun_prop

private lemma regular_add (a : E 1) (V : Set (E 1)) :
    FullRankLocalExtension (∞ : ℕ∞ω) V (fun u => a + u) := by
  intro u hu
  refine ⟨univ, (fun u => a + u), isOpen_univ, mem_univ _, ?_, ?_, ?_⟩
  · intro x hx; rfl
  · exact (contDiff_const.add contDiff_id).contDiffOn
  · intro x hx
    have hd : fderiv ℝ (fun u : E 1 => a + u) x =
        ContinuousLinearMap.id ℝ (E 1) :=
      ((hasFDerivAt_id (𝕜 := ℝ) x).const_add a).fderiv
    rw [hd]
    exact Function.injective_id

private lemma regular_sub (b : E 1) (V : Set (E 1)) :
    FullRankLocalExtension (∞ : ℕ∞ω) V (fun u => b - u) := by
  intro u hu
  refine ⟨univ, (fun u => b - u), isOpen_univ, mem_univ _, ?_, ?_, ?_⟩
  · intro x hx; rfl
  · exact (contDiff_const.sub contDiff_id).contDiffOn
  · intro x hx
    have hd : fderiv ℝ (fun u : E 1 => b - u) x =
        -ContinuousLinearMap.id ℝ (E 1) :=
      ((hasFDerivAt_id (𝕜 := ℝ) x).const_sub b).fderiv
    rw [hd]
    intro y z h
    simpa using h

/-- Translation gives a smooth half-space chart at the left endpoint. -/
def leftEndpointChart (a b : E 1) : EmbeddedChart (∞ : ℕ∞ω) 1 1 (box a b) where
  half := true
  half_pos := by intro; decide
  source := parameterSpace 1 true ∩ {u | u 0 < b 0 - a 0}
  source_open := ⟨{u | u 0 < b 0 - a 0}, isOpen_lt coordinate_continuous continuous_const, rfl⟩
  ambient := {x | x 0 < b 0}
  ambient_open := isOpen_lt coordinate_continuous continuous_const
  toFun := fun u => a + u
  invFun := fun x => x - a
  map_source := by
    intro u hu
    have h0 : 0 ≤ u 0 := hu.1
    have h1 : u 0 < b 0 - a 0 := hu.2
    constructor
    · intro i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      change a 0 ≤ a 0 + u 0 ∧ a 0 + u 0 ≤ b 0
      constructor <;> linarith
    · change a 0 + u 0 < b 0
      linarith
  map_target := by
    intro x hx
    have h0 := (hx.1 (0 : Fin 1)).1
    have h1 : x 0 < b 0 := hx.2
    constructor
    · change 0 ≤ x 0 - a 0
      linarith
    · change x 0 - a 0 < b 0 - a 0
      linarith
  left_inv := by intro u hu; exact add_sub_cancel_left a u
  right_inv := by intro x hx; exact add_sub_cancel _ _
  continuous_toFun := (continuous_const.add continuous_id).continuousOn
  continuous_invFun := (continuous_id.sub continuous_const).continuousOn
  regular := regular_add a _

/-- Reflection and translation give a smooth half-space chart at the right endpoint. -/
def rightEndpointChart (a b : E 1) : EmbeddedChart (∞ : ℕ∞ω) 1 1 (box a b) where
  half := true
  half_pos := by intro; decide
  source := parameterSpace 1 true ∩ {u | u 0 < b 0 - a 0}
  source_open := ⟨{u | u 0 < b 0 - a 0}, isOpen_lt coordinate_continuous continuous_const, rfl⟩
  ambient := {x | a 0 < x 0}
  ambient_open := isOpen_lt continuous_const coordinate_continuous
  toFun := fun u => b - u
  invFun := fun x => b - x
  map_source := by
    intro u hu
    have h0 : 0 ≤ u 0 := hu.1
    have h1 : u 0 < b 0 - a 0 := hu.2
    constructor
    · intro i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      change a 0 ≤ b 0 - u 0 ∧ b 0 - u 0 ≤ b 0
      constructor <;> linarith
    · change a 0 < b 0 - u 0
      linarith
  map_target := by
    intro x hx
    have h0 := (hx.1 (0 : Fin 1)).2
    have h1 : a 0 < x 0 := hx.2
    constructor
    · change 0 ≤ b 0 - x 0
      linarith
    · change b 0 - x 0 < b 0 - a 0
      linarith
  left_inv := by intro u hu; exact sub_sub_cancel b u
  right_inv := by intro x hx; exact sub_sub_cancel b x
  continuous_toFun := (continuous_const.sub continuous_id).continuousOn
  continuous_invFun := (continuous_const.sub continuous_id).continuousOn
  regular := regular_sub b _

theorem interval_endpoint_charts :
    Specs.D04CornerCompletion.IntervalEndpointCharts.interval_endpoint_chartsType := by
  intro a b hab v hv
  rcases hv with hv | hv
  · subst v
    refine ⟨leftEndpointChart a b, rfl, ?_, ?_⟩
    · constructor
      · constructor
        · change 0 ≤ (0 : E 1) (Fin.last 0)
          simp
        · change (0 : E 1) 0 < b 0 - a 0
          simpa using sub_pos.mpr hab
      · intro h
        change (0 : E 1) (Fin.last 0) = 0
        simp
    · change a + 0 = a
      simp
  · subst v
    refine ⟨rightEndpointChart a b, rfl, ?_, ?_⟩
    · constructor
      · constructor
        · change 0 ≤ (0 : E 1) (Fin.last 0)
          simp
        · change (0 : E 1) 0 < b 0 - a 0
          simpa using sub_pos.mpr hab
      · intro h
        change (0 : E 1) (Fin.last 0) = 0
        simp
    · change b - 0 = b
      simp

end D04CornerCompletion
