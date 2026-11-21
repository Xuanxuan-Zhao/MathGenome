import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch03.UniformBox
import MathGenome.Internal.ODEDynamics.D13Unified.Ch01.AutonomousParameters
import MathGenome.Internal.ODEDynamics.D13Unified.Ch01.IntegralFormulation
import Mathlib.Analysis.ODE.ExistUnique

/-! A single controlled interval for nearby initial times, states and parameters.
We use Mathlib's Picard fixed point with its original confinement estimate,
then the shared differential/integral equivalence for the actual closed interval.
-/

noncomputable section
open Set Metric

namespace D13Unified.Ch03.UniformBox

/-- Retain the confinement information carried by the Picard path space.
The ambient representative is extended by projection outside its actual interval. -/
private theorem exists_picard_path
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {tmin tmax : ℝ} {s : Icc tmin tmax}
    {x₀ ξ : E} {b r M L : NNReal}
    (hf : IsPicardLindelof f s x₀ b r M L) (hξ : ξ ∈ closedBall x₀ r) :
    ∃ x : ℝ → E, Continuous x ∧
      (∀ t, x t ∈ closedBall x₀ b) ∧
      ∀ t ∈ Icc tmin tmax, x t = ξ + ∫ z in (s : ℝ)..t, f z (x z) := by
  obtain ⟨x, hx⟩ := ODE.FunSpace.exists_isFixedPt_next hf hξ
  refine ⟨x.compProj, x.continuous_compProj,
    fun _ => x.compProj_mem_closedBall hf.mul_max_le, ?_⟩
  intro t ht
  rw [ODE.FunSpace.compProj_of_mem ht]
  exact (ODE.FunSpace.isFixedPt_next_iff hf hξ).mp hx ⟨t, ht⟩

/-- Theorem d13:03:uniform-box, including uniqueness of the IVP in the box. -/
theorem uniform_box : Specs.D13Unified.Ch03.UniformBox.uniformBoxExpected.{u, v} := by
  intro E _ _ _ P _ _ _ F s₀ ξ₀ p₀ a b c M L hM hL hdomain hbound hlip
    h hh hha hMh _hLh s ξ p hs hξ hp
  let J := Specs.D13Unified.Ch03.UniformBox.commonInterval s₀ h hh.le
  have hsJ : s ∈ J.carrier := ⟨hs.1.le, hs.2.le⟩
  have hJQ : J.carrier ⊆ Icc (s₀ - a) (s₀ + a) := by
    intro t ht
    change t ∈ Icc (s₀ - h / 2) (s₀ + h / 2) at ht
    constructor <;> linarith [ht.1, ht.2]
  have hb : 0 ≤ b := by
    have hx := (mem_ball.mp hξ)
    have := dist_nonneg (x := ξ) (y := ξ₀)
    linarith
  let B : NNReal := ⟨b, hb⟩
  let R : NNReal := ⟨b / 2, by positivity⟩
  let N : NNReal := ⟨M, hM⟩
  let K : NNReal := ⟨L, hL⟩
  have hp' : p ∈ closedBall p₀ c := ball_subset_closedBall hp
  let f : ℝ → E → E := fun t x => F.eval t x p
  have hlipJ (t : ℝ) (ht : t ∈ J.carrier) :
      LipschitzOnWith K (f t) (closedBall ξ₀ b) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [dist_eq_norm, dist_eq_norm]
    change ‖F.eval t x p - F.eval t y p‖ ≤ L * ‖x - y‖
    exact hlip t (hJQ ht) x hx y hy p hp'
  have hf : IsPicardLindelof f ⟨s, hsJ⟩ ξ₀ B R N K := by
    constructor
    · exact hlipJ
    · intro x hx
      have hcont := (F.atParameter p).continuousOn_eval
      exact hcont.comp (continuousOn_id.prodMk continuousOn_const)
        (fun t ht => hdomain t (hJQ ht) x hx p hp')
    · intro t ht x hx
      exact hbound t (hJQ ht) x hx p hp'
    · change M * max (s₀ + h / 2 - s) (s - (s₀ - h / 2)) ≤ b - b / 2
      have hmax : max (s₀ + h / 2 - s) (s - (s₀ - h / 2)) ≤ h := by
        apply max_le <;> linarith [hs.1, hs.2]
      calc
        M * max (s₀ + h / 2 - s) (s - (s₀ - h / 2)) ≤ M * h :=
          mul_le_mul_of_nonneg_left hmax hM
        _ ≤ b - b / 2 := by linarith
  obtain ⟨x, hxcont, hxball, hxint⟩ := exists_picard_path hf
    (show ξ ∈ closedBall ξ₀ R from ball_subset_closedBall hξ)
  have hxgraph : ∀ t ∈ J.carrier, (t, x t) ∈ (F.atParameter p).domain :=
    fun t ht => hdomain t (hJQ ht) (x t) (hxball t) p hp'
  have hxivp : IsIVPOn (F.atParameter p) J x s ξ :=
    (ivp_iff_integral (F.atParameter p) J x s ξ hsJ hxcont.continuousOn hxgraph).mpr hxint
  refine ⟨x, hxivp, fun t _ => hxball t, ?_⟩
  intro y hy hyball
  apply ODE_solution_unique_of_mem_Icc (v := f) (s := fun _ => closedBall ξ₀ b)
    (K := K) (fun t ht => hlipJ t (Ioo_subset_Icc_self ht)) hs
    hy.1.1 ?_ (fun t ht => hyball (Ioo_subset_Icc_self ht))
    hxivp.1.1 ?_ (fun t _ => hxball t) (hy.2.2.trans hxivp.2.2.symm)
  · intro t ht
    exact (hy.1.2.2 t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  · intro t ht
    exact (hxivp.1.2.2 t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)

end D13Unified.Ch03.UniformBox
