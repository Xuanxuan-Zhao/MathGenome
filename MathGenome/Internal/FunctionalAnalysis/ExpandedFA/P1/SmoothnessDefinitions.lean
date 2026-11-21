import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.SmoothnessDefinitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C04Dual
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.Linarith

namespace ExpandedFA.P1.SmoothnessDefinitions

open Set Metric Filter
open scoped Topology
universe u v

/-- The support functionals D(x), using the continuous linear dual. -/
abbrev normingFunctionals : Spec.NormingFunctionalsType.{u,v} :=
  fun 𝕜 E _ _ _ x => {f : C04Dual.ContinuousDual 𝕜 E | ‖f‖ = 1 ∧ f x = 1}

/-- Smoothness at a unit vector. -/
def SmoothAt : Spec.SmoothAtType.{u,v} :=
  fun 𝕜 _ _ _ _ x => ∃ f, normingFunctionals 𝕜 x = {f}

/-- The closed-unit-ball modulus, including its zero-space convention. -/
noncomputable def modulusOfSmoothness : Spec.ModulusType.{u,v} :=
  fun 𝕜 E _ _ _ t => max 0 (sSup {r : ℝ | ∃ x y : E,
    ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1 ∧
      r = (‖x + (t : 𝕜) • y‖ + ‖x - (t : 𝕜) • y‖) / 2 - 1})

/-- Uniform smoothness is the right-sided little-o condition on the modulus. -/
def UniformlySmooth : Spec.UniformlySmoothType.{u,v} :=
  fun 𝕜 E _ _ _ => Tendsto (fun t : ℝ => modulusOfSmoothness 𝕜 E t / t) (𝓝[>] 0) (𝓝 0)

private theorem convex_norm_pair {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) : ConvexOn ℝ univ (fun x : E => ‖x + v‖ + ‖x - v‖) := by
  have hp := convexOn_univ_norm (E := E) |>.comp_affineMap
    (AffineMap.id ℝ E + AffineMap.const ℝ E v)
  have hm := convexOn_univ_norm (E := E) |>.comp_affineMap
    (AffineMap.id ℝ E - AffineMap.const ℝ E v)
  exact hp.add hm

private theorem convex_norm_pair_right {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (x : E) (t : ℝ) :
    ConvexOn ℝ univ (fun y : E => ‖x + t • y‖ + ‖x - t • y‖) := by
  have h := (convex_norm_pair x).comp_affineMap (t • AffineMap.id ℝ E)
  change ConvexOn ℝ univ (fun y : E => ‖t • y + x‖ + ‖t • y - x‖) at h
  simpa only [add_comm (t • _) x, norm_sub_rev (t • _) x] using h

private theorem exists_sphere_pair_ge {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Nontrivial E] (t : ℝ) (x y : E)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ∃ u v : E, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧
      ‖x + t • y‖ + ‖x - t • y‖ ≤ ‖u + t • v‖ + ‖u - t • v‖ := by
  have hx' : x ∈ convexHull ℝ (sphere (0 : E) 1) := by
    rw [convexHull_sphere_eq_closedBall _ zero_le_one]
    simpa using hx
  have hy' : y ∈ convexHull ℝ (sphere (0 : E) 1) := by
    rw [convexHull_sphere_eq_closedBall _ zero_le_one]
    simpa using hy
  obtain ⟨u, hu, hxu⟩ := (convex_norm_pair (t • y)).exists_ge_of_mem_convexHull
    (subset_univ _) hx'
  obtain ⟨v, hv, huv⟩ := (convex_norm_pair_right u t).exists_ge_of_mem_convexHull
    (subset_univ _) hy'
  exact ⟨u, v, by simpa using hu, by simpa using hv, hxu.trans huv⟩

private theorem ball_values_bddAbove (𝕜 : Type*) (E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (t : ℝ) :
    BddAbove {r : ℝ | ∃ x y : E, ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1 ∧
      r = (‖x + (t : 𝕜) • y‖ + ‖x - (t : 𝕜) • y‖) / 2 - 1} := by
  refine ⟨|t|, ?_⟩
  rintro r ⟨x, y, hx, hy, rfl⟩
  have hp := norm_add_le x ((t : 𝕜) • y)
  have hm := norm_sub_le x ((t : 𝕜) • y)
  simp only [norm_smul, RCLike.norm_ofReal] at hp hm
  have hty : |t| * ‖y‖ ≤ |t| := by nlinarith [abs_nonneg t]
  linarith

/-- The two raw suprema agree: convexity moves each ball vector to a sphere vector. -/
theorem ball_sphere_supremum : Spec.BallSphereSupremum.{u,v} := by
  intro 𝕜 E _ _ _ _ t
  let B : Set ℝ := {r | ∃ x y : E, ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1 ∧
    r = (‖x + (t : 𝕜) • y‖ + ‖x - (t : 𝕜) • y‖) / 2 - 1}
  let S : Set ℝ := {r | ∃ x y : E, ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
    r = (‖x + (t : 𝕜) • y‖ + ‖x - (t : 𝕜) • y‖) / 2 - 1}
  have hSB : S ⊆ B := by
    rintro r ⟨x, y, hx, hy, hr⟩
    exact ⟨x, y, hx.le, hy.le, hr⟩
  have hB : BddAbove B := ball_values_bddAbove 𝕜 E t
  have hS : BddAbove S := hB.mono hSB
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  obtain ⟨z, hz⟩ := exists_norm_eq E (show (0 : ℝ) ≤ 1 by norm_num)
  have hSne : S.Nonempty := ⟨_, z, z, hz, hz, rfl⟩
  change sSup B = sSup S
  refine le_antisymm (csSup_le (hSne.mono hSB) ?_) (csSup_le_csSup hB hSne hSB)
  rintro r ⟨x, y, hx, hy, rfl⟩
  obtain ⟨a, b, ha, hb, hab⟩ := exists_sphere_pair_ge t x y hx hy
  change ‖x + (t : 𝕜) • y‖ + ‖x - (t : 𝕜) • y‖ ≤
    ‖a + (t : 𝕜) • b‖ + ‖a - (t : 𝕜) • b‖ at hab
  exact (by linarith :
    (‖x + (t : 𝕜) • y‖ + ‖x - (t : 𝕜) • y‖) / 2 - 1 ≤
    (‖a + (t : 𝕜) • b‖ + ‖a - (t : 𝕜) • b‖) / 2 - 1).trans
      (le_csSup hS ⟨a, b, ha, hb, rfl⟩)

/-- On a nonzero space the modulus is the sphere supremum, which is nonnegative. -/
theorem modulus_sphere_formula : Spec.SphereFormula.{u,v} := by
  intro 𝕜 E _ _ _ _ t
  let B : Set ℝ := {r | ∃ x y : E, ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1 ∧
    r = (‖x + (t : 𝕜) • y‖ + ‖x - (t : 𝕜) • y‖) / 2 - 1}
  have hB : BddAbove B := ball_values_bddAbove 𝕜 E t
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  obtain ⟨z, hz⟩ := exists_norm_eq E (show (0 : ℝ) ≤ 1 by norm_num)
  have hzero : (0 : ℝ) ∈ B := by
    refine ⟨z, 0, hz.le, by simp, ?_⟩
    simp [hz]
  have hn : 0 ≤ sSup B := le_csSup hB hzero
  change max 0 (sSup B) = _
  rw [max_eq_right hn]
  exact ball_sphere_supremum 𝕜 E t

/-- The explicit outer maximum gives the stated zero-space convention. -/
theorem modulus_zero_space : Spec.ZeroSpaceModulus.{u,v} := by
  intro 𝕜 E _ _ _ _ t
  have hz (x : E) : x = 0 := Subsingleton.elim _ _
  have hset : {r : ℝ | ∃ x y : E, ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1 ∧
      r = (‖x + (t : 𝕜) • y‖ + ‖x - (t : 𝕜) • y‖) / 2 - 1} = {-1} := by
    ext r
    constructor
    · rintro ⟨x, y, _, _, hr⟩
      simpa [hz x, hz y] using hr
    · intro hr
      refine ⟨0, 0, by simp, by simp, ?_⟩
      simpa using hr
  change max 0 (sSup _) = 0
  rw [hset]
  norm_num

/-- The zero space satisfies the right-sided smoothness limit. -/
theorem uniformlySmooth_zero_space : Spec.ZeroSpaceUniformlySmooth.{u,v} := by
  intro 𝕜 E _ _ _ _
  change Tendsto (fun t : ℝ => Spec.ModulusValue 𝕜 E t / t) (𝓝[>] 0) (𝓝 0)
  simpa only [modulus_zero_space 𝕜 E, zero_div] using
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 0))

end ExpandedFA.P1.SmoothnessDefinitions
