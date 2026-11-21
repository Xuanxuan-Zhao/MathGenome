import MathGenome.Internal.ExtremalOptimization.Specs.P205.Convex.MidpointExtreme
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace P205.Convex

open P205.Polyhedra

/-- When the first weight is the smaller one, double it to obtain a segment
whose midpoint is the given point. -/
private theorem endpoints_eq_of_le {n : ℕ} {P : Set (Coordinate n)}
    {x y z : Coordinate n} (hP : Convex ℝ P) (hx : MidpointExtreme P x)
    (hy : y ∈ P) (hz : z ∈ P) {a b : ℝ} (ha : 0 < a)
    (hab : a + b = 1) (hle : a ≤ b) (heq : a • y + b • z = x) : y = z := by
  let w := (2 * a) • y + (b - a) • z
  have hw : w ∈ P :=
    hP hy hz (by linarith) (by linarith) (by linarith)
  have hm : (1 / 2 : ℝ) • (w + z) = x := by
    ext j
    have hj := congrFun heq j
    have hs := congrArg (fun t : ℝ => t * z j) hab
    simp only [w, Pi.smul_apply, Pi.add_apply, smul_eq_mul] at *
    nlinarith
  have hwz := hx.2 w hw z hz hm
  ext j
  have hj := congrFun hwz j
  have hs := congrArg (fun t : ℝ => t * z j) hab
  simp only [w, Pi.smul_apply, Pi.add_apply, smul_eq_mul] at hj
  have hp : (2 * a) * (y j - z j) = 0 := by nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left (by positivity))

/-- For every convex set of real coordinate vectors, the midpoint test agrees
with Mathlib's definition using arbitrary open segments. -/
theorem midpointExtreme_iff_mem_extremePoints {n : ℕ} (P : Set (Coordinate n))
    (x : Coordinate n) (hP : Convex ℝ P) :
    MidpointExtreme P x ↔ x ∈ P.extremePoints ℝ := by
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    intro y hy z hz hseg
    obtain ⟨a, b, ha, hb, hab, heq⟩ := hseg
    have hyz : y = z := by
      rcases le_total a b with hle | hle
      · exact endpoints_eq_of_le hP hx hy hz ha hab hle heq
      · exact (endpoints_eq_of_le hP hx hz hy hb (by linarith) hle
          (by simpa only [add_comm] using heq)).symm
    rw [← hyz, ← add_smul, hab, one_smul] at heq
    exact heq
  · intro hx
    refine ⟨hx.1, ?_⟩
    intro y hy z hz heq
    have hs : x ∈ openSegment ℝ y z := by
      refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
      simpa only [← smul_add] using heq
    have hyx := hx.2 hy hz hs
    have hzx := hx.2 hz hy (by rwa [openSegment_symm])
    exact hyx.trans hzx.symm

/-- The midpoint test excludes every strict two-point convex decomposition. -/
theorem eq_of_midpointExtreme_convex_combination {n : ℕ} (P : Set (Coordinate n))
    (x y z : Coordinate n) (t : ℝ) (hP : Convex ℝ P)
    (hx : MidpointExtreme P x) (hy : y ∈ P) (hz : z ∈ P)
    (ht : 0 < t) (ht' : t < 1) (heq : t • y + (1 - t) • z = x) :
    y = x ∧ z = x := by
  have hext := (midpointExtreme_iff_mem_extremePoints P x hP).mp hx
  have hs : x ∈ openSegment ℝ y z :=
    ⟨t, 1 - t, ht, by linarith, by linarith, heq⟩
  exact ⟨hext.2 hy hz hs, hext.2 hz hy (by rwa [openSegment_symm])⟩

end P205.Convex
