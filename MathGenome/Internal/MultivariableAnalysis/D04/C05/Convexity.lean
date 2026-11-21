import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C05.Convexity
import MathGenome.Internal.MultivariableAnalysis.D04.C05.ExistenceFermat
import MathGenome.Internal.MultivariableAnalysis.D04.C03.LineRestrictions
import MathGenome.Internal.MultivariableAnalysis.D04.C03.Symmetry
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.Module

/-! Differential tests for convexity (paper d04:05:convexity).
All dimensions are allowed. The line proofs use the actual existing first and
second derivatives; no conclusion is inferred from a zero derivative selector.
The coordinate corollaries use the shared Hessian and its proved tensor bridge. -/
noncomputable section
open Set Filter Topology
namespace D04

def ScalarConvexOn : Specs.D04.C05.Convexity.ScalarConvexOnType :=
  Specs.D04.C05.Convexity.ScalarConvexOnValue

def ScalarStrictConvexOn : Specs.D04.C05.Convexity.ScalarStrictConvexOnType :=
  Specs.D04.C05.Convexity.ScalarStrictConvexOnValue

theorem scalarConvexOn_iff_convexOn {n : ℕ} (U : Set (E n)) (f : E n → ℝ)
    (hU : Convex ℝ U) : ScalarConvexOn U f ↔ ConvexOn ℝ U f := by
  constructor
  · intro h
    refine ⟨hU, fun x hx y hy a b ha hb hab => ?_⟩
    have he : a = 1-b := by linarith
    subst a
    exact h x hx y hy b ⟨hb, by linarith⟩
  · intro h x hx y hy t ht
    exact h.2 hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring)

theorem scalarStrictConvexOn_iff_strictConvexOn {n : ℕ} (U : Set (E n)) (f : E n → ℝ)
    (hU : Convex ℝ U) : ScalarStrictConvexOn U f ↔ StrictConvexOn ℝ U f := by
  constructor
  · intro h
    refine ⟨hU, fun x hx y hy hxy a b ha hb hab => ?_⟩
    have he : a = 1-b := by linarith
    subst a
    exact h x hx y hy hxy b ⟨hb, by linarith⟩
  · intro h x hx y hy hxy t ht
    exact h.2 hx hy hxy (sub_pos.mpr ht.2) ht.1 (by ring)

private theorem line_hasDerivAt {n : ℕ} (f : E n → ℝ) (a v : E n) (t : ℝ)
    (hf : DifferentiableAt ℝ f (a + t • v)) :
    HasDerivAt (fun s : ℝ => f (a + s • v)) (totalDerivative f (a+t • v) v) t := by
  have hl : HasDerivAt (fun s : ℝ => a + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add a
  exact hf.hasFDerivAt.comp_hasDerivAt t hl

private theorem convexOn_line {n : ℕ} (U : Set (E n)) (f : E n → ℝ)
    (hf : ConvexOn ℝ U f) (a v : E n) :
    ConvexOn ℝ {t : ℝ | a+t • v ∈ U} (fun t => f (a+t • v)) := by
  have h := hf.comp_affineMap (AffineMap.lineMap a (a+v))
  change ConvexOn ℝ {t | AffineMap.lineMap a (a+v) t ∈ U}
    (fun t => f (AffineMap.lineMap a (a+v) t)) at h
  simpa [AffineMap.lineMap_apply_module', add_comm] using h

theorem scalarConvexOn_iff_supporting {n : ℕ} (U : Set (E n)) (f : E n → ℝ)
    (hU : IsOpen U) (hconv : Convex ℝ U) (hf : TotalDifferentiableOn U f) :
    ScalarConvexOn U f ↔ ∀ x ∈ U, ∀ y ∈ U,
      f x + totalDerivative f x (y-x) ≤ f y := by
  have hd (x : E n) (hx : x ∈ U) : DifferentiableAt ℝ f x :=
    ((totalDifferentiableOn_iff U f hU).mp hf x hx).differentiableAt (hU.mem_nhds hx)
  constructor
  · intro hc x hx y hy
    have hl := convexOn_line U f ((scalarConvexOn_iff_convexOn U f hconv).mp hc) x (y-x)
    have hder := line_hasDerivAt f x (y-x) 0 (by simpa using hd x hx)
    have hb := hl.le_slope_of_hasDerivAt (by simpa using hx) (by simpa using hy)
      zero_lt_one hder
    simp only [slope_def_field, sub_zero, div_one, zero_smul, add_zero, one_smul,
      add_sub_cancel] at hb
    linarith
  · intro hs x hx y hy t ht
    let z := (1-t) • x + t • y
    have hz : z ∈ U := hconv hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring)
    have h₁ := mul_le_mul_of_nonneg_left (hs z hz x hx) (sub_nonneg.mpr ht.2)
    have h₂ := mul_le_mul_of_nonneg_left (hs z hz y hy) ht.1
    have he : (1-t) * totalDerivative f z (x-z) + t * totalDerivative f z (y-z) = 0 := by
      rw [← smul_eq_mul, ← smul_eq_mul, ← map_smul, ← map_smul, ← map_add]
      have he : (1-t) • (x-z) + t • (y-z) = 0 := by dsimp [z]; module
      rw [he, map_zero]
    dsimp only [z] at h₁ h₂ he ⊢
    nlinarith


/-- Along a line the second scalar derivative is the diagonal of the shared Hessian. -/
private theorem line_second_derivative {n : ℕ} (U : Set (E n)) (f : E n → ℝ)
    (hU : IsOpen U) (hf : CrOn 2 U f) (a v : E n) (t : ℝ)
    (ht : a+t • v ∈ U) :
    HasDerivAt (deriv (fun s : ℝ => f (a+s • v)))
      (differentialDiagonal (higherDifferential 2 f (a+t • v)) v) t := by
  simpa only [iteratedDeriv_one] using
    lineRestriction_hasDerivAt 1 U f a v t (crOn_timesDifferentiableAt 2 U f hU hf _ ht)

private theorem crOn_two_differentiable {n : ℕ} (U : Set (E n)) (f : E n → ℝ)
    (hf : CrOn 2 U f) : TotalDifferentiableOn U f := hf.1

private theorem line_first_differentiable {n : ℕ} (U : Set (E n)) (f : E n → ℝ)
    (hU : IsOpen U) (hf : TotalDifferentiableOn U f) (a v : E n) (t : ℝ)
    (ht : a+t • v ∈ U) : DifferentiableAt ℝ (fun s : ℝ => f (a+s • v)) t := by
  exact (line_hasDerivAt f a v t
    (((totalDifferentiableOn_iff U f hU).mp hf _ ht).differentiableAt
      (hU.mem_nhds ht))).differentiableAt

theorem scalarConvexOn_iff_hessian_nonneg {n : ℕ} (U : Set (E n)) (f : E n → ℝ)
    (hU : IsOpen U) (hconv : Convex ℝ U) (hf : CrOn 2 U f) :
    ScalarConvexOn U f ↔
      ∀ x ∈ U, ∀ v : E n, 0 ≤ differentialDiagonal (higherDifferential 2 f x) v := by
  constructor
  · intro hc x hx v
    let D := {t : ℝ | x+t • v ∈ U}
    have hD : IsOpen D := hU.preimage (continuous_const.add (continuous_id.smul continuous_const))
    have h0 : (0 : ℝ) ∈ D := by simpa [D] using hx
    have hline := convexOn_line U f ((scalarConvexOn_iff_convexOn U f hconv).mp hc) x v
    have hm := hline.monotoneOn_deriv (fun t ht =>
      line_first_differentiable U f hU (crOn_two_differentiable U f hf) x v t ht)
    have hn := hm.derivWithin_nonneg (x := 0)
    rw [derivWithin_of_isOpen hD h0, (line_second_derivative U f hU hf x v 0
      (by simpa using hx)).deriv] at hn
    simpa using hn
  · intro hh x hx y hy t ht
    let v := y-x
    let g := fun s : ℝ => f (x+s • v)
    have hmem (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : x+s • v ∈ U := by
      have he : x+s • v = (1-s) • x + s • y := by dsimp [v]; module
      rw [he]
      exact hconv hx hy (sub_nonneg.mpr hs.2) hs.1 (by ring)
    have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : DifferentiableAt ℝ g s :=
      line_first_differentiable U f hU (crOn_two_differentiable U f hf) x v s (hmem s hs)
    have hdd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :=
      line_second_derivative U f hU hf x v s (hmem s hs)
    have hg : ConvexOn ℝ (Icc (0 : ℝ) 1) g :=
      convexOn_of_deriv2_nonneg (convex_Icc 0 1)
        (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
        (fun s hs => (hd s (interior_subset hs)).differentiableWithinAt)
        (fun s hs => (hdd s (interior_subset hs)).differentiableAt.differentiableWithinAt)
        (fun s hs => by
          change 0 ≤ deriv (deriv g) s
          rw [(hdd s (interior_subset hs)).deriv]
          exact hh _ (hmem s (interior_subset hs)) v)
    have hb := hg.2 (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
      (sub_nonneg.mpr ht.2) ht.1 (by ring : (1-t)+t = 1)
    have he : x+t • v = (1-t) • x + t • y := by dsimp [v]; module
    simpa [g, v, he, smul_eq_mul] using hb

theorem scalarStrictConvexOn_of_hessian_pos {n : ℕ} (U : Set (E n)) (f : E n → ℝ)
    (hU : IsOpen U) (hconv : Convex ℝ U) (hf : CrOn 2 U f)
    (hh : ∀ x ∈ U, ∀ v : E n, v ≠ 0 →
      0 < differentialDiagonal (higherDifferential 2 f x) v) : ScalarStrictConvexOn U f := by
  intro x hx y hy hxy t ht
  let v := y-x
  let g := fun s : ℝ => f (x+s • v)
  have hv : v ≠ 0 := sub_ne_zero.mpr hxy.symm
  have hmem (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : x+s • v ∈ U := by
    have he : x+s • v = (1-s) • x + s • y := by dsimp [v]; module
    rw [he]
    exact hconv hx hy (sub_nonneg.mpr hs.2) hs.1 (by ring)
  have hg : StrictConvexOn ℝ (Icc (0 : ℝ) 1) g :=
    strictConvexOn_of_deriv2_pos (convex_Icc 0 1)
      (fun s hs => (line_first_differentiable U f hU (crOn_two_differentiable U f hf)
        x v s (hmem s hs)).continuousAt.continuousWithinAt)
      (fun s hs => by
        change 0 < deriv (deriv g) s
        rw [(line_second_derivative U f hU hf x v s (hmem s (interior_subset hs))).deriv]
        exact hh _ (hmem s (interior_subset hs)) v hv)
  have hb := hg.2 (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
    zero_ne_one (sub_pos.mpr ht.2) ht.1 (by ring : (1-t)+t = 1)
  have he : x+t • v = (1-t) • x + t • y := by dsimp [v]; module
  simpa [g, v, he, smul_eq_mul] using hb

theorem convex_stationary_globalMinimum {n : ℕ} (U : Set (E n)) (f : E n → ℝ)
    (a : E n) (hU : IsOpen U) (hconv : Convex ℝ U) (hf : TotalDifferentiableOn U f)
    (hc : ScalarConvexOn U f) (ha : StationaryPoint U f a) : GlobalMinimumOn U f a := by
  have ha' := (stationaryPoint_iff U f a).mp ha
  refine ⟨ha'.2.1, fun x hx => ?_⟩
  have hb := (scalarConvexOn_iff_supporting U f hU hconv hf).mp hc a ha'.2.1 x hx
  simpa [ha'.2.2.2] using hb

theorem strictConvex_minimum_unique {n : ℕ} (U : Set (E n)) (f : E n → ℝ)
    (a b : E n) (hconv : Convex ℝ U) (hc : ScalarStrictConvexOn U f)
    (ha : GlobalMinimumOn U f a) (hb : GlobalMinimumOn U f b) : a = b :=
  ((scalarStrictConvexOn_iff_strictConvexOn U f hconv).mp hc).eq_of_isMinOn
    ha.2 hb.2 ha.1 hb.1

theorem strictConvex_stationary_uniqueMinimum {n : ℕ} (U : Set (E n)) (f : E n → ℝ)
    (a : E n) (hU : IsOpen U) (hconv : Convex ℝ U) (hf : TotalDifferentiableOn U f)
    (hc : ScalarStrictConvexOn U f) (ha : StationaryPoint U f a) :
    GlobalMinimumOn U f a ∧ ∀ b : E n, GlobalMinimumOn U f b → b = a := by
  have hc' := ((scalarStrictConvexOn_iff_strictConvexOn U f hconv).mp hc).convexOn
  have hm := convex_stationary_globalMinimum U f a hU hconv hf
    ((scalarConvexOn_iff_convexOn U f hconv).mpr hc') ha
  exact ⟨hm, fun b hb => strictConvex_minimum_unique U f b a hconv hc hb hm⟩

theorem convex_feasible_minimum_iff {n : ℕ} (U S : Set (E n)) (f : E n → ℝ)
    (a : E n) (hU : IsOpen U) (hconv : Convex ℝ U) (hSU : S ⊆ U)
    (hS : Convex ℝ S) (ha : a ∈ S) (hf : TotalDifferentiableOn U f)
    (hc : ScalarConvexOn U f) :
    GlobalMinimumOn S f a ↔ ∀ x ∈ S, 0 ≤ totalDerivative f a (x-a) := by
  constructor
  · intro hm x hx
    have hlocal := (global_extrema_are_local S f a).1 hm
    have ht : TotalDifferentiableAt U f a := hf a (hSU ha)
    have hl : HasDerivAt (fun t : ℝ => a+t • (x-a)) (x-a) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (x-a)).const_add a
    apply feasible_right_curve_minimum U S f a (fun t : ℝ => a+t • (x-a)) (x-a)
      ht hlocal (by simp) hl.hasDerivWithinAt
    have he : ∀ᶠ t : ℝ in 𝓝[Ici (0 : ℝ)] 0, t ∈ Icc (0 : ℝ) 1 := by
      filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
        with t ht ht1
      exact ⟨ht, ht1.le⟩
    filter_upwards [he] with t ht
    have heq : a+t • (x-a) = (1-t) • a + t • x := by module
    rw [heq]
    exact hS ha hx (sub_nonneg.mpr ht.2) ht.1 (by ring)
  · intro hh
    refine ⟨ha, fun x hx => ?_⟩
    have hb := (scalarConvexOn_iff_supporting U f hU hconv hf).mp hc a (hSU ha) x (hSU hx)
    linarith [hh x hx]

/-- Coordinate matrix form of the Hessian criterion. -/
theorem scalarConvexOn_iff_hessian_posSemidef {n : ℕ} (U : Set (E n)) (f : E n → ℝ)
    (hU : IsOpen U) (hconv : Convex ℝ U) (hf : CrOn 2 U f) :
    ScalarConvexOn U f ↔ ∀ x ∈ U, (hessian f x).PosSemidef := by
  rw [scalarConvexOn_iff_hessian_nonneg U f hU hconv hf]
  constructor
  · intro hh x hx
    have ht := crOn_timesDifferentiableAt 2 U f hU hf x hx
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · exact Matrix.isHermitian_iff_isSymm.mpr (hessian_symmetric U f x ht)
    · intro v
      have hv := hh x hx ((coordinates n).symm v)
      rw [higherDifferential_diagonal_hessian U f x ht,
        LinearEquiv.apply_symm_apply] at hv
      simpa using hv
  · intro hh x hx v
    rw [higherDifferential_diagonal_hessian U f x
      (crOn_timesDifferentiableAt 2 U f hU hf x hx)]
    simpa using (hh x hx).dotProduct_mulVec_nonneg (coordinates n v)

theorem scalarStrictConvexOn_of_hessian_posDef {n : ℕ} (U : Set (E n)) (f : E n → ℝ)
    (hU : IsOpen U) (hconv : Convex ℝ U) (hf : CrOn 2 U f)
    (hh : ∀ x ∈ U, (hessian f x).PosDef) : ScalarStrictConvexOn U f := by
  apply scalarStrictConvexOn_of_hessian_pos U f hU hconv hf
  intro x hx v hv
  rw [higherDifferential_diagonal_hessian U f x
    (crOn_timesDifferentiableAt 2 U f hU hf x hx)]
  have hv' : coordinates n v ≠ 0 := fun h => hv ((coordinates n).map_eq_zero_iff.mp h)
  simpa using (hh x hx).dotProduct_mulVec_pos hv'

end D04
