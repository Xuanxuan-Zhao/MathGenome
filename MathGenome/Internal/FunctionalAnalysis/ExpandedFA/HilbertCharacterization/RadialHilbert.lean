import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.HilbertCharacterization.RadialHilbert
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.HilbertCharacterization.RadialCriterion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.HilbertCharacterization.Kakutani
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Supplements.FiniteDimensionalApproximation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.Projection
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.Module

noncomputable section
open scoped InnerProductSpace
namespace ExpandedFA.HilbertCharacterization.RadialHilbert
universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Minimality at coefficient one, rescaled to an equal-norm pair. -/
lemma norm_le_of_line_minimizer (h : EqualNormMinimizerBound X) (x y : X)
    (hm : ∀ t : ℝ, ‖x-y‖ ≤ ‖x-t • y‖) : ‖y‖ ≤ ‖x‖ := by
  by_cases hy : y = 0
  · simp [hy]
  by_cases hx : x = 0
  · have hh := hm 0
    simpa [hx] using hh
  have hxp : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hyp : 0 < ‖y‖ := norm_pos_iff.mpr hy
  let v : X := (‖x‖ / ‖y‖) • y
  have hv : ‖v‖ = ‖x‖ := by
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hxp hyp), div_mul_cancel₀ _ hyp.ne']
  have ha : (‖y‖ / ‖x‖) • v = y := by
    dsimp [v]
    rw [smul_smul, div_mul_div_cancel₀ hxp.ne', div_self hyp.ne', one_smul]
  have hb := h x v hv.symm hxp (‖y‖ / ‖x‖) (by
    intro t
    rw [ha]
    simpa only [v, smul_smul] using hm (t * (‖x‖ / ‖y‖)))
  rw [abs_of_pos (div_pos hyp hxp)] at hb
  exact (div_le_one hxp).mp hb

/-- A closest-point residual remains minimal after any scalar dilation. -/
lemma scaled_residual_minimal (L : Submodule ℝ X) (u : X)
    (hm : ∀ z ∈ L, ‖u‖ ≤ ‖u-z‖) (a : ℝ) (z : X) (hz : z ∈ L) :
    ‖a • u‖ ≤ ‖a • u+z‖ := by
  by_cases ha : a = 0
  · simp [ha]
  have hh := mul_le_mul_of_nonneg_left (hm (-(a⁻¹ • z)) (L.neg_mem (L.smul_mem _ hz)))
    (abs_nonneg a)
  have hid : a • (u - -(a⁻¹ • z)) = a • u + z := by
    rw [sub_neg_eq_add, smul_add, smul_smul, mul_inv_cancel₀ ha, one_smul]
  simpa only [← Real.norm_eq_abs, ← norm_smul, hid] using hh

/-- In dimension three a nearest point supplies a transverse kernel line;
the equal-norm criterion makes the resulting linear plane projection contractive. -/
lemma three_dimensional_contractive_planes [FiniteDimensional ℝ X]
    (hd : Module.finrank ℝ X = 3) (h : EqualNormMinimizerBound X) :
    Kakutani.ContractivePlanes X := by
  intro L hL
  let : FiniteDimensional ℝ L := Module.finite_of_finrank_pos (by omega)
  have hLne : L ≠ ⊤ := by
    intro ht
    rw [ht, finrank_top] at hL
    omega
  obtain ⟨x₀, _, hx₀⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr hLne)
  obtain ⟨y₀, hy₀, hmin⟩ :=
    Supplements.FiniteDimensionalApproximation.subspace_nearest_point ℝ X L x₀
  let u := x₀-y₀
  have hu : u ∉ L := by
    intro hu
    exact hx₀ (by simpa [u] using L.add_mem hu hy₀)
  have hu0 : u ≠ 0 := fun he => hu (he ▸ L.zero_mem)
  have hminu : ∀ z ∈ L, ‖u‖ ≤ ‖u-z‖ := by
    intro z hz
    have hh := hmin (y₀+z) (L.add_mem hy₀ hz)
    simpa only [u, sub_sub] using hh
  let N := Submodule.span ℝ {u}
  have hc : IsCompl L N := by
    apply (Submodule.isCompl_iff_disjoint L N ?_).mpr
    · exact Submodule.disjoint_span_singleton_of_notMem hu
    · dsimp [N]
      rw [hd, hL, finrank_span_singleton hu0]
  let p : X →ₗ[ℝ] X := L.projection N hc
  have hp (x : X) : p x ∈ L := L.projection_apply_mem hc x
  have hfix (x : X) (hx : x ∈ L) : p x = x := L.projection_apply_of_mem_left hc hx
  have hnorm (x : X) : ‖p x‖ ≤ ‖x‖ := by
    apply norm_le_of_line_minimizer h
    intro t
    have hn := L.sub_projection_mem hc x
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hn
    have hid : x-t • p x = a • u + (1-t) • p x := by
      change a • u = x-p x at ha
      rw [ha]
      module
    rw [hid, ← ha]
    exact scaled_residual_minimal L u hminu a _ (L.smul_mem _ (hp x))
  let P : X →L[ℝ] X := p.mkContinuous 1 (by simpa only [one_mul] using hnorm)
  exact ⟨P, hp, hfix, hnorm⟩

/-- The inner-product direction uses minimality on a line and Cauchy–Schwarz,
so it also applies to incomplete inner-product spaces. -/
lemma innerProduct_minimizer_bound {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] : EqualNormMinimizerBound E := by
  intro x y hxy hx a hm
  let L := Submodule.span ℝ {y}
  have hp : a • y ∈ L := Submodule.mem_span_singleton.mpr ⟨a, rfl⟩
  have hvar := (Hilbert.Projection.minimizer_iff_variational ℝ E (L : Set E)
    L.convex x (a • y) hp).mp (by
      intro z hz
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hz
      exact hm t)
  have hpos := hvar (a • y + y) (L.add_mem hp (Submodule.subset_span (by simp)))
  have hneg := hvar (a • y - y) (L.sub_mem hp (Submodule.subset_span (by simp)))
  simp only [add_sub_cancel_left, RCLike.re_to_real] at hpos
  simp only [sub_sub_cancel_left, inner_neg_right, RCLike.re_to_real] at hneg
  have hzero : ⟪x-a • y,y⟫_ℝ = 0 := le_antisymm hpos (neg_nonpos.mp hneg)
  rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at hzero
  have hcs := abs_real_inner_le_norm x y
  rw [sub_eq_zero.mp hzero, abs_mul, abs_of_nonneg (sq_nonneg ‖y‖), hxy] at hcs
  have hyp : 0 < ‖y‖ := hxy ▸ hx
  nlinarith [sq_pos_of_pos hyp]

/-- Radial characterization with the original dimension bound and no
completeness assumption. -/
theorem radial_characterization : Spec.Characterization.{u} := by
  intro X _ _ hr
  constructor
  · intro hR
    apply (Hilbert.Parallelogram.parallelogram_characterization ℝ X).mpr
    intro x y
    obtain ⟨V, hVf, hVd, hx, hy⟩ := Kakutani.exists_three_dimensional_pair hr x y
    let : FiniteDimensional ℝ V := hVf
    have hRV : ∀ x y : V, ‖radialRetraction x - radialRetraction y‖ ≤ ‖x-y‖ := by
      intro x y
      exact hR (x : X) (y : X)
    exact Kakutani.three_dimensional_parallelogram hVd
      (three_dimensional_contractive_planes hVd ((radial_nonexpansive_iff V).mp hRV))
      ⟨x, hx⟩ ⟨y, hy⟩
  · rintro ⟨p, hp⟩
    cases hp
    exact (radial_nonexpansive_iff X).mpr (@innerProduct_minimizer_bound X _ p)

end ExpandedFA.HilbertCharacterization.RadialHilbert
