import MathGenome.Internal.LinearPDE.P201Specs.Common.Cea
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic.Linarith

noncomputable section
open scoped Topology InnerProductSpace
namespace P201.Common
universe u

/-- Lax--Milgram with the unknown in the first slot, as in the manuscript. -/
theorem bilinear_solvability
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (α : ℝ) (hα : 0 < α)
    (hc : ∀ x, α * ‖x‖ ^ 2 ≤ B x x) (ℓ : V →L[ℝ] ℝ) :
    ∃! u : V, ∀ v, B u v = ℓ v := by
  have hco : IsCoercive B := ⟨α, hα, fun x => by
    simpa only [pow_two, mul_assoc] using hc x⟩
  let f := (InnerProductSpace.toDual ℝ V).symm ℓ
  let u := hco.continuousLinearEquivOfBilin.symm f
  have hu : ∀ v, B u v = ℓ v := by
    intro v
    rw [← hco.continuousLinearEquivOfBilin_apply]
    simp [u, f]
  refine ⟨u, hu, ?_⟩
  intro w hw
  apply hco.continuousLinearEquivOfBilin.injective
  apply ext_inner_right ℝ
  intro v
  simp only [hco.continuousLinearEquivOfBilin_apply, hw, hu]

/-- Nestedness upgrades density of the union to eventual best approximation. -/
theorem infDist_tendsto_zero_of_dense_union
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (W : ℕ → Submodule ℝ V) (hmono : Monotone W)
    (hdense : Dense (⋃ m, (W m : Set V))) (x : V) :
    Filter.Tendsto (fun m => Metric.infDist x (W m : Set V)) Filter.atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨v, hv, hdist⟩ := hdense.exists_dist_lt x hε
  obtain ⟨j, hvj⟩ := Set.mem_iUnion.mp hv
  refine ⟨j, fun m hm => ?_⟩
  have hvm : v ∈ W m := hmono hm hvj
  have hle := Metric.infDist_le_dist_of_mem hvm (x := x)
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg Metric.infDist_nonneg] using
    hle.trans_lt hdist

/-- The nonsymmetric Céa estimate, including the zero-error case. -/
theorem cea_bound
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (M α : ℝ) (hα : 0 < α)
    (hb : ∀ x y, ‖B x y‖ ≤ M * ‖x‖ * ‖y‖)
    (hc : ∀ x, α * ‖x‖ ^ 2 ≤ B x x)
    (W : Submodule ℝ V) [CompleteSpace W] (ℓ : V →L[ℝ] ℝ)
    (u : V) (w : W) (hu : ∀ v, B u v = ℓ v)
    (hw : ∀ v : W, B (w : V) (v : V) = ℓ (v : V)) :
    ‖u - (w : V)‖ ≤ (M / α) * Metric.infDist u (W : Set V) := by
  by_cases he : u - (w : V) = 0
  · have humem : u ∈ W := (sub_eq_zero.mp he) ▸ w.property
    rw [he, norm_zero, Metric.infDist_zero_of_mem humem, mul_zero]
  have hpos : 0 < ‖u - (w : V)‖ := norm_pos_iff.mpr he
  have horth (v : W) : B (u - (w : V)) (v : V) = 0 := by
    simp only [map_sub, sub_apply, hu, hw, sub_self]
  let v : W := W.orthogonalProjectionOnto u
  have heq : B (u - (w : V)) (u - (w : V)) =
      B (u - (w : V)) (u - (v : V)) := by
    have hz := horth (v - w)
    have hdecomp : u - (w : V) = (u - (v : V)) + ((v : V) - (w : V)) := by
      simp only [sub_add_sub_cancel]
    calc
      B (u - (w : V)) (u - (w : V)) =
          B (u - (w : V)) ((u - (v : V)) + ((v : V) - (w : V))) :=
        congrArg (B (u - (w : V))) hdecomp
      _ = B (u - (w : V)) (u - (v : V)) := by
        rw [map_add, show B (u - (w : V)) ((v : V) - (w : V)) = 0 from hz, add_zero]
  have hbound : α * ‖u - (w : V)‖ ^ 2 ≤
      M * ‖u - (w : V)‖ * ‖u - (v : V)‖ := calc
    _ ≤ B (u - (w : V)) (u - (w : V)) := hc _
    _ = B (u - (w : V)) (u - (v : V)) := heq
    _ ≤ ‖B (u - (w : V)) (u - (v : V))‖ := le_abs_self _
    _ ≤ _ := hb _ _
  have hcancel : α * ‖u - (w : V)‖ ≤ M * ‖u - (v : V)‖ := by
    apply (mul_le_mul_iff_left₀ hpos).mp
    nlinarith only [hbound]
  have hpoint : ‖u - (w : V)‖ ≤ (M / α) * ‖u - (v : V)‖ := by
    apply (le_div_iff₀' hα).mpr at hcancel
    simpa only [div_mul_eq_mul_div] using hcancel
  have hbest : ‖u - (v : V)‖ = Metric.infDist u (W : Set V) := by
    simpa only [dist_eq_norm, Submodule.starProjection_apply] using
      W.dist_starProjection_eq_infDist u
  rwa [hbest] at hpoint

/-- Coercive Galerkin approximation in the full generality of `thm:pde-cea`. -/
theorem coercive_galerkin : P201Specs.Common.CoerciveGalerkin.{u} := by
  intro V _ _ _ a M α ℓ hb hα hc W hfin hmono hdense
  let B : V →L[ℝ] V →L[ℝ] ℝ := a.mkContinuous₂ M (by
    intro x y
    simpa only [Real.norm_eq_abs] using hb x y)
  have hBc : ∀ x, α * ‖x‖ ^ 2 ≤ B x x := hc
  have hBb : ∀ x y, ‖B x y‖ ≤ M * ‖x‖ * ‖y‖ := by
    intro x y
    exact (Real.norm_eq_abs _).le.trans (hb x y)
  obtain ⟨u, hu, huniq⟩ := bilinear_solvability B α hα hBc ℓ
  have hs (m : ℕ) : ∃! w : W m, ∀ v : W m, B (w : V) (v : V) = ℓ (v : V) := by
    let := hfin m
    exact bilinear_solvability (B.bilinearComp (W m).subtypeL (W m).subtypeL)
      α hα (fun x => hBc x) (ℓ.comp (W m).subtypeL)
  choose uₘ huₘ huniqₘ using hs
  refine ⟨u, uₘ, hu, huniq, huₘ, huniqₘ, ?_, ?_⟩
  · intro m
    let := hfin m
    exact cea_bound B M α hα hBb hBc (W m) ℓ u (uₘ m) hu (huₘ m)
  · have herr (m : ℕ) : ‖u - (uₘ m : V)‖ ≤
        (M / α) * Metric.infDist u (W m : Set V) := by
      let := hfin m
      exact cea_bound B M α hα hBb hBc (W m) ℓ u (uₘ m) hu (huₘ m)
    have hlim : Filter.Tendsto (fun m => (M / α) * Metric.infDist u (W m : Set V))
        Filter.atTop (𝓝 0) := by
      simpa only [mul_zero] using
        tendsto_const_nhds.mul (infDist_tendsto_zero_of_dense_union W hmono hdense u)
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hnorm := squeeze_zero (fun m => norm_nonneg (u - (uₘ m : V))) herr hlim
    simpa only [dist_eq_norm, norm_sub_rev] using hnorm

end P201.Common
