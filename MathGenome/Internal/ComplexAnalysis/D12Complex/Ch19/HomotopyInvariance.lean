import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch19.HomotopyInvariance
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch19.ChainStability
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch19.ContinuationUniqueOperations
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.UniformSpace.HeineCantor

open Set Filter
open scoped Topology
noncomputable section
namespace D12Complex.HomotopyInvariance

/-! Chain stability and uniqueness make the terminal germ locally constant.
Connectedness of the homotopy parameter interval then makes it constant. -/

/-- Equal basepoints identify transported initial germs. -/
private lemma transport_initial {x y a : ℂ} (hx : x = a) (hy : y = a)
    (φ : HolomorphicGerm a) (h : x = y) :
    (h.symm ▸ (hy.symm ▸ φ)) = (hx.symm ▸ φ) := by
  subst x
  subst y
  rfl

/-- Heterogeneous equality of terminal germs becomes equality in the fixed fibre. -/
private lemma transport_terminal {x y b : ℂ} (hx : x = b) (hy : y = b)
    (φ : HolomorphicGerm x) (ψ : HolomorphicGerm y) (h : HEq φ ψ) :
    Eq.mp (congrArg HolomorphicGerm hx) φ = Eq.mp (congrArg HolomorphicGerm hy) ψ := by
  subst x
  subst y
  exact eq_of_heq h

/-- Continuity on the compact square controls all points of a slice at once.
The factor two keeps the supremum strictly below the requested tolerance. -/
lemma slices_uniformly_close {H : unitInterval × unitInterval → ℂ}
    (hH : Continuous H) (s : unitInterval) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ r in 𝓝 s, (⨆ t, ‖H (t, r) - H (t, s)‖) < δ := by
  obtain ⟨ε, hε, hcontrol⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hH) (δ / 2) (half_pos hδ)
  filter_upwards [Metric.ball_mem_nhds s hε] with r hr
  have hpoint (t : unitInterval) : ‖H (t, r) - H (t, s)‖ < δ / 2 := by
    have hd : dist (t, r) (t, s) < ε := by
      simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using
        (show dist r s < ε from hr)
    simpa only [dist_eq_norm] using hcontrol hd
  exact (ciSup_le (fun t => (hpoint t).le)).trans_lt (half_lt_self hδ)

theorem homotopy_invariance :
    Specs.D12Complex.Ch19.HomotopyInvariance.homotopy_invariance_type := by
  intro Ω a b H _hΩ hH hmem h0 h1 φ hex
  choose F hF using hex
  let E : unitInterval → HolomorphicGerm b :=
    fun s => Eq.mp (congrArg HolomorphicGerm (h1 s)) (F s 1)
  have hE : IsLocallyConstant E := by
    apply (IsLocallyConstant.iff_eventually_eq E).mpr
    intro s
    obtain ⟨δ, hδ, hstable⟩ :=
      ChainStability.continuation_stability_fixed_endpoints
        Ω (fun t => H (t, s)) _ (F s) (hF s)
    filter_upwards [slices_uniformly_close hH s hδ] with r hr
    have hc : Continuous (fun t => H (t, r)) :=
      hH.comp (continuous_id.prodMk continuous_const)
    have hstart : H (0, r) = H (0, s) := (h0 r).trans (h0 s).symm
    have hend : H (1, r) = H (1, s) := (h1 r).trans (h1 s).symm
    obtain ⟨G, hG, hterm⟩ := hstable (fun t => H (t, r)) hc
      (fun t => hmem (t, r)) hstart hend hr
    have hG' : IsContinuation Ω (fun t => H (t, r)) ((h0 r).symm ▸ φ) G := by
      simpa only [transport_initial (h0 r) (h0 s) φ hstart] using hG
    have heq := ContinuationOperations.continuation_unique Ω (fun t => H (t, r))
      _ (F r) G (hF r) hG' 1
    exact transport_terminal (h1 r) (h1 s) (F r 1) (F s 1)
      ((heq_of_eq heq).trans hterm)
  intro s r Φ Ψ hΦ hΨ
  have hs := ContinuationOperations.continuation_unique Ω (fun t => H (t, s))
    _ Φ (F s) hΦ (hF s) 1
  have hr := ContinuationOperations.continuation_unique Ω (fun t => H (t, r))
    _ Ψ (F r) hΨ (hF r) 1
  calc
    Eq.mp (congrArg HolomorphicGerm (h1 s)) (Φ 1) = E s :=
      congrArg (fun g => Eq.mp (congrArg HolomorphicGerm (h1 s)) g) hs
    _ = E r := hE.apply_eq_of_preconnectedSpace s r
    _ = Eq.mp (congrArg HolomorphicGerm (h1 r)) (Ψ 1) :=
      (congrArg (fun g => Eq.mp (congrArg HolomorphicGerm (h1 r)) g) hr).symm

end D12Complex.HomotopyInvariance
