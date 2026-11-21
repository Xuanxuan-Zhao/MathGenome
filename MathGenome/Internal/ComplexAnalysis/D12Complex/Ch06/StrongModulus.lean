import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch06.StrongModulus
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.OpenMapping
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
The strong modulus principles follow from open mapping. An open image cannot
have one of its own points on the sphere bounding a closed ball containing it.
The minimum principle applies the maximum principle to the reciprocal, whose
holomorphy requires exactly the stated nonvanishing on Ω.
-/

open Filter Set
open scoped Topology

namespace D12Complex.StrongModulus

theorem constant_of_local_maximum_modulus :
    Specs.D12Complex.Ch06.StrongModulus.constant_of_local_maximum_modulus_type := by
  intro Ω f a hΩ hf ha hmax
  classical
  by_contra hnot
  have hnc : ¬ ∃ c : ℂ, ∀ z ∈ Ω, f z = c := by
    rintro ⟨c, hc⟩
    exact hnot (fun z hz => (hc z hz).trans (hc a ha).symm)
  have hlocal : ∀ᶠ z in 𝓝 a, ‖f z‖ ≤ ‖f a‖ :=
    hmax.isLocalMax (hf.1.mem_nhds ha)
  have hmem : ∀ᶠ z in 𝓝 a, z ∈ Ω := hf.1.mem_nhds ha
  obtain ⟨U, hU, hUopen, haU⟩ := mem_nhds_iff.mp (hmem.and hlocal)
  have himage : IsOpen (f '' U) :=
    OpenMapping.image_open_of_nonconstant Ω f hΩ hf hnc U hUopen
      (fun z hz => (hU hz).1)
  have hsub : f '' U ⊆ Metric.closedBall (0 : ℂ) ‖f a‖ := by
    rintro _ ⟨z, hz, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using (hU hz).2
  have hinner : f a ∈ interior (Metric.closedBall (0 : ℂ) ‖f a‖) :=
    mem_interior_iff_mem_nhds.mpr
      (mem_of_superset (himage.mem_nhds ⟨a, haU, rfl⟩) hsub)
  rw [interior_closedBall', Metric.mem_ball, dist_zero_right] at hinner
  exact (lt_irrefl ‖f a‖) hinner

theorem constant_of_local_minimum_modulus :
    Specs.D12Complex.Ch06.StrongModulus.constant_of_local_minimum_modulus_type := by
  intro Ω f a hΩ hf hne ha hmin
  have hinv : HolomorphicOn Ω (fun z => (f z)⁻¹) :=
    ⟨hf.1, fun z hz => (hf.2 z hz).inv (hne z hz)⟩
  have hmax : IsLocalMaxOn (fun z => ‖(f z)⁻¹‖) Ω a := by
    filter_upwards [hmin] with z hz
    simpa only [norm_inv] using inv_anti₀ (norm_pos_iff.mpr (hne a ha)) hz
  have heq := constant_of_local_maximum_modulus Ω (fun z => (f z)⁻¹) a
    hΩ hinv ha hmax
  exact fun z hz => inv_inj.mp (heq z hz)

end D12Complex.StrongModulus
