import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.Casorati
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.SingularityGrowth

open Filter
open scoped Topology

namespace D12Complex.Casorati

/-- The upstream order classification excludes essential singularities
for meromorphic germs, independently of the value at the puncture. -/
lemma removable_or_pole_of_meromorphic {f : ℂ → ℂ} {a : ℂ}
    (hi : IsolatedSingularityAt f a) (hf : MeromorphicAt f a) :
    RemovableSingularityAt f a ∨ PoleAt f a := by
  by_cases ho : 0 ≤ meromorphicOrderAt f a
  · exact Or.inl ((SingularityGrowth.removable_iff_order_nonneg hi hf).mpr ho)
  · exact Or.inr ((SingularityGrowth.pole_iff_order_neg hi).mpr ⟨hf, lt_of_not_ge ho⟩)

/-- An omitted disk supplies a bounded holomorphic reciprocal, hence a
meromorphic original germ. No assumption on `f a` is used. -/
lemma meromorphic_of_omitted_disk {f : ℂ → ℂ} {a w : ℂ} {r ε : ℝ}
    (hr : 0 < r) (hf : HolomorphicOn (puncturedDisk a r) f) (hε : 0 < ε)
    (homit : ∀ z ∈ puncturedDisk a r, ε ≤ ‖f z - w‖) : MeromorphicAt f a := by
  have hne : ∀ z ∈ puncturedDisk a r, f z - w ≠ 0 := by
    intro z hz
    exact norm_pos_iff.mp (hε.trans_le (homit z hz))
  have hi : IsolatedSingularityAt (fun z => (f z - w)⁻¹) a :=
    ⟨r, hr, hf.1, fun z hz => ((hf.2 z hz).sub_const w).inv (hne z hz)⟩
  have hb : ∃ C : ℝ, ∀ᶠ z in 𝓝[≠] a, ‖(f z - w)⁻¹‖ ≤ C := by
    refine ⟨ε⁻¹, ?_⟩
    filter_upwards [SingularityGrowth.puncturedDisk_mem (a := a) hr] with z hz
    rw [norm_inv]
    exact inv_anti₀ hε (homit z hz)
  have hm := SingularityGrowth.meromorphic_of_removable
    (SingularityGrowth.bounded_removable _ _ hi hb)
  have hback := hm.inv.add (MeromorphicAt.const w a)
  change MeromorphicAt (fun z => ((f z - w)⁻¹)⁻¹ + w) a at hback
  simpa only [inv_inv, sub_add_cancel] using hback

theorem approximation : Specs.D12Complex.Ch07.Casorati.approximation_type := by
  intro f a R _ hf he r hr hrR w ε hε
  by_contra h
  have homit : ∀ z ∈ puncturedDisk a r, ε ≤ ‖f z - w‖ := by
    intro z hz
    exact le_of_not_gt (fun hlt => h ⟨z, hz, hlt⟩)
  have hfr : HolomorphicOn (puncturedDisk a r) f :=
    ⟨(isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))).inter
      (isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const),
      fun z hz => hf.2 z ⟨hz.1, hz.2.trans_le hrR⟩⟩
  rcases removable_or_pole_of_meromorphic he.1
      (meromorphic_of_omitted_disk hr hfr hε homit) with hrem | hpole
  · exact he.2.1 hrem
  · exact he.2.2 hpole

end D12Complex.Casorati
