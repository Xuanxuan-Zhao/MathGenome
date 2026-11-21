import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.Sphere
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Normed.Group.Bounded

open scoped Topology
noncomputable section

namespace D12Complex.Sphere

abbrev RiemannSphere : Specs.D12Complex.Ch07.Sphere.RiemannSphere_type :=
  _root_.D12Complex.RiemannSphere

abbrev sphereInfty : Specs.D12Complex.Ch07.Sphere.sphereInfty_type :=
  _root_.D12Complex.sphereInfty

abbrev sphereFinite : Specs.D12Complex.Ch07.Sphere.sphereFinite_type :=
  _root_.D12Complex.sphereFinite

abbrev finiteCoordinate : Specs.D12Complex.Ch07.Sphere.finiteCoordinate_type :=
  _root_.D12Complex.finiteCoordinate

abbrev infinityCoordinate : Specs.D12Complex.Ch07.Sphere.infinityCoordinate_type :=
  _root_.D12Complex.infinityCoordinate

abbrev infinityParametrization : Specs.D12Complex.Ch07.Sphere.infinityParametrization_type :=
  _root_.D12Complex.infinityParametrization

abbrev finiteChart : Specs.D12Complex.Ch07.Sphere.finiteChart_type :=
  _root_.D12Complex.finiteChart

abbrev infinityChart : Specs.D12Complex.Ch07.Sphere.infinityChart_type :=
  _root_.D12Complex.infinityChart

abbrev exterior : Specs.D12Complex.Ch07.Sphere.exterior_type :=
  _root_.D12Complex.exterior

abbrev infinityNeighborhood : Specs.D12Complex.Ch07.Sphere.infinityNeighborhood_type :=
  _root_.D12Complex.infinityNeighborhood

abbrev reciprocalPullback : Specs.D12Complex.Ch07.Sphere.reciprocalPullback_type :=
  _root_.D12Complex.reciprocalPullback

abbrev infinityPullback : Specs.D12Complex.Ch07.Sphere.infinityPullback_type :=
  _root_.D12Complex.infinityPullback

abbrev IsolatedSingularityAtInfinity : Specs.D12Complex.Ch07.Sphere.IsolatedSingularityAtInfinity_type :=
  _root_.D12Complex.IsolatedSingularityAtInfinity

abbrev RemovableSingularityAtInfinity : Specs.D12Complex.Ch07.Sphere.RemovableSingularityAtInfinity_type :=
  _root_.D12Complex.RemovableSingularityAtInfinity

abbrev PoleOfOrderAtInfinity : Specs.D12Complex.Ch07.Sphere.PoleOfOrderAtInfinity_type :=
  _root_.D12Complex.PoleOfOrderAtInfinity

abbrev PoleAtInfinity : Specs.D12Complex.Ch07.Sphere.PoleAtInfinity_type :=
  _root_.D12Complex.PoleAtInfinity

abbrev EssentialSingularityAtInfinity : Specs.D12Complex.Ch07.Sphere.EssentialSingularityAtInfinity_type :=
  _root_.D12Complex.EssentialSingularityAtInfinity

abbrev HolomorphicAtInfinity : Specs.D12Complex.Ch07.Sphere.HolomorphicAtInfinity_type :=
  _root_.D12Complex.HolomorphicAtInfinity

abbrev MeromorphicAtInfinity : Specs.D12Complex.Ch07.Sphere.MeromorphicAtInfinity_type :=
  _root_.D12Complex.MeromorphicAtInfinity

abbrev HolomorphicAtInfinityWithValue : Specs.D12Complex.Ch07.Sphere.HolomorphicAtInfinityWithValue_type :=
  _root_.D12Complex.HolomorphicAtInfinityWithValue

end D12Complex.Sphere

namespace D12Complex

theorem sphereFinite_injective : Function.Injective sphereFinite :=
  OnePoint.coe_injective

theorem sphere_eq_infty_or_finite (p : RiemannSphere) :
    p = sphereInfty ∨ ∃ z : ℂ, p = sphereFinite z := by
  induction p using OnePoint.rec with
  | infty => exact Or.inl rfl
  | coe z => exact Or.inr ⟨z, rfl⟩

theorem nhds_sphereFinite (z : ℂ) :
    𝓝 (sphereFinite z) = Filter.map sphereFinite (𝓝 z) :=
  OnePoint.nhds_coe_eq z

theorem mem_nhds_sphereInfty_iff (U : Set RiemannSphere) :
    U ∈ 𝓝 sphereInfty ↔ ∃ R : ℝ, 0 < R ∧ infinityNeighborhood R ⊆ U := by
  rw [sphereInfty, OnePoint.nhds_infty_eq]
  simp only [Filter.mem_sup, Filter.mem_map, Filter.mem_pure]
  rw [Filter.coclosedCompact_eq_cocompact,
    Metric.mem_cocompact_iff_closedBall_compl_subset (0 : ℂ)]
  constructor
  · rintro ⟨⟨r, hr⟩, hi⟩
    refine ⟨max r 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
    intro p hp
    rcases hp with hp | ⟨z, hz, rfl⟩
    · change p = sphereInfty at hp
      exact hp.symm ▸ hi
    · apply hr
      change ¬dist z 0 ≤ r
      have hz' : max r 1 < ‖z‖ := hz
      simpa only [dist_zero_right, not_le] using
        lt_of_le_of_lt (le_max_left r 1) hz'
  · rintro ⟨R, hR, hU⟩
    refine ⟨⟨R, ?_⟩, hU (Or.inl rfl)⟩
    intro z hz
    apply hU
    right
    refine ⟨z, ?_, rfl⟩
    simpa only [exterior, Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right, Set.mem_compl_iff, not_le]
      using hz

@[simp] theorem finiteCoordinate_sphereFinite (z : ℂ) :
    finiteCoordinate (sphereFinite z) = z := rfl

@[simp] theorem infinityCoordinate_sphereFinite (z : ℂ) :
    infinityCoordinate (sphereFinite z) = z⁻¹ := rfl

@[simp] theorem infinityCoordinate_sphereInfty :
    infinityCoordinate sphereInfty = 0 := rfl

@[simp] theorem infinityParametrization_zero :
    infinityParametrization 0 = sphereInfty := by
  simp [infinityParametrization]

theorem infinityParametrization_ne_zero (w : ℂ) (hw : w ≠ 0) :
    infinityParametrization w = sphereFinite w⁻¹ := by
  simp [infinityParametrization, hw]

theorem infinityChart_finiteChart_transition (z : ℂ) (_hz : z ≠ 0) :
    infinityChart (finiteChart.symm z) = z⁻¹ := rfl

/-- Inversion takes an entire exterior into an entire punctured disk. -/
private theorem inv_mem_puncturedDisk {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : r⁻¹ < ‖z‖) : z⁻¹ ∈ puncturedDisk 0 r := by
  have hn : 0 < ‖z‖ := lt_trans (inv_pos.mpr hr) hz
  simp only [puncturedDisk, Set.mem_ofPred_eq, sub_zero, norm_inv]
  exact ⟨inv_pos.mpr hn, (inv_lt_comm₀ hr hn).mp hz⟩

/-- Inversion takes every point of the punctured disk into the corresponding exterior. -/
private theorem inv_mem_exterior {r : ℝ} (hr : 0 < r) {w : ℂ}
    (hw : w ∈ puncturedDisk 0 r) : w⁻¹ ∈ exterior r⁻¹ := by
  have hw' : 0 < ‖w‖ ∧ ‖w‖ < r := by simpa [puncturedDisk] using hw
  change r⁻¹ < ‖w⁻¹‖
  rw [norm_inv]
  exact (inv_lt_inv₀ hr hw'.1).mpr hw'.2

theorem isolatedSingularityAtInfinity_iff_exterior (f : ℂ → ℂ) :
    IsolatedSingularityAtInfinity f ↔
      ∃ R : ℝ, 0 < R ∧ HolomorphicOn (exterior R) f := by
  constructor
  · rintro ⟨r, hr, hg⟩
    refine ⟨r⁻¹, inv_pos.mpr hr, ?_, ?_⟩
    · exact isOpen_lt continuous_const continuous_norm
    · intro z hz
      have hz' : r⁻¹ < ‖z‖ := hz
      have hn : z ≠ 0 := norm_pos_iff.mp (lt_trans (inv_pos.mpr hr) hz')
      have h := (hg.2 z⁻¹ (inv_mem_puncturedDisk hr hz')).comp z
        (differentiableAt_inv_iff.mpr hn)
      simpa only [Function.comp_def, reciprocalPullback, inv_inv] using h
  · rintro ⟨R, hR, hf⟩
    refine ⟨R⁻¹, inv_pos.mpr hR, ?_, ?_⟩
    · simpa only [puncturedDisk, sub_zero, Set.ofPred_and] using
        (isOpen_lt (f := fun _ : ℂ => (0 : ℝ)) continuous_const continuous_norm).inter
          (isOpen_lt continuous_norm (g := fun _ : ℂ => R⁻¹) continuous_const)
    · intro w hw
      have hw' : 0 < ‖w‖ ∧ ‖w‖ < R⁻¹ := by simpa [puncturedDisk] using hw
      have he : w⁻¹ ∈ exterior R := by
        have := inv_mem_exterior (inv_pos.mpr hR) hw
        simpa only [inv_inv] using this
      exact (hf.2 w⁻¹ he).comp w
        (differentiableAt_inv_iff.mpr (norm_pos_iff.mp hw'.1))

theorem removableSingularityAtInfinity_isolated (f : ℂ → ℂ)
    (h : RemovableSingularityAtInfinity f) : IsolatedSingularityAtInfinity f := h.1

theorem poleOfOrderAtInfinity_positive (f : ℂ → ℂ) (m : ℕ)
    (h : PoleOfOrderAtInfinity f m) : 1 ≤ m := h.1

theorem poleOfOrderAtInfinity_isolated (f : ℂ → ℂ) (m : ℕ)
    (h : PoleOfOrderAtInfinity f m) : IsolatedSingularityAtInfinity f := h.2.1

theorem essentialSingularityAtInfinity_iff (f : ℂ → ℂ) :
    EssentialSingularityAtInfinity f ↔
      IsolatedSingularityAtInfinity f ∧ ¬RemovableSingularityAtInfinity f ∧
        ¬PoleAtInfinity f := Iff.rfl

theorem holomorphicAtInfinity_iff_removable (f : ℂ → ℂ) :
    HolomorphicAtInfinity f ↔ RemovableSingularityAtInfinity f := Iff.rfl

theorem meromorphicAtInfinity_iff (f : ℂ → ℂ) :
    MeromorphicAtInfinity f ↔ RemovableSingularityAtInfinity f ∨ PoleAtInfinity f := Iff.rfl

end D12Complex
