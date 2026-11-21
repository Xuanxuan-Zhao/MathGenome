import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.EmbeddedManifoldCharts
import MathGenome.Internal.MultivariableAnalysis.D04.C01.Compactness
import MathGenome.Internal.MultivariableAnalysis.D04.C02.DerivativeInterfaces

/-! Embedded charts, restriction, and dimension zero (d04:14:embedded).
The shared objects live in the independent Spec; this module proves their
basic properties. It assumes neither chart-transition regularity nor integration. -/
noncomputable section
open Set Topology
open scoped ContDiff
namespace D04

abbrev ManifoldRegularity := Specs.D04.C14.EmbeddedManifoldCharts.Model.ManifoldRegularity
abbrev halfSpace := Specs.D04.C14.EmbeddedManifoldCharts.Model.halfSpace
abbrev flatBoundary := Specs.D04.C14.EmbeddedManifoldCharts.Model.flatBoundary
abbrev parameterSpace := Specs.D04.C14.EmbeddedManifoldCharts.Model.parameterSpace
abbrev FullRankLocalExtension := @Specs.D04.C14.EmbeddedManifoldCharts.Model.FullRankLocalExtension
abbrev EmbeddedChart := Specs.D04.C14.EmbeddedManifoldCharts.Model.EmbeddedChart
abbrev CenteredAt := @Specs.D04.C14.EmbeddedManifoldCharts.Model.CenteredAt
abbrev IsEmbeddedManifold := @Specs.D04.C14.EmbeddedManifoldCharts.Model.IsEmbeddedManifold
abbrev intrinsicBoundary := @Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary

theorem halfSpace_succ (d : ℕ) (u : E (d+1)) :
    u ∈ halfSpace (d+1) ↔ 0 ≤ u (Fin.last d) := Iff.rfl

theorem flatBoundary_succ (d : ℕ) (u : E (d+1)) :
    u ∈ flatBoundary (d+1) ↔ u (Fin.last d) = 0 := Iff.rfl

namespace EmbeddedChart
variable {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}

/-- The chart data are precisely a homeomorphism for the relative topologies. -/
def homeomorph (c : EmbeddedChart r k n M) : c.source ≃ₜ ↥(M ∩ c.ambient) where
  toFun u := ⟨c.toFun u, c.map_source u.property⟩
  invFun x := ⟨c.invFun x, c.map_target x.property⟩
  left_inv u := Subtype.ext (c.left_inv u u.property)
  right_inv x := Subtype.ext (c.right_inv x x.property)
  continuous_toFun := c.continuous_toFun.mapsToRestrict c.map_source
  continuous_invFun := c.continuous_invFun.mapsToRestrict c.map_target

/-- Restrict to any ambient open neighborhood. Empty restrictions are also charts. -/
def restrict (c : EmbeddedChart r k n M) (O : Set (E n)) (hO : IsOpen O) :
    EmbeddedChart r k n M where
  half := c.half
  half_pos := c.half_pos
  source := c.source ∩ c.toFun ⁻¹' O
  source_open := by
    obtain ⟨W, hW, hcW⟩ := c.source_open
    obtain ⟨T, hT, he⟩ := continuousOn_iff'.mp c.continuous_toFun O hO
    refine ⟨W ∩ T, hW.inter hT, ?_⟩
    rw [inter_comm c.source, he, hcW]
    ext u
    simp only [mem_inter_iff]
    tauto
  ambient := c.ambient ∩ O
  ambient_open := c.ambient_open.inter hO
  toFun := c.toFun
  invFun := c.invFun
  map_source := by
    intro u hu
    exact ⟨(c.map_source hu.1).1, (c.map_source hu.1).2, hu.2⟩
  map_target := by
    intro x hx
    refine ⟨c.map_target ⟨hx.1, hx.2.1⟩, ?_⟩
    change c.toFun (c.invFun x) ∈ O
    rw [c.right_inv x ⟨hx.1, hx.2.1⟩]
    exact hx.2.2
  left_inv u hu := c.left_inv u hu.1
  right_inv x hx := c.right_inv x ⟨hx.1, hx.2.1⟩
  continuous_toFun := c.continuous_toFun.mono inter_subset_left
  continuous_invFun := c.continuous_invFun.mono (by intro x hx; exact ⟨hx.1, hx.2.1⟩)
  regular := by
    intro u hu
    obtain ⟨W, g, hW, huW, he, hg, hDg⟩ := c.regular u hu.1
    exact ⟨W, g, hW, huW, he.mono (by intro v hv; exact ⟨hv.1.1, hv.2⟩), hg, hDg⟩

end EmbeddedChart

theorem embeddedChart_homeomorph {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart r k n M) :
    ∃ e : c.source ≃ₜ ↥(M ∩ c.ambient), ∀ u : c.source, (e u).val = c.toFun u :=
  ⟨c.homeomorph, fun _ => rfl⟩

theorem embeddedChart_restrict {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart r k n M) (O : Set (E n)) (hO : IsOpen O) :
    ∃ d : EmbeddedChart r k n M,
      d.half = c.half ∧ d.source = c.source ∩ c.toFun ⁻¹' O ∧
      d.ambient = c.ambient ∩ O ∧ d.toFun = c.toFun ∧ d.invFun = c.invFun :=
  ⟨c.restrict O hO, rfl, rfl, rfl, rfl, rfl⟩

/-- Restriction to an open set in the parameter space is also realized by an
ambient open restriction, because the inverse chart is relatively continuous. -/
theorem embeddedChart_restrict_parameter {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart r k n M) (W : Set (E k)) (hW : IsOpen W) :
    ∃ d : EmbeddedChart r k n M,
      d.source = c.source ∩ W ∧ d.ambient ⊆ c.ambient ∧
      d.toFun = c.toFun ∧ d.invFun = c.invFun ∧ d.half = c.half := by
  obtain ⟨T, hT, he⟩ := continuousOn_iff'.mp c.continuous_invFun W hW
  refine ⟨c.restrict T hT, ?_, inter_subset_left, rfl, rfl, rfl⟩
  change c.source ∩ c.toFun ⁻¹' T = c.source ∩ W
  ext u
  constructor
  · rintro ⟨hu, huT⟩
    have htu : c.toFun u ∈ T ∩ (M ∩ c.ambient) := ⟨huT, c.map_source hu⟩
    rw [← he] at htu
    exact ⟨hu, by simpa only [mem_preimage, c.left_inv u hu] using htu.1⟩
  · rintro ⟨hu, huW⟩
    have htu : c.toFun u ∈ c.invFun ⁻¹' W ∩ (M ∩ c.ambient) :=
      ⟨by simpa only [mem_preimage, c.left_inv u hu] using huW, c.map_source hu⟩
    rw [he] at htu
    exact ⟨hu, htu.1⟩

theorem centered_restriction {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart r k n M) (u : E k) (O : Set (E n))
    (hu : CenteredAt c u) (hO : IsOpen O) (huO : c.toFun u ∈ O) :
    ∃ d : EmbeddedChart r k n M, CenteredAt d u ∧
      d.source = c.source ∩ c.toFun ⁻¹' O ∧ d.ambient = c.ambient ∩ O ∧
      d.toFun = c.toFun ∧ d.invFun = c.invFun ∧ d.half = c.half := by
  exact ⟨c.restrict O hO, ⟨⟨hu.1, huO⟩, hu.2⟩, rfl, rfl, rfl, rfl, rfl⟩

theorem derivative_rank {k n : ℕ} (A : E k →L[ℝ] E n) (hA : Function.Injective A) :
    Module.finrank ℝ (LinearMap.range A.toLinearMap) = k := by
  rw [LinearMap.finrank_range_of_inj hA]
  exact finrank_euclideanSpace_fin

theorem open_fullRankLocalExtension_iff {r : ℕ∞ω} {k n : ℕ}
    (V : Set (E k)) (f : E k → E n) (hV : IsOpen V) :
    FullRankLocalExtension r V f ↔
      ContDiffOn ℝ r f V ∧ ∀ u ∈ V, Function.Injective (fderiv ℝ f u) := by
  constructor
  · intro h
    constructor
    · intro u hu
      obtain ⟨W, g, hW, huW, he, hg, _⟩ := h u hu
      have heq : g =ᶠ[𝓝 u] f :=
        Filter.eventuallyEq_of_mem ((hV.inter hW).mem_nhds ⟨hu, huW⟩) he
      exact ((hg.contDiffAt (hW.mem_nhds huW)).congr_of_eventuallyEq heq.symm).contDiffWithinAt
    · intro u hu
      obtain ⟨W, g, hW, huW, he, _, hDg⟩ := h u hu
      have heq : g =ᶠ[𝓝 u] f :=
        Filter.eventuallyEq_of_mem ((hV.inter hW).mem_nhds ⟨hu, huW⟩) he
      rw [← heq.fderiv_eq]
      exact hDg u huW
  · rintro ⟨hf, hDf⟩ u hu
    exact ⟨V, f, hV, hu, fun _ _ => rfl, hf, hDf⟩

/-- An isolated point gives a genuine zero-dimensional chart. -/
private def zeroChart {r : ℕ∞ω} {n : ℕ} {M : Set (E n)}
    (x : E n) (O : Set (E n)) (hO : IsOpen O) (he : O ∩ M = {x}) :
    EmbeddedChart r 0 n M where
  half := false
  half_pos := by simp
  source := univ
  source_open := ⟨univ, isOpen_univ, by simp [Specs.D04.C14.EmbeddedManifoldCharts.Model.parameterSpace]⟩
  ambient := O
  ambient_open := hO
  toFun := fun _ => x
  invFun := fun _ => 0
  map_source := by
    intro _ _
    have hx : x ∈ O ∩ M := by rw [he]; exact mem_singleton x
    exact ⟨hx.2, hx.1⟩
  map_target := by intro _ _; trivial
  left_inv := by intro u _; exact Subsingleton.elim _ _
  right_inv := by
    intro y hy
    have : y ∈ O ∩ M := ⟨hy.2, hy.1⟩
    rw [he] at this
    exact (mem_singleton_iff.mp this).symm
  continuous_toFun := continuous_const.continuousOn
  continuous_invFun := continuous_const.continuousOn
  regular := by
    intro u _
    refine ⟨univ, (fun _ => x), isOpen_univ, mem_univ u, fun _ _ => rfl,
      contDiffOn_const, ?_⟩
    intro _ _ a b _
    exact Subsingleton.elim a b

theorem zero_manifold_iff_discrete (r : ℕ∞ω) {n : ℕ} (M : Set (E n)) :
    IsEmbeddedManifold r 0 M ↔ ManifoldRegularity r ∧ IsDiscrete M := by
  constructor
  · rintro ⟨hr, _, hcharts⟩
    refine ⟨hr, isDiscrete_iff_forall_mem_exists_isOpen.mpr ?_⟩
    intro x hx
    obtain ⟨c, u, hu, hux⟩ := hcharts x hx
    refine ⟨c.ambient, c.ambient_open, ?_⟩
    ext y
    constructor
    · intro hy
      have hy' := c.right_inv y ⟨hy.2, hy.1⟩
      have hzero : c.invFun y = u := Subsingleton.elim _ _
      rw [hzero, hux] at hy'
      exact mem_singleton_iff.mpr hy'.symm
    · intro hy
      have hyx := mem_singleton_iff.mp hy
      subst y
      exact ⟨(hux ▸ c.map_source hu.1).2, hx⟩
  · rintro ⟨hr, hd⟩
    refine ⟨hr, Nat.zero_le n, ?_⟩
    intro x hx
    obtain ⟨O, hO, he⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hd x hx
    exact ⟨zeroChart x O hO he, 0, ⟨mem_univ _, by simp [zeroChart]⟩, rfl⟩

theorem zero_intrinsicBoundary (r : ℕ∞ω) {n : ℕ} (M : Set (E n)) :
    intrinsicBoundary r 0 M = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro x ⟨_, c, u, _, _, hu, _⟩
  exact hu

theorem compact_zero_manifold_finite (r : ℕ∞ω) {n : ℕ} (M : Set (E n))
    (hM : IsEmbeddedManifold r 0 M) (hcompact : Compact M) : M.Finite := by
  exact ((compact_iff_isCompact M).mp hcompact).finite
    ((zero_manifold_iff_discrete r M).mp hM).2

end D04
