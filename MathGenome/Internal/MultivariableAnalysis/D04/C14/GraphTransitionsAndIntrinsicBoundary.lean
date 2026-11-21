import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary
import MathGenome.Internal.MultivariableAnalysis.D04.C14.LocalGraphAndAmbientInverse
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.TangentCone.Real

noncomputable section
open Set Filter Topology
open scoped ContDiff NNReal
namespace D04

abbrev chartOverlap := @Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model.chartOverlap
abbrev chartTransition := @Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model.chartTransition
abbrev IsBoundaryParameter := @Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model.IsBoundaryParameter
abbrev inwardParameterCone := @Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model.inwardParameterCone
abbrev IsBoundarylessEmbeddedManifold :=
  @Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model.IsBoundarylessEmbeddedManifold

theorem local_graph : Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.local_graphType :=
  local_graph_and_ambient_inverse

theorem intrinsic_boundary_zero :
    Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.intrinsic_boundary_zeroType :=
  zero_intrinsicBoundary

namespace EmbeddedChart
variable {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}

theorem transition_mem (c d : EmbeddedChart r k n M) {u : E k}
    (hu : u ∈ chartOverlap c d) : chartTransition c d u ∈ chartOverlap d c := by
  have hx : c.toFun u ∈ M ∩ d.ambient := ⟨(c.map_source hu.1).1, hu.2⟩
  refine ⟨d.map_target hx, ?_⟩
  change d.toFun (d.invFun (c.toFun u)) ∈ c.ambient
  rw [d.right_inv _ hx]
  exact (c.map_source hu.1).2

theorem transition_left_inv (c d : EmbeddedChart r k n M) {u : E k}
    (hu : u ∈ chartOverlap c d) :
    chartTransition d c (chartTransition c d u) = u := by
  change c.invFun (d.toFun (d.invFun (c.toFun u))) = u
  rw [d.right_inv _ ⟨(c.map_source hu.1).1, hu.2⟩, c.left_inv _ hu.1]

theorem transition_continuous (c d : EmbeddedChart r k n M) :
    ContinuousOn (chartTransition c d) (chartOverlap c d) := by
  apply d.continuous_invFun.comp (c.continuous_toFun.mono inter_subset_left)
  intro u hu
  exact ⟨(c.map_source hu.1).1, hu.2⟩

theorem overlap_relatively_open (c d : EmbeddedChart r k n M) :
    ∃ W : Set (E k), IsOpen W ∧ chartOverlap c d = c.source ∩ W := by
  obtain ⟨W, hW, he⟩ := continuousOn_iff'.mp c.continuous_toFun d.ambient d.ambient_open
  exact ⟨W, hW, by change c.source ∩ c.toFun ⁻¹' d.ambient = c.source ∩ W; simpa only [inter_comm] using he⟩

end EmbeddedChart
open EmbeddedChart

theorem chart_inverse_extension :
    Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.chart_inverse_extensionType := by
  intro r k n M c hr hkn u hu
  obtain ⟨s, W, g, X, Y, q, h⟩ := local_graph_and_ambient_inverse
    c.source c.toFun u c.half hr hkn c.half_pos c.source_open c.regular hu
  obtain ⟨hX, hY, huX, hguY, hXW, _, _, _, _, _⟩ := h.inverse
  let P := coordinateProjection s
  obtain ⟨T, hT, he⟩ := continuousOn_iff'.mp c.continuous_invFun X hX
  have hxu : c.toFun u ∈ M ∩ c.ambient := c.map_source hu
  have hxT : c.toFun u ∈ T := by
    have : c.toFun u ∈ c.invFun ⁻¹' X ∩ (M ∩ c.ambient) :=
      ⟨by simpa only [mem_preimage, c.left_inv u hu] using huX, hxu⟩
    rw [he] at this
    exact this.1
  have hxY : P (c.toFun u) ∈ Y := by
    rw [← h.extension_agrees ⟨hu, hXW huX⟩]
    exact hguY
  refine ⟨T ∩ P ⁻¹' Y, q ∘ P, hT.inter (hY.preimage P.continuous), ?_, ?_, ?_⟩
  · exact ⟨hxT, hxY⟩
  · exact h.inverse_ambient_regular.mono inter_subset_right
  · intro x hx
    have hxX : c.invFun x ∈ X := by
      have : x ∈ T ∩ (M ∩ c.ambient) := ⟨hx.2.1, hx.1⟩
      rw [← he] at this
      exact this.1
    have hinv := h.inverse_left ⟨c.map_target hx.1, hxX⟩
    rw [c.right_inv x hx.1] at hinv
    exact hinv

namespace EmbeddedChart
variable {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}

/-- A transition has a genuine Euclidean extension locally, even when its
source is only relatively open in the half-space. -/
theorem transition_extension (c d : EmbeddedChart r k n M)
    (hr : ManifoldRegularity r) (hkn : k ≤ n) {u : E k}
    (hu : u ∈ chartOverlap c d) :
    ∃ (W : Set (E k)) (F : E k → E k), IsOpen W ∧ u ∈ W ∧
      ContDiffOn ℝ r F W ∧ EqOn F (chartTransition c d) (chartOverlap c d ∩ W) := by
  have hv := (EmbeddedChart.transition_mem c) d hu
  obtain ⟨O, J, hO, hxO, hJ, hJe⟩ := chart_inverse_extension d hr hkn
    (chartTransition c d u) hv.1
  have hdu : d.toFun (chartTransition c d u) = c.toFun u :=
    d.right_inv _ ⟨(c.map_source hu.1).1, hu.2⟩
  rw [hdu] at hxO
  obtain ⟨W, g, hW, huW, he, hg, _⟩ := c.regular u hu.1
  have hgu : g u = c.toFun u := he ⟨hu.1, huW⟩
  refine ⟨W ∩ g ⁻¹' O, J ∘ g,
    hg.continuousOn.isOpen_inter_preimage hW hO, ⟨huW, by change g u ∈ O; rw [hgu]; exact hxO⟩,
    hJ.comp (hg.mono inter_subset_left) (fun _ hv => hv.2), ?_⟩
  intro v hv
  change J (g v) = d.invFun (c.toFun v)
  rw [he ⟨hv.1.1, hv.2.1⟩]
  apply hJe
  refine ⟨⟨(c.map_source hv.1.1).1, hv.1.2⟩, ?_⟩
  simpa only [mem_preimage, he ⟨hv.1.1, hv.2.1⟩] using hv.2.2

end EmbeddedChart

theorem chart_transition_regular :
    Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.chart_transition_regularType := by
  intro r k n M c d hr hkn
  refine ⟨?_, fun u hu => (EmbeddedChart.transition_extension c) d hr hkn hu⟩
  intro u hu
  obtain ⟨W, F, hW, huW, hF, he⟩ := (EmbeddedChart.transition_extension c) d hr hkn hu
  exact ((hF.contDiffAt (hW.mem_nhds huW)).contDiffWithinAt).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (hW.mem_nhds huW))) he.symm)
    (he ⟨hu, huW⟩).symm

/-- Half-space domains have unique full derivatives, including at the flat face. -/
theorem parameterSpace_uniqueDiff (k : ℕ) (half : Bool) :
    UniqueDiffOn ℝ (parameterSpace k half) := by
  cases half with
  | false => exact uniqueDiffOn_univ
  | true =>
    cases k with
    | zero => exact uniqueDiffOn_univ
    | succ d =>
      let π : E (d+1) →L[ℝ] ℝ := EuclideanSpace.proj (Fin.last d)
      have hconv : Convex ℝ (halfSpace (d+1)) :=
        (convex_Ici (0 : ℝ)).linear_preimage π.toLinearMap
      have hpos : IsOpen {u : E (d+1) | 0 < π u} :=
        isOpen_lt continuous_const π.continuous
      have hin : (interior (halfSpace (d+1))).Nonempty := by
        refine ⟨WithLp.toLp 2 (fun _ => (1 : ℝ)), ?_⟩
        apply interior_mono (s := {u : E (d+1) | 0 < π u})
          (t := halfSpace (d+1))
          (fun u hu => (show 0 ≤ π u from le_of_lt hu))
        rw [hpos.interior_eq]
        exact (show (0 : ℝ) < 1 from zero_lt_one)
      exact uniqueDiffOn_convex hconv hin

namespace EmbeddedChart
variable {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}

theorem source_uniqueDiff (c : EmbeddedChart r k n M) : UniqueDiffOn ℝ c.source := by
  obtain ⟨W, hW, he⟩ := c.source_open
  rw [he]
  exact (parameterSpace_uniqueDiff k c.half).inter hW

theorem overlap_uniqueDiff (c d : EmbeddedChart r k n M) :
    UniqueDiffOn ℝ (chartOverlap c d) := by
  obtain ⟨W, hW, he⟩ := (EmbeddedChart.overlap_relatively_open c) d
  rw [he]
  exact (EmbeddedChart.source_uniqueDiff c).inter hW

end EmbeddedChart

theorem chart_transition_derivatives :
    Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.chart_transition_derivativesType := by
  intro r k n M c d hr hkn u hu
  have hv := (EmbeddedChart.transition_mem c) d hu
  have hn : r ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hr.1)
  have hF := ((chart_transition_regular c d hr hkn).1.differentiableOn hn) u hu
  have hG := ((chart_transition_regular d c hr hkn).1.differentiableOn hn)
    (chartTransition c d u) hv
  let A := fderivWithin ℝ (chartTransition c d) (chartOverlap c d) u
  let B := fderivWithin ℝ (chartTransition d c) (chartOverlap d c) (chartTransition c d u)
  have hA : HasFDerivWithinAt (chartTransition c d) A (chartOverlap c d) u :=
    hF.hasFDerivWithinAt
  have hB : HasFDerivWithinAt (chartTransition d c) B (chartOverlap d c)
      (chartTransition c d u) := hG.hasFDerivWithinAt
  have hBA : B.comp A = ContinuousLinearMap.id ℝ (E k) := by
    apply ((EmbeddedChart.overlap_uniqueDiff c) d u hu).eq
      (hB.comp u hA (fun v hv => (EmbeddedChart.transition_mem c) d hv))
    exact (hasFDerivWithinAt_id _ _).congr'
      (fun v hv => (EmbeddedChart.transition_left_inv c) d hv) hu
  have hAB : A.comp B = ContinuousLinearMap.id ℝ (E k) := by
    apply ((EmbeddedChart.overlap_uniqueDiff d) c _ hv).eq
    · have hA' : HasFDerivWithinAt (chartTransition c d) A (chartOverlap c d)
          (chartTransition d c (chartTransition c d u)) := by
        simpa only [(EmbeddedChart.transition_left_inv c) d hu] using hA
      exact hA'.comp _ hB (fun v hv => (EmbeddedChart.transition_mem d) c hv)
    · exact (hasFDerivWithinAt_id _ _).congr'
        (fun v hv => (EmbeddedChart.transition_left_inv d) c hv) hv
  exact ⟨ContinuousLinearEquiv.equivOfInverse' A B hAB hBA, hA, hB⟩

namespace EmbeddedChart
variable {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}

theorem source_subset_parameterSpace (c : EmbeddedChart r k n M) :
    c.source ⊆ parameterSpace k c.half := by
  obtain ⟨W, _, he⟩ := c.source_open
  rw [he]
  exact inter_subset_left

theorem source_mem_nhds (c : EmbeddedChart r k n M) {u : E k}
    (hu : u ∈ c.source) (h : ¬ IsBoundaryParameter c u) : c.source ∈ 𝓝 u := by
  obtain ⟨W, hW, he⟩ := c.source_open
  have huW : u ∈ W := (he ▸ hu).2
  rw [he]
  apply inter_mem _ (hW.mem_nhds huW)
  cases hc : c.half with
  | false => exact Filter.univ_mem
  | true =>
    cases k with
    | zero => exact False.elim (Nat.lt_irrefl 0 (c.half_pos hc))
    | succ d =>
      have hu0 : 0 ≤ u (Fin.last d) := by
        have hp := (he ▸ hu).1
        rw [hc] at hp
        exact hp
      have hne : u (Fin.last d) ≠ 0 := fun hz => h ⟨hc, hz⟩
      have hpos := lt_of_le_of_ne hu0 (Ne.symm hne)
      have hopen : IsOpen {v : E (d+1) | 0 < v (Fin.last d)} :=
        isOpen_lt continuous_const (EuclideanSpace.proj (Fin.last d)).continuous
      exact mem_of_superset (hopen.mem_nhds hpos)
        (fun _ hv => (show (0 : ℝ) ≤ _ from le_of_lt hv))

theorem overlap_mem_nhds (c d : EmbeddedChart r k n M) {u : E k}
    (hu : u ∈ chartOverlap c d) (hi : ¬ IsBoundaryParameter c u) :
    chartOverlap c d ∈ 𝓝 u := by
  obtain ⟨W, hW, he⟩ := overlap_relatively_open c d
  rw [he]
  exact inter_mem (source_mem_nhds c hu.1 hi) (hW.mem_nhds ((he ▸ hu).2))

/-- A local minimum of the last transition coordinate rules out sending an
interior point to a flat-boundary point: its derivative would fail surjectivity. -/
theorem transition_not_boundary (c d : EmbeddedChart r k n M)
    (hr : ManifoldRegularity r) (hkn : k ≤ n) {u : E k}
    (hu : u ∈ chartOverlap c d) (hi : ¬ IsBoundaryParameter c u) :
    ¬ IsBoundaryParameter d (chartTransition c d u) := by
  intro hb
  obtain ⟨A, hA, _⟩ := chart_transition_derivatives c d hr hkn u hu
  have hnhds := overlap_mem_nhds c d hu hi
  cases k with
  | zero => exact Nat.lt_irrefl 0 (d.half_pos hb.1)
  | succ e =>
    let π : E (e+1) →L[ℝ] ℝ := EuclideanSpace.proj (Fin.last e)
    have hmin : IsLocalMin (π ∘ chartTransition c d) u := by
      apply Filter.eventually_of_mem hnhds
      intro v hv
      have hv' := source_subset_parameterSpace d (transition_mem c d hv).1
      have hzero : π (chartTransition c d u) = 0 := hb.2
      change π (chartTransition c d u) ≤ π (chartTransition c d v)
      rw [hzero]
      rw [hb.1] at hv'
      exact hv'
    have hder := π.hasFDerivAt.comp u (hA.hasFDerivAt hnhds)
    have hzero := hmin.hasFDerivAt_eq_zero hder
    have hval := DFunLike.congr_fun hzero (A.symm (WithLp.toLp 2 (fun _ => (1 : ℝ))))
    have : (1 : ℝ) = 0 := by simpa [π] using hval
    exact one_ne_zero this

end EmbeddedChart

theorem chart_transition_boundary :
    Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.chart_transition_boundaryType := by
  intro r k n M c d hr hkn u hu
  constructor
  · intro hc
    by_contra hd
    have hh := EmbeddedChart.transition_not_boundary d c hr hkn
      (EmbeddedChart.transition_mem c d hu) hd
    rw [EmbeddedChart.transition_left_inv c d hu] at hh
    exact hh hc
  · exact fun hd => Classical.byContradiction
      (fun hc => EmbeddedChart.transition_not_boundary c d hr hkn hu hc hd)

theorem chart_intrinsicBoundary :
    Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.chart_intrinsicBoundaryType := by
  intro r k n M c hr hkn u hu
  constructor
  · rintro ⟨hxM, d, v, hd, hv, hvflat, hdx⟩
    have huover : u ∈ chartOverlap c d :=
      ⟨hu, by change c.toFun u ∈ d.ambient; rw [← hdx]; exact (d.map_source hv).2⟩
    apply (chart_transition_boundary c d hr hkn u huover).mpr
    have heq : chartTransition c d u = v := by
      change d.invFun (c.toFun u) = v
      rw [← hdx, d.left_inv v hv]
    change IsBoundaryParameter d (chartTransition c d u)
    rw [heq]
    exact ⟨hd, hvflat⟩
  · rintro ⟨hc, hflat⟩
    exact ⟨(c.map_source hu).1, c, u, hc, hu, hflat, rfl⟩

namespace EmbeddedChart
variable {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}

/-- Every inward vector is a positive tangent direction on the overlap. -/
theorem inward_mem_posTangentCone (c d : EmbeddedChart r k n M)
    {u w : E k} (hu : u ∈ chartOverlap c d) (hw : w ∈ inwardParameterCone c u) :
    w ∈ posTangentConeAt (chartOverlap c d) u := by
  classical
  by_cases hb : IsBoundaryParameter c u
  · obtain ⟨W, hW, he⟩ := overlap_relatively_open c d
    obtain ⟨Z, hZ, hcZ⟩ := c.source_open
    have huW := (he ▸ hu).2
    have huZ := (hcZ ▸ hu.1).2
    change w ∈ tangentConeAt ℝ≥0 (chartOverlap c d) u
    rw [he, tangentConeAt_inter_nhds (hW.mem_nhds huW), hcZ,
      tangentConeAt_inter_nhds (hZ.mem_nhds huZ), hb.1]
    cases k with
    | zero => exact False.elim (Nat.lt_irrefl 0 (c.half_pos hb.1))
    | succ e =>
      have hwu : 0 ≤ w (Fin.last e) := by
        change w ∈ (if IsBoundaryParameter c u then halfSpace (e+1) else univ) at hw
        rw [if_pos hb] at hw
        exact hw
      have huc : 0 ≤ u (Fin.last e) := le_of_eq hb.2.symm
      have hsum : u + w ∈ halfSpace (e+1) := add_nonneg huc hwu
      have hconv : Convex ℝ (halfSpace (e+1)) :=
        (convex_Ici (0 : ℝ)).linear_preimage
          (EuclideanSpace.proj (Fin.last e)).toLinearMap
      exact mem_posTangentConeAt_of_segment_subset (hconv.segment_subset huc hsum)
  · change w ∈ tangentConeAt ℝ≥0 (chartOverlap c d) u
    rw [tangentConeAt_of_mem_nhds (𝕜 := ℝ≥0) (overlap_mem_nhds c d hu hb)]
    trivial

theorem transition_maps_inward (c d : EmbeddedChart r k n M)
    (hr : ManifoldRegularity r) (hkn : k ≤ n) {u : E k}
    (hu : u ∈ chartOverlap c d) {A : E k →L[ℝ] E k}
    (hA : HasFDerivWithinAt (chartTransition c d) A (chartOverlap c d) u) :
    MapsTo A (inwardParameterCone c u) (inwardParameterCone d (chartTransition c d u)) := by
  classical
  intro w hw
  by_cases hb : IsBoundaryParameter d (chartTransition c d u)
  · cases k with
    | zero => exact False.elim (Nat.lt_irrefl 0 (d.half_pos hb.1))
    | succ e =>
      let π : E (e+1) →L[ℝ] ℝ := EuclideanSpace.proj (Fin.last e)
      have hmin : IsLocalMinOn (π ∘ chartTransition c d) (chartOverlap c d) u := by
        apply Filter.eventually_of_mem self_mem_nhdsWithin
        intro v hv
        change π (chartTransition c d u) ≤ π (chartTransition c d v)
        rw [show π (chartTransition c d u) = 0 from hb.2]
        have hp := source_subset_parameterSpace d (transition_mem c d hv).1
        rw [hb.1] at hp
        exact hp
      have hpos := hmin.hasFDerivWithinAt_nonneg
        (π.hasFDerivAt.comp_hasFDerivWithinAt u hA) (inward_mem_posTangentCone c d hu hw)
      change A w ∈ (if IsBoundaryParameter d (chartTransition c d u)
        then halfSpace (e+1) else univ)
      rw [if_pos hb]
      exact hpos
  · change A w ∈ (if IsBoundaryParameter d (chartTransition c d u) then halfSpace k else univ)
    rw [if_neg hb]
    trivial

end EmbeddedChart

theorem chart_transition_cones :
    Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.chart_transition_conesType := by
  intro r k n M c d hr hkn u hu A hA
  classical
  obtain ⟨B, hB, hBi⟩ := chart_transition_derivatives c d hr hkn u hu
  have heq : A.toContinuousLinearMap = B.toContinuousLinearMap :=
    (EmbeddedChart.overlap_uniqueDiff c d u hu).eq hA hB
  have hAB : A = B := by
    apply DFunLike.ext
    intro v
    exact DFunLike.congr_fun heq v
  subst B
  have hv := EmbeddedChart.transition_mem c d hu
  have hmaps := EmbeddedChart.transition_maps_inward c d hr hkn hu hA
  have hmapinv := EmbeddedChart.transition_maps_inward d c hr hkn hv hBi
  rw [EmbeddedChart.transition_left_inv c d hu] at hmapinv
  have hcone : A '' inwardParameterCone c u = inwardParameterCone d (chartTransition c d u) := by
    apply Subset.antisymm hmaps.image_subset
    intro w hw
    exact ⟨A.symm w, hmapinv hw, A.apply_symm_apply w⟩
  refine ⟨hcone, ?_⟩
  intro hb
  have hb' := (chart_transition_boundary c d hr hkn u hu).mp hb
  have hcones : A '' halfSpace k = halfSpace k := by
    change A '' (if IsBoundaryParameter c u then halfSpace k else univ) =
      (if IsBoundaryParameter d (chartTransition c d u) then halfSpace k else univ) at hcone
    simpa only [if_pos hb, if_pos hb'] using hcone
  cases k with
  | zero => exact False.elim (Nat.lt_irrefl 0 (c.half_pos hb.1))
  | succ e =>
    have hflat : ∀ v : E (e+1), v ∈ flatBoundary (e+1) ↔
        v ∈ halfSpace (e+1) ∧ -v ∈ halfSpace (e+1) := by
      intro v
      change v (Fin.last e) = 0 ↔ 0 ≤ v (Fin.last e) ∧ 0 ≤ -v (Fin.last e)
      constructor
      · intro hv; simp [hv]
      · rintro ⟨h1,h2⟩; exact le_antisymm (neg_nonneg.mp h2) h1
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [hflat] at hv ⊢
      exact ⟨hcones ▸ mem_image_of_mem A hv.1,
        by rw [← map_neg]; exact hcones ▸ mem_image_of_mem A hv.2⟩
    · intro hw
      have hwi := (hflat w).mp hw
      have hm : MapsTo A.symm (halfSpace (e+1)) (halfSpace (e+1)) := by
        intro z hz
        obtain ⟨v,hv,hvz⟩ := hcones.symm ▸ hz
        rw [← hvz, A.symm_apply_apply]
        exact hv
      refine ⟨A.symm w, (hflat _).mpr ⟨hm hwi.1, ?_⟩, A.apply_symm_apply w⟩
      rw [← map_neg]
      exact hm hwi.2

namespace EmbeddedChart
variable {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}

/-- An open Euclidean chart has image disjoint from the intrinsic boundary. -/
def interiorChart (c : EmbeddedChart r k n M) (hr : ManifoldRegularity r)
    (hkn : k ≤ n) (hc : c.half = false) :
    EmbeddedChart r k n (M \ intrinsicBoundary r k M) where
  half := c.half
  half_pos := c.half_pos
  source := c.source
  source_open := c.source_open
  ambient := c.ambient
  ambient_open := c.ambient_open
  toFun := c.toFun
  invFun := c.invFun
  map_source := by
    intro u hu
    refine ⟨⟨(c.map_source hu).1, ?_⟩, (c.map_source hu).2⟩
    intro hb
    have hp := (chart_intrinsicBoundary c hr hkn u hu).mp hb
    have : false = true := hc.symm.trans hp.1
    cases this
  map_target := fun _ hx => c.map_target ⟨hx.1.1, hx.2⟩
  left_inv := c.left_inv
  right_inv := fun _ hx => c.right_inv _ ⟨hx.1.1, hx.2⟩
  continuous_toFun := c.continuous_toFun
  continuous_invFun := c.continuous_invFun.mono (fun _ hx => ⟨hx.1.1, hx.2⟩)
  regular := c.regular

end EmbeddedChart

theorem intrinsic_interior_manifold :
    Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.intrinsic_interior_manifoldType := by
  intro r k n M hM
  obtain ⟨hr, hkn, hcharts⟩ := hM
  refine ⟨hr, hkn, ?_⟩
  intro x hx
  obtain ⟨c, u, hu, hux⟩ := hcharts x hx.1
  have hc : c.half = false := by
    cases he : c.half with
    | false => rfl
    | true =>
      have hb : c.toFun u ∈ intrinsicBoundary r k M :=
        (chart_intrinsicBoundary c hr hkn u hu.1).mpr ⟨he, hu.2 he⟩
      exact False.elim (hx.2 (hux ▸ hb))
  exact ⟨EmbeddedChart.interiorChart c hr hkn hc, u, hc, hu.1, hux⟩

/-- Inclusion of the flat face in the last-coordinate half-space model. -/
def flatInclusion (d : ℕ) : E d →L[ℝ] E (d+1) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (Fin.snoc (fun i => v i) 0)
      map_add' := by
        intro v w
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      map_smul' := by
        intro a v
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp }

def flatProjection (d : ℕ) : E (d+1) →L[ℝ] E d :=
  coordinateProjection ⟨Fin.castSucc, Fin.castSucc_injective d⟩

@[simp] theorem flatInclusion_castSucc (d : ℕ) (v : E d) (i : Fin d) :
    flatInclusion d v i.castSucc = v i := by simp [flatInclusion]

@[simp] theorem flatInclusion_last (d : ℕ) (v : E d) :
    flatInclusion d v (Fin.last d) = 0 := by simp [flatInclusion]

@[simp] theorem flatProjection_apply (d : ℕ) (v : E (d+1)) (i : Fin d) :
    flatProjection d v i = v i.castSucc := rfl

@[simp] theorem flatProjection_inclusion (d : ℕ) (v : E d) :
    flatProjection d (flatInclusion d v) = v := by ext i; simp

theorem flatInclusion_projection (d : ℕ) (v : E (d+1))
    (hv : v ∈ flatBoundary (d+1)) : flatInclusion d (flatProjection d v) = v := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using hv.symm
  · simp

theorem flatInclusion_injective (d : ℕ) : Function.Injective (flatInclusion d) := by
  intro v w h
  have := congrArg (flatProjection d) h
  simpa only [flatProjection_inclusion] using this

namespace EmbeddedChart
variable {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}

/-- Restriction of a boundary chart to its flat face, now parametrized by E d. -/
def boundaryChart (c : EmbeddedChart r (d+1) n M) (hr : ManifoldRegularity r)
    (hkn : d+1 ≤ n) (hc : c.half = true) :
    EmbeddedChart r d n (intrinsicBoundary r (d+1) M) where
  half := false
  half_pos := by simp
  source := flatInclusion d ⁻¹' c.source
  source_open := by
    obtain ⟨W, hW, he⟩ := c.source_open
    refine ⟨flatInclusion d ⁻¹' W, hW.preimage (flatInclusion d).continuous, ?_⟩
    ext v
    change flatInclusion d v ∈ c.source ↔ v ∈ univ ∩ flatInclusion d ⁻¹' W
    rw [he, hc]
    simp only [mem_inter_iff, mem_preimage, mem_univ, true_and]
    exact and_iff_right (show flatInclusion d v ∈ parameterSpace (d+1) true from
      le_of_eq (flatInclusion_last d v).symm)
  ambient := c.ambient
  ambient_open := c.ambient_open
  toFun := c.toFun ∘ flatInclusion d
  invFun := flatProjection d ∘ c.invFun
  map_source := by
    intro v hv
    refine ⟨(chart_intrinsicBoundary c hr hkn _ hv).mpr ⟨hc, ?_⟩,
      (c.map_source hv).2⟩
    exact flatInclusion_last d v
  map_target := by
    intro x hx
    have hxM : x ∈ M ∩ c.ambient := ⟨hx.1.1, hx.2⟩
    have hv := c.map_target hxM
    have hb : c.invFun x ∈ flatBoundary (d+1) := by
      apply ((chart_intrinsicBoundary c hr hkn _ hv).mp ?_).2
      rw [c.right_inv x hxM]
      exact hx.1
    change flatInclusion d (flatProjection d (c.invFun x)) ∈ c.source
    rw [flatInclusion_projection d _ hb]
    exact hv
  left_inv := by
    intro v hv
    change flatProjection d (c.invFun (c.toFun (flatInclusion d v))) = v
    rw [c.left_inv _ hv, flatProjection_inclusion]
  right_inv := by
    intro x hx
    have hxM : x ∈ M ∩ c.ambient := ⟨hx.1.1, hx.2⟩
    have hv := c.map_target hxM
    have hb : c.invFun x ∈ flatBoundary (d+1) := by
      apply ((chart_intrinsicBoundary c hr hkn _ hv).mp ?_).2
      rw [c.right_inv x hxM]
      exact hx.1
    change c.toFun (flatInclusion d (flatProjection d (c.invFun x))) = x
    rw [flatInclusion_projection d _ hb, c.right_inv x hxM]
  continuous_toFun := c.continuous_toFun.comp (flatInclusion d).continuous.continuousOn
    (fun _ hv => hv)
  continuous_invFun := (flatProjection d).continuous.comp_continuousOn
    (c.continuous_invFun.mono (fun _ hx => ⟨hx.1.1, hx.2⟩))
  regular := by
    intro v hv
    obtain ⟨W, g, hW, hvW, he, hg, hgrank⟩ := c.regular (flatInclusion d v) hv
    refine ⟨flatInclusion d ⁻¹' W, g ∘ flatInclusion d,
      hW.preimage (flatInclusion d).continuous, hvW, ?_, ?_, ?_⟩
    · intro w hw
      exact he ⟨hw.1, hw.2⟩
    · exact hg.comp (flatInclusion d).contDiff.contDiffOn (fun _ hw => hw)
    · intro w hw
      have hgd : DifferentiableAt ℝ g (flatInclusion d w) :=
        (hg.contDiffAt (hW.mem_nhds hw)).differentiableAt
          (ne_of_gt (lt_of_lt_of_le zero_lt_one hr.1))
      rw [fderiv_comp w hgd (flatInclusion d).differentiableAt,
        ContinuousLinearMap.fderiv]
      exact (hgrank _ hw).comp (flatInclusion_injective d)

end EmbeddedChart

theorem intrinsic_boundary_manifold :
    Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.intrinsic_boundary_manifoldType := by
  intro r d n M hM
  obtain ⟨hr, hkn, _⟩ := hM
  refine ⟨hr, (Nat.le_succ d).trans hkn, ?_⟩
  intro x hx
  obtain ⟨hxM, c, u, hc, hu, huflat, hux⟩ := hx
  let b := EmbeddedChart.boundaryChart c hr hkn hc
  have hp : flatInclusion d (flatProjection d u) = u := flatInclusion_projection d u huflat
  refine ⟨b, flatProjection d u, rfl, ?_, ?_⟩
  · change flatInclusion d (flatProjection d u) ∈ c.source
    rwa [hp]
  · change c.toFun (flatInclusion d (flatProjection d u)) = x
    rwa [hp]

/-- The coordinate formula for the cone agrees with the positive tangent-cone
definition, rather than merely naming a half-space 'inward'. -/
theorem inwardParameterCone_eq_posTangentCone :
    Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.inwardParameterCone_eq_posTangentConeType := by
  intro r k n M c d u hu
  classical
  apply Subset.antisymm (fun _ hw => EmbeddedChart.inward_mem_posTangentCone c d hu hw)
  intro w hw
  by_cases hb : IsBoundaryParameter c u
  · cases k with
    | zero => exact False.elim (Nat.lt_irrefl 0 (c.half_pos hb.1))
    | succ e =>
      let π : E (e+1) →L[ℝ] ℝ := EuclideanSpace.proj (Fin.last e)
      have hmin : IsLocalMinOn π (chartOverlap c d) u := by
        apply Filter.eventually_of_mem self_mem_nhdsWithin
        intro v hv
        change π u ≤ π v
        rw [show π u = 0 from hb.2]
        have hp := EmbeddedChart.source_subset_parameterSpace c hv.1
        rw [hb.1] at hp
        exact hp
      have hpos := hmin.hasFDerivWithinAt_nonneg π.hasFDerivAt.hasFDerivWithinAt hw
      change w ∈ (if IsBoundaryParameter c u then halfSpace (e+1) else univ)
      rw [if_pos hb]
      exact hpos
  · change w ∈ (if IsBoundaryParameter c u then halfSpace k else univ)
    rw [if_neg hb]
    trivial

/-- Open-chart and empty-intrinsic-boundary formulations coincide for the
original embedded-manifold representation. -/
theorem boundaryless_iff : Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.boundaryless_iffType := by
  intro r k n M
  constructor
  · rintro ⟨hr, hkn, hcharts⟩
    refine ⟨⟨hr, hkn, ?_⟩, ?_⟩
    · intro x hx
      obtain ⟨c,u,hc,hu,hux⟩ := hcharts x hx
      exact ⟨c,u,⟨hu, fun he => False.elim (Bool.false_ne_true (hc.symm.trans he))⟩, hux⟩
    · apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨c,u,hc,hu,hux⟩ := hcharts x hx.1
      have hb : IsBoundaryParameter c u :=
        (chart_intrinsicBoundary c hr hkn u hu).mp (hux.symm ▸ hx)
      exact Bool.false_ne_true (hc.symm.trans hb.1)
  · rintro ⟨⟨hr,hkn,hcharts⟩, hboundary⟩
    refine ⟨hr,hkn,?_⟩
    intro x hx
    obtain ⟨c,u,hu,hux⟩ := hcharts x hx
    have hc : c.half = false := by
      cases he : c.half with
      | false => rfl
      | true =>
        have hb := (chart_intrinsicBoundary c hr hkn u hu.1).mpr ⟨he, hu.2 he⟩
        rw [hboundary] at hb
        exact False.elim hb
    exact ⟨c,u,hc,hu.1,hux⟩

end D04



