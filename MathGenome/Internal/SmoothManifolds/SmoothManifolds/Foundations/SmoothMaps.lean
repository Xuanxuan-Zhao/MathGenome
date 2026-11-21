import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Atlases
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.SmoothMaps
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Order.Filter.AtTopBot.Ring
import Mathlib.Tactic.NormNum

namespace SmoothManifolds
open Set Filter
open scoped Topology ContDiff
universe u v w

abbrev LocalCoordinateExtension := @MapData.LocalCoordinateExtension
abbrev ChartContDiffAt := @MapData.ChartContDiffAt
abbrev ManifoldContDiffAt := @MapData.ManifoldContDiffAt
abbrev ManifoldContDiffOn := @MapData.ManifoldContDiffOn
abbrev ManifoldContDiff := @MapData.ManifoldContDiff
abbrev ManifoldSmoothAt := @MapData.ManifoldSmoothAt
abbrev ManifoldSmoothOn := @MapData.ManifoldSmoothOn
abbrev ManifoldSmooth := @MapData.ManifoldSmooth
abbrev LocalChartTestOn := @MapData.LocalChartTestOn
abbrev ContDiffDiffeomorph := @MapData.ContDiffDiffeomorph
abbrev Diffeomorph := @MapData.Diffeomorph
abbrev transportAtlas := @MapData.transportAtlas
abbrev ManifoldContDiffToEuclideanAt := @MapData.ManifoldContDiffToEuclideanAt
abbrev LocallyContDiffOnSubset := @MapData.LocallyContDiffOnSubset
abbrev LocallySmoothOnSubset := @MapData.LocallySmoothOnSubset
abbrev LocallyContDiffOnSubsetToManifold := @MapData.LocallyContDiffOnSubsetToManifold
abbrev LocallySmoothOnSubsetToManifold := @MapData.LocallySmoothOnSubsetToManifold
abbrev IsSmoothMap := @MapData.IsSmoothMap

noncomputable abbrev openSubsetAtlas := @MapData.openSubsetAtlas
namespace ContDiffDiffeomorph
abbrev toHomeomorph {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N] {r : ℕ∞}
    {A : Set (ModelChart n a M)} {B : Set (ModelChart m b N)}
    (h : ContDiffDiffeomorph r A B) : M ≃ₜ N :=
  MapData.ContDiffDiffeomorph.toHomeomorph h
end ContDiffDiffeomorph

namespace LocalCoordinateExtension
variable {X : Type u} [TopologicalSpace X] {n m l : ℕ} {r q : ℕ∞}
  {ι : X → Euclidean n} {f : X → Euclidean m} {g : X → Euclidean l} {x : X}

theorem self (r : ℕ∞) (ι : X → Euclidean n) (x : X) :
    LocalCoordinateExtension r ι ι x :=
  ⟨univ, isOpen_univ, mem_univ _, id, contDiffOn_id, Eventually.of_forall (fun _ => rfl)⟩

theorem congr (h : LocalCoordinateExtension r ι f x) {g : X → Euclidean m}
    (heq : f =ᶠ[𝓝 x] g) : LocalCoordinateExtension r ι g x := by
  obtain ⟨U, hU, hx, F, hF, he⟩ := h
  exact ⟨U, hU, hx, F, hF, he.trans heq⟩

theorem of_le (h : LocalCoordinateExtension r ι f x) (hqr : q ≤ r) :
    LocalCoordinateExtension q ι f x := by
  obtain ⟨U, hU, hx, F, hF, he⟩ := h
  refine ⟨U, hU, hx, F, hF.of_le ?_, he⟩
  exact_mod_cast hqr

/-- Compose ambient extensions on U ∩ F⁻¹(V); this also works at order zero. -/
theorem comp (hg : LocalCoordinateExtension r f g x)
    (hf : LocalCoordinateExtension r ι f x) : LocalCoordinateExtension r ι g x := by
  obtain ⟨U, hU, hxU, F, hF, heF⟩ := hf
  obtain ⟨V, hV, hxV, G, hG, heG⟩ := hg
  refine ⟨U ∩ F ⁻¹' V, hF.continuousOn.isOpen_inter_preimage hU hV,
    ⟨hxU, ?_⟩, G ∘ F,
    hG.comp (hF.mono inter_subset_left) (fun _ hy => hy.2), ?_⟩
  · change F (ι x) ∈ V
    rw [heF.eq_of_nhds]
    exact hxV
  · exact (heF.fun_comp G).trans heG

/-- Pull a germ back along a continuous map of source spaces. -/
theorem precomp {Y : Type v} [TopologicalSpace Y] {p : Y} {h : Y → X}
    (hf : LocalCoordinateExtension r ι f x) (hh : ContinuousAt h p) (hp : h p = x) :
    LocalCoordinateExtension r (ι ∘ h) (f ∘ h) p := by
  subst x
  obtain ⟨U, hU, hx, F, hF, he⟩ := hf
  exact ⟨U, hU, hx, F, hF, he.comp_tendsto hh⟩

/-- One representing extension works at every sufficiently nearby point. -/
theorem eventually (hf : LocalCoordinateExtension r ι f x) (hι : ContinuousAt ι x) :
    ∀ᶠ y in 𝓝 x, LocalCoordinateExtension r ι f y := by
  obtain ⟨U, hU, hx, F, hF, he⟩ := hf
  obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp he
  filter_upwards [hι.preimage_mem_nhds (hU.mem_nhds hx), hVopen.mem_nhds hxV] with y hyU hyV
  exact ⟨U, hU, hyU, F, hF,
    Filter.mem_of_superset (hVopen.mem_nhds hyV) (fun z hz => hVsub hz)⟩
end LocalCoordinateExtension

section Maps
variable {n m l : ℕ} {a b c : ModelKind}
  {M : Type u} {N : Type v} {P : Type w}
  [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]

/-- The upstream transition extension gives the same germ in the manifold. -/
theorem chartContDiffAt_of_compatible {r : ℕ∞} {e d : ModelChart n a M}
    (h : ContDiffCompatible r e d) {x : M} (hx : x ∈ e.source) (hxd : x ∈ d.source) :
    ChartContDiffAt r e d id x := by
  have hxt : e x ∈ (e.symm.trans d).source := by
    simp only [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage]
    exact ⟨e.map_source hx, by simpa only [e.left_inv hx] using hxd⟩
  obtain ⟨U, hU, hxU, F, hF, heq⟩ := h.1 (e x) hxt
  refine ⟨U, hU, hxU, F, hF, ?_⟩
  filter_upwards [e.open_source.mem_nhds hx, d.open_source.mem_nhds hxd,
    ((continuous_subtype_val.continuousAt.comp (e.continuousAt hx)).preimage_mem_nhds
      (hU.mem_nhds hxU))] with y hye hyd hyU
  have hyt : e y ∈ (e.symm.trans d).source := by
    simp only [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage]
    exact ⟨e.map_source hye, by simpa only [e.left_inv hye] using hyd⟩
  have := heq (e y) hyt hyU
  simpa only [OpenPartialHomeomorph.trans_apply, e.left_inv hye, id_eq] using this

/-- Pre- and post-composition by coordinate transitions proves chart independence. -/
theorem chartContDiffAt_changeCharts {r : ℕ∞}
    {e e' : ModelChart n a M} {d d' : ModelChart m b N}
    {f : M → N} {x : M} (hf : ContinuousAt f x)
    (he : ContDiffCompatible r e' e) (hd : ContDiffCompatible r d d')
    (hx : x ∈ e.source) (hx' : x ∈ e'.source)
    (hfx : f x ∈ d.source) (hfx' : f x ∈ d'.source)
    (h : ChartContDiffAt r e d f x) : ChartContDiffAt r e' d' f x := by
  have hsource := chartContDiffAt_of_compatible he hx' hx
  have htarget := LocalCoordinateExtension.precomp
    (chartContDiffAt_of_compatible hd hfx hfx') hf rfl
  exact LocalCoordinateExtension.comp htarget (LocalCoordinateExtension.comp h hsource)

theorem manifoldContDiffAt_iff_oneChart
    (r : ℕ∞) (A : Set (ModelChart n a M)) (B : Set (ModelChart m b N))
    (hA : IsContDiffAtlas r A) (hB : IsContDiffAtlas r B) (f : M → N) (x : M) :
    ManifoldContDiffAt r A B f x ↔
      ContinuousAt f x ∧ ∃ e ∈ A, ∃ d ∈ B,
        x ∈ e.source ∧ f x ∈ d.source ∧ ChartContDiffAt r e d f x := by
  constructor
  · intro h
    obtain ⟨e, he, hx⟩ := hA.1 x
    obtain ⟨d, hd, hfx⟩ := hB.1 (f x)
    exact ⟨h.1, e, he, d, hd, hx, hfx, h.2 e he d hd hx hfx⟩
  · rintro ⟨hf, e, he, d, hd, hx, hfx, h⟩
    refine ⟨hf, ?_⟩
    intro e' he' d' hd' hx' hfx'
    exact chartContDiffAt_changeCharts hf (hA.2 e' he' e he) (hB.2 d hd d' hd')
      hx hx' hfx hfx' h


theorem manifoldContDiffOn_mono (r : ℕ∞)
    (A : Set (ModelChart n a M)) (B : Set (ModelChart m b N))
    (f : M → N) (s t : Set M) (h : ManifoldContDiffOn r A B f t) (hst : s ⊆ t) :
    ManifoldContDiffOn r A B f s := fun x hx => h x (hst hx)

theorem manifoldContDiffOn_glue (r : ℕ∞)
    (A : Set (ModelChart n a M)) (B : Set (ModelChart m b N))
    (f : M → N) (s : Set M) {ι : Type*} (U : ι → Set M)
    (_hU : ∀ i, IsOpen (U i)) (hs : s ⊆ ⋃ i, U i)
    (h : ∀ i, ManifoldContDiffOn r A B f (s ∩ U i)) :
    ManifoldContDiffOn r A B f s ∧ ContinuousOn f s := by
  have hf : ManifoldContDiffOn r A B f s := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hs hx)
    exact h i x ⟨hx, hi⟩
  exact ⟨hf, fun x hx => (hf x hx).1.continuousWithinAt⟩

/-- Germ equality is enough to transfer all the coordinate tests and continuity. -/
theorem manifoldContDiffAt_congr {r : ℕ∞}
    {A : Set (ModelChart n a M)} {B : Set (ModelChart m b N)}
    {f g : M → N} {x : M} (hf : ManifoldContDiffAt r A B f x)
    (heq : f =ᶠ[𝓝 x] g) : ManifoldContDiffAt r A B g x := by
  have hx : f x = g x := heq.eq_of_nhds
  refine ⟨hf.1.congr heq, ?_⟩
  intro e he d hd hxe hxd
  exact LocalCoordinateExtension.congr
    (hf.2 e he d hd hxe (by simpa only [hx] using hxd))
    (heq.fun_comp (fun z => (d z).val))

theorem manifoldContDiffOn_of_local_eq (r : ℕ∞)
    (A : Set (ModelChart n a M)) (B : Set (ModelChart m b N))
    (f : M → N) (s : Set M)
    (h : ∀ x ∈ s, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ g : M → N, EqOn f g U ∧ ManifoldContDiffOn r A B g U) :
    ManifoldContDiffOn r A B f s ∧ ContinuousOn f s := by
  have hf : ManifoldContDiffOn r A B f s := by
    intro x hx
    obtain ⟨U, hU, hxU, g, heq, hg⟩ := h x hx
    exact manifoldContDiffAt_congr (hg x hxU)
      (Filter.mem_of_superset (hU.mem_nhds hxU) (fun y hy => (heq hy).symm))
  exact ⟨hf, fun x hx => (hf x hx).1.continuousWithinAt⟩

theorem manifoldContDiffAt_comp {r : ℕ∞}
    {A : Set (ModelChart n a M)} {B : Set (ModelChart m b N)}
    {C : Set (ModelChart l c P)} (hB : IsAtlas B) {f : M → N} {g : N → P} {x : M}
    (hf : ManifoldContDiffAt r A B f x) (hg : ManifoldContDiffAt r B C g (f x)) :
    ManifoldContDiffAt r A C (g ∘ f) x := by
  refine ⟨hg.1.comp hf.1, ?_⟩
  intro e he d hd hx hfx
  obtain ⟨j, hj, hxj⟩ := hB (f x)
  have ht : LocalCoordinateExtension r (fun y => (j (f y)).val)
      (fun y => (d (g (f y))).val) x :=
    LocalCoordinateExtension.precomp (ι := fun z : N => (j z).val)
      (f := fun z : N => (d (g z)).val) (hg.2 j hj d hd hxj hfx) hf.1 rfl
  exact LocalCoordinateExtension.comp ht (hf.2 e he j hj hx hxj)

theorem manifoldContDiff_comp (r : ℕ∞)
    (A : Set (ModelChart n a M)) (B : Set (ModelChart m b N))
    (C : Set (ModelChart l c P)) (hB : IsAtlas B) (f : M → N) (g : N → P)
    (hf : ManifoldContDiff r A B f) (hg : ManifoldContDiff r B C g) :
    ManifoldContDiff r A C (g ∘ f) :=
  fun x => manifoldContDiffAt_comp hB (hf x) (hg (f x))

theorem manifoldContDiffOn_comp (r : ℕ∞)
    (A : Set (ModelChart n a M)) (B : Set (ModelChart m b N))
    (C : Set (ModelChart l c P)) (hB : IsAtlas B)
    (f : M → N) (g : N → P) (s : Set M) (t : Set N)
    (_hs : IsOpen s) (_ht : IsOpen t) (hst : MapsTo f s t)
    (hf : ManifoldContDiffOn r A B f s) (hg : ManifoldContDiffOn r B C g t) :
    ManifoldContDiffOn r A C (g ∘ f) s :=
  fun x hx => manifoldContDiffAt_comp hB (hf x hx) (hg (f x) (hst hx))

theorem manifoldContDiff_id (r : ℕ∞) (A : Set (ModelChart n a M))
    (hA : IsContDiffAtlas r A) : ManifoldContDiff r A A id := by
  intro x
  exact ⟨continuousAt_id, fun e he d hd hx hxd =>
    chartContDiffAt_of_compatible (hA.2 e he d hd) hx hxd⟩

theorem manifoldContDiff_of_le (r q : ℕ∞)
    (A : Set (ModelChart n a M)) (B : Set (ModelChart m b N)) (f : M → N)
    (hqr : q ≤ r) (hf : ManifoldContDiff r A B f) : ManifoldContDiff q A B f := by
  intro x
  exact ⟨(hf x).1, fun e he d hd hx hxd =>
    LocalCoordinateExtension.of_le ((hf x).2 e he d hd hx hxd) hqr⟩

/-- Every given chart is compatible with every chart in its maximal extension. -/
theorem manifoldContDiff_maximalExtension_iff (r : ℕ∞)
    (A : Set (ModelChart n a M)) (B : Set (ModelChart m b N))
    (hA : IsContDiffAtlas r A) (hB : IsContDiffAtlas r B) (f : M → N) :
    ManifoldContDiff r (maximalExtension r A) (maximalExtension r B) f ↔
      ManifoldContDiff r A B f := by
  constructor
  · intro h x
    exact ⟨(h x).1, fun e he d hd hx hxd =>
      (h x).2 e (subset_maximalExtension hA he) d (subset_maximalExtension hB hd) hx hxd⟩
  · intro h x
    apply (manifoldContDiffAt_iff_oneChart r _ _
      (maximalExtension_isContDiffAtlas hA) (maximalExtension_isContDiffAtlas hB) f x).mpr
    obtain ⟨e, he, hx⟩ := hA.1 x
    obtain ⟨d, hd, hfx⟩ := hB.1 (f x)
    exact ⟨(h x).1, e, subset_maximalExtension hA he,
      d, subset_maximalExtension hB hd, hx, hfx, (h x).2 e he d hd hx hfx⟩

theorem manifoldContDiffOn_iff_localChartTest (r : ℕ∞)
    (A : Set (ModelChart n a M)) (B : Set (ModelChart m b N))
    (hA : IsContDiffAtlas r A) (hB : IsContDiffAtlas r B)
    (f : M → N) (s : Set M) (hs : IsOpen s) (hf : ContinuousOn f s) :
    ManifoldContDiffOn r A B f s ↔ LocalChartTestOn r A B f s := by
  constructor
  · intro h x hx
    obtain ⟨e, he, hxe⟩ := hA.1 x
    obtain ⟨d, hd, hxd⟩ := hB.1 (f x)
    have hcoord := LocalCoordinateExtension.eventually ((h x hx).2 e he d hd hxe hxd)
      (continuous_subtype_val.continuousAt.comp (e.continuousAt hxe))
    have hneigh : {y | y ∈ e.source ∧ f y ∈ d.source ∧ ChartContDiffAt r e d f y} ∈ 𝓝 x :=
      Filter.inter_mem (e.open_source.mem_nhds hxe)
        (Filter.inter_mem ((h x hx).1.preimage_mem_nhds (d.open_source.mem_nhds hxd)) hcoord)
    obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.mp hneigh
    exact ⟨e, he, d, hd, V, hV, hxV, fun y hy => (hVsub hy).1,
      fun y hy => (hVsub hy).2.1, fun y hy => (hVsub hy).2.2⟩
  · intro h x hx
    obtain ⟨e, he, d, hd, V, _hV, hxV, hVe, hVd, hcoord⟩ := h x hx
    exact (manifoldContDiffAt_iff_oneChart r A B hA hB f x).mpr
      ⟨(hf x hx).continuousAt (hs.mem_nhds hx), e, he, d, hd,
        hVe hxV, hVd hxV, hcoord x hxV⟩

/-- A chart germ is exactly an ambient extension on its relative coordinate domain. -/
theorem chartContDiffAt_iff_modelExtension (r : ℕ∞)
    (e : ModelChart n a M) (d : ModelChart m b N)
    (f : M → N) (x : M) (hx : x ∈ e.source) (hfx : f x ∈ d.source)
    (hf : ContinuousAt f x) :
    ChartContDiffAt r e d f x ↔
      ∃ U : Set (Euclidean n), IsOpen U ∧ (e x).val ∈ U ∧
        ∃ F : Euclidean n → Euclidean m, ContDiffOn ℝ r F U ∧
          ∀ y : ModelSpace n a, y ∈ e.target → f (e.symm y) ∈ d.source →
            y.val ∈ U → F y.val = (d (f (e.symm y))).val := by
  constructor
  · rintro ⟨U, hU, hxU, F, hF, heq⟩
    obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.mp heq
    have hT := e.symm.isOpen_inter_preimage hV
    obtain ⟨W, hW, hWT⟩ := isOpen_induced_iff.mp hT
    have hxW : (e x).val ∈ W := by
      change e x ∈ Subtype.val ⁻¹' W
      rw [hWT]
      exact ⟨e.map_source hx, by change e.symm (e x) ∈ V; simpa only [e.left_inv hx] using hxV⟩
    refine ⟨U ∩ W, hU.inter hW, ⟨hxU, hxW⟩, F, hF.mono inter_subset_left, ?_⟩
    intro y hy _hyf hyUW
    have hyT : y ∈ e.target ∩ e.symm ⁻¹' V := by
      change y ∈ e.symm.source ∩ e.symm ⁻¹' V
      rw [← hWT]
      exact hyUW.2
    have hh : F (e (e.symm y)).val = (d (f (e.symm y))).val := hVsub hyT.2
    simpa only [e.right_inv hy] using hh
  · rintro ⟨U, hU, hxU, F, hF, heq⟩
    refine ⟨U, hU, hxU, F, hF, ?_⟩
    filter_upwards [e.open_source.mem_nhds hx,
      hf.preimage_mem_nhds (d.open_source.mem_nhds hfx),
      (continuous_subtype_val.continuousAt.comp (e.continuousAt hx)).preimage_mem_nhds
        (hU.mem_nhds hxU)] with y hye hyd hyU
    simpa only [e.left_inv hye] using heq (e y) (e.map_source hye)
      (by rw [e.left_inv hye]; exact hyd) hyU

/-- Open inclusions preserve and reflect the extension germ, including empty sets. -/
theorem localCoordinateExtension_open_subtype_iff {r : ℕ∞} {s : Set M} (hs : IsOpen s)
    (ι : M → Euclidean n) (f : M → Euclidean m) (x : s) :
    LocalCoordinateExtension r (ι ∘ Subtype.val) (f ∘ Subtype.val) x ↔
      LocalCoordinateExtension r ι f x.val := by
  constructor
  · rintro ⟨U, hU, hxU, F, hF, heq⟩
    refine ⟨U, hU, hxU, F, hF, ?_⟩
    rw [← hs.isOpenEmbedding_subtypeVal.map_nhds_eq x]
    exact heq
  · intro h
    exact LocalCoordinateExtension.precomp h continuousAt_subtype_val rfl

theorem manifoldContDiff_restrict_open (r : ℕ∞)
    (A : Set (ModelChart n a M)) (B : Set (ModelChart m b N))
    (f : M → N) (s : Set M) (hs : IsOpen s) :
    let R : Set (ModelChart n a s) :=
      {e | ∃ hne : Nonempty s, ∃ d ∈ A, e = d.subtypeRestr (s := ⟨s, hs⟩) hne}
    ManifoldContDiffOn r A B f s ↔
      ManifoldContDiff r R B (fun x : s => f x.val) := by
  dsimp only
  constructor
  · intro h x
    refine ⟨(h x.val x.property).1.comp continuousAt_subtype_val, ?_⟩
    rintro _ ⟨hne, e, he, rfl⟩ d hd hx hfx
    apply (localCoordinateExtension_open_subtype_iff hs
      (fun y => (e y).val) (fun y => (d (f y)).val) x).mpr
    exact (h x.val x.property).2 e he d hd (by simpa only [OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using hx) hfx
  · intro h x hx
    let z : s := ⟨x, hx⟩
    refine ⟨hs.isOpenEmbedding_subtypeVal.continuousAt_iff.mp (h z).1, ?_⟩
    intro e he d hd hxe hfx
    have hh := (h z).2 (e.subtypeRestr (s := ⟨s, hs⟩) ⟨z⟩)
      ⟨⟨z⟩, e, he, rfl⟩ d hd (by simpa only [OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using hxe) hfx
    exact (localCoordinateExtension_open_subtype_iff hs
      (fun y => (e y).val) (fun y => (d (f y)).val) z).mp hh

/-- Recover transition smoothness from local coordinate germs. -/
theorem contDiffOnModel_transition_of_germs {r : ℕ∞} {e d : ModelChart n a M}
    (h : ∀ x, x ∈ e.source → x ∈ d.source → ChartContDiffAt r e d id x) :
    ContDiffOnModel r (e.symm.trans d) (e.symm.trans d).source := by
  intro y hy
  have hye : y ∈ e.target := hy.1
  have hx : e.symm y ∈ e.source := e.symm.map_source hye
  have hxd : e.symm y ∈ d.source := hy.2
  obtain ⟨U, hU, hxU, F, hF, heq⟩ :=
    (chartContDiffAt_iff_modelExtension r e d id (e.symm y) hx hxd continuousAt_id).mp
      (h (e.symm y) hx hxd)
  refine ⟨U, hU, ?_, F, hF, ?_⟩
  · simpa only [e.right_inv hye] using hxU
  · intro z hz hzU
    exact heq z hz.1 hz.2 hzU

theorem contDiffCompatible_of_germs {r : ℕ∞} {e d : ModelChart n a M}
    (h : ∀ x, x ∈ e.source → x ∈ d.source → ChartContDiffAt r e d id x)
    (h' : ∀ x, x ∈ d.source → x ∈ e.source → ChartContDiffAt r d e id x) :
    ContDiffCompatible r e d := by
  refine ⟨contDiffOnModel_transition_of_germs h, ?_⟩
  have hi : (e.symm.trans d).symm = d.symm.trans e := by
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm]
  have hs : (e.symm.trans d).target = (d.symm.trans e).source := by
    rw [← hi]; rfl
  change ContDiffOnModel r (e.symm.trans d).symm (e.symm.trans d).target
  rw [hi, hs]
  exact contDiffOnModel_transition_of_germs h'

/-- Transport a chart while retaining its original coordinate function. -/
@[simp] theorem transportedChart_apply (h : M ≃ₜ N) (e : ModelChart n a M) (y : N) :
    (h.symm.toOpenPartialHomeomorph.trans e) y = e (h.symm y) := rfl

@[simp] theorem mem_transportedChart_source (h : M ≃ₜ N) (e : ModelChart n a M) (y : N) :
    y ∈ (h.symm.toOpenPartialHomeomorph.trans e).source ↔ h.symm y ∈ e.source := by
  change (y ∈ Set.univ ∧ h.symm y ∈ e.source) ↔ h.symm y ∈ e.source
  exact and_iff_right (mem_univ y)

theorem transportAtlas_isContDiffAtlas (r : ℕ∞) (A : Set (ModelChart n a M))
    (h : M ≃ₜ N) (hA : IsContDiffAtlas r A) : IsContDiffAtlas r (transportAtlas h A) := by
  constructor
  · intro y
    obtain ⟨e, he, hye⟩ := hA.1 (h.symm y)
    exact ⟨h.symm.toOpenPartialHomeomorph.trans e, ⟨e, he, rfl⟩,
      (mem_transportedChart_source h e y).mpr hye⟩
  · rintro _ ⟨e, he, rfl⟩ _ ⟨d, hd, rfl⟩
    apply contDiffCompatible_of_germs
    · intro y hye hyd
      have hh := chartContDiffAt_of_compatible (hA.2 e he d hd)
        ((mem_transportedChart_source h e y).mp hye)
        ((mem_transportedChart_source h d y).mp hyd)
      exact LocalCoordinateExtension.precomp hh h.symm.continuous.continuousAt rfl
    · intro y hyd hye
      have hh := chartContDiffAt_of_compatible (hA.2 d hd e he)
        ((mem_transportedChart_source h d y).mp hyd)
        ((mem_transportedChart_source h e y).mp hye)
      exact LocalCoordinateExtension.precomp hh h.symm.continuous.continuousAt rfl

theorem transportAtlas_maps (r : ℕ∞) (A : Set (ModelChart n a M))
    (h : M ≃ₜ N) (hA : IsContDiffAtlas r A) :
    ManifoldContDiff r A (transportAtlas h A) h ∧
      ManifoldContDiff r (transportAtlas h A) A h.symm := by
  constructor
  · intro x
    refine ⟨h.continuous.continuousAt, ?_⟩
    rintro e he _ ⟨d, hd, rfl⟩ hxe hxd
    have hxd' : x ∈ d.source := by
      simpa only [mem_transportedChart_source, h.symm_apply_apply] using hxd
    apply LocalCoordinateExtension.congr (chartContDiffAt_of_compatible (hA.2 e he d hd) hxe hxd')
    exact Eventually.of_forall (fun y => by simp only [id_eq, transportedChart_apply, h.symm_apply_apply])
  · intro y
    refine ⟨h.symm.continuous.continuousAt, ?_⟩
    rintro _ ⟨e, he, rfl⟩ d hd hye hyd
    have hh := chartContDiffAt_of_compatible (hA.2 e he d hd)
      ((mem_transportedChart_source h e y).mp hye) hyd
    exact LocalCoordinateExtension.precomp hh h.symm.continuous.continuousAt rfl

/-- Chart transport also preserves smooth compatibility across the different
permitted source and target model kinds and ambient dimensions. -/
theorem diffeomorph_transport_charts (r : ℕ∞)
    (A : Set (ModelChart n a M)) (B : Set (ModelChart m b N)) (h : M ≃ₜ N)
    (hf : ManifoldContDiff r A B h) (hg : ManifoldContDiff r B A h.symm)
    (e : ModelChart n a M) (he : e ∈ A) (d : ModelChart m b N) (hd : d ∈ B)
    (y : N) (hye : h.symm y ∈ e.source) (hyd : y ∈ d.source) :
    ChartContDiffAt r (h.symm.toOpenPartialHomeomorph.trans e) d id y ∧
      ChartContDiffAt r d (h.symm.toOpenPartialHomeomorph.trans e) id y := by
  constructor
  · have hdy : h (h.symm y) ∈ d.source := by simpa only [h.apply_symm_apply] using hyd
    have hh := (hf (h.symm y)).2 e he d hd hye hdy
    have ht : LocalCoordinateExtension r (fun z => (e (h.symm z)).val)
        (fun z => (d (h (h.symm z))).val) y :=
      LocalCoordinateExtension.precomp (ι := fun z : M => (e z).val)
        (f := fun z : M => (d (h z)).val) hh h.symm.continuous.continuousAt rfl
    exact LocalCoordinateExtension.congr ht
      (Eventually.of_forall (fun z => by simp only [h.apply_symm_apply, id_eq]))
  · exact (hg y).2 d hd e he hyd hye

/-- A smooth bijection with smooth inverse sends every chart into the target
maximal atlas. The smoothness hypotheses are checked in both directions. -/
theorem transportAtlas_subset_of_maps {r : ℕ∞}
    {A : Set (ModelChart n a M)} {B : Set (ModelChart n a N)}
    (hB : IsMaximalContDiffAtlas r B) (h : M ≃ₜ N)
    (hf : ManifoldContDiff r A B h) (hg : ManifoldContDiff r B A h.symm) :
    transportAtlas h A ⊆ B := by
  have hmax : maximalExtension r B = B :=
    hB.2 _ (maximalExtension_isContDiffAtlas hB.1) (subset_maximalExtension hB.1)
  rw [← hmax]
  rintro _ ⟨e, he, rfl⟩ d hd
  have hdB : d ∈ B := hd
  apply contDiffCompatible_of_germs
  · intro y hye hyd
    exact (diffeomorph_transport_charts r A B h hf hg e he d hdB y
      ((mem_transportedChart_source h e y).mp hye) hyd).1
  · intro y hyd hye
    exact (diffeomorph_transport_charts r A B h hf hg e he d hdB y
      ((mem_transportedChart_source h e y).mp hye) hyd).2

theorem diffeomorph_transportAtlas (r : ℕ∞)
    (A : Set (ModelChart n a M)) (B : Set (ModelChart n a N))
    (hA : IsMaximalContDiffAtlas r A) (hB : IsMaximalContDiffAtlas r B)
    (h : M ≃ₜ N) (hf : ManifoldContDiff r A B h)
    (hg : ManifoldContDiff r B A h.symm) : transportAtlas h A = B := by
  apply Subset.antisymm (transportAtlas_subset_of_maps hB h hf hg)
  intro d hd
  have he : h.toOpenPartialHomeomorph.trans d ∈ A :=
    transportAtlas_subset_of_maps hA h.symm hg hf ⟨d, hd, rfl⟩
  refine ⟨h.toOpenPartialHomeomorph.trans d, he, ?_⟩
  apply OpenPartialHomeomorph.ext
  · intro y
    change d (h (h.symm y)) = d y
    rw [h.apply_symm_apply]
  · intro y
    change h (h.symm (d.symm y)) = d.symm y
    rw [h.apply_symm_apply]
  · ext y
    change (y ∈ univ ∧ (h.symm y ∈ univ ∧ h (h.symm y) ∈ d.source)) ↔ y ∈ d.source
    simp only [mem_univ, true_and, h.apply_symm_apply]


theorem contDiffDiffeomorph_transportAtlas (r : ℕ∞)
    (A : Set (ModelChart n a M)) (B : Set (ModelChart n a N))
    (hA : IsMaximalContDiffAtlas r A) (hB : IsMaximalContDiffAtlas r B)
    (h : ContDiffDiffeomorph r A B) : transportAtlas h.toHomeomorph A = B :=
  diffeomorph_transportAtlas r A B hA hB h.toHomeomorph h.contDiff_toFun h.contDiff_invFun

theorem exists_unique_manifoldContDiff_gluing (r : ℕ∞)
    (A : Set (ModelChart n a M)) (B : Set (ModelChart m b N))
    {ι : Type w} (U : ι → Set M) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x : M, ∃ i, x ∈ U i) (F : ∀ i, U i → N)
    (hcompat : ∀ i j (x : M) (hi : x ∈ U i) (hj : x ∈ U j), F i ⟨x, hi⟩ = F j ⟨x, hj⟩)
    (hF : ∀ i, ManifoldContDiff r (openSubsetAtlas A (U i) (hU i)) B (F i)) :
    ∃! f : M → N, ManifoldContDiff r A B f ∧ Continuous f ∧
      ∀ i (x : M) (hx : x ∈ U i), f x = F i ⟨x, hx⟩ := by
  classical
  let f : M → N := fun x => F (Classical.choose (hcover x))
    ⟨x, Classical.choose_spec (hcover x)⟩
  have heq : ∀ i (x : M) (hx : x ∈ U i), f x = F i ⟨x, hx⟩ := by
    intro i x hx
    exact hcompat (Classical.choose (hcover x)) i x (Classical.choose_spec (hcover x)) hx
  have hf : ManifoldContDiff r A B f := by
    intro x
    obtain ⟨i, hxi⟩ := hcover x
    let g : M → N := fun y => if hy : y ∈ U i then F i ⟨y, hy⟩ else f y
    have hrestrict : (fun z : U i => g z.val) = F i := by
      funext z
      simp only [g, dite_eq_left z.property]
    have hg : ManifoldContDiffOn r A B g (U i) :=
      (manifoldContDiff_restrict_open r A B g (U i) (hU i)).mpr (by rw [hrestrict]; exact hF i)
    apply manifoldContDiffAt_congr (hg x hxi)
    apply Filter.mem_of_superset ((hU i).mem_nhds hxi)
    intro y hy
    change g y = f y
    rw [show g y = F i ⟨y, hy⟩ by simp only [g, dite_eq_left hy], heq i y hy]
  refine ⟨f, ⟨hf, continuous_iff_continuousAt.mpr (fun x => (hf x).1), heq⟩, ?_⟩
  rintro g ⟨_hg, _hgc, hgeq⟩
  funext x
  obtain ⟨i, hxi⟩ := hcover x
  exact (hgeq i x hxi).trans (heq i x hxi).symm


end Maps

/-- The chain rule forces a differentiable left inverse of x³ to have
(derivative of the identity) = (derivative of g) · 0, which is impossible. -/
theorem cubic_smooth_bijection :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => x ^ 3) ∧
      Function.Bijective (fun x : ℝ => x ^ 3) ∧
      ∀ g : ℝ → ℝ, Function.LeftInverse g (fun x : ℝ => x ^ 3) →
        ¬ DifferentiableAt ℝ g 0 := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => x ^ 3) := contDiff_id.pow 3
  refine ⟨hc, ⟨(show Odd (3 : ℕ) by decide).pow_injective, ?_⟩, ?_⟩
  · apply hc.continuous.surjective (tendsto_pow_atTop (by decide))
    have hbot : Tendsto (fun x : ℝ => x * x * x) atBot atBot :=
      (tendsto_id.atBot_mul_atBot₀ tendsto_id).atTop_mul_atBot₀ tendsto_id
    simpa only [pow_succ, pow_zero, one_mul] using hbot
  · intro g hg hdiff
    have hg0 : g 0 = 0 := by simpa using hg 0
    have hpow : HasDerivAt (fun x : ℝ => x ^ 3) 0 0 := by
      simpa using (hasDerivAt_id' (0 : ℝ)).fun_pow 3
    have hcomp : HasDerivAt (g ∘ (fun x : ℝ => x ^ 3)) 0 0 := by
      have hg' : HasDerivAt g (deriv g 0) ((0 : ℝ) ^ 3) := by simpa using hdiff.hasDerivAt
      simpa using hg'.comp (h := fun x : ℝ => x ^ 3) (0 : ℝ) hpow
    have heq : (g ∘ (fun x : ℝ => x ^ 3)) = id := funext hg
    rw [heq] at hcomp
    have := hcomp.unique (hasDerivAt_id (0 : ℝ))
    norm_num at this

end SmoothManifolds
