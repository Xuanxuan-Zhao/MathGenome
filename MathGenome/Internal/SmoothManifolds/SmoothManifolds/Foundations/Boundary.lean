import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.SmoothMaps
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Boundary
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace SmoothManifolds
open Set Filter
open scoped Topology ContDiff
universe u v

abbrev modelFace := BoundaryData.modelFace
abbrev intrinsicBoundary := @BoundaryData.intrinsicBoundary
abbrev manifoldInterior := @BoundaryData.manifoldInterior
abbrev faceEmbedding := @BoundaryData.faceEmbedding
abbrev IsFaceRestriction := @BoundaryData.IsFaceRestriction

@[simp] theorem intrinsicBoundary_zero {kind : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold 0 kind M) : intrinsicBoundary S = ∅ := by
  ext p
  cases kind <;> simp [intrinsicBoundary, BoundaryData.intrinsicBoundary,
    BoundaryData.modelFace, ModelData.halfSpaceFace]

@[simp] theorem intrinsicBoundary_euclidean {n : ℕ} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n .euclidean M) :
    intrinsicBoundary S = ∅ := by
  ext p
  simp [intrinsicBoundary, BoundaryData.intrinsicBoundary, BoundaryData.modelFace]

/-- The local half-space face is exactly the complement of its ambient interior. -/
theorem mem_modelFace_iff_not_mem_interior {n : ℕ} {kind : ModelKind}
    (x : ModelSpace n kind) :
    x.val ∈ modelFace n kind ↔ x.val ∉ interior (modelSet n kind) := by
  cases kind with
  | euclidean => simp [modelFace, BoundaryData.modelFace, modelSet, ModelData.modelSet]
  | halfSpace =>
    cases n with
    | zero => simp [modelFace, BoundaryData.modelFace, ModelData.halfSpaceFace,
        modelSet, ModelData.modelSet, ModelData.halfSpaceSet]
    | succ n =>
      have hi : interior (modelSet (n + 1) .halfSpace) =
          {z : Euclidean (n + 1) | 0 < z (Fin.last n)} := by
        change interior ((fun z : Euclidean (n + 1) => z (Fin.last n)) ⁻¹' Ici 0) = _
        rw [← (isOpenMap_eval (Fin.last n)).preimage_interior_eq_interior_preimage
          (continuous_apply (Fin.last n)), interior_Ici]
        rfl
      rw [hi]
      change x.val (Fin.last n) = 0 ↔ ¬ 0 < x.val (Fin.last n)
      exact ⟨fun h => by rw [h]; exact lt_irrefl _,
        fun h => le_antisymm (le_of_not_gt h) x.property⟩

/-- Convert a model-neighborhood assertion into an ambient assertion at an
interior point. This step does not assume boundary invariance. -/
private theorem eventually_ambient_of_model {n : ℕ} {kind : ModelKind}
    (x : ModelSpace n kind) (hx : x.val ∈ interior (modelSet n kind))
    {P : Euclidean n → Prop} (h : ∀ᶠ z in 𝓝 x, P z.val) : ∀ᶠ z in 𝓝 x.val, P z := by
  have hm : map (Subtype.val : ModelSpace n kind → Euclidean n) (𝓝 x) = 𝓝 x.val := by
    rw [map_nhds_subtype_val, nhdsWithin_eq_nhds.mpr (mem_interior_iff_mem_nhds.mp hx)]
  rw [← hm]
  exact h

/-- Inverse ambient germs preserve interior points of the two permitted models.
Only the source interior is needed: the chain rule there gives a left inverse,
and finite dimension makes the forward derivative surjective. -/
private theorem model_inverse_preserves_interior {n : ℕ} {a b : ModelKind}
    (x : ModelSpace n a) (y : ModelSpace n b)
    {F G : Euclidean n → Euclidean n}
    (hF : DifferentiableAt ℝ F x.val) (hG : DifferentiableAt ℝ G y.val)
    (hFx : F x.val = y.val)
    (hGF : (fun z : ModelSpace n a => G (F z.val)) =ᶠ[𝓝 x] Subtype.val)
    (hmap : ∀ᶠ z : ModelSpace n a in 𝓝 x, F z.val ∈ modelSet n b)
    (hx : x.val ∈ interior (modelSet n a)) :
    y.val ∈ interior (modelSet n b) := by
  have heq : (G ∘ F) =ᶠ[𝓝 x.val] id := eventually_ambient_of_model x hx hGF
  have hG' : DifferentiableAt ℝ G (F x.val) := hFx.symm ▸ hG
  have hcomp := (hG'.hasFDerivAt.comp x.val hF.hasFDerivAt).congr_of_eventuallyEq heq.symm
  have hlin : (fderiv ℝ G y.val).comp (fderiv ℝ F x.val) =
      ContinuousLinearMap.id ℝ (Euclidean n) := by
    simpa only [hFx] using hcomp.unique (hasFDerivAt_id x.val)
  have hinj : Function.Injective (fderiv ℝ F x.val) := by
    intro u v huv
    have hh := congrArg (fderiv ℝ G y.val) huv
    simpa only [← ContinuousLinearMap.comp_apply, hlin, ContinuousLinearMap.id_apply] using hh
  have hsurj : Function.Surjective (fderiv ℝ F x.val) :=
    (fderiv ℝ F x.val).toLinearMap.injective_iff_surjective.mp hinj
  have hm : ∀ᶠ z in 𝓝 x.val, F z ∈ modelSet n b := eventually_ambient_of_model x hx hmap
  by_contra hy
  have hyface := (mem_modelFace_iff_not_mem_interior y).mpr hy
  cases b with
  | euclidean => exact hyface
  | halfSpace =>
    cases n with
    | zero => exact hyface
    | succ n =>
      change y.val (Fin.last n) = 0 at hyface
      have hmin : IsLocalMin (fun z => F z (Fin.last n)) x.val := by
        filter_upwards [hm] with z hz
        change F x.val (Fin.last n) ≤ F z (Fin.last n)
        rw [hFx, hyface]
        exact hz
      have hz := hmin.hasFDerivAt_eq_zero
        (((ContinuousLinearMap.proj (Fin.last n) : Euclidean (n + 1) →L[ℝ] ℝ)).hasFDerivAt.comp x.val hF.hasFDerivAt)
      obtain ⟨v, hv⟩ := hsurj (fun _ => 1)
      have hh := DFunLike.congr_fun hz v
      change (fderiv ℝ F x.val v) (Fin.last n) = 0 at hh
      rw [hv] at hh
      exact one_ne_zero hh

/-- Analytic chart comparison, with different source and target model kinds
permitted. Smoothness is used only through the two actual extension germs. -/
theorem chart_interior_preserved {n : ℕ} {a b : ModelKind} {M : Type u}
    [TopologicalSpace M] (c : ModelChart n a M) (d : ModelChart n b M) (p : M)
    (hc : p ∈ c.source) (hd : p ∈ d.source)
    (hcd : ChartContDiffAt (⊤ : ℕ∞) c d id p)
    (hdc : ChartContDiffAt (⊤ : ℕ∞) d c id p)
    (hp : (c p).val ∈ interior (modelSet n a)) :
    (d p).val ∈ interior (modelSet n b) := by
  obtain ⟨U, hU, hpU, F, hF, heF⟩ := hcd
  obtain ⟨V, hV, hpV, G, hG, heG⟩ := hdc
  have hFc : F (c p).val = (d p).val := heF.eq_of_nhds
  have hGF : (fun z : ModelSpace n a => G (F z.val)) =ᶠ[𝓝 (c p)] Subtype.val := by
    have ht : Tendsto c.symm (𝓝 (c p)) (𝓝 p) := by
      simpa only [ContinuousAt, c.left_inv hc] using c.symm.continuousAt (c.map_source hc)
    filter_upwards [heF.comp_tendsto ht, heG.comp_tendsto ht,
      c.open_target.mem_nhds (c.map_source hc)] with z hzF hzG hz
    change G (F z.val) = z.val
    change F (c (c.symm z)).val = (d (c.symm z)).val at hzF
    change G (d (c.symm z)).val = (c (c.symm z)).val at hzG
    rw [c.right_inv hz] at hzF hzG
    rw [hzF, hzG]
  have hm : ∀ᶠ z : ModelSpace n a in 𝓝 (c p), F z.val ∈ modelSet n b := by
    have ht : Tendsto c.symm (𝓝 (c p)) (𝓝 p) := by
      simpa only [ContinuousAt, c.left_inv hc] using c.symm.continuousAt (c.map_source hc)
    filter_upwards [heF.comp_tendsto ht, c.open_target.mem_nhds (c.map_source hc)] with z hzF hz
    change F (c (c.symm z)).val = (d (c.symm z)).val at hzF
    rw [c.right_inv hz] at hzF
    rw [hzF]
    exact (d (c.symm z)).property
  exact model_inverse_preserves_interior (c p) (d p)
    ((hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp))
    ((hG.contDiffAt (hV.mem_nhds hpV)).differentiableAt (by simp)) hFc hGF hm hp

theorem modelFace_chart_independent {n : ℕ} {a b : ModelKind} {M : Type u}
    [TopologicalSpace M] (c : ModelChart n a M) (d : ModelChart n b M) (p : M)
    (hc : p ∈ c.source) (hd : p ∈ d.source)
    (hcd : ChartContDiffAt (⊤ : ℕ∞) c d id p)
    (hdc : ChartContDiffAt (⊤ : ℕ∞) d c id p) :
    (c p).val ∈ modelFace n a ↔ (d p).val ∈ modelFace n b := by
  rw [mem_modelFace_iff_not_mem_interior, mem_modelFace_iff_not_mem_interior]
  exact not_congr ⟨chart_interior_preserved c d p hc hd hcd hdc,
    chart_interior_preserved d c p hd hc hdc hcd⟩

theorem intrinsicBoundary_iff_chart {n : ℕ} {kind : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n kind M) (c : ModelChart n kind M)
    (hc : c ∈ S.smoothStructure.val) (p : M) (hp : p ∈ c.source) :
    p ∈ intrinsicBoundary S ↔ (c p).val ∈ modelFace n kind := by
  constructor
  · rintro ⟨d, hd, hpd, hface⟩
    have hdc := S.smoothStructure.property.1.2 d hd c hc
    exact (modelFace_chart_independent d c p hpd hp
      (chartContDiffAt_of_compatible hdc hpd hp)
      (chartContDiffAt_of_compatible (contDiffCompatible_symm hdc) hp hpd)).mp hface
  · intro hface
    exact ⟨c, hc, hp, hface⟩

theorem isOpen_manifoldInterior {n : ℕ} {kind : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n kind M) : IsOpen (manifoldInterior S) := by
  apply isOpen_iff_forall_mem_open.mpr
  rintro p ⟨c, hc, hp, hpi⟩
  refine ⟨c.source ∩ (fun q => (c q).val) ⁻¹' interior (modelSet n kind), ?_, ?_, ⟨hp, hpi⟩⟩
  · intro q hq
    exact ⟨c, hc, hq.1, hq.2⟩
  · exact c.isOpen_inter_preimage
      (isOpen_interior.preimage continuous_subtype_val)

theorem compl_intrinsicBoundary {n : ℕ} {kind : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n kind M) :
    (intrinsicBoundary S)ᶜ = manifoldInterior S := by
  ext p
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  constructor
  · intro h
    refine ⟨c, hc, hp, ?_⟩
    have hnf : (c p).val ∉ modelFace n kind := by
      intro hf
      exact h ((intrinsicBoundary_iff_chart S c hc p hp).mpr hf)
    exact not_not.mp (mt (mem_modelFace_iff_not_mem_interior (c p)).mpr hnf)
  · rintro ⟨d, hd, hpd, hpi⟩ hbound
    exact (mem_modelFace_iff_not_mem_interior (d p)).mp
      ((intrinsicBoundary_iff_chart S d hd p hpd).mp hbound) hpi

theorem isClosed_intrinsicBoundary {n : ℕ} {kind : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n kind M) : IsClosed (intrinsicBoundary S) := by
  rw [← isOpen_compl_iff, compl_intrinsicBoundary]
  exact isOpen_manifoldInterior S

/-- A right inverse of ambient derivatives is available even at a target face:
its model has unique derivatives, as proved from the actual half-space domain. -/
private theorem model_right_inverse_preserves_interior {n m : ℕ} {a b : ModelKind}
    (x : ModelSpace n a) (y : ModelSpace m b)
    {F : Euclidean n → Euclidean m} {G : Euclidean m → Euclidean n}
    (hF : DifferentiableAt ℝ F x.val) (hG : DifferentiableAt ℝ G y.val)
    (hFx : F x.val = y.val) (hGy : G y.val = x.val)
    (hFG : (fun z : ModelSpace m b => F (G z.val)) =ᶠ[𝓝 y] Subtype.val)
    (hmap : ∀ᶠ z : ModelSpace n a in 𝓝 x, F z.val ∈ modelSet m b)
    (hx : x.val ∈ interior (modelSet n a)) :
    y.val ∈ interior (modelSet m b) := by
  have heq : (F ∘ G) =ᶠ[𝓝[modelSet m b] y.val] id := by
    rw [← map_nhds_subtype_val y]
    exact hFG
  have hF' : DifferentiableAt ℝ F (G y.val) := hGy.symm ▸ hF
  have hcomp := (hF'.hasFDerivAt.comp y.val hG.hasFDerivAt).hasFDerivWithinAt (s := modelSet m b)
  have hcomp' := hcomp.congr_of_eventuallyEq heq.symm (by simp only [Function.comp_apply, id_eq, hGy, hFx])
  have hlin : (fderiv ℝ F x.val).comp (fderiv ℝ G y.val) =
      ContinuousLinearMap.id ℝ (Euclidean m) := by
    simpa only [hGy] using (uniqueDiffOn_modelSet m b).eq y.property hcomp'
      (hasFDerivWithinAt_id y.val (modelSet m b))
  have hsurj : Function.Surjective (fderiv ℝ F x.val) := by
    intro z
    exact ⟨fderiv ℝ G y.val z, DFunLike.congr_fun hlin z⟩
  have hm : ∀ᶠ z in 𝓝 x.val, F z ∈ modelSet m b := eventually_ambient_of_model x hx hmap
  by_contra hy
  have hyface := (mem_modelFace_iff_not_mem_interior y).mpr hy
  cases b with
  | euclidean => exact hyface
  | halfSpace =>
    cases m with
    | zero => exact hyface
    | succ m =>
      change y.val (Fin.last m) = 0 at hyface
      have hmin : IsLocalMin (fun z => F z (Fin.last m)) x.val := by
        filter_upwards [hm] with z hz
        change F x.val (Fin.last m) ≤ F z (Fin.last m)
        rw [hFx, hyface]
        exact hz
      have hz := hmin.hasFDerivAt_eq_zero
        ((ContinuousLinearMap.proj (Fin.last m) : Euclidean (m + 1) →L[ℝ] ℝ).hasFDerivAt.comp x.val hF.hasFDerivAt)
      obtain ⟨v, hv⟩ := hsurj (fun _ => 1)
      have hh := DFunLike.congr_fun hz v
      change (fderiv ℝ F x.val v) (Fin.last m) = 0 at hh
      rw [hv] at hh
      exact one_ne_zero hh

private theorem homeomorph_chart_interior_preserved {n m : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (c : ModelChart n a M) (d : ModelChart m b N) (h : M ≃ₜ N) (p : M)
    (hc : p ∈ c.source) (hd : h p ∈ d.source)
    (hcd : ChartContDiffAt (⊤ : ℕ∞) c d h p)
    (hdc : ChartContDiffAt (⊤ : ℕ∞) d c h.symm (h p))
    (hp : (c p).val ∈ interior (modelSet n a)) :
    (d (h p)).val ∈ interior (modelSet m b) := by
  obtain ⟨U, hU, hpU, F, hF, heF⟩ := hcd
  obtain ⟨V, hV, hpV, G, hG, heG⟩ := hdc
  have hGy : G (d (h p)).val = (c p).val := by
    simpa only [h.symm_apply_apply] using heG.eq_of_nhds
  have ht : Tendsto c.symm (𝓝 (c p)) (𝓝 p) := by
    simpa only [ContinuousAt, c.left_inv hc] using c.symm.continuousAt (c.map_source hc)
  have ht' : Tendsto d.symm (𝓝 (d (h p))) (𝓝 (h p)) := by
    simpa only [ContinuousAt, d.left_inv hd] using d.symm.continuousAt (d.map_source hd)
  have ht'' : Tendsto (h.symm ∘ d.symm) (𝓝 (d (h p))) (𝓝 p) := by
    simpa only [h.symm_apply_apply] using h.symm.continuous.continuousAt.tendsto.comp ht'
  have hFG : (fun z : ModelSpace m b => F (G z.val)) =ᶠ[𝓝 (d (h p))] Subtype.val := by
    filter_upwards [heG.comp_tendsto ht', heF.comp_tendsto ht'',
      d.open_target.mem_nhds (d.map_source hd)] with z hzG hzF hz
    change G (d (d.symm z)).val = (c (h.symm (d.symm z))).val at hzG
    change F (c (h.symm (d.symm z))).val = (d (h (h.symm (d.symm z)))).val at hzF
    rw [h.apply_symm_apply, d.right_inv hz] at hzF
    rw [d.right_inv hz] at hzG
    rw [hzG, hzF]
  have hm : ∀ᶠ z : ModelSpace n a in 𝓝 (c p), F z.val ∈ modelSet m b := by
    filter_upwards [heF.comp_tendsto ht, c.open_target.mem_nhds (c.map_source hc)] with z hzF hz
    change F (c (c.symm z)).val = (d (h (c.symm z))).val at hzF
    rw [c.right_inv hz] at hzF
    rw [hzF]
    exact (d (h (c.symm z))).property
  exact model_right_inverse_preserves_interior (c p) (d (h p))
    ((hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp))
    ((hG.contDiffAt (hV.mem_nhds hpV)).differentiableAt (by simp)) heF.eq_of_nhds hGy hFG hm hp

private theorem diffeomorph_interior_forward {n m : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (h : Diffeomorph S.smoothStructure.val T.smoothStructure.val) (p : M)
    (hp : p ∈ manifoldInterior S) : h.toEquiv p ∈ manifoldInterior T := by
  obtain ⟨c, hc, hpc, hpint⟩ := hp
  obtain ⟨d, hd, hpd⟩ := T.smoothStructure.property.1.1 (h.toEquiv p)
  refine ⟨d, hd, hpd, ?_⟩
  apply homeomorph_chart_interior_preserved c d h.toHomeomorph p hpc hpd
    ((h.contDiff_toFun p).2 c hc d hd hpc hpd)
  · apply (h.contDiff_invFun (h.toEquiv p)).2 d hd c hc hpd
    simpa only [Equiv.symm_apply_apply] using hpc
  · exact hpint

theorem diffeomorph_interior_iff {n m : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (h : Diffeomorph S.smoothStructure.val T.smoothStructure.val) (p : M) :
    h.toEquiv p ∈ manifoldInterior T ↔ p ∈ manifoldInterior S := by
  constructor
  · intro hp
    let hi : Diffeomorph T.smoothStructure.val S.smoothStructure.val :=
      ⟨h.toEquiv.symm, h.contDiff_invFun, h.contDiff_toFun⟩
    simpa only [hi, Equiv.symm_apply_apply] using diffeomorph_interior_forward T S hi (h.toEquiv p) hp
  · exact diffeomorph_interior_forward S T h p

theorem diffeomorph_boundary_iff {n m : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (h : Diffeomorph S.smoothStructure.val T.smoothStructure.val) (p : M) :
    h.toEquiv p ∈ intrinsicBoundary T ↔ p ∈ intrinsicBoundary S := by
  have hh := not_congr (diffeomorph_interior_iff S T h p)
  simpa only [← compl_intrinsicBoundary, mem_compl_iff, not_not] using hh

section FaceCharts
variable {n : ℕ} {M : Type u} [TopologicalSpace M]

private theorem continuous_faceEmbedding (kind : ModelKind) :
    Continuous (faceEmbedding (n := n) kind) := by
  exact (Continuous.finSnoc (A := fun _ : Fin (n + 1) => ℝ)
    (continuous_subtype_val : Continuous (fun z : ModelSpace n .euclidean => z.val))
    (continuous_const : Continuous (fun _ : ModelSpace n .euclidean => (0 : ℝ)))).subtype_mk _

private theorem faceEmbedding_drop (x : ModelSpace (n + 1) .halfSpace)
    (hx : x.val ∈ modelFace (n + 1) .halfSpace) :
    faceEmbedding .halfSpace ⟨fun i : Fin n => x.val i.castSucc, mem_univ _⟩ = x := by
  apply Subtype.ext
  change Fin.snoc (Fin.init x.val) 0 = x.val
  change x.val (Fin.last n) = 0 at hx
  rw [← hx, Fin.snoc_init_self]

private theorem boundary_symm_face (S : SmoothManifold (n + 1) .halfSpace M)
    (c : ModelChart (n + 1) .halfSpace M) (hc : c ∈ S.smoothStructure.val)
    (z : ModelSpace n .euclidean) (hz : faceEmbedding .halfSpace z ∈ c.target) :
    c.symm (faceEmbedding .halfSpace z) ∈ intrinsicBoundary S := by
  apply (intrinsicBoundary_iff_chart S c hc _ (c.symm.map_source hz)).mpr
  rw [c.right_inv hz]
  change Fin.snoc (α := fun _ : Fin (n + 1) => ℝ) z.val 0 (Fin.last n) = 0
  exact Fin.snoc_last _ _

/-- The face chart, with a harmless default value outside its target. The
nonemptiness hypothesis is used only to define that off-target inverse. -/
private noncomputable def restrictedFaceChart
    (S : SmoothManifold (n + 1) .halfSpace M)
    (c : ModelChart (n + 1) .halfSpace M) (hc : c ∈ S.smoothStructure.val)
    (hne : Nonempty {p : intrinsicBoundary S // p.val ∈ c.source}) :
    ModelChart n .euclidean (intrinsicBoundary S) := by
  classical
  exact {
  toFun p := ⟨fun i => (c p.val).val i.castSucc, mem_univ _⟩
  invFun z := if hz : faceEmbedding .halfSpace z ∈ c.target then
      ⟨c.symm (faceEmbedding .halfSpace z), boundary_symm_face S c hc z hz⟩
    else (Classical.choice hne).val
  source := Subtype.val ⁻¹' c.source
  target := faceEmbedding .halfSpace ⁻¹' c.target
  map_source' p hp := by
    change faceEmbedding .halfSpace
      ⟨fun i : Fin n => (c p.val).val i.castSucc, mem_univ _⟩ ∈ c.target
    rw [faceEmbedding_drop (c p.val) ((intrinsicBoundary_iff_chart S c hc _ hp).mp p.property)]
    exact c.map_source hp
  map_target' z hz := by
    change faceEmbedding .halfSpace z ∈ c.target at hz
    simp only [dite_eq_left hz]
    exact c.symm.map_source hz
  left_inv' p hp := by
    have hface := (intrinsicBoundary_iff_chart S c hc _ hp).mp p.property
    have hemb := faceEmbedding_drop (c p.val) hface
    have ht : faceEmbedding .halfSpace
        ⟨fun i : Fin n => (c p.val).val i.castSucc, mem_univ _⟩ ∈ c.target := by
      rw [hemb]; exact c.map_source hp
    simp only [dite_eq_left ht]
    apply Subtype.ext
    change c.symm (faceEmbedding .halfSpace _) = p.val
    rw [hemb, c.left_inv hp]
  right_inv' z hz := by
    change faceEmbedding .halfSpace z ∈ c.target at hz
    simp only [dite_eq_left hz]
    apply Subtype.ext
    funext i
    change (c (c.symm (faceEmbedding .halfSpace z))).val i.castSucc = z.val i
    rw [c.right_inv hz]
    simp [faceEmbedding, BoundaryData.faceEmbedding]
  open_source := c.open_source.preimage continuous_subtype_val
  open_target := c.open_target.preimage (continuous_faceEmbedding .halfSpace)
  continuousOn_toFun := by
    apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    apply continuousOn_pi.mpr
    intro i
    exact (continuous_apply i.castSucc).comp_continuousOn
      (continuous_subtype_val.comp_continuousOn
        (c.continuousOn.comp continuous_subtype_val.continuousOn (fun _ h => h)))
  continuousOn_invFun := by
    apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    apply (c.symm.continuousOn.comp (continuous_faceEmbedding .halfSpace).continuousOn
      (fun _ h => h)).congr
    intro z hz
    change faceEmbedding .halfSpace z ∈ c.target at hz
    simp only [Function.comp_apply, dite_eq_left hz]
  }

private theorem restrictedFaceChart_isFaceRestriction
    (S : SmoothManifold (n + 1) .halfSpace M)
    (c : ModelChart (n + 1) .halfSpace M) (hc : c ∈ S.smoothStructure.val)
    (hne : Nonempty {p : intrinsicBoundary S // p.val ∈ c.source}) :
    IsFaceRestriction S c (restrictedFaceChart S c hc hne) :=
  ⟨rfl, rfl, fun _ _ _ => rfl⟩

private theorem contDiff_insertZero : ContDiff ℝ (⊤ : ℕ∞)
    (fun z : Euclidean n => (Fin.snoc (α := fun _ : Fin (n + 1) => ℝ) z 0 : Euclidean (n + 1))) := by
  apply contDiff_pi.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Euclidean n => (0 : ℝ)))
  · simpa only [Fin.snoc_castSucc] using (contDiff_apply ℝ (fun _ : Fin n => ℝ) j)

private theorem contDiff_dropLast : ContDiff ℝ (⊤ : ℕ∞)
    (fun z : Euclidean (n + 1) => (fun i : Fin n => z i.castSucc)) :=
  contDiff_pi.mpr (fun i => contDiff_apply ℝ (fun _ : Fin (n + 1) => ℝ) i.castSucc)

private theorem restrictedFaceChart_inclusion
    (S : SmoothManifold (n + 1) .halfSpace M)
    (c : ModelChart (n + 1) .halfSpace M) (hc : c ∈ S.smoothStructure.val)
    (hne : Nonempty {p : intrinsicBoundary S // p.val ∈ c.source})
    (p : intrinsicBoundary S) (hp : p.val ∈ c.source) :
    ChartContDiffAt (⊤ : ℕ∞) (restrictedFaceChart S c hc hne) c Subtype.val p := by
  refine ⟨univ, isOpen_univ, mem_univ _, _, contDiff_insertZero.contDiffOn, ?_⟩
  filter_upwards [c.open_source.preimage continuous_subtype_val |>.mem_nhds hp] with q hq
  exact congrArg Subtype.val (faceEmbedding_drop (c q.val)
    ((intrinsicBoundary_iff_chart S c hc _ hq).mp q.property))

private theorem restrictedFaceChart_transition
    (S : SmoothManifold (n + 1) .halfSpace M)
    (c d : ModelChart (n + 1) .halfSpace M)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
    (hne : Nonempty {p : intrinsicBoundary S // p.val ∈ c.source})
    (hne' : Nonempty {p : intrinsicBoundary S // p.val ∈ d.source})
    (p : intrinsicBoundary S) (hp : p.val ∈ c.source) (hp' : p.val ∈ d.source) :
    ChartContDiffAt (⊤ : ℕ∞) (restrictedFaceChart S c hc hne)
      (restrictedFaceChart S d hd hne') id p := by
  have horig := chartContDiffAt_of_compatible (S.smoothStructure.property.1.2 c hc d hd) hp hp'
  have hmid : LocalCoordinateExtension (⊤ : ℕ∞) (fun q : intrinsicBoundary S => (c q.val).val)
      (fun q => (d q.val).val) p :=
    LocalCoordinateExtension.precomp horig continuous_subtype_val.continuousAt rfl
  have hproj : LocalCoordinateExtension (⊤ : ℕ∞) (fun q : intrinsicBoundary S => (d q.val).val)
      (fun q => ((restrictedFaceChart S d hd hne') q).val) p :=
    ⟨univ, isOpen_univ, mem_univ _, _, contDiff_dropLast.contDiffOn,
      Eventually.of_forall (fun _ => rfl)⟩
  exact hproj.comp (hmid.comp (restrictedFaceChart_inclusion S c hc hne p hp))

private def faceAtlas (S : SmoothManifold (n + 1) .halfSpace M) :
    Set (ModelChart n .euclidean (intrinsicBoundary S)) :=
  {b | ∃ c : ModelChart (n + 1) .halfSpace M,
    ∃ hc : c ∈ S.smoothStructure.val,
    ∃ hne : Nonempty {p : intrinsicBoundary S // p.val ∈ c.source},
      b = restrictedFaceChart S c hc hne}

private theorem faceAtlas_isContDiffAtlas (S : SmoothManifold (n + 1) .halfSpace M) :
    IsContDiffAtlas (⊤ : ℕ∞) (faceAtlas S) := by
  constructor
  · intro p
    obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p.val
    let hne : Nonempty {p : intrinsicBoundary S // p.val ∈ c.source} := ⟨⟨p, hp⟩⟩
    exact ⟨restrictedFaceChart S c hc hne, ⟨c, hc, hne, rfl⟩, hp⟩
  · rintro b ⟨c, hc, hne, rfl⟩ b' ⟨d, hd, hne', rfl⟩
    apply contDiffCompatible_of_germs
    · intro p hp hp'
      exact restrictedFaceChart_transition S c d hc hd hne hne' p hp hp'
    · intro p hp hp'
      exact restrictedFaceChart_transition S d c hd hc hne' hne p hp hp'

private theorem exists_halfSpace_boundary_smoothManifold
    (S : SmoothManifold (n + 1) .halfSpace M) :
    ∃ B : SmoothManifold n .euclidean (intrinsicBoundary S),
      IsSmoothMap B S Subtype.val ∧
      ∀ c ∈ S.smoothStructure.val,
        Nonempty {p : intrinsicBoundary S // p.val ∈ c.source} →
        ∃ b ∈ B.smoothStructure.val, IsFaceRestriction S c b := by
  letI : T2Space M := S.topologicalManifold.hausdorff
  letI : SecondCountableTopology M := S.topologicalManifold.secondCountable
  have hA := faceAtlas_isContDiffAtlas S
  let B : SmoothManifold n .euclidean (intrinsicBoundary S) := {
    topologicalManifold := ⟨inferInstance, inferInstance, faceAtlas S, hA.1⟩
    smoothStructure := ⟨maximalExtension (⊤ : ℕ∞) (faceAtlas S), maximalExtension_isMaximal hA⟩ }
  refine ⟨B, ?_, ?_⟩
  · intro p
    obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p.val
    let hne : Nonempty {p : intrinsicBoundary S // p.val ∈ c.source} := ⟨⟨p, hp⟩⟩
    apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) B.smoothStructure.val
      S.smoothStructure.val B.smoothStructure.property.1 S.smoothStructure.property.1
      Subtype.val p).mpr
    exact ⟨continuous_subtype_val.continuousAt, restrictedFaceChart S c hc hne,
      subset_maximalExtension hA ⟨c, hc, hne, rfl⟩,
      c, hc, hp, hp, restrictedFaceChart_inclusion S c hc hne p hp⟩
  · intro c hc hne
    exact ⟨restrictedFaceChart S c hc hne, subset_maximalExtension hA ⟨c, hc, hne, rfl⟩,
      restrictedFaceChart_isFaceRestriction S c hc hne⟩

end FaceCharts

/-- Include the empty boundary of a Euclidean-model manifold as well. -/
theorem exists_boundary_smoothManifold {n : ℕ} {kind : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold (n + 1) kind M) :
    ∃ B : SmoothManifold n .euclidean (intrinsicBoundary S),
      IsSmoothMap B S Subtype.val ∧
      ∀ c ∈ S.smoothStructure.val,
        Nonempty {p : intrinsicBoundary S // p.val ∈ c.source} →
        ∃ b ∈ B.smoothStructure.val, IsFaceRestriction S c b := by
  cases kind with
  | halfSpace => exact exists_halfSpace_boundary_smoothManifold S
  | euclidean =>
    haveI : IsEmpty (intrinsicBoundary S) := by
      refine ⟨fun p => ?_⟩
      have hp := p.property
      simpa only [intrinsicBoundary_euclidean S, Set.mem_empty_iff_false] using hp
    letI : T2Space M := S.topologicalManifold.hausdorff
    letI : SecondCountableTopology M := S.topologicalManifold.secondCountable
    have hA : IsContDiffAtlas (⊤ : ℕ∞)
        (∅ : Set (ModelChart n .euclidean (intrinsicBoundary S))) :=
      ⟨fun p => isEmptyElim p, fun _ h => h.elim⟩
    let B : SmoothManifold n .euclidean (intrinsicBoundary S) := {
      topologicalManifold := ⟨inferInstance, inferInstance, ∅, hA.1⟩
      smoothStructure := ⟨maximalExtension (⊤ : ℕ∞) ∅, maximalExtension_isMaximal hA⟩ }
    refine ⟨B, fun p => isEmptyElim p, ?_⟩
    intro c hc hne
    exact isEmptyElim (Classical.choice hne).val

end SmoothManifolds
