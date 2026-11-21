import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.CoveringTopology
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Boundary
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.CoveringStructure

namespace SmoothManifolds.CoveringStructure
open Set Filter Topology
universe u v w

abbrev liftedAtlas := @CoveringData.liftedAtlas
abbrev IsSmoothCovering := @CoveringData.IsSmoothCovering
abbrev SmoothAlongAt := @CoveringData.SmoothAlongAt
abbrev ParameterSmoothAt := @CoveringData.ParameterSmoothAt
abbrev intervalParameter := CoveringData.intervalParameter

/-- Changing both sides of a coordinate germ by neighborhood equality. -/
theorem extension_congr {X : Type*} [TopologicalSpace X] {n m : ℕ} {r : ℕ∞}
    {ι ι' : X → Euclidean n} {f f' : X → Euclidean m} {x : X}
    (h : LocalCoordinateExtension r ι f x)
    (hi : ι =ᶠ[𝓝 x] ι') (hf : f =ᶠ[𝓝 x] f') :
    LocalCoordinateExtension r ι' f' x := by
  obtain ⟨U, hU, hx, F, hF, he⟩ := h
  refine ⟨U, hU, hi.eq_of_nhds ▸ hx, F, hF, ?_⟩
  exact (hi.fun_comp F).symm.trans (he.trans hf)

section Atlas
variable {n : ℕ} {a : ModelKind} {E : Type u} {M : Type v}
  [TopologicalSpace E] [TopologicalSpace M]
  (A : Set (ModelChart n a M)) (p : E → M)

lemma liftedAtlas_covers (hA : IsAtlas A) (hp : IsLocalHomeomorph p) :
    IsAtlas (liftedAtlas A p) := by
  intro x
  obtain ⟨q, hxq, heq⟩ := hp x
  obtain ⟨c, hc, hxc⟩ := hA (p x)
  refine ⟨q.trans c, ⟨q, ?_, c, hc, rfl⟩, hxq, ?_⟩
  · intro z _; exact congrFun heq.symm z
  · change q x ∈ c.source
    rw [← congrFun heq x]
    exact hxc

lemma lifted_chart_germ {q : OpenPartialHomeomorph E M} (hq : EqOn q p q.source)
    (c : ModelChart n a M) {x : E} (hx : x ∈ q.source) :
    (fun y => ((q.trans c) y).val) =ᶠ[𝓝 x] (fun y => (c (p y)).val) := by
  filter_upwards [q.open_source.mem_nhds hx] with y hy
  change (c (q y)).val = (c (p y)).val
  rw [hq hy]

lemma liftedAtlas_compatible (hA : IsContDiffAtlas (⊤ : ℕ∞) A)
    (hp : Continuous p) :
    ∀ e ∈ liftedAtlas A p, ∀ d ∈ liftedAtlas A p,
      ContDiffCompatible (⊤ : ℕ∞) e d := by
  have hforward : ∀ e ∈ liftedAtlas A p, ∀ d ∈ liftedAtlas A p,
      ∀ x ∈ e.source, x ∈ d.source → ChartContDiffAt (⊤ : ℕ∞) e d id x := by
    rintro e ⟨q, hq, c, hc, rfl⟩ d ⟨s, hs, b, hb, rfl⟩ x hx hy
    have hxc : p x ∈ c.source := by rw [← hq hx.1]; exact hx.2
    have hxb : p x ∈ b.source := by rw [← hs hy.1]; exact hy.2
    have h := LocalCoordinateExtension.precomp
      (chartContDiffAt_of_compatible (hA.2 c hc b hb) hxc hxb) hp.continuousAt rfl
    exact extension_congr h (lifted_chart_germ p hq c hx.1).symm
      (lifted_chart_germ p hs b hy.1).symm
  intro e he d hd
  exact contDiffCompatible_of_germs (hforward e he d hd) (hforward d hd e he)

lemma liftedAtlas_isContDiffAtlas (hA : IsContDiffAtlas (⊤ : ℕ∞) A)
    (hp : IsLocalHomeomorph p) : IsContDiffAtlas (⊤ : ℕ∞) (liftedAtlas A p) :=
  ⟨liftedAtlas_covers A p hA.1 hp, liftedAtlas_compatible A p hA hp.continuous⟩

end Atlas
section Construction
variable {n : ℕ} {a : ModelKind} {E : Type u} {M : Type v}
  [TopologicalSpace E] [TopologicalSpace M]

/-- The maximal extension of the pulled-back chart cover makes the covering
projection and each inverse branch smooth in the ambient-extension sense. -/
theorem smooth_covering_of_liftedAtlas (T : SmoothManifold n a E)
    (S : SmoothManifold n a M) (p : E → M) (hp : IsCoveringMap p)
    (hT : T.smoothStructure.val =
      maximalExtension (⊤ : ℕ∞) (liftedAtlas S.smoothStructure.val p)) :
    IsSmoothCovering T S p := by
  have hL := liftedAtlas_isContDiffAtlas S.smoothStructure.val p
    S.smoothStructure.property.1 hp.isLocalHomeomorph
  have hmem : liftedAtlas S.smoothStructure.val p ⊆ T.smoothStructure.val := by
    rw [hT]; exact subset_maximalExtension hL
  refine ⟨hp, ?_, ?_⟩
  · intro x
    obtain ⟨q, hxq, hpq⟩ := hp.isLocalHomeomorph x
    obtain ⟨c, hc, hxc⟩ := S.smoothStructure.property.1.1 (p x)
    have hq : EqOn q p q.source := fun y _ => congrFun hpq.symm y
    refine (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞)
      T.smoothStructure.val S.smoothStructure.val
      T.smoothStructure.property.1 S.smoothStructure.property.1 p x).mpr
      ⟨hp.continuous.continuousAt, q.trans c, hmem ⟨q, hq, c, hc, rfl⟩,
        c, hc, ⟨hxq, ?_⟩, hxc, ?_⟩
    · change q x ∈ c.source
      rw [← congrFun hpq x]; exact hxc
    · exact LocalCoordinateExtension.congr
        (LocalCoordinateExtension.self (⊤ : ℕ∞) (fun y => ((q.trans c) y).val) x)
        (lifted_chart_germ p hq c hxq)
  · intro q hq y hy
    obtain ⟨c, hc, hyc⟩ := S.smoothStructure.property.1.1 y
    refine (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞)
      S.smoothStructure.val T.smoothStructure.val
      S.smoothStructure.property.1 T.smoothStructure.property.1 q.symm y).mpr
      ⟨q.symm.continuousAt hy, c, hc, q.trans c, hmem ⟨q, hq, c, hc, rfl⟩,
        hyc, ⟨q.symm.map_source hy, ?_⟩, ?_⟩
    · change q (q.symm y) ∈ c.source
      rwa [q.right_inv hy]
    · apply LocalCoordinateExtension.congr
        (LocalCoordinateExtension.self (⊤ : ℕ∞) (fun z => (c z).val) y)
      filter_upwards [q.open_target.mem_nhds hy] with z hz
      change (c z).val = (c (q (q.symm z))).val
      rw [q.right_inv hz]

/-- A lifted chart has exactly the face coordinates of its base chart. -/
theorem boundary_of_liftedAtlas (T : SmoothManifold n a E)
    (S : SmoothManifold n a M) (p : E → M) (hp : IsCoveringMap p)
    (hT : T.smoothStructure.val =
      maximalExtension (⊤ : ℕ∞) (liftedAtlas S.smoothStructure.val p)) :
    intrinsicBoundary T = p ⁻¹' intrinsicBoundary S := by
  have hL := liftedAtlas_isContDiffAtlas S.smoothStructure.val p
    S.smoothStructure.property.1 hp.isLocalHomeomorph
  ext x
  obtain ⟨q, hxq, hpq⟩ := hp.isLocalHomeomorph x
  obtain ⟨c, hc, hxc⟩ := S.smoothStructure.property.1.1 (p x)
  have hq : EqOn q p q.source := fun y _ => congrFun hpq.symm y
  have he : q.trans c ∈ T.smoothStructure.val := by
    rw [hT]
    exact subset_maximalExtension hL ⟨q, hq, c, hc, rfl⟩
  have hxe : x ∈ (q.trans c).source := by
    refine ⟨hxq, ?_⟩
    change q x ∈ c.source
    rw [← congrFun hpq x]; exact hxc
  rw [intrinsicBoundary_iff_chart T (q.trans c) he x hxe]
  change ((q.trans c) x).val ∈ modelFace n a ↔ p x ∈ intrinsicBoundary S
  rw [intrinsicBoundary_iff_chart S c hc (p x) hxc]
  change (c (q x)).val ∈ modelFace n a ↔ (c (p x)).val ∈ modelFace n a
  rw [hq hxq]

end Construction

section Lift
variable {n k : ℕ} {a b : ModelKind}
  {E : Type u} {M : Type v} {X : Type w}
  [TopologicalSpace E] [TopologicalSpace M] [TopologicalSpace X]

/-- Local smoothness of a lift uses just one inverse branch near the point. -/
theorem smooth_lift {n k : ℕ} {a b c : ModelKind}
    {E : Type u} {M : Type v} {X : Type w}
    [TopologicalSpace E] [TopologicalSpace M] [TopologicalSpace X]
    (T : SmoothManifold n a E) (S : SmoothManifold n c M)
    (R : SmoothManifold k b X) (p : E → M) (hp : IsSmoothCovering T S p)
    (f : X → M) (g : X → E) (hf : IsSmoothMap R S f) (hg : Continuous g)
    (heq : p ∘ g = f) : IsSmoothMap R T g := by
  intro x
  obtain ⟨q, hxq, hpq⟩ := hp.1.isLocalHomeomorph (g x)
  have hfx : f x ∈ q.target := by
    rw [← congrFun heq x, Function.comp_apply, hpq]
    exact q.map_source hxq
  have hq : EqOn q p q.source := fun y _ => congrFun hpq.symm y
  have hi := hp.2.2 q hq (f x) hfx
  have hc := manifoldContDiffAt_comp S.smoothStructure.property.1.1 (hf x) hi
  apply manifoldContDiffAt_congr hc
  filter_upwards [hg.continuousAt.preimage_mem_nhds (q.open_source.mem_nhds hxq)] with y hy
  change q.symm (f y) = g y
  rw [← congrFun heq y, Function.comp_apply, hpq]
  exact q.left_inv hy

/-- Arbitrary Euclidean parameters include charts in ordinary manifolds and
embedded interval/orthant parameters for paths and homotopies. -/
theorem smooth_lift_alongAt (T : SmoothManifold n a E) (S : SmoothManifold n a M)
    (p : E → M) (hp : IsSmoothCovering T S p)
    (ι : X → Euclidean k) (f : X → M) (g : X → E) (x : X)
    (hf : SmoothAlongAt S ι f x) (hg : ContinuousAt g x) (heq : p ∘ g = f) :
    SmoothAlongAt T ι g x := by
  obtain ⟨q, hxq, hpq⟩ := hp.1.isLocalHomeomorph (g x)
  have hfx : f x ∈ q.target := by
    rw [← congrFun heq x, Function.comp_apply, hpq]
    exact q.map_source hxq
  have hq : EqOn q p q.source := fun y _ => congrFun hpq.symm y
  have hi := hp.2.2 q hq (f x) hfx
  refine ⟨hg, ?_⟩
  intro d hd hxd
  obtain ⟨c, hc, hxc⟩ := S.smoothStructure.property.1.1 (f x)
  have hqi : q.symm (f x) = g x := by
    rw [← congrFun heq x, Function.comp_apply, hpq]
    exact q.left_inv hxq
  have hl := LocalCoordinateExtension.precomp
    (hi.2 c hc d hd hxc (by rwa [hqi])) hf.1 rfl
  have hl' := LocalCoordinateExtension.comp hl (hf.2 c hc hxc)
  apply LocalCoordinateExtension.congr hl'
  filter_upwards [hg.preimage_mem_nhds (q.open_source.mem_nhds hxq)] with y hy
  change (d (q.symm (f y))).val = (d (g y)).val
  rw [← congrFun heq y, Function.comp_apply, hpq, q.left_inv hy]

/-- On an induced parameter topology, germ agreement is equivalent to agreement
on the whole domain over a smaller ambient open neighborhood. -/
theorem extension_iff_of_isInducing {X : Type*} [TopologicalSpace X] {j l : ℕ}
    (ι : X → Euclidean j) (hi : Topology.IsInducing ι)
    (f : X → Euclidean l) (x : X) :
    LocalCoordinateExtension (⊤ : ℕ∞) ι f x ↔
      HasLocalContDiffExtensionAt (⊤ : ℕ∞) ι f x := by
  constructor
  · rintro ⟨U, hU, hxU, F, hF, he⟩
    obtain ⟨V, hVe, hV, hxV⟩ := mem_nhds_iff.mp he
    obtain ⟨W, hW, hWV⟩ := hi.isOpen_iff.mp hV
    refine ⟨U ∩ W, hU.inter hW, ⟨hxU, ?_⟩, F, hF.mono inter_subset_left, ?_⟩
    · change x ∈ ι ⁻¹' W
      rwa [hWV]
    · intro y hy
      exact hVe (by rw [← hWV]; exact hy.2)
  · rintro ⟨U, hU, hxU, F, hF, he⟩
    refine ⟨U, hU, hxU, F, hF, ?_⟩
    filter_upwards [hi.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU)] with y hy
    exact he y hy

theorem parameterSmoothAt_iff (S : SmoothManifold n a M)
    (ι : X → Euclidean k) (hi : Topology.IsInducing ι) (f : X → M) (x : X) :
    ParameterSmoothAt S ι f x ↔ SmoothAlongAt S ι f x := by
  constructor <;> intro h <;> refine ⟨h.1, ?_⟩ <;> intro d hd hxd
  · exact (extension_iff_of_isInducing ι hi _ x).mpr (h.2 d hd hxd)
  · exact (extension_iff_of_isInducing ι hi _ x).mp (h.2 d hd hxd)

theorem smooth_parameter_lift (T : SmoothManifold n a E) (S : SmoothManifold n a M)
    (p : E → M) (hp : IsSmoothCovering T S p)
    (ι : X → Euclidean k) (hi : Topology.IsInducing ι)
    (f : X → M) (g : X → E) (x : X) (hf : ParameterSmoothAt S ι f x)
    (hg : ContinuousAt g x) (heq : p ∘ g = f) : ParameterSmoothAt T ι g x := by
  rw [parameterSmoothAt_iff T ι hi]
  exact smooth_lift_alongAt T S p hp ι f g x
    ((parameterSmoothAt_iff S ι hi f x).mp hf) hg heq

end Lift

section Consequences
variable {n k : ℕ} {a : ModelKind} {E : Type u} {M : Type v} {X : Type w}
  [TopologicalSpace E] [TopologicalSpace M] [TopologicalSpace X]

lemma intervalParameter_isInducing : Topology.IsInducing intervalParameter := by
  exact (Homeomorph.funUnique (Fin 1) ℝ).symm.isInducing.comp Topology.IsInducing.subtypeVal

/-- Smoothness of the lift supplied by Mathlib's topological path theorem. -/
theorem smooth_liftPath (T : SmoothManifold n a E) (S : SmoothManifold n a M)
    (p : E → M) (hp : IsSmoothCovering T S p)
    (γ : C(unitInterval, M)) (e : E) (h₀ : γ 0 = p e)
    (hγ : ∀ t, ParameterSmoothAt S intervalParameter γ t) :
    ∀ t, ParameterSmoothAt T intervalParameter (hp.1.liftPath γ e h₀) t := by
  intro t
  exact smooth_parameter_lift T S p hp intervalParameter intervalParameter_isInducing
    γ (hp.1.liftPath γ e h₀) t (hγ t) (hp.1.liftPath γ e h₀).continuous.continuousAt
    (hp.1.liftPath_lifts γ e h₀)

/-- Smoothness of the lift supplied by the topological homotopy theorem. -/
theorem smooth_liftHomotopy (T : SmoothManifold n a E) (S : SmoothManifold n a M)
    (p : E → M) (hp : IsSmoothCovering T S p)
    (H : C(unitInterval × X, M)) (g₀ : C(X, E))
    (h₀ : ∀ x, H (0, x) = p (g₀ x)) (ι : unitInterval × X → Euclidean k)
    (hH : ∀ z, SmoothAlongAt S ι H z) :
    ∀ z, SmoothAlongAt T ι (hp.1.liftHomotopy H g₀ h₀) z := by
  intro z
  exact smooth_lift_alongAt T S p hp ι H (hp.1.liftHomotopy H g₀ h₀) z (hH z)
    (hp.1.liftHomotopy H g₀ h₀).continuous.continuousAt (hp.1.liftHomotopy_lifts H g₀ h₀)

theorem smooth_parameter_liftHomotopy (T : SmoothManifold n a E) (S : SmoothManifold n a M)
    (p : E → M) (hp : IsSmoothCovering T S p)
    (H : C(unitInterval × X, M)) (g₀ : C(X, E))
    (h₀ : ∀ x, H (0, x) = p (g₀ x)) (ι : unitInterval × X → Euclidean k)
    (hi : Topology.IsInducing ι) (hH : ∀ z, ParameterSmoothAt S ι H z) :
    ∀ z, ParameterSmoothAt T ι (hp.1.liftHomotopy H g₀ h₀) z := by
  intro z
  exact smooth_parameter_lift T S p hp ι hi H (hp.1.liftHomotopy H g₀ h₀) z (hH z)
    (hp.1.liftHomotopy H g₀ h₀).continuous.continuousAt (hp.1.liftHomotopy_lifts H g₀ h₀)

/-- In particular this applies to every sheet over a connected evenly covered
coordinate neighborhood, with the same inverse and unchanged open domains. -/
theorem smooth_branch (T : SmoothManifold n a E) (S : SmoothManifold n a M)
    (p : E → M) (hp : IsSmoothCovering T S p)
    (q : OpenPartialHomeomorph E M) (hq : EqOn q p q.source) :
    ManifoldSmoothOn T.smoothStructure.val S.smoothStructure.val q q.source ∧
    ManifoldSmoothOn S.smoothStructure.val T.smoothStructure.val q.symm q.target := by
  refine ⟨?_, hp.2.2 q hq⟩
  intro x hx
  apply manifoldContDiffAt_congr (hp.2.1 x)
  filter_upwards [q.open_source.mem_nhds hx] with y hy
  exact (hq hy).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- The restrictions are actual diffeomorphisms between the open sheet and its
base neighborhood, using the shared restricted atlases and the original maps. -/
private noncomputable def sheetDiffeomorph (T : SmoothManifold n a E) (S : SmoothManifold n a M)
    (p : E → M) (hp : IsSmoothCovering T S p)
    (q : OpenPartialHomeomorph E M) (hq : EqOn q p q.source) :
    Diffeomorph (MapData.openSubsetAtlas T.smoothStructure.val q.source q.open_source)
      (MapData.openSubsetAtlas S.smoothStructure.val q.target q.open_target) where
  toEquiv := q.toHomeomorphSourceTarget.toEquiv
  contDiff_toFun := by
    intro x
    have hcoe (z : q.source) : (q.toHomeomorphSourceTarget.toEquiv z).val = q z.val :=
      q.toHomeomorphSourceTarget_apply_coe z
    refine ⟨q.toHomeomorphSourceTarget.continuous.continuousAt, ?_⟩
    rintro _ ⟨hne, e, he, rfl⟩ _ ⟨hne', d, hd, rfl⟩ hx hdx
    have hdx' : (q.toHomeomorphSourceTarget.toEquiv x).val ∈ d.source := by
      simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hdx
    rw [hcoe] at hdx'
    have h := ((smooth_branch T S p hp q hq).1 x.val x.property).2 e he d hd
      (by simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hx) hdx'
    refine extension_congr (LocalCoordinateExtension.precomp h continuousAt_subtype_val rfl) ?_ ?_
    · exact Eventually.of_forall (fun _ => rfl)
    · apply Eventually.of_forall
      intro y
      change (d (q y.val)).val = (d (q.toHomeomorphSourceTarget.toEquiv y).val).val
      rw [hcoe]
  contDiff_invFun := by
    intro x
    have hcoe (z : q.target) : (q.toHomeomorphSourceTarget.toEquiv.symm z).val = q.symm z.val :=
      q.toHomeomorphSourceTarget_symm_apply_coe z
    refine ⟨q.toHomeomorphSourceTarget.symm.continuous.continuousAt, ?_⟩
    rintro _ ⟨hne, e, he, rfl⟩ _ ⟨hne', d, hd, rfl⟩ hx hdx
    have hdx' : (q.toHomeomorphSourceTarget.toEquiv.symm x).val ∈ d.source := by
      simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hdx
    rw [hcoe] at hdx'
    have h := ((smooth_branch T S p hp q hq).2 x.val x.property).2 e he d hd
      (by simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hx) hdx'
    refine extension_congr (LocalCoordinateExtension.precomp h continuousAt_subtype_val rfl) ?_ ?_
    · exact Eventually.of_forall (fun _ => rfl)
    · apply Eventually.of_forall
      intro y
      change (d (q.symm y.val)).val = (d (q.toHomeomorphSourceTarget.toEquiv.symm y).val).val
      rw [hcoe]

/-- Every open sheet is diffeomorphic to its base neighborhood by the actual
restriction of the covering branch, with its actual inverse. -/
theorem exists_sheet_diffeomorph (T : SmoothManifold n a E) (S : SmoothManifold n a M)
    (p : E → M) (hp : IsSmoothCovering T S p)
    (q : OpenPartialHomeomorph E M) (hq : EqOn q p q.source) :
    ∃ D : Diffeomorph (MapData.openSubsetAtlas T.smoothStructure.val q.source q.open_source)
      (MapData.openSubsetAtlas S.smoothStructure.val q.target q.open_target),
      D.toEquiv = q.toHomeomorphSourceTarget.toEquiv :=
  ⟨sheetDiffeomorph T S p hp q hq, rfl⟩

end Consequences


section Uniqueness
variable {n : ℕ} {a : ModelKind} {E : Type u} {M : Type v}
  [TopologicalSpace E] [TopologicalSpace M]

/-- Mutual smooth identity maps identify maximal atlases on a fixed space. -/
theorem smoothStructure_eq_of_id (T T' : SmoothManifold n a E)
    (h : IsSmoothMap T T' id) (h' : IsSmoothMap T' T id) :
    T.smoothStructure = T'.smoothStructure := by
  have hc : ∀ e ∈ T.smoothStructure.val, ∀ d ∈ T'.smoothStructure.val,
      ContDiffCompatible (⊤ : ℕ∞) e d := by
    intro e he d hd
    exact contDiffCompatible_of_germs
      (fun x hx hy => (h x).2 e he d hd hx hy)
      (fun x hx hy => (h' x).2 d hd e he hx hy)
  have hsub : T.smoothStructure.val ⊆ maximalExtension (⊤ : ℕ∞) T'.smoothStructure.val :=
    fun e he d hd => hc e he d hd
  have hmax : maximalExtension (⊤ : ℕ∞) T'.smoothStructure.val = T'.smoothStructure.val :=
    T'.smoothStructure.property.2 _
      (maximalExtension_isContDiffAtlas T'.smoothStructure.property.1)
      (subset_maximalExtension T'.smoothStructure.property.1)
  apply Subtype.ext
  exact (T.smoothStructure.property.2 _ T'.smoothStructure.property.1
    (hmax ▸ hsub)).symm

/-- Smooth lifts of the two projections force equality, not just an abstract
diffeomorphism between two possible structures. -/
theorem smooth_covering_unique (T T' : SmoothManifold n a E)
    (S : SmoothManifold n a M) (p : E → M)
    (hT : IsSmoothCovering T S p) (hT' : IsSmoothCovering T' S p) :
    T.smoothStructure = T'.smoothStructure := by
  exact smoothStructure_eq_of_id T T'
    (smooth_lift T' S T p hT' p id hT.2.1 continuous_id rfl)
    (smooth_lift T S T' p hT p id hT'.2.1 continuous_id rfl)

/-- This also compares the half-space and Euclidean representations when both
are permitted: the identity is smooth in both directions. -/
theorem smooth_covering_compatible {n : ℕ} {a b c : ModelKind}
    {E : Type u} {M : Type v} [TopologicalSpace E] [TopologicalSpace M]
    (T : SmoothManifold n a E) (T' : SmoothManifold n b E)
    (S : SmoothManifold n c M) (p : E → M)
    (hT : IsSmoothCovering T S p) (hT' : IsSmoothCovering T' S p) :
    IsSmoothMap T T' id ∧ IsSmoothMap T' T id := by
  exact ⟨smooth_lift T' S T p hT' p id hT.2.1 continuous_id rfl,
    smooth_lift T S T' p hT p id hT'.2.1 continuous_id rfl⟩

end Uniqueness
section Existence
variable {n : ℕ} {a : ModelKind} {E : Type u} {M : Type v}
  [TopologicalSpace E] [TopologicalSpace M]

/-- The dimension and topology are unchanged. Separation and countability are
proved from the covering hypotheses before constructing the manifold record. -/
theorem exists_canonical_smooth_covering (S : SmoothManifold n a M)
    (p : E → M) (hp : IsCoveringMap p)
    (hcount : (∀ y : M, (p ⁻¹' {y}).Countable) ∨ PreconnectedSpace E) :
    ∃ T : SmoothManifold n a E,
      T.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (liftedAtlas S.smoothStructure.val p) ∧
      IsSmoothCovering T S p ∧
      intrinsicBoundary T = p ⁻¹' intrinsicBoundary S ∧
      ∀ T' : SmoothManifold n a E, IsSmoothCovering T' S p →
        T'.smoothStructure = T.smoothStructure := by
  have hHaus := CoveringTopology.hausdorff S.topologicalManifold p hp
  have hSC : SecondCountableTopology E := by
    rcases hcount with h | h
    · exact CoveringTopology.secondCountable_of_countable_fibers S.topologicalManifold p hp h
    · let := h
      exact CoveringTopology.secondCountable_of_preconnected S.topologicalManifold p hp
  let L := liftedAtlas S.smoothStructure.val p
  have hL : IsContDiffAtlas (⊤ : ℕ∞) L :=
    liftedAtlas_isContDiffAtlas _ _ S.smoothStructure.property.1 hp.isLocalHomeomorph
  let T : SmoothManifold n a E :=
    ⟨⟨hHaus, hSC, L, hL.1⟩, ⟨maximalExtension (⊤ : ℕ∞) L, maximalExtension_isMaximal hL⟩⟩
  have hT := smooth_covering_of_liftedAtlas T S p hp rfl
  exact ⟨T, rfl, hT, boundary_of_liftedAtlas T S p hp rfl,
    fun T' hT' => smooth_covering_unique T' T S p hT' hT⟩

/-- The dimension-zero face is empty in either permitted model. -/
theorem zero_boundary {a : ModelKind} {E : Type u} {M : Type v}
    [TopologicalSpace E] [TopologicalSpace M]
    (T : SmoothManifold 0 a E) (S : SmoothManifold 0 a M) :
    intrinsicBoundary T = ∅ ∧ intrinsicBoundary S = ∅ := by
  constructor <;> apply eq_empty_iff_forall_notMem.mpr <;>
    rintro x ⟨c, hc, hx, hf⟩ <;> cases a <;> exact hf

theorem simplyConnected_covering_smooth [SimplyConnectedSpace E]
    (S : SmoothManifold n a M) (p : E → M) (hp : IsCoveringMap p) :
    ∃ T : SmoothManifold n a E, IsSmoothCovering T S p ∧
      intrinsicBoundary T = p ⁻¹' intrinsicBoundary S ∧
      ∀ T' : SmoothManifold n a E, IsSmoothCovering T' S p →
        T'.smoothStructure = T.smoothStructure := by
  obtain ⟨T, _, hT, hbd, hu⟩ := exists_canonical_smooth_covering S p hp (Or.inr inferInstance)
  exact ⟨T, hT, hbd, hu⟩

/-- No chart exists on an empty space, since its model contains the origin. -/
theorem empty_atlas {n : ℕ} {a : ModelKind} {E : Type u}
    [TopologicalSpace E] [IsEmpty E] (T : SmoothManifold n a E) :
    T.smoothStructure.val = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro c hc
  have hz : (0 : Euclidean n) ∈ modelSet n a := by
    cases a with
    | euclidean => exact mem_univ _
    | halfSpace => cases n <;> simp [modelSet, ModelData.modelSet, ModelData.halfSpaceSet]
  exact isEmptyElim (c.symm ⟨0, hz⟩)

end Existence
end SmoothManifolds.CoveringStructure
