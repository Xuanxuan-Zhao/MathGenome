import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.InteriorConstantRank
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.InteriorInverse
import MathGenome.MultivariableAnalysis.Topics.D04.C04

set_option autoImplicit false

namespace SmoothManifolds.InteriorConstantRank
open ModelData AtlasData MapData BoundaryData FiniteRegularityData MapClassData InteriorRankData Set Filter
open scoped Topology ContDiff
universe u v

/-- The continuous linear coordinate conversion, with no restriction on dimension. -/
noncomputable def toL2 (m : ℕ) : Euclidean m ≃L[ℝ] E m :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm

/-- Use the public finite/smooth D04 interfaces and their genuine regularity bridges. -/
theorem euclidean_constant_rank {m n : ℕ} (r : ℕ∞) (hr : 1 ≤ r)
    (U : Set (E m)) (hU : IsOpen U) (g : E m → E n)
    (hg : ContDiffOn ℝ r g U) (z : E m) (hz : z ∈ U) (k : ℕ)
    (hk : Specs.D04.C04.ConstantRank.NeighborhoodRank g z k) :
    0 ≤ k ∧ k ≤ min m n ∧
      Specs.D04.C04.ConstantRank.RankNormalForm r U g z k := by
  rcases eq_or_ne r ⊤ with h | h
  · subst r
    exact D04.constant_rank_smooth U g z k hU
      ((D04.smoothOn_iff_contDiffOn U g hU).mpr hg) hz hk
  · obtain ⟨s, rfl⟩ := WithTop.ne_top_iff_exists.mp h
    exact D04.constant_rank_finite s U g z k (ENat.natCast_le_natCast.mp hr) hU
      ((D04.crOn_iff_contDiffOn s U g hU).mpr hg) hz hk

/-- An original interior chart, expressed in the L² coordinate norm. -/
noncomputable def l2Chart {m : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (e : ModelChart m a M) :
    OpenPartialHomeomorph M (E m) :=
  (InteriorInverse.ambientChart e).transHomeomorph (toL2 m).toHomeomorph

@[simp] theorem l2Chart_apply {m : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (e : ModelChart m a M) (x : M) :
    l2Chart e x = toL2 m (e x).val := rfl

/-- Composing an interior chart with a Euclidean C^r diffeomorphism
produces compatible coordinates in the exact sense of the independent Spec. -/
theorem compatible_trans {m : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (r : ℕ∞) (S : SmoothManifold m a M)
    (e : ModelChart m a M) (he : e ∈ S.smoothStructure.val)
    (Φ : OpenPartialHomeomorph (E m) (E m))
    (hΦ : ContDiffOn ℝ r Φ Φ.source) (hΦi : ContDiffOn ℝ r Φ.symm Φ.target) :
    CompatibleCoordinates r S ((l2Chart e).trans Φ) := by
  let A := (toL2 m).toHomeomorph.transOpenPartialHomeomorph Φ
  refine ⟨e, he, A, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hΦ.comp (toL2 m).contDiff.contDiffOn (fun _ hx => hx)
  · exact (toL2 m).symm.contDiff.comp_contDiffOn hΦi
  · intro x hx
    exact hx.1
  · intro x hx
    exact ⟨hx.2, rfl⟩
  · intro z hz
    exact hz.1
  · intro z hz
    change (InteriorInverse.ambientChart e)
      ((InteriorInverse.ambientChart e).symm ((toL2 m).symm (Φ.symm z))) = _
    exact (InteriorInverse.ambientChart e).right_inv hz.2

/-- A single open Euclidean representative valid throughout a neighborhood.
The last clause bridges the intrinsic full differential and all three Jacobian
invariants, rather than identifying the two coordinate norm conventions. -/
theorem interior_representative {m n : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (r : ℕ∞) (hr : 1 ≤ r) (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (f : M → N) (hf : ManifoldContDiff r S.smoothStructure.val T.smoothStructure.val f)
    (p : M) (e : ModelChart m a M) (d : ModelChart n b N)
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
    (hp : p ∈ (l2Chart e).source) (hfp : f p ∈ (l2Chart d).source)
    (W : Set M) (hW : IsOpen W) (hpW : p ∈ W) :
    ∃ U : Set (E m), IsOpen U ∧ l2Chart e p ∈ U ∧
    ∃ g : E m → E n, ContDiffOn ℝ r g U ∧
      (∀ z ∈ U, z ∈ (l2Chart e).target ∧ (l2Chart e).symm z ∈ W ∧
        f ((l2Chart e).symm z) ∈ (l2Chart d).source ∧
        g z = l2Chart d (f ((l2Chart e).symm z))) ∧
      (∀ x ∈ (l2Chart e).source, l2Chart e x ∈ U →
        rankAt S T f x = Module.finrank ℝ (LinearMap.range (fderiv ℝ g (l2Chart e x)).toLinearMap) ∧
        (IsImmersionAt S T f x ↔ Function.Injective (fderiv ℝ g (l2Chart e x))) ∧
        (IsSubmersionAt S T f x ↔ Function.Surjective (fderiv ℝ g (l2Chart e x)))) := by
  let C := l2Chart e
  let D := l2Chart d
  obtain ⟨O, hO, hpO, g₀, hg₀, heq⟩ := (hf p).2 e he d hd hp.1 hfp.1
  obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp
    (heq.and (inter_mem (C.open_source.mem_nhds hp)
      (inter_mem ((hf p).1.preimage_mem_nhds (D.open_source.mem_nhds hfp)) (hW.mem_nhds hpW))))
  let U := (C.target ∩ C.symm ⁻¹' V) ∩ (toL2 m).symm ⁻¹' O
  have hU : IsOpen U := (C.symm.isOpen_inter_preimage hV).inter
    (hO.preimage (toL2 m).symm.continuous)
  have hpU : C p ∈ U := by
    refine ⟨⟨C.map_source hp, ?_⟩, ?_⟩
    · change C.symm (C p) ∈ V
      rwa [C.left_inv hp]
    · change (toL2 m).symm (toL2 m (e p).val) ∈ O
      rwa [ContinuousLinearEquiv.symm_apply_apply]
  let g : E m → E n := fun z => toL2 n (g₀ ((toL2 m).symm z))
  have hg : ContDiffOn ℝ r g U := (toL2 n).contDiff.comp_contDiffOn
    (hg₀.comp (toL2 m).symm.contDiff.contDiffOn (fun _ hz => hz.2))
  have hxV (x : M) (hx : x ∈ C.source) (hxu : C x ∈ U) : x ∈ V := by
    have h : C.symm (C x) ∈ V := hxu.1.2
    simpa only [C.left_inv hx] using h
  have hfeq (x : M) (hx : x ∈ V) : g (C x) = D (f x) := by
    change toL2 n (g₀ ((toL2 m).symm (toL2 m (e x).val))) = toL2 n (d (f x)).val
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact congrArg (toL2 n) (hVsub hx).1
  refine ⟨U, hU, hpU, g, hg, ?_, ?_⟩
  · intro z hz
    refine ⟨hz.1.1, (hVsub hz.1.2).2.2.2, (hVsub hz.1.2).2.2.1, ?_⟩
    have h := hfeq (C.symm z) hz.1.2
    rwa [C.right_inv hz.1.1] at h
  · intro x hx hxu
    have hxv := hxV x hx hxu
    have hfxD := (hVsub hxv).2.2.1
    have hox : (e x).val ∈ O := by
      have h : (toL2 m).symm (toL2 m (e x).val) ∈ O := hxu.2
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using h
    have hr0 : (r : ℕ∞ω) ≠ 0 := by
      exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by decide : (0 : ℕ∞) < 1) hr))
    have hg₀x := ((hg₀.contDiffAt (hO.mem_nhds hox)).differentiableAt hr0).hasFDerivAt
    have heqx : (fun y => g₀ (e y).val) =ᶠ[𝓝 x] (fun y => (d (f y)).val) := by
      filter_upwards [hV.mem_nhds hxv] with y hy
      exact (hVsub hy).1
    have hJ : chartDerivative e d f x = fderiv ℝ g₀ (e x).val :=
      FiniteRegularity.coordinateDerivative_eq e _ x hx.1 _ ⟨g₀, hg₀x, heqx⟩
    have hgd : HasFDerivAt g
        ((toL2 n).toContinuousLinearMap.comp
          ((fderiv ℝ g₀ (e x).val).comp (toL2 m).symm.toContinuousLinearMap)) (C x) := by
      have hi := (toL2 m).symm.hasFDerivAt (x := C x)
      have hg' : HasFDerivAt g₀ (fderiv ℝ g₀ (e x).val) ((toL2 m).symm (C x)) := by
        simpa only [C, l2Chart_apply, ContinuousLinearEquiv.symm_apply_apply] using hg₀x
      exact (toL2 n).hasFDerivAt.comp _ (hg'.comp _ hi)
    have hlin := MapClasses.linear_invariants (toL2 m).toLinearEquiv (toL2 n).toLinearEquiv
      (chartDerivative e d f x).toLinearMap (fderiv ℝ g (C x)).toLinearMap (by
        intro v
        rw [hJ, hgd.fderiv]
        simp)
    have hf1 := manifoldContDiff_of_le r 1 _ _ f hr hf
    have hi := MapClasses.chart_invariants S T f hf1 x e d he hd hx.1 hfxD.1
    exact ⟨hi.1.trans hlin.1, hi.2.1.trans hlin.2.1, hi.2.2.trans hlin.2.2⟩

/-- Transport the complete Euclidean normal form to actual manifold charts. -/
theorem normalForm_of_representative {m n : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (r : ℕ∞) (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (f : M → N) (p : M) (k : ℕ)
    (e : ModelChart m a M) (d : ModelChart n b N)
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
    (hp : p ∈ (l2Chart e).source) (hfp : f p ∈ (l2Chart d).source)
    (U : Set (E m)) (g : E m → E n)
    (hrep : ∀ z ∈ U, z ∈ (l2Chart e).target ∧
      f ((l2Chart e).symm z) ∈ (l2Chart d).source ∧
      g z = l2Chart d (f ((l2Chart e).symm z)))
    (hn : Specs.D04.C04.ConstantRank.RankNormalForm r U g (l2Chart e p) k) :
    NormalForm r S T f p k := by
  let C := l2Chart e
  let D := l2Chart d
  obtain ⟨Φ, Ψ, ha, hsub, hΦa, hfa, hΨa, hΦ, hΦi, hΨ, hΨi, hmap, hn⟩ := hn
  have hdata (x : M) (hx : x ∈ C.source) (hxu : C x ∈ U) :
      f x ∈ D.source ∧ g (C x) = D (f x) := by
    have h := (hrep (C x) hxu).2
    change f (C.symm (C x)) ∈ D.source ∧ g (C x) = D (f (C.symm (C x))) at h
    rwa [C.left_inv hx] at h
  have hpdata := hdata p hp (hsub ha)
  refine ⟨C.trans Φ, D.trans Ψ, compatible_trans r S e he Φ hΦ hΦi,
    compatible_trans r T d hd Ψ hΨ hΨi, ⟨hp, ha⟩, hΦa,
    ⟨hfp, by change D (f p) ∈ Ψ.source; rw [← hpdata.2]; exact hfa⟩, ?_, ?_, ?_⟩
  · change Ψ (D (f p)) = 0
    rw [← hpdata.2, hΨa]
  · intro x hx
    have h := hdata x hx.1 (hsub hx.2)
    refine ⟨h.1, ?_⟩
    change D (f x) ∈ Ψ.source
    rw [← h.2]
    exact hmap hx.2
  · intro u hu
    change Ψ (D (f (C.symm (Φ.symm u)))) = _
    rw [← (hrep (Φ.symm u) (hsub (Φ.map_target hu.1))).2.2, hn u hu.1]
    rfl

/-- The constant-rank theorem at interior source and target points. -/
theorem interior_constant_rank :
    Specs.SmoothManifolds.Ch03.InteriorConstantRank.interior_constant_rankType.{u,v} := by
  intro m n a b M N _ _ r hr S T f hf p hpi hfpi k hk
  obtain ⟨e, he, hp, hpei⟩ := hpi
  obtain ⟨d, hd, hfp, hfpei⟩ := hfpi
  have hpC : p ∈ (l2Chart e).source := ⟨hp, hpei⟩
  have hfpD : f p ∈ (l2Chart d).source := ⟨hfp, hfpei⟩
  obtain ⟨W, hW, hpW, hkrank⟩ := hk
  obtain ⟨U, hU, hpU, g, hg, hrep, hinv⟩ :=
    interior_representative r hr S T f hf p e d he hd hpC hfpD W hW hpW
  have hk' : Specs.D04.C04.ConstantRank.NeighborhoodRank g (l2Chart e p) k := by
    change ∀ᶠ z in 𝓝 (l2Chart e p),
      Module.finrank ℝ (LinearMap.range (fderiv ℝ g z).toLinearMap) = k
    filter_upwards [hU.mem_nhds hpU] with z hz
    have h := hrep z hz
    have hcz := (l2Chart e).right_inv h.1
    have hi := (hinv ((l2Chart e).symm z) ((l2Chart e).map_target h.1)
      (hcz.symm ▸ hz)).1
    rw [hcz] at hi
    exact hi.symm.trans (hkrank _ h.2.1)
  obtain ⟨hk0, hkmn, hn⟩ := euclidean_constant_rank r hr U hU g hg _ hpU k hk'
  exact ⟨hk0, hkmn, normalForm_of_representative r S T f p k e d he hd hpC hfpD U g
    (fun z hz => ⟨(hrep z hz).1, (hrep z hz).2.2⟩) hn⟩

/-- Injectivity at one point gives inclusion coordinates and persists on an
actual open neighborhood; constant rank is a conclusion here. -/
theorem interior_immersion :
    Specs.SmoothManifolds.Ch03.InteriorConstantRank.interior_immersionType.{u,v} := by
  intro m n a b M N _ _ r hr S T f hf p hpi hfpi himm
  obtain ⟨e, he, hp, hpei⟩ := hpi
  obtain ⟨d, hd, hfp, hfpei⟩ := hfpi
  have hpC : p ∈ (l2Chart e).source := ⟨hp, hpei⟩
  have hfpD : f p ∈ (l2Chart d).source := ⟨hfp, hfpei⟩
  obtain ⟨U, hU, hpU, g, hg, hrep, hinv⟩ :=
    interior_representative r hr S T f hf p e d he hd hpC hfpD univ isOpen_univ (mem_univ _)
  have hi : D04.ImmersionAt g (l2Chart e p) := (hinv p hpC hpU).2.1.mp himm
  obtain ⟨hmn, hn, hpers⟩ := D04.SubmersionImmersion.immersion_normal_form r
    (by exact_mod_cast hr) U hU g hg (l2Chart e p) hpU hi
  refine ⟨hmn, normalForm_of_representative r S T f p m e d he hd hpC hfpD U g
    (fun z hz => ⟨(hrep z hz).1, (hrep z hz).2.2⟩) hn, ?_⟩
  have hlocal : ∀ᶠ x in 𝓝 p, IsImmersionAt S T f x ∧ rankAt S T f x = m := by
    filter_upwards [(l2Chart e).open_source.mem_nhds hpC,
      (l2Chart e).continuousAt hpC |>.preimage_mem_nhds (hU.mem_nhds hpU),
      ((l2Chart e).continuousAt hpC).preimage_mem_nhds hpers] with x hx hxU hxi
    have h := hinv x hx hxU
    exact ⟨h.2.1.mpr hxi, h.1.trans (D04.SubmersionImmersion.rank_of_immersion g _ hxi)⟩
  obtain ⟨W, hWsub, hW, hpW⟩ := mem_nhds_iff.mp hlocal
  exact ⟨W, hW, hpW, fun x hx => hWsub hx⟩

/-- Surjectivity at one point gives projection coordinates and persists on
an actual open neighborhood, including a zero-dimensional target. -/
theorem interior_submersion :
    Specs.SmoothManifolds.Ch03.InteriorConstantRank.interior_submersionType.{u,v} := by
  intro m n a b M N _ _ r hr S T f hf p hpi hfpi hsubm
  obtain ⟨e, he, hp, hpei⟩ := hpi
  obtain ⟨d, hd, hfp, hfpei⟩ := hfpi
  have hpC : p ∈ (l2Chart e).source := ⟨hp, hpei⟩
  have hfpD : f p ∈ (l2Chart d).source := ⟨hfp, hfpei⟩
  obtain ⟨U, hU, hpU, g, hg, hrep, hinv⟩ :=
    interior_representative r hr S T f hf p e d he hd hpC hfpD univ isOpen_univ (mem_univ _)
  have hi : D04.SubmersionAt g (l2Chart e p) := (hinv p hpC hpU).2.2.mp hsubm
  obtain ⟨hnm, hn, hpers⟩ := D04.SubmersionImmersion.submersion_normal_form r
    (by exact_mod_cast hr) U hU g hg (l2Chart e p) hpU hi
  refine ⟨hnm, normalForm_of_representative r S T f p n e d he hd hpC hfpD U g
    (fun z hz => ⟨(hrep z hz).1, (hrep z hz).2.2⟩) hn, ?_⟩
  have hlocal : ∀ᶠ x in 𝓝 p, IsSubmersionAt S T f x ∧ rankAt S T f x = n := by
    filter_upwards [(l2Chart e).open_source.mem_nhds hpC,
      (l2Chart e).continuousAt hpC |>.preimage_mem_nhds (hU.mem_nhds hpU),
      ((l2Chart e).continuousAt hpC).preimage_mem_nhds hpers] with x hx hxU hxi
    have h := hinv x hx hxU
    exact ⟨h.2.2.mpr hxi, h.1.trans (D04.SubmersionImmersion.rank_of_submersion g _ hxi)⟩
  obtain ⟨W, hWsub, hW, hpW⟩ := mem_nhds_iff.mp hlocal
  exact ⟨W, hW, hpW, fun x hx => hWsub hx⟩

end SmoothManifolds.InteriorConstantRank
