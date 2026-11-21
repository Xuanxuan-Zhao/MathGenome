import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.BoundaryInverse
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.InteriorInverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace SmoothManifolds.BoundaryInverse
open ModelData AtlasData MapData BoundaryData FiniteRegularityData BoundaryInverseData Set Filter
open scoped Topology ContDiff

/-- No open ambient neighborhood of a face point lies in the half-space. -/
theorem no_open_neighborhood_in_halfSpace {n : ℕ} (p : HalfSpace (n + 1))
    (hp : p.val (Fin.last n) = 0) (W : Set (Euclidean (n + 1)))
    (hW : IsOpen W) (hpW : p.val ∈ W) : ¬ W ⊆ halfSpaceSet (n + 1) := by
  intro hsub
  have hi : p.val ∈ interior (halfSpaceSet (n + 1)) :=
    mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hW.mem_nhds hpW) hsub)
  have hn := (mem_modelFace_iff_not_mem_interior (n := n + 1) (kind := .halfSpace) p).mp hp
  exact hn hi

/-- The inclusion cannot map any source subset onto an open target neighborhood
of a face point, even without continuity assumptions on that subset. -/
theorem inclusion_not_locally_onto {n : ℕ} (p : HalfSpace (n + 1))
    (hp : p.val (Fin.last n) = 0) (V : Set (HalfSpace (n + 1))) :
    ¬ ∃ W : Set (Euclidean (n + 1)), IsOpen W ∧ p.val ∈ W ∧
      W ⊆ Subtype.val '' V := by
  rintro ⟨W, hW, hpW, hsub⟩
  apply no_open_neighborhood_in_halfSpace p hp W hW hpW
  rintro y hy
  obtain ⟨x, _, rfl⟩ := hsub hy
  exact x.property

/-- There is no local homeomorphism agreeing with inclusion at a face point. -/
theorem inclusion_not_local_homeomorph {n : ℕ} (p : HalfSpace (n + 1))
    (hp : p.val (Fin.last n) = 0) :
    ¬ ∃ h : OpenPartialHomeomorph (HalfSpace (n + 1)) (Euclidean (n + 1)),
      p ∈ h.source ∧ EqOn h Subtype.val h.source := by
  rintro ⟨h, hph, heq⟩
  apply inclusion_not_locally_onto p hp h.source
  refine ⟨h.target, h.open_target, ?_, ?_⟩
  · rw [← heq hph]; exact h.map_source hph
  · intro y hy
    exact ⟨h.symm y, h.map_target hy, (heq (h.map_target hy)).symm.trans (h.right_inv hy)⟩

/-- In fact inclusion has no set-theoretic section on an open neighborhood. -/
theorem inclusion_no_local_section {n : ℕ} (p : HalfSpace (n + 1))
    (hp : p.val (Fin.last n) = 0) :
    ¬ ∃ (W : Set (Euclidean (n + 1))) (s : W → HalfSpace (n + 1)),
      IsOpen W ∧ p.val ∈ W ∧ ∀ y : W, (s y).val = y.val := by
  rintro ⟨W, s, hW, hpW, hs⟩
  apply no_open_neighborhood_in_halfSpace p hp W hW hpW
  intro y hy
  have hh := (s ⟨y, hy⟩).property
  rwa [hs ⟨y, hy⟩] at hh

/-- The derivative of a boundary-preserving ambient germ has a positive
normal row. Only differentiability at the face point is needed here. -/
theorem normal_derivative_positive {n : ℕ}
    (F : Euclidean (n + 1) → Euclidean (n + 1)) (p : Euclidean (n + 1))
    (hp : p (Fin.last n) = 0) (L : Euclidean (n + 1) →L[ℝ] Euclidean (n + 1))
    (hL : HasFDerivAt F L p) (hsur : Function.Surjective L)
    (hface : ∀ᶠ x in 𝓝 p, x (Fin.last n) = 0 → F x (Fin.last n) = 0)
    (hhalf : ∀ᶠ x in 𝓝 p, 0 ≤ x (Fin.last n) → 0 ≤ F x (Fin.last n)) :
    ∃ c : ℝ, 0 < c ∧ ∀ v, L v (Fin.last n) = c * v (Fin.last n) := by
  let j := Fin.last n
  let normal : Euclidean (n + 1) := Pi.single j 1
  have hn : normal j = 1 := by simp [normal]
  have hFp : F p j = 0 := Filter.Eventually.self_of_nhds hface hp
  have hline (v : Euclidean (n + 1)) :
      HasDerivAt (fun t : ℝ => F (p + t • v) j) (L v j) 0 := by
    have hv : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p)
    have hbase : HasFDerivAt F L (p + (0 : ℝ) • v) := by simpa using hL
    exact ((ContinuousLinearMap.proj j : Euclidean (n + 1) →L[ℝ] ℝ).hasFDerivAt.comp _ hbase).comp_hasDerivAt 0 hv
  have htangent (v : Euclidean (n + 1)) (hv : v j = 0) : L v j = 0 := by
    have ht : Tendsto (fun t : ℝ => p + t • v) (𝓝 0) (𝓝 p) := by
      have hcont : Continuous (fun t : ℝ => p + t • v) := by fun_prop
      simpa using hcont.tendsto (0 : ℝ)
    have heq : (fun t : ℝ => F (p + t • v) j) =ᶠ[𝓝 0] (fun _ => (0 : ℝ)) := by
      filter_upwards [ht.eventually hface] with t h
      exact h (by simp [Pi.add_apply, Pi.smul_apply, hp, hv, j])
    exact ((hline v).congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const 0 0)
  let c := L normal j
  have hrow (v : Euclidean (n + 1)) : L v j = c * v j := by
    have ht := htangent (v - v j • normal) (by simp [hn])
    simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at ht
    dsimp [c]
    nlinarith
  have hc0 : 0 ≤ c := by
    have ht : Tendsto (fun t : ℝ => p + t • normal) (𝓝 0) (𝓝 p) := by
      have hcont : Continuous (fun t : ℝ => p + t • normal) := by fun_prop
      simpa using hcont.tendsto (0 : ℝ)
    apply ge_of_tendsto (hline normal).tendsto_slope_zero_right
    filter_upwards [(ht.eventually hhalf).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ht hpos
    simp only [zero_add, zero_smul, add_zero, hFp, sub_zero, smul_eq_mul]
    apply mul_nonneg (inv_nonneg.mpr (le_of_lt hpos))
    exact ht (by simpa [Pi.add_apply, Pi.smul_apply, hp, hn, j] using le_of_lt hpos)
  have hc : c ≠ 0 := by
    intro hc
    obtain ⟨v, hv⟩ := hsur (fun _ => 1)
    have h := hrow v
    rw [hc, zero_mul, hv] at h
    exact one_ne_zero h
  exact ⟨c, lt_of_le_of_ne hc0 hc.symm, hrow⟩

/-- A C¹ ambient map with invertible differential, preserving the half-space
and its face locally, preserves the sign of its normal coordinate locally. -/
theorem normal_sign_near {n : ℕ}
    (r : ℕ∞) (hr : 1 ≤ r)
    (F : Euclidean (n + 1) → Euclidean (n + 1)) (U : Set (Euclidean (n + 1)))
    (hU : IsOpen U) (hF : ContDiffOn ℝ r F U) (p : Euclidean (n + 1)) (hpU : p ∈ U)
    (hp : p (Fin.last n) = 0) (hsur : Function.Surjective (fderiv ℝ F p))
    (hface : ∀ᶠ x in 𝓝 p, x (Fin.last n) = 0 → F x (Fin.last n) = 0)
    (hhalf : ∀ᶠ x in 𝓝 p, 0 ≤ x (Fin.last n) → 0 ≤ F x (Fin.last n)) :
    ∀ᶠ x in 𝓝 p, (0 ≤ F x (Fin.last n) ↔ 0 ≤ x (Fin.last n)) := by
  let j := Fin.last n
  let normal : Euclidean (n + 1) := Pi.single j 1
  have hr0 : (r : ℕ∞ω) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by decide : (0 : ℕ∞) < 1) hr))
  have hd := ((hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt hr0).hasFDerivAt
  obtain ⟨c, hc, hrow⟩ := normal_derivative_positive F p hp _ hd hsur hface hhalf
  have hpos : ∀ᶠ x in 𝓝 p, 0 < fderiv ℝ F x normal j := by
    have hcont := ((hF.continuousOn_fderiv_of_isOpen hU (by exact_mod_cast hr)).continuousAt
      (hU.mem_nhds hpU)).clm_apply (continuousAt_const (y := normal))
    have hcont' := (continuous_apply j).continuousAt.comp hcont
    apply hcont'.eventually (Ioi_mem_nhds _)
    change 0 < fderiv ℝ F p normal (Fin.last n)
    rw [hrow]
    simpa [normal, j] using hc
  obtain ⟨δ, hδ, hδall⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (hU.mem_nhds hpU) (Filter.Eventually.and hface hpos))
  filter_upwards [Metric.ball_mem_nhds p hδ] with x hx
  let q : ℝ → Euclidean (n + 1) := fun t => Function.update x j t
  have hq (t : ℝ) (ht : t ∈ Ioo (-δ) δ) : q t ∈ Metric.ball p δ := by
    apply (dist_pi_lt_iff hδ).mpr
    intro i
    by_cases hi : i = j
    · subst i
      simpa [q, hp, j, Real.dist_eq, abs_lt] using ht
    · simpa [q, Function.update_of_ne hi] using (dist_pi_lt_iff hδ).mp hx i
  have hqd (t : ℝ) : HasDerivAt q normal t := by
    have heq : q = (fun s : ℝ => x + (s - x j) • normal) := by
      funext s; ext i
      by_cases hi : i = j
      · subst i; simp [q, normal]
      · simp [q, normal, Function.update_of_ne hi, Pi.single_eq_of_ne hi]
    rw [heq]
    simpa using (((hasDerivAt_id t).sub_const (x j)).smul_const normal).const_add x
  have hder (t : ℝ) (ht : t ∈ Ioo (-δ) δ) :
      HasDerivAt (fun s => F (q s) j) (fderiv ℝ F (q t) normal j) t := by
    have hdt := ((hF.contDiffAt (hU.mem_nhds (hδall (hq t ht)).1)).differentiableAt hr0).hasFDerivAt
    exact ((ContinuousLinearMap.proj j : Euclidean (n + 1) →L[ℝ] ℝ).hasFDerivAt.comp _ hdt).comp_hasDerivAt t (hqd t)
  have hmono : StrictMonoOn (fun t => F (q t) j) (Ioo (-δ) δ) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    · intro t ht; exact (hder t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [(hder t (interior_subset ht)).deriv]
      exact (hδall (hq t (interior_subset ht))).2.2
  have hzero : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_neg_iff_pos.mpr hδ, hδ⟩
  have hq0 : F (q 0) j = 0 := (hδall (hq 0 hzero)).2.1 (by simp [q, j])
  have hxj : x j ∈ Ioo (-δ) δ := by
    simpa [Real.dist_eq, hp, j, abs_lt] using (dist_pi_lt_iff hδ).mp hx j
  have hqx : q (x j) = x := Function.update_eq_self j x
  have hcmp := hmono.le_iff_le hzero hxj
  rw [hq0, hqx] at hcmp
  exact hcmp

/-- Restrict a partial homeomorphism to an invariant subset, keeping the
subspace topology even when that subset is closed rather than open. -/
noncomputable def restrictInvariant {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X X) (s : Set X) (hs : e.IsImage s s) (p : s) :
    OpenPartialHomeomorph s s := by
  classical
  let f : s → s := fun x => if hx : e x.val ∈ s then ⟨e x.val, hx⟩ else p
  let g : s → s := fun x => if hx : e.symm x.val ∈ s then ⟨e.symm x.val, hx⟩ else p
  have hf (x : s) (hx : x.val ∈ e.source) : (f x).val = e x.val := by
    simp [f, (hs hx).mpr x.property]
  have hg (x : s) (hx : x.val ∈ e.target) : (g x).val = e.symm x.val := by
    simp [g, (hs.symm hx).mpr x.property]
  exact {
    toFun := f
    invFun := g
    source := Subtype.val ⁻¹' e.source
    target := Subtype.val ⁻¹' e.target
    map_source' := fun x hx => by change (f x).val ∈ e.target; rw [hf x hx]; exact e.map_source hx
    map_target' := fun x hx => by change (g x).val ∈ e.source; rw [hg x hx]; exact e.map_target hx
    left_inv' := fun x hx => by
      apply Subtype.ext
      rw [hg (f x) (by rw [hf x hx]; exact e.map_source hx), hf x hx, e.left_inv hx]
    right_inv' := fun x hx => by
      apply Subtype.ext
      rw [hf (g x) (by rw [hg x hx]; exact e.map_target hx), hg x hx, e.right_inv hx]
    open_source := e.open_source.preimage continuous_subtype_val
    open_target := e.open_target.preimage continuous_subtype_val
    continuousOn_toFun := Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
      ((e.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hx => hx)).congr hf)
    continuousOn_invFun := Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
      ((e.symm.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hx => hx)).congr hg) }

theorem restrictInvariant_val {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X X) (s : Set X) (hs : e.IsImage s s) (p : s)
    (x : s) (hx : x.val ∈ e.source) :
    (restrictInvariant e s hs p x).val = e x.val := by
  classical
  simp [restrictInvariant, (hs hx).mpr x.property]

theorem restrictInvariant_symm_val {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X X) (s : Set X) (hs : e.IsImage s s) (p : s)
    (x : s) (hx : x.val ∈ e.target) :
    ((restrictInvariant e s hs p).symm x).val = e.symm x.val := by
  classical
  simp [restrictInvariant, (hs.symm hx).mpr x.property]

universe u v

/-- The boundary inverse theorem in positive-dimensional half-space charts. -/
theorem boundary_inverse_halfSpace {n : ℕ} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N] (r : ℕ∞) (hr : 1 ≤ r)
    (S : SmoothManifold (n + 1) .halfSpace M) (T : SmoothManifold (n + 1) .halfSpace N)
    (f : M → N) (hf : ManifoldContDiff r S.smoothStructure.val T.smoothStructure.val f)
    (p : M) (hp : p ∈ intrinsicBoundary S) (_hfp : f p ∈ intrinsicBoundary T)
    (hbd : ∀ᶠ x in 𝓝 p, x ∈ intrinsicBoundary S → f x ∈ intrinsicBoundary T)
    (F : FiberModel S.smoothStructure.val p) (G : FiberModel T.smoothStructure.val (f p)) :
    letI := F.group; letI := F.module; letI := G.group; letI := G.module
    ∀ L : CoordinateTangent S.smoothStructure.val p →ₗ[ℝ]
      CoordinateTangent T.smoothStructure.val (f p),
    IsCoordinateDifferential f p F G L → Function.Bijective L →
    ∃ h : OpenPartialHomeomorph M N,
      p ∈ h.source ∧ EqOn h f h.source ∧
      ManifoldContDiffOn r S.smoothStructure.val T.smoothStructure.val f h.source ∧
      ManifoldContDiffOn r T.smoothStructure.val S.smoothStructure.val h.symm h.target := by
  letI := F.group; letI := F.module; letI := G.group; letI := G.module
  intro L hL hbij
  obtain ⟨e, he, hpe⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨d, hd, hfpd⟩ := T.smoothStructure.property.1.1 (f p)
  have hpface : (e p).val (Fin.last n) = 0 :=
    (intrinsicBoundary_iff_chart S e he p hpe).mp hp
  obtain ⟨U, hU, hepU, g, hg, heq⟩ := (hf p).2 e he d hd hpe hfpd
  have hr0 : (r : ℕ∞ω) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by decide : (0 : ℕ∞) < 1) hr))
  have hdg := ((hg.contDiffAt (hU.mem_nhds hepU)).differentiableAt hr0).hasFDerivAt
  have hderiv : chartDerivative e d f p = fderiv ℝ g (e p).val :=
    FiniteRegularity.coordinateDerivative_eq e _ p hpe _ ⟨g, hdg, heq⟩
  have hlin := MapClasses.differential_chart_invariants S T f p F G e d he hd hpe hfpd L hL
  have hgBij : Function.Bijective (fderiv ℝ g (e p).val) := by
    rw [← hderiv]
    exact ⟨hlin.2.1.mp hbij.1, hlin.2.2.mp hbij.2⟩
  have ht : Tendsto e.symm (𝓝 (e p)) (𝓝 p) := by
    simpa only [ContinuousAt, e.left_inv hpe] using e.symm.continuousAt (e.map_source hpe)
  have hmodel : ∀ᶠ z : ModelSpace (n + 1) .halfSpace in 𝓝 (e p),
      (0 ≤ g z.val (Fin.last n)) ∧ (z.val (Fin.last n) = 0 → g z.val (Fin.last n) = 0) := by
    filter_upwards [heq.comp_tendsto ht, ht.eventually hbd,
      e.open_target.mem_nhds (e.map_source hpe),
      ht.eventually ((hf p).1.preimage_mem_nhds (d.open_source.mem_nhds hfpd))]
      with z hz hzb hzt hzfd
    have hz' : g z.val = (d (f (e.symm z))).val := by
      change g (e (e.symm z)).val = (d (f (e.symm z))).val at hz
      rwa [e.right_inv hzt] at hz
    rw [hz']
    refine ⟨(d (f (e.symm z))).property, ?_⟩
    intro hzface
    apply (intrinsicBoundary_iff_chart T d hd _ hzfd).mp
    apply hzb
    apply (intrinsicBoundary_iff_chart S e he _ (e.map_target hzt)).mpr
    change (e (e.symm z)).val (Fin.last n) = 0
    rwa [e.right_inv hzt]
  have hamb : ∀ᶠ x in 𝓝 (e p).val,
      x ∈ halfSpaceSet (n + 1) →
      (0 ≤ g x (Fin.last n)) ∧ (x (Fin.last n) = 0 → g x (Fin.last n) = 0) := by
    apply eventually_nhdsWithin_iff.mp
    have hm : map (Subtype.val : ModelSpace (n + 1) .halfSpace → Euclidean (n + 1))
        (𝓝 (e p)) = 𝓝[halfSpaceSet (n + 1)] (e p).val := map_nhds_subtype_val _
    rw [← hm]
    exact hmodel
  have hhalf : ∀ᶠ x in 𝓝 (e p).val,
      0 ≤ x (Fin.last n) → 0 ≤ g x (Fin.last n) := by
    filter_upwards [hamb] with x hx
    exact fun h => (hx h).1
  have hface : ∀ᶠ x in 𝓝 (e p).val,
      x (Fin.last n) = 0 → g x (Fin.last n) = 0 := by
    filter_upwards [hamb] with x hx
    exact fun h => (hx (by change 0 ≤ x (Fin.last n); rw [h])).2 h
  obtain ⟨W, hWsub, hW, hpW⟩ := mem_nhds_iff.mp
    (normal_sign_near r hr g U hU hg (e p).val hepU hpface hgBij.2 hface hhalf)
  obtain ⟨j₀, hpj₀, hj₀, hji₀⟩ := InteriorInverse.euclidean_inverse r hr g U hU hg
    (e p).val hepU (fderiv ℝ g (e p).val) hdg hgBij
  let j := j₀.restrOpen W hW
  have hpj : (e p).val ∈ j.source := ⟨hpj₀, hpW⟩
  have hj : (j : Euclidean (n + 1) → Euclidean (n + 1)) = g := hj₀
  have hji : ContDiffOn ℝ r j.symm j.target := hji₀.mono inter_subset_left
  have hsame : j.IsImage (halfSpaceSet (n + 1)) (halfSpaceSet (n + 1)) := by
    intro x hx
    change 0 ≤ j x (Fin.last n) ↔ 0 ≤ x (Fin.last n)
    rw [hj]
    exact hWsub hx.2
  let k := restrictInvariant j (halfSpaceSet (n + 1)) hsame (e p)
  have hkval (x : ModelSpace (n + 1) .halfSpace) (hx : x ∈ k.source) :
      (k x).val = g x.val := by
    rw [restrictInvariant_val j _ hsame (e p) x hx]
    exact congrFun hj x.val
  obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp
    (heq.and ((hf p).1.preimage_mem_nhds (d.open_source.mem_nhds hfpd)))
  let h₀ := (e.trans k).trans d.symm
  let h := h₀.restrOpen V hV
  have hkp : k (e p) = d (f p) := by
    apply Subtype.ext
    exact (hkval (e p) hpj).trans heq.eq_of_nhds
  have hph₀ : p ∈ h₀.source := by
    refine ⟨⟨hpe, hpj⟩, ?_⟩
    change k (e p) ∈ d.target
    rw [hkp]
    exact d.map_source hfpd
  have hforward : EqOn h f h.source := by
    intro x hx
    have hxV := hVsub hx.2
    change d.symm (k (e x)) = f x
    have hgx : k (e x) = d (f x) := by
      apply Subtype.ext
      exact (hkval (e x) hx.1.1.2).trans hxV.1
    rw [hgx, d.left_inv hxV.2]
  have hinv_coords (y : N) (hy : y ∈ h.target) :
      (e (h.symm y)).val = j.symm (d y).val := by
    have hyE : k.symm (d y) ∈ e.target := hy.1.2.2
    change (e (e.symm (k.symm (d y)))).val = _
    rw [e.right_inv hyE]
    exact restrictInvariant_symm_val j _ hsame (e p) (d y) hy.1.2.1
  refine ⟨h, ⟨hph₀, hpV⟩, hforward, (fun x _ => hf x), ?_⟩
  intro y hy
  apply (manifoldContDiffAt_iff_oneChart r _ _
    (InteriorInverse.smoothAtlas_contDiff T r) (InteriorInverse.smoothAtlas_contDiff S r)
    h.symm y).mpr
  have hsy := h.map_target hy
  refine ⟨h.symm.continuousAt hy, d, hd, e, he, hy.1.1, hsy.1.1.1, ?_⟩
  refine ⟨j.target, j.open_target, hy.1.2.1, j.symm, hji, ?_⟩
  filter_upwards [h.open_target.mem_nhds hy] with z hz
  exact (hinv_coords z hz).symm

/-- The full boundary inverse theorem, including the vacuous dimension-zero
and Euclidean-model cases. Boundary membership itself forces positive dimension. -/
theorem boundary_inverse :
    Specs.SmoothManifolds.Ch03.BoundaryInverse.boundary_inverseType.{u,v} := by
  intro n a b M N _ _ r hr S T f hf p hp hfp hbd F G
  cases n with
  | zero => simp only [intrinsicBoundary_zero S, mem_empty_iff_false] at hp
  | succ n =>
    cases a with
    | euclidean => simp only [intrinsicBoundary_euclidean S, mem_empty_iff_false] at hp
    | halfSpace =>
      cases b with
      | euclidean => simp only [intrinsicBoundary_euclidean T, mem_empty_iff_false] at hfp
      | halfSpace => exact boundary_inverse_halfSpace r hr S T f hf p hp hfp hbd F G

/-- A global chart with identity ambient transition generates a standard
smooth manifold. The chart is retained in its maximal smooth atlas. -/
theorem smoothManifold_of_globalChart {n : ℕ} {a : ModelKind} {M : Type*}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    (e : ModelChart n a M) (he : e.source = univ) :
    ∃ S : SmoothManifold n a M, e ∈ S.smoothStructure.val := by
  let A : Set (ModelChart n a M) := {e}
  have hA : IsContDiffAtlas (⊤ : ℕ∞) A := by
    constructor
    · intro p; exact ⟨e, mem_singleton _, he ▸ mem_univ p⟩
    · intro c hc d hd
      have hc' : c = e := hc
      have hd' : d = e := hd
      subst c; subst d
      constructor
      · intro x hx
        refine ⟨univ, isOpen_univ, mem_univ _, id, contDiffOn_id, ?_⟩
        intro y hy _
        change y.val = (e (e.symm y)).val
        exact congrArg Subtype.val (e.right_inv hy.1).symm
      · intro x hx
        refine ⟨univ, isOpen_univ, mem_univ _, id, contDiffOn_id, ?_⟩
        intro y hy _
        change y.val = (e (e.symm y)).val
        exact congrArg Subtype.val (e.right_inv hy.1).symm
  exact ⟨⟨⟨inferInstance, inferInstance, A, hA.1⟩,
    ⟨maximalExtension (⊤ : ℕ∞) A, maximalExtension_isMaximal hA⟩⟩,
    subset_maximalExtension hA (mem_singleton _)⟩

/-- The standard inclusion is smooth in every compatible chart, and its
full coordinate derivative in the global charts is the ambient identity. -/
theorem inclusion_smooth_and_derivative (n : ℕ)
    (S : SmoothManifold n .halfSpace (HalfSpace n))
    (T : SmoothManifold n .euclidean (Euclidean n))
    (hS : OpenPartialHomeomorph.refl (HalfSpace n) ∈ S.smoothStructure.val)
    (hT : euclideanChart n ∈ T.smoothStructure.val) :
    IsSmoothMap S T Subtype.val ∧
    ∀ p : HalfSpace n,
      chartDerivative (a := .halfSpace) (b := .euclidean) (OpenPartialHomeomorph.refl (HalfSpace n)) (euclideanChart n)
        Subtype.val p = ContinuousLinearMap.id ℝ (Euclidean n) := by
  constructor
  · intro p
    apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
      S.smoothStructure.property.1 T.smoothStructure.property.1 Subtype.val p).mpr
    exact ⟨continuous_subtype_val.continuousAt, _, hS, _, hT, mem_univ _, mem_univ _,
      univ, isOpen_univ, mem_univ _, id, contDiffOn_id, Filter.Eventually.of_forall (fun _ => rfl)⟩
  · intro p
    exact FiniteRegularity.coordinateDerivative_eq _ _ p (mem_univ _) _
      ⟨id, hasFDerivAt_id p.val, Filter.Eventually.of_forall (fun _ => rfl)⟩

/-- All the advertised failures occur for the smooth inclusion, although its
actual full tangent differential is invertible at every point. -/
theorem halfSpace_inclusion_counterexample :
    Specs.SmoothManifolds.Ch03.BoundaryInverse.halfSpace_inclusion_counterexampleType := by
  intro n
  obtain ⟨S, hS⟩ := smoothManifold_of_globalChart
    (OpenPartialHomeomorph.refl (ModelSpace (n + 1) .halfSpace)) rfl
  obtain ⟨T, hT⟩ := smoothManifold_of_globalChart (euclideanChart (n + 1)) rfl
  have hf := inclusion_smooth_and_derivative (n + 1) S T hS hT
  refine ⟨S, T, hS, hT, hf.1, ?_, ?_, ?_⟩
  · intro p
    have hf1 := manifoldContDiff_of_le (⊤ : ℕ∞) 1 _ _ _ (by simp) hf.1
    obtain ⟨F, G, L, hL⟩ := MapClasses.exists_differential_model S T Subtype.val hf1 p
    letI := F.group; letI := F.module; letI := G.group; letI := G.module
    refine ⟨F, G, L, hL, ?_⟩
    have hi := MapClasses.differential_chart_invariants S T Subtype.val p F G
      (OpenPartialHomeomorph.refl (HalfSpace (n + 1))) (euclideanChart (n + 1))
      hS hT (mem_univ _) (mem_univ _) L hL
    have hder := hf.2 p
    have hinj : Function.Injective (chartDerivative (a := .halfSpace) (b := .euclidean)
        (OpenPartialHomeomorph.refl (HalfSpace (n + 1))) (euclideanChart (n + 1)) Subtype.val p) := by
      rw [hder]; exact Function.injective_id
    have hsur : Function.Surjective (chartDerivative (a := .halfSpace) (b := .euclidean)
        (OpenPartialHomeomorph.refl (HalfSpace (n + 1))) (euclideanChart (n + 1)) Subtype.val p) := by
      rw [hder]; exact Function.surjective_id
    exact ⟨hi.2.1.mpr hinj, hi.2.2.mpr hsur⟩
  · intro p
    exact intrinsicBoundary_iff_chart S _ hS p (mem_univ _)
  · intro p hp
    exact ⟨inclusion_not_local_homeomorph p hp, inclusion_not_locally_onto p hp,
      inclusion_no_local_section p hp⟩

end SmoothManifolds.BoundaryInverse
