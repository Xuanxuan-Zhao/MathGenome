import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.CircularRetainedDisplay
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.CircularCornerRounding
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.FiniteCircularArcs
import Mathlib.Order.Interval.Set.Disjoint

noncomputable section
open Set Metric Filter Complex
open scoped Topology ContDiff NNReal

namespace D12Complex.CircularRetainedDisplay
open CircularExhaustion CircularCornerRounding

/-- Every actual tip is inside its supplied chart target. -/
lemma tip_subset_target {U : Set ℂ} {J : Finset ℂ} (H : Charts U J)
    {ε : ℝ} (hε : 0 < ε) (hεR : ε < H.radius) :
    ∀ p ∈ J, sectorTip ε (H.angle p) ⊆ (H.e p).target := by
  intro p hp
  exact (sectorTip_subset_closedBall hε).trans
    ((closedBall_subset_closedBall hεR.le).trans (H.target_ball p hp))

/-- The accepted surgery theorem applies to exactly the domain in the interface. -/
lemma surgery_defining_functions {U : Set ℂ} {J : Finset ℂ}
    (hgeom : RoundingGeometry U J) (H : Charts U J) {ε : ℝ}
    (hε : 0 < ε) (hεR : ε < H.radius) :
    HasC1DefiningFunctions (surgeryDomain H ε) := by
  exact (finite_chart_surgery hgeom H.e H.angle hε H.angles H.side H.smooth
    H.normalized H.disjoint (tip_subset_target H hε hεR)).2.2.1

/-- The finite endpoint set is finite, including an empty index set. -/
lemma endpointSet_finite {m : ℕ} (γ : Fin m → ℝ → ℂ) (a b : Fin m → ℝ) :
    (endpointSet γ a b).Finite :=
  (Set.finite_range _).union (Set.finite_range _)

/-- Open injectivity and disjoint open images put all nontrivial overlaps
among the actual finite endpoint images. -/
lemma overlaps_at_endpoints {m : ℕ} (γ : Fin m → ℝ → ℂ) (a b : Fin m → ℝ)
    (hinj : ∀ i, InjOn (γ i) (Ioo (a i) (b i)))
    (hdisj : ∀ i j, i ≠ j → Disjoint (γ i '' Ioo (a i) (b i))
      (γ j '' Ioo (a j) (b j))) :
    ∀ i j s t, s ∈ Icc (a i) (b i) → t ∈ Icc (a j) (b j) →
      γ i s = γ j t → (i ≠ j ∨ s ≠ t) → γ i s ∈ endpointSet γ a b := by
  intro i j s t hs ht he hne
  by_cases hsa : s = a i
  · exact Or.inl ⟨i, by rw [hsa]⟩
  by_cases hsb : s = b i
  · exact Or.inr ⟨i, by rw [hsb]⟩
  by_cases hta : t = a j
  · exact Or.inl ⟨j, by simpa only [hta] using he.symm⟩
  by_cases htb : t = b j
  · exact Or.inr ⟨j, by simpa only [htb] using he.symm⟩
  have hs' : s ∈ Ioo (a i) (b i) := ⟨lt_of_le_of_ne hs.1 (Ne.symm hsa), lt_of_le_of_ne hs.2 hsb⟩
  have ht' : t ∈ Ioo (a j) (b j) := ⟨lt_of_le_of_ne ht.1 (Ne.symm hta), lt_of_le_of_ne ht.2 htb⟩
  by_cases hij : i = j
  · subst j
    exact (hne.elim (fun h => h rfl) (fun h => h (hinj i hs' ht' he))).elim
  · exact (Set.disjoint_left.mp (hdisj i j hij) ⟨s, hs', rfl⟩ ⟨t, ht', he.symm⟩).elim



/-- A chart and its inverse preserve the actual nonzero derivative of a
regular curve, on the ordinary preimage of the chart target. -/
lemma chart_inverse_curve_regular (e : OpenPartialHomeomorph ℂ ℂ)
    (hc : ContDiffOn ℝ 1 e e.source)
    (hci : ContDiffOn ℝ 1 e.symm e.target)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hdf : ∀ t, deriv f t ≠ 0) :
    ContDiffOn ℝ 1 (fun t => e.symm (f t)) (f ⁻¹' e.target) ∧
    ∀ t ∈ f ⁻¹' e.target, deriv (fun s => e.symm (f s)) t ≠ 0 := by
  have hO : IsOpen (f ⁻¹' e.target) := e.open_target.preimage hf.continuous
  have hcomp : ContDiffOn ℝ 1 (fun t => e.symm (f t)) (f ⁻¹' e.target) :=
    hci.comp hf.contDiffOn (fun _ ht => ht)
  refine ⟨hcomp, ?_⟩
  intro t ht
  have hdc := (hcomp.contDiffAt (hO.mem_nhds ht)).differentiableAt (by norm_num)
  have hec := (hc.contDiffAt (e.open_source.mem_nhds (e.map_target ht))).differentiableAt
    (by norm_num)
  have hd := hec.hasFDerivAt.comp_hasDerivAt t hdc.hasDerivAt
  have heq : f =ᶠ[𝓝 t] (e ∘ (fun s => e.symm (f s))) :=
    Filter.mem_of_superset (hO.mem_nhds ht) (fun s hs => (e.right_inv hs).symm)
  have hderiv := (hd.congr_of_eventuallyEq heq).deriv
  intro hzero
  apply hdf t
  rw [hderiv, hzero, map_zero]

/-- Restricting the pullback of a genuine embedding to parameters landing in
the target remains a genuine topological embedding. -/
lemma chart_inverse_curve_embedding (e : OpenPartialHomeomorph ℂ ℂ)
    (f : ℝ → ℂ) (hf : Topology.IsEmbedding f)
    (T : Set ℝ) (hT : ∀ t ∈ T, f t ∈ e.target) :
    Topology.IsEmbedding (fun t : T => e.symm (f t)) := by
  have hfT : Topology.IsEmbedding (fun t : T => f t) :=
    hf.comp Topology.IsEmbedding.subtypeVal
  have hcod := hfT.codRestrict e.target (fun t => hT t t.property)
  exact e.symm.isEmbedding_restrict.comp hcod

lemma joinedRounding_eq_arc {ε θ t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    joinedRounding ε θ t = roundingArc ε θ t := by
  by_cases h0 : t ≤ 0
  · have ht0 : t = 0 := le_antisymm h0 ht.1
    subst t
    simp [joinedRounding, bottomRay, (roundingArc_endpoints ε θ).1]
  · simp [joinedRounding, h0, ht.2]

/-- The literal inserted curve is C1 on an actual open neighborhood of its
closed interval and its actual derivative is nonzero there. -/
lemma inserted_curve_regular_neighborhood (e : OpenPartialHomeomorph ℂ ℂ)
    (hc : ContDiffOn ℝ 1 e e.source)
    (hci : ContDiffOn ℝ 1 e.symm e.target)
    {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (htip : sectorTip ε θ ⊆ e.target) :
    ∃ T : Set ℝ, IsOpen T ∧ Icc (0 : ℝ) 1 ⊆ T ∧
      ContDiffOn ℝ 1 (fun t => e.symm (roundingArc ε θ t)) T ∧
      ∀ t ∈ T, deriv (fun s => e.symm (roundingArc ε θ s)) t ≠ 0 := by
  let T := (roundingArc ε θ) ⁻¹' e.target ∩
    {t | deriv (roundingArc ε θ) t ≠ 0}
  have hcArc : ContDiff ℝ 1 (roundingArc ε θ) :=
    (contDiff_roundingArc ε θ).of_le (by simp)
  have hT : IsOpen T := (e.open_target.preimage hcArc.continuous).inter
    (isOpen_ne.preimage (hcArc.continuous_deriv (by norm_num)))
  have hsub : Icc (0 : ℝ) 1 ⊆ T := by
    intro t ht
    exact ⟨htip (roundingArc_image_subset_sectorTip ε θ ⟨t, ht, rfl⟩),
      roundingArc_regular hε hθ ht⟩
  have hcomp : ContDiffOn ℝ 1 (fun t => e.symm (roundingArc ε θ t)) T :=
    hci.comp hcArc.contDiffOn (fun _ ht => ht.1)
  refine ⟨T, hT, hsub, hcomp, ?_⟩
  intro t ht
  have hdc := (hcomp.contDiffAt (hT.mem_nhds ht)).differentiableAt (by norm_num)
  have hec := (hc.contDiffAt (e.open_source.mem_nhds (e.map_target ht.1))).differentiableAt
    (by norm_num)
  have hd := hec.hasFDerivAt.comp_hasDerivAt t hdc.hasDerivAt
  have heq : roundingArc ε θ =ᶠ[𝓝 t]
      (e ∘ (fun s => e.symm (roundingArc ε θ s))) :=
    Filter.mem_of_superset (hT.mem_nhds ht) (fun s hs => (e.right_inv hs.1).symm)
  have hderiv := (hd.congr_of_eventuallyEq heq).deriv
  intro hzero
  apply ht.2
  rw [hderiv, hzero, map_zero]

/-- Pull back the actual joined model curve, including its two straight tails,
to give extensions at every closed displayed point. -/
lemma inserted_closed_extension {V : Set ℂ} (e : OpenPartialHomeomorph ℂ ℂ)
    (hc : ContDiffOn ℝ 1 e e.source)
    (hci : ContDiffOn ℝ 1 e.symm e.target)
    {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) (hθ' : θ < 2 * Real.pi)
    (hside : e.IsImage V (roundedSector ε θ))
    (htip : sectorTip ε θ ⊆ e.target) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ (δ : ℝ) (W : Set ℂ) (η : ℝ → ℂ),
      0 < δ ∧ IsOpen W ∧ e.symm (roundingArc ε θ t) ∈ W ∧
      η t = e.symm (roundingArc ε θ t) ∧
      ContDiffOn ℝ 1 η (Ioo (t - δ) (t + δ)) ∧
      (∀ s ∈ Ioo (t - δ) (t + δ), deriv η s ≠ 0) ∧
      (∀ s ∈ Ioo (t - δ) (t + δ) ∩ Icc (0 : ℝ) 1,
        η s = e.symm (roundingArc ε θ s)) ∧
      Topology.IsEmbedding (fun s : Ioo (t - δ) (t + δ) => η s) ∧
      η '' Ioo (t - δ) (t + δ) = frontier V ∩ W := by
  let f := joinedRounding ε θ
  let η := fun s => e.symm (f s)
  have hf : ContDiff ℝ 1 f := contDiff_joinedRounding ε θ
  have hfemb : Topology.IsEmbedding f := (isClosedEmbedding_joinedRounding hε hθ hθ').isEmbedding
  have htarg : f t ∈ e.target := by
    dsimp [f]
    rw [joinedRounding_eq_arc ht]
    exact htip (roundingArc_image_subset_sectorTip ε θ ⟨t, ht, rfl⟩)
  have hO : IsOpen (f ⁻¹' e.target) := e.open_target.preimage hf.continuous
  obtain ⟨δ, hδ, hδO⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds htarg)
  have hIO : Ioo (t - δ) (t + δ) ⊆ f ⁻¹' e.target := by
    intro s hs
    apply hδO
    rw [mem_ball, Real.dist_eq]
    exact abs_lt.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
  obtain ⟨N, hN, hpre⟩ := hfemb.isInducing.isOpen_iff.mp
    (isOpen_Ioo : IsOpen (Ioo (t - δ) (t + δ)))
  let W := e.source ∩ e ⁻¹' N
  have hW : IsOpen W := e.isOpen_inter_preimage hN
  have hreg := chart_inverse_curve_regular e hc hci f hf (joinedRounding_regular hε hθ)
  refine ⟨δ, W, η, hδ, hW, ?_, ?_, hreg.1.mono hIO,
    (fun s hs => hreg.2 s (hIO hs)), ?_, ?_, ?_⟩
  · have htn : f t ∈ N := by
      change t ∈ f ⁻¹' N
      rw [hpre]
      exact ⟨by linarith, by linarith⟩
    change e.symm (roundingArc ε θ t) ∈ e.source ∩ e ⁻¹' N
    rw [← joinedRounding_eq_arc ht]
    exact ⟨e.map_target htarg, by change e (e.symm (f t)) ∈ N; rw [e.right_inv htarg]; exact htn⟩
  · dsimp [η, f]
    rw [joinedRounding_eq_arc ht]
  · intro s hs
    dsimp [η, f]
    rw [joinedRounding_eq_arc hs.2]
  · exact chart_inverse_curve_embedding e f hfemb _ (fun s hs => hIO hs)
  · ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      have htarget : f s ∈ e.target := hIO hs
      have hsource : η s ∈ e.source := e.map_target htarget
      refine ⟨(hside.frontier hsource).mp ?_, hsource, ?_⟩
      · change e (e.symm (f s)) ∈ frontier (roundedSector ε θ)
        rw [e.right_inv htarget, frontier_roundedSector_eq_range hε hθ hθ']
        exact ⟨s, rfl⟩
      · change e (e.symm (f s)) ∈ N
        rw [e.right_inv htarget]
        change s ∈ f ⁻¹' N
        rw [hpre]
        exact hs
    · rintro ⟨hzf, hzs, hzn⟩
      have hzmodel : e z ∈ frontier (roundedSector ε θ) := (hside.frontier hzs).mpr hzf
      rw [frontier_roundedSector_eq_range hε hθ hθ'] at hzmodel
      obtain ⟨s, hs⟩ := hzmodel
      change f s = e z at hs
      have hsI : s ∈ Ioo (t - δ) (t + δ) := by
        rw [← hpre]
        change f s ∈ N
        rw [hs]
        exact hzn
      refine ⟨s, hsI, ?_⟩
      dsimp [η]
      rw [hs, e.left_inv hzs]

lemma inserted_regular {U : Set ℂ} {J : Finset ℂ} (H : Charts U J)
    {ε : ℝ} (hε : 0 < ε) (hεR : ε < H.radius) (p : ℂ) (hp : p ∈ J) :
    ∃ T : Set ℝ, IsOpen T ∧ Icc (0 : ℝ) 1 ⊆ T ∧
      ContDiffOn ℝ 1 (insertedCurve H ε p) T ∧
      ∀ t ∈ Icc (0 : ℝ) 1, deriv (insertedCurve H ε p) t ≠ 0 := by
  obtain ⟨T, hT, hsub, hc, hd⟩ := inserted_curve_regular_neighborhood (H.e p)
    (H.smooth p hp).1 (H.smooth p hp).2 hε (H.angles p hp).1 (tip_subset_target H hε hεR p hp)
  exact ⟨T, hT, hsub, hc, fun t ht => hd t (hsub ht)⟩

lemma inserted_injective {U : Set ℂ} {J : Finset ℂ} (H : Charts U J)
    {ε : ℝ} (hε : 0 < ε) (hεR : ε < H.radius) (p : ℂ) (hp : p ∈ J) :
    InjOn (insertedCurve H ε p) (Icc (0 : ℝ) 1) := by
  intro s hs t ht heq
  apply roundingArc_injOn hε (H.angles p hp).1 (H.angles p hp).2 hs ht
  exact (H.e p).symm.injOn
    (tip_subset_target H hε hεR p hp (roundingArc_image_subset_sectorTip ε (H.angle p) ⟨s, hs, rfl⟩))
    (tip_subset_target H hε hεR p hp (roundingArc_image_subset_sectorTip ε (H.angle p) ⟨t, ht, rfl⟩)) heq

lemma inserted_extensions {U : Set ℂ} {J : Finset ℂ} (H : Charts U J)
    {ε : ℝ} (hε : 0 < ε) (hεR : ε < H.radius) (p : ℂ) (hp : p ∈ J) :
    HasLocalRegularExtensions (surgeryDomain H ε) (insertedCurve H ε p) 0 1 := by
  intro t ht
  have hside := chart_surgery_isImage H.e H.angle ε H.side H.disjoint (tip_subset_target H hε hεR) p hp
  obtain ⟨δ, W, η, hδ, hW, hpW, _, hc, hd, heq, hemb, himg⟩ :=
    inserted_closed_extension (H.e p) (H.smooth p hp).1 (H.smooth p hp).2 hε
      (H.angles p hp).1 (H.angles p hp).2 hside (tip_subset_target H hε hεR p hp) t ht
  exact ⟨δ, W, η, hδ, hW, hpW, hc, hd, heq, hemb, himg⟩



lemma deriv_eq_of_eqOn_closed_germ {f g : ℝ → ℂ} {a b t : ℝ}
    (hab : a < b) (ht : t ∈ Icc a b)
    (hf : DifferentiableAt ℝ f t) (hg : DifferentiableAt ℝ g t)
    (heq : f =ᶠ[𝓝[Icc a b] t] g) : deriv f t = deriv g t := by
  exact (uniqueDiffOn_Icc hab t ht).eq_deriv _ hf.hasDerivAt.hasDerivWithinAt
    (hg.hasDerivAt.hasDerivWithinAt.congr_of_eventuallyEq_of_mem heq ht)

/-- A C1 defining function gives a local regular extension preserving any
regular C1 parameter whose closed interval lies in the actual frontier. -/
lemma closed_frontier_curve_flattening {V : Set ℂ} (hV : HasC1DefiningFunctions V)
    {γ : ℝ → ℂ} {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b)
    (hγ : ContDiffAt ℝ 1 γ t) (hdγ : deriv γ t ≠ 0)
    (hfront : γ '' Icc a b ⊆ frontier V) :
    ∃ (e : OpenPartialHomeomorph ℂ ℂ) (q : ℝ → ℝ) (W : Set ℂ),
      IsOpen W ∧ γ t ∈ W ∧
      (∀ z ∈ W, z ∈ frontier V ↔ (e z).im = 0) ∧
      γ t ∈ e.source ∧ ContDiffAt ℝ 1 e.symm (e (γ t)) ∧
      ContDiffAt ℝ 1 q t ∧ deriv q t ≠ 0 ∧
      (q t : ℂ) = e (γ t) ∧
      ContDiffAt ℝ 1 (fun s => e.symm (q s : ℂ)) t ∧
      deriv (fun s => e.symm (q s : ℂ)) t ≠ 0 ∧
      (fun s => e.symm (q s : ℂ)) =ᶠ[𝓝[Icc a b] t] γ := by
  have hp : γ t ∈ frontier V := hfront (mem_image_of_mem γ ht)
  obtain ⟨W, ρ, hW, hpW, hc, _, hz, hd⟩ := hV _ hp
  have hρp : ρ (γ t) = 0 := (hz _ hpW).mp hp
  obtain ⟨e, hpe, hci, heim, hce⟩ := scalar_flattening_chart hW hpW hc (hd _ hpW hρp)
  let q : ℝ → ℝ := fun s => (e (γ s)).re
  let η : ℝ → ℂ := fun s => e.symm (q s : ℂ)
  have hepim : (e (γ t)).im = 0 := (heim _).trans hρp
  have hqp : (q t : ℂ) = e (γ t) := by
    apply Complex.ext <;> simp [q, hepim]
  have hq : ContDiffAt ℝ 1 q t :=
    Complex.reCLM.contDiff.contDiffAt.comp t ((hce.contDiffAt (hW.mem_nhds hpW)).comp t hγ)
  have hη : ContDiffAt ℝ 1 η t := by
    exact (hqp ▸ hci).comp t (Complex.ofRealCLM.contDiff.contDiffAt.comp t hq)
  have hγnear : γ ⁻¹' (W ∩ e.source) ∈ 𝓝 t :=
    hγ.continuousAt.preimage_mem_nhds ((hW.inter e.open_source).mem_nhds ⟨hpW, hpe⟩)
  have heq : η =ᶠ[𝓝[Icc a b] t] γ := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds hγnear, self_mem_nhdsWithin] with s hs hsab
    have hi : (e (γ s)).im = 0 := (heim _).trans ((hz _ hs.1).mp (hfront (mem_image_of_mem γ hsab)))
    have hqes : (q s : ℂ) = e (γ s) := by
      apply Complex.ext <;> simp [q, hi]
    simpa only [η, hqes] using e.left_inv hs.2
  have hηderiv : deriv η t = deriv γ t :=
    deriv_eq_of_eqOn_closed_germ hab ht (hη.differentiableAt (by norm_num))
      (hγ.differentiableAt (by norm_num)) heq
  have hqd : deriv q t ≠ 0 := by
    intro hzero
    have hdη := ((hqp ▸ hci).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t
      (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
        (hq.differentiableAt (by norm_num)).hasDerivAt)
    have hh := hdη.deriv
    change deriv η t = _ at hh
    rw [hzero, map_zero, map_zero] at hh
    exact hdγ (hηderiv.symm.trans hh)
  exact ⟨e, q, W, hW, hpW, fun z hzW => (hz z hzW).trans (by rw [heim]),
    hpe, hci, hq, hqd, hqp, hη, hηderiv.trans_ne hdγ, heq⟩

theorem regular_extension : Specs.D12Complex.Ch14.CircularRetainedDisplay.regular_extension_type := by
  intro V hV γ a b hab hγ hdγ hfront t ht
  obtain ⟨T, hT, hTab, hγT⟩ := hγ
  obtain ⟨e, q, W₀, hW₀, hpW₀, hzero, hpe, hci, hq, hqd, hqp, hη, hdη, heq⟩ :=
    closed_frontier_curve_flattening hV hab ht (hγT.contDiffAt (hT.mem_nhds (hTab ht)))
      (hdγ t ht) hfront
  let η : ℝ → ℂ := fun s => e.symm (q s : ℂ)
  let L : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft (Units.mk0 (deriv q t) hqd)
  have hqL : HasFDerivAt q (L : ℝ →L[ℝ] ℝ) t := by
    convert (hq.differentiableAt (by norm_num)).hasDerivAt.hasFDerivAt using 1
    ext
    simp [L, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]
  let k := hq.toOpenPartialHomeomorph q hqL (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have htk : t ∈ k.source := hq.mem_toOpenPartialHomeomorph_source hqL (by norm_num)
  let B : Set ℂ := e.target ∩ e.symm ⁻¹' W₀
  have hB : IsOpen B := e.symm.isOpen_inter_preimage hW₀
  have hqtB : (q t : ℂ) ∈ B := by
    rw [hqp]
    exact ⟨e.map_source hpe, by
      change e.symm (e (γ t)) ∈ W₀
      rw [e.left_inv hpe]
      exact hpW₀⟩
  have hqB : (fun s => (q s : ℂ)) ⁻¹' B ∈ 𝓝 t :=
    (Complex.continuous_ofReal.continuousAt.comp hq.continuousAt).preimage_mem_nhds (hB.mem_nhds hqtB)
  obtain ⟨N, hN, htN, hηN'⟩ := hη.contDiffOn' le_rfl (by norm_num)
  have hηN : ContDiffOn ℝ 1 η N := by simpa [η] using hηN'
  have hdn : {s | deriv η s ≠ 0} ∈ 𝓝 t := by
    exact ((hη.derivWithin (m := 0) (by norm_num)).continuousAt).eventually_ne hdη
  obtain ⟨E, hEt, hE⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp heq
  have hgood : N ∩ k.source ∩ (fun s => (q s : ℂ)) ⁻¹' B ∩
      {s | deriv η s ≠ 0} ∩ E ∈ 𝓝 t := by
    exact inter_mem (inter_mem (inter_mem (inter_mem (hN.mem_nhds htN)
      (k.open_source.mem_nhds htk)) hqB) hdn) hEt
  obtain ⟨δ, hδ, hδgood⟩ := Metric.mem_nhds_iff.mp hgood
  let I : Set ℝ := Ioo (t - δ) (t + δ)
  have hI : I ⊆ N ∩ k.source ∩ (fun s => (q s : ℂ)) ⁻¹' B ∩
      {s | deriv η s ≠ 0} ∩ E := by
    intro s hs
    apply hδgood
    simpa only [Real.dist_eq, abs_lt, mem_ball, mem_Ioo] using
      (show -δ < s - t ∧ s - t < δ by constructor <;> linarith [hs.1, hs.2])
  have hIk : I ⊆ k.source := fun s hs => (hI hs).1.1.1.2
  have hIB : ∀ s ∈ I, (q s : ℂ) ∈ B := fun s hs => (hI hs).1.1.2
  let O : Set ℝ := q '' I
  have hO : IsOpen O := k.isOpen_image_of_subset_source isOpen_Ioo hIk
  let A : Set ℂ := B ∩ Complex.re ⁻¹' O
  have hA : IsOpen A := hB.inter (Complex.continuous_re.isOpen_preimage _ hO)
  have hAe : A ⊆ e.target := fun z hz => hz.1.1
  let W : Set ℂ := e.symm '' A
  have hW : IsOpen W := e.symm.isOpen_image_of_subset_source hA hAe
  have htI : t ∈ I := by constructor <;> linarith
  have hqA (s : ℝ) (hs : s ∈ I) : (q s : ℂ) ∈ A :=
    ⟨hIB s hs, by
      change (q s : ℂ).re ∈ O
      exact mem_image_of_mem q hs⟩
  have hηeq : η t = γ t := by
    simpa only [η, hqp] using e.left_inv hpe
  refine ⟨δ, W, η, hδ, hW, ?_, hηN.mono (fun s hs => (hI hs).1.1.1.1),
    (fun s hs => (hI hs).1.2), ?_, ?_, ?_⟩
  · exact hηeq ▸ mem_image_of_mem e.symm (hqA t htI)
  · intro s hs
    exact hE ⟨(hI hs.1).2, hs.2⟩
  · have hkemb : Topology.IsEmbedding (fun s : I => q s) :=
      k.isEmbedding_restrict.comp (Topology.IsEmbedding.inclusion hIk)
    have hcastemb : Topology.IsEmbedding (fun s : I => (q s : ℂ)) :=
      Complex.isometry_ofReal.isEmbedding.comp hkemb
    have hcodemb : Topology.IsEmbedding (fun s : I => (⟨(q s : ℂ), (hIB s s.property).1⟩ : e.target)) :=
      hcastemb.codRestrict _ _
    exact e.symm.isEmbedding_restrict.comp hcodemb
  · ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hsz : η s ∈ W₀ := (hIB s hs).2
      refine ⟨(hzero _ hsz).mpr ?_, mem_image_of_mem e.symm (hqA s hs)⟩
      change (e (e.symm (q s : ℂ))).im = 0
      rw [e.right_inv (hIB s hs).1]
      exact Complex.ofReal_im _
    · rintro ⟨hzf, y, hy, rfl⟩
      have hyim : y.im = 0 := by
        rw [← e.right_inv (hAe hy)]
        exact (hzero _ hy.1.2).mp hzf
      obtain ⟨s, hs, hqs⟩ := hy.2
      have hyq : (q s : ℂ) = y := by
        apply Complex.ext
        · simpa only [Complex.ofReal_re] using hqs
        · simpa only [Complex.ofReal_im] using hyim.symm
      exact ⟨s, hs, by simp only [η, hyq]⟩


namespace FiniteCuts


lemma node_interval_subset {k : ℕ} (node : Fin (k+1) → ℝ)
    (hnode : StrictMono node) (j : Fin k) :
    Ioo (node j.castSucc) (node j.succ) ⊆ Ioo (node 0) (node (Fin.last k)) := by
  intro t ht
  exact ⟨lt_of_le_of_lt (hnode.monotone (Fin.zero_le _)) ht.1,
    lt_of_lt_of_le ht.2 (hnode.monotone (Fin.le_last _))⟩

lemma node_interval_lt {k : ℕ} (node : Fin (k+1) → ℝ)
    (hnode : StrictMono node) (j : Fin k) : node j.castSucc < node j.succ := by
  apply hnode
  simp

lemma disjoint_node_intervals {k : ℕ} (node : Fin (k+1) → ℝ)
    (hnode : StrictMono node) {j l : Fin k} (hjl : j ≠ l) :
    Disjoint (Ioo (node j.castSucc) (node j.succ))
      (Ioo (node l.castSucc) (node l.succ)) := by
  rcases lt_or_gt_of_ne hjl with h | h
  · have hle : node j.succ ≤ node l.castSucc := hnode.monotone
      (Fin.le_iff_val_le_val.mpr (Nat.succ_le_iff.mpr h))
    exact Set.disjoint_left.mpr fun _ hj hl => (not_lt_of_ge hle) (lt_trans hl.1 hj.2)
  · have hle : node l.succ ≤ node j.castSucc := hnode.monotone
      (Fin.le_iff_val_le_val.mpr (Nat.succ_le_iff.mpr h))
    exact Set.disjoint_left.mpr fun _ hj hl => (not_lt_of_ge hle) (lt_trans hj.1 hl.2)

lemma disjoint_images_of_injOn {α β : Type*} {f : α → β} {s t u : Set α}
    (hf : InjOn f u) (hs : s ⊆ u) (ht : t ⊆ u) (hst : Disjoint s t) :
    Disjoint (f '' s) (f '' t) := by
  rw [Set.disjoint_left] at hst ⊢
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
  exact hst hx ((hf (ht hy) (hs hx) he) ▸ hy)

lemma disjoint_subdivided_images {n : ℕ} (γ : Fin n → ℝ → ℂ)
    (k : Fin n → ℕ) (node : (i : Fin n) → Fin (k i+1) → ℝ)
    (hnode : ∀ i, StrictMono (node i))
    (hinj : ∀ i, InjOn (γ i) (Ioo (node i 0) (node i (Fin.last (k i)))))
    (hdisj : ∀ i l, i ≠ l → Disjoint
      (γ i '' Ioo (node i 0) (node i (Fin.last (k i))))
      (γ l '' Ioo (node l 0) (node l (Fin.last (k l)))))
    {q r : Σ i, Fin (k i)} (hqr : q ≠ r) :
    Disjoint (γ q.1 '' Ioo (node q.1 q.2.castSucc) (node q.1 q.2.succ))
      (γ r.1 '' Ioo (node r.1 r.2.castSucc) (node r.1 r.2.succ)) := by
  rcases q with ⟨i,j⟩
  rcases r with ⟨l,r⟩
  by_cases hil : i = l
  · subst l
    have hjr : j ≠ r := by
      intro hjr
      apply hqr
      simp [hjr]
    exact disjoint_images_of_injOn (hinj i)
      (node_interval_subset _ (hnode i) _)
      (node_interval_subset _ (hnode i) _)
      (disjoint_node_intervals _ (hnode i) hjr)
  · exact (hdisj i l hil).mono
      (Set.image_mono (node_interval_subset _ (hnode i) _))
      (Set.image_mono (node_interval_subset _ (hnode l) _))


end FiniteCuts


lemma retained_interval_subset {U V : Set ℂ} {C : CircleData U} (P : CutData C V)
    (i : Fin C.n) (j : Fin (P.count i)) :
    Ioo (P.node i j.castSucc) (P.node i j.succ) ⊆ Ioo (C.start i) (C.stop i) := by
  simpa only [P.first, P.last] using FiniteCuts.node_interval_subset (P.node i) (P.strict i) j

lemma retained_positive {U V : Set ℂ} {C : CircleData U} (P : CutData C V)
    (q : RetainedIndex P) : P.node q.val.1 q.val.2.castSucc < P.node q.val.1 q.val.2.succ :=
  FiniteCuts.node_interval_lt _ (P.strict _) _

lemma retained_injective {U V : Set ℂ} {C : CircleData U} (P : CutData C V)
    (q : RetainedIndex P) :
    InjOn (arcParam (C.center q.val.1) (C.radius q.val.1))
      (Ioo (P.node q.val.1 q.val.2.castSucc) (P.node q.val.1 q.val.2.succ)) :=
  (C.injective _).mono (retained_interval_subset P _ _)

lemma retained_disjoint {U V : Set ℂ} {C : CircleData U} (P : CutData C V)
    (q r : RetainedIndex P) (hqr : q ≠ r) :
    Disjoint
      (arcParam (C.center q.val.1) (C.radius q.val.1) ''
        Ioo (P.node q.val.1 q.val.2.castSucc) (P.node q.val.1 q.val.2.succ))
      (arcParam (C.center r.val.1) (C.radius r.val.1) ''
        Ioo (P.node r.val.1 r.val.2.castSucc) (P.node r.val.1 r.val.2.succ)) := by
  apply FiniteCuts.disjoint_subdivided_images
    (fun i => arcParam (C.center i) (C.radius i)) P.count P.node P.strict
    (q := q.val) (r := r.val)
  · intro i
    simpa only [P.first, P.last] using C.injective i
  · intro i j hij
    simpa only [P.first, P.last] using C.disjoint i j hij
  · exact Subtype.val_injective.ne hqr

lemma retained_regular {U V : Set ℂ} {C : CircleData U} (P : CutData C V)
    (q : RetainedIndex P) :
    ∃ T : Set ℝ, IsOpen T ∧ Icc (P.node q.val.1 q.val.2.castSucc) (P.node q.val.1 q.val.2.succ) ⊆ T ∧
      ContDiffOn ℝ 1 (arcParam (C.center q.val.1) (C.radius q.val.1)) T ∧
      ∀ t ∈ Icc (P.node q.val.1 q.val.2.castSucc) (P.node q.val.1 q.val.2.succ),
        deriv (arcParam (C.center q.val.1) (C.radius q.val.1)) t ≠ 0 := by
  refine ⟨univ, isOpen_univ, subset_univ _, ?_, ?_⟩
  · exact (contDiff_const.add (contDiff_const.mul
      (Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.mul contDiff_const)))).contDiffOn
  · intro t _
    have hd := _root_.D12Complex.FiniteCircularArcs.circle_hasDerivAt
      (C.center q.val.1) (C.radius q.val.1) t
    change HasDerivAt (arcParam (C.center q.val.1) (C.radius q.val.1)) _ t at hd
    rw [hd.deriv]
    exact mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr (C.bounds _).1.ne')
      (Complex.exp_ne_zero _)) Complex.I_ne_zero

instance {U V : Set ℂ} {C : CircleData U} (P : CutData C V) : Fintype (RetainedIndex P) := by
  classical
  unfold RetainedIndex
  infer_instance

-- Every raw retained pair is listed exactly once, followed by every join.
def enumerationIndex {U V : Set ℂ} {J : Finset ℂ} {C : CircleData U} (P : CutData C V) :
    Fin (Fintype.card (RetainedIndex P ⊕ {p : ℂ // p ∈ J})) ≃
      (RetainedIndex P ⊕ {p : ℂ // p ∈ J}) := by
  classical
  exact (Fintype.equivFin _).symm



lemma inserted_closed_frontier {U : Set ℂ} {J : Finset ℂ}
    (e : ℂ → OpenPartialHomeomorph ℂ ℂ) (θ : ℂ → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hθ : ∀ p ∈ J, 0 < θ p ∧ θ p < 2 * Real.pi)
    (hside : ∀ p ∈ J, (e p).IsImage U (sector (θ p)))
    (hdisj : ∀ p ∈ J, ∀ q ∈ J, p ≠ q → Disjoint (e p).source (e q).source)
    (htip : ∀ p ∈ J, sectorTip ε (θ p) ⊆ (e p).target)
    (p : ℂ) (hp : p ∈ J) :
    (fun t => (e p).symm (roundingArc ε (θ p) t)) '' Icc (0 : ℝ) 1 ⊆
      frontier (U \ ⋃ q ∈ J, (e q).symm '' sectorTip ε (θ q)) := by
  rintro z ⟨t, ht, rfl⟩
  have htar : roundingArc ε (θ p) t ∈ (e p).target :=
    htip p hp (roundingArc_image_subset_sectorTip ε (θ p) ⟨t, ht, rfl⟩)
  have hlocal := chart_surgery_isImage e θ ε hside hdisj htip p hp
  apply (hlocal.frontier ((e p).map_target htar)).mp
  rw [(e p).right_inv htar]
  exact roundingArc_image_subset_frontier hε (hθ p hp).1 (hθ p hp).2 ⟨t,ht,rfl⟩

lemma inserted_open_subset_U {U : Set ℂ} {J : Finset ℂ}
    (e : ℂ → OpenPartialHomeomorph ℂ ℂ) (θ : ℂ → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hθ : ∀ p ∈ J, 0 < θ p)
    (hside : ∀ p ∈ J, (e p).IsImage U (sector (θ p)))
    (htip : ∀ p ∈ J, sectorTip ε (θ p) ⊆ (e p).target)
    (p : ℂ) (hp : p ∈ J) :
    (fun t => (e p).symm (roundingArc ε (θ p) t)) '' Ioo (0 : ℝ) 1 ⊆ U := by
  rintro z ⟨t, ht, rfl⟩
  have htar : roundingArc ε (θ p) t ∈ (e p).target :=
    htip p hp (roundingArc_image_subset_sectorTip ε (θ p) ⟨t, Ioo_subset_Icc_self ht, rfl⟩)
  apply (hside p hp ((e p).map_target htar)).mp
  rw [(e p).right_inv htar]
  exact roundingArc_mem_sector hε (hθ p hp) ht

lemma inserted_disjoint {J : Finset ℂ}
    (e : ℂ → OpenPartialHomeomorph ℂ ℂ) (θ : ℂ → ℝ) (ε : ℝ)
    (hdisj : ∀ p ∈ J, ∀ q ∈ J, p ≠ q → Disjoint (e p).source (e q).source)
    (htip : ∀ p ∈ J, sectorTip ε (θ p) ⊆ (e p).target)
    (p : ℂ) (hp : p ∈ J) (q : ℂ) (hq : q ∈ J) (hpq : p ≠ q) :
    Disjoint
      ((fun t => (e p).symm (roundingArc ε (θ p) t)) '' Icc (0 : ℝ) 1)
      ((fun t => (e q).symm (roundingArc ε (θ q) t)) '' Icc (0 : ℝ) 1) := by
  apply (hdisj p hp q hq hpq).mono
  · rintro z ⟨t, ht, rfl⟩
    exact (e p).map_target (htip p hp (roundingArc_image_subset_sectorTip ε (θ p) ⟨t,ht,rfl⟩))
  · rintro z ⟨t, ht, rfl⟩
    exact (e q).map_target (htip q hq (roundingArc_image_subset_sectorTip ε (θ q) ⟨t,ht,rfl⟩))

lemma surgery_frontier_eq_retained_union_inserted {U : Set ℂ} {J : Finset ℂ}
    (e : ℂ → OpenPartialHomeomorph ℂ ℂ) (θ : ℂ → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hθ : ∀ p ∈ J, 0 < θ p ∧ θ p < 2 * Real.pi)
    (hside : ∀ p ∈ J, (e p).IsImage U (sector (θ p)))
    (hdisj : ∀ p ∈ J, ∀ q ∈ J, p ≠ q → Disjoint (e p).source (e q).source)
    (htip : ∀ p ∈ J, sectorTip ε (θ p) ⊆ (e p).target) :
    let V := U \ ⋃ q ∈ J, (e q).symm '' sectorTip ε (θ q)
    frontier V = (frontier U ∩ frontier V) ∪
      ⋃ p ∈ J, (fun t => (e p).symm (roundingArc ε (θ p) t)) '' Icc (0 : ℝ) 1 := by
  dsimp only
  let V := U \ ⋃ q ∈ J, (e q).symm '' sectorTip ε (θ q)
  change frontier V = (frontier U ∩ frontier V) ∪ _
  apply Set.Subset.antisymm
  · intro z hz
    by_cases hu : z ∈ frontier U
    · exact Or.inl ⟨hu,hz⟩
    · right
      have hadd := (chart_surgery_frontier_differences e θ hε hθ hside hdisj htip).2 ⟨hz,hu⟩
      rcases mem_iUnion₂.mp hadd with ⟨p,hp,w,⟨t,ht,hew⟩,he⟩
      exact mem_iUnion₂.mpr ⟨p,hp,t,ht,by simpa only [hew] using he⟩
  · rintro z (hz | hz)
    · exact hz.2
    · obtain ⟨p,hp,hz⟩ := mem_iUnion₂.mp hz
      exact inserted_closed_frontier e θ hε hθ hside hdisj htip p hp hz



/-- Assemble the finite literal curves from the retained/inserted geometry. -/
lemma assemble_raw_display {U : Set ℂ} {J : Finset ℂ}
    (hU : IsOpen U) (C : CircleData U) (H : Charts U J) (ε : ℝ)
    (P : CutData C (surgeryDomain H ε))
    (hcover : frontier (surgeryDomain H ε) = (frontier U ∩ frontier (surgeryDomain H ε)) ∪
      ⋃ p ∈ J, insertedCurve H ε p '' Icc (0 : ℝ) 1)
    (hireg : ∀ p ∈ J, ∃ T : Set ℝ, IsOpen T ∧ Icc (0 : ℝ) 1 ⊆ T ∧
      ContDiffOn ℝ 1 (insertedCurve H ε p) T ∧
      ∀ t ∈ Icc (0 : ℝ) 1, deriv (insertedCurve H ε p) t ≠ 0)
    (hiinj : ∀ p ∈ J, InjOn (insertedCurve H ε p) (Ioo (0 : ℝ) 1))
    (hidisj : ∀ p ∈ J, ∀ q ∈ J, p ≠ q → Disjoint
      (insertedCurve H ε p '' Ioo (0 : ℝ) 1) (insertedCurve H ε q '' Ioo (0 : ℝ) 1))
    (hiU : ∀ p ∈ J, insertedCurve H ε p '' Ioo (0 : ℝ) 1 ⊆ U)
    (hirext : ∀ p ∈ J, HasLocalRegularExtensions (surgeryDomain H ε) (insertedCurve H ε p) 0 1)
    (hrext : ∀ q : RetainedIndex P, HasLocalRegularExtensions (surgeryDomain H ε)
      (arcParam (C.center q.val.1) (C.radius q.val.1))
      (P.node q.val.1 q.val.2.castSucc) (P.node q.val.1 q.val.2.succ)) :
    Nonempty (RawDisplay C H ε P) := by
  classical
  let S := RetainedIndex P ⊕ {p : ℂ // p ∈ J}
  let m := Fintype.card S
  let e : Fin m ≃ S := enumerationIndex P
  let γ : S → ℝ → ℂ := Sum.elim
    (fun q => arcParam (C.center q.val.1) (C.radius q.val.1))
    (fun p => insertedCurve H ε p)
  let a : S → ℝ := Sum.elim (fun q => P.node q.val.1 q.val.2.castSucc) (fun _ => 0)
  let b : S → ℝ := Sum.elim (fun q => P.node q.val.1 q.val.2.succ) (fun _ => 1)
  have hretU : ∀ q : RetainedIndex P,
      γ (.inl q) '' Ioo (a (.inl q)) (b (.inl q)) ⊆ frontier U := by
    intro q
    apply (Set.image_mono ((retained_interval_subset P _ _).trans Ioo_subset_Icc_self)).trans
    intro z hz
    rw [C.cover]
    exact mem_iUnion.mpr ⟨q.val.1, hz⟩
  have hinj : ∀ i, InjOn (γ (e i)) (Ioo (a (e i)) (b (e i))) := by
    intro i
    rcases e i with q | p
    · exact retained_injective P q
    · exact hiinj p p.property
  have hdisj : ∀ i j, i ≠ j → Disjoint
      (γ (e i) '' Ioo (a (e i)) (b (e i))) (γ (e j) '' Ioo (a (e j)) (b (e j))) := by
    intro i j hij
    have heij := e.injective.ne hij
    rcases hei : e i with q | p <;> rcases hej : e j with r | s
    · apply retained_disjoint P q r
      exact fun hqr => heij (by rw [hei, hej, hqr])
    · apply (disjoint_frontier_iff_isOpen.mpr hU).mono (hretU q) (hiU s s.property)
    · apply Disjoint.symm
      apply (disjoint_frontier_iff_isOpen.mpr hU).mono (hretU r) (hiU p p.property)
    · apply hidisj p p.property s s.property
      intro hps
      apply heij
      rw [hei, hej, Subtype.ext hps]
  refine ⟨{
    count := m
    curve := fun i => γ (e i)
    left := fun i => a (e i)
    right := fun i => b (e i)
    index := e
    literal := ?_
    left_eq := ?_
    right_eq := ?_
    start_point := ?_
    stop_point := ?_
    positive := ?_
    regular := ?_
    cover := ?_
    injective := hinj
    disjoint := hdisj
    finite_endpoints := endpointSet_finite _ _ _
    overlaps := overlaps_at_endpoints _ _ _ hinj hdisj
    extensions := ?_ }⟩
  · intro i
    rcases e i with q | p <;> rfl
  · intro i
    rcases e i with q | p <;> rfl
  · intro i
    rcases e i with q | p <;> rfl
  · intro i
    rcases e i with q | p
    · rfl
    · exact congrArg (H.e p).symm (roundingArc_endpoints ε (H.angle p)).1
  · intro i
    rcases e i with q | p
    · rfl
    · exact congrArg (H.e p).symm (roundingArc_endpoints ε (H.angle p)).2
  · intro i
    rcases e i with q | p
    · exact retained_positive P q
    · norm_num [a, b]
  · intro i
    rcases e i with q | p
    · exact retained_regular P q
    · exact hireg p p.property
  · rw [e.surjective.iUnion_comp (fun s : S => γ s '' Icc (a s) (b s))]
    rw [Set.iUnion_sum]
    rw [hcover, P.retained_cover]
    apply congrArg₂ (fun s t : Set ℂ => s ∪ t)
    · ext z
      simp only [mem_iUnion, RetainedIndex, Subtype.exists, Sigma.exists, γ, a, b, Sum.elim_inl]
    · ext z
      simp only [mem_iUnion, Subtype.exists, γ, a, b, Sum.elim_inr]
  · intro i
    rcases e i with q | p
    · exact hrext q
    · exact hirext p p.property


/-- The complete finite raw display for the literal surgery. At new joins the
actual C1 boundary used below is the one constructed from `joinedRounding`
by `finite_chart_surgery`. The regular scalar coordinate in `regular_extension`
preserves a retained literal circle parameter through that boundary, including
its closed endpoints; no continuation of the total circle along the frontier
is assumed. Inserted pieces use `joinedRounding` directly. -/
theorem circular_retained_display :
    Specs.D12Complex.Ch14.CircularRetainedDisplay.circular_retained_display_type := by
  intro U J hgeom C H ε hε hεR P
  have htip := tip_subset_target H hε hεR
  have hdef := surgery_defining_functions hgeom H hε hεR
  have hcover := surgery_frontier_eq_retained_union_inserted H.e H.angle hε H.angles
    H.side H.disjoint htip
  apply assemble_raw_display hgeom.1 C H ε P hcover
  · exact fun p hp => inserted_regular H hε hεR p hp
  · exact fun p hp => (inserted_injective H hε hεR p hp).mono Ioo_subset_Icc_self
  · intro p hp q hq hpq
    exact (inserted_disjoint H.e H.angle ε H.disjoint htip p hp q hq hpq).mono
      (Set.image_mono Ioo_subset_Icc_self) (Set.image_mono Ioo_subset_Icc_self)
  · exact inserted_open_subset_U H.e H.angle hε (fun p hp => (H.angles p hp).1) H.side htip
  · exact inserted_extensions H hε hεR
  · intro q
    obtain ⟨T, hT, hsub, hc, hd⟩ := retained_regular P q
    exact regular_extension _ hdef _ _ _ (retained_positive P q) ⟨T, hT, hsub, hc⟩ hd
      (P.retained_frontier _ _ q.property)

end D12Complex.CircularRetainedDisplay
