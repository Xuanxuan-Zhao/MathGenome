import MathGenome.Internal.LinearPDE.P201Specs.Potential.ContinuousHarmonicLift
import MathGenome.Internal.LinearPDE.P201.Potential.SubharmonicComparison
import MathGenome.Internal.LinearPDE.P201.Potential.HarnackConvergence
import MathGenome.Internal.LinearPDE.P201.Potential.HarmonicBarriers
import MathGenome.Internal.LinearPDE.P201.Potential.PerronReplacement
import Mathlib.Topology.Order.IsLUB

noncomputable section
open Set Filter Metric
open scoped Topology

namespace P201.ContinuousHarmonicLift
open P201Specs
open P201Specs.ContinuousHarmonicLift

/-- The bounded-domain maximum principle applied to a real harmonic function.
Continuity is required only on the closure and harmonicity only inside. -/
theorem harmonic_nonpos {n : ℕ} (hn : 2 ≤ n) (Ω : Domain n)
    (hΩ : Bornology.IsBounded (Ω : Set (Space n))) (u : Space n → ℝ)
    (hu : MeanValues.IsHarmonic Ω u) (hc : ContinuousOn u (closure (Ω : Set _)))
    (hb : ∀ z ∈ frontier (Ω : Set (Space n)), u z ≤ 0) :
    ∀ x ∈ closure (Ω : Set (Space n)), u x ≤ 0 := by
  have hs : SubharmonicMaximum.IsSubharmonic Ω (fun x => (u x : EReal)) :=
    (SubharmonicComparison.smooth_criterion hn Ω u hu.1).2.2.2.mpr
      (fun x hx => (hu.2 x hx).ge)
  have hboundary : ∀ z ∈ frontier (Ω : Set (Space n)),
      limsup (fun x => (u x : EReal)) (𝓝[Ω] z) ≤ (0 : EReal) := by
    intro z hz
    have : NeBot (𝓝[Ω] z) := mem_closure_iff_nhdsWithin_neBot.mp hz.1
    have ht : Tendsto (fun x => (u x : EReal)) (𝓝[Ω] z) (𝓝 (u z : EReal)) :=
      continuous_coe_real_ereal.continuousAt.tendsto.comp
        ((hc z hz.1).mono subset_closure)
    rw [ht.limsup_eq]
    exact EReal.coe_le_coe_iff.mpr (hb z hz)
  have hle := SubharmonicComparison.boundary_maximum hn Ω
    (fun x => (u x : EReal)) 0 hΩ hs hboundary
  intro x hx
  by_cases hi : x ∈ Ω
  · exact EReal.coe_le_coe_iff.mp (hle x hi)
  · apply hb x
    refine ⟨hx, ?_⟩
    rw [Ω.isOpen.interior_eq]
    exact hi

/-- Zero continuous trace forces a real harmonic function to vanish, without
assuming that the domain is connected or nonempty. -/
theorem harmonic_zero {n : ℕ} (hn : 2 ≤ n) (Ω : Domain n)
    (hΩ : Bornology.IsBounded (Ω : Set (Space n))) (u : Space n → ℝ)
    (hu : MeanValues.IsHarmonic Ω u) (hc : ContinuousOn u (closure (Ω : Set _)))
    (hb : ∀ z ∈ frontier (Ω : Set (Space n)), u z = 0) :
    EqOn u (fun _ => 0) (closure (Ω : Set (Space n))) := by
  have hp := harmonic_nonpos hn Ω hΩ u hu hc (fun z hz => (hb z hz).le)
  have hneg : MeanValues.IsHarmonic Ω (fun x => -u x) :=
    (P201.MeanValues.harmonic_bridge Ω _).mpr
      (((P201.MeanValues.harmonic_bridge Ω u).mp hu).neg)
  have hm := harmonic_nonpos hn Ω hΩ (fun x => -u x) hneg hc.neg
    (fun z hz => by simp only [hb z hz, neg_zero, le_refl])
  intro x hx
  exact le_antisymm (hp x hx) (neg_nonpos.mp (hm x hx))

/-- Uniqueness for all RCLike fields follows from the two real components. -/
theorem uniqueness : UniquenessStatement := by
  intro n hn 𝕜 _ Ω hΩ g u v hu hv
  let w : Space n → 𝕜 := fun x => u x - v x
  have hw : InnerProductSpace.HarmonicOnNhd w (Ω : Set _) :=
    ((P201.MeanValues.harmonic_bridge Ω u).mp hu.1).sub
      ((P201.MeanValues.harmonic_bridge Ω v).mp hv.1)
  have hc : ContinuousOn w (closure (Ω : Set _)) := hu.2.1.sub hv.2.1
  have hb : ∀ z ∈ frontier (Ω : Set (Space n)), w z = 0 := by
    intro z hz
    exact sub_eq_zero.mpr ((hu.2.2 ⟨z, hz⟩).trans (hv.2.2 ⟨z, hz⟩).symm)
  have hre := harmonic_zero hn Ω hΩ (fun x => RCLike.re (w x))
    ((P201.MeanValues.harmonic_bridge Ω _).mpr (hw.comp_CLM RCLike.reCLM))
    (RCLike.continuous_re.comp_continuousOn hc)
    (fun z hz => by rw [hb z hz, map_zero])
  have him := harmonic_zero hn Ω hΩ (fun x => RCLike.im (w x))
    ((P201.MeanValues.harmonic_bridge Ω _).mpr (hw.comp_CLM RCLike.imCLM))
    (RCLike.continuous_im.comp_continuousOn hc)
    (fun z hz => by rw [hb z hz, map_zero])
  intro x hx
  apply sub_eq_zero.mp
  change w x = 0
  apply RCLike.ext
  · simpa only [map_zero] using hre hx
  · simpa only [map_zero] using him hx

/-- Construct a complex extension from actual real extensions of the real
and imaginary boundary components. All regularity and trace claims are proved. -/
theorem complexification : ComplexificationStatement := by
  intro n Ω hex 𝕜 _ g
  let gre : C(frontier (Ω : Set (Space n)), ℝ) :=
    ⟨fun z => RCLike.re (g z), RCLike.continuous_re.comp g.continuous⟩
  let gim : C(frontier (Ω : Set (Space n)), ℝ) :=
    ⟨fun z => RCLike.im (g z), RCLike.continuous_im.comp g.continuous⟩
  obtain ⟨u, hu⟩ := hex gre
  obtain ⟨v, hv⟩ := hex gim
  let L : ℝ →L[ℝ] 𝕜 := (ContinuousLinearMap.id ℝ ℝ).smulRight (RCLike.I : 𝕜)
  let h : Space n → 𝕜 := fun x => RCLike.ofRealCLM (u x) + L (v x)
  refine ⟨h, ?_, ?_, ?_⟩
  · apply (P201.MeanValues.harmonic_bridge Ω h).mpr
    exact (((P201.MeanValues.harmonic_bridge Ω u).mp hu.1).comp_CLM
      RCLike.ofRealCLM).add
      (((P201.MeanValues.harmonic_bridge Ω v).mp hv.1).comp_CLM L)
  · exact (RCLike.ofRealCLM.continuous.comp_continuousOn hu.2.1).add
      (L.continuous.comp_continuousOn hv.2.1)
  · intro z
    dsimp only [h]
    rw [hu.2.2 z, hv.2.2 z]
    simpa only [gre, gim, ContinuousMap.coe_mk, RCLike.ofRealCLM_apply,
      L, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
      RCLike.real_smul_eq_coe_mul] using RCLike.re_add_im (g z)

/-- Assemble uniqueness and complexification from real existence. -/
theorem lift_of_real_existence : LiftOfRealExistenceStatement := by
  intro hex m hm 𝕜 _ Ω hΩ hC g
  obtain ⟨h, hh⟩ := complexification Ω (hex hm Ω hΩ hC) g
  exact ⟨h, hh, fun v hv => uniqueness (by omega) Ω hΩ g v h hv hh⟩

/-- Successive maxima followed by harmonic raising make a monotone harmonic
sequence majorizing any prescribed sequence in the family. Order preservation
of the raising operation itself is unnecessary. -/
theorem harmonic_majorant_sequence {n : ℕ} (F : Set (Space n → ℝ))
    (D : Domain n)
    (hmax : ∀ u ∈ F, ∀ v ∈ F, (fun x => max (u x) (v x)) ∈ F)
    (hraise : ∀ u ∈ F, ∃ v ∈ F, u ≤ v ∧ MeanValues.IsHarmonic D v)
    (u : ℕ → Space n → ℝ) (hu : ∀ j, u j ∈ F) :
    ∃ v : ℕ → Space n → ℝ, (∀ j, v j ∈ F) ∧
      (∀ j, MeanValues.IsHarmonic D (v j)) ∧
      (∀ x, Monotone (fun j => v j x)) ∧ (∀ j, u j ≤ v j) := by
  classical
  choose R hRF hRle hRh using hraise
  let step : F → F → F := fun f g =>
    ⟨R (fun x => max (f.val x) (g.val x)) (hmax f.val f.property g.val g.property),
      hRF _ _⟩
  have step_left (f g : F) : f.val ≤ (step f g).val :=
    fun x => (le_max_left (f.val x) (g.val x)).trans
      (hRle (fun y => max (f.val y) (g.val y))
        (hmax f.val f.property g.val g.property) x)
  have step_right (f g : F) : g.val ≤ (step f g).val :=
    fun x => (le_max_right (f.val x) (g.val x)).trans
      (hRle (fun y => max (f.val y) (g.val y))
        (hmax f.val f.property g.val g.property) x)
  have step_harmonic (f g : F) : MeanValues.IsHarmonic D (step f g).val := hRh _ _
  let q : ℕ → F := Nat.rec (step ⟨u 0, hu 0⟩ ⟨u 0, hu 0⟩)
    (fun j prev => step prev ⟨u (j + 1), hu (j + 1)⟩)
  refine ⟨fun j => (q j).val, fun j => (q j).property, ?_, ?_, ?_⟩
  · intro j
    cases j with
    | zero => exact step_harmonic _ _
    | succ j => exact step_harmonic _ _
  · intro x
    apply monotone_nat_of_le_succ
    intro j
    exact step_left (q j) ⟨u (j + 1), hu (j + 1)⟩ x
  · intro j
    cases j with
    | zero => exact step_right ⟨u 0, hu 0⟩ ⟨u 0, hu 0⟩
    | succ j => exact step_right (q j) ⟨u (j + 1), hu (j + 1)⟩

/-- A monotone harmonic sequence in a pointwise bounded family has a finite
limit on the ball. Only the ball is connected; the ambient domain need not be. -/
theorem family_sequence_limit {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (F : Set (Space n → ℝ))
    (hb : ∀ x ∈ Ω, BddAbove ((fun u : Space n → ℝ => u x) '' F))
    (a : Space n) (r : ℝ) (hr : 0 < r) (hsub : closedBall a r ⊆ (Ω : Set _))
    (v : ℕ → Space n → ℝ) (hv : ∀ j, v j ∈ F)
    (hh : ∀ j, MeanValues.IsHarmonic ⟨ball a r, isOpen_ball⟩ (v j))
    (hm : ∀ x, Monotone (fun j => v j x)) :
    ∃ V : Space n → ℝ, MeanValues.IsHarmonic ⟨ball a r, isOpen_ball⟩ V ∧
      (∀ x ∈ ball a r, Tendsto (fun j => v j x) atTop (𝓝 (V x))) ∧
      ∀ x ∈ ball a r, V x ≤ sSup ((fun u : Space n → ℝ => u x) '' F) := by
  have haΩ := hsub (mem_closedBall_self hr.le)
  have hbd : BddAbove (range (fun j => v j a)) := (hb a haΩ).mono (by
    rintro _ ⟨j, rfl⟩
    exact ⟨v j, hv j, rfl⟩)
  obtain ⟨V, hV, hconv⟩ := HarnackConvergence.bounded_convergence hn
    ⟨ball a r, isOpen_ball⟩ (isConnected_ball hr) v hh
    (fun x _ => hm x) a (mem_ball_self hr) hbd
  have hlim : ∀ x ∈ ball a r, Tendsto (fun j => v j x) atTop (𝓝 (V x)) := by
    intro x hx
    exact (hconv {x} isCompact_singleton (singleton_subset_iff.mpr hx)).tendsto_at
      (mem_singleton x)
  refine ⟨V, hV, hlim, ?_⟩
  intro x hx
  apply le_of_tendsto (hlim x hx)
  exact Eventually.of_forall (fun j => le_csSup (hb x (hsub (ball_subset_closedBall hx)))
    ⟨v j, hv j, rfl⟩)

/-- Perron's two-sequence argument on one ball. The second sequence tests
every member of the family, which identifies the whole supremum with the
first harmonic limit rather than merely identifying its value at the center. -/
theorem family_envelope_harmonic_on_ball {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (F : Set (Space n → ℝ)) (hne : F.Nonempty)
    (hb : ∀ x ∈ Ω, BddAbove ((fun u : Space n → ℝ => u x) '' F))
    (hmax : ∀ u ∈ F, ∀ v ∈ F, (fun x => max (u x) (v x)) ∈ F)
    (a : Space n) (r : ℝ) (hr : 0 < r) (hsub : closedBall a r ⊆ (Ω : Set _))
    (hraise : ∀ u ∈ F, ∃ v ∈ F, u ≤ v ∧
      MeanValues.IsHarmonic ⟨ball a r, isOpen_ball⟩ v) :
    MeanValues.IsHarmonic ⟨ball a r, isOpen_ball⟩
      (fun x => sSup ((fun u : Space n → ℝ => u x) '' F)) := by
  classical
  let U : Space n → ℝ := fun x => sSup ((fun u : Space n → ℝ => u x) '' F)
  have ha : a ∈ ball a r := mem_ball_self hr
  have haΩ := hsub (mem_closedBall_self hr.le)
  obtain ⟨c, _, hct, hc⟩ := exists_seq_tendsto_sSup
    (hne.image (fun u : Space n → ℝ => u a)) (hb a haΩ)
  choose u hu he using hc
  obtain ⟨v, hv, hvh, hvm, huv⟩ := harmonic_majorant_sequence F
    ⟨ball a r, isOpen_ball⟩ hmax hraise u hu
  have hvt : Tendsto (fun j => v j a) atTop (𝓝 (U a)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hct tendsto_const_nhds
    · intro j
      rw [← he j]
      exact huv j a
    · intro j
      exact le_csSup (hb a haΩ) ⟨v j, hv j, rfl⟩
  obtain ⟨V, hV, hlimV, hVU⟩ := family_sequence_limit hn Ω F hb a r hr hsub v hv hvh hvm
  have hVa : V a = U a := tendsto_nhds_unique (hlimV a ha) hvt
  have hbound : ∀ w ∈ F, ∀ x ∈ ball a r, w x ≤ V x := by
    intro w hw
    let t : ℕ → Space n → ℝ := fun j x => max (v j x) (w x)
    have ht : ∀ j, t j ∈ F := fun j => hmax _ (hv j) w hw
    obtain ⟨q, hq, hqh, hqm, htq⟩ := harmonic_majorant_sequence F
      ⟨ball a r, isOpen_ball⟩ hmax hraise t ht
    obtain ⟨W, hW, hlimW, hWU⟩ := family_sequence_limit hn Ω F hb a r hr hsub q hq hqh hqm
    have hvq (j : ℕ) (x : Space n) : v j x ≤ q j x :=
      (le_max_left _ _).trans (htq j x)
    have hwq (j : ℕ) (x : Space n) : w x ≤ q j x :=
      (le_max_right _ _).trans (htq j x)
    have hVW : ∀ x ∈ ball a r, V x ≤ W x := by
      intro x hx
      exact le_of_tendsto_of_tendsto (hlimV x hx) (hlimW x hx)
        (Eventually.of_forall (fun j => hvq j x))
    have hWa : W a = V a := le_antisymm ((hWU a ha).trans_eq hVa.symm) (hVW a ha)
    have hdiff := HarnackConvergence.harmonic_sub ⟨ball a r, isOpen_ball⟩ hV hW
    have heq := BallPoisson.harmonic_eqOn_ball_of_max hn a r (fun x => V x - W x)
      hdiff ha (fun x hx => by linarith [hVW x hx, hWa])
    intro x hx
    have hwW : w x ≤ W x := ge_of_tendsto (hlimW x hx)
      (Eventually.of_forall (fun j => hwq j x))
    have he := heq hx
    linarith
  have heq : EqOn V U (ball a r) := by
    intro x hx
    apply le_antisymm (hVU x hx)
    apply csSup_le (hne.image (fun u : Space n → ℝ => u x))
    rintro _ ⟨w, hw, rfl⟩
    exact hbound w hw x hx
  apply (P201.MeanValues.harmonic_bridge ⟨ball a r, isOpen_ball⟩ U).mpr
  have hVn := (P201.MeanValues.harmonic_bridge ⟨ball a r, isOpen_ball⟩ V).mp hV
  intro x hx
  apply (InnerProductSpace.harmonicAt_congr_nhds _).mp (hVn x hx)
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  exact heq hy

/-- The actual finite supremum of any family satisfying the local Perron
closure properties is harmonic. This is an interior theorem, leaving boundary
regularity and the closure properties of the concrete Perron family to prove. -/
theorem perron_interior : PerronInteriorStatement := by
  intro n hn Ω F hne hb hmax hraise
  apply (P201.MeanValues.harmonic_bridge Ω _).mpr
  intro a ha
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp Ω.isOpen a ha
  have hclosed : closedBall a (r / 2) ⊆ (Ω : Set _) :=
    (closedBall_subset_ball (by linarith)).trans hball
  have hh := family_envelope_harmonic_on_ball (by omega) Ω F hne hb hmax
    a (r / 2) (half_pos hr) hclosed (hraise a (r / 2) (half_pos hr) hclosed)
  exact ((P201.MeanValues.harmonic_bridge ⟨ball a (r / 2), isOpen_ball⟩ _).mp hh)
    a (mem_ball_self (half_pos hr))

/-- A continuous positive barrier on a compact boundary controls the
oscillation of any continuous datum, with an arbitrarily small error at
its unique zero. This is the compactness step in the boundary squeeze. -/
theorem barrier_domination {X : Type*} [MetricSpace X] {K : Set X}
    (hK : IsCompact K) {z : X} (hz : z ∈ K) (f b : X → ℝ)
    (hf : ContinuousOn f K) (hb : ContinuousOn b K)
    (hbz : b z = 0) (hpos : ∀ x ∈ K, x ≠ z → 0 < b x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K, |f x - f z| ≤ ε + M * b x := by
  have hbn : ∀ x ∈ K, 0 ≤ b x := by
    intro x hx
    by_cases he : x = z
    · simp [he, hbz]
    · exact (hpos x hx he).le
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousWithinAt_iff.mp (hf z hz) ε hε
  let L := K \ ball z δ
  have hL : IsCompact L := hK.diff isOpen_ball
  have hnear : ∀ x ∈ K, x ∈ ball z δ → |f x - f z| ≤ ε := by
    intro x hx hi
    exact (show |f x - f z| < ε by simpa only [Real.dist_eq] using hd hx hi).le
  by_cases hne : L.Nonempty
  · obtain ⟨y, hy, hmin⟩ := hL.exists_isMinOn hne (hb.mono sdiff_subset)
    have hby : 0 < b y := hpos y hy.1 (by
      intro he
      exact hy.2 (he ▸ mem_ball_self hδ))
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hf.sub continuousOn_const)
    let M := max B 0 / b y
    have hM : 0 ≤ M := div_nonneg (le_max_right B 0) hby.le
    refine ⟨M, hM, ?_⟩
    intro x hx
    by_cases hi : x ∈ ball z δ
    · exact (hnear x hx hi).trans (le_add_of_nonneg_right (mul_nonneg hM (hbn x hx)))
    · have heq : M * b y = max B 0 := div_mul_cancel₀ _ hby.ne'
      calc
        |f x - f z| ≤ B := by simpa only [Real.norm_eq_abs, Pi.sub_apply] using hB x hx
        _ ≤ max B 0 := le_max_left _ _
        _ = M * b y := heq.symm
        _ ≤ M * b x := mul_le_mul_of_nonneg_left (hmin ⟨hx, hi⟩) hM
        _ ≤ ε + M * b x := le_add_of_nonneg_left hε.le
  · refine ⟨0, le_rfl, ?_⟩
    intro x hx
    have hi : x ∈ ball z δ := by
      by_contra hi
      exact hne ⟨x, hx, hi⟩
    simpa only [zero_mul, add_zero] using hnear x hx hi

/-- Joining all interior boundary limits to continuous boundary data gives
continuity on the full closure, also along approaches mixing the two sets. -/
theorem continuousOn_extension {X : Type*} [MetricSpace X] {Ω : Set X}
    (hΩ : IsOpen Ω) {f φ : X → ℝ} (hf : ContinuousOn f Ω)
    (hφ : ContinuousOn φ (frontier Ω))
    (hlim : ∀ z ∈ frontier Ω, Tendsto f (𝓝[Ω] z) (𝓝 (φ z))) :
    ContinuousOn (fun z => @ite ℝ (z ∈ Ω) (Classical.propDecidable _) (f z) (φ z))
      (closure Ω) := by
  classical
  intro z hz
  apply Metric.continuousWithinAt_iff.mpr
  intro ε hε
  by_cases hzi : z ∈ Ω
  · obtain ⟨δ, hδ, hd⟩ := Metric.continuousWithinAt_iff.mp (hf z hzi) ε hε
    obtain ⟨r, hr, hs⟩ := Metric.isOpen_iff.mp hΩ z hzi
    refine ⟨min δ r, lt_min hδ hr, fun x _ hx => ?_⟩
    have hxi : x ∈ Ω := hs (hx.trans_le (min_le_right _ _))
    simpa only [ite_eq_left hxi, ite_eq_left hzi] using hd hxi (hx.trans_le (min_le_left _ _))
  · have hzf : z ∈ frontier Ω := by rw [hΩ.frontier_eq]; exact ⟨hz, hzi⟩
    obtain ⟨δ, hδ, hd⟩ := Metric.tendsto_nhdsWithin_nhds.mp (hlim z hzf) ε hε
    obtain ⟨r, hr, hs⟩ := Metric.continuousWithinAt_iff.mp (hφ z hzf) ε hε
    refine ⟨min δ r, lt_min hδ hr, fun x hx hdist => ?_⟩
    by_cases hxi : x ∈ Ω
    · simpa only [ite_eq_left hxi, ite_eq_right hzi] using hd hxi
        (hdist.trans_le (min_le_left _ _))
    · have hxf : x ∈ frontier Ω := by rw [hΩ.frontier_eq]; exact ⟨hx, hxi⟩
      simpa only [ite_eq_right hxi, ite_eq_right hzi] using hs hxf
        (hdist.trans_le (min_le_right _ _))

/-- Finite continuous subsolutions remain subharmonic after subtracting a
harmonic function. The ball-submean theorem also handles extended values;
here real-valuedness supplies admissibility on every component. -/
theorem subharmonic_sub_harmonic {n : ℕ} (hn : 2 ≤ n) (Ω : Domain n)
    (u h : Space n → ℝ) (hc : ContinuousOn u (Ω : Set _))
    (hu : SubharmonicMaximum.IsSubharmonic Ω (fun x => (u x : EReal)))
    (hh : MeanValues.IsHarmonic Ω h) :
    SubharmonicMaximum.IsSubharmonic Ω (fun x => (u x - h x : ℝ)) := by
  have had := SubharmonicMaximum.real_admissible Ω (fun x => u x - h x)
    (hc.sub hh.1.continuousOn)
  refine ⟨had, (SubharmonicComparison.equivalence hn Ω _ had).1.mpr ?_⟩
  have hm := SubharmonicComparison.ball_submean_sub_harmonic (by omega) Ω
    (fun x => (u x : EReal)) h hu.1.1 hu.1.2.1
    ((SubharmonicComparison.equivalence hn Ω _ hu.1).1.mp hu.2) hh
  simpa only [EReal.coe_sub] using hm

/-- Bounded-domain comparison for continuous subsolutions and harmonic
majorants, with their actual boundary values. -/
theorem subharmonic_le_harmonic {n : ℕ} (hn : 2 ≤ n) (Ω : Domain n)
    (hΩ : Bornology.IsBounded (Ω : Set (Space n))) (u h : Space n → ℝ)
    (hu : SubharmonicMaximum.IsSubharmonic Ω (fun x => (u x : EReal)))
    (hc : ContinuousOn u (closure (Ω : Set _)))
    (hh : MeanValues.IsHarmonic Ω h) (hhc : ContinuousOn h (closure (Ω : Set _)))
    (hb : ∀ z ∈ frontier (Ω : Set (Space n)), u z ≤ h z) :
    ∀ x ∈ Ω, u x ≤ h x := by
  have hd := subharmonic_sub_harmonic hn Ω u h (hc.mono subset_closure) hu hh
  have hm := SubharmonicComparison.boundary_maximum hn Ω
    (fun x => (u x - h x : ℝ)) 0 hΩ hd (by
      intro z hz
      rw [PerronReplacement.limsup_coe_eq (u := fun x => u x - h x) (hc.sub hhc) subset_closure hz.1 hz.1]
      exact EReal.coe_le_coe_iff.mpr (sub_nonpos.mpr (hb z hz)))
  intro x hx
  exact sub_nonpos.mp (EReal.coe_le_coe_iff.mp (hm x hx))

/-- Harmonic continuous minorants belong to the concrete Perron class. -/
theorem harmonic_mem_perronClass {n : ℕ} (hn : 2 ≤ n) (Ω : Domain n)
    (g : C(frontier (Ω : Set (Space n)), ℝ)) (u : Space n → ℝ)
    (hu : MeanValues.IsHarmonic Ω u) (hc : ContinuousOn u (closure (Ω : Set _)))
    (hb : ∀ z : frontier (Ω : Set (Space n)), u z ≤ g z) :
    u ∈ PerronReplacement.perronClass Ω g := by
  exact ⟨hc, (SubharmonicComparison.smooth_criterion hn Ω u hu.1).2.2.2.mpr
    (fun x hx => (hu.2 x hx).ge), hb⟩

/-- Compact boundary data supply a constant member and a finite common
upper bound for the Perron class, even when the boundary is empty. -/
theorem perronClass_nonempty_bdd {n : ℕ} (hn : 2 ≤ n) (Ω : Domain n)
    (hΩ : Bornology.IsBounded (Ω : Set (Space n)))
    (g : C(frontier (Ω : Set (Space n)), ℝ)) :
    (PerronReplacement.perronClass Ω g).Nonempty ∧
      ∀ x ∈ Ω, BddAbove ((fun u : Space n → ℝ => u x) ''
        PerronReplacement.perronClass Ω g) := by
  have hK : IsCompact (frontier (Ω : Set (Space n))) :=
    hΩ.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have : CompactSpace (frontier (Ω : Set (Space n))) := isCompact_iff_compactSpace.mp hK
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn g.continuous.continuousOn
  have hg (z : frontier (Ω : Set (Space n))) : |g z| ≤ B := by
    simpa only [Real.norm_eq_abs] using hB z (mem_univ z)
  have hconst (c : ℝ) : MeanValues.IsHarmonic Ω (fun _ => c) :=
    (P201.MeanValues.harmonic_bridge Ω _).mpr (InnerProductSpace.harmonicOnNhd_const c)
  refine ⟨⟨fun _ => -B, harmonic_mem_perronClass hn Ω g _ (hconst (-B))
    continuousOn_const (fun z => by linarith [neg_abs_le (g z), hg z])⟩, ?_⟩
  intro x hx
  refine ⟨B, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  exact subharmonic_le_harmonic hn Ω hΩ u (fun _ => B) hu.2.1 hu.1
    (hconst B) continuousOn_const
    (fun z hz => (hu.2.2 ⟨z, hz⟩).trans ((le_abs_self _).trans (hg ⟨z, hz⟩))) x hx

/-- The actual Perron supremum is squeezed by the two affine harmonic
barriers. Each lower barrier belongs to the class; comparison bounds every
member by the upper barrier. -/
theorem perron_barrier_squeeze {n : ℕ} (hn : 2 ≤ n) (Ω : Domain n)
    (hΩ : Bornology.IsBounded (Ω : Set (Space n)))
    (g : C(frontier (Ω : Set (Space n)), ℝ))
    (φ : Space n → ℝ) (hφ : ContinuousOn φ (frontier (Ω : Set (Space n))))
    (hφg : ∀ z : frontier (Ω : Set (Space n)), φ z = g z)
    (z : Space n) (hz : z ∈ frontier (Ω : Set (Space n)))
    (b : Space n → ℝ) (hb : MeanValues.IsHarmonic Ω b)
    (hbc : ContinuousOn b (closure (Ω : Set _))) (hbz : b z = 0)
    (hpos : ∀ x ∈ closure (Ω : Set (Space n)), x ≠ z → 0 < b x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Ω,
      |sSup ((fun u : Space n → ℝ => u x) '' PerronReplacement.perronClass Ω g) - φ z|
        ≤ ε + M * b x := by
  have hK : IsCompact (frontier (Ω : Set (Space n))) :=
    hΩ.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨M, hM, hdom⟩ := barrier_domination hK hz φ b hφ
    (hbc.mono frontier_subset_closure) hbz
    (fun x hx hne => hpos x (frontier_subset_closure hx) hne) hε
  have hbM : MeanValues.IsHarmonic Ω (fun x => M * b x) := by
    apply (P201.MeanValues.harmonic_bridge Ω _).mpr
    simpa only [Pi.smul_def, smul_eq_mul] using
      ((P201.MeanValues.harmonic_bridge Ω b).mp hb).const_smul (c := M)
  have hcM : ContinuousOn (fun x => M * b x) (closure (Ω : Set _)) :=
    continuousOn_const.mul hbc
  let L : Space n → ℝ := fun x => φ z - ε - M * b x
  let H : Space n → ℝ := fun x => φ z + ε + M * b x
  have hL : MeanValues.IsHarmonic Ω L :=
    (P201.MeanValues.harmonic_bridge Ω _).mpr
      ((InnerProductSpace.harmonicOnNhd_const (φ z - ε)).sub
        ((P201.MeanValues.harmonic_bridge Ω _).mp hbM))
  have hH : MeanValues.IsHarmonic Ω H :=
    (P201.MeanValues.harmonic_bridge Ω _).mpr
      ((InnerProductSpace.harmonicOnNhd_const (φ z + ε)).add
        ((P201.MeanValues.harmonic_bridge Ω _).mp hbM))
  have hLc : ContinuousOn L (closure (Ω : Set _)) := continuousOn_const.sub hcM
  have hHc : ContinuousOn H (closure (Ω : Set _)) := continuousOn_const.add hcM
  have hLb : ∀ w : frontier (Ω : Set (Space n)), L w ≤ g w := by
    intro w
    rw [← hφg w]
    have hd := hdom w w.property
    dsimp only [L]
    linarith [neg_abs_le (φ w - φ z)]
  have hHb : ∀ w : frontier (Ω : Set (Space n)), g w ≤ H w := by
    intro w
    rw [← hφg w]
    have hd := hdom w w.property
    dsimp only [H]
    linarith [le_abs_self (φ w - φ z)]
  have hLF := harmonic_mem_perronClass hn Ω g L hL hLc hLb
  obtain ⟨hne, hbd⟩ := perronClass_nonempty_bdd hn Ω hΩ g
  refine ⟨M, hM, ?_⟩
  intro x hx
  have hlow := le_csSup (hbd x hx) ⟨L, hLF, rfl⟩
  have hupp : sSup ((fun u : Space n → ℝ => u x) ''
      PerronReplacement.perronClass Ω g) ≤ H x := by
    apply csSup_le (hne.image (fun u : Space n → ℝ => u x))
    rintro _ ⟨u, hu, rfl⟩
    exact subharmonic_le_harmonic hn Ω hΩ u H hu.2.1 hu.1 hH hHc
      (fun w hw => (hu.2.2 ⟨w, hw⟩).trans (hHb ⟨w, hw⟩)) x hx
  apply abs_le.mpr
  dsimp only [L] at hlow
  dsimp only [H] at hupp
  constructor <;> linarith

/-- A positive harmonic barrier forces the full interior limit of the
Perron supremum at its boundary point. -/
theorem perron_boundary_limit {n : ℕ} (hn : 2 ≤ n) (Ω : Domain n)
    (hΩ : Bornology.IsBounded (Ω : Set (Space n)))
    (g : C(frontier (Ω : Set (Space n)), ℝ))
    (φ : Space n → ℝ) (hφ : ContinuousOn φ (frontier (Ω : Set (Space n))))
    (hφg : ∀ z : frontier (Ω : Set (Space n)), φ z = g z)
    (z : Space n) (hz : z ∈ frontier (Ω : Set (Space n)))
    (hbar : HarmonicBarriers.HasHarmonicBarrierAt Ω z) :
    Tendsto (fun x => sSup ((fun u : Space n → ℝ => u x) ''
      PerronReplacement.perronClass Ω g)) (𝓝[Ω] z) (𝓝 (φ z)) := by
  obtain ⟨b, hb, hbc, hbz, hpos⟩ := hbar
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨M, _, hs⟩ := perron_barrier_squeeze hn Ω hΩ g φ hφ hφg
    z hz b hb hbc hbz hpos (half_pos hε)
  have hbt : Tendsto b (𝓝[Ω] z) (𝓝 (0 : ℝ)) := by
    have ht := ((hbc z hz.1).mono subset_closure).tendsto
    rw [hbz] at ht
    exact ht
  have ht : Tendsto (fun x => ε / 2 + M * b x) (𝓝[Ω] z) (𝓝 (ε / 2)) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hbt))
  have he : ∀ᶠ x in 𝓝[Ω] z, ε / 2 + M * b x < ε :=
    ht.eventually (gt_mem_nhds (by linarith : ε / 2 < ε))
  filter_upwards [self_mem_nhdsWithin, he] with x hx he
  simpa only [Real.dist_eq] using (hs x hx).trans_lt he

/-- Continuous-data existence on any bounded open set with positive harmonic
barriers. The family, supremum, harmonicity, boundary limit, and continuous
pasting are all constructed here. -/
theorem real_existence_of_barriers {n : ℕ} (hn : 2 ≤ n) (Ω : Domain n)
    (hΩ : Bornology.IsBounded (Ω : Set (Space n)))
    (hbar : ∀ z ∈ frontier (Ω : Set (Space n)), HarmonicBarriers.HasHarmonicBarrierAt Ω z)
    (g : C(frontier (Ω : Set (Space n)), ℝ)) :
    ∃ h : Space n → ℝ, IsExtension Ω g h := by
  classical
  let φ : Space n → ℝ := fun x => if hx : x ∈ frontier (Ω : Set (Space n))
    then g ⟨x, hx⟩ else 0
  have hφg : ∀ z : frontier (Ω : Set (Space n)), φ z = g z := by
    intro z
    simp only [φ, dite_eq_left z.property]
  have hφ : ContinuousOn φ (frontier (Ω : Set (Space n))) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert g.continuous using 1
    funext z
    exact hφg z
  let F := PerronReplacement.perronClass Ω g
  let U : Space n → ℝ := fun x => sSup ((fun u : Space n → ℝ => u x) '' F)
  obtain ⟨hne, hbd⟩ := perronClass_nonempty_bdd hn Ω hΩ g
  have hU : MeanValues.IsHarmonic Ω U :=
    perron_interior hn Ω F hne hbd
      (fun u hu v hv => PerronReplacement.max_closure hn Ω g u v hu hv)
      (PerronReplacement.harmonic_raising hn Ω g)
  have hlim : ∀ z ∈ frontier (Ω : Set (Space n)), Tendsto U (𝓝[Ω] z) (𝓝 (φ z)) := by
    intro z hz
    exact perron_boundary_limit hn Ω hΩ g φ hφ hφg z hz (hbar z hz)
  let h : Space n → ℝ := fun x => if x ∈ Ω then U x else φ x
  have hh : MeanValues.IsHarmonic Ω h :=
    PerronReplacement.harmonic_congr Ω hU (by
      intro x hx
      change x ∈ Ω at hx
      simp only [h, ite_eq_left hx])
  refine ⟨h, hh, ?_, ?_⟩
  · exact continuousOn_extension Ω.isOpen hU.1.continuousOn hφ hlim
  · intro z
    have hz : (z : Space n) ∉ Ω := by
      intro hx
      exact z.property.2 (by rwa [Ω.isOpen.interior_eq])
    simpa only [h, ite_eq_right hz] using hφg z

/-- Real continuous Dirichlet data on every bounded C² open set in dimension
at least two have an actual harmonic extension continuous on the closure. -/
theorem real_existence : RealExistenceStatement := by
  intro m hm Ω hΩ hC g
  exact real_existence_of_barriers (by omega) Ω hΩ
    (HarmonicBarriers.c2_harmonic_barriers hm Ω hΩ hC) g

/-- The complete continuous harmonic lifting theorem, for real or complex
boundary data, without a connectedness or nonemptiness assumption. -/
theorem harmonic_lift : HarmonicLiftStatement :=
  lift_of_real_existence real_existence

end P201.ContinuousHarmonicLift
