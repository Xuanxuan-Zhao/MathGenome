import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch12.AnalyticArcs
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch12.Reflection
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.LocalHolomorphicInverse
import Mathlib.Analysis.Complex.OpenMapping

noncomputable section
open Set Metric Complex Filter
open scoped Topology
namespace D12Complex.AnalyticArcs

/-! The canonical objects live in the independent Spec so that its statements
can use them. These implementation-owned aliases verify their expected values
without treating declarations in the Spec as candidate proof targets. -/
namespace Definitions

abbrev side := D12Complex.AnalyticArcs.side
abbrev sideClosure := D12Complex.AnalyticArcs.sideClosure
abbrev realTrace := D12Complex.AnalyticArcs.realTrace
abbrev RegularParam := D12Complex.AnalyticArcs.RegularParam
abbrev ExtendsAcross := D12Complex.AnalyticArcs.ExtendsAcross
abbrev coordinate := D12Complex.AnalyticArcs.coordinate
abbrev sideFor := D12Complex.AnalyticArcs.sideFor
abbrev closureFor := D12Complex.AnalyticArcs.closureFor
abbrev ExtendsAcrossFor := D12Complex.AnalyticArcs.ExtendsAcrossFor

end Definitions

/-- The chain rule for the actual interior inverse supplies noncriticality. -/
theorem biholomorphic_deriv_ne_zero {U V : Set ℂ} {f g : ℂ → ℂ}
    (hp : BiholomorphicPair U V f g) {a : ℂ} (ha : a ∈ U) :
    deriv f a ≠ 0 ∧ deriv g (f a) ≠ 0 := by
  have hd : HasDerivAt (fun z : ℂ => z) (deriv g (f a) * deriv f a) a := ((hp.2.1.2 _ (hp.2.2.1 ha)).hasDerivAt.comp a
    (hp.1.2 a ha).hasDerivAt).congr_of_eventuallyEq
      (eventually_of_mem (hp.1.1.mem_nhds ha) (fun z hz => (hp.2.2.2.2.1 hz).symm))
  have he : deriv g (f a) * deriv f a = 1 := hd.unique (hasDerivAt_id a)
  constructor <;> intro h <;> simp [h] at he

/-- If an injective holomorphic disk map is real on its diameter and has no
critical points off that diameter, its inverse is continuous by openness and
holomorphic off the target real line. Continuous line gluing extends the
inverse, and differentiation of the inverse identity excludes a boundary
critical point. -/
theorem boundary_deriv_ne_zero {a : ℂ} {r : ℝ} {F : ℂ → ℂ}
    (hr : 0 < r) (hf : HolomorphicOn (ball a r) F)
    (hi : InjOn F (ball a r))
    (hreal : ∀ z ∈ ball a r, z.im = 0 → (F z).im = 0)
    (hnc : ∀ z ∈ ball a r, z.im ≠ 0 → deriv F z ≠ 0) :
    deriv F a ≠ 0 := by
  have hd : DifferentiableOn ℂ F (ball a r) := fun z hz => (hf.2 z hz).differentiableWithinAt
  have hfa : AnalyticOnNhd ℂ F (ball a r) := hd.analyticOnNhd isOpen_ball
  have hopen := (hfa.is_constant_or_isOpen (convex_ball a r).isPreconnected).resolve_left (by
    rintro ⟨w, hw⟩
    have hpt : a + (r / 2 : ℝ) ∈ ball a r := by
      simpa [mem_ball, dist_eq_norm, abs_of_pos hr] using (half_lt_self hr)
    have he : a + (r / 2 : ℝ) = a :=
      hi hpt (mem_ball_self hr) ((hw _ hpt).trans (hw _ (mem_ball_self hr)).symm)
    have : (r / 2 : ℝ) = 0 := by exact_mod_cast (add_left_cancel (he.trans (add_zero a).symm))
    exact (ne_of_gt (half_pos hr)) this)
  let p := hi.toPartialEquiv F (ball a r)
  have hmap : IsOpenMap ((ball a r).domRestrict F) := by
    intro s hs
    have hs' : IsOpen ((Subtype.val : ball a r → ℂ) '' s) :=
      isOpen_ball.isOpenMap_subtype_val s hs
    convert hopen _ (by rintro _ ⟨x, hx, rfl⟩; exact x.property) hs' using 1
    exact (image_image F Subtype.val s).symm
  let e : OpenPartialHomeomorph ℂ ℂ :=
    OpenPartialHomeomorph.ofContinuousOpenRestrict p
      (fun z hz => (hf.2 z hz).continuousAt.continuousWithinAt) hmap isOpen_ball
  have heF : (e : ℂ → ℂ) = F := rfl
  have hI : HolomorphicOn e.target e.symm := by
    apply Reflection.continuous_line_gluing _ _ e.open_target e.continuousOn_symm
    intro w hw hwi
    have hz := e.map_target hw
    have hzreal : (e.symm w).im ≠ 0 := by
      intro h
      have := hreal _ hz h
      rw [← heF, e.right_inv hw] at this
      exact hwi this
    exact (e.hasDerivAt_symm hw (hnc _ hz hzreal)
      (by simpa only [heF] using (hf.2 _ hz).hasDerivAt)).differentiableAt
  have hpair : BiholomorphicPair e.source e.target e e.symm :=
    ⟨by change HolomorphicOn (ball a r) F; exact hf, hI, e.mapsTo, e.mapsTo_symm, e.leftInvOn, e.rightInvOn⟩
  exact (biholomorphic_deriv_ne_zero hpair (mem_ball_self hr)).1

private theorem conj_mem_ball {a z : ℂ} {r : ℝ} (ha : a.im = 0)
    (hz : z ∈ ball a r) : star z ∈ ball a r := by
  have haa : star a = a := Complex.conj_eq_iff_im.mpr ha
  change dist (star z) a < r
  rw [← haa, dist_star_star]
  exact hz

/-- Under the conformal-side hypotheses, the reflected map has an actual
holomorphic inverse through the boundary. -/
theorem reflection_deriv_ne_zero {a : ℂ} {r : ℝ} {q : ℂ → ℂ}
    (ha : a.im = 0) (hr : 0 < r)
    (hq : HolomorphicOn (Reflection.upper a r) q)
    (hc : ContinuousOn q (Reflection.upperClosure a r))
    (hreal : ∀ z ∈ Reflection.diameter a r, (q z).im = 0)
    (hi : InjOn q (Reflection.upperClosure a r))
    (hnc : ∀ z ∈ Reflection.upper a r, deriv q z ≠ 0)
    (hpos : ∀ z ∈ Reflection.upper a r, 0 < (q z).im) :
    deriv (Reflection.extension q) a ≠ 0 := by
  obtain ⟨hF, hagree, _, _⟩ := Reflection.schwarz_reflection a r q ha hr hq hc hreal
  have hnonneg : ∀ z ∈ Reflection.upperClosure a r, 0 ≤ (Reflection.extension q z).im := by
    intro z hz
    rw [hagree hz]
    by_cases h : 0 < z.im
    · exact le_of_lt (hpos z ⟨hz.1, h⟩)
    · exact le_of_eq (hreal z ⟨hz.1, le_antisymm (not_lt.mp h) hz.2⟩).symm
  have hnegative : ∀ z ∈ ball a r, z.im < 0 → (Reflection.extension q z).im < 0 := by
    intro z hz h
    have hp := hpos (star z) ⟨conj_mem_ball ha hz, by simpa using neg_pos.mpr h⟩
    simpa [Reflection.extension, not_le.mpr h] using neg_neg_of_pos hp
  have hFi : InjOn (Reflection.extension q) (ball a r) := by
    intro z hz w hw he
    by_cases hz0 : 0 ≤ z.im <;> by_cases hw0 : 0 ≤ w.im
    · exact hi ⟨hz, hz0⟩ ⟨hw, hw0⟩
        ((hagree ⟨hz, hz0⟩).symm.trans (he.trans (hagree ⟨hw, hw0⟩)))
    · have := congrArg Complex.im he
      linarith [hnonneg z ⟨hz, hz0⟩, hnegative w hw (not_le.mp hw0)]
    · have := congrArg Complex.im he
      linarith [hnegative z hz (not_le.mp hz0), hnonneg w ⟨hw, hw0⟩]
    · have hqw : q (star z) = q (star w) := by
        simpa only [Reflection.extension, ite_eq_right hz0, ite_eq_right hw0, star_inj] using he
      have hs := hi ⟨conj_mem_ball ha hz, by simpa using le_of_lt (neg_pos.mpr (not_le.mp hz0))⟩
        ⟨conj_mem_ball ha hw, by simpa using le_of_lt (neg_pos.mpr (not_le.mp hw0))⟩ hqw
      exact star_injective hs
  apply boundary_deriv_ne_zero hr hF hFi
  · intro z hz h
    rw [hagree ⟨hz, le_of_eq h.symm⟩]
    exact hreal z ⟨hz, h⟩
  · intro z hz h
    rcases lt_or_gt_of_ne h with hneg | hposz
    · have hsz : star z ∈ Reflection.upper a r :=
        ⟨conj_mem_ball ha hz, by simpa using neg_pos.mpr hneg⟩
      have hd : HasDerivAt (fun w => star (q (star w))) (star (deriv q (star z))) z := by
        simpa only [Function.comp_def, starRingEnd_apply, star_star] using
          (hq.2 _ hsz).hasDerivAt.conj_conj
      have hd' : HasDerivAt (Reflection.extension q) (star (deriv q (star z))) z :=
        hd.congr_of_eventuallyEq (by
          filter_upwards [isOpen_lt continuous_im continuous_const |>.mem_nhds hneg] with w hw
          simp only [Reflection.extension, ite_eq_right (not_le.mpr hw)])
      rw [hd'.deriv]
      simpa only [ne_eq, star_eq_zero] using hnc _ hsz
    · have hd : HasDerivAt (Reflection.extension q) (deriv q z) z :=
        (hq.2 z ⟨hz, hposz⟩).hasDerivAt.congr_of_eventuallyEq (by
          filter_upwards [isOpen_lt continuous_const continuous_im |>.mem_nhds hposz] with w hw
          simp only [Reflection.extension, ite_eq_left (le_of_lt hw)])
      rw [hd.deriv]
      exact hnc z ⟨hz, hposz⟩

/-- Construct the inverse of a regular parametrization locally, retaining
injectivity against all the original parameter neighborhood. -/
theorem param_inverse {U : Set ℂ} {γ : ℂ → ℂ}
    (hγ : RegularParam U γ) {a : ℂ} (ha : a ∈ U) :
    ∃ (A X : Set ℂ) (η : ℂ → ℂ), a ∈ A ∧ γ a ∈ X ∧ A ⊆ U ∧
      BiholomorphicPair A X γ η ∧
      (∀ z ∈ U, γ z ∈ X → η (γ z) = z) := by
  obtain ⟨A, X, η, haA, haX, hAU, hpair, _⟩ :=
    LocalHolomorphicInverse.local_holomorphic_inverse U γ a hγ.1 ha (hγ.2.2 a ha)
  refine ⟨A, X, η, haA, haX, hAU, hpair, ?_⟩
  intro z hz hzX
  exact hγ.2.1 (hAU (hpair.2.2.2.1 hzX)) hz (hpair.2.2.2.2.2 hzX)

/-- Reflection in two actual local holomorphic charts. The image of the
reflected function is restricted to the target chart before transforming back. -/
theorem extension_in_charts_data {U V Ω A X B Y : Set ℂ} {γ ψ f η κ : ℂ → ℂ}
    {a b : ℂ} (hγ : RegularParam U γ) (hψ : RegularParam V ψ)
    (ha : a ∈ realTrace U) (hb : b ∈ realTrace V)
    (hA : a ∈ A) (hX : γ a ∈ X) (hAU : A ⊆ U)
    (hsource : BiholomorphicPair A X γ η)
    (hB : b ∈ B) (hY : ψ b ∈ Y) (_hBV : B ⊆ V)
    (htarget : BiholomorphicPair B Y ψ κ)
    (hκ : ∀ z ∈ V, ψ z ∈ Y → κ (ψ z) = z)
    (hab : f (γ a) = ψ b)
    (hside : γ '' side U ⊆ Ω) (hf : HolomorphicOn Ω f)
    (hcont : ContinuousOn f (γ '' sideClosure U))
    (hmap : MapsTo f (γ '' realTrace U) (ψ '' realTrace V)) :
    ∃ r : ℝ, 0 < r ∧ ball a r ⊆ A ∧
      (∀ z ∈ Reflection.upperClosure a r, f (γ z) ∈ Y) ∧
      HolomorphicOn (Reflection.upper a r) (fun z => κ (f (γ z))) ∧
      ContinuousOn (fun z => κ (f (γ z))) (Reflection.upperClosure a r) ∧
      (∀ z ∈ Reflection.diameter a r, (κ (f (γ z))).im = 0) ∧
      ∃ W F, ExtendsAcross U γ f a W F ∧
        (deriv (Reflection.extension (fun z => κ (f (γ z)) )) a ≠ 0 →
          deriv F (γ a) ≠ 0) := by
  let q : ℂ → ℂ := fun z => κ (f (γ z))
  have hγcont : ContinuousOn γ U := fun z hz => (hγ.1.2 z hz).continuousAt.continuousWithinAt
  have hfc : ContinuousOn (fun z => f (γ z)) (sideClosure U) :=
    hcont.comp (hγcont.mono inter_subset_left) (fun z hz => mem_image_of_mem γ hz)
  have haC : a ∈ sideClosure U := ⟨ha.1, le_of_eq ha.2.symm⟩
  have hpre : (fun z => f (γ z)) ⁻¹' Y ∈ 𝓝[sideClosure U] a :=
    (hfc a haC).preimage_mem_nhdsWithin (htarget.2.1.1.mem_nhds (hab ▸ hY))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp hpre
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hsource.1.1.mem_nhds hA)
  let r := min δ ε
  have hr : 0 < r := lt_min hδ hε
  have hball : ball a r ⊆ A := (ball_subset_ball (min_le_right δ ε)).trans hεsub
  have hval : ∀ z ∈ Reflection.upperClosure a r, f (γ z) ∈ Y := by
    intro z hz
    exact hδsub ⟨(ball_subset_ball (min_le_left δ ε)) hz.1, hAU (hball hz.1), hz.2⟩
  have hq : HolomorphicOn (Reflection.upper a r) q := by
    refine ⟨isOpen_ball.inter (isOpen_lt continuous_const continuous_im), ?_⟩
    intro z hz
    exact (htarget.2.1.2 _ (hval z ⟨hz.1, (show (0 : ℝ) ≤ z.im from le_of_lt hz.2)⟩)).comp z
      ((hf.2 _ (hside ⟨z, ⟨hAU (hball hz.1), hz.2⟩, rfl⟩)).comp z
        (hγ.1.2 z (hAU (hball hz.1))))
  have hκcont : ContinuousOn κ Y := fun z hz =>
    (htarget.2.1.2 z hz).continuousAt.continuousWithinAt
  have hqc : ContinuousOn q (Reflection.upperClosure a r) :=
    hκcont.comp
      (hfc.mono (fun z (hz : z ∈ Reflection.upperClosure a r) => ⟨hAU (hball hz.1), hz.2⟩)) hval
  have hreal : ∀ z ∈ Reflection.diameter a r, (q z).im = 0 := by
    intro z hz
    obtain ⟨t, ht, he⟩ := hmap ⟨z, ⟨hAU (hball hz.1), hz.2⟩, rfl⟩
    dsimp [q]
    rw [← he, hκ t ht.1 (he ▸ hval z ⟨hz.1, le_of_eq hz.2.symm⟩)]
    exact ht.2
  obtain ⟨hG, hagree, _, _⟩ := Reflection.schwarz_reflection a r q ha.2 hr hq hqc hreal
  let G := Reflection.extension q
  have hGa : G a = b := by
    change Reflection.extension q a = b
    rw [hagree ⟨mem_ball_self hr, le_of_eq ha.2.symm⟩]
    change κ (f (γ a)) = b
    rw [hab]
    exact htarget.2.2.2.2.1 hB
  let D := ball a r ∩ G ⁻¹' B
  have hGc : ContinuousOn G (ball a r) := fun z hz =>
    (hG.2 z hz).continuousAt.continuousWithinAt
  have hD : IsOpen D := hGc.isOpen_inter_preimage isOpen_ball htarget.1.1
  have haD : a ∈ D := ⟨mem_ball_self hr, by change G a ∈ B; rw [hGa]; exact hB⟩
  let W := X ∩ η ⁻¹' D
  let F : ℂ → ℂ := fun z => ψ (G (η z))
  have hηa : η (γ a) = a := hsource.2.2.2.2.1 hA
  refine ⟨r, hr, hball, hval, hq, hqc, hreal, W, F, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact ⟨hX, by change η (γ a) ∈ D; rw [hηa]; exact haD⟩
    · have hηc : ContinuousOn η X := fun z hz =>
        (hsource.2.1.2 z hz).continuousAt.continuousWithinAt
      refine ⟨hηc.isOpen_inter_preimage hsource.2.1.1 hD, ?_⟩
      intro z hz
      exact (htarget.1.2 _ hz.2.2).comp z
        ((hG.2 _ hz.2.1).comp z (hsource.2.1.2 z hz.1))
    · intro z hz
      exact ⟨η z, hAU (hsource.2.2.2.1 hz.1), hsource.2.2.2.2.2 hz.1⟩
    · intro z hz
      obtain ⟨t, ht, htz⟩ := hz.2
      have hηz : η z = t := by
        apply hγ.2.1 (hAU (hsource.2.2.2.1 hz.1.1)) ht.1
        exact (hsource.2.2.2.2.2 hz.1.1).trans htz.symm
      have htball : t ∈ ball a r := hηz ▸ hz.1.2.1
      change ψ (G (η z)) = f z
      rw [hηz]
      change ψ (Reflection.extension q t) = f z
      rw [hagree ⟨htball, ht.2⟩]
      exact (htarget.2.2.2.2.2 (hval t ⟨htball, ht.2⟩)).trans (congrArg f htz)
  · intro hnonzero
    have hηnz := (biholomorphic_deriv_ne_zero hsource hA).2
    have hdη := (hsource.2.1.2 _ hX).hasDerivAt
    have hdG : HasDerivAt G (deriv G a) (η (γ a)) := by
      rw [hηa]
      exact (hG.2 a (mem_ball_self hr)).hasDerivAt
    have hdψ : HasDerivAt ψ (deriv ψ b) (G (η (γ a))) := by
      rw [hηa, hGa]
      exact (htarget.1.2 b hB).hasDerivAt
    have hd : HasDerivAt F (deriv ψ b * (deriv G a * deriv η (γ a))) (γ a) :=
      hdψ.comp (γ a) (hdG.comp (γ a) hdη)
    rw [hd.deriv]
    exact mul_ne_zero (hψ.2.2 b hb.1) (mul_ne_zero hnonzero hηnz)

/-- Holomorphic extension across each interior point of a regular analytic arc. -/
theorem analytic_arc_extension :
    Specs.D12Complex.Ch12.AnalyticArcs.analytic_arc_extension_type := by
  intro U V Ω γ ψ f hγ hψ hside hf hcont hmap a ha
  obtain ⟨b, hb, hab⟩ := hmap ⟨a, ha, rfl⟩
  obtain ⟨A, X, η, haA, haX, hAU, hs, _⟩ := param_inverse hγ ha.1
  obtain ⟨B, Y, κ, hbB, hbY, hBV, ht, hκ⟩ := param_inverse hψ hb.1
  obtain ⟨r, hr, hball, hval, hq, hc, hreal, W, F, hExt, _⟩ :=
    extension_in_charts_data hγ hψ ha hb haA haX hAU hs hbB hbY hBV ht hκ
      hab.symm hside hf hcont hmap
  exact ⟨W, F, hExt⟩

/-- A conformal equivalence preserving the prescribed sides extends with
nonzero boundary derivative. Only its interior inverse is used as input. -/
theorem analytic_arc_conformal_extension :
    Specs.D12Complex.Ch12.AnalyticArcs.analytic_arc_conformal_extension_type := by
  intro U V Ω Ξ γ ψ f g hγ hψ hside hp hcont hmap hib hsideMap a ha
  obtain ⟨b, hb, hab⟩ := hmap ⟨a, ha, rfl⟩
  obtain ⟨A, X, η, haA, haX, hAU, hs, _⟩ := param_inverse hγ ha.1
  obtain ⟨B, Y, κ, hbB, hbY, hBV, ht, hκ⟩ := param_inverse hψ hb.1
  obtain ⟨r, hr, hball, hval, hq, hc, hreal, W, F, hExt, hderiv⟩ :=
    extension_in_charts_data hγ hψ ha hb haA haX hAU hs hbB hbY hBV ht hκ
      hab.symm hside hp.1 hcont hmap
  let q : ℂ → ℂ := fun z => κ (f (γ z))
  have hqpos : ∀ z ∈ Reflection.upper a r, 0 < (q z).im := by
    intro z hz
    obtain ⟨t, htV, he⟩ := hsideMap ⟨z, ⟨hAU (hball hz.1), hz.2⟩, rfl⟩
    change 0 < (κ (f (γ z))).im
    rw [← he, hκ t htV.1 (he ▸ hval z ⟨hz.1, (show (0 : ℝ) ≤ z.im from le_of_lt hz.2)⟩)]
    exact htV.2
  have hqeq : ∀ z ∈ Reflection.upperClosure a r, ∀ w ∈ Reflection.upperClosure a r,
      q z = q w → f (γ z) = f (γ w) := by
    intro z hz w hw he
    calc
      f (γ z) = ψ (q z) := (ht.2.2.2.2.2 (hval z hz)).symm
      _ = ψ (q w) := congrArg ψ he
      _ = f (γ w) := ht.2.2.2.2.2 (hval w hw)
  have hqi : InjOn q (Reflection.upperClosure a r) := by
    intro z hz w hw he
    have hzU := hAU (hball hz.1)
    have hwU := hAU (hball hw.1)
    by_cases hzpos : 0 < z.im <;> by_cases hwpos : 0 < w.im
    · apply hγ.2.1 hzU hwU
      apply hp.2.2.2.2.1.injOn (hside ⟨z, ⟨hzU, hzpos⟩, rfl⟩)
        (hside ⟨w, ⟨hwU, hwpos⟩, rfl⟩)
      exact hqeq z hz w hw he
    · have hwzero : w.im = 0 := le_antisymm (not_lt.mp hwpos) hw.2
      have h1 := hqpos z ⟨hz.1, hzpos⟩
      have h2 := hreal w ⟨hw.1, hwzero⟩
      have h3 := congrArg Complex.im he
      change (q w).im = 0 at h2
      linarith
    · have hzzero : z.im = 0 := le_antisymm (not_lt.mp hzpos) hz.2
      have h1 := hqpos w ⟨hw.1, hwpos⟩
      have h2 := hreal z ⟨hz.1, hzzero⟩
      have h3 := congrArg Complex.im he
      change (q z).im = 0 at h2
      linarith
    · apply hγ.2.1 hzU hwU
      exact hib ⟨z, ⟨hzU, le_antisymm (not_lt.mp hzpos) hz.2⟩, rfl⟩
        ⟨w, ⟨hwU, le_antisymm (not_lt.mp hwpos) hw.2⟩, rfl⟩ (hqeq z hz w hw he)
  have htsymm : BiholomorphicPair Y B κ ψ :=
    ⟨ht.2.1, ht.1, ht.2.2.2.1, ht.2.2.1, ht.2.2.2.2.2, ht.2.2.2.2.1⟩
  have hqnc : ∀ z ∈ Reflection.upper a r, deriv q z ≠ 0 := by
    intro z hz
    have hzU := hAU (hball hz.1)
    have hzΩ := hside ⟨z, ⟨hzU, hz.2⟩, rfl⟩
    have hzY := hval z ⟨hz.1, (show (0 : ℝ) ≤ z.im from le_of_lt hz.2)⟩
    have hd : HasDerivAt q (deriv κ (f (γ z)) * (deriv f (γ z) * deriv γ z)) z :=
      (ht.2.1.2 _ hzY).hasDerivAt.comp z
        ((hp.1.2 _ hzΩ).hasDerivAt.comp z (hγ.1.2 _ hzU).hasDerivAt)
    rw [hd.deriv]
    exact mul_ne_zero (biholomorphic_deriv_ne_zero htsymm hzY).1
      (mul_ne_zero (biholomorphic_deriv_ne_zero hp hzΩ).1 (hγ.2.2 z hzU))
  exact ⟨W, F, hExt, hderiv (reflection_deriv_ne_zero ha.2 hr hq hc hreal hqi hqnc hqpos)⟩

@[simp] theorem coordinate_coordinate (reverse : Bool) (z : ℂ) :
    coordinate reverse (coordinate reverse z) = z := by cases reverse <;> simp [coordinate]

/-- Reversing a real parameter preserves regular holomorphic parametrizations. -/
theorem regularParam_coordinate (reverse : Bool) {U : Set ℂ} {γ : ℂ → ℂ}
    (hγ : RegularParam U γ) :
    RegularParam (coordinate reverse ⁻¹' U) (fun z => γ (coordinate reverse z)) := by
  cases reverse
  · change RegularParam U γ
    exact hγ
  · change RegularParam ((fun z : ℂ => -z) ⁻¹' U) (fun z => γ (-z))
    refine ⟨⟨hγ.1.1.preimage continuous_neg, ?_⟩, ?_, ?_⟩
    · intro z hz
      exact (hγ.1.2 (-z) hz).comp z differentiableAt_id.neg
    · intro z hz w hw he
      exact neg_injective (hγ.2.1 hz hw he)
    · intro z hz
      have hd := (hγ.1.2 (-z) hz).hasDerivAt.comp z (hasDerivAt_id z).neg
      change deriv (γ ∘ Neg.neg) z ≠ 0
      rw [hd.deriv]
      exact mul_ne_zero (hγ.2.2 (-z) hz) (by norm_num)

private theorem image_coordinate (reverse : Bool) (U : Set ℂ) (γ : ℂ → ℂ)
    (P : ℂ → Prop) :
    (fun z => γ (coordinate reverse z)) '' (coordinate reverse ⁻¹' U ∩ {z | P z}) =
      γ '' (U ∩ {z | P (coordinate reverse z)}) := by
  ext w
  constructor
  · rintro ⟨z, ⟨hz, hP⟩, he⟩
    exact ⟨coordinate reverse z, ⟨hz, by simpa using hP⟩, he⟩
  · rintro ⟨z, ⟨hz, hP⟩, he⟩
    exact ⟨coordinate reverse z, ⟨by simpa using hz, hP⟩, by simpa using he⟩

private theorem side_image_coordinate (reverse : Bool) (U : Set ℂ) (γ : ℂ → ℂ) :
    (fun z => γ (coordinate reverse z)) '' side (coordinate reverse ⁻¹' U) =
      γ '' sideFor reverse U := image_coordinate reverse U γ (fun z => 0 < z.im)

private theorem closure_image_coordinate (reverse : Bool) (U : Set ℂ) (γ : ℂ → ℂ) :
    (fun z => γ (coordinate reverse z)) '' sideClosure (coordinate reverse ⁻¹' U) =
      γ '' closureFor reverse U := image_coordinate reverse U γ (fun z => 0 ≤ z.im)

private theorem trace_image_coordinate (reverse : Bool) (U : Set ℂ) (γ : ℂ → ℂ) :
    (fun z => γ (coordinate reverse z)) '' realTrace (coordinate reverse ⁻¹' U) =
      γ '' realTrace U := by
  rw [realTrace, image_coordinate]
  cases reverse <;> simp [coordinate, realTrace]

private theorem param_image_coordinate (reverse : Bool) (U : Set ℂ) (γ : ℂ → ℂ) :
    (fun z => γ (coordinate reverse z)) '' (coordinate reverse ⁻¹' U) = γ '' U := by
  ext w
  constructor
  · rintro ⟨z, hz, he⟩
    exact ⟨coordinate reverse z, hz, he⟩
  · rintro ⟨z, hz, he⟩
    exact ⟨coordinate reverse z, by simpa using hz, by simpa using he⟩

private theorem trace_coordinate (reverse : Bool) {U : Set ℂ} {a : ℂ}
    (ha : a ∈ realTrace U) :
    coordinate reverse a ∈ realTrace (coordinate reverse ⁻¹' U) := by
  refine ⟨by simpa using ha.1, ?_⟩
  cases reverse <;> simpa [coordinate] using ha.2

private theorem extends_coordinate (reverse : Bool) {U : Set ℂ} {γ f : ℂ → ℂ}
    {a : ℂ} {W : Set ℂ} {F : ℂ → ℂ}
    (he : ExtendsAcross (coordinate reverse ⁻¹' U) (fun z => γ (coordinate reverse z))
      f (coordinate reverse a) W F) : ExtendsAcrossFor reverse U γ f a W F := by
  rcases he with ⟨hpoint, hF, hsub, hagree⟩
  refine ⟨by simpa using hpoint, hF, ?_, ?_⟩
  · rwa [param_image_coordinate] at hsub
  · rwa [closure_image_coordinate] at hagree

theorem analytic_arc_extension_sides :
    Specs.D12Complex.Ch12.AnalyticArcs.analytic_arc_extension_sides_type := by
  intro reverse U V Ω γ ψ f hγ hψ hside hf hcont hmap a ha
  obtain ⟨W, F, he⟩ := analytic_arc_extension
    (coordinate reverse ⁻¹' U) V Ω (fun z => γ (coordinate reverse z)) ψ f
    (regularParam_coordinate reverse hγ) hψ
    (by rwa [side_image_coordinate]) hf
    (by rwa [closure_image_coordinate]) (by rwa [trace_image_coordinate])
    (coordinate reverse a) (trace_coordinate reverse ha)
  exact ⟨W, F, extends_coordinate reverse he⟩

theorem analytic_arc_conformal_extension_sides :
    Specs.D12Complex.Ch12.AnalyticArcs.analytic_arc_conformal_extension_sides_type := by
  intro reverse targetReverse U V Ω Ξ γ ψ f g hγ hψ hside hp hcont hmap hib hmapSide a ha
  obtain ⟨W, F, he, hderiv⟩ := analytic_arc_conformal_extension
    (coordinate reverse ⁻¹' U) (coordinate targetReverse ⁻¹' V) Ω Ξ
    (fun z => γ (coordinate reverse z)) (fun z => ψ (coordinate targetReverse z)) f g
    (regularParam_coordinate reverse hγ) (regularParam_coordinate targetReverse hψ)
    (by rwa [side_image_coordinate]) hp
    (by rwa [closure_image_coordinate])
    (by rwa [trace_image_coordinate, trace_image_coordinate])
    (by rwa [trace_image_coordinate])
    (by rwa [side_image_coordinate, side_image_coordinate])
    (coordinate reverse a) (trace_coordinate reverse ha)
  exact ⟨W, F, extends_coordinate reverse he, by simpa using hderiv⟩

end D12Complex.AnalyticArcs
