import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.CornerDecay
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch13.HarmonicReflection
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch13.LocalConjugateRegularity
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.CircularExhaustion
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.StraightSectorDecay
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open Set Metric InnerProductSpace
open scoped Topology ContDiff

namespace D12Complex.CornerDecay

/-- Under the real inner product, the Riesz identification is an isometry. -/
lemma norm_gradient_eq_norm_fderiv (u : ℂ → ℝ) (z : ℂ) :
    ‖gradient u z‖ = ‖fderiv ℝ u z‖ := by
  exact (toDual ℝ ℂ).symm.norm_map _

/-- A C¹ function vanishing at c is linearly bounded near c, with a bounded
derivative on the same ball. This step uses real mean value estimates. -/
lemma linear_bounds_of_contDiffOn {U : Set ℂ} {v : ℂ → ℝ} {c : ℂ}
    (hU : IsOpen U) (hv : ContDiffOn ℝ 1 v U) (hc : c ∈ U) (hzero : v c = 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ r : ℝ, 0 < r ∧ ball c r ⊆ U ∧
      ∀ z ∈ ball c r, |v z| ≤ C * ‖z - c‖ ∧ ‖gradient v z‖ ≤ C := by
  let C : ℝ := ‖fderiv ℝ v c‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hcont : ContinuousAt (fun z => ‖fderiv ℝ v z‖) c :=
    ((hv.continuousOn_fderiv_of_isOpen hU (by norm_num)).continuousAt
      (hU.mem_nhds hc)).norm
  have hbound : ∀ᶠ z in 𝓝 c, ‖fderiv ℝ v z‖ < C :=
    hcont.eventually (gt_mem_nhds (by dsimp [C]; linarith))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (hU.mem_nhds hc) hbound)
  have hrU : ball c r ⊆ U := fun z hz => (hsub hz).1
  have hrB : ∀ z ∈ ball c r, ‖fderiv ℝ v z‖ ≤ C :=
    fun z hz => (hsub hz).2.le
  refine ⟨C, hC, r, hr, hrU, fun z hz => ⟨?_, ?_⟩⟩
  · have h := (convex_ball c r).norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := ℝ) (fun z hz => ((hv z (hrU hz)).contDiffAt
        (hU.mem_nhds (hrU hz))).differentiableAt (by norm_num))
      hrB (mem_ball_self hr) hz
    simpa [hzero, Real.norm_eq_abs] using h
  · rw [norm_gradient_eq_norm_fderiv]
    exact hrB z hz

theorem harmonic_linear_bounds :
    Specs.D12Complex.Ch14.CornerDecay.harmonic_linear_bounds_type := by
  intro U v c hv hc hz
  exact linear_bounds_of_contDiffOn hv.1 (hv.2.1.of_le (by norm_num)) hc hz

theorem halfDisk_decay :
    Specs.D12Complex.Ch14.CornerDecay.halfDisk_decay_type := by
  intro R u hR hu hcont hzero
  let v := HarmonicReflection.oddReflection u
  have hv : HarmonicOn (ball 0 R) v :=
    HarmonicReflection.harmonic_oddReflection R u hR hu hcont hzero
  have hv0 : v 0 = 0 := HarmonicReflection.oddReflection_of_zero u (by simp)
  obtain ⟨C, hC, r, hr, hrU, hbound⟩ :=
    harmonic_linear_bounds (ball 0 R) v 0 hv (mem_ball_self hR) hv0
  refine ⟨C, hC, min r R, lt_min hr hR, min_le_right _ _, ?_⟩
  intro z hz hi
  have hzr : z ∈ ball 0 r := by simpa using hz.trans_le (min_le_left r R)
  have heq : v =ᶠ[𝓝 z] u := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_im |>.mem_nhds hi]
      with w hw
    exact HarmonicReflection.oddReflection_of_pos u hw
  obtain ⟨hb, hg⟩ := hbound z hzr
  rw [heq.eq_of_nhds] at hb
  rw [heq.gradient_eq] at hg
  exact ⟨by simpa using hb, hg⟩


lemma sector_pi_iff_im_pos (w : ℂ) :
    w ∈ CircularExhaustion.sector Real.pi ↔ 0 < w.im := by
  constructor
  · rintro ⟨ρ, t, hρ, ht, htπ, heq⟩
    exact (DiskUnionBoundarySectors.upper_half_plane_iff_polar w).mpr
      ⟨ρ, hρ, t, ht, htπ, heq⟩
  · intro hw
    obtain ⟨ρ, hρ, t, ht, htπ, heq⟩ :=
      (DiskUnionBoundarySectors.upper_half_plane_iff_polar w).mp hw
    exact ⟨ρ, t, hρ, ht, htπ, heq⟩

lemma mem_closure_upperHalfPlane {z : ℂ} (hi : 0 ≤ z.im) :
    z ∈ closure {w : ℂ | 0 < w.im} := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  refine ⟨z + (ε / 2 : ℝ) * Complex.I, ?_, ?_⟩
  · simp only [mem_ofPred_eq, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.ofReal_im, Complex.I_re, mul_one, zero_mul, add_zero]
    linarith
  · rw [dist_eq_norm]
    simp only [sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_real,
      Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith

/-- Closure data transport uses continuity, rather than any assumed boundary
regularity of u or its derivatives. -/
lemma maps_upperHalfPlane_closure {V D : Set ℂ} {g : ℂ → ℂ}
    (hV : IsOpen V) (hg : ContinuousOn g V)
    (hm : MapsTo g (V ∩ {w : ℂ | 0 < w.im}) D)
    {z : ℂ} (hz : z ∈ V) (hi : 0 ≤ z.im) : g z ∈ closure D := by
  have hzcl : z ∈ closure (V ∩ {w : ℂ | 0 < w.im}) :=
    hV.inter_closure ⟨hz, mem_closure_upperHalfPlane hi⟩
  exact ((hg z hz).continuousAt (hV.mem_nhds hz)).continuousWithinAt.mem_closure hzcl hm

lemma im_nonneg_on_closure {U D : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hf : ContinuousOn f U)
    (hm : ∀ z ∈ D ∩ U, 0 < (f z).im)
    {z : ℂ} (hz : z ∈ U) (hDz : z ∈ closure D) : 0 ≤ (f z).im := by
  have hcont : ContinuousAt (fun w => (f w).im) z :=
    Complex.continuous_im.continuousAt.comp ((hf z hz).continuousAt (hU.mem_nhds hz))
  have hcl : (f z).im ∈ closure (Ioi (0 : ℝ)) :=
    hcont.continuousWithinAt.mem_closure (hU.closure_inter ⟨hDz, hz⟩) hm
  simpa only [closure_Ioi, mem_Ici] using hcl

/-- Reflection in an arbitrary actual biholomorphic half-plane chart gives a
harmonic extension across the boundary. No differentiability of the original
function on the boundary is used. -/
lemma extension_in_halfPlane_chart {D U V : Set ℂ} {c : ℂ} {R : ℝ}
    {u : ℂ → ℝ} {f g : ℂ → ℂ}
    (hc : c ∈ U) (hbi : BiholomorphicPair U V f g) (hfc : f c = 0)
    (hside : ∀ z ∈ U, z ∈ D ↔ 0 < (f z).im)
    (hR : 0 < R) (hu : HarmonicOn (D ∩ ball c R) u)
    (hcont : ContinuousOn u (closure D ∩ ball c R))
    (hzero : ∀ z ∈ frontier D ∩ ball c R, u z = 0)
    (hD : IsOpen D) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ ∃ v : ℂ → ℝ,
      HarmonicOn (ball c r) v ∧ ContDiffOn ℝ ∞ v (ball c r) ∧
      EqOn v u (closure D ∩ ball c r) := by
  rcases hbi with ⟨hf, hg, hmf, hmg, hleft, hright⟩
  have h0V : (0 : ℂ) ∈ V := hfc ▸ hmf hc
  have hg0 : g 0 = c := by simpa only [hfc] using hleft hc
  have hgc : ContinuousAt g 0 := (hg.2 0 h0V).continuousAt
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (hg.1.mem_nhds h0V)
      (hgc.preimage_mem_nhds (by simpa [hg0] using ball_mem_nhds c hR)))
  have hεV : ball 0 ε ⊆ V := fun z hz => (hεsub hz).1
  have hεR : MapsTo g (ball 0 ε) (ball c R) := fun z hz => (hεsub hz).2
  have hgD : MapsTo g (V ∩ {w : ℂ | 0 < w.im}) D := by
    intro w hw
    apply (hside _ (hmg hw.1)).mpr
    rw [hright hw.1]
    exact hw.2
  have hgCl {w : ℂ} (hw : w ∈ V) (hi : 0 ≤ w.im) : g w ∈ closure D :=
    maps_upperHalfPlane_closure hg.1 (fun z hz => (hg.2 z hz).continuousAt.continuousWithinAt)
      hgD hw hi
  let H : Set ℂ := {w : ℂ | ‖w‖ < ε ∧ 0 < w.im}
  let K : Set ℂ := {w : ℂ | ‖w‖ < ε ∧ 0 ≤ w.im}
  have hHball : H ⊆ ball 0 ε := fun w hw => by simpa using hw.1
  have hKball : K ⊆ ball 0 ε := fun w hw => by simpa using hw.1
  have hvH : HarmonicOn H (u ∘ g) :=
    HarmonicFoundation.harmonicOn_comp_holomorphic _ H u g hu
      ⟨HarmonicReflection.halfDisk_isOpen ε,
        fun w hw => hg.2 w (hεV (hHball hw))⟩
      (fun w hw => ⟨hgD ⟨hεV (hHball hw), hw.2⟩, hεR (hHball hw)⟩)
  have hvK : ContinuousOn (u ∘ g) K :=
    hcont.comp (fun w hw => (hg.2 w (hεV (hKball hw))).continuousAt.continuousWithinAt)
      (fun w hw => ⟨hgCl (hεV (hKball hw)) hw.2, hεR (hKball hw)⟩)
  have hvzero : ∀ w : ℂ, ‖w‖ < ε → w.im = 0 → (u ∘ g) w = 0 := by
    intro w hw hi
    have hwB : w ∈ ball 0 ε := by simpa using hw
    have hwV := hεV hwB
    apply hzero
    refine ⟨?_, hεR hwB⟩
    rw [hD.frontier_eq]
    refine ⟨hgCl hwV hi.ge, ?_⟩
    intro hd
    have hp := (hside _ (hmg hwV)).mp hd
    rw [hright hwV, hi] at hp
    exact lt_irrefl 0 hp
  let W : ℂ → ℝ := HarmonicReflection.oddReflection (u ∘ g)
  have hW : HarmonicOn (ball 0 ε) W :=
    HarmonicReflection.harmonic_oddReflection ε (u ∘ g) hε hvH hvK hvzero
  have hfccont : ContinuousAt f c := (hf.2 c hc).continuousAt
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (hf.1.mem_nhds hc)
      (Filter.inter_mem (ball_mem_nhds c hR)
        (hfccont.preimage_mem_nhds (by simpa [hfc] using ball_mem_nhds (0 : ℂ) hε))))
  have hrU : ball c r ⊆ U := fun z hz => (hrsub hz).1
  have hrR : ball c r ⊆ ball c R := fun z hz => (hrsub hz).2.1
  have hrF : MapsTo f (ball c r) (ball 0 ε) := fun z hz => (hrsub hz).2.2
  let v : ℂ → ℝ := W ∘ f
  have hv : HarmonicOn (ball c r) v :=
    HarmonicFoundation.harmonicOn_comp_holomorphic _ _ W f hW
      ⟨isOpen_ball, fun z hz => hf.2 z (hrU hz)⟩ hrF
  refine ⟨min r R, lt_min hr hR, min_le_right _ _, v, ?_, ?_, ?_⟩
  · exact ⟨isOpen_ball, hv.2.1.mono (ball_subset_ball (min_le_left _ _)),
      fun z hz => hv.2.2 z (ball_subset_ball (min_le_left _ _) hz)⟩
  · exact (LocalConjugateRegularity.harmonic_smooth _ _ hv).mono
      (ball_subset_ball (min_le_left _ _))
  · intro z hz
    have hzr : z ∈ ball c r := ball_subset_ball (min_le_left _ _) hz.2
    have hzU := hrU hzr
    have hi : 0 ≤ (f z).im :=
      im_nonneg_on_closure hf.1 (fun z hz => (hf.2 z hz).continuousAt.continuousWithinAt)
        (fun z hz => (hside z hz.2).mp hz.1) hzU hz.1
    change W (f z) = u z
    rcases hi.eq_or_lt with hi | hi
    · rw [show W (f z) = 0 from HarmonicReflection.oddReflection_of_zero _ hi.symm]
      symm
      apply hzero
      refine ⟨?_, hrR hzr⟩
      rw [hD.frontier_eq]
      refine ⟨hz.1, fun hd => ?_⟩
      have hp := (hside z hzU).mp hd
      linarith
    · rw [show W (f z) = (u ∘ g) (f z) from HarmonicReflection.oddReflection_of_pos _ hi]
      simp only [Function.comp_apply, hleft hzU]

theorem smooth_boundary_extension :
    Specs.D12Complex.Ch14.CornerDecay.smooth_boundary_extension_type := by
  intro D c R u hD hchart hR hu hcont hzero
  obtain ⟨U, V, f, g, hc, hbi, hfc, _, hside⟩ := hchart
  exact extension_in_halfPlane_chart hc hbi hfc
    (fun z hz => (hside z hz).trans (sector_pi_iff_im_pos (f z))) hR hu hcont hzero hD


/-- The coordinate change has locally comparable radii and bounded real
differential. Positivity of the lower constant comes from the actual inverse. -/
lemma biholomorphic_norm_bounds {U V : Set ℂ} {f g : ℂ → ℂ} {c : ℂ}
    (hc : c ∈ U) (hbi : BiholomorphicPair U V f g) (hf0 : f c = 0) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∃ r : ℝ, 0 < r ∧ ball c r ⊆ U ∧
      ∀ z ∈ ball c r,
        A * ‖z - c‖ ≤ ‖f z‖ ∧ ‖f z‖ ≤ B * ‖z - c‖ ∧ ‖fderiv ℝ f z‖ ≤ B := by
  rcases hbi with ⟨hf, hg, hmf, hmg, hleft, hright⟩
  have h0V : (0 : ℂ) ∈ V := hf0 ▸ hmf hc
  have hg0 : g 0 = c := by simpa only [hf0] using hleft hc
  have localBounds : ∀ (W : Set ℂ) (F : ℂ → ℂ) (a : ℂ),
      HolomorphicOn W F → a ∈ W →
      ∃ C : ℝ, 0 < C ∧ ∃ r : ℝ, 0 < r ∧ ball a r ⊆ W ∧
        ∀ z ∈ ball a r,
          ‖F z - F a‖ ≤ C * ‖z - a‖ ∧ ‖fderiv ℝ F z‖ ≤ C := by
    intro W F a hF ha
    have hF1 : ContDiffOn ℝ 1 F W :=
      (TaylorSmoothness.holomorphic_real_smooth W F hF).of_le (by simp)
    let C : ℝ := ‖fderiv ℝ F a‖ + 1
    have hC : 0 < C := by dsimp [C]; positivity
    have hcont : ContinuousAt (fun z => ‖fderiv ℝ F z‖) a :=
      ((hF1.continuousOn_fderiv_of_isOpen hF.1 (by norm_num)).continuousAt
        (hF.1.mem_nhds ha)).norm
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp
      (Filter.inter_mem (hF.1.mem_nhds ha)
        (hcont.eventually (gt_mem_nhds (show ‖fderiv ℝ F a‖ < C by dsimp [C]; linarith))))
    have hrW : ball a r ⊆ W := fun z hz => (hsub hz).1
    have hrB : ∀ z ∈ ball a r, ‖fderiv ℝ F z‖ ≤ C := fun z hz => (hsub hz).2.le
    refine ⟨C, hC, r, hr, hrW, fun z hz => ⟨?_, hrB z hz⟩⟩
    exact (convex_ball a r).norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := ℝ) (fun z hz => ((hF1 z (hrW hz)).contDiffAt
        (hF.1.mem_nhds (hrW hz))).differentiableAt (by norm_num))
      hrB (mem_ball_self hr) hz
  obtain ⟨B, hB, r, hr, hrU, hfB⟩ := localBounds U f c hf hc
  obtain ⟨K, hK, s, hs, hsV, hgB⟩ := localBounds V g 0 hg h0V
  have hfc := (hf.2 c hc).continuousAt
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (ball_mem_nhds c hr)
      (hfc.preimage_mem_nhds (by simpa [hf0] using ball_mem_nhds (0 : ℂ) hs)))
  refine ⟨1 / K, B, by positivity, hB, δ, hδ,
    fun z hz => hrU (hδsub hz).1, fun z hz => ?_⟩
  have hzr := (hδsub hz).1
  have hzf := (hδsub hz).2
  obtain ⟨hfu, hfd⟩ := hfB z hzr
  obtain ⟨hgu, _⟩ := hgB (f z) hzf
  rw [hleft (hrU hzr), hg0, sub_zero] at hgu
  refine ⟨?_, by simpa only [hf0, sub_zero] using hfu, hfd⟩
  rw [one_div_mul_eq_div, div_le_iff₀ hK]
  simpa only [mul_comm] using hgu

/-- A two-sided radial comparison controls every real exponent. In particular
this retains the negative exponent occurring at reentrant corners. -/
lemma rpow_bound_of_comparable {x y A B : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hA : 0 < A) (hB : 0 < B) (hl : A * y ≤ x) (hu : x ≤ B * y) (p : ℝ) :
    x ^ p ≤ max (A ^ p) (B ^ p) * y ^ p := by
  by_cases hp : 0 ≤ p
  · calc
      x ^ p ≤ (B * y) ^ p := Real.rpow_le_rpow hx.le hu hp
      _ = B ^ p * y ^ p := Real.mul_rpow hB.le hy.le
      _ ≤ max (A ^ p) (B ^ p) * y ^ p :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hy.le _)
  · calc
      x ^ p ≤ (A * y) ^ p := Real.rpow_le_rpow_of_nonpos (mul_pos hA hy) hl (le_of_lt (lt_of_not_ge hp))
      _ = A ^ p * y ^ p := Real.mul_rpow hA.le hy.le
      _ ≤ max (A ^ p) (B ^ p) * y ^ p :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hy.le _)


/-- An actual local inverse transports closure membership in both directions. -/
lemma chart_closure_iff {D S U V : Set ℂ} {f g : ℂ → ℂ}
    (hbi : BiholomorphicPair U V f g)
    (hside : ∀ z ∈ U, z ∈ D ↔ f z ∈ S) {z : ℂ} (hz : z ∈ U) :
    z ∈ closure D ↔ f z ∈ closure S := by
  rcases hbi with ⟨hf, hg, hmf, hmg, hleft, hright⟩
  constructor
  · intro hDz
    exact (hf.2 z hz).continuousAt.continuousWithinAt.mem_closure
      (hf.1.closure_inter ⟨hDz, hz⟩) (fun w hw => (hside w hw.2).mp hw.1)
  · intro hSz
    have h : g (f z) ∈ closure D :=
      (hg.2 (f z) (hmf hz)).continuousAt.continuousWithinAt.mem_closure
        (hg.1.closure_inter ⟨hSz, hmf hz⟩) (fun w hw => by
          apply (hside _ (hmg hw.2)).mpr
          simpa only [hright hw.2] using hw.1)
    simpa only [hleft hz] using h

lemma chart_frontier_iff {D S U V : Set ℂ} {f g : ℂ → ℂ}
    (hbi : BiholomorphicPair U V f g)
    (hside : ∀ z ∈ U, z ∈ D ↔ f z ∈ S) {z : ℂ} (hz : z ∈ U) :
    z ∈ frontier D ↔ f z ∈ frontier S := by
  have hc := chart_closure_iff hbi hside hz
  have hcc := chart_closure_iff (D := Dᶜ) (S := Sᶜ) hbi
    (fun z hz => not_congr (hside z hz)) hz
  simp only [frontier_eq_closure_inter_closure, mem_inter_iff, hc, hcc]

/-- Transport the original harmonicity, continuous closure values, and zero
boundary values to a smaller sector cap. Neither decay estimate is assumed. -/
lemma zero_boundary_data_in_chart {D S U V : Set ℂ} {c : ℂ} {R : ℝ}
    {u : ℂ → ℝ} {f g : ℂ → ℂ}
    (hc : c ∈ U) (hbi : BiholomorphicPair U V f g) (hfc : f c = 0)
    (hside : ∀ z ∈ U, z ∈ D ↔ f z ∈ S) (hD : IsOpen D) (hR : 0 < R)
    (hu : HarmonicOn (D ∩ ball c R) u)
    (hcont : ContinuousOn u (closure D ∩ ball c R))
    (hzero : ∀ z ∈ frontier D ∩ ball c R, u z = 0) :
    ∃ ε : ℝ, 0 < ε ∧
      HarmonicOn (S ∩ ball 0 ε) (u ∘ g) ∧
      ContinuousOn (u ∘ g) (closure S ∩ ball 0 ε) ∧
      (∀ z ∈ frontier S ∩ ball 0 ε, (u ∘ g) z = 0) := by
  rcases hbi with ⟨hf, hg, hmf, hmg, hleft, hright⟩
  have hbi : BiholomorphicPair U V f g := ⟨hf, hg, hmf, hmg, hleft, hright⟩
  have h0V : (0 : ℂ) ∈ V := hfc ▸ hmf hc
  have hg0 : g 0 = c := by simpa only [hfc] using hleft hc
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (hg.1.mem_nhds h0V)
      ((hg.2 0 h0V).continuousAt.preimage_mem_nhds
        (by simpa [hg0] using ball_mem_nhds c hR)))
  have hεV : ball 0 ε ⊆ V := fun z hz => (hεsub hz).1
  have hεR : MapsTo g (ball 0 ε) (ball c R) := fun z hz => (hεsub hz).2
  have hginS {z : ℂ} (hz : z ∈ V) : g z ∈ D ↔ z ∈ S := by
    simpa only [hright hz] using hside (g z) (hmg hz)
  have hcap : IsOpen (S ∩ ball (0 : ℂ) ε) := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    have hzV := hεV hz.2
    apply Filter.mem_of_superset
      (Filter.inter_mem (isOpen_ball.mem_nhds hz.2)
        ((hg.2 z hzV).continuousAt.preimage_mem_nhds
          (hD.mem_nhds ((hginS hzV).mpr hz.1))))
    intro w hw
    exact ⟨(hginS (hεV hw.1)).mp hw.2, hw.1⟩
  refine ⟨ε, hε, ?_, ?_, ?_⟩
  · exact HarmonicFoundation.harmonicOn_comp_holomorphic _ _ u g hu
      ⟨hcap, fun z hz => hg.2 z (hεV hz.2)⟩
      (fun z hz => ⟨(hginS (hεV hz.2)).mpr hz.1, hεR hz.2⟩)
  · apply hcont.comp
      (fun z hz => (hg.2 z (hεV hz.2)).continuousAt.continuousWithinAt)
    intro z hz
    refine ⟨?_, hεR hz.2⟩
    apply (chart_closure_iff hbi hside (hmg (hεV hz.2))).mpr
    simpa only [hright (hεV hz.2)] using hz.1
  · intro z hz
    apply hzero
    refine ⟨?_, hεR hz.2⟩
    apply (chart_frontier_iff hbi hside (hmg (hεV hz.2))).mpr
    simpa only [hright (hεV hz.2)] using hz.1

theorem corner_decay_of_sector_decay :
    Specs.D12Complex.Ch14.CornerDecay.corner_decay_of_sector_decay_type := by
  intro hsector D c θ R u hD hθ hθ2 hchart hR hu hcont hzero
  obtain ⟨U, V, f, g, hc, hbi, hfc, _, hside⟩ := hchart
  obtain ⟨ε, hε, hv, hvcont, hvzero⟩ :=
    zero_boundary_data_in_chart hc hbi hfc hside hD hR hu hcont hzero
  obtain ⟨C, hC, s, hs, hsε, hdecay⟩ := hsector θ ε (u ∘ g) hθ hθ2 hε hv hvcont hvzero
  obtain ⟨A, B, hA, hB, r, hr, hrU, hrad⟩ := biholomorphic_norm_bounds hc hbi hfc
  have hf := hbi.1
  have hleft := hbi.2.2.2.2.1
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (ball_mem_nhds c hr)
      ((hf.2 c hc).continuousAt.preimage_mem_nhds
        (by simpa [hfc] using ball_mem_nhds (0 : ℂ) hs)))
  let α : ℝ := Real.pi / θ
  let M : ℝ := max (A ^ (α - 1)) (B ^ (α - 1))
  let K : ℝ := max (C * B ^ α) (C * M * B) + 1
  have hM : 0 < M := lt_max_of_lt_left (Real.rpow_pos_of_pos hA _)
  have hK : 0 < K := by dsimp [K]; have := Real.rpow_pos_of_pos hB α; positivity
  refine ⟨K, hK, min δ R, lt_min hδ hR, min_le_right _ _, ?_⟩
  intro z hzD hzn
  have hzδ : z ∈ ball c δ := by simpa [dist_eq_norm] using hzn.trans_le (min_le_left δ R)
  have hzr := (hδsub hzδ).1
  have hzU := hrU hzr
  have hfzS := (hside z hzU).mp hzD
  have hfzs : ‖f z‖ < s := by simpa using (hδsub hzδ).2
  have hfzε : f z ∈ CircularExhaustion.sector θ ∩ ball 0 ε :=
    ⟨hfzS, by simpa using hfzs.trans_le hsε⟩
  have hzc : z ≠ c := by
    intro heq
    have : (0 : ℂ) ∈ CircularExhaustion.sector θ := hfc ▸ (heq ▸ hfzS)
    obtain ⟨ρ, t, hρ, _, _, he⟩ := this
    have hn := congrArg norm he
    have : ρ = 0 := by simpa [norm_mul, Complex.norm_exp, abs_of_pos hρ] using hn.symm
    linarith
  have hy : 0 < ‖z - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzc)
  obtain ⟨hlow, hupp, hdfbound⟩ := hrad z hzr
  have hx : 0 < ‖f z‖ := (mul_pos hA hy).trans_le hlow
  obtain ⟨hval, hgrad⟩ := hdecay (f z) hfzS hfzs
  have heq : (u ∘ g) ∘ f =ᶠ[𝓝 z] u := by
    apply EqOn.eventuallyEq_of_mem (s := U) _ (hf.1.mem_nhds hzU)
    intro w hw
    simp only [Function.comp_apply, hleft hw]
  have hdv : DifferentiableAt ℝ (u ∘ g) (f z) :=
    ((hv.2.1 (f z) hfzε).contDiffAt (hv.1.mem_nhds hfzε)).differentiableAt (by norm_num)
  have hdf : DifferentiableAt ℝ f z := (hf.2 z hzU).restrictScalars ℝ
  have hgchain : ‖gradient u z‖ ≤ ‖gradient (u ∘ g) (f z)‖ * B := by
    simp only [norm_gradient_eq_norm_fderiv]
    rw [← heq.fderiv_eq, fderiv_comp z hdv hdf]
    exact ((fderiv ℝ (u ∘ g) (f z)).opNorm_comp_le (fderiv ℝ f z)).trans
      (mul_le_mul_of_nonneg_left hdfbound (norm_nonneg _))
  constructor
  · have hpow : ‖f z‖ ^ α ≤ B ^ α * ‖z - c‖ ^ α := by
      calc
        _ ≤ (B * ‖z - c‖) ^ α := Real.rpow_le_rpow hx.le hupp (by dsimp [α]; positivity)
        _ = _ := Real.mul_rpow hB.le hy.le
    have hCK : C * B ^ α ≤ K := (le_max_left _ _).trans (by dsimp [K]; linarith)
    calc
      |u z| = |(u ∘ g) (f z)| := congrArg abs (heq.eq_of_nhds.symm)
      _ ≤ C * ‖f z‖ ^ α := hval
      _ ≤ C * (B ^ α * ‖z - c‖ ^ α) := mul_le_mul_of_nonneg_left hpow hC.le
      _ = (C * B ^ α) * ‖z - c‖ ^ α := by ring
      _ ≤ K * ‖z - c‖ ^ α :=
        mul_le_mul_of_nonneg_right hCK (Real.rpow_nonneg hy.le _)
  · have hpow : ‖f z‖ ^ (α - 1) ≤ M * ‖z - c‖ ^ (α - 1) :=
      rpow_bound_of_comparable hx hy hA hB hlow hupp (α - 1)
    have hCK : C * M * B ≤ K := (le_max_right _ _).trans (by dsimp [K]; linarith)
    calc
      ‖gradient u z‖ ≤ ‖gradient (u ∘ g) (f z)‖ * B := hgchain
      _ ≤ (C * ‖f z‖ ^ (α - 1)) * B := mul_le_mul_of_nonneg_right hgrad hB.le
      _ ≤ (C * (M * ‖z - c‖ ^ (α - 1))) * B := by gcongr
      _ = (C * M * B) * ‖z - c‖ ^ (α - 1) := by ring
      _ ≤ K * ‖z - c‖ ^ (α - 1) :=
        mul_le_mul_of_nonneg_right hCK (Real.rpow_nonneg hy.le _)

/-- The straight-sector theorem has exactly the original interior and closure
data, including all reentrant angles. -/
theorem sector_decay :
    Specs.D12Complex.Ch14.CornerDecay.sector_decay_type :=
  StraightSectorDecay.sector_decay

/-- Zero boundary values at a conformal corner give the original two power
estimates. Circular exhaustion stages supply these actual local charts through
`IsCircularExhaustion` and `BoundarySectors`. No estimate at the vertex is an
assumption, and the gradient exponent may be negative. -/
theorem corner_decay :
    Specs.D12Complex.Ch14.CornerDecay.corner_decay_type :=
  corner_decay_of_sector_decay sector_decay

/-- The supplied exhaustion geometry gives precisely the hypotheses of the
local theorems at every corner and every remaining analytic arc point. -/
theorem exhaustion_boundary_estimates :
    Specs.D12Complex.Ch14.CornerDecay.exhaustion_boundary_estimates_type := by
  intro Ω s r hE j
  rcases hE.1 j with ⟨_, hD, _, _, _, _, ⟨corners, hc, hs, ha⟩, _, _⟩
  refine ⟨corners, hc, ?_, ?_⟩
  · intro c hcf hcn R u hR hu hcont hzero
    exact smooth_boundary_extension _ c R u hD.2.1 (hs c hcf hcn) hR hu hcont hzero
  · intro c hcc
    obtain ⟨θ, hθ, hθ2, hchart⟩ := ha c hcc
    refine ⟨θ, hθ, hθ2, hchart, ?_⟩
    intro R u hR hu hcont hzero
    exact corner_decay _ c θ R u hD.2.1 hθ hθ2 hchart hR hu hcont hzero

end D12Complex.CornerDecay
