import MathGenome.Internal.LinearPDE.P201Specs.Potential.GreenRepresentation
import MathGenome.Internal.LinearPDE.P201.Potential.GreenConstruction
import MathGenome.Internal.LinearPDE.P201.Potential.GreenCompactC2
import MathGenome.Internal.LinearPDE.P201.Potential.GreenCollarLocalization
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
open Set MeasureTheory Metric
open scoped ContDiff
namespace P201.GreenRepresentation
open P201Specs P201Specs.GreenRepresentation

theorem compact_smooth : CompactSmoothStatement :=
  @P201.GreenCompactC2.compact_smooth

/-- Global integrability of a Green row on a bounded domain. -/
theorem green_integrable {n : ℕ} (Ω : Domain n)
    (hb : Bornology.IsBounded (Ω : Set (Space n))) {x : Space n} (hx : x ∈ Ω)
    (g : Space n → ℝ) (hg : P201Specs.GreenConstruction.IsGreenFunction Ω x g) :
    IntegrableOn g (Ω : Set _) volume :=
  P201.GreenCompactC2.green_integrable Ω hb hx g hg

/-- Every continuous forcing has a genuine Green volume integral. -/
theorem green_mul_continuous_integrable {n : ℕ} (Ω : Domain n)
    (hb : Bornology.IsBounded (Ω : Set (Space n))) {x : Space n} (hx : x ∈ Ω)
    (g : Space n → ℝ) (hg : P201Specs.GreenConstruction.IsGreenFunction Ω x g)
    (f : Space n → ℝ) (hf : ContinuousOn f (closure (Ω : Set _))) :
    IntegrableOn (fun y => g y * f y) (Ω : Set _) volume :=
  P201.GreenCompactC2.green_mul_continuous_integrable Ω hb hx g hg f hf

/-- Integration by parts with an affine weight, on any subinterval of the
original C² interval. Keeping its derivative fixed avoids changing endpoint
conventions when the integration is split at the pole. -/
lemma affine_weight_second {a b c d : ℝ} (hab : a < b)
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Icc a b)) (k l : ℝ) :
    (∫ t in c..d, (k*t+l) * derivWithin (derivWithin f (Icc a b)) (Icc a b) t) =
      (k*d+l) * derivWithin f (Icc a b) d -
      (k*c+l) * derivWithin f (Icc a b) c - k * (f d - f c) := by
  let S := Icc a b
  let f₁ := derivWithin f S
  let f₂ := derivWithin f₁ S
  have hs : UniqueDiffOn ℝ S := uniqueDiffOn_Icc hab
  have hsub : Icc c d ⊆ S := Icc_subset_Icc hac hdb
  have hf₁ : ContDiffOn ℝ 1 f₁ S := hf.derivWithin hs (by norm_num)
  have hc₁ : ContinuousOn f₁ (Icc c d) := hf₁.continuousOn.mono hsub
  have hc₂ : ContinuousOn f₂ (Icc c d) :=
    (hf₁.continuousOn_derivWithin hs (by norm_num)).mono hsub
  have hd₁ (t : ℝ) (ht : t ∈ Icc c d) : HasDerivWithinAt f₁ (f₂ t) (Icc c d) t :=
    (hf₁.differentiableOn (by norm_num) t (hsub ht)).hasDerivWithinAt.mono hsub
  have hFTC : (∫ t in c..d, f₁ t) = f d - f c := by
    apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hcd
      (hf.continuousOn.mono hsub)
    · intro t ht
      exact ((hf.differentiableOn (by norm_num) t (hsub (Ioo_subset_Icc_self ht))).hasDerivWithinAt.hasDerivAt
        (Icc_mem_nhds (hac.trans_lt ht.1) (ht.2.trans_le hdb))).hasDerivWithinAt
    · exact hc₁.intervalIntegrable_of_Icc hcd
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (u := fun t : ℝ => k*t+l) (v := f₁) (u' := fun _ => k) (v' := f₂)
    (by
      simp only [uIcc_of_le hcd]
      intro t ht
      simpa using (((hasDerivAt_id t).const_mul k).add_const l).hasDerivWithinAt)
    (by simpa only [uIcc_of_le hcd] using hd₁)
    (intervalIntegrable_const) (hc₂.intervalIntegrable_of_Icc hcd)
  rw [intervalIntegral.integral_const_mul, hFTC] at hparts
  exact hparts

theorem interval : IntervalStatement := by
  intro a b x hax hxb f hf
  have hab := hax.trans hxb
  let f₁ := derivWithin f (Icc a b)
  let f₂ := derivWithin f₁ (Icc a b)
  have hs : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  have hc₂ : ContinuousOn f₂ (Icc a b) :=
    (hf.derivWithin hs (m := 1) (by norm_num)).continuousOn_derivWithin hs (by norm_num)
  have hi : IntervalIntegrable (fun y => P201Specs.GreenConstruction.intervalKernel a b x y * (-f₂ y))
      volume a b :=
    ((P201.GreenConstruction.intervalKernel_continuous a b x).continuousOn.mul hc₂.neg).intervalIntegrable_of_Icc hab.le
  have hileft := hi.mono_set (show Set.uIcc a x ⊆ Set.uIcc a b by
    simpa [uIcc_of_le hax.le, uIcc_of_le hab.le] using Icc_subset_Icc le_rfl hxb.le)
  have hiright := hi.mono_set (show Set.uIcc x b ⊆ Set.uIcc a b by
    simpa [uIcc_of_le hxb.le, uIcc_of_le hab.le] using Icc_subset_Icc hax.le le_rfl)
  have hL := affine_weight_second hab le_rfl hax.le hxb.le f hf
    ((b-x)/(b-a)) (-a*((b-x)/(b-a)))
  have hR := affine_weight_second hab hax.le hxb.le le_rfl f hf
    (-(x-a)/(b-a)) (b*((x-a)/(b-a)))
  have hLI : (∫ y in a..x, P201Specs.GreenConstruction.intervalKernel a b x y * (-f₂ y)) =
      -(∫ y in a..x, (((b-x)/(b-a))*y-a*((b-x)/(b-a))) * f₂ y) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with y hy
    have hyx : y ≤ x := (show y ∈ Ioc a x by simpa [uIoc_of_le hax.le] using hy).2
    rw [P201.GreenConstruction.intervalKernel_left hyx]
    ring
  have hRI : (∫ y in x..b, P201Specs.GreenConstruction.intervalKernel a b x y * (-f₂ y)) =
      -(∫ y in x..b, ((-(x-a)/(b-a))*y+b*((x-a)/(b-a))) * f₂ y) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with y hy
    have hxy : x ≤ y := (show y ∈ Ioc x b by simpa [uIoc_of_le hxb.le] using hy).1.le
    rw [P201.GreenConstruction.intervalKernel_right hxy]
    ring
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hileft hiright
  simp only [neg_mul, ← sub_eq_add_neg] at hL
  have hvolume : (∫ y in Ioo a b, P201Specs.GreenConstruction.intervalKernel a b x y * (-f₂ y)) =
      -((b-x)/(b-a) * x-a*((b-x)/(b-a))) * f₁ x +
      ((b-x)/(b-a) * a-a*((b-x)/(b-a))) * f₁ a +
      (b-x)/(b-a) * (f x-f a) -
      ((-(x-a)/(b-a))*b+b*((x-a)/(b-a))) * f₁ b +
      ((-(x-a)/(b-a))*x+b*((x-a)/(b-a))) * f₁ x -
      (x-a)/(b-a) * (f b-f x) := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hab.le, ← hsplit, hLI, hRI, hL, hR]
    dsimp [f₁, f₂]
    ring
  refine ⟨?_, ?_⟩
  · exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).mp hi
  · change f x = (∫ y in Ioo a b, P201Specs.GreenConstruction.intervalKernel a b x y * (-f₂ y)) - _
    rw [hvolume]
    have hne : b-a ≠ 0 := sub_ne_zero.mpr hab.ne'
    field_simp [hne]
    ring

/-- Assemble the full theorem from the analytic row representation and
the normalized upstream construction. -/
theorem full_of_rows
    (rows : ∀ {m : ℕ} (Ω : Domain (m+1)),
      Bornology.IsBounded (Ω : Set (Space (m+1))) → HasCkBoundary Ω 2 →
      ∀ x ∈ Ω, ∀ g : Space (m+1) → ℝ,
        P201Specs.GreenConstruction.IsGreenFunction Ω x g →
        P201Specs.GreenConstruction.HasCollarNormalTrace Ω x g →
        ∀ u : Space (m+1) → ℝ, C2OnClosure Ω u → Represents Ω x g u) :
    FullStatement := by
  refine ⟨interval, ?_⟩
  intro m Ω hb hC
  obtain ⟨G, hG, hsym, hpos, hzero, _, hinterval⟩ :=
    P201.GreenConstruction.construction Ω hb hC
  refine ⟨G, hG, hsym, hpos, hzero, hinterval, ?_⟩
  intro u hu x hx
  exact rows Ω hb hC x hx (G x) (hG x hx).1 (hG x hx).2.2 u hu

lemma local_laplacian_sub {n : ℕ} (u v : Space n → ℝ) (y : Space n)
    (hu : ContDiffAt ℝ 2 u y) (hv : ContDiffAt ℝ 2 v y) :
    laplacian (u - v) y = laplacian u y - laplacian v y := by
  change P201Specs.laplacian (u - v) y = P201Specs.laplacian u y - P201Specs.laplacian v y
  rw [P201.MeanValues.laplacian_bridge (u - v) y (hu.sub hv),
    hu.laplacian_sub hv,
    ← P201.MeanValues.laplacian_bridge u y hu,
    ← P201.MeanValues.laplacian_bridge v y hv]

lemma cutoff_laplacian {n : ℕ} (Ω : Domain n)
    (u : Space n → ℝ) (hu : ContDiffOn ℝ 2 u (closure (Ω : Set _)))
    {x : Space n} (β : ContDiffBump x)
    (hv : ContDiffOn ℝ 2 (P201Specs.GreenCollarLocalization.remainder β u) (closure (Ω : Set _)))
    (y : Space n) (hy : y ∈ Ω) :
    laplacian (P201Specs.GreenCollarLocalization.compactPart β u) y = laplacian u y - laplacian (P201Specs.GreenCollarLocalization.remainder β u) y := by
  have heq : P201Specs.GreenCollarLocalization.compactPart β u = u - P201Specs.GreenCollarLocalization.remainder β u := by
    funext z
    simp only [P201Specs.GreenCollarLocalization.compactPart,
      P201Specs.GreenCollarLocalization.remainder, Pi.sub_apply]
    ring
  rw [heq]
  exact local_laplacian_sub u (P201Specs.GreenCollarLocalization.remainder β u) y
    ((hu.mono subset_closure).contDiffAt (Ω.isOpen.mem_nhds hy))
    ((hv.mono subset_closure).contDiffAt (Ω.isOpen.mem_nhds hy))

/-- The complete row formula follows by evaluating the compact part and
localizing the nonsingular remainder to the physical outer boundary. -/
theorem represents {m : ℕ} (Ω : Domain (m+1))
    (hb : Bornology.IsBounded (Ω : Set (Space (m+1))))
    (hC : HasCkBoundary Ω 2) (x : Space (m+1)) (hx : x ∈ Ω)
    (g : Space (m+1) → ℝ) (hg : P201Specs.GreenConstruction.IsGreenFunction Ω x g)
    (hcollar : P201Specs.GreenConstruction.HasCollarNormalTrace Ω x g)
    (u : Space (m+1) → ℝ) (hu : C2OnClosure Ω u) : Represents Ω x g u := by
  obtain ⟨r, hr, hball, hL, β, w, D, τ, b, hβ, hw, hΔw, hτ, hbphys,
      hremInt, hremFlux, ν, vi, hν, hvi, houterInt, houterFlux⟩ :=
    P201.GreenCollarLocalization.localization Ω hb hC x hx g hg hcollar u hu
  obtain ⟨hin, hout, hφ, hφcompact, hφsupport, hφx, hv, hzero, houter, hvalues⟩ := hβ
  have heval := P201.GreenCompactC2.compact_c2 (Nat.succ_le_succ (Nat.zero_le m)) Ω x hx g hg
    (P201Specs.GreenCollarLocalization.compactPart β u) hφ hφcompact hφsupport
  have hInt := P201.GreenCompactC2.volume_integrability Ω hb hC x hx g hg u hu
  have hsplit :
      (∫ y in Ω, g y * (-laplacian (P201Specs.GreenCollarLocalization.compactPart β u) y)) =
      (∫ y in Ω, g y * (-laplacian u y)) +
        ∫ y in Ω, g y * laplacian (P201Specs.GreenCollarLocalization.remainder β u) y := by
    rw [← integral_add hInt hremInt]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with y hy
    rw [cutoff_laplacian Ω u hu β hv y hy]
    ring
  have hformula : u x = (∫ y in Ω, g y * (-laplacian u y)) - τ b := by
    rw [hφx] at heval
    rw [hremFlux]
    linarith only [heval.2, hsplit]
  exact ⟨hInt, r, hr, hball, hL, w, D, τ, b, hw, hΔw, hτ, hbphys,
    hformula, ν, vi, hν, hvi, houterInt, houterFlux⟩

/-- Green representation on every bounded C² open set, including the
normalized construction, uniqueness, symmetry, component signs, physical
outward boundary flux and signed one-dimensional endpoint formula. -/
theorem full : FullStatement := by
  apply full_of_rows
  intro m Ω hb hC x hx g hg hcollar u hu
  exact represents Ω hb hC x hx g hg hcollar u hu

end P201.GreenRepresentation
