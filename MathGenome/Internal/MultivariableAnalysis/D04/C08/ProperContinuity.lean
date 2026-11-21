import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C08.ProperContinuity
import MathGenome.Internal.MultivariableAnalysis.D04.C06.JordanRegions
import MathGenome.Internal.MultivariableAnalysis.D04.C01.CompactContinuity
import Mathlib.Topology.UniformSpace.HeineCantor

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace D04.ProperContinuity
open Darboux JordanRegions
variable {n m k : ℕ} {S : Set (E n)} {P : Set (E m)}

lemma scalar_sub_integrable {f g : S → ℝ} (hf : RegionIntegrable f)
    (hg : RegionIntegrable g) : RegionIntegrable (fun x => f x - g x) := by
  have hQ := enclosingBox_encloses (encloses_bounded hf.2.choose_spec.1)
  apply (region_integrable_iff_box _ hQ).mpr
  have he : zeroExtension (fun x => f x - g x) =
      (fun x => zeroExtension f x - zeroExtension g x) := by
    funext x
    by_cases hx : x ∈ S
    · simp [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension, hx]
    · simp [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension, hx]
  rw [he]
  exact Darboux.integrable_sub ((region_integrable_iff_box _ hQ).mp hf)
    ((region_integrable_iff_box _ hQ).mp hg)

lemma scalar_integral_sub {f g : S → ℝ} (hf : RegionIntegrable f)
    (hg : RegionIntegrable g) :
    regionIntegral (fun x => f x - g x) = regionIntegral f - regionIntegral g := by
  have hQ := enclosingBox_encloses (encloses_bounded hf.2.choose_spec.1)
  have hi := (region_integrable_iff_box _ hQ).mp hf
  have hj := (region_integrable_iff_box _ hQ).mp hg
  have hd := scalar_sub_integrable hf hg
  have he : zeroExtension (fun x => f x - g x) =
      (fun x => zeroExtension f x - zeroExtension g x) := by
    funext x
    by_cases hx : x ∈ S <;>
      simp [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension, hx]
  rw [integral_eq_on_enclosing_box _ hf hQ hi,
    integral_eq_on_enclosing_box _ hg hQ hj,
    integral_eq_on_enclosing_box _ hd hQ ((region_integrable_iff_box _ hQ).mp hd)]
  simpa only [he] using Darboux.integral_sub hi hj (Darboux.integrable_sub hi hj)

lemma vector_sub_integrable {f g : S → E k} (hf : VectorRegionIntegrable f)
    (hg : VectorRegionIntegrable g) : VectorRegionIntegrable (fun x => f x - g x) :=
  ⟨hf.1, fun i => scalar_sub_integrable (hf.2 i) (hg.2 i)⟩

lemma vector_integral_sub {f g : S → E k} (hf : VectorRegionIntegrable f)
    (hg : VectorRegionIntegrable g) :
    vectorRegionIntegral (fun x => f x - g x) = vectorRegionIntegral f - vectorRegionIntegral g := by
  ext i
  exact scalar_integral_sub (hf.2 i) (hg.2 i)

lemma integral_sub_le (hS : Jordan S) {f g : S → E k}
    (hf : VectorRegionIntegrable f) (hg : VectorRegionIntegrable g)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, ‖f x - g x‖ ≤ M) :
    ‖vectorRegionIntegral f - vectorRegionIntegral g‖ ≤ volume S * M := by
  rw [← vector_integral_sub hf hg, mul_comm]
  exact vector_uniform_bound hS _ (vector_sub_integrable hf hg) M hM hb

lemma vector_region_bounded {f : S → E k} (hf : VectorRegionIntegrable f) :
    RegionBounded f := by
  obtain ⟨M, hM⟩ := (vector_integrable_norm f hf).1
  exact ⟨M, fun x => by simpa only [Real.norm_eq_abs, abs_norm] using hM x⟩

lemma difference_bddAbove {f g : S → E k} (hf : VectorRegionIntegrable f)
    (hg : VectorRegionIntegrable g) : BddAbove (range (fun x => ‖f x - g x‖)) := by
  obtain ⟨M, hM⟩ := vector_region_bounded hf
  obtain ⟨N, hN⟩ := vector_region_bounded hg
  exact ⟨M + N, by rintro _ ⟨x, rfl⟩; exact (norm_sub_le _ _).trans (add_le_add (hM x) (hN x))⟩

lemma integral_sub_bound (hS : Jordan S) (f g : S → E k)
    (hf : VectorRegionIntegrable f) (hg : VectorRegionIntegrable g) :
    ‖vectorRegionIntegral f - vectorRegionIntegral g‖ ≤
      volume S * sSup (range (fun x => ‖f x - g x‖)) := by
  by_cases he : IsEmpty S
  · have hzero (v : S → E k) : vectorRegionIntegral v = 0 := by
      have hs : S = ∅ := by ext x; exact ⟨fun hx => (he.false ⟨x,hx⟩).elim, False.elim⟩
      subst S
      exact (vector_empty v).2
    simp [hzero, Set.range_eq_empty_iff.mpr he]
  · have hn : Nonempty S := not_isEmpty_iff.mp he
    have hb := difference_bddAbove hf hg
    have hu (x : S) : ‖f x - g x‖ ≤ sSup (range (fun x => ‖f x - g x‖)) :=
      le_csSup hb (mem_range_self x)
    obtain ⟨x⟩ := hn
    exact integral_sub_le hS hf hg ((norm_nonneg _).trans (hu x)) hu

/-- Uniform convergence of slices passes to their Riemann integrals along any
filter; no continuity or measurability in the parameter is needed. -/
lemma integral_tendsto_of_uniform {ι : Type*} {l : Filter ι} (hS : Jordan S)
    (f : ι → S → E k) (g : S → E k)
    (hf : ∀ p, VectorRegionIntegrable (f p)) (hg : VectorRegionIntegrable g)
    (hu : TendstoUniformly f g l) :
    Tendsto (fun p => vectorRegionIntegral (f p)) l (𝓝 (vectorRegionIntegral g)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε / (volume S + 1)
  have hv := volume_nonneg hS
  have hd : 0 < volume S + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hd
  filter_upwards [(Metric.tendstoUniformly_iff.mp hu) δ hδ] with p hp
  rw [dist_eq_norm]
  have he := integral_sub_le hS (hf p) hg hδ.le
    (fun x => by simpa only [dist_eq_norm, norm_sub_rev] using (hp x).le)
  have heq : δ * (volume S + 1) = ε := div_mul_cancel₀ _ (ne_of_gt hd)
  nlinarith

lemma parameter_continuity (hS : Jordan S) (f : S → P → E k)
    (hf : ∀ p, VectorRegionIntegrable (fun x => f x p)) (p₀ : P)
    (hu : Tendsto (fun p => sSup (range (fun x => ‖f x p - f x p₀‖)))
      (𝓝 p₀) (𝓝 0)) :
    ContinuousAt (fun p => vectorRegionIntegral (fun x => f x p)) p₀ := by
  apply integral_tendsto_of_uniform hS (fun p x => f x p) (fun x => f x p₀) hf (hf p₀)
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp hu) ε hε] with p hp x
  have he := le_csSup (difference_bddAbove (hf p) (hf p₀))
    (mem_range_self (f := fun x => ‖f x p - f x p₀‖) x)
  rw [dist_eq_norm, norm_sub_rev]
  exact he.trans_lt (lt_of_le_of_lt (le_abs_self _) (by simpa [Real.dist_eq] using hp))

/-- Uniform limits remain Riemann integrable on the actual region. -/
lemma region_uniform_limit (f : ℕ → S → ℝ) (g : S → ℝ)
    (hf : ∀ j, RegionIntegrable (f j)) (hu : TendstoUniformly f g atTop) :
    RegionIntegrable g := by
  have hQ := enclosingBox_encloses (encloses_bounded (hf 0).2.choose_spec.1)
  apply (region_integrable_iff_box _ hQ).mpr
  apply (Darboux.uniform_limit (fun j => zeroExtension (f j)) (zeroExtension g)
    (fun j => (region_integrable_iff_box _ hQ).mp (hf j)) ?_).choose
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendstoUniformly_iff.mp hu) ε hε] with j hj x _
  by_cases hx : x ∈ S
  · simpa [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension, hx] using hj ⟨x,hx⟩
  · simpa [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension, hx] using hε

lemma vector_region_uniform_limit (f : ℕ → S → E k) (g : S → E k)
    (hf : ∀ j, VectorRegionIntegrable (f j)) (hu : TendstoUniformly f g atTop) :
    VectorRegionIntegrable g := by
  refine ⟨(hf 0).1, fun i => region_uniform_limit (fun j x => f j x i)
    (fun x => g x i) (fun j => (hf j).2 i) ?_⟩
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendstoUniformly_iff.mp hu) ε hε] with j hj x
  have hi := PiLp.norm_apply_le (p := (2 : ℝ≥0∞)) (g x - f j x) i
  exact lt_of_le_of_lt (by simpa [Real.dist_eq] using hi) (by simpa [dist_eq_norm] using hj x)

lemma uniform_limits (hS : Jordan S) (f : ℕ → S → P → E k) (g : S → P → E k)
    (hf : ∀ j p, VectorRegionIntegrable (fun x => f j x p))
    (hu : TendstoUniformly (fun j (z : S × P) => f j z.1 z.2)
      (fun z => g z.1 z.2) atTop) :
    (∀ p, VectorRegionIntegrable (fun x => g x p)) ∧
    TendstoUniformly (fun j p => vectorRegionIntegral (fun x => f j x p))
      (fun p => vectorRegionIntegral (fun x => g x p)) atTop := by
  have hg (p : P) : VectorRegionIntegrable (fun x => g x p) := by
    apply vector_region_uniform_limit (fun j x => f j x p) (fun x => g x p)
      (fun j => hf j p)
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [(Metric.tendstoUniformly_iff.mp hu) ε hε] with j hj x
    exact hj (x,p)
  refine ⟨hg, Metric.tendstoUniformly_iff.mpr ?_⟩
  intro ε hε
  let δ := ε / (volume S + 1)
  have hv := volume_nonneg hS
  have hd : 0 < volume S + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hd
  filter_upwards [(Metric.tendstoUniformly_iff.mp hu) δ hδ] with j hj p
  rw [dist_eq_norm, norm_sub_rev]
  have he := integral_sub_le hS (hf j p) (hg p) hδ.le
    (fun x => by simpa [dist_eq_norm, norm_sub_rev] using (hj (x,p)).le)
  have heq : δ * (volume S + 1) = ε := div_mul_cancel₀ _ (ne_of_gt hd)
  nlinarith

lemma continuous_closure_integrable (hS : Jordan S) (f : closure S → E k)
    (hf : Continuous f) :
    VectorRegionIntegrable (fun x : S => f ⟨x, subset_closure x.property⟩) := by
  refine ⟨jordan_bounded hS, fun i => ?_⟩
  by_cases hn : n = 0
  · subst n
    exact region_integrable_zero_dim _ _
  · exact integrable_continuous_on_closure (Nat.pos_of_ne_zero hn) hS (fun x => f x i)
      ((PiLp.continuous_apply 2 (fun _ : Fin k => ℝ) i).comp hf)

lemma joint_continuity (hS : Jordan S) (f : closure S × P → E k) (hf : Continuous f) :
    (∀ p : P, VectorRegionIntegrable (fun x : S => f (⟨x, subset_closure x.property⟩, p))) ∧
    Continuous (fun p : P => vectorRegionIntegral
      (fun x : S => f (⟨x, subset_closure x.property⟩, p))) := by
  have hi (p : P) := continuous_closure_integrable hS (fun x => f (x,p))
    (hf.comp (continuous_id.prodMk continuous_const))
  refine ⟨hi, continuous_iff_continuousAt.mpr fun p₀ => ?_⟩
  apply integral_tendsto_of_uniform hS _ _ hi (hi p₀)
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  let K := closure S
  have hk : IsCompact K := (jordan_bounded hS).isCompact_closure
  let : CompactSpace K := isCompact_iff_compactSpace.mp hk
  have hc : Continuous (fun z : P × K => f (z.2,z.1)) :=
    hf.comp (continuous_snd.prodMk continuous_fst)
  obtain ⟨v, hv, hb⟩ := (@IsCompact.mem_uniformity_of_prod P K (E k) inferInstance inferInstance
      (PiLp.uniformSpace 2 (fun _ : Fin k => ℝ)))
    (k := (univ : Set K)) (s := (univ : Set P))
    (u := {z : E k × E k | dist z.1 z.2 < ε}) (f := fun p (x : K) => f (x,p))
    isCompact_univ
    (by
      rw [univ_prod_univ]
      exact hc.continuousOn)
    (mem_univ p₀) (Metric.dist_mem_uniformity hε)
  have hv' : v ∈ 𝓝 p₀ := by simpa only [nhdsWithin_univ] using hv
  filter_upwards [hv'] with p hp x
  have h := hb p hp ⟨x, subset_closure x.property⟩ (mem_univ _)
  simpa only [mem_ofPred, dist_comm] using h

lemma zero_volume (hS : Jordan S) (hv : volume S = 0) (f : S → P → E k)
    (hf : ∀ p, VectorRegionIntegrable (fun x => f x p)) :
    (fun p => vectorRegionIntegral (fun x => f x p)) = (fun _ : P => 0) := by
  funext p
  exact (vector_zero_volume hS hv _ (vector_region_bounded (hf p))).2

lemma empty (f : (∅ : Set (E n)) → P → E k) :
    (∀ p, VectorRegionIntegrable (fun x => f x p)) ∧
    (fun p => vectorRegionIntegral (fun x => f x p)) = (fun _ : P => 0) :=
  ⟨fun p => (vector_empty (fun x => f x p)).1,
    funext fun p => (vector_empty (fun x => f x p)).2⟩

end D04.ProperContinuity
