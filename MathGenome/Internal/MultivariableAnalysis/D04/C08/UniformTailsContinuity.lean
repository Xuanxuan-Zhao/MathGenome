import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C08.UniformTailsContinuity
import MathGenome.Internal.MultivariableAnalysis.D04.C06.AbsoluteConvergence
import MathGenome.Internal.MultivariableAnalysis.D04.C08.ProperContinuity

noncomputable section
set_option maxHeartbeats 1200000
open Set Filter Topology
open scoped Classical ENNReal
namespace D04.UniformTailsContinuity
open Darboux JordanRegions ImproperExhaustions AbsoluteConvergence
abbrev truncatedIntegral := @Specs.D04.C08.UniformTailsContinuity.Model.truncatedIntegral
abbrev tailIntegral := @Specs.D04.C08.UniformTailsContinuity.Model.tailIntegral
abbrev exhaustionIntegral := @Specs.D04.C08.UniformTailsContinuity.Model.exhaustionIntegral
abbrev UniformImproperConverges := @Specs.D04.C08.UniformTailsContinuity.Model.UniformImproperConverges
abbrev UniformCauchyTails := @Specs.D04.C08.UniformTailsContinuity.Model.UniformCauchyTails
abbrev UniformAbsoluteTails := @Specs.D04.C08.UniformTailsContinuity.Model.UniformAbsoluteTails
abbrev EndpointwiseUniformAbsoluteTails :=
  @Specs.D04.C08.UniformTailsContinuity.Model.EndpointwiseUniformAbsoluteTails
abbrev EndpointwiseUniformTails := @Specs.D04.C08.UniformTailsContinuity.Model.EndpointwiseUniformTails

variable {n m k : ℕ} {Ω : Set (E n)} {K : ℕ → Set (E n)}
  {f : E n → E m → E k} {B : Set (E m)}

lemma tail_difference (hΩ : IsOpen Ω) (hK : RegularExhaustion Ω K)
    (p : E m) (hf : LocallyVectorRiemannIntegrable Ω (fun x => f x p))
    (j l : ℕ) (hjl : j ≤ l) :
    tailIntegral K f j l p = truncatedIntegral K f l p - truncatedIntegral K f j p :=
  vector_integral_diff (f := fun x => f x p) (hK.1 l).2.1 (hK.1 j).2.1 (regular_exhaustion_mono hK hjl)
    (vector_integrable_on_compact hΩ hf (hK.1 l))

lemma tails_iff_uniformCauchy (hΩ : IsOpen Ω) (hK : RegularExhaustion Ω K)
    (hf : ∀ p ∈ B, LocallyVectorRiemannIntegrable Ω (fun x => f x p)) :
    UniformCauchyTails K f B ↔ UniformCauchySeqOn (truncatedIntegral K f) atTop B := by
  rw [Metric.uniformCauchySeqOn_iff]
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N, fun i hi j hj p hp => ?_⟩
    rcases le_total i j with hij | hji
    · simpa only [dist_eq_norm, norm_sub_rev,
        tail_difference hΩ hK p (hf p hp) i j hij] using hN i hi j hij p hp
    · simpa only [dist_eq_norm,
        tail_difference hΩ hK p (hf p hp) j i hji] using hN j hj i hji p hp
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N, fun j hj l hjl p hp => ?_⟩
    change ‖tailIntegral K f j l p‖ < ε
    rw [tail_difference hΩ hK p (hf p hp) j l hjl]
    exact hN l (hj.trans hjl) j hj p hp

lemma uniform_converges_to_integral (hΩ : IsOpen Ω) (hK : RegularExhaustion Ω K)
    (hf : ∀ p ∈ B, LocallyVectorRiemannIntegrable Ω (fun x => f x p))
    (ht : UniformCauchyTails K f B) :
    TendstoUniformlyOn (truncatedIntegral K f)
      (fun p => exhaustionIntegral K (fun x => f x p)) atTop B := by
  have hc := (tails_iff_uniformCauchy hΩ hK hf).mp ht
  exact hc.tendstoUniformlyOn_of_tendsto (fun p hp => (hc.cauchySeq hp).tendsto_limUnder)

lemma convergence_iff_cauchy (hΩ : IsOpen Ω) (hK : RegularExhaustion Ω K)
    (hf : ∀ p ∈ B, LocallyVectorRiemannIntegrable Ω (fun x => f x p)) :
    UniformImproperConverges K f B ↔ UniformCauchyTails K f B := by
  constructor
  · rintro ⟨F, hF⟩
    exact (tails_iff_uniformCauchy hΩ hK hf).mpr hF.uniformCauchySeqOn
  · intro ht
    exact ⟨_, uniform_converges_to_integral hΩ hK hf ht⟩

lemma supremum_tails (K : ℕ → Set (E n)) (f : E n → E m → E k) (B : Set (E m)) :
    UniformCauchyTails K f B ↔
    ∀ ε > (0 : ℝ), ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ l ≥ j,
      ∃ c : ℝ, 0 ≤ c ∧ c < ε ∧ ∀ p ∈ B, ‖tailIntegral K f j l p‖ ≤ c := by
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := h (ε / 2) (by positivity)
    exact ⟨N, fun j hj l hjl => ⟨ε / 2, by positivity, by linarith,
      fun p hp => (hN j hj l hjl p hp).le⟩⟩
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N, fun j hj l hjl p hp => ?_⟩
    obtain ⟨c, _, hc, hb⟩ := hN j hj l hjl
    exact (hb p hp).trans_lt hc

lemma absolute_implies_signed (hΩ : IsOpen Ω) (hK : RegularExhaustion Ω K)
    (hf : ∀ p ∈ B, LocallyVectorRiemannIntegrable Ω (fun x => f x p))
    (ht : UniformAbsoluteTails K f B) : UniformCauchyTails K f B := by
  intro ε hε
  obtain ⟨N, hN⟩ := ht ε hε
  refine ⟨N, fun j hj l hjl p hp => ?_⟩
  have hi : VectorRegionIntegrable (fun x : (K l \ K j : Set (E n)) => f x p) :=
    ⟨jordan_bounded (jordan_diff (hK.1 l).2.1 (hK.1 j).2.1), fun i =>
      region_restrict (f := fun x => f x p i)
        ((vector_integrable_on_compact hΩ (hf p hp) (hK.1 l)).2 i)
        (jordan_diff (hK.1 l).2.1 (hK.1 j).2.1) sdiff_subset⟩
  exact (vector_norm_bound _ hi).trans_lt (hN j hj l hjl p hp)

lemma uniform_limit_continuous {F : E m → E k}
    (hc : ∀ j, ContinuousOn (truncatedIntegral K f j) B)
    (hu : TendstoUniformlyOn (truncatedIntegral K f) F atTop B) : ContinuousOn F B :=
  hu.continuousOn (Frequently.of_forall hc)


lemma improper_integral_continuous (hΩ : IsOpen Ω) (hK : RegularExhaustion Ω K)
    (hf : ∀ p ∈ B, LocallyVectorRiemannIntegrable Ω (fun x => f x p))
    (hc : ∀ j, ContinuousOn (truncatedIntegral K f j) B)
    (ht : UniformCauchyTails K f B) :
    ContinuousOn (fun p => exhaustionIntegral K (fun x => f x p)) B :=
  uniform_limit_continuous hc (uniform_converges_to_integral hΩ hK hf ht)

lemma domination_absolute_tails (hΩ : IsOpen Ω) (hK : RegularExhaustion Ω K)
    (hf : ∀ p ∈ B, LocallyVectorRiemannIntegrable Ω (fun x => f x p))
    {M : E n → ℝ} (hM : AbsolutelyConvergent Ω M) (_hpos : ∀ x ∈ Ω, 0 ≤ M x)
    (hdom : ∀ p ∈ B, ∀ x ∈ Ω, ‖f x p‖ ≤ M x) : UniformAbsoluteTails K f B := by
  have hlim : Tendsto (fun j => (absoluteMass Ω M).toReal -
      regionIntegral (fun x : K j => |M x|)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (absoluteMass Ω M).toReal)).sub
      (absolute_mass_tendsto hΩ hM hK)
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
  refine ⟨N, fun j hj l hjl p hp => ?_⟩
  have hfL : VectorRegionIntegrable (fun x : K l => f x p) :=
    vector_integrable_on_compact hΩ (hf p hp) (hK.1 l)
  have hiF : RegionIntegrable (fun x : (K l \ K j : Set (E n)) => ‖f x p‖) := region_restrict (f := fun x => ‖f x p‖) (vector_integrable_norm _ hfL)
    (jordan_diff (hK.1 l).2.1 (hK.1 j).2.1) sdiff_subset
  have hiM : RegionIntegrable (fun x : K l => |M x|) :=
    locally_integrable_on_compact_jordan hΩ (locally_integrable_abs hM.1) (hK.1 l)
  have hiD : RegionIntegrable (fun x : (K l \ K j : Set (E n)) => |M x|) :=
    region_restrict (f := fun x => |M x|) hiM (jordan_diff (hK.1 l).2.1 (hK.1 j).2.1) sdiff_subset
  calc
    regionIntegral (fun x : (K l \ K j : Set (E n)) => ‖f x p‖) ≤
        regionIntegral (fun x : (K l \ K j : Set (E n)) => |M x|) :=
      region_mono (h := fun x : (K l \ K j : Set (E n)) => ‖f x p‖)
        (l := fun x : (K l \ K j : Set (E n)) => |M x|) hiF hiD (fun x => (hdom p hp x ((hK.1 l).2.2 x.property.1)).trans
        (le_abs_self _))
    _ = regionIntegral (fun x : K l => |M x|) -
        regionIntegral (fun x : K j => |M x|) :=
      region_diff (f := fun x => |M x|) (hK.1 l).2.1 (hK.1 j).2.1 (regular_exhaustion_mono hK hjl) hiM
    _ ≤ (absoluteMass Ω M).toReal - regionIntegral (fun x : K j => |M x|) :=
      sub_le_sub_right (integral_abs_le_mass hM.2 (hK.1 l)) _
    _ < ε := hN j hj

lemma endpointwise_common_threshold {r : ℕ} (K : Fin r → ℕ → Set (E n))
    (f : Fin r → E n → E m → E k) (B : Set (E m)) :
    EndpointwiseUniformTails K f B ↔
    ∀ ε > (0 : ℝ), ∃ j₀ : ℕ, ∀ e, ∀ j ≥ j₀, ∀ l ≥ j, ∀ p ∈ B,
      ‖tailIntegral (K e) (f e) j l p‖ < ε := by
  constructor
  · intro h ε hε
    choose N hN using fun e => h e ε hε
    refine ⟨Finset.univ.sup N, fun e j hj l hjl p hp => ?_⟩
    exact hN e j ((Finset.le_sup (Finset.mem_univ e)).trans hj) l hjl p hp
  · intro h e ε hε
    obtain ⟨N, hN⟩ := h ε hε
    exact ⟨N, hN e⟩

lemma endpointwise_absolute_common_threshold {r : ℕ} (K : Fin r → ℕ → Set (E n))
    (f : Fin r → E n → E m → E k) (B : Set (E m)) :
    EndpointwiseUniformAbsoluteTails K f B ↔
    ∀ ε > (0 : ℝ), ∃ j₀ : ℕ, ∀ e, ∀ j ≥ j₀, ∀ l ≥ j, ∀ p ∈ B,
      regionIntegral (fun x : (K e l \ K e j : Set (E n)) => ‖f e x p‖) < ε := by
  constructor
  · intro h ε hε
    choose N hN using fun e => h e ε hε
    refine ⟨Finset.univ.sup N, fun e j hj l hjl p hp => ?_⟩
    exact hN e j ((Finset.le_sup (Finset.mem_univ e)).trans hj) l hjl p hp
  · intro h e ε hε
    obtain ⟨N, hN⟩ := h ε hε
    exact ⟨N, hN e⟩

/-- A uniform limit along any nontrivial filter is a uniform sequential limit
of selected approximants. The sequence only serves the Riemann closure theorem;
no countability assumption on the original parameter filter is used. -/
lemma uniform_approximation_sequence {ι X : Type*} {l : Filter ι} [NeBot l]
    {v : ι → X → E k} {w : X → E k} {A : ι → Prop}
    (hA : ∀ᶠ p in l, A p) (hu : TendstoUniformly v w l) :
    ∃ s : ℕ → ι, (∀ j, A (s j)) ∧ TendstoUniformly (fun j => v (s j)) w atTop := by
  have hex : ∀ j : ℕ, ∃ p, A p ∧ ∀ x, dist (w x) (v p x) < 1 / ((j : ℝ) + 1) := by
    intro j
    exact (hA.and ((Metric.tendstoUniformly_iff.mp hu) _ (by positivity))).exists
  choose s hs using hex
  refine ⟨s, fun j => (hs j).1, Metric.tendstoUniformly_iff.mpr ?_⟩
  intro ε hε
  filter_upwards [(tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (gt_mem_nhds hε)] with j hj x
  exact ((hs j).2 x).trans hj

lemma region_uniform_limit_filter {ι : Type*} {l : Filter ι} [NeBot l]
    {S : Set (E n)} {v : ι → S → E k} {w : S → E k} (hS : Jordan S)
    (hv : ∀ᶠ p in l, VectorRegionIntegrable (v p)) (hu : TendstoUniformly v w l) :
    VectorRegionIntegrable w ∧
    Tendsto (fun p => vectorRegionIntegral (v p)) l (𝓝 (vectorRegionIntegral w)) := by
  obtain ⟨s, hs, hsu⟩ := uniform_approximation_sequence hv hu
  have hw := ProperContinuity.vector_region_uniform_limit (fun j => v (s j)) w hs hsu
  refine ⟨hw, Metric.tendsto_nhds.mpr ?_⟩
  intro ε hε
  let δ := ε / (volume S + 1)
  have hvS := volume_nonneg hS
  have hd : 0 < volume S + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hd
  filter_upwards [hv, (Metric.tendstoUniformly_iff.mp hu) δ hδ] with p hp hup
  rw [dist_eq_norm]
  have hb := ProperContinuity.integral_sub_le hS hp hw hδ.le
    (fun x => by simpa only [dist_eq_norm, norm_sub_rev] using (hup x).le)
  have he : δ * (volume S + 1) = ε := div_mul_cancel₀ _ hd.ne'
  nlinarith


/-- The Moore--Osgood argument for signed finite-dimensional truncations. -/
lemma uniformCauchy_limit_interchange {ι : Type*} {l : Filter ι} [NeBot l]
    {A : ℕ → ι → E k} {G : ℕ → E k} {B : Set ι} (hB : B ∈ l)
    (hc : UniformCauchySeqOn A atTop B)
    (hproper : ∀ j, Tendsto (A j) l (𝓝 (G j))) :
    Tendsto G atTop (𝓝 (limUnder atTop G)) ∧
    Tendsto (fun p => limUnder atTop (fun j => A j p)) l (𝓝 (limUnder atTop G)) := by
  have hcG : CauchySeq G := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.uniformCauchySeqOn_iff.mp hc) (ε / 2) (by positivity)
    refine ⟨N, fun i hi j hj => ?_⟩
    have hb : ‖G i - G j‖ ≤ ε / 2 :=
      le_of_tendsto ((hproper i).sub (hproper j)).norm
        ((show ∀ᶠ p in l, p ∈ B from hB).mono (fun p hp => (hN i hi j hj p hp).le))
    exact hb.trans_lt (by linarith)
  have hu : TendstoUniformlyOn A
      (fun p => limUnder atTop (fun j => A j p)) atTop B :=
    hc.tendstoUniformlyOn_of_tendsto (fun p hp => (hc.cauchySeq hp).tendsto_limUnder)
  refine ⟨hcG.tendsto_limUnder, ?_⟩
  exact (hu.tendstoUniformlyOnFilter.mono_right (le_principal_iff.mpr hB)).tendsto_of_eventually_tendsto
    (Eventually.of_forall hproper) hcG.tendsto_limUnder

lemma locally_uniform_limit {g : E n → E k} (l : Filter (E m)) [NeBot l] (hB : B ∈ l)
    (hK : RegularExhaustion Ω K)
    (hf : ∀ p ∈ B, LocallyVectorRiemannIntegrable Ω (fun x => f x p))
    (hu : ∀ j, TendstoUniformlyOn (fun p x => f x p) g l (K j)) :
    LocallyVectorRiemannIntegrable Ω g := by
  intro i Q hQ
  obtain ⟨j, hj⟩ := compact_contained_in_exhaustion hK (DiscontinuityCriterion.carrier_compact Q) hQ
  obtain ⟨s, hs, hsu⟩ := uniform_approximation_sequence
    ((show ∀ᶠ p in l, p ∈ B from hB).mono (fun p hp => hf p hp))
    ((tendstoUniformlyOn_iff_restrict).mp (hu j))
  apply (Darboux.uniform_limit (fun t x => f x (s t) i) (fun x => g x i)
    (fun t => hs t i Q hQ) ?_).choose
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendstoUniformly_iff.mp hsu) ε hε] with t ht x hx
  have hi := PiLp.norm_apply_le (p := (2 : ℝ≥0∞)) (g x - f x (s t)) i
  exact lt_of_le_of_lt (by simpa [Real.dist_eq, dist_eq_norm] using hi)
    (ht ⟨x, hj hx⟩)

lemma improper_limit {g : E n → E k} (l : Filter (E m)) (hl : NeBot l) (hB : B ∈ l)
    (hΩ : IsOpen Ω) (hK : RegularExhaustion Ω K)
    (hf : ∀ p ∈ B, LocallyVectorRiemannIntegrable Ω (fun x => f x p))
    (hu : ∀ j, TendstoUniformlyOn (fun p x => f x p) g l (K j))
    (ht : UniformCauchyTails K f B) :
    LocallyVectorRiemannIntegrable Ω g ∧
    (∀ j, VectorRegionIntegrable (fun x : K j => g x)) ∧
    HasVectorIntegralAlong g K (exhaustionIntegral K g) ∧
    (∀ p ∈ B, HasVectorIntegralAlong (fun x => f x p) K
      (exhaustionIntegral K (fun x => f x p))) ∧
    Tendsto (fun p => exhaustionIntegral K (fun x => f x p)) l
      (𝓝 (exhaustionIntegral K g)) := by
  haveI : NeBot l := hl
  have hproper (j : ℕ) := region_uniform_limit_filter (hK.1 j).2.1
    ((show ∀ᶠ p in l, p ∈ B from hB).mono (fun p hp => vector_integrable_on_compact hΩ (hf p hp) (hK.1 j)))
    ((tendstoUniformlyOn_iff_restrict).mp (hu j))
  have hc := (tails_iff_uniformCauchy hΩ hK hf).mp ht
  have hdouble := uniformCauchy_limit_interchange hB hc (fun j => (hproper j).2)
  exact ⟨locally_uniform_limit l hB hK hf hu, fun j => (hproper j).1, hdouble.1,
    fun p hp => (hc.cauchySeq hp).tendsto_limUnder, hdouble.2⟩

/-- The scalar member of the finite-dimensional interface uses ordinary
absolute values and the actual scalar Riemann integral. -/
lemma scalar_tail_identity (K : ℕ → Set (E n)) (v : E n → E m → ℝ)
    (j l : ℕ) (p : E m) :
    ‖tailIntegral K (fun x p => WithLp.toLp 2 (fun _ : Fin 1 => v x p)) j l p‖ =
      |regionIntegral (fun x : (K l \ K j : Set (E n)) => v x p)| := by
  change ‖WithLp.toLp 2 (Function.const (Fin 1)
    (regionIntegral (fun x : (K l \ K j : Set (E n)) => v x p)))‖ = _
  simpa using
    (PiLp.norm_toLp_const' (p := (2 : ℝ≥0∞))
      (ι := Fin 1) (regionIntegral (fun x : (K l \ K j : Set (E n)) => v x p)))

end D04.UniformTailsContinuity
