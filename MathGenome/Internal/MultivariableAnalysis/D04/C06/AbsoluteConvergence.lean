import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.AbsoluteConvergence
import MathGenome.Internal.MultivariableAnalysis.D04.C06.ImproperExhaustions
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.MetricSpace.Cauchy

noncomputable section
open Set Filter Topology
open scoped Classical ENNReal
namespace D04.AbsoluteConvergence
open Darboux JordanRegions ImproperExhaustions
abbrev improperIntegral := @Specs.D04.C06.AbsoluteConvergence.Model.improperIntegral
abbrev LocallyVectorRiemannIntegrable :=
  @Specs.D04.C06.AbsoluteConvergence.Model.LocallyVectorRiemannIntegrable
abbrev vectorAbsoluteMass := @Specs.D04.C06.AbsoluteConvergence.Model.vectorAbsoluteMass
abbrev VectorAbsolutelyConvergent :=
  @Specs.D04.C06.AbsoluteConvergence.Model.VectorAbsolutelyConvergent
abbrev vectorImproperIntegral := @Specs.D04.C06.AbsoluteConvergence.Model.vectorImproperIntegral
abbrev HasVectorIntegralAlong := @Specs.D04.C06.AbsoluteConvergence.Model.HasVectorIntegralAlong

variable {n : ℕ} {Ω S T : Set (E n)} {f g : E n → ℝ}

lemma region_nonneg {h : S → ℝ} (hi : RegionIntegrable h) (hp : ∀ x, 0 ≤ h x) :
    0 ≤ regionIntegral h := by
  obtain ⟨Q, hQ, hiQ⟩ := hi.2
  rw [integral_eq_on_enclosing_box h hi hQ hiQ]
  have hz := integrable_const Q 0
  have hh := integral_mono hz hiQ (fun x _ => by
    by_cases hx : x ∈ S
    · simpa only [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension,
        dite_eq_left hx] using hp ⟨x, hx⟩
    · simp [zeroExtension_of_not_mem h hx])
  simpa only [integral_const, zero_mul] using hh

lemma region_mono {h l : S → ℝ} (hh : RegionIntegrable h) (hl : RegionIntegrable l)
    (hhl : ∀ x, h x ≤ l x) : regionIntegral h ≤ regionIntegral l := by
  obtain ⟨Q, hQ, hiQ⟩ := hh.2
  have hlQ := (region_integrable_iff_box l hQ).mp hl
  rw [integral_eq_on_enclosing_box h hh hQ hiQ,
    integral_eq_on_enclosing_box l hl hQ hlQ]
  apply integral_mono hiQ hlQ
  intro x _
  by_cases hx : x ∈ S
  · simpa only [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension,
      dite_eq_left hx] using hhl ⟨x, hx⟩
  · simp only [zeroExtension_of_not_mem _ hx, le_refl]

/-- Restriction to a Jordan subset uses the product of the actual zero
extension with its indicator. No continuity of the integrand is assumed. -/
lemma region_restrict (hf : RegionIntegrable (fun x : S => f x))
    (hT : Jordan T) (hTS : T ⊆ S) : RegionIntegrable (fun x : T => f x) := by
  obtain ⟨Q, hQ, hfQ⟩ := hf.2
  have htQ : Encloses T Q := (closure_mono hTS).trans hQ
  have hi := integrable_mul hfQ (jordan_integrable_on_box hT htQ)
  have he : zeroExtension (fun x : T => f x) =
      fun x => zeroExtension (fun x : S => f x) x * JordanRegions.indicator T x := by
    funext x
    by_cases ht : x ∈ T
    · simp [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension,
        JordanRegions.indicator, Specs.D04.C06.JordanRegions.Model.indicator, ht, hTS ht]
    · simp [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension,
        JordanRegions.indicator, Specs.D04.C06.JordanRegions.Model.indicator, ht]
  exact (region_integrable_iff_box _ htQ).mpr (he ▸ hi)

lemma region_mono_set (hfS : RegionIntegrable (fun x : S => f x))
    (hfT : RegionIntegrable (fun x : T => f x)) (hST : S ⊆ T)
    (hp : ∀ x ∈ T, 0 ≤ f x) :
    regionIntegral (fun x : S => f x) ≤ regionIntegral (fun x : T => f x) := by
  obtain ⟨Q, hQ, htQ⟩ := hfT.2
  have hsQ : Encloses S Q := (closure_mono hST).trans hQ
  have hiS := (region_integrable_iff_box _ hsQ).mp hfS
  rw [integral_eq_on_enclosing_box _ hfS hsQ hiS,
    integral_eq_on_enclosing_box _ hfT hQ htQ]
  apply integral_mono hiS htQ
  intro x _
  by_cases hs : x ∈ S
  · simp [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension, hs, hST hs]
  · by_cases ht : x ∈ T
    · simpa [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension, hs, ht] using hp x ht
    · simp [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension, hs, ht]

lemma region_diff (hS : Jordan S) (hT : Jordan T) (hTS : T ⊆ S)
    (hf : RegionIntegrable (fun x : S => f x)) :
    regionIntegral (fun x : (S \ T : Set (E n)) => f x) =
      regionIntegral (fun x : S => f x) - regionIntegral (fun x : T => f x) := by
  have he : (S \ T) ∪ T = S := sdiff_union_of_subset hTS
  have hiD := region_restrict hf (jordan_diff hS hT) sdiff_subset
  have hiT := region_restrict hf hT hTS
  have hadd := (integral_disjoint_union f (jordan_diff hS hT) hT disjoint_sdiff_left hiD hiT).2
  rw [he] at hadd
  linarith

lemma integral_increment_bound (hS : Jordan S) (hT : Jordan T) (hTS : T ⊆ S)
    (hf : RegionIntegrable (fun x : S => f x)) :
    |regionIntegral (fun x : S => f x) - regionIntegral (fun x : T => f x)| ≤
      regionIntegral (fun x : S => |f x|) - regionIntegral (fun x : T => |f x|) := by
  have hiD := region_restrict hf (jordan_diff hS hT) sdiff_subset
  rw [← region_diff hS hT hTS hf,
    ← region_diff (f := fun x => |f x|) hS hT hTS (scalar_abs_bound _ hf).1]
  exact (scalar_abs_bound _ hiD).2

lemma locally_integrable_abs (hf : LocallyRiemannIntegrable Ω f) :
    LocallyRiemannIntegrable Ω (fun x => |f x|) := fun Q hQ => integrable_abs (hf Q hQ)

lemma integral_abs_nonneg (hΩ : IsOpen Ω) (hf : LocallyRiemannIntegrable Ω f)
    (hS : CompactJordanSubset Ω S) : 0 ≤ regionIntegral (fun x : S => |f x|) :=
  region_nonneg (scalar_abs_bound _ (locally_integrable_on_compact_jordan hΩ hf hS)).1
    (fun _ => abs_nonneg _)

lemma ofReal_integral_abs_le (hS : CompactJordanSubset Ω S) :
    ENNReal.ofReal (regionIntegral (fun x : S => |f x|)) ≤ absoluteMass Ω f :=
  le_iSup_of_le S (le_iSup_of_le hS le_rfl)

lemma integral_abs_le_mass (hfin : absoluteMass Ω f < ⊤) (hS : CompactJordanSubset Ω S) :
    regionIntegral (fun x : S => |f x|) ≤ (absoluteMass Ω f).toReal :=
  (ENNReal.ofReal_le_iff_le_toReal hfin.ne).mp (ofReal_integral_abs_le hS)

lemma nonnegative_exhaustion (hΩ : IsOpen Ω) (hf : LocallyRiemannIntegrable Ω f)
    (hp : ∀ x ∈ Ω, 0 ≤ f x) {K : ℕ → Set (E n)} (hK : RegularExhaustion Ω K) :
    Monotone (fun j => regionIntegral (fun x : K j => f x)) ∧
    (⨆ j, ENNReal.ofReal (regionIntegral (fun x : K j => f x))) = absoluteMass Ω f ∧
    Tendsto (fun j => ENNReal.ofReal (regionIntegral (fun x : K j => f x)))
      atTop (𝓝 (absoluteMass Ω f)) := by
  have hi (S) (hS : CompactJordanSubset Ω S) := locally_integrable_on_compact_jordan hΩ hf hS
  have habs (S) (hS : CompactJordanSubset Ω S) :
      regionIntegral (fun x : S => |f x|) = regionIntegral (fun x : S => f x) := by
    congr 1
    funext x
    exact abs_of_nonneg (hp x (hS.2.2 x.property))
  have hm : Monotone (fun j => regionIntegral (fun x : K j => f x)) := by
    intro i j hij
    exact region_mono_set (hi _ (hK.1 i)) (hi _ (hK.1 j))
      (regular_exhaustion_mono hK hij) (fun x hx => hp x ((hK.1 j).2.2 hx))
  have he : (⨆ j, ENNReal.ofReal (regionIntegral (fun x : K j => f x))) =
      absoluteMass Ω f := by
    apply le_antisymm
    · apply iSup_le
      intro j
      rw [← habs _ (hK.1 j)]
      exact ofReal_integral_abs_le (hK.1 j)
    · apply iSup_le
      intro S
      apply iSup_le
      intro hS
      obtain ⟨j, hj⟩ := compact_contained_in_exhaustion hK hS.1 hS.2.2
      change ENNReal.ofReal (regionIntegral (fun x : S => |f x|)) ≤ _
      rw [habs S hS]
      apply le_iSup_of_le j
      exact ENNReal.ofReal_le_ofReal (region_mono_set (hi _ hS) (hi _ (hK.1 j)) hj
        (fun x hx => hp x ((hK.1 j).2.2 hx)))
  refine ⟨hm, he, ?_⟩
  rw [← he]
  exact tendsto_atTop_iSup (ENNReal.ofReal_mono.comp hm)

lemma absolute_mass_abs : absoluteMass Ω (fun x => |f x|) = absoluteMass Ω f := by
  simp only [absoluteMass, Specs.D04.C06.ImproperExhaustions.Model.absoluteMass, abs_abs]

lemma absolute_mass_tendsto (hΩ : IsOpen Ω) (hf : AbsolutelyConvergent Ω f)
    {K : ℕ → Set (E n)} (hK : RegularExhaustion Ω K) :
    Tendsto (fun j => regionIntegral (fun x : K j => |f x|)) atTop
      (𝓝 (absoluteMass Ω f).toReal) := by
  have he := (nonnegative_exhaustion hΩ (locally_integrable_abs hf.1)
    (fun x _ => abs_nonneg (f x)) hK).2.2
  rw [absolute_mass_abs] at he
  have ht := (ENNReal.tendsto_toReal hf.2.ne).comp he
  convert ht using 1
  funext j
  exact (ENNReal.toReal_ofReal (integral_abs_nonneg hΩ hf.1 (hK.1 j))).symm

lemma integral_along_exists (hΩ : IsOpen Ω) (hf : AbsolutelyConvergent Ω f)
    {K : ℕ → Set (E n)} (hK : RegularExhaustion Ω K) : ∃ I, HasIntegralAlong f K I := by
  apply cauchySeq_tendsto_of_complete
  apply cauchySeq_of_le_tendsto_0' (fun j => (absoluteMass Ω f).toReal -
    regionIntegral (fun x : K j => |f x|))
  · intro i j hij
    rw [Real.dist_eq, abs_sub_comm]
    exact (integral_increment_bound (hK.1 j).2.1 (hK.1 i).2.1
      (regular_exhaustion_mono hK hij)
      (locally_integrable_on_compact_jordan hΩ hf.1 (hK.1 j))).trans
      (sub_le_sub_right (integral_abs_le_mass hf.2 (hK.1 j)) _)
  · simpa using (tendsto_const_nhds (x := (absoluteMass Ω f).toReal)).sub (absolute_mass_tendsto hΩ hf hK)

lemma limit_tail_bound (hΩ : IsOpen Ω) (hf : AbsolutelyConvergent Ω f)
    {K : ℕ → Set (E n)} (hK : RegularExhaustion Ω K) {I : ℝ}
    (hI : HasIntegralAlong f K I) (hS : CompactJordanSubset Ω S) :
    |I - regionIntegral (fun x : S => f x)| ≤
      (absoluteMass Ω f).toReal - regionIntegral (fun x : S => |f x|) := by
  obtain ⟨j, hj⟩ := compact_contained_in_exhaustion hK hS.1 hS.2.2
  apply le_of_tendsto (hI.sub tendsto_const_nhds).abs
  filter_upwards [eventually_ge_atTop j] with k hk
  exact (integral_increment_bound (hK.1 k).2.1 hS.2.1
    (hj.trans (regular_exhaustion_mono hK hk))
    (locally_integrable_on_compact_jordan hΩ hf.1 (hK.1 k))).trans
    (sub_le_sub_right (integral_abs_le_mass hf.2 (hK.1 k)) _)

lemma exhaustion_limits_equal (hΩ : IsOpen Ω) (hf : AbsolutelyConvergent Ω f)
    {K L : ℕ → Set (E n)} (hK : RegularExhaustion Ω K) (hL : RegularExhaustion Ω L)
    {I J : ℝ} (hI : HasIntegralAlong f K I) (hJ : HasIntegralAlong f L J) : I = J := by
  have htail : Tendsto (fun j => 2 * ((absoluteMass Ω f).toReal -
      regionIntegral (fun x : K j => |f x|))) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := (absoluteMass Ω f).toReal)).sub (absolute_mass_tendsto hΩ hf hK)).const_mul 2
  have hh : |I - J| ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds htail
    (Eventually.of_forall (fun j => by
      have h1 := limit_tail_bound hΩ hf hK hI (hK.1 j)
      have h2 := limit_tail_bound hΩ hf hL hJ (hK.1 j)
      calc |I - J| ≤ |I - regionIntegral (fun x : K j => f x)| +
          |regionIntegral (fun x : K j => f x) - J| := abs_sub_le _ _ _
        _ ≤ 2 * ((absoluteMass Ω f).toReal - regionIntegral (fun x : K j => |f x|)) := by
          rw [abs_sub_comm (regionIntegral _) J]
          linarith))
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)))

lemma universal_limit_exists (hΩ : IsOpen Ω) (hf : AbsolutelyConvergent Ω f) :
    ∃ I : ℝ, ∀ K, RegularExhaustion Ω K → HasIntegralAlong f K I := by
  obtain ⟨K, hK⟩ := regular_exhaustion_exists Ω hΩ
  obtain ⟨I, hI⟩ := integral_along_exists hΩ hf hK
  refine ⟨I, fun L hL => ?_⟩
  obtain ⟨J, hJ⟩ := integral_along_exists hΩ hf hL
  rw [exhaustion_limits_equal hΩ hf hK hL hI hJ]
  exact hJ

lemma absolute_exhaustion (hΩ : IsOpen Ω) (hf : AbsolutelyConvergent Ω f) :
    (∀ K, RegularExhaustion Ω K → HasIntegralAlong f K (improperIntegral Ω f)) ∧
    ∀ K, CompactJordanSubset Ω K →
      |improperIntegral Ω f - regionIntegral (fun x : K => f x)| ≤
        (absoluteMass Ω f).toReal - regionIntegral (fun x : K => |f x|) := by
  have hex := universal_limit_exists hΩ hf
  have hlim : ∀ K, RegularExhaustion Ω K → HasIntegralAlong f K (improperIntegral Ω f) := by
    change ∀ K, RegularExhaustion Ω K → HasIntegralAlong f K
      (if h : ∃ I : ℝ, ∀ L, RegularExhaustion Ω L → HasIntegralAlong f L I then
        Classical.choose h else 0)
    rw [dite_eq_left hex]
    exact Classical.choose_spec hex
  refine ⟨hlim, ?_⟩
  intro S hS
  obtain ⟨K, hK⟩ := regular_exhaustion_exists Ω hΩ
  exact limit_tail_bound hΩ hf hK (hlim K hK) hS

lemma absolute_limit_unique (hΩ : IsOpen Ω) (hf : AbsolutelyConvergent Ω f)
    {K : ℕ → Set (E n)} {I : ℝ} (hK : RegularExhaustion Ω K)
    (hI : HasIntegralAlong f K I) : I = improperIntegral Ω f :=
  integral_along_unique hI ((absolute_exhaustion hΩ hf).1 K hK)

/-- Comparison is made on Ω alone; ambient extension values do not enter. -/
lemma absoluteMass_mono (hΩ : IsOpen Ω) (hf : LocallyRiemannIntegrable Ω f)
    (hg : LocallyRiemannIntegrable Ω g) (hfg : ∀ x ∈ Ω, |f x| ≤ |g x|) :
    absoluteMass Ω f ≤ absoluteMass Ω g := by
  apply iSup_le
  intro S
  apply iSup_le
  intro hS
  change ENNReal.ofReal (regionIntegral (fun x : S => |f x|)) ≤ _
  exact (ENNReal.ofReal_le_ofReal (region_mono
    (scalar_abs_bound _ (locally_integrable_on_compact_jordan hΩ hf hS)).1
    (scalar_abs_bound _ (locally_integrable_on_compact_jordan hΩ hg hS)).1
    (fun x => hfg x (hS.2.2 x.property)))).trans (ofReal_integral_abs_le hS)

lemma locally_vector_norm {k : ℕ} {f : E n → E k}
    (hf : LocallyVectorRiemannIntegrable Ω f) :
    LocallyRiemannIntegrable Ω (fun x => ‖f x‖) := by
  intro Q hQ
  exact Darboux.integrable_norm (fun i => hf i Q hQ)

lemma vector_integrable_on_compact {k : ℕ} {f : E n → E k}
    (hΩ : IsOpen Ω) (hf : LocallyVectorRiemannIntegrable Ω f)
    (hS : CompactJordanSubset Ω S) : VectorRegionIntegrable (fun x : S => f x) :=
  ⟨hS.1.isBounded, fun i => locally_integrable_on_compact_jordan hΩ (hf i) hS⟩

lemma coordinate_absolutely_convergent {k : ℕ} {f : E n → E k}
    (hΩ : IsOpen Ω) (hf : VectorAbsolutelyConvergent Ω f) (i : Fin k) :
    AbsolutelyConvergent Ω (fun x => f x i) := by
  refine ⟨hf.1 i, lt_of_le_of_lt ?_ hf.2⟩
  apply absoluteMass_mono hΩ (hf.1 i) (locally_vector_norm hf.1)
  intro x _
  simpa only [Real.norm_eq_abs, abs_norm] using PiLp.norm_apply_le (f x) i

lemma vector_integral_diff {k : ℕ} {f : E n → E k}
    (hS : Jordan S) (hT : Jordan T) (hTS : T ⊆ S)
    (hf : VectorRegionIntegrable (fun x : S => f x)) :
    vectorRegionIntegral (fun x : (S \ T : Set (E n)) => f x) =
      vectorRegionIntegral (fun x : S => f x) - vectorRegionIntegral (fun x : T => f x) := by
  ext i
  change regionIntegral (fun x : (S \ T : Set (E n)) => f x i) =
    regionIntegral (fun x : S => f x i) - regionIntegral (fun x : T => f x i)
  exact region_diff (f := fun x => f x i) hS hT hTS (hf.2 i)

lemma vector_increment_bound {k : ℕ} {f : E n → E k}
    (hS : Jordan S) (hT : Jordan T) (hTS : T ⊆ S)
    (hf : VectorRegionIntegrable (fun x : S => f x)) :
    ‖vectorRegionIntegral (fun x : S => f x) - vectorRegionIntegral (fun x : T => f x)‖ ≤
      regionIntegral (fun x : S => ‖f x‖) - regionIntegral (fun x : T => ‖f x‖) := by
  have hiD : VectorRegionIntegrable (fun x : (S \ T : Set (E n)) => f x) :=
    ⟨(jordan_bounded (jordan_diff hS hT)),
      fun i => region_restrict (f := fun x => f x i) (hf.2 i) (jordan_diff hS hT) sdiff_subset⟩
  rw [← vector_integral_diff hS hT hTS hf,
    ← region_diff (f := fun x => ‖f x‖) hS hT hTS (vector_integrable_norm _ hf)]
  exact vector_norm_bound _ hiD

lemma vector_integral_along (hΩ : IsOpen Ω) {k : ℕ} {f : E n → E k}
    (hf : VectorAbsolutelyConvergent Ω f) {K : ℕ → Set (E n)}
    (hK : RegularExhaustion Ω K) :
    HasVectorIntegralAlong f K (vectorImproperIntegral Ω f) := by
  have hc : ∀ i : Fin k, Tendsto (fun j => regionIntegral (fun x : K j => f x i))
      atTop (𝓝 (improperIntegral Ω (fun x => f x i))) :=
    fun i => (absolute_exhaustion hΩ (coordinate_absolutely_convergent hΩ hf i)).1 K hK
  exact (D04.tendsto_iff_coordinate_tendsto _ _).mpr hc

lemma vector_limit_tail_bound {k : ℕ} {f : E n → E k}
    (hΩ : IsOpen Ω) (hf : VectorAbsolutelyConvergent Ω f)
    {K : ℕ → Set (E n)} (hK : RegularExhaustion Ω K) {I : E k}
    (hI : HasVectorIntegralAlong f K I) (hS : CompactJordanSubset Ω S) :
    ‖I - vectorRegionIntegral (fun x : S => f x)‖ ≤
      (vectorAbsoluteMass Ω f).toReal - regionIntegral (fun x : S => ‖f x‖) := by
  obtain ⟨j, hj⟩ := compact_contained_in_exhaustion hK hS.1 hS.2.2
  apply le_of_tendsto (hI.sub tendsto_const_nhds).norm
  filter_upwards [eventually_ge_atTop j] with l hl
  have hb : regionIntegral (fun x : K l => ‖f x‖) ≤ (vectorAbsoluteMass Ω f).toReal := by
    change regionIntegral (fun x : K l => ‖f x‖) ≤ (absoluteMass Ω (fun x => ‖f x‖)).toReal
    simpa only [abs_norm] using (integral_abs_le_mass (f := fun x => ‖f x‖) hf.2 (hK.1 l))
  exact (vector_increment_bound (hK.1 l).2.1 hS.2.1
    (hj.trans (regular_exhaustion_mono hK hl))
    (vector_integrable_on_compact hΩ hf.1 (hK.1 l))).trans (sub_le_sub_right hb _)

lemma vector_absolute_exhaustion {k : ℕ} {f : E n → E k}
    (hΩ : IsOpen Ω) (hf : VectorAbsolutelyConvergent Ω f) :
    (∀ K, RegularExhaustion Ω K → HasVectorIntegralAlong f K (vectorImproperIntegral Ω f)) ∧
    ∀ K, CompactJordanSubset Ω K →
      ‖vectorImproperIntegral Ω f - vectorRegionIntegral (fun x : K => f x)‖ ≤
        (vectorAbsoluteMass Ω f).toReal - regionIntegral (fun x : K => ‖f x‖) := by
  refine ⟨fun _ hK => vector_integral_along hΩ hf hK, fun S hS => ?_⟩
  obtain ⟨K, hK⟩ := regular_exhaustion_exists Ω hΩ
  exact vector_limit_tail_bound hΩ hf hK (vector_integral_along hΩ hf hK) hS

end D04.AbsoluteConvergence
