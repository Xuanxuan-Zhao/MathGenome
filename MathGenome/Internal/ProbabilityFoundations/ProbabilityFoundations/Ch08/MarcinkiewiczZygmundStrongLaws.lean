import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundStrongLaws
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundTruncation
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch08.EtemadiStrongLaw
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch08.MZDeterministicMeans
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch08.MZFiniteLimitMoment

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

noncomputable section

namespace ProbabilityFoundations.Ch08

universe u

theorem mz_first_moment :
    Specs.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundStrongLaws.firstMomentType := by
  intro Ω mΩ P hP X p hX hp hmom
  apply ((integrable_const (1 : ℝ)).add hmom).mono' hX.aestronglyMeasurable
  filter_upwards [] with ω
  change |X ω| ≤ 1 + |X ω| ^ p
  by_cases h : |X ω| ≤ 1
  · exact h.trans (le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _))
  · have hpow : |X ω| ≤ |X ω| ^ p := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h) hp
    linarith

theorem mz_exponent_one :
    Specs.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundStrongLaws.exponentOneType := by
  intro Ω mΩ P hP X hX hind hd hmom
  have hfirst : Integrable (X 0) P := mz_first_moment P (X 0) 1 (hX 0) le_rfl hmom
  have hi := (Ch02.independentRandomElements_iff_iIndepFun P X).mp hind
  have hs := ProbabilityTheory.strong_law_ae_real X hfirst (fun i j hij => hi.indepFun hij) hd
  filter_upwards [hs] with ω hω
  have ht := hω.sub (tendsto_const_nhds (x := ∫ t, X 0 t ∂P))
  simp only [sub_self] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  dsimp only [MZ.weight,
    Specs.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundTruncation.weight]
  norm_num
  field_simp

namespace MZ

/-- An eventually fixed finite change in a partial sum vanishes under MZ scaling. -/
lemma constant_difference_tendsto {p : ℝ} (hp : 0 < p) (a b : ℕ → ℝ)
    (h : ∃ c : ℝ, ∀ᶠ n in atTop, a n - b n = c) :
    Tendsto (fun n => (a n - b n) / weight p n) atTop (𝓝 0) := by
  obtain ⟨c, hc⟩ := h
  have hw : Tendsto (weight p) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < 1 / p)).comp tendsto_natCast_atTop_atTop
  exact ((tendsto_const_nhds (x := c)).div_atTop hw).congr'
    (hc.mono fun n hn => by dsimp only; rw [hn])

/-- Assembly of the stochastic truncation theorem with any proved deterministic
mean correction. This does not assume an MZ conclusion. -/
lemma transfer_from_truncated_means {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (p c : ℝ)
    (hX : ∀ k, Measurable (X k))
    (hind : Specs.ProbabilityFoundations.Ch02.IndependenceInterfaces.IndependentRandomElementsValue P X)
    (hd : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hp : 0 < p) (hp2 : p < 2) (hmom : Integrable (fun ω => |X 0 ω| ^ p) P)
    (hmean : Tendsto
      (fun n => ((∑ k ∈ Finset.range n, ∫ t, truncated p X k t ∂P) - (n : ℝ) * c) /
        weight p n) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n => ((∑ k ∈ Finset.range n, X k ω) - (n : ℝ) * c) / weight p n)
      atTop (𝓝 0) := by
  filter_upwards [mz_centered_truncation P X p hX hind hd hp hp2 hmom,
    mz_eventually_constant_difference P X p hX hd hp hp2 hmom] with ω hc he
  have hz := constant_difference_tendsto hp
    (fun n => ∑ k ∈ Finset.range n, X k ω)
    (fun n => ∑ k ∈ Finset.range n, truncated p X k ω) he
  have hcenter : Tendsto
      (fun n => (∑ k ∈ Finset.range n,
        (truncated p X k ω - ∫ t, truncated p X k t ∂P)) / weight p n)
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_comm] using hc
  have htotal := (hz.add hcenter).add hmean
  simp only [add_zero] at htotal
  convert htotal using 1
  ext n
  simp only [Finset.sum_sub_distrib]
  ring

end MZ

/-- The uncentered Marcinkiewicz–Zygmund law below exponent one. -/
theorem mz_subunit :
    Specs.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundStrongLaws.subunitType := by
  intro Ω mΩ P hP X p hX hind hd hp hp1 hmom
  have hmean := mz_deterministic_means_subunit P X p hX hd hp hp1 hmom
  have ht := MZ.transfer_from_truncated_means P X p 0 hX hind hd hp
    (by linarith : p < 2) hmom (by simpa only [mul_zero, sub_zero] using hmean)
  simpa only [mul_zero, sub_zero] using ht

/-- The centered Marcinkiewicz–Zygmund law, including exponent one and
the first moment needed to define its centering as an expectation. -/
theorem mz_centered :
    Specs.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundStrongLaws.centeredType := by
  intro Ω mΩ P hP X p hX hind hd hp hp2 hmom
  refine ⟨mz_first_moment P (X 0) p (hX 0) hp hmom, ?_⟩
  rcases hp.eq_or_lt with heq | hgt
  · subst p
    exact mz_exponent_one P X hX hind hd hmom
  · exact MZ.transfer_from_truncated_means P X p (∫ t, X 0 t ∂P)
      hX hind hd (by linarith) hp2 hmom
      (mz_deterministic_means_centered P X p hX hd hgt hp2 hmom)

/-- Once the p-th moment has been established, a finite MZ limit determines
the centering for p > 1. No condition is imposed on the limit function. -/
theorem mz_centering_eq_of_moment {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (p c : ℝ)
    (Z : Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : Specs.ProbabilityFoundations.Ch02.IndependenceInterfaces.IndependentRandomElementsValue P X)
    (hd : ∀ k, IdentDistrib (X k) (X 0) P P) (hp : 1 < p)
    (hmom : Integrable (fun ω => |X 0 ω| ^ p) P)
    (hconv : ∀ᵐ ω ∂P, Tendsto
      (fun n => ((∑ k ∈ Finset.range n, X k ω) - (n : ℝ) * c) / MZ.weight p n)
      atTop (𝓝 (Z ω))) : c = ∫ t, X 0 t ∂P := by
  have hint := mz_first_moment P (X 0) p (hX 0) hp.le hmom
  have hi := (Ch02.independentRandomElements_iff_iIndepFun P X).mp hind
  have hs := ProbabilityTheory.strong_law_ae_real X hint (fun i j hij => hi.indepFun hij) hd
  obtain ⟨ω, hω, hsω⟩ := (hconv.and hs).exists
  have hp0 : 0 < p := by linarith
  have hexp : 0 < 1 - 1 / p := by
    have := (div_lt_one hp0).mpr hp
    linarith
  have hr : Tendsto (fun n : ℕ => MZ.weight p n / (n : ℝ)) atTop (𝓝 0) := by
    have ht := (tendsto_rpow_neg_atTop hexp).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    apply ht.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    dsimp only [MZ.weight,
      Specs.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundTruncation.weight]
    change (n : ℝ) ^ (-(1 - 1 / p)) = (n : ℝ) ^ (1 / p) / (n : ℝ)
    rw [show -(1 - 1 / p) = 1 / p - 1 by ring, Real.rpow_sub hn0, Real.rpow_one]
  have hz := hω.mul hr
  simp only [mul_zero] at hz
  have hc : Tendsto
      (fun n => (∑ k ∈ Finset.range n, X k ω) / (n : ℝ)) atTop (𝓝 c) := by
    have ht := hz.add (tendsto_const_nhds (x := c))
    simp only [zero_add] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hw0 : MZ.weight p n ≠ 0 := (Real.rpow_pos_of_pos hn0 _).ne'
    field_simp [hw0, hn0.ne']
    ring
  exact tendsto_nhds_unique hc hsω

/-- Any finite almost sure normalized limit forces the p-th absolute moment;
above exponent one it also determines the centering. -/
theorem mz_converse :
    Specs.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundStrongLaws.converseType := by
  intro Ω mΩ P hP X p c Z hX hind hd hp hp2 hconv
  have hmom := mz_finite_limit_moment P X p c Z hX hind hd hp hp2 hconv
  exact ⟨hmom, fun hp1 =>
    mz_centering_eq_of_moment P X p c Z hX hind hd hp1 hmom hconv⟩

end ProbabilityFoundations.Ch08
