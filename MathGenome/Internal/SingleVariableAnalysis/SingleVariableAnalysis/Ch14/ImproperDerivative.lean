import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch14.ImproperDerivative
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch14.UniformImproper
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch12.Differentiation
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch14.ProperDerivative
import Batteries.Tactic.OpenPrivate

/-!
Differentiation of improper integral families, K03.14.improper_derivative.
The closed-interval mean estimate gives a uniform Cauchy family, with all real
truncations as indices. Scalar completeness supplies its uniform limit. The
uniform-limit derivative theorem is applied with that same index filter; it
does not require the limiting derivative to be continuous.
-/
namespace SingleVariableAnalysis.Riemann.Improper

open Set Filter
open scoped Topology
open Specs.SingleVariableAnalysis.Ch10.OneEndpoint

open private SingleVariableAnalysis.difference_bound_of_mean
  from MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch12.DerivativeUniformCauchy

/-- The derivative-limit argument for a cofinal, rather than sequential, family.
The mean inequality is an explicit argument so that the two scalar cases reuse
their already proved real and complex mean inequalities. -/
theorem uniform_limit_of_cofinal_derivatives
    {α K : Type*} [LinearOrder α] [Nonempty α] [NoMaxOrder α]
    [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]
    (mean : ∀ (f : ℝ → K) (u v M : ℝ), u < v → 0 ≤ M →
      ContinuousOn f (Icc u v) →
      (∀ t ∈ Ioo u v, DifferentiableAt ℝ f t) →
      (∀ t ∈ Ioo u v, ‖deriv f t‖ ≤ M) → ‖f v - f u‖ ≤ M * (v-u))
    (F D : α → ℝ → K) (G : ℝ → K) (c d t₀ : ℝ)
    (hcd : c ≤ d) (ht₀ : t₀ ∈ Icc c d)
    (hc : ∀ R, ContinuousOn (F R) (Icc c d))
    (hd : ∀ R t, t ∈ Ioo c d → HasDerivAt (F R) (D R t) t)
    (hg : ∀ ε : ℝ, 0 < ε → ∃ r : α, ∀ R, r < R →
      ∀ t ∈ Icc c d, ‖D R t - G t‖ < ε)
    (hbase : ∃ L : K, ∀ ε : ℝ, 0 < ε → ∃ r : α,
      ∀ R, r < R → ‖F R t₀ - L‖ < ε) :
    ∃ f : ℝ → K,
      (∀ ε : ℝ, 0 < ε → ∃ r : α, ∀ R, r < R →
        ∀ t ∈ Icc c d, ‖F R t - f t‖ < ε) ∧
      ContinuousOn f (Icc c d) ∧ ∀ t ∈ Ioo c d, HasDerivAt f (G t) t := by
  have bound (R S : α) (x M : ℝ) (hx : x ∈ Icc c d) (hM : 0 ≤ M)
      (hb : ∀ t ∈ Ioo c d, ‖D R t - D S t‖ ≤ M) :
      ‖F R x - F S x‖ ≤ ‖F R t₀ - F S t₀‖ + (d-c) * M := by
    rcases hcd.eq_or_lt with he | he
    · have hx₀ : x = t₀ := by linarith [hx.1, hx.2, ht₀.1, ht₀.2]
      simp only [hx₀, he, sub_self, zero_mul, add_zero, le_refl]
    · let H : ℕ → ℝ → K := fun n => if n = 0 then F R else F S
      have hHc : ∀ n, ContinuousOn (H n) (Icc c d) := by
        intro n; dsimp [H]; split_ifs <;> apply hc
      have hHd : ∀ n t, t ∈ Ioo c d → DifferentiableAt ℝ (H n) t := by
        intro n t ht; dsimp [H]; split_ifs <;> exact (hd _ t ht).differentiableAt
      have hHb : ∀ t ∈ Ioo c d, ‖deriv (H 0) t - deriv (H 1) t‖ ≤ M := by
        intro t ht
        simpa only [H, ite_eq_left rfl, ite_eq_right (by omega : (1 : ℕ) ≠ 0),
          (hd R t ht).deriv, (hd S t ht).deriv] using hb t ht
      simpa only [H, ite_eq_left rfl, ite_eq_right (by omega : (1 : ℕ) ≠ 0)] using
        SingleVariableAnalysis.difference_bound_of_mean mean H c d t₀ x M 1 0 he ht₀ hx hM hHc hHd hHb
  have hC : ∀ ε : ℝ, 0 < ε → ∃ r : α,
      ∀ t : Icc c d, ∀ R S : α, r < R → R < S → dist (F S t) (F R t) < ε := by
    intro ε hε
    let δ := ε / (4 * (d-c+1))
    have hpos : 0 < d-c+1 := by linarith
    have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hpos)
    obtain ⟨L, hL⟩ := hbase
    obtain ⟨r₀, hr₀⟩ := hL δ hδ
    obtain ⟨r₁, hr₁⟩ := hg δ hδ
    refine ⟨max r₀ r₁, fun t R S hR hRS => ?_⟩
    have hR₀ := (le_max_left r₀ r₁).trans_lt hR
    have hR₁ := (le_max_right r₀ r₁).trans_lt hR
    have hb : ‖F S t₀ - F R t₀‖ < 2 * δ := by
      calc
        _ ≤ ‖F S t₀ - L‖ + ‖F R t₀ - L‖ := by
          simpa only [norm_sub_rev L] using
            norm_sub_le_norm_sub_add_norm_sub (F S t₀) L (F R t₀)
        _ < δ + δ := add_lt_add (hr₀ S (hR₀.trans hRS)) (hr₀ R hR₀)
        _ = 2 * δ := by ring
    have hder (u : ℝ) (hu : u ∈ Ioo c d) : ‖D S u - D R u‖ ≤ 2 * δ := by
      calc
        _ ≤ ‖D S u - G u‖ + ‖D R u - G u‖ := by
          simpa only [norm_sub_rev (G u)] using
            norm_sub_le_norm_sub_add_norm_sub (D S u) (G u) (D R u)
        _ ≤ δ + δ := add_le_add
          (hr₁ S (hR₁.trans hRS) u (Ioo_subset_Icc_self hu)).le
          (hr₁ R hR₁ u (Ioo_subset_Icc_self hu)).le
        _ = 2 * δ := by ring
    have hid : 2 * δ + (d-c) * (2 * δ) = ε / 2 := by
      dsimp [δ]
      field_simp
      ring
    rw [dist_eq_norm]
    calc
      _ ≤ ‖F S t₀ - F R t₀‖ + (d-c) * (2 * δ) :=
        bound S R t (2 * δ) t.property (by positivity) hder
      _ < 2 * δ + (d-c) * (2 * δ) := by linarith
      _ = ε / 2 := hid
      _ < ε := half_lt_self hε
  obtain ⟨f, hf⟩ := (exists_uniform_cofinal_limit_iff
    (fun R (t : Icc c d) => F R t) inferInstance (fun r => exists_gt r)).mpr hC
  obtain ⟨fext, hext⟩ := exists_ambientExtension (Icc c d) f
  have hlim : ∀ ε : ℝ, 0 < ε → ∃ r : α, ∀ R, r < R →
      ∀ t ∈ Icc c d, ‖F R t - fext t‖ < ε := by
    intro ε hε
    obtain ⟨r, hr⟩ := hf ε hε
    refine ⟨r, fun R hR t ht => ?_⟩
    simpa only [hext ⟨t, ht⟩, dist_eq_norm] using hr R hR ⟨t, ht⟩
  have hfun : TendstoUniformlyOn F fext atTop (Icc c d) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    obtain ⟨r, hr⟩ := hlim ε hε
    filter_upwards [eventually_gt_atTop r] with R hR t ht
    simpa only [dist_eq_norm, norm_sub_rev] using hr R hR t ht
  have hder : TendstoUniformlyOn D G atTop (Ioo c d) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    obtain ⟨r, hr⟩ := hg ε hε
    filter_upwards [eventually_gt_atTop r] with R hR t ht
    simpa only [dist_eq_norm, norm_sub_rev] using hr R hR t (Ioo_subset_Icc_self ht)
  exact ⟨fext, hlim, hfun.continuousOn (Eventually.of_forall hc).frequently,
    fun t ht => hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo hder
      (Eventually.of_forall hd) (fun u hu => hfun.tendsto_at (Ioo_subset_Icc_self hu)) ht⟩

theorem improper_derivative :
    Specs.SingleVariableAnalysis.Ch14.ImproperDerivative.improperDerivative := by
  intro k a c d hcd f ft hf hft FR D G heq hc hd hDeq hg hbase
  let : Nonempty (RightIndex a ⊤) :=
    ⟨⟨a + 1, lt_add_one a, WithTop.coe_lt_top _⟩⟩
  let : NoMaxOrder (RightIndex a ⊤) := ⟨fun r => by
    obtain ⟨s, hrs, _⟩ := right_later r r
    exact ⟨s, hrs⟩⟩
  let : NormedSpace ℝ (S.scalarValue k) :=
    Specs.SingleVariableAnalysis.Ch14.ImproperDerivative.scalarRealNormedSpace k
  let : CompleteSpace (S.scalarValue k) := by
    cases k with
    | real => exact inferInstanceAs (CompleteSpace ℝ)
    | complex => exact inferInstanceAs (CompleteSpace ℂ)
  have hD (R : RightIndex a ⊤) (t : ℝ) (ht : t ∈ Ioo c d) :
      HasDerivAt (FR R) (D R t) t := by
    rw [hDeq R ⟨t, ht⟩]
    exact hd R t ht
  have hG : ∀ ε : ℝ, 0 < ε → ∃ r : RightIndex a ⊤, ∀ R, r < R →
      ∀ t ∈ Icc c d, ‖D R t - G t‖ < ε := by
    intro ε hε
    obtain ⟨r, hr⟩ := hg ε hε
    exact ⟨r, fun R hR t ht => by
      simpa only [dist_eq_norm] using hr R hR t ht⟩
  obtain ⟨t₀, L, _, hL⟩ := hbase
  have hbase' : ∃ L : S.scalarValue k, ∀ ε : ℝ, 0 < ε →
      ∃ r : RightIndex a ⊤, ∀ R, r < R → ‖FR R t₀ - L‖ < ε := by
    refine ⟨L, fun ε hε => ?_⟩
    obtain ⟨r, hr⟩ := hL ε hε
    refine ⟨r, fun R hR => ?_⟩
    rw [heq R t₀]
    simpa only [dist_eq_norm] using hr R hR
  have mean : ∀ (v : ℝ → S.scalarValue k) (u w M : ℝ), u < w → 0 ≤ M →
      ContinuousOn v (Icc u w) →
      (∀ t ∈ Ioo u w, DifferentiableAt ℝ v t) →
      (∀ t ∈ Ioo u w, ‖deriv v t‖ ≤ M) → ‖v w - v u‖ ≤ M * (w-u) := by
    cases k with
    | real =>
      change ∀ (v : ℝ → ℝ) (u w M : ℝ), u < w → 0 ≤ M →
        ContinuousOn v (Icc u w) →
        (∀ t ∈ Ioo u w, DifferentiableAt ℝ v t) →
        (∀ t ∈ Ioo u w, ‖deriv v t‖ ≤ M) → ‖v w - v u‖ ≤ M * (w-u)
      simpa only [Real.norm_eq_abs] using real_mean_inequality
    | complex => exact complex_mean_inequality
  obtain ⟨F, hF, hcont, hder⟩ := uniform_limit_of_cofinal_derivatives
    mean FR D G c d t₀ hcd t₀.property hc hD hG hbase'
  have hu : RightUniformHasIntegral k (Icc c d) f a ⊤ (fun t => F t) := by
    refine ⟨hf, fun ε hε => ?_⟩
    obtain ⟨r, hr⟩ := hF ε hε
    refine ⟨r, fun R hR t => ?_⟩
    rw [← heq R t]
    simpa only [dist_eq_norm] using hr R hR t t.property
  exact ⟨F, hu, right_uniform_pointwise k (Icc c d) f a ⊤ (fun t => F t) hu,
    hcont, hder⟩

theorem regular_rectangle_proper_assumptions :
    Specs.SingleVariableAnalysis.Ch14.ImproperDerivative.rectangleProperAssumptions := by
  intro k a b c d hab hcd f ft hf hft hd
  have hswap (v : ℝ → Icc a b → S.scalarValue k)
      (hv : Specs.SingleVariableAnalysis.Ch14.ProperDerivative.JointContinuous (Icc c d) v) :
      Continuous (Function.uncurry (fun (x : Icc a b) (t : Icc c d) => v t x)) :=
    hv.comp_continuous
      ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)
      (fun p => ⟨p.2.property, mem_univ _⟩)
  have rectangle (v : ℝ → Icc a b → S.scalarValue k)
      (hv : Specs.SingleVariableAnalysis.Ch14.ProperDerivative.JointContinuous (Icc c d) v) :
      ∃ h : ∀ t : Icc c d,
        Specs.SingleVariableAnalysis.Ch14.ProperDefinition.sectionIntegrableValue k
          (fun x t => v t.val x) t,
      Continuous (fun t =>
        Specs.SingleVariableAnalysis.Ch14.ProperDefinition.familyValue k
          (fun x t => v t.val x) ⟨t, h t⟩) := by
    cases k with
    | real => exact ParameterIntegral.real_rectangle_continuity hab hcd _ (hswap v hv)
    | complex => exact ParameterIntegral.complex_rectangle_continuity hab hcd _ (hswap v hv)
  obtain ⟨hi, hci⟩ := rectangle f hf
  obtain ⟨hgi, _⟩ := rectangle ft hft
  refine ⟨hi, hgi, fun F G hF hG => ⟨?_, ?_⟩⟩
  · apply continuousOn_iff_continuous_domRestrict.mpr
    exact hci.congr (fun t => (hF t).symm)
  · rcases hcd.eq_or_lt with he | he
    · intro t ht
      exfalso
      linarith [ht.1, ht.2]
    · cases k with
      | real =>
        obtain ⟨hi', hgi', hresult⟩ :=
          ParameterIntegral.real_compact_neighborhood_derivative hab he f ft hf hft hd
        have hFi (t : Ioo c d) : F t =
            Specs.SingleVariableAnalysis.Ch14.ProperDefinition.familyValue .real
              (fun x t => f t.val x) ⟨t, hi' t⟩ :=
          hF ⟨t, Ioo_subset_Icc_self t.property⟩
        have hGi (t : Ioo c d) : G t =
            Specs.SingleVariableAnalysis.Ch14.ProperDefinition.familyValue .real
              (fun x t => ft t.val x) ⟨t, hgi' t⟩ :=
          hG ⟨t, Ioo_subset_Icc_self t.property⟩
        exact (hresult F G hFi hGi).2.2
      | complex =>
        obtain ⟨hi', hgi', hresult⟩ :=
          ParameterIntegral.complex_compact_neighborhood_derivative hab he f ft hf hft hd
        have hFi (t : Ioo c d) : F t =
            Specs.SingleVariableAnalysis.Ch14.ProperDefinition.familyValue .complex
              (fun x t => f t.val x) ⟨t, hi' t⟩ :=
          hF ⟨t, Ioo_subset_Icc_self t.property⟩
        have hGi (t : Ioo c d) : G t =
            Specs.SingleVariableAnalysis.Ch14.ProperDefinition.familyValue .complex
              (fun x t => ft t.val x) ⟨t, hgi' t⟩ :=
          hG ⟨t, Ioo_subset_Icc_self t.property⟩
        exact (hresult F G hFi hGi).2.2

end SingleVariableAnalysis.Riemann.Improper
