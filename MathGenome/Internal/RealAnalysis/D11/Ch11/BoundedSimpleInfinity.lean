import MathGenome.Internal.RealAnalysis.Specs.D11.Ch11.BoundedSimpleInfinity
import MathGenome.Internal.RealAnalysis.D11.Ch10.QuotientConstruction
import MathGenome.Internal.RealAnalysis.D11.Ch04.SimpleApproximation
import Mathlib.Tactic.Linarith

/-! Bounded simple approximation in ordinary L-infinity on arbitrary measures.
A bounded measurable representative is approximated uniformly by combining
finite-valued approximations of its real and imaginary components. The uniform
bound on the error gives the essential-norm estimate. Supports are unrestricted.
-/
open Set Filter MeasureTheory
open scoped ENNReal Topology
universe u
noncomputable section
namespace D11.Ch11.BoundedSimpleInfinity

variable {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]

private theorem uniform_simple_approximation (f : X → 𝕜) (hf : Measurable f)
    (hB : ∃ B : ℝ, ∀ x, ‖f x‖ ≤ B) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : SimpleFunc X 𝕜, ∀ x, ‖f x - s x‖ < ε := by
  obtain ⟨B, hB⟩ := hB
  obtain ⟨r, _, _, hr⟩ :=
    D11.Ch04.SimpleApproximation.bounded_real_uniform_approximation
      (fun x => RCLike.re (f x)) (RCLike.continuous_re.measurable.comp hf)
      ⟨B, fun x => (RCLike.abs_re_le_norm (f x)).trans (hB x)⟩
  obtain ⟨i, _, _, hi⟩ :=
    D11.Ch04.SimpleApproximation.bounded_real_uniform_approximation
      (fun x => RCLike.im (f x)) (RCLike.continuous_im.measurable.comp hf)
      ⟨B, fun x => (RCLike.abs_im_le_norm (f x)).trans (hB x)⟩
  rw [Metric.tendstoUniformly_iff] at hr hi
  obtain ⟨n, hnre, hnim⟩ := ((hr (ε / 2) (by positivity)).and
    (hi (ε / 2) (by positivity))).exists
  let s : SimpleFunc X 𝕜 := (r n).map RCLike.ofReal +
    (i n).map RCLike.ofReal * SimpleFunc.const X RCLike.I
  refine ⟨s, fun x => ?_⟩
  have heq : f x - s x = ((RCLike.re (f x) - r n x : ℝ) : 𝕜) +
      ((RCLike.im (f x) - i n x : ℝ) : 𝕜) * RCLike.I := by
    change f x - ((r n x : 𝕜) + (i n x : 𝕜) * RCLike.I) = _
    rw [RCLike.ofReal_sub, RCLike.ofReal_sub]
    have := RCLike.re_add_im (f x)
    linear_combination -this
  have hI : ‖(RCLike.I : 𝕜)‖ ≤ 1 := by
    rw [RCLike.norm_I]
    split_ifs <;> norm_num
  calc
    ‖f x - s x‖ ≤ |RCLike.re (f x) - r n x| + |RCLike.im (f x) - i n x| := by
      rw [heq]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, RCLike.norm_ofReal, RCLike.norm_ofReal]
      exact add_le_add_right (mul_le_of_le_one_right (abs_nonneg _) hI) _
    _ < ε := by
      have hre := hnre x
      have him := hnim x
      rw [Real.dist_eq] at hre him
      linarith

omit [MeasurableSpace 𝕜] [BorelSpace 𝕜] in
private theorem simple_bounded (s : SimpleFunc X 𝕜) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖s x‖ ≤ B := by
  classical
  refine ⟨∑ c ∈ s.range, ‖c‖, Finset.sum_nonneg (fun c _ => norm_nonneg c), ?_⟩
  intro x
  exact Finset.single_le_sum (fun c _ => norm_nonneg c) (s.mem_range_self x)

theorem raw_approximation : Specs.D11.Ch11.BoundedSimpleInfinity.raw_approximation := by
  intro X 𝕜 _ _ _ _ μ f hf ε hε
  obtain ⟨g, hg, hfg, hb, _, _⟩ :=
    D11.Ch10.LpDefinition.bounded_measurable_representative μ f hf
  obtain ⟨s, hs⟩ := uniform_simple_approximation g hg ⟨_, hb⟩ (ε / 2) (by positivity)
  obtain ⟨B, hB, hsb⟩ := simple_bounded s
  have hsm : MemLp (s : X → 𝕜) ∞ μ :=
    memLp_top_of_bound s.aestronglyMeasurable B (Eventually.of_forall hsb)
  have hsa : (s : X → 𝕜) ∈ D11.Ch10.LpDefinition.rawLInfinity μ :=
    (D11.Ch10.LpDefinition.rawLInfinity_iff_memLp μ s).mpr ⟨s.measurable, hsm⟩
  refine ⟨s, ⟨B, hB, hsb⟩, hsa, ?_⟩
  have ha : ∀ᵐ x ∂μ, ‖f x - s x‖ ≤ ε / 2 := by
    have heq := (D11.Ch04.AeCommonException.aeEq_iff_native μ f g).mp hfg
    filter_upwards [heq] with x hx
    rw [hx]
    exact (hs x).le
  change D11.Ch04.EssentialBounds.essentialSupNorm μ (fun x => f x - s x) < _
  rw [D11.Ch04.EssentialBounds.essentialSupNorm_eq_native]
  exact (eLpNormEssSup_le_of_ae_bound ha).trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith))

theorem quotient_approximation :
    Specs.D11.Ch11.BoundedSimpleInfinity.quotient_approximation := by
  intro X 𝕜 _ _ _ _ μ q ε hε
  induction q using Quotient.inductionOn with
  | _ f =>
    obtain ⟨s, hB, hsm, he⟩ := raw_approximation μ f.val
      ((D11.Ch10.QuotientConstruction.raw_top μ f.val).mp f.property) ε hε
    refine ⟨s, hB, (D11.Ch10.QuotientConstruction.raw_top μ s).mpr hsm, ?_⟩
    intro g hg
    have hgf := (D11.Ch10.QuotientConstruction.nullRelation_iff_native μ ∞ g f).mp
      (Quotient.exact hg)
    have hsub : D11.Ch04.AeCommonException.aeEq μ
        (fun x => g.val x - s x) (fun x => f.val x - s x) := by
      apply (D11.Ch04.AeCommonException.aeEq_iff_native μ _ _).mpr
      filter_upwards [hgf] with x hx
      rw [hx]
    change D11.Ch04.EssentialBounds.essentialSupNorm μ (fun x => g.val x - s x) < _
    rw [D11.Ch04.EssentialBounds.essentialSupNorm_congr μ _ _ hsub]
    exact he

set_option maxHeartbeats 800000 in
theorem native_approximation :
    Specs.D11.Ch11.BoundedSimpleInfinity.native_approximation := by
  intro X 𝕜 _ _ _ _ μ f ε hε
  have hf : (f : X → 𝕜) ∈ D11.Ch10.LpDefinition.rawLInfinity μ :=
    (D11.Ch10.LpDefinition.rawLInfinity_iff_memLp μ f).mpr
      ⟨(Lp.stronglyMeasurable f).measurable, Lp.memLp f⟩
  obtain ⟨s, hB, hsm, he⟩ := raw_approximation μ f hf ε hε
  have hs := ((D11.Ch10.LpDefinition.rawLInfinity_iff_memLp μ s).mp hsm).2
  refine ⟨s, hs, hB, ?_⟩
  have hd := (Lp.memLp f).sub hs
  have hnorm : ‖f - hs.toLp s‖ =
      (eLpNorm (fun x => f x - s x) ∞ μ).toReal := by
    calc
      ‖f - hs.toLp s‖ = ‖hd.toLp ((f : X → 𝕜) - (s : X → 𝕜))‖ := by
        rw [MemLp.toLp_sub (Lp.memLp f) hs, Lp.toLp_coeFn f (Lp.memLp f)]
      _ = _ := Lp.norm_toLp _ hd
  rw [hnorm]
  have hmeas : Measurable (fun x => f x - s x) :=
    (Lp.stronglyMeasurable f).measurable.sub s.measurable
  rw [D11.Ch10.LpDefinition.essentialSupNorm_eq_eLpNorm μ _ hmeas] at he
  change (eLpNorm ((f : X → 𝕜) - (s : X → 𝕜)) ∞ μ).toReal < ε
  have h := (ENNReal.toReal_lt_toReal hd.eLpNorm_ne_top ENNReal.ofReal_ne_top).mpr he
  rwa [ENNReal.toReal_ofReal hε.le] at h

end D11.Ch11.BoundedSimpleInfinity
