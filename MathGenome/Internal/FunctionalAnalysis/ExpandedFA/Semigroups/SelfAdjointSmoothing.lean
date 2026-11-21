import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.SelfAdjointSmoothing
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.NormalSemigroups
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.SpectralProductAndSumDomains
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal ContDiff
namespace ExpandedFA.Semigroups.SelfAdjointSmoothing
open Unbounded Unbounded.MeasurableSpectralCalculus
universe u v

/-- Raising the elementary maximum y exp(-y) ≤ exp(-1) gives every
integer-order sharp smoothing constant, without differentiating powers. -/
theorem scalar_estimate : Spec.ScalarEstimate := by
  intro m hm t ht r hr
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h := pow_le_pow_left₀
    (mul_nonneg (div_nonneg (mul_nonneg ht.le hr) hm0.le) (Real.exp_nonneg _))
    (Real.mul_exp_neg_le_exp_neg_one (t * r / m)) m
  have he : (Real.exp (-(t * r / (m : ℝ)))) ^ m = Real.exp (-t * r) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [mul_pow, he, ← Real.exp_nat_mul] at h
  have he' : Real.exp ((m : ℝ) * (-1)) = (Real.exp 1)⁻¹ ^ m := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]
  rw [he'] at h
  have hh := mul_le_mul_of_nonneg_right h (pow_nonneg (div_nonneg hm0.le ht.le) m)
  calc
    r ^ m * Real.exp (-t * r) =
        ((t * r / (m : ℝ)) ^ m * Real.exp (-t * r)) * ((m : ℝ) / t) ^ m := by
      rw [mul_assoc, mul_comm (Real.exp _), ← mul_assoc, ← mul_pow]
      congr 1
      field_simp
    _ ≤ _ := hh
    _ = _ := by rw [← mul_pow]; congr 1; field_simp

/-- The energy argument requires positivity alone; self-adjointness and any
regularity at zero stronger than continuity are unnecessary for uniqueness. -/
theorem classical_uniqueness : Spec.ClassicalUniqueness.{u} := by
  intro 𝕜 _ H _ _ _ L hpos x u v hu hv
  let := InnerProductSpace.rclikeToReal 𝕜 H
  let w : ℝ → H := fun s => u s - v s
  have hw0 : w 0 = 0 := by simp [w, hu.1, hv.1]
  have hwd (s : ℝ) (hs : 0 < s) : ∃ h : w s ∈ L.domain,
      HasDerivAt w (-(L ⟨w s, h⟩)) s := by
    obtain ⟨huD, hu'⟩ := hu.2.2 s hs
    obtain ⟨hvD, hv'⟩ := hv.2.2 s hs
    refine ⟨L.domain.sub_mem huD hvD, ?_⟩
    have hh := hu'.sub hv'
    convert hh using 1
    change -(L ((⟨u s, huD⟩ : L.domain) - ⟨v s, hvD⟩)) = _
    rw [L.map_sub]
    abel
  have hwc : ContinuousOn w (Ici 0) := by
    intro s hs
    change 0 ≤ s at hs
    rcases eq_or_lt_of_le hs with rfl | hs
    · exact hu.2.1.sub hv.2.1
    · exact (hwd s hs).choose_spec.continuousAt.continuousWithinAt
  have henergy : AntitoneOn (fun s => ‖w s‖ ^ 2) (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0) (hwc.norm.pow 2)
    · intro s hs
      rw [interior_Ici] at hs
      exact (hwd s hs).choose_spec.norm_sq.differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      obtain ⟨hD, hd⟩ := hwd s hs
      change deriv (fun s => ‖w s‖ ^ 2) s ≤ 0
      rw [hd.norm_sq.deriv]
      change 2 * RCLike.re (inner 𝕜 (w s) (-(L ⟨w s, hD⟩))) ≤ 0
      rw [inner_neg_right, map_neg]
      have hp := hpos ⟨w s, hD⟩
      linarith
  intro t ht
  have hh := henergy (show (0 : ℝ) ∈ Ici 0 by simp) ht ht
  change ‖w t‖ ^ 2 ≤ ‖w 0‖ ^ 2 at hh
  rw [hw0, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hh
  have hn : ‖w t‖ = 0 := by nlinarith [norm_nonneg (w t)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

section Spectral
variable {S : Type v} {H : Type u} [MeasurableSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : SpectralMeasure.ProjectionValuedMeasure S H} (C : BoundedRealization E)

omit [CompleteSpace H] in
lemma mem_neg_graph_iff (A : Operator ℂ H H) (x y : H) :
    (x, y) ∈ (-A).graph ↔ (x, -y) ∈ A.graph := by
  rw [(-A).mem_graph_iff, A.mem_graph_iff]
  constructor
  · rintro ⟨z, hz, hy⟩
    exact ⟨z, hz, by simpa using congrArg Neg.neg hy⟩
  · rintro ⟨z, hz, hy⟩
    exact ⟨z, hz, by simpa using congrArg Neg.neg hy⟩

theorem measurableIntegral_neg {f : S → ℂ} (hf : Measurable f) :
    measurableIntegral C (-f) = -measurableIntegral C f := by
  have hn (n : ℕ) : C.integral (truncation (-f) n) = -C.integral (truncation f n) := by
    have he : truncation (-f) n = -truncation f n := by
      classical
      funext s
      by_cases hs : ‖f s‖ ≤ (n : ℝ) <;> simp [truncation, hs]
    rw [he]
    simpa using C.smul (-1) (truncation f n) (boundedMeasurable_truncation hf n)
  apply LinearPMap.eq_of_eq_graph
  ext ⟨x, y⟩
  rw [mem_neg_graph_iff]
  change (x, y) ∈ (limitOperator (fun n => C.integral (truncation (-f) n))).graph ↔
    (x, -y) ∈ (limitOperator (fun n => C.integral (truncation f n))).graph
  rw [mem_limitOperator_graph_iff, mem_limitOperator_graph_iff]
  simp only [hn, neg_apply]
  exact ⟨fun h => by simpa using h.neg, fun h => by simpa using h.neg⟩

theorem heat_symbol_bounded (f : S → ℝ) (hf : Measurable f)
    (hpos : ∀ s, 0 ≤ f s) (t : ℝ≥0) :
    SpectralMeasure.Spec.IsBoundedMeasurable
      (fun s => Complex.exp (-(t : ℂ) * (f s : ℂ))) := by
  convert NormalSemigroups.exponentialSymbol_bounded
    (hf.complex_ofReal.neg) («ω» := 0) (fun s => neg_nonpos.mpr (hpos s)) t using 1
  ext s
  simp only [Pi.neg_apply]
  congr 1
  ring

omit [MeasurableSpace S] in
theorem heat_symbol_norm (f : S → ℝ) (hpos : ∀ s, 0 ≤ f s) (t : ℝ≥0) (s : S) :
    ‖Complex.exp (-(t : ℂ) * (f s : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  apply Real.exp_le_one_iff.mpr
  simpa using neg_nonpos.mpr (mul_nonneg t.coe_nonneg (hpos s))

/-- The spectral construction already supplies strong continuity at zero;
realness of the heat symbol supplies self-adjointness at every time. -/
theorem spectral_heat_semigroup (f : S → ℝ) (hf : Measurable f)
    (hpos : ∀ s, 0 ≤ f s) :
    ∃ T : C0Semigroup ℂ H,
      C0SemigroupSpec.generatorValue T = -measurableIntegral C (fun s => (f s : ℂ)) ∧
      (∀ t : ℝ≥0, T.operators t = C.integral
        (fun s => Complex.exp (-(t : ℂ) * (f s : ℂ)))) ∧
      ∀ t, IsSelfAdjoint (T.operators t) ∧ ‖T.operators t‖ ≤ 1 := by
  let g : S → ℂ := fun s => -(f s : ℂ)
  have hg : Measurable g := hf.complex_ofReal.neg
  have hgb : ∀ s, (g s).re ≤ 0 := fun s => neg_nonpos.mpr (hpos s)
  obtain ⟨T, _, hT⟩ := NormalSemigroups.spectral_semigroup S H E C g hg ⟨0, hgb⟩
  have hgen := NormalSemigroups.generator_eq_spectralIntegral C hg hgb T hT
  have hT' (t : ℝ≥0) : T.operators t = C.integral
      (fun s => Complex.exp (-(t : ℂ) * (f s : ℂ))) := by
    rw [hT]
    congr 1
    funext s
    dsimp [g]
    congr 1
    ring
  refine ⟨T, ?_, hT', ?_⟩
  · exact hgen.trans (measurableIntegral_neg C hf.complex_ofReal)
  · intro t
    have hb := heat_symbol_bounded f hf hpos t
    rw [hT']
    constructor
    · change star (C.integral _) = C.integral _
      rw [← C.map_star _ hb]
      congr 1
      funext s
      simp only [Pi.star_apply, Complex.star_def, ← Complex.exp_conj,
        map_mul, map_neg, Complex.conj_ofReal]
    · exact C.bound _ 1 hb zero_le_one (heat_symbol_norm f hpos t)

theorem spectral_heat_decay (f : S → ℝ) (hf : Measurable f) (c : ℝ)
    (hc : 0 ≤ c) (hbound : ∀ s, c ≤ f s) (t : ℝ≥0) :
    ‖C.integral (fun s => Complex.exp (-(t : ℂ) * (f s : ℂ)))‖ ≤
      Real.exp (-c * (t : ℝ)) := by
  apply C.bound _ _ (heat_symbol_bounded f hf (fun s => hc.trans (hbound s)) t)
    (Real.exp_nonneg _)
  intro s
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
    Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
  nlinarith [mul_le_mul_of_nonneg_left (hbound s) t.coe_nonneg]

/-- Bounded symbols for every differentiated heat multiplier. -/
theorem heat_power_symbol_bounded (f : S → ℝ) (hf : Measurable f)
    (hpos : ∀ s, 0 ≤ f s) (m : ℕ) (t : ℝ≥0) (ht : 0 < t) :
    SpectralMeasure.Spec.IsBoundedMeasurable
      (fun s => (f s : ℂ)^m * Complex.exp (-(t : ℂ) * (f s : ℂ))) := by
  refine ⟨(hf.complex_ofReal.pow_const m).mul
    ((measurable_const.mul hf.complex_ofReal).cexp), ?_⟩
  by_cases hm : m = 0
  · subst m
    exact ⟨1, by simpa using heat_symbol_norm f hpos t⟩
  · refine ⟨((m : ℝ) / (Real.exp 1 * (t : ℝ)))^m, fun s => ?_⟩
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hpos s), Complex.norm_exp]
    simpa using scalar_estimate m (Nat.one_le_iff_ne_zero.mpr hm) t ht (f s) (hpos s)

/-- This proves membership in the iterated *operator* powers directly from
the product graph; no replacement of a power domain by a closure is used. -/
theorem spectral_heat_power_graph (f : S → ℝ) (hf : Measurable f)
    (hpos : ∀ s, 0 ≤ f s) (t : ℝ≥0) (ht : 0 < t) (m : ℕ) (x : H) :
    (C.integral (fun s => Complex.exp (-(t : ℂ) * (f s : ℂ))) x,
     C.integral (fun s => (f s : ℂ)^m * Complex.exp (-(t : ℂ) * (f s : ℂ))) x) ∈
      (OperatorDomainsSpec.powerValue (measurableIntegral C (fun s => (f s : ℂ))) m).graph := by
  induction m with
  | zero =>
    simp only [pow_zero, one_mul]
    exact (OperatorDomainsSpec.powerValue _ 0).mem_graph_iff.mpr
      ⟨⟨_, Submodule.mem_top⟩, rfl, rfl⟩
  | succ m ih =>
    apply (mem_product_graph_iff _ _ _ _).mpr
    refine ⟨_, ih, ?_⟩
    have hg := heat_power_symbol_bounded f hf hpos m t ht
    have hfg := heat_power_symbol_bounded f hf hpos (m+1) t ht
    have he : (fun s => (f s : ℂ)) *
        (fun s => (f s : ℂ)^m * Complex.exp (-(t : ℂ) * (f s : ℂ))) =
        (fun s => (f s : ℂ)^(m+1) * Complex.exp (-(t : ℂ) * (f s : ℂ))) := by
      funext s
      simp only [Pi.mul_apply, pow_succ]
      ring
    have hg' := Unbounded.UnboundedNormalSpectralTheorem.SpectralRepresentation.bounded_product_graph
      C hf.complex_ofReal hg (by rwa [he]) x
    rwa [he] at hg'

/-- Multiplying a positive-time differentiated symbol by an additional heat
symbol translates its time. -/
theorem heat_power_add (f : S → ℝ) (hf : Measurable f) (hpos : ∀ s, 0 ≤ f s)
    (t a : ℝ≥0) (ha : 0 < a) (m : ℕ) :
    C.integral (fun s => Complex.exp (-(t : ℂ) * (f s : ℂ))) *
      C.integral (fun s => (f s : ℂ)^m * Complex.exp (-(a : ℂ) * (f s : ℂ))) =
    C.integral (fun s => (f s : ℂ)^m * Complex.exp (-((t+a : ℝ≥0) : ℂ) * (f s : ℂ))) := by
  rw [← C.mul _ _ (heat_symbol_bounded f hf hpos t)
    (heat_power_symbol_bounded f hf hpos m a ha)]
  congr 1
  funext s
  have he : -((t+a : ℝ≥0) : ℂ) * (f s : ℂ) =
      -(t : ℂ) * (f s : ℂ) + -(a : ℂ) * (f s : ℂ) := by
    simp only [NNReal.coe_add, Complex.ofReal_add]
    ring
  rw [he, Complex.exp_add]
  dsimp only [Pi.mul_apply]
  ring

/-- Positive time can be split in half. The first half produces a vector in
the generator domain; differentiating its subsequent orbit differentiates
an arbitrary heat multiplier, without a scalar domination hypothesis. -/
theorem heat_power_hasDerivAt (f : S → ℝ) (hf : Measurable f)
    (hpos : ∀ s, 0 ≤ f s) (T : C0Semigroup ℂ H)
    (hgen : C0SemigroupSpec.generatorValue T = -measurableIntegral C (fun s => (f s : ℂ)))
    (hT : ∀ t : ℝ≥0, T.operators t = C.integral
      (fun s => Complex.exp (-(t : ℂ) * (f s : ℂ)))) (m : ℕ) (x : H)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun r : ℝ => C.integral
      (fun s => (f s : ℂ)^m * Complex.exp (-(r.toNNReal : ℂ) * (f s : ℂ))) x)
      (-(C.integral (fun s => (f s : ℂ)^(m+1) *
        Complex.exp (-(t.toNNReal : ℂ) * (f s : ℂ))) x)) t := by
  let a : ℝ≥0 := ⟨t/2, half_pos ht |>.le⟩
  have ha : 0 < a := half_pos ht
  let b (n : ℕ) (r : ℝ≥0) : H := C.integral
    (fun s => (f s : ℂ)^n * Complex.exp (-(r : ℂ) * (f s : ℂ))) x
  have hadd (n : ℕ) (r : ℝ≥0) : T.operators r (b n a) = b n (r+a) := by
    rw [hT]
    exact congrArg (fun B : H →L[ℂ] H => B x) (heat_power_add C f hf hpos r a ha n)
  have hgraph : (b m a, b (m+1) a) ∈
      (measurableIntegral C (fun s => (f s : ℂ))).graph := by
    have he : (fun s => (f s : ℂ)) *
        (fun s => (f s : ℂ)^m * Complex.exp (-(a : ℂ) * (f s : ℂ))) =
        (fun s => (f s : ℂ)^(m+1) * Complex.exp (-(a : ℂ) * (f s : ℂ))) := by
      funext s
      dsimp only [Pi.mul_apply]
      rw [pow_succ]
      ring
    have hh := Unbounded.UnboundedNormalSpectralTheorem.SpectralRepresentation.bounded_product_graph
      C hf.complex_ofReal (heat_power_symbol_bounded f hf hpos m a ha)
      (by rw [he]; exact heat_power_symbol_bounded f hf hpos (m+1) a ha) x
    simpa only [he] using hh
  have hg : (b m a, -(b (m+1) a)) ∈ (C0SemigroupSpec.generatorValue T).graph := by
    rw [hgen, mem_neg_graph_iff]
    simpa using hgraph
  obtain ⟨y, hy, hyval⟩ := (C0SemigroupSpec.generatorValue T).mem_graph_iff.mp hg
  have hta : 0 < t - (a : ℝ) := by change 0 < t - t/2; linarith
  have hd := (T.hasDerivWithinAt_orbit y (t-a) hta.le).hasDerivAt (Ici_mem_nhds hta)
  have hd' := hd.comp_sub_const t a
  have hsum {r : ℝ} (hr : (a : ℝ) < r) : (r-a).toNNReal + a = r.toNNReal := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_add, Real.coe_toNNReal _ (sub_pos.mpr hr).le,
      Real.coe_toNNReal _ (a.coe_nonneg.trans hr.le)]
    ring
  have hv : T.operators (t-(a : ℝ)).toNNReal (C0SemigroupSpec.generatorValue T y) =
      -(b (m+1) t.toNNReal) := by
    rw [hyval, map_neg, hadd, hsum (by change t/2 < t; linarith)]
  change HasDerivAt _ (T.operators (t-(a : ℝ)).toNNReal
    (C0SemigroupSpec.generatorValue T y)) t at hd'
  rw [hv] at hd'
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (show (a : ℝ) < t by change t/2 < t; linarith)] with r hr
  rw [hy, hadd, hsum hr]

/-- All differentiated trajectories form a derivative tower on (0,∞). -/
theorem spectral_heat_smooth (f : S → ℝ) (hf : Measurable f) (hpos : ∀ s, 0 ≤ f s)
    (T : C0Semigroup ℂ H)
    (hgen : C0SemigroupSpec.generatorValue T = -measurableIntegral C (fun s => (f s : ℂ)))
    (hT : ∀ t : ℝ≥0, T.operators t = C.integral
      (fun s => Complex.exp (-(t : ℂ) * (f s : ℂ)))) (x : H) :
    ContDiffOn ℝ ∞ (fun t : ℝ => T.operators t.toNNReal x) (Ioi 0) := by
  let b (m : ℕ) (t : ℝ) : H := C.integral
    (fun s => (f s : ℂ)^m * Complex.exp (-(t.toNNReal : ℂ) * (f s : ℂ))) x
  have hd (m : ℕ) (t : ℝ) (ht : t ∈ Ioi 0) : HasDerivAt (b m) (-(b (m+1) t)) t :=
    heat_power_hasDerivAt C f hf hpos T hgen hT m x t ht
  have hs : ∀ (n m : ℕ), ContDiffOn ℝ n (b m) (Ioi 0) := by
    intro n
    induction n with
    | zero =>
      intro m
      exact contDiffOn_zero.mpr (fun t ht => (hd m t ht).continuousAt.continuousWithinAt)
    | succ n ih =>
      intro m
      rw [show (↑(n+1) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp,
        contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
      refine ⟨fun t ht => (hd m t ht).differentiableAt.differentiableWithinAt,
        by simp, ?_⟩
      apply (ih (m+1)).neg.congr
      intro t ht
      exact (hd m t ht).deriv
  have hh : ContDiffOn ℝ ∞ (b 0) (Ioi 0) := contDiffOn_infty.mpr (fun n => hs n 0)
  apply hh.congr
  intro t _
  simp only [b, pow_zero, one_mul, hT]


theorem spectral_heat_classical (f : S → ℝ) (hf : Measurable f) (hpos : ∀ s, 0 ≤ f s)
    (T : C0Semigroup ℂ H)
    (hgen : C0SemigroupSpec.generatorValue T = -measurableIntegral C (fun s => (f s : ℂ)))
    (hT : ∀ t : ℝ≥0, T.operators t = C.integral
      (fun s => Complex.exp (-(t : ℂ) * (f s : ℂ)))) (x : H) :
    ClassicalSolution (measurableIntegral C (fun s => (f s : ℂ))) x
      (fun t : ℝ => T.operators t.toNNReal x) := by
  refine ⟨by simp, (T.continuous_real_orbit x).continuousAt.continuousWithinAt, ?_⟩
  intro t ht
  have ht' : 0 < t.toNNReal := Real.toNNReal_pos.mpr ht
  let A := measurableIntegral C (fun s => (f s : ℂ))
  let y : H := C.integral (fun s => (f s : ℂ) *
    Complex.exp (-(t.toNNReal : ℂ) * (f s : ℂ))) x
  have hgraph : (T.operators t.toNNReal x, y) ∈ A.graph := by
    rw [hT]
    apply Unbounded.UnboundedNormalSpectralTheorem.SpectralRepresentation.bounded_product_graph
      C hf.complex_ofReal (heat_symbol_bounded f hf hpos t.toNNReal)
    simpa only [pow_one, Pi.mul_def] using heat_power_symbol_bounded f hf hpos 1 t.toNNReal ht'
  obtain ⟨z, hz, hval⟩ := A.mem_graph_iff.mp hgraph
  change (z : H) = T.operators t.toNNReal x at hz
  have hD : T.operators t.toNNReal x ∈ A.domain := by
    rw [← hz]
    exact z.prop
  refine ⟨hD, ?_⟩
  have he : A ⟨T.operators t.toNNReal x, hD⟩ = y :=
    A.mem_graph_snd_inj (A.mem_graph _) hgraph rfl
  rw [he]
  have hd := heat_power_hasDerivAt C f hf hpos T hgen hT 0 x t ht
  simpa only [pow_zero, one_mul, zero_add, pow_one, ← hT] using hd

end Spectral

section ComplexCore
open Unbounded.UnboundedNormalSpectralTheorem
open Unbounded.UnboundedNormalSpectralTheorem.SpectralRepresentation
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A lower numerical bound controls the real parts of the actual unbounded
spectrum. Spectral disks provide the test vectors, on their full domains. -/
theorem spectral_lower_of_numerical (L : Operator ℂ H H)
    (hd : Dense (L.domain : Set H)) (hc : L.IsClosed)
    (hn : OperatorDomainsSpec.productValue (HilbertAdjointSpec.adjointValue L) L =
      OperatorDomainsSpec.productValue L (HilbertAdjointSpec.adjointValue L))
    (c : ℝ)
    (hnum : ∀ x : L.domain, c * ‖(x : H)‖ ^ 2 ≤ (inner ℂ (x : H) (L x)).re) :
    ∀ z ∈ operatorSpectrum L, c ≤ z.re := by
  obtain ⟨E, C, hC, _⟩ := spectral_existence H L hd hc hn
  have hsupp := (spectral_uniqueness_and_support H L hd hc hn E
    (resolves_of_integral_eq L E C hC)).1
  intro z hz
  by_contra hh
  have hgap : 0 < c - z.re := sub_pos.mpr (lt_of_not_ge hh)
  let r := (c - z.re) / 2
  have hr : 0 < r := half_pos hgap
  have hP : E (Metric.ball z r) ≠ 0 :=
    (UnboundedNormalSpectralTheorem.mem_spectrum_iff L E hsupp z).mp hz _
      Metric.isOpen_ball (Metric.mem_ball_self hr)
  obtain ⟨y, hy⟩ : ∃ y : H, E (Metric.ball z r) y ≠ 0 := by
    by_contra hnot
    apply hP
    ext y
    simp only [not_exists, not_not] at hnot
    simpa using hnot y
  let x := E (Metric.ball z r) y
  have hx : x ≠ 0 := hy
  have hfix : E (Metric.closedBall z r) x = x := by
    change (E (Metric.closedBall z r) * E (Metric.ball z r)) y = _
    rw [E.inter _ _ measurableSet_closedBall measurableSet_ball,
      inter_eq_right.mpr Metric.ball_subset_closedBall]
  obtain ⟨a, ha0, haD, hag, hab⟩ := disk_sequence C z r hr.le x hfix
  have hdom : x ∈ L.domain := by simpa [hC, ha0] using haD 0
  have hgraph : (x, z • x + a 1) ∈ L.graph := by simpa [hC, ha0] using hag 0
  have heval : L ⟨x, hdom⟩ = z • x + a 1 :=
    L.mem_graph_snd_inj (L.mem_graph ⟨x, hdom⟩) hgraph rfl
  have hn1 : ‖a 1‖ ≤ r * ‖x‖ := by simpa only [pow_one] using hab 1
  have hn0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have herror : (inner ℂ x (a 1)).re ≤ r * ‖x‖ ^ 2 := by
    have hh1 := (abs_le.mp (Complex.abs_re_le_norm (inner ℂ x (a 1)))).2
    have hh2 := norm_inner_le_norm x (a 1) (𝕜 := ℂ)
    have hh3 := mul_le_mul_of_nonneg_left hn1 (norm_nonneg x)
    nlinarith
  have hip : (inner ℂ x (L ⟨x, hdom⟩)).re =
      z.re * ‖x‖ ^ 2 + (inner ℂ x (a 1)).re := by
    rw [heval, inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp [Complex.mul_re, ← Complex.ofReal_pow]
  have hhnum := hnum ⟨x, hdom⟩
  change c * ‖x‖ ^ 2 ≤ (inner ℂ x (L ⟨x, hdom⟩)).re at hhnum
  rw [hip] at hhnum
  have hr2 : 2 * r = c - z.re := by dsimp [r]; ring
  nlinarith [sq_pos_of_pos hn0]

/-- The same spectral construction has the exact power graphs and the
operator-norm bound, rather than just a square-integrability statement. -/
theorem spectral_power_smoothing {S : Type v} [MeasurableSpace S]
    {E : SpectralMeasure.ProjectionValuedMeasure S H} (C : BoundedRealization E)
    (f : S → ℝ) (hf : Measurable f) (hpos : ∀ s, 0 ≤ f s)
    (L : Operator ℂ H H) (hL : measurableIntegral C (fun s => (f s : ℂ)) = L)
    (T : C0Semigroup ℂ H)
    (hT : ∀ t : ℝ≥0, T.operators t = C.integral
      (fun s => Complex.exp (-(t : ℂ) * (f s : ℂ)))) : PowerSmoothing L T := by
  intro t ht m hm
  let a : S → ℂ := fun s => (f s : ℂ)^m * Complex.exp (-(t : ℂ) * (f s : ℂ))
  have ha := heat_power_symbol_bounded f hf hpos m t ht
  refine ⟨C.integral a, ?_, ?_⟩
  · intro x
    rw [hT, ← hL]
    exact spectral_heat_power_graph C f hf hpos t ht m x
  · apply C.bound a _ ha (pow_nonneg (div_nonneg (Nat.cast_nonneg m)
      (mul_nonneg (Real.exp_nonneg _) t.coe_nonneg)) m)
    intro s
    dsimp [a]
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hpos s), Complex.norm_exp]
    simpa using scalar_estimate m hm t ht (f s) (hpos s)

/-- All assertions of self-adjoint smoothing on an arbitrary complex Hilbert
space, with no separability or nonzero-space assumption. -/
theorem complex_selfadjoint_smoothing : Spec.ComplexTheorem.{u} := by
  intro H _ _ _ L hL
  obtain ⟨hd, hself, hpos⟩ := hL
  have hc : L.IsClosed := by
    have hh := hilbertAdjoint_isClosed L hd
    change (HilbertAdjointSpec.adjointValue L).IsClosed at hh
    rwa [hself] at hh
  have hn : OperatorDomainsSpec.productValue (HilbertAdjointSpec.adjointValue L) L =
      OperatorDomainsSpec.productValue L (HilbertAdjointSpec.adjointValue L) := by rw [hself]
  obtain ⟨E, hE⟩ := spectral_existence H L hd hc hn
  have hsupp := (spectral_uniqueness_and_support H L hd hc hn E hE).1
  obtain ⟨C, hC, _⟩ := hE
  have hsa : (measurableIntegral C id).adjoint = measurableIntegral C id := by
    change (measurableIntegral C (fun z : ℂ => z)).adjoint =
      measurableIntegral C (fun z : ℂ => z)
    rw [hC]
    exact hself
  have hspec (x : H) : ∀ᵐ z ∂C.measure x, z ∈ operatorSpectrum L := by
    apply ae_iff.mpr
    change C.measure x (operatorSpectrum L)ᶜ = 0
    rw [C.measure_apply x _ hsupp.1.measurableSet.compl, hsupp.2.1]
    simp
  have hlower : ∀ z ∈ operatorSpectrum L, 0 ≤ z.re :=
    spectral_lower_of_numerical L hd hc hn 0 (by simpa using hpos)
  let f : ℂ → ℝ := fun z => max z.re 0
  have hf : Measurable f := Complex.continuous_re.measurable.max measurable_const
  have hfpos : ∀ z, 0 ≤ f z := fun z => le_max_right _ _
  have hfeq (x : H) : (fun z => (f z : ℂ)) =ᵐ[C.measure x] id := by
    filter_upwards [hspec x, C.symbol_real_ae_of_selfAdjoint id measurable_id hsa x] with z hz hr
    apply Complex.ext
    · exact max_eq_left (hlower z hz)
    · simpa using hr.symm
  have hfL : measurableIntegral C (fun z => (f z : ℂ)) = L :=
    (C.measurableIntegral_congr_ae _ id hf.complex_ofReal measurable_id hfeq).trans hC
  obtain ⟨T, hgen, hT, hcont⟩ := spectral_heat_semigroup C f hf hfpos
  have hrep : Spec.ComplexHeatRepresentation L T := by
    refine ⟨E, C, hC, ?_⟩
    intro t
    calc
      measurableIntegral C (fun z => Complex.exp (-(t : ℂ) * z)) =
          measurableIntegral C (fun z => Complex.exp (-(t : ℂ) * (f z : ℂ))) := by
        apply C.measurableIntegral_congr_ae
        · exact (measurable_const.mul measurable_id).cexp
        · exact (measurable_const.mul hf.complex_ofReal).cexp
        · intro x
          filter_upwards [hfeq x] with z hz
          simp only [id_eq] at hz
          rw [hz]
      _ = (C.integral (fun z => Complex.exp (-(t : ℂ) * (f z : ℂ)))).toLinearMap.toPMap ⊤ :=
        NormalSemigroups.measurableIntegral_of_bounded C (heat_symbol_bounded f hf hfpos t)
      _ = (T.operators t).toLinearMap.toPMap ⊤ := by rw [hT]
  have hclassical (x : H) : ClassicalSolution L x (fun t : ℝ => T.operators t.toNNReal x) := by
    rw [← hfL]
    exact spectral_heat_classical C f hf hfpos T hgen hT x
  refine ⟨T, ?_, hrep⟩
  refine ⟨?_, hcont, spectral_power_smoothing C f hf hfpos L hfL T hT,
    spectral_heat_smooth C f hf hfpos T hgen hT, hclassical, ?_, ?_⟩
  · rwa [hfL] at hgen
  · intro x u hu t ht
    exact classical_uniqueness ℂ H L hpos x u _ hu (hclassical x) t ht
  · intro c hc0 hnum t
    let g : ℂ → ℝ := fun z => max z.re c
    have hg : Measurable g := Complex.continuous_re.measurable.max measurable_const
    have hglower : ∀ z, c ≤ g z := fun z => le_max_right _ _
    have hspec_lower := spectral_lower_of_numerical L hd hc hn c hnum
    have heq (x : H) : (fun z => Complex.exp (-(t : ℂ) * (f z : ℂ))) =ᵐ[C.measure x]
        (fun z => Complex.exp (-(t : ℂ) * (g z : ℂ))) := by
      filter_upwards [hspec x] with z hz
      have hz0 := hlower z hz
      have hzc := hspec_lower z hz
      simp [f, g, max_eq_left hz0, max_eq_left hzc]
    have hfg : C.integral (fun z => Complex.exp (-(t : ℂ) * (f z : ℂ))) =
        C.integral (fun z => Complex.exp (-(t : ℂ) * (g z : ℂ))) := by
      ext x
      exact C.integral_apply_congr_ae _ _ (heat_symbol_bounded f hf hfpos t)
        (heat_symbol_bounded g hg (fun z => hc0.le.trans (hglower z)) t) x (heq x)
    rw [hT, hfg]
    exact spectral_heat_decay C g hg c hc0.le hglower t

end ComplexCore

/-- The Hilbert complexification, retaining the L² product norm. -/
def Complexification (H : Type u) := WithLp 2 (H × H)
open Unbounded
namespace Complexification
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
instance : NormedAddCommGroup (Complexification H) :=
  inferInstanceAs (NormedAddCommGroup (WithLp 2 (H × H)))
instance [CompleteSpace H] : CompleteSpace (Complexification H) :=
  inferInstanceAs (CompleteSpace (WithLp 2 (H × H)))

def re (x : Complexification H) : H := (WithLp.ofLp x).1
def im (x : Complexification H) : H := (WithLp.ofLp x).2
def mk (x y : H) : Complexification H := WithLp.toLp 2 (x,y)
@[ext] lemma ext {x y : Complexification H} (hr : re x = re y) (hi : im x = im y) : x = y :=
  congrArg (WithLp.toLp 2) (Prod.ext hr hi)
@[simp] lemma re_mk (x y : H) : re (mk x y) = x := rfl
@[simp] lemma im_mk (x y : H) : im (mk x y) = y := rfl
@[simp] lemma re_add (x y : Complexification H) : re (x+y) = re x + re y := rfl
@[simp] lemma im_add (x y : Complexification H) : im (x+y) = im x + im y := rfl
@[simp] lemma re_zero : re (0 : Complexification H) = 0 := rfl
@[simp] lemma im_zero : im (0 : Complexification H) = 0 := rfl
@[simp] lemma re_neg (x : Complexification H) : re (-x) = -re x := rfl
@[simp] lemma im_neg (x : Complexification H) : im (-x) = -im x := rfl

instance : SMul ℂ (Complexification H) where
  smul z x := mk (z.re • re x - z.im • im x) (z.im • re x + z.re • im x)
@[simp] lemma re_smul (z : ℂ) (x : Complexification H) :
    re (z • x) = z.re • re x - z.im • im x := rfl
@[simp] lemma im_smul (z : ℂ) (x : Complexification H) :
    im (z • x) = z.im • re x + z.re • im x := rfl
instance : Module ℂ (Complexification H) where
  one_smul x := by apply ext <;> simp
  mul_smul z w x := by
    apply ext <;>
      simp [Complex.mul_re, Complex.mul_im, mul_smul, add_smul, sub_smul, smul_add,
        smul_sub] <;> abel
  smul_zero z := by apply ext <;> simp
  smul_add z x y := by apply ext <;> simp [smul_add] <;> abel
  add_smul z w x := by apply ext <;> simp [add_smul] <;> abel
  zero_smul x := by apply ext <;> simp


lemma norm_sq (x : Complexification H) : ‖x‖ ^ 2 = ‖re x‖ ^ 2 + ‖im x‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 x
lemma norm_smul_sq (z : ℂ) (x : Complexification H) : ‖z • x‖ ^ 2 = ‖z‖ ^ 2 * ‖x‖ ^ 2 := by
  simp only [norm_sq, re_smul, im_smul, norm_sub_sq_real, norm_add_sq_real,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_left,
    real_inner_smul_right, Complex.sq_norm, Complex.normSq_apply]
  rw [real_inner_comm (im x) (re x)]
  ring
instance : NormedSpace ℂ (Complexification H) where
  norm_smul_le z x := by
    have h := norm_smul_sq z x
    nlinarith [norm_nonneg (z • x), norm_nonneg z, norm_nonneg x,
      mul_nonneg (norm_nonneg z) (norm_nonneg x)]

instance : InnerProductSpace ℂ (Complexification H) where
  inner x y := ⟨inner ℝ (re x) (re y) + inner ℝ (im x) (im y),
    inner ℝ (re x) (im y) - inner ℝ (im x) (re y)⟩
  norm_sq_eq_re_inner x := by simp [norm_sq, real_inner_self_eq_norm_sq]
  conj_inner_symm x y := by apply Complex.ext <;> simp [real_inner_comm] <;> ring
  add_left x y z := by apply Complex.ext <;> simp [inner_add_left] <;> ring
  smul_left x y z := by
    apply Complex.ext <;>
      simp [inner_sub_left, inner_add_left, real_inner_smul_left, Complex.mul_re,
        Complex.mul_im] <;> ring

/-- Use the canonical restricted real structure, so real derivatives agree
with those in `ClassicalSolution`. -/
instance : NormedSpace ℝ (Complexification H) :=
  NormedSpace.restrictScalars ℝ ℂ (Complexification H)
instance : InnerProductSpace ℝ (Complexification H) :=
  InnerProductSpace.rclikeToReal ℂ (Complexification H)
instance : IsScalarTower ℝ ℂ (Complexification H) where
  smul_assoc r z x := by
    change ((algebraMap ℝ ℂ r) * z) • x = (algebraMap ℝ ℂ r) • (z • x)
    exact mul_smul _ _ _

@[simp] lemma re_rsmul (r : ℝ) (x : Complexification H) : re (r • x) = r • re x := by
  change re ((r : ℂ) • x) = _
  simp only [re_smul, Complex.ofReal_re, Complex.ofReal_im, zero_smul, sub_zero]
@[simp] lemma im_rsmul (r : ℝ) (x : Complexification H) : im (r • x) = r • im x := by
  change im ((r : ℂ) • x) = _
  simp only [im_smul, Complex.ofReal_re, Complex.ofReal_im, zero_smul, zero_add]

lemma norm_re_le (x : Complexification H) : ‖re x‖ ≤ ‖x‖ := by
  have h := norm_sq x
  nlinarith [norm_nonneg (re x), norm_nonneg x, sq_nonneg ‖im x‖]
lemma norm_im_le (x : Complexification H) : ‖im x‖ ≤ ‖x‖ := by
  have h := norm_sq x
  nlinarith [norm_nonneg (im x), norm_nonneg x, sq_nonneg ‖re x‖]

lemma inner_re (x y : Complexification H) :
    (inner ℂ x y).re = inner ℝ (re x) (re y) + inner ℝ (im x) (im y) := rfl
lemma inner_im (x y : Complexification H) :
    (inner ℂ x y).im = inner ℝ (re x) (im y) - inner ℝ (im x) (re y) := rfl

/-- The original real Hilbert space embeds isometrically. -/
def inclusion : H →ₗᵢ[ℝ] Complexification H where
  toFun x := mk x 0
  map_add' x y := by apply ext <;> simp
  map_smul' r x := by apply ext <;> simp
  norm_map' x := by
    have h := norm_sq (mk x (0 : H))
    simp only [re_mk, im_mk, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, add_zero] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

def realPart : Complexification H →L[ℝ] H :=
  LinearMap.mkContinuous
    { toFun := re
      map_add' := re_add
      map_smul' := fun r x => re_rsmul r x } 1 (fun x => by simpa using norm_re_le x)
def imaginaryPart : Complexification H →L[ℝ] H :=
  LinearMap.mkContinuous
    { toFun := im
      map_add' := im_add
      map_smul' := fun r x => im_rsmul r x } 1 (fun x => by simpa using norm_im_le x)
@[simp] lemma inclusion_apply (x : H) : inclusion x = mk x 0 := rfl
@[simp] lemma realPart_apply (x : Complexification H) : realPart x = re x := rfl
@[simp] lemma imaginaryPart_apply (x : Complexification H) : imaginaryPart x = im x := rfl

/-- Complexification on exactly the product of the two real domains. -/
def domain (A : Operator ℝ H H) : Submodule ℂ (Complexification H) where
  carrier := {x | re x ∈ A.domain ∧ im x ∈ A.domain}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨hr,hi⟩ ⟨kr,ki⟩
    exact ⟨A.domain.add_mem hr kr, A.domain.add_mem hi ki⟩
  smul_mem' := by
    rintro z x ⟨hr,hi⟩
    exact ⟨A.domain.sub_mem (A.domain.smul_mem z.re hr) (A.domain.smul_mem z.im hi),
      A.domain.add_mem (A.domain.smul_mem z.im hr) (A.domain.smul_mem z.re hi)⟩

def lift (A : Operator ℝ H H) : Operator ℂ (Complexification H) (Complexification H) where
  domain := domain A
  toFun :=
    { toFun := fun x => mk (A ⟨re x, x.2.1⟩) (A ⟨im x, x.2.2⟩)
      map_add' := by
        intro x y
        apply ext <;> simp only [re_mk, im_mk, re_add, im_add]
        · exact A.map_add ⟨re x,x.2.1⟩ ⟨re y,y.2.1⟩
        · exact A.map_add ⟨im x,x.2.2⟩ ⟨im y,y.2.2⟩
      map_smul' := by
        intro z x
        apply ext <;> simp only [re_mk, im_mk, re_smul, im_smul]
        · exact (A.map_sub (z.re • ⟨re x,x.2.1⟩) (z.im • ⟨im x,x.2.2⟩)).trans
            (congrArg₂ (· - ·) (A.map_smul _ _) (A.map_smul _ _))
        · exact (A.map_add (z.im • ⟨re x,x.2.1⟩) (z.re • ⟨im x,x.2.2⟩)).trans
            (congrArg₂ (· + ·) (A.map_smul _ _) (A.map_smul _ _)) }

@[simp] lemma mem_lift_domain (A : Operator ℝ H H) (x : Complexification H) :
    x ∈ (lift A).domain ↔ re x ∈ A.domain ∧ im x ∈ A.domain := Iff.rfl
@[simp] lemma re_lift (A : Operator ℝ H H) (x : (lift A).domain) :
    re (lift A x) = A ⟨re x, x.2.1⟩ := rfl
@[simp] lemma im_lift (A : Operator ℝ H H) (x : (lift A).domain) :
    im (lift A x) = A ⟨im x, x.2.2⟩ := rfl

lemma mem_lift_graph (A : Operator ℝ H H) (x y : Complexification H) :
    (x,y) ∈ (lift A).graph ↔
      (re x,re y) ∈ A.graph ∧ (im x,im y) ∈ A.graph := by
  change (x,y) ∈ OperatorDomainsSpec.graphValue (lift A) ↔
    (re x,re y) ∈ OperatorDomainsSpec.graphValue A ∧
      (im x,im y) ∈ OperatorDomainsSpec.graphValue A
  rw [Unbounded.mem_graph_iff, Unbounded.mem_graph_iff, Unbounded.mem_graph_iff]
  constructor
  · rintro ⟨hx, he⟩
    exact ⟨⟨hx.1, congrArg re he⟩, ⟨hx.2, congrArg im he⟩⟩
  · rintro ⟨⟨hr,er⟩,⟨hi,ei⟩⟩
    exact ⟨⟨hr,hi⟩, ext er ei⟩

lemma lift_dense (A : Operator ℝ H H) (hd : Dense (A.domain : Set H)) :
    Dense ((lift A).domain : Set (Complexification H)) := by
  have hh := hd.prod hd
  let he := (WithLp.prodContinuousLinearEquiv 2 ℝ H H).symm.toHomeomorph
  apply (he.isDenseEmbedding.dense_image.mpr hh).mono
  rintro x ⟨y, hy, rfl⟩
  change (WithLp.toLp 2 y) ∈ (lift A).domain
  exact hy

variable [CompleteSpace H]
lemma lift_adjoint (A : Operator ℝ H H) (hd : Dense (A.domain : Set H)) :
    HilbertAdjointSpec.adjointValue (lift A) = lift (HilbertAdjointSpec.adjointValue A) := by
  apply LinearPMap.eq_of_eq_graph
  ext ⟨x,y⟩
  rw [mem_lift_graph]
  change (x,y) ∈ (hilbertAdjoint (lift A)).graph ↔
    (re x,re y) ∈ (hilbertAdjoint A).graph ∧ (im x,im y) ∈ (hilbertAdjoint A).graph
  rw [mem_hilbertAdjoint_graph_iff (lift A) (lift_dense A hd),
    mem_hilbertAdjoint_graph_iff A hd, mem_hilbertAdjoint_graph_iff A hd]
  constructor
  · intro h
    have hh (a : A.domain) := h ⟨mk a 0, a.2, A.domain.zero_mem⟩
    constructor
    · intro a
      have hr := congrArg Complex.re (hh a)
      simpa [inner_re, show A ⟨(0 : H), A.domain.zero_mem⟩ = 0 from A.map_zero] using hr
    · intro a
      have hi := congrArg Complex.im (hh a)
      simpa [inner_im, show A ⟨(0 : H), A.domain.zero_mem⟩ = 0 from A.map_zero] using hi
  · rintro ⟨hr,hi⟩ z
    apply Complex.ext
    · simpa only [inner_re, re_lift, im_lift] using
        congrArg₂ (· + ·) (hr ⟨re z,z.2.1⟩) (hi ⟨im z,z.2.2⟩)
    · simpa only [inner_im, re_lift, im_lift] using
        congrArg₂ (· - ·) (hi ⟨re z,z.2.1⟩) (hr ⟨im z,z.2.2⟩)

lemma lift_nonnegativeSelfAdjoint (A : Operator ℝ H H) (hA : NonnegativeSelfAdjoint A) :
    NonnegativeSelfAdjoint (lift A) := by
  refine ⟨lift_dense A hA.1, ?_, ?_⟩
  · rw [lift_adjoint A hA.1, hA.2.1]
  · intro x
    exact add_nonneg (hA.2.2 ⟨re x,x.2.1⟩) (hA.2.2 ⟨im x,x.2.2⟩)

lemma lift_lower_bound (A : Operator ℝ H H) (c : ℝ)
    (hc : ∀ x : A.domain, c * ‖(x : H)‖ ^ 2 ≤ inner ℝ (x : H) (A x)) :
    ∀ x : (lift A).domain,
      c * ‖(x : Complexification H)‖ ^ 2 ≤ (inner ℂ (x : Complexification H) (lift A x)).re := by
  intro x
  rw [norm_sq, mul_add, inner_re]
  exact add_le_add (hc ⟨re x,x.2.1⟩) (hc ⟨im x,x.2.2⟩)


/-- Compression through the real isometric inclusion does not increase norm. -/
def compress (B : Complexification H →L[ℂ] Complexification H) : H →L[ℝ] H :=
  realPart.comp ((B.restrictScalars ℝ).comp inclusion.toContinuousLinearMap)
@[simp] lemma compress_apply (B : Complexification H →L[ℂ] Complexification H) (x : H) :
    compress B x = re (B (inclusion x)) := rfl
lemma norm_compress_le (B : Complexification H →L[ℂ] Complexification H) : ‖compress B‖ ≤ ‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  apply (norm_re_le _).trans
  have hh := B.le_opNorm (inclusion x)
  rwa [inclusion.norm_map] at hh

def projectReal : Complexification H →L[ℝ] Complexification H :=
  inclusion.toContinuousLinearMap.comp realPart
@[simp] lemma projectReal_apply (x : Complexification H) : projectReal x = mk (re x) 0 := rfl

lemma projectReal_solution (A : Operator ℝ H H) (x : H) (u : ℝ → Complexification H)
    (hu : ClassicalSolution (lift A) (inclusion x) u) :
    ClassicalSolution (lift A) (inclusion x) (fun t => projectReal (u t)) := by
  refine ⟨?_, projectReal.continuous.continuousAt.comp_continuousWithinAt hu.2.1, ?_⟩
  · simp [hu.1]
  · intro t ht
    obtain ⟨hD,hd⟩ := hu.2.2 t ht
    have hpD : projectReal (u t) ∈ (lift A).domain := ⟨hD.1,A.domain.zero_mem⟩
    refine ⟨hpD, ?_⟩
    have hh := projectReal.hasFDerivAt.comp_hasDerivAt t hd
    convert hh using 1
    · rfl
    · apply ext <;> simp [show A ⟨(0 : H),A.domain.zero_mem⟩ = 0 from A.map_zero]

/-- Positive self-adjoint evolution preserves the original real form, proved
from energy uniqueness rather than assumed for a chosen spectral measure. -/
lemma preserves_real (A : Operator ℝ H H) (hA : NonnegativeSelfAdjoint A)
    (S : C0Semigroup ℂ (Complexification H)) (hS : SmoothingConclusion (lift A) S)
    (t : ℝ≥0) (x : H) : inclusion (compress (S.operators t) x) = S.operators t (inclusion x) := by
  have hh := classical_uniqueness ℂ (Complexification H) (lift A)
    (lift_nonnegativeSelfAdjoint A hA).2.2 (inclusion x)
    _ _ (projectReal_solution A x _ (hS.2.2.2.2.1 (inclusion x)))
      (hS.2.2.2.2.1 (inclusion x)) t t.coe_nonneg
  simpa using hh

def restrictSemigroup (A : Operator ℝ H H) (hA : NonnegativeSelfAdjoint A)
    (S : C0Semigroup ℂ (Complexification H)) (hS : SmoothingConclusion (lift A) S) :
    C0Semigroup ℝ H where
  operators t := compress (S.operators t)
  at_zero := by ext x; simp [S.at_zero]
  add_time t s := by
    ext x
    change re (S.operators (t+s) (inclusion x)) =
      re (S.operators t (inclusion (compress (S.operators s) x)))
    rw [preserves_real A hA S hS, S.add_time]
    rfl
  strong_zero x := by
    have hh := realPart.continuous.continuousAt.tendsto.comp (S.strong_zero (inclusion x))
    simpa only [Function.comp_def, realPart_apply, inclusion_apply, re_mk, compress_apply] using hh

lemma compress_selfAdjoint (B : Complexification H →L[ℂ] Complexification H)
    (hB : IsSelfAdjoint B) : IsSelfAdjoint (compress B) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  have hh := congrArg Complex.re (hB.isSymmetric (inclusion x) (inclusion y))
  simpa [inner_re] using hh

/-- The product graph characterization works over either manuscript field. -/
lemma partial_product_graph {𝕜 : Type*} [RCLike 𝕜] {V : Type*}
    [AddCommGroup V] [Module 𝕜 V] (A B : Operator 𝕜 V V) (x z : V) :
    (x,z) ∈ (OperatorDomainsSpec.productValue A B).graph ↔
      ∃ y, (x,y) ∈ B.graph ∧ (y,z) ∈ A.graph := by
  constructor
  · intro h
    obtain ⟨hx, hy⟩ := (Unbounded.mem_graph_iff _ (x,z)).mp h
    exact ⟨B ⟨x,hx.choose⟩, B.mem_graph ⟨x,hx.choose⟩,
      (Unbounded.mem_graph_iff A (_,z)).mpr ⟨hx.choose_spec,hy⟩⟩
  · rintro ⟨y,hxy,hyz⟩
    obtain ⟨hx,ex⟩ := (Unbounded.mem_graph_iff B (x,y)).mp hxy
    obtain ⟨hy,ey⟩ := (Unbounded.mem_graph_iff A (y,z)).mp hyz
    have hx' : x ∈ (OperatorDomainsSpec.productValue A B).domain :=
      ⟨hx, ex.symm ▸ hy⟩
    apply (Unbounded.mem_graph_iff _ (x,z)).mpr
    refine ⟨hx', ?_⟩
    change A ⟨B ⟨x,hx'.choose⟩,hx'.choose_spec⟩ = z
    simpa only [ex] using ey

lemma lift_power_graph (A : Operator ℝ H H) (m : ℕ) (x y : Complexification H) :
    (x,y) ∈ (OperatorDomainsSpec.powerValue (lift A) m).graph ↔
      (re x,re y) ∈ (OperatorDomainsSpec.powerValue A m).graph ∧
      (im x,im y) ∈ (OperatorDomainsSpec.powerValue A m).graph := by
  induction m generalizing x y with
  | zero =>
    change (x,y) ∈ ((LinearMap.id : Complexification H →ₗ[ℂ] Complexification H).toPMap ⊤).graph ↔
      (re x,re y) ∈ ((LinearMap.id : H →ₗ[ℝ] H).toPMap ⊤).graph ∧
      (im x,im y) ∈ ((LinearMap.id : H →ₗ[ℝ] H).toPMap ⊤).graph
    simp only [LinearPMap.mem_graph_iff, LinearMap.toPMap_apply, LinearMap.id_apply]
    constructor
    · rintro ⟨z,hz,he⟩
      exact ⟨⟨⟨re x,Submodule.mem_top⟩,rfl,congrArg re (hz.symm.trans he)⟩,
        ⟨⟨im x,Submodule.mem_top⟩,rfl,congrArg im (hz.symm.trans he)⟩⟩
    · rintro ⟨⟨a,ha,ea⟩,⟨b,hb,eb⟩⟩
      exact ⟨⟨x,Submodule.mem_top⟩,rfl,ext (ha.symm.trans ea) (hb.symm.trans eb)⟩
  | succ m ih =>
    change (x,y) ∈ (OperatorDomainsSpec.productValue (lift A)
      (OperatorDomainsSpec.powerValue (lift A) m)).graph ↔
      (re x,re y) ∈ (OperatorDomainsSpec.productValue A
        (OperatorDomainsSpec.powerValue A m)).graph ∧
      (im x,im y) ∈ (OperatorDomainsSpec.productValue A
        (OperatorDomainsSpec.powerValue A m)).graph
    rw [partial_product_graph, partial_product_graph, partial_product_graph]
    constructor
    · rintro ⟨z,hxz,hzy⟩
      exact ⟨⟨re z,(ih _ _).mp hxz |>.1,(mem_lift_graph _ _ _).mp hzy |>.1⟩,
        ⟨im z,(ih _ _).mp hxz |>.2,(mem_lift_graph _ _ _).mp hzy |>.2⟩⟩
    · rintro ⟨⟨a,ha,ka⟩,⟨b,hb,kb⟩⟩
      exact ⟨mk a b,(ih _ _).mpr ⟨ha,hb⟩,(mem_lift_graph _ _ _).mpr ⟨ka,kb⟩⟩


lemma inclusion_differenceQuotient (A : Operator ℝ H H) (hA : NonnegativeSelfAdjoint A)
    (S : C0Semigroup ℂ (Complexification H)) (hS : SmoothingConclusion (lift A) S)
    (h : ℝ) (x : H) :
    inclusion (C0SemigroupSpec.differenceQuotientValue (restrictSemigroup A hA S hS) h x) =
      C0SemigroupSpec.differenceQuotientValue S h (inclusion x) := by
  change inclusion (h⁻¹ • (compress (S.operators h.toNNReal) x - x)) =
    (algebraMap ℝ ℂ h)⁻¹ • (S.operators h.toNNReal (inclusion x) - inclusion x)
  rw [inclusion.map_smul, inclusion.map_sub, preserves_real A hA S hS]
  rw [← map_inv₀, IsScalarTower.algebraMap_smul]

lemma generatorLimit_restrict_iff (A : Operator ℝ H H) (hA : NonnegativeSelfAdjoint A)
    (S : C0Semigroup ℂ (Complexification H)) (hS : SmoothingConclusion (lift A) S)
    (x y : H) :
    C0SemigroupSpec.hasGeneratorLimitValue (restrictSemigroup A hA S hS) x y ↔
      C0SemigroupSpec.hasGeneratorLimitValue S (inclusion x) (inclusion y) := by
  constructor
  · intro hh
    have ht := (inclusion (H := H)).continuous.continuousAt.tendsto.comp hh
    simpa only [C0SemigroupSpec.hasGeneratorLimitValue, Function.comp_def,
      inclusion_differenceQuotient A hA S hS] using ht
  · intro hh
    have ht := (realPart (H := H)).continuous.continuousAt.tendsto.comp hh
    have he (h : ℝ) :
        realPart (C0SemigroupSpec.differenceQuotientValue S h (inclusion x)) =
          C0SemigroupSpec.differenceQuotientValue (restrictSemigroup A hA S hS) h x := by
      rw [← inclusion_differenceQuotient A hA S hS]
      rfl
    change Tendsto (fun h => realPart (C0SemigroupSpec.differenceQuotientValue S h (inclusion x)))
      (𝓝[>] (0 : ℝ)) (𝓝 y) at ht
    simpa only [C0SemigroupSpec.hasGeneratorLimitValue, he] using ht

lemma inclusion_mem_neg_lift_graph (A : Operator ℝ H H) (x y : H) :
    (inclusion x, inclusion y) ∈ (-lift A).graph ↔ (x,y) ∈ (-A).graph := by
  change (inclusion x, inclusion y) ∈ OperatorDomainsSpec.graphValue (-lift A) ↔
    (x,y) ∈ OperatorDomainsSpec.graphValue (-A)
  rw [Unbounded.mem_graph_iff, Unbounded.mem_graph_iff]
  constructor
  · rintro ⟨hx,he⟩
    exact ⟨hx.1, by simpa using congrArg re he⟩
  · rintro ⟨hx,he⟩
    refine ⟨⟨hx,A.domain.zero_mem⟩, ?_⟩
    apply ext
    · exact he
    · simp [show A ⟨(0 : H),A.domain.zero_mem⟩ = 0 from A.map_zero]

lemma restrict_generator (A : Operator ℝ H H) (hA : NonnegativeSelfAdjoint A)
    (S : C0Semigroup ℂ (Complexification H)) (hS : SmoothingConclusion (lift A) S) :
    C0SemigroupSpec.generatorValue (restrictSemigroup A hA S hS) = -A := by
  apply LinearPMap.eq_of_eq_graph
  ext ⟨x,y⟩
  rw [mem_generator_graph_iff, generatorLimit_restrict_iff A hA S hS,
    ← mem_generator_graph_iff, hS.1, inclusion_mem_neg_lift_graph]


lemma restrict_power_smoothing (A : Operator ℝ H H) (hA : NonnegativeSelfAdjoint A)
    (S : C0Semigroup ℂ (Complexification H)) (hS : SmoothingConclusion (lift A) S) :
    PowerSmoothing A (restrictSemigroup A hA S hS) := by
  intro t ht m hm
  obtain ⟨B, hB, hb⟩ := hS.2.2.1 t ht m hm
  refine ⟨compress B, ?_, (norm_compress_le B).trans hb⟩
  intro x
  exact ((lift_power_graph A m _ _).mp (hB (inclusion x))).1

lemma restrict_classical_solution (A : Operator ℝ H H) (hA : NonnegativeSelfAdjoint A)
    (S : C0Semigroup ℂ (Complexification H)) (hS : SmoothingConclusion (lift A) S)
    (x : H) : ClassicalSolution A x
      (fun t : ℝ => (restrictSemigroup A hA S hS).operators t.toNNReal x) := by
  have hu := hS.2.2.2.2.1 (inclusion x)
  simp only [ClassicalSolution] at hu ⊢
  refine ⟨?_, ?_, ?_⟩
  · change re (S.operators (Real.toNNReal 0) (inclusion x)) = x
    simp [S.at_zero]
  · exact realPart.continuous.continuousAt.comp_continuousWithinAt hu.2.1
  · intro t ht
    obtain ⟨hD, hd⟩ := hu.2.2 t ht
    refine ⟨hD.1, ?_⟩
    have hh := realPart.hasFDerivAt.comp_hasDerivAt t hd
    rw [hasDerivAt_iff_tendsto] at hh ⊢
    simpa [restrictSemigroup, compress_apply, realPart_apply, re_neg, re_lift, Function.comp_def,
      NormedSpace.restrictScalars, Module.restrictScalars, Module.compHom] using hh

lemma restrict_smoothing_conclusion (A : Operator ℝ H H) (hA : NonnegativeSelfAdjoint A)
    (S : C0Semigroup ℂ (Complexification H)) (hS : SmoothingConclusion (lift A) S)
    (hgen : C0SemigroupSpec.generatorValue (restrictSemigroup A hA S hS) = -A) :
    SmoothingConclusion A (restrictSemigroup A hA S hS) := by
  simp only [SmoothingConclusion]
  refine ⟨hgen, ?_, restrict_power_smoothing A hA S hS, ?_,
    restrict_classical_solution A hA S hS, ?_, ?_⟩
  · intro t
    exact ⟨compress_selfAdjoint _ (hS.2.1 t).1,
      (norm_compress_le _).trans (hS.2.1 t).2⟩
  · intro x
    have hh := hS.2.2.2.1 (inclusion x)
    exact hh.continuousLinearMap_comp realPart
  · intro x v hv t ht
    exact classical_uniqueness ℝ H A hA.2.2 x v _ hv
      (restrict_classical_solution A hA S hS x) t ht
  · intro c hc hb t
    apply (norm_compress_le _).trans
    apply hS.2.2.2.2.2.2 c hc
    exact lift_lower_bound A c hb

end Complexification

/-- The real-Hilbert theorem descends through the actual real isometric
inclusion in the Hilbert complexification, with the full generator domain. -/
theorem real_selfadjoint_smoothing : Spec.RealTheorem.{u} := by
  intro H _ _ _ L hL
  obtain ⟨S, hS, _⟩ := complex_selfadjoint_smoothing (Complexification.lift L)
    (Complexification.lift_nonnegativeSelfAdjoint L hL)
  refine ⟨Complexification.restrictSemigroup L hL S hS, ?_⟩
  exact Complexification.restrict_smoothing_conclusion L hL S hS
    (Complexification.restrict_generator L hL S hS)

/-- Self-adjoint heat smoothing over both manuscript scalar fields. -/
theorem selfadjoint_smoothing : Spec.FullTheorem.{u} :=
  ⟨real_selfadjoint_smoothing, complex_selfadjoint_smoothing⟩

end ExpandedFA.Semigroups.SelfAdjointSmoothing
