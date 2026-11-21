import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.C0pBoundary
import MathGenome.Internal.RealAnalysis.D11.Ch05.AtomicIntegrals
import MathGenome.Internal.RealAnalysis.D11.Ch10.QuotientConstruction
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Tactic.NormNum

/-! The two counterexamples of paper.tex:3575–3582. The counting example uses
exactly the source power integral, including exponents below one. On the
infinite atom integrability forces pointwise zero, before any scalar integral
is evaluated. Quotients and source norms are the accepted ordinary a.e. ones. -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace D11.Ch10.C0pBoundary
open Specs.D11.Ch10.C0pBoundary
open Specs.D11.Ch10.QuotientConstruction
open D11.Ch10.LpDefinition

variable {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]

lemma point_indicator_norm (p : ℝ) (hp : 0 < p) (a : Bool) :
    powerNorm Measure.count p (pointIndicator (𝕜 := 𝕜) a) = 1 := by
  rw [powerNorm, D11.Ch05.NonnegativeIntegral.integral_eq_lintegral,
    lintegral_fintype]
  cases a <;>
    simp [pointIndicator, Real.zero_rpow hp.ne']

lemma sum_indicators :
    pointIndicator (𝕜 := 𝕜) false + pointIndicator true = (fun _ => 1) := by
  funext x
  cases x <;> simp [pointIndicator]

lemma sum_indicator_norm (p : ℝ) :
    powerNorm Measure.count p
      (pointIndicator (𝕜 := 𝕜) false + pointIndicator true) = (2 : ℝ≥0∞) ^ (1 / p) := by
  rw [sum_indicators, powerNorm, D11.Ch05.NonnegativeIntegral.integral_eq_lintegral,
    lintegral_fintype]
  simp

theorem two_point_failure : Specs.D11.Ch10.C0pBoundary.two_point_failure := by
  intro 𝕜 _ _ _ p hp hp1
  dsimp only
  have hf := point_indicator_norm (𝕜 := 𝕜) p hp false
  have hg := point_indicator_norm (𝕜 := 𝕜) p hp true
  have hsum := sum_indicator_norm (𝕜 := 𝕜) p
  have hexp : 1 < 1 / p := (lt_div_iff₀ hp).mpr (by simpa using hp1)
  have hstrict : (2 : ℝ≥0∞) < (2 : ℝ≥0∞) ^ (1 / p) := by
    simpa using ENNReal.rpow_lt_rpow_of_exponent_lt
      (by norm_num : (1 : ℝ≥0∞) < 2) (by norm_num) hexp
  refine ⟨?_, ⟨measurable_of_countable _, ?_⟩,
    ⟨measurable_of_countable _, ?_⟩, ⟨measurable_of_countable _, ?_⟩,
    hf, hg, hsum, ?_, ?_⟩
  · intro heq
    have := congrFun heq false
    simp [pointIndicator] at this
  · change powerNorm _ _ _ < ∞
    rw [hf]
    exact ENNReal.one_lt_top
  · change powerNorm _ _ _ < ∞
    rw [hg]
    exact ENNReal.one_lt_top
  · change powerNorm _ _ _ < ∞
    rw [hsum]
    exact ENNReal.rpow_lt_top_of_nonneg (le_of_lt (one_div_pos.mpr hp)) (by norm_num)
  · simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hexp
  · change powerNorm _ _ _ + powerNorm _ _ _ < powerNorm _ _ _
    rw [hf, hg, hsum]
    convert hstrict using 1
    norm_num

lemma infinite_atom_univ : infiniteAtom univ = ∞ := by
  simp [infiniteAtom]

lemma infinite_atom_ne_zero : infiniteAtom ≠ 0 := by
  intro h
  have := infinite_atom_univ
  simp [h] at this

theorem infinite_atom_mass : Specs.D11.Ch10.C0pBoundary.infinite_atom_mass := by
  constructor
  · have h : ({()} : Set Unit) = univ := by ext x; cases x; simp
    rw [h, infinite_atom_univ]
  · intro s
    by_cases hs : () ∈ s
    · have heq : s = univ := Set.eq_univ_of_forall (fun x => by cases x; exact hs)
      rw [heq, infinite_atom_univ]
      simp
    · have heq : s = ∅ := by ext x; cases x; simp_all
      simp [heq]

lemma atom_power_one (f : Unit → 𝕜) :
    powerNorm infiniteAtom 1 f = ENNReal.ofReal ‖f ()‖ * ∞ := by
  rw [powerNorm, D11.Ch05.NonnegativeIntegral.integral_eq_lintegral,
    lintegral_unique, infinite_atom_univ]
  simp

lemma atom_raw_one_iff (f : Unit → 𝕜) :
    f ∈ rawLp infiniteAtom 1 ↔ f = 0 := by
  constructor
  · intro hf
    have hn := hf.2
    rw [atom_power_one] at hn
    have hz : f () = 0 := by
      by_contra h
      have hc : ENNReal.ofReal ‖f ()‖ ≠ 0 :=
        ne_of_gt (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr h))
      rw [ENNReal.mul_top hc] at hn
      exact (lt_irrefl _) hn
    funext x
    cases x
    exact hz
  · rintro rfl
    refine ⟨measurable_const, ?_⟩
    rw [atom_power_one]
    simp

lemma atom_raw_eq_zero (g : Raw (𝕜 := 𝕜) infiniteAtom 1) : g = 0 := by
  apply Subtype.ext
  apply (atom_raw_one_iff g.val).mp
  exact (D11.Ch10.LpDefinition.rawLp_iff_memLp infiniteAtom 1 g.val le_rfl).mpr
    ⟨g.property.1, by simpa using g.property.2⟩

lemma atom_quotient_eq_zero (q : QuotientLp (𝕜 := 𝕜) infiniteAtom 1) :
    q = classOf (0 : Raw (𝕜 := 𝕜) infiniteAtom 1) := by
  induction q using Quotient.inductionOn with
  | _ g =>
    rw [atom_raw_eq_zero g]
    rfl

theorem infinite_atom_L1 : Specs.D11.Ch10.C0pBoundary.infinite_atom_L1 := by
  intro 𝕜 _ _ _
  exact ⟨atom_raw_one_iff, atom_quotient_eq_zero⟩

lemma atom_one_source_norm :
    sourceNorm infiniteAtom ∞ (fun _ : Unit => (1 : 𝕜)) = 1 := by
  change D11.Ch04.EssentialBounds.essentialSupNorm infiniteAtom (fun _ => (1 : 𝕜)) = 1
  rw [D11.Ch04.EssentialBounds.essentialSupNorm_eq_native]
  simp only [enorm_one]
  exact essSup_const 1 infinite_atom_ne_zero

/-- This is the actual norm of the ordinary quotient, by the accepted
representative formula; it is not merely a raw-function calculation. -/
lemma atom_one_quotient_norm (f : Raw (𝕜 := 𝕜) infiniteAtom ∞)
    (hf : f.val = (fun _ => 1)) : ‖classOf f‖ = 1 := by
  rw [D11.Ch10.QuotientConstruction.norm_classOf]
  rw [hf, atom_one_source_norm]
  simp

lemma atom_pairing_zero (q : QuotientLp (𝕜 := 𝕜) infiniteAtom 1) : atomPairing q = 0 := by
  induction q using Quotient.inductionOn with
  | _ g =>
    change (∫ x, g.val x * (1 : 𝕜) ∂infiniteAtom) = 0
    rw [atom_raw_eq_zero g]
    simp

lemma atom_pairing_supremum :
    sSup ((fun q => ‖atomPairing q‖ₑ) '' (atomUnitBall (𝕜 := 𝕜))) = 0 := by
  apply le_antisymm _ bot_le
  apply sSup_le
  rintro _ ⟨q, _, rfl⟩
  simp [atom_pairing_zero]

theorem infinite_atom_endpoint : Specs.D11.Ch10.C0pBoundary.infinite_atom_endpoint := by
  intro 𝕜 _ _ _
  let oneRaw : Raw (𝕜 := 𝕜) infiniteAtom ∞ :=
    ⟨(fun _ => 1), measurable_const, memLp_top_const 1⟩
  have hn : sourceNorm infiniteAtom ∞ oneRaw.val = 1 := atom_one_source_norm
  refine ⟨oneRaw, rfl, hn, ?_, ?_, atom_pairing_supremum, ?_⟩
  · intro heq
    have hnorm := atom_one_quotient_norm oneRaw rfl
    rw [heq, D11.Ch10.QuotientConstruction.classOf_zero] at hnorm
    norm_num at hnorm
  · intro g
    rw [atom_raw_eq_zero g]
    constructor
    · simp
    · simp
  · rw [atom_pairing_supremum, hn]
    exact zero_lt_one

end D11.Ch10.C0pBoundary
