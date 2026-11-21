import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.UniformConvexSmoothDuals
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14UniformConvexity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.SmoothnessDefinitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05Norming
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Topology.Order.LeftRightNhds
import Batteries.Tactic.OpenPrivate

/-!
Uniform duality for the source moduli (paper.tex:4802–4839).
An equivalent norming-pair proof gives both equivalences directly. Its estimates
use only approximate norming in two unit balls, so do not need completeness.
Compare Carlen, *Notes on Uniform Convexity and Uniform Smoothness* (2009),
Theorem 2.3: the norming-pair estimates there are independent of completeness.
The actual dual below remains 𝕜-linear, including when 𝕜 = ℂ.
-/
namespace ExpandedFA.P1.UniformConvexSmoothDuals
open Filter
open scoped Topology
noncomputable section
universe u v

/-- A real bilinear pairing which determines both norms, with arbitrary
positive approximation error. This formulation includes the zero spaces. -/
structure RealNormingPair (A B : Type*) [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] where
  pair : A →ₗ[ℝ] B →ₗ[ℝ] ℝ
  bound : ∀ a b, pair a b ≤ ‖a‖ * ‖b‖
  left_approx : ∀ a (η : ℝ), 0 < η → ∃ b, ‖b‖ ≤ 1 ∧ ‖a‖ - η < pair a b
  right_approx : ∀ b (η : ℝ), 0 < η → ∃ a, ‖a‖ ≤ 1 ∧ ‖b‖ - η < pair a b

/-- A norm-sum version of uniform convexity. -/
def BallConvex (A : Type*) [NormedAddCommGroup A] : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a c : A,
    ‖a‖ ≤ 1 → ‖c‖ ≤ 1 → ε ≤ ‖a - c‖ → ‖a + c‖ ≤ 2 - δ

/-- The uniform small-parameter norm estimate equivalent to ρ(t)/t → 0. -/
def BallSmooth (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ τ : ℝ, 0 < τ ∧ ∀ t : ℝ, 0 < t → t < τ →
    ∀ b d : B, ‖b‖ ≤ 1 → ‖d‖ ≤ 1 →
      ‖b + t • d‖ + ‖b - t • d‖ ≤ 2 + ε * t

namespace RealNormingPair
variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

def flip (p : RealNormingPair A B) : RealNormingPair B A where
  pair := p.pair.flip
  bound b a := (p.bound a b).trans_eq (mul_comm _ _)
  left_approx := p.right_approx
  right_approx := p.left_approx

lemma sum_bound (p : RealNormingPair A B) (b d : B) (C : ℝ)
    (h : ∀ a c : A, ‖a‖ ≤ 1 → ‖c‖ ≤ 1 → p.pair a b + p.pair c d ≤ C) :
    ‖b‖ + ‖d‖ ≤ C := by
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨a, ha, hab⟩ := p.right_approx b (η / 2) (by positivity)
  obtain ⟨c, hc, hcd⟩ := p.right_approx d (η / 2) (by positivity)
  have := h a c ha hc
  linarith

lemma weighted_bound (p : RealNormingPair A B) (a c : A) {t : ℝ} (ht : 0 ≤ t)
    (C : ℝ) (h : ∀ b d : B, ‖b‖ ≤ 1 → ‖d‖ ≤ 1 →
      p.pair a b + t * p.pair c d ≤ C) : ‖a‖ + t * ‖c‖ ≤ C := by
  apply le_of_forall_pos_le_add
  intro η hη
  have hd : 0 < η / (1 + t) := div_pos hη (by linarith)
  obtain ⟨b, hb, hab⟩ := p.left_approx a _ hd
  obtain ⟨d, hd', hcd⟩ := p.left_approx c _ hd
  have heq : η / (1 + t) * (1 + t) = η := div_mul_cancel₀ _ (by linarith)
  have := h b d hb hd'
  have := mul_le_mul_of_nonneg_left hcd.le ht
  nlinarith

lemma expansion (p : RealNormingPair A B) (a c : A) (b d : B) (t : ℝ) :
    p.pair a (b + t • d) + p.pair c (b - t • d) =
      p.pair (a + c) b + t * p.pair (a - c) d := by
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    smul_eq_mul]
  ring

lemma expansion_le_left (p : RealNormingPair A B) (a c : A) (b d : B) {t : ℝ}
    (ht : 0 ≤ t) (hb : ‖b‖ ≤ 1) (hd : ‖d‖ ≤ 1) :
    p.pair a (b + t • d) + p.pair c (b - t • d) ≤ ‖a + c‖ + t * ‖a - c‖ := by
  rw [p.expansion]
  have h₁ := (p.bound (a + c) b).trans (mul_le_of_le_one_right (norm_nonneg _) hb)
  have h₂ := (p.bound (a - c) d).trans (mul_le_of_le_one_right (norm_nonneg _) hd)
  nlinarith

lemma convex_implies_smooth (p : RealNormingPair A B) (h : BallConvex A) :
    BallSmooth B := by
  intro ε hε
  let η := min ε 1
  have hη : 0 < η := lt_min hε zero_lt_one
  obtain ⟨δ, hδ, hc⟩ := h η hη
  refine ⟨δ / 2, by positivity, ?_⟩
  intro t ht htδ b d hb hd
  apply p.sum_bound
  intro a c ha hc'
  apply (p.expansion_le_left a c b d ht.le hb hd).trans
  have hsum : ‖a + c‖ ≤ 2 := (norm_add_le a c).trans (by linarith)
  have hdiff : ‖a - c‖ ≤ 2 := (norm_sub_le a c).trans (by linarith)
  by_cases hsep : η ≤ ‖a - c‖
  · have := hc a c ha hc' hsep
    nlinarith
  · have hηε : η ≤ ε := min_le_left _ _
    nlinarith

lemma smooth_implies_convex (p : RealNormingPair A B) (h : BallSmooth B) :
    BallConvex A := by
  intro ε hε
  obtain ⟨τ, hτ, hs⟩ := h (ε / 2) (by positivity)
  let t := τ / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have htτ : t < τ := by dsimp [t]; linarith
  refine ⟨ε * t / 2, by positivity, ?_⟩
  intro a c ha hc hsep
  have hbound : ‖a + c‖ + t * ‖a - c‖ ≤ 2 + (ε / 2) * t := by
    apply p.weighted_bound (a + c) (a - c) ht.le
    intro b d hb hd
    rw [← p.expansion]
    have h₁ := (p.bound a (b + t • d)).trans
      (mul_le_of_le_one_left (norm_nonneg _) ha)
    have h₂ := (p.bound c (b - t • d)).trans
      (mul_le_of_le_one_left (norm_nonneg _) hc)
    have := hs t ht htτ b d hb hd
    linarith
  nlinarith

end RealNormingPair

/-- The source's scalar midpoint and this norm-sum condition agree. -/
lemma uniformlyConvex_iff_ballConvex (𝕜 : Type*) (E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    C14UniformConvexity.Spec.UniformlyConvexValue 𝕜 E ↔ BallConvex E := by
  constructor
  · intro h ε hε
    by_cases hε₂ : ε ≤ 2
    · obtain ⟨δ, hδ, hc⟩ := h ε hε hε₂
      refine ⟨2 * δ, by positivity, ?_⟩
      intro a c ha hc' hsep
      have := hc a c ha hc' hsep
      rw [C14UniformConvexity.norm_midpoint_eq_half] at this
      linarith
    · refine ⟨1, zero_lt_one, ?_⟩
      intro a c ha hc hsep
      have := norm_sub_le a c
      exfalso
      linarith
  · intro h ε hε _
    obtain ⟨δ, hδ, hc⟩ := h ε hε
    refine ⟨δ / 2, by positivity, ?_⟩
    intro a c ha hc' hsep
    rw [C14UniformConvexity.norm_midpoint_eq_half]
    have := hc a c ha hc' hsep
    linarith

open private ball_values_bddAbove from MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.SmoothnessDefinitions

/-- Every pair in the two unit balls is bounded by the source modulus. -/
lemma norm_pair_le_modulus (𝕜 : Type*) (E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (t : ℝ) (x y : E)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    (‖x + (t : 𝕜) • y‖ + ‖x - (t : 𝕜) • y‖) / 2 - 1 ≤
      SmoothnessDefinitions.Spec.ModulusValue 𝕜 E t := by
  exact (le_csSup (ball_values_bddAbove 𝕜 E t) ⟨x, y, hx, hy, rfl⟩).trans
    (le_max_right _ _)

/-- This estimate is equivalent to the right-sided modulus limit, including
when the space has no unit vectors. -/
lemma uniformlySmooth_iff_ballSmooth (𝕜 : Type*) (E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
    [IsScalarTower ℝ 𝕜 E] :
    SmoothnessDefinitions.Spec.UniformlySmoothValue 𝕜 E ↔ BallSmooth E := by
  constructor
  · intro h ε hε
    have he : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        SmoothnessDefinitions.Spec.ModulusValue 𝕜 E t / t < ε / 2 :=
      h.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 2))
    obtain ⟨τ, hτ, heτ⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp he
    refine ⟨τ, hτ, ?_⟩
    intro t ht htτ x y hx hy
    have htρ := (div_lt_iff₀ ht).mp (heτ ⟨ht, htτ⟩)
    have hp := norm_pair_le_modulus 𝕜 E t x y hx hy
    simp only [← RCLike.real_smul_eq_coe_smul (K := 𝕜)] at hp
    linarith
  · intro h
    apply tendsto_order.2
    constructor
    · intro a ha
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      have hρ : 0 ≤ SmoothnessDefinitions.Spec.ModulusValue 𝕜 E t := le_max_left _ _
      exact ha.trans_le (div_nonneg hρ ht.le)
    · intro ε hε
      obtain ⟨τ, hτ, hs⟩ := h ε hε
      apply (nhdsGT_basis (0 : ℝ)).eventually_iff.mpr
      refine ⟨τ, hτ, ?_⟩
      intro t ⟨ht, htτ⟩
      have hρ : SmoothnessDefinitions.Spec.ModulusValue 𝕜 E t ≤ ε * t / 2 := by
        apply max_le (by positivity)
        apply csSup_le
        · exact ⟨-1, 0, 0, by simp, by simp, by simp⟩
        · rintro r ⟨x, y, hx, hy, rfl⟩
          have := hs t ht htτ x y hx hy
          simp only [RCLike.real_smul_eq_coe_smul (K := 𝕜)] at this
          linarith
      have hdiv : SmoothnessDefinitions.Spec.ModulusValue 𝕜 E t / t ≤ ε / 2 :=
        (div_le_iff₀ ht).mpr (by linarith)
      nlinarith

/-- Real-part evaluation, retaining the scalar-linear dual over 𝕜. -/
def evaluationPair (𝕜 : Type*) (E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    RealNormingPair E (E →L[𝕜] 𝕜) := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  refine { pair := ?_, bound := ?_, left_approx := ?_, right_approx := ?_ }
  · exact {
      toFun := fun x => {
        toFun := fun f => RCLike.re (f x)
        map_add' := by intros; simp
        map_smul' := by intros; simp [RCLike.smul_re] }
      map_add' := by intros; ext f; simp
      map_smul' := by intros; ext f; simp [RCLike.smul_re] }
  · intro x f
    exact (RCLike.re_le_norm _).trans ((f.le_opNorm x).trans_eq (mul_comm _ _))
  · intro x η hη
    obtain ⟨f, hf, hfx⟩ := C05Norming.norming_functional 𝕜 E x
    refine ⟨f, hf, ?_⟩
    change ‖x‖ - η < RCLike.re (f x)
    rw [hfx, RCLike.ofReal_re]
    linarith
  · intro f η hη
    obtain ⟨x, hx, hfx⟩ := f.exists_lt_apply_of_lt_opNorm (by linarith : ‖f‖ - η < ‖f‖)
    obtain ⟨c, hc, hcf⟩ := RCLike.exists_norm_eq_mul_self (f x)
    refine ⟨c • x, ?_, ?_⟩
    · simpa [norm_smul, hc] using hx.le
    · change ‖f‖ - η < RCLike.re (f (c • x))
      rw [map_smul, smul_eq_mul, ← hcf, RCLike.ofReal_re]
      exact hfx

/-- The first uniform duality equivalence, for arbitrary normed spaces. -/
theorem uniformlyConvex_iff_dual_uniformlySmooth : Spec.ConvexIffDualSmooth.{u,v} := by
  intro 𝕜 E _ _ _
  rcases subsingleton_or_nontrivial E with hE | hE
  · let := hE
    exact ⟨fun _ => SmoothnessDefinitions.uniformlySmooth_zero_space 𝕜 (E →L[𝕜] 𝕜),
      fun _ => C14UniformConvexity.uniformlyConvex_of_subsingleton 𝕜 E⟩
  · let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    let p := evaluationPair 𝕜 E
    rw [uniformlyConvex_iff_ballConvex 𝕜 E, uniformlySmooth_iff_ballSmooth 𝕜 (E →L[𝕜] 𝕜)]
    exact ⟨p.convex_implies_smooth, p.smooth_implies_convex⟩

/-- Swap the two sides of the norming pairing to obtain the second equivalence;
there is no completeness or reflexivity hypothesis. -/
theorem uniformlySmooth_iff_dual_uniformlyConvex : Spec.SmoothIffDualConvex.{u,v} := by
  intro 𝕜 E _ _ _
  rcases subsingleton_or_nontrivial E with hE | hE
  · let := hE
    exact ⟨fun _ => C14UniformConvexity.uniformlyConvex_of_subsingleton 𝕜 (E →L[𝕜] 𝕜),
      fun _ => SmoothnessDefinitions.uniformlySmooth_zero_space 𝕜 E⟩
  · let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    let p := (evaluationPair 𝕜 E).flip
    rw [uniformlySmooth_iff_ballSmooth 𝕜 E, uniformlyConvex_iff_ballConvex 𝕜 (E →L[𝕜] 𝕜)]
    exact ⟨p.smooth_implies_convex, p.convex_implies_smooth⟩

end
end ExpandedFA.P1.UniformConvexSmoothDuals
