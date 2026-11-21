import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Proximal.EnvelopeGradient
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Proximal.MoreauDecomposition
import Mathlib.Analysis.Asymptotics.Lemmas
import Batteries.Tactic.OpenPrivate

/-!
Hilbert envelope differentiability from the standing hypotheses of
paper.tex:8430–8535 and the agreed Problem 26 differentiability disposition.

At x the proximal subgradient supplies the affine lower support. Comparing
the envelope at y against the minimizer at x supplies the quadratic upper
remainder. This proves the Fréchet derivative for every positive real μ.
Nonexpansiveness makes the residual and its Riesz functional norm continuous.
Moreau decomposition identifies the residual with the conjugate proximal
point; Fenchel equality and the quadratic square bound prove dual attainment.
-/
noncomputable section
open scoped InnerProductSpace Topology
namespace ExpandedFA.Proximal
open P1.ExtendedConvexFunctions Filter
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The real representative of the actual extended-real infimum. -/
def realMoreauEnvelope : EnvelopeSpec.RealEnvelopeType.{u} := EnvelopeSpec.RealEnvelopeValue

/-- The residual vector divided by the positive parameter. -/
def moreauGradient : EnvelopeSpec.GradientType.{u} := EnvelopeSpec.GradientValue

open private envelope_at_finite_minimizer from MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Proximal.MoreauDecomposition

lemma realMoreauEnvelope_at_minimizer (φ : ExtendedFunction H) (μ : ℝ) (f u : H)
    (r : ℝ) (hr : φ u = (r : WithTop ℝ)) (hu : IsProximalMinimizer H φ μ f u) :
    realMoreauEnvelope H φ μ f = r + ‖f - u‖ ^ 2 / (2 * μ) := by
  change (moreauEnvelope H φ μ f).toReal = _
  rw [envelope_at_finite_minimizer φ μ f u r hr hu, EReal.toReal_coe]

lemma realMoreauEnvelope_coe [CompleteSpace H] (φ : ExtendedFunction H)
    (hp : Proper H φ) (hc : ExtendedConvex H φ) (hl : LowerSemicontinuous H φ)
    (μ : ℝ) (hμ : 0 < μ) (f : H) :
    moreauEnvelope H φ μ f = (realMoreauEnvelope H φ μ f : EReal) := by
  obtain ⟨r, hr⟩ := moreauEnvelope_finite H φ hp hc hl μ hμ f
  change moreauEnvelope H φ μ f = ((moreauEnvelope H φ μ f).toReal : EReal)
  change moreauEnvelope H φ μ f = (r : EReal) at hr
  rw [hr, EReal.toReal_coe]

private lemma quadratic_support (μ : ℝ) (hμ : 0 < μ) (a b : H) :
    ‖b‖ ^ 2 / (2 * μ) + μ⁻¹ * ⟪b, a - b⟫_ℝ ≤ ‖a‖ ^ 2 / (2 * μ) := by
  have hn := sq_nonneg ‖a - b‖
  rw [norm_sub_sq_real] at hn
  rw [inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm a b]
  apply (mul_le_mul_iff_of_pos_right (by positivity : 0 < 2 * μ)).mp
  field_simp
  nlinarith

private lemma quadratic_increment (μ : ℝ) (hμ : 0 < μ) (a d : H) :
    ‖a + d‖ ^ 2 / (2 * μ) = ‖a‖ ^ 2 / (2 * μ) +
      μ⁻¹ * ⟪a, d⟫_ℝ + ‖d‖ ^ 2 / (2 * μ) := by
  rw [norm_add_sq_real]
  field_simp

/-- Global affine lower support and a quadratic upper remainder. -/
lemma moreauEnvelope_remainder [CompleteSpace H] (φ : ExtendedFunction H)
    (hp : Proper H φ) (hc : ExtendedConvex H φ) (hl : LowerSemicontinuous H φ)
    (μ : ℝ) (hμ : 0 < μ) (x y : H) :
    0 ≤ realMoreauEnvelope H φ μ y - realMoreauEnvelope H φ μ x -
        ⟪moreauGradient H φ μ x, y - x⟫_ℝ ∧
    realMoreauEnvelope H φ μ y - realMoreauEnvelope H φ μ x -
        ⟪moreauGradient H φ μ x, y - x⟫_ℝ ≤ ‖y - x‖ ^ 2 / (2 * μ) := by
  let u := proximalMap H φ μ x
  let z := proximalMap H φ μ y
  have hu : IsProximalMinimizer H φ μ x u := proximalMap_minimizes H φ hp hc hl μ hμ x
  have hz : IsProximalMinimizer H φ μ y z := proximalMap_minimizes H φ hp hc hl μ hμ y
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hu.1
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hz.1
  change (r : WithTop ℝ) = φ u at hr
  change (s : WithTop ℝ) = φ z at hs
  have hex := realMoreauEnvelope_at_minimizer φ μ x u r hr.symm hu
  have hey := realMoreauEnvelope_at_minimizer φ μ y z s hs.symm hz
  have hw := (proximalMap_characterization H φ hp hc hl μ hμ x u).2.mp rfl
  have hsub := hw.2 z
  change φ u + (⟪μ⁻¹ • (x - u), z - u⟫_ℝ : WithTop ℝ) ≤ φ z at hsub
  rw [← hr, ← hs, real_inner_smul_left, ← WithTop.coe_add] at hsub
  have hsub' := WithTop.coe_le_coe.mp hsub
  have hquad := quadratic_support μ hμ (y - z) (x - u)
  have hi : ⟪x - u, z - u⟫_ℝ + ⟪x - u, (y - z) - (x - u)⟫_ℝ =
      ⟪x - u, y - x⟫_ℝ := by
    rw [← inner_add_right]
    congr 1
    abel
  have hcomp := hz.2 u
  change φ z + ((‖y - z‖ ^ 2 / (2 * μ) : ℝ) : WithTop ℝ) ≤
    φ u + ((‖y - u‖ ^ 2 / (2 * μ) : ℝ) : WithTop ℝ) at hcomp
  rw [← hr, ← hs, ← WithTop.coe_add, ← WithTop.coe_add] at hcomp
  have hcomp' := WithTop.coe_le_coe.mp hcomp
  have hinc := quadratic_increment μ hμ (x - u) (y - x)
  have hid : (x - u) + (y - x) = y - u := by abel
  rw [hid] at hinc
  change 0 ≤ realMoreauEnvelope H φ μ y - realMoreauEnvelope H φ μ x -
    ⟪μ⁻¹ • (x - u), y - x⟫_ℝ ∧
    realMoreauEnvelope H φ μ y - realMoreauEnvelope H φ μ x -
    ⟪μ⁻¹ • (x - u), y - x⟫_ℝ ≤ ‖y - x‖ ^ 2 / (2 * μ)
  rw [hex, hey, real_inner_smul_left]
  have his := congrArg (fun t : ℝ => μ⁻¹ * t) hi
  constructor <;> nlinarith

lemma moreauGradient_continuous [CompleteSpace H] (φ : ExtendedFunction H)
    (hp : Proper H φ) (hc : ExtendedConvex H φ) (hl : LowerSemicontinuous H φ)
    (μ : ℝ) (hμ : 0 < μ) : Continuous (moreauGradient H φ μ) := by
  have hP : LipschitzWith 1 (proximalMap H φ μ) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_eq_norm, NNReal.coe_one, one_mul]
    exact proximalMap_nonexpansive H φ hp hc hl μ hμ x y
  exact (continuous_id.sub hP.continuous).const_smul μ⁻¹

lemma realMoreauEnvelope_hasFDerivAt [CompleteSpace H] (φ : ExtendedFunction H)
    (hp : Proper H φ) (hc : ExtendedConvex H φ) (hl : LowerSemicontinuous H φ)
    (μ : ℝ) (hμ : 0 < μ) (x : H) :
    HasFDerivAt (realMoreauEnvelope H φ μ)
      (InnerProductSpace.toDual ℝ H (moreauGradient H φ μ x)) x := by
  rw [hasFDerivAt_iff_isLittleO]
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have hden : 0 < 2 * μ := by positivity
  have he : ∀ᶠ y in 𝓝 x, ‖y - x‖ < ε * (2 * μ) := by
    have hb : ∀ᶠ y in 𝓝 x, y ∈ Metric.ball x (ε * (2 * μ)) :=
      Metric.ball_mem_nhds x (mul_pos hε hden)
    simpa only [Metric.mem_ball, dist_eq_norm] using hb
  filter_upwards [he] with y hy
  obtain ⟨hlower, hupper⟩ := moreauEnvelope_remainder φ hp hc hl μ hμ x y
  change ‖realMoreauEnvelope H φ μ y - realMoreauEnvelope H φ μ x -
    ⟪moreauGradient H φ μ x, y - x⟫_ℝ‖ ≤ ε * ‖y - x‖
  rw [Real.norm_eq_abs, abs_of_nonneg hlower]
  apply hupper.trans
  apply (div_le_iff₀ hden).mpr
  nlinarith [mul_le_mul_of_nonneg_right hy.le (norm_nonneg (y - x))]

theorem moreauEnvelope_regularity : EnvelopeSpec.Regularity.{u} := by
  intro H _ _ _ φ hp hc hl μ hμ
  have hg := moreauGradient_continuous φ hp hc hl μ hμ
  have hd := realMoreauEnvelope_hasFDerivAt φ hp hc hl μ hμ
  have hdc : Continuous (fun f => InnerProductSpace.toDual ℝ H (moreauGradient H φ μ f)) :=
    (InnerProductSpace.toDual ℝ H).continuous.comp hg
  refine ⟨realMoreauEnvelope_coe φ hp hc hl μ hμ,
    contDiff_one_iff_hasFDerivAt.mpr ⟨_, hdc, hd⟩, hd, fun f => (hd f).fderiv, ?_, hg⟩
  exact hdc.congr (fun f => (hd f).fderiv.symm)

private lemma quadratic_dual_bound (μ : ℝ) (hμ : 0 < μ) (a z : H) :
    ⟪z, a⟫_ℝ - μ * ‖z‖ ^ 2 / 2 ≤ ‖a‖ ^ 2 / (2 * μ) := by
  have hn := sq_nonneg ‖a - μ • z‖
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right, real_inner_comm z a] at hn
  apply (mul_le_mul_iff_of_pos_right (by positivity : 0 < 2 * μ)).mp
  field_simp
  nlinarith

/-- Weak duality for every Hilbert vector, including infinite conjugate values. -/
lemma moreau_dual_le [CompleteSpace H] (φ : ExtendedFunction H)
    (hp : Proper H φ) (hc : ExtendedConvex H φ) (hl : LowerSemicontinuous H φ)
    (μ : ℝ) (hμ : 0 < μ) (f z : H) :
    (⟪z, f⟫_ℝ : EReal) - hilbertConjugate H φ z -
      ((μ * ‖z‖ ^ 2 / 2 : ℝ) : EReal) ≤ moreauEnvelope H φ μ f := by
  by_cases ht : hilbertConjugate H φ z = ⊤
  · rw [ht, EReal.sub_top, EReal.bot_sub]
    exact bot_le
  · have hb := hilbertConjugate_ne_bot H φ hp z
    change hilbertConjugate H φ z ≠ ⊥ at hb
    let s := (hilbertConjugate H φ z).toReal
    have hs : hilbertConjugate H φ z = (s : EReal) := (EReal.coe_toReal ht hb).symm
    let u := proximalMap H φ μ f
    have hu : IsProximalMinimizer H φ μ f u :=
      proximalMap_minimizes H φ hp hc hl μ hμ f
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hu.1
    change (r : WithTop ℝ) = φ u at hr
    have hbound := (hilbertConjugate_isLUB H φ z).1 ⟨u, rfl⟩
    change (⟪z, u⟫_ℝ : EReal) - P1.C06Conjugates.extendedRealValue (φ u) ≤
      hilbertConjugate H φ z at hbound
    rw [← hr, hs] at hbound
    change (⟪z, u⟫_ℝ : EReal) - (r : EReal) ≤ (s : EReal) at hbound
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at hbound
    have hyoung := quadratic_dual_bound μ hμ (f - u) z
    rw [inner_sub_right] at hyoung
    rw [hs, realMoreauEnvelope_coe φ hp hc hl μ hμ f,
      realMoreauEnvelope_at_minimizer φ μ f u r hr.symm hu,
      ← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    linarith

theorem moreauGradient_dual_identification : EnvelopeSpec.DualIdentification.{u} := by
  intro H _ _ _ φ hp hc hl μ hμ f
  let u := proximalMap H φ μ f
  let w := moreauGradient H φ μ f
  have hw : w ∈ hilbertSubdifferential H φ u :=
    (proximalMap_characterization H φ hp hc hl μ hμ f u).2.mp rfl
  obtain ⟨r, s, hr, hs, _, hrs, _⟩ := conjugate_subgradient φ hp u w hw
  have hdecomp := (moreau_decomposition H φ hp hc hl μ hμ f).1
  change u + μ • proximalMap H (conjugateFunction H φ) μ⁻¹ (μ⁻¹ • f) = f at hdecomp
  have hfu : f - u = μ • w := by
    change f - u = μ • (μ⁻¹ • (f - u))
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hμ), one_smul]
  have hf : u + μ • w = f := by rw [← hfu]; abel
  have hdual : w = proximalMap H (conjugateFunction H φ) μ⁻¹ (μ⁻¹ • f) := by
    apply (smul_right_injective H (ne_of_gt hμ))
    exact add_left_cancel (hf.trans hdecomp.symm)
  have hex := realMoreauEnvelope_at_minimizer φ μ f u r hr
    (proximalMap_minimizes H φ hp hc hl μ hμ f)
  have hinner : ⟪w, f⟫_ℝ = ⟪u, w⟫_ℝ + μ * ‖w‖ ^ 2 := by
    rw [← hf, inner_add_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, real_inner_comm w u]
  have heq : realMoreauEnvelope H φ μ f = ⟪w, f⟫_ℝ - s - μ * ‖w‖ ^ 2 / 2 := by
    rw [hex, hfu, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hinner, ← hrs]
    field_simp
    ring
  exact ⟨hdual, r, s, hr, hs, hrs, heq, fun z => moreau_dual_le φ hp hc hl μ hμ f z⟩

end ExpandedFA.Proximal
