import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Proximal.SmallParameter
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Proximal.Existence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.Projection
import Mathlib.Topology.Order.Filter

/-! The small positive parameter limit, paper.tex:8573–8621.
Energy comparison and an affine minorant give a direct squared-distance bound.
Approximating the projection by points of the finite domain then proves the
full norm limit, including data outside the closure of the domain. -/
noncomputable section
open Set Filter
open scoped Topology InnerProductSpace
namespace ExpandedFA.Proximal
open P1.ExtendedConvexFunctions
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def domainProjection : SmallParameterSpec.DomainProjectionType.{u} :=
  SmallParameterSpec.DomainProjectionValue

/-- This is definitionally the accepted nearest-point projection; the proof
arguments establish its well-posedness and do not change its value. -/
theorem domainProjection_eq_convexProjection [CompleteSpace H]
    (φ : ExtendedFunction H)
    (hne : (closure (finiteDomain H φ)).Nonempty)
    (hc : Convex ℝ (closure (finiteDomain H φ))) (f : H) :
    domainProjection H φ f = Hilbert.Projection.convexProjection ℝ H
      (closure (finiteDomain H φ)) hne isClosed_closure hc f := rfl

private lemma projection_square_bound (f p u : H)
    (hproj : ⟪f - p, u - p⟫_ℝ ≤ 0) :
    ‖u - p‖ ^ 2 ≤ ‖f - u‖ ^ 2 - ‖f - p‖ ^ 2 := by
  have heq : f - u = (f - p) - (u - p) := by abel
  have hn := norm_sub_sq_real (f - p) (u - p)
  rw [← heq] at hn
  linarith

/-- Young's inequality absorbs the affine minorant's linear error. No global
lower bound on φ, or boundedness of its domain, is assumed. -/
private lemma distance_square_bound (φ : ExtendedFunction H)
    (ℓ : H →L[ℝ] ℝ) (c : ℝ)
    (hm : P1.AffineMinorants.IsContinuousAffineMinorant φ ℓ c)
    (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1) (f p u v : H) (s : ℝ)
    (hu : IsProximalMinimizer H φ μ f u) (hv : φ v = (s : WithTop ℝ))
    (hproj : ⟪f - p, u - p⟫_ℝ ≤ 0) :
    ‖u - p‖ ^ 2 ≤ 2 * (‖f - v‖ ^ 2 - ‖f - p‖ ^ 2) +
      4 * μ * (|s - ℓ p - c| + ‖ℓ‖ ^ 2) := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hu.1
  have he := hu.2 v
  change φ u + _ ≤ φ v + _ at he
  rw [← hr, hv, ← WithTop.coe_add, ← WithTop.coe_add] at he
  have he' := WithTop.coe_le_coe.mp he
  have he'' := mul_le_mul_of_nonneg_right he' (by positivity : 0 ≤ 2 * μ)
  field_simp at he''
  have hm' : ℓ u + c ≤ r := WithTop.coe_le_coe.mp (by simpa [hr] using hm u)
  have hℓ : ℓ p - ℓ u ≤ ‖ℓ‖ * ‖u - p‖ := by
    calc
      ℓ p - ℓ u = ℓ (p - u) := (map_sub ℓ p u).symm
      _ ≤ ‖ℓ (p - u)‖ := le_abs_self _
      _ ≤ ‖ℓ‖ * ‖p - u‖ := ℓ.le_opNorm _
      _ = ‖ℓ‖ * ‖u - p‖ := by rw [norm_sub_rev]
  have hp := projection_square_bound f p u hproj
  have hy := sq_nonneg (‖u - p‖ - 2 * μ * ‖ℓ‖)
  have hμsq : μ ^ 2 ≤ μ := by nlinarith
  have hμℓ := mul_le_mul_of_nonneg_right hμsq (sq_nonneg ‖ℓ‖)
  have ha := le_abs_self (s - ℓ p - c)
  have hemin : ‖f - u‖ ^ 2 ≤ ‖f - v‖ ^ 2 + 2 * μ * (s - r) := by
    nlinarith
  have hlower : s - r ≤ |s - ℓ p - c| + ‖ℓ‖ * ‖u - p‖ := by linarith
  have hmul := mul_le_mul_of_nonneg_left hlower hμ.le
  nlinarith

/-- Positive real parameters, with no closed-domain or in-domain restriction. -/
theorem proximalMap_smallParameter : SmallParameterSpec.SmallParameterLimit.{u} := by
  intro H _ _ _ φ hp hc hl f
  let C := closure (finiteDomain H φ)
  have hne : C.Nonempty := hp.closure
  have hconv : Convex ℝ C := (convex_finiteDomain H φ hc).closure
  let p := Hilbert.Projection.convexProjection ℝ H C hne isClosed_closure hconv f
  have hpvi := (Hilbert.Projection.eq_convexProjection_iff_variational
    ℝ H C hne isClosed_closure hconv f p).mp rfl
  change Tendsto (fun μ : ℝ => proximalMap H φ μ f) (𝓝[>] (0 : ℝ)) (𝓝 p)
  obtain ⟨ℓ, c, hm⟩ := P1.AffineMinorants.exists_continuous_affine_minorant H φ hp hc hl
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hcont : Continuous (fun v : H => ‖f - v‖ ^ 2) :=
    (continuous_const.sub continuous_id).norm.pow 2
  have hnb : {v : H | ‖f - v‖ ^ 2 < ‖f - p‖ ^ 2 + ε ^ 2 / 4} ∈ 𝓝 p :=
    hcont.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by linarith))
  obtain ⟨v, hvnb, hv⟩ := mem_closure_iff_nhds.mp hpvi.1 _ hnb
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hv
  let A := |s - ℓ p - c| + ‖ℓ‖ ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hδ : 0 < ε ^ 2 / (8 * (A + 1)) := div_pos hεsq (by positivity)
  have hevent : ∀ᶠ μ : ℝ in 𝓝[>] (0 : ℝ),
      0 < μ ∧ μ < 1 ∧ μ < ε ^ 2 / (8 * (A + 1)) := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with μ hpos h1 hsmall
    exact ⟨hpos, h1, hsmall⟩
  filter_upwards [hevent] with μ hμ
  have hu := proximalMap_minimizes H φ hp hc hl μ hμ.1 f
  have huC : proximalMap H φ μ f ∈ C := subset_closure hu.1
  have hb := distance_square_bound φ ℓ c hm μ hμ.1 hμ.2.1.le
    f p _ v s hu hs.symm (hpvi.2 _ huC)
  have hsmall := (lt_div_iff₀ (by positivity : 0 < 8 * (A + 1))).mp hμ.2.2
  rw [dist_eq_norm]
  change ‖proximalMap H φ μ f - p‖ < ε
  change ‖f - v‖ ^ 2 < ‖f - p‖ ^ 2 + ε ^ 2 / 4 at hvnb
  change ‖proximalMap H φ μ f - p‖ ^ 2 ≤
    2 * (‖f - v‖ ^ 2 - ‖f - p‖ ^ 2) + 4 * μ * A at hb
  nlinarith [norm_nonneg (proximalMap H φ μ f - p)]

end ExpandedFA.Proximal
