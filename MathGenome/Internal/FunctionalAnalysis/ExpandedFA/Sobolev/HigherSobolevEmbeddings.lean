import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.HigherSobolevEmbeddings
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.SubcriticalSobolevEmbedding
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.MorreyEmbedding
import Mathlib.MeasureTheory.Function.LpSeminorm.Count
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Pow

noncomputable section
open Set TopologicalSpace MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology

namespace ExpandedFA.Sobolev.Higher
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Distribution derivatives compose by addition of their actual multi-indices. -/
theorem multiIndexDerivative_add (α β : Fin d → ℕ) (u : ScalarDistribution 𝕜 Ω) :
    Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue
      𝕜 d Ω (α + β) u =
    Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue
      𝕜 d Ω β
      (Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue
        𝕜 d Ω α u) := by
  change distributionDerivative 𝕜 d Ω (multiIndexWord (α + β)) u =
    distributionDerivative 𝕜 d Ω (multiIndexWord β)
      (distributionDerivative 𝕜 d Ω (multiIndexWord α) u)
  rw [← Smoothing.distributionDerivative_append]
  apply Smoothing.distributionDerivative_perm
  apply List.perm_iff_count.mpr
  intro i
  simp

@[simp] theorem natIndex_shiftIndex {m n : ℕ} (α : Fin d → ℕ)
    (h : (∑ i, α i) + n ≤ m) (β : DerivativeIndex d n) :
    natIndex (shiftIndex α h β) = α + natIndex β := rfl

@[simp] theorem natIndex_zeroIndex (n : ℕ) : natIndex (zeroIndex d n) = 0 := rfl

theorem shiftIndex_injective {m n : ℕ} (α : Fin d → ℕ)
    (h : (∑ i, α i) + n ≤ m) : Function.Injective (shiftIndex α h) := by
  intro β γ heq
  apply Subtype.ext
  funext i
  apply Fin.ext
  have hi := congrArg (fun δ => natIndex δ i) heq
  exact Nat.add_left_cancel hi

/-- The fixed weak derivative, with all its remaining weak derivatives. -/
def derivativeReduction {m n : ℕ} (α : Fin d → ℕ)
    (h : (∑ i, α i) + n ≤ m) (u : SpaceValue 𝕜 d Ω m p) :
    SpaceValue 𝕜 d Ω n p :=
  ⟨WithLp.toLp 1 (fun β => u.val (shiftIndex α h β)), by
    intro β
    change lpDistribution (u.val (shiftIndex α h β)) =
      Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue
        𝕜 d Ω (natIndex β) (lpDistribution (u.val (shiftIndex α h (zeroIndex d n))))
    have hβ := u.property (shiftIndex α h β)
    have hzero := u.property (shiftIndex α h (zeroIndex d n))
    change lpDistribution _ = _ at hβ hzero
    simp only [natIndex_shiftIndex, natIndex_zeroIndex, add_zero] at hβ hzero
    exact hβ.trans ((multiIndexDerivative_add α (natIndex β) _).trans
      (congrArg
        (Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue
          𝕜 d Ω (natIndex β)) hzero.symm))⟩

@[simp] theorem derivativeReduction_val {m n : ℕ} (α : Fin d → ℕ)
    (h : (∑ i, α i) + n ≤ m) (u : SpaceValue 𝕜 d Ω m p)
    (β : DerivativeIndex d n) :
    (derivativeReduction α h u).val β = u.val (shiftIndex α h β) := rfl

theorem derivativeReduction_norm_le {m n : ℕ} (α : Fin d → ℕ)
    (h : (∑ i, α i) + n ≤ m) (u : SpaceValue 𝕜 d Ω m p) :
    ‖derivativeReduction α h u‖ ≤ ‖u‖ := by
  classical
  rw [sobolev_norm_formula, sobolev_norm_formula]
  change (∑ β, ‖u.val (shiftIndex α h β)‖) ≤ ∑ γ, ‖u.val γ‖
  have hi : Set.InjOn (shiftIndex α h) (Finset.univ : Finset (DerivativeIndex d n)) :=
    (shiftIndex_injective α h).injOn
  rw [← Finset.sum_image (f := fun γ => ‖u.val γ‖) hi]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun _ _ _ => norm_nonneg _)

/-- A bounded scalar-linear operator on the accepted Sobolev graph. -/
def derivativeCLM {m n : ℕ} (α : Fin d → ℕ) (h : (∑ i, α i) + n ≤ m) :
    SpaceValue 𝕜 d Ω m p →L[𝕜] SpaceValue 𝕜 d Ω n p :=
  LinearMap.mkContinuous
    { toFun := derivativeReduction α h
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    1 (fun u => by
      change ‖derivativeReduction α h u‖ ≤ 1 * ‖u‖
      simpa only [one_mul] using derivativeReduction_norm_le α h u)

theorem derivative_reduction :
    Specs.ExpandedFA.Sobolev.HigherSobolevEmbeddings.DerivativeReduction := by
  intro 𝕜 _ d Ω m n p _ α h
  exact ⟨derivativeCLM α h, fun u => ⟨fun _ => rfl, derivativeReduction_norm_le α h u⟩⟩

/-- Uniform in the order and multi-index: the derivative reduction is a
contraction, so the accepted extension-domain Morrey constant suffices. -/
theorem derivative_morrey :
    Specs.ExpandedFA.Sobolev.HigherSobolevEmbeddings.DerivativeMorrey := by
  intro 𝕜 _ d Ω p _ hdp E hE
  obtain ⟨C, hC, h⟩ := Morrey.extension_domains 𝕜 d Ω p hdp E hE
  refine ⟨C, hC, fun m α hα u => ?_⟩
  obtain ⟨f, hf, hrep, hbound⟩ := h (derivativeReduction α hα u)
  refine ⟨f, hf, hrep, fun x hx y hy => (hbound x hx y hy).trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (derivativeReduction_norm_le α hα u) hC)
    (Real.rpow_nonneg (norm_nonneg _) _)

theorem c1_extension_domains :
    Specs.ExpandedFA.Sobolev.HigherSobolevEmbeddings.C1ExtensionDomains := by
  intro 𝕜 _ d Ω hΩ hcompact
  obtain ⟨T, E, hE, _⟩ := C1Extension.extension_exists 𝕜 d Ω hΩ hcompact
  intro p _
  exact ⟨E p, hE p⟩

section ChangeExponent
variable {q : ℝ≥0∞} [Fact (1 ≤ q)] {m : ℕ}

/-- Rebuild the same derivative graph at a new exponent. The membership
hypotheses concern the actual old derivative representatives. -/
def changeExponent (u : SpaceValue 𝕜 d Ω m p)
    (hmem : ∀ β, MemLp (u.val β) q (volume.restrict (Ω : Set (Domain d)))) :
    SpaceValue 𝕜 d Ω m q := by
  let v : DerivativeTuple 𝕜 Ω m q := WithLp.toLp 1 fun β => (hmem β).toLp (u.val β)
  have hv (β) : v β =ᵐ[volume.restrict (Ω : Set (Domain d))] u.val β :=
    (hmem β).coeFn_toLp
  refine ⟨v, ?_⟩
  intro β
  change lpDistribution (v β) =
    Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue
      𝕜 d Ω (natIndex β) (lpDistribution (v (zeroIndex d m)))
  rw [C1Extension.Transport.lpDistribution_eq_of_ae_exponent (v β) (u.val β) (hv β),
    C1Extension.Transport.lpDistribution_eq_of_ae_exponent
      (v (zeroIndex d m)) (u.val (zeroIndex d m)) (hv _)]
  exact u.property β

theorem changeExponent_coe (u : SpaceValue 𝕜 d Ω m p)
    (hmem : ∀ β, MemLp (u.val β) q (volume.restrict (Ω : Set (Domain d)))) (β) :
    (changeExponent u hmem).val β =ᵐ[volume.restrict (Ω : Set (Domain d))] u.val β :=
  (hmem β).coeFn_toLp

end ChangeExponent

/-- The norm formula in the extended nonnegative reals avoids any implicit
conversion between an Lp function and the chosen representative of its class. -/
theorem eNorm_eq_sum {m : ℕ} (u : SpaceValue 𝕜 d Ω m p) :
    ENNReal.ofReal ‖u‖ =
      ∑ β, eLpNorm (u.val β) p (volume.restrict (Ω : Set (Domain d))) := by
  rw [sobolev_norm_formula]
  simp only [NormValue]
  rw [ENNReal.ofReal_sum_of_nonneg (fun β _ => norm_nonneg (u.val β))]
  simp only [ofReal_norm, Lp.enorm_def]

/-- One full iteration step, proved on all components of the graph. -/
theorem lp_gain_step : Specs.ExpandedFA.Sobolev.HigherSobolevEmbeddings.LpGainStep := by
  intro 𝕜 _ d m Ω p q _ _ C hC u
  let hzero : (∑ i : Fin d, (0 : Fin d → ℕ) i) + m ≤ m+1 := by simp
  let w : SpaceValue 𝕜 d Ω m p := derivativeReduction 0 hzero u
  have hw (β : DerivativeIndex d m) :
      w.val β = u.val (orderIndex (Nat.le_succ m) β) := rfl
  let hβ (β : DerivativeIndex d m) : (∑ i, natIndex β i) + 1 ≤ m+1 :=
    Nat.add_le_add_right β.property 1
  let D (β : DerivativeIndex d m) : SpaceValue 𝕜 d Ω 1 p :=
    derivativeReduction (natIndex β) (hβ β) u
  have hD (β : DerivativeIndex d m) : (D β).val (zeroIndex d 1) = w.val β := by
    change u.val (shiftIndex (natIndex β) (hβ β) (zeroIndex d 1)) =
      u.val (shiftIndex 0 hzero β)
    have hi : shiftIndex (natIndex β) (hβ β) (zeroIndex d 1) = shiftIndex 0 hzero β := by
      apply Subtype.ext
      funext i
      apply Fin.ext
      simp [shiftIndex, natIndex, zeroIndex]
    rw [hi]
  have hmem (β : DerivativeIndex d m) :
      MemLp (w.val β) q (volume.restrict (Ω : Set (Domain d))) := by
    rw [← hD β]
    exact (hC (D β)).1
  refine ⟨changeExponent w hmem, ?_, ?_⟩
  · intro β
    simpa only [hw β] using changeExponent_coe w hmem β
  · rw [eNorm_eq_sum]
    calc
      _ = ∑ β, eLpNorm (w.val β) q (volume.restrict (Ω : Set (Domain d))) := by
        apply Finset.sum_congr rfl
        intro β _
        exact eLpNorm_congr_ae (changeExponent_coe w hmem β)
      _ ≤ ∑ _β : DerivativeIndex d m, (C : ℝ≥0∞) * ENNReal.ofReal ‖u‖ := by
        apply Finset.sum_le_sum
        intro β _
        rw [← hD β]
        apply (hC (D β)).2.trans
        exact mul_le_mul_of_nonneg_left
          (ENNReal.ofReal_le_ofReal (derivativeReduction_norm_le (natIndex β) (hβ β) u))
          (by positivity)
      _ = _ := by simp [mul_assoc]

/-- A bound on n remaining derivatives raises the exponent of an entire
m-th order graph; all its canonical components are preserved almost everywhere. -/
theorem lp_gain_order {m n : ℕ} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (C : ℝ≥0)
    (hC : ∀ u : SpaceValue 𝕜 d Ω n p,
      MemLp (u.val (zeroIndex d n)) q (volume.restrict (Ω : Set (Domain d))) ∧
      eLpNorm (u.val (zeroIndex d n)) q (volume.restrict (Ω : Set (Domain d))) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal ‖u‖)
    (u : SpaceValue 𝕜 d Ω (m+n) p) :
    ∃ v : SpaceValue 𝕜 d Ω m q,
      (∀ β, v.val β =ᵐ[volume.restrict (Ω : Set (Domain d))]
        u.val (orderIndex (Nat.le_add_right m n) β)) ∧
      ENNReal.ofReal ‖v‖ ≤ (Fintype.card (DerivativeIndex d m) : ℝ≥0∞) *
        (C : ℝ≥0∞) * ENNReal.ofReal ‖u‖ := by
  let hzero : (∑ i : Fin d, (0 : Fin d → ℕ) i) + m ≤ m+n := by simp
  let w : SpaceValue 𝕜 d Ω m p := derivativeReduction 0 hzero u
  have hw (β : DerivativeIndex d m) :
      w.val β = u.val (orderIndex (Nat.le_add_right m n) β) := rfl
  let hβ (β : DerivativeIndex d m) : (∑ i, natIndex β i) + n ≤ m+n :=
    Nat.add_le_add_right β.property n
  let D (β : DerivativeIndex d m) : SpaceValue 𝕜 d Ω n p :=
    derivativeReduction (natIndex β) (hβ β) u
  have hD (β : DerivativeIndex d m) : (D β).val (zeroIndex d n) = w.val β := by
    change u.val (shiftIndex (natIndex β) (hβ β) (zeroIndex d n)) =
      u.val (shiftIndex 0 hzero β)
    have hi : shiftIndex (natIndex β) (hβ β) (zeroIndex d n) = shiftIndex 0 hzero β := by
      apply Subtype.ext
      funext i
      apply Fin.ext
      simp [shiftIndex, natIndex, zeroIndex]
    rw [hi]
  have hmem (β : DerivativeIndex d m) :
      MemLp (w.val β) q (volume.restrict (Ω : Set (Domain d))) := by
    rw [← hD β]
    exact (hC (D β)).1
  refine ⟨changeExponent w hmem, ?_, ?_⟩
  · intro β
    simpa only [hw β] using changeExponent_coe w hmem β
  · rw [eNorm_eq_sum]
    calc
      _ = ∑ β, eLpNorm (w.val β) q (volume.restrict (Ω : Set (Domain d))) := by
        apply Finset.sum_congr rfl
        intro β _
        exact eLpNorm_congr_ae (changeExponent_coe w hmem β)
      _ ≤ ∑ _β : DerivativeIndex d m, (C : ℝ≥0∞) * ENNReal.ofReal ‖u‖ := by
        apply Finset.sum_le_sum
        intro β _
        rw [← hD β]
        apply (hC (D β)).2.trans
        exact mul_le_mul_of_nonneg_left
          (ENNReal.ofReal_le_ofReal (derivativeReduction_norm_le (natIndex β) (hβ β) u))
          (by positivity)
      _ = _ := by simp [mul_assoc]

/-- Whole space has the extension property, using the identity at every exponent. -/
theorem wholeSpace_extension :
    FirstOrderExtensionDomain 𝕜 (⊤ : Opens (Domain d)) := by
  intro p _
  exact ⟨ContinuousLinearMap.id 𝕜 _, fun _ => Filter.EventuallyEq.rfl⟩

/-- The accepted homogeneous first-order estimate gives a full-norm bound
on any domain with the actual first-order extension property. -/
theorem firstOrder_subcritical (hΩ : FirstOrderExtensionDomain 𝕜 Ω)
    (p : ℝ≥0) [Fact (1 ≤ (p : ℝ≥0∞))] (hp : 1 ≤ p) (hpd : p < d) :
    LpInclusion 𝕜 Ω 1 p (Subcritical.criticalExponent d p) := by
  obtain ⟨E, hE⟩ := hΩ p
  obtain ⟨C, hC⟩ := Subcritical.whole_space_inequality d p hp hpd
  refine ⟨C * d * (‖E‖).toNNReal, fun u => ?_⟩
  obtain ⟨hm, hb⟩ := hC 𝕜 (E u)
  refine ⟨(hm.restrict (Ω : Set (Domain d))).ae_eq (hE u), ?_⟩
  calc
    _ = eLpNorm ((E u).val (zeroIndex d 1)) (Subcritical.criticalExponent d p)
        (volume.restrict (Ω : Set (Domain d))) := eLpNorm_congr_ae (hE u).symm
    _ ≤ eLpNorm ((E u).val (zeroIndex d 1)) (Subcritical.criticalExponent d p) volume :=
      eLpNorm_restrict_le _ _ _ _
    _ ≤ (C : ℝ≥0∞) * eLpNorm (Subcritical.weakGradient (E u)) p volume := hb
    _ ≤ (C : ℝ≥0∞) * (d * ENNReal.ofReal ‖E u‖) := by
      apply mul_le_mul_right
      simpa using Subcritical.weakGradient_eLpNorm_le (E u)
    _ ≤ (C : ℝ≥0∞) * (d * (ENNReal.ofReal ‖E‖ * ENNReal.ofReal ‖u‖)) := by
      apply mul_le_mul_right
      apply mul_le_mul_right
      simpa only [ENNReal.ofReal_mul (norm_nonneg E)] using
        ENNReal.ofReal_le_ofReal (E.le_opNorm u)
    _ = _ := by
      simp only [ENNReal.coe_mul, ENNReal.coe_natCast, mul_assoc]
      rfl

@[simp] theorem orderIndex_zeroIndex {m n : ℕ} (h : n ≤ m) :
    orderIndex h (zeroIndex d n) = zeroIndex d m := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  simp [orderIndex, shiftIndex, zeroIndex, natIndex]

/-- Compose a gain on all components with a bound on the resulting graph. -/
theorem lpInclusion_step {m : ℕ} {q r : ℝ≥0∞} [Fact (1 ≤ q)]
    (H : LpInclusion 𝕜 Ω 1 p q) (K : LpInclusion 𝕜 Ω m q r) :
    LpInclusion 𝕜 Ω (m+1) p r := by
  obtain ⟨C, hC⟩ := H
  obtain ⟨D, hD⟩ := K
  refine ⟨D * Fintype.card (DerivativeIndex d m) * C, fun u => ?_⟩
  obtain ⟨v, hv, hn⟩ := lp_gain_step 𝕜 d m Ω p q C hC u
  obtain ⟨hm, hb⟩ := hD v
  have hzero := hv (zeroIndex d m)
  simp only [orderIndex_zeroIndex] at hzero
  refine ⟨hm.ae_eq hzero, ?_⟩
  calc
    _ = eLpNorm (v.val (zeroIndex d m)) r (volume.restrict (Ω : Set (Domain d))) :=
      eLpNorm_congr_ae hzero.symm
    _ ≤ (D : ℝ≥0∞) * ENNReal.ofReal ‖v‖ := hb
    _ ≤ (D : ℝ≥0∞) * ((Fintype.card (DerivativeIndex d m) : ℝ≥0∞) *
        (C : ℝ≥0∞) * ENNReal.ofReal ‖u‖) := by gcongr
    _ = _ := by simp only [ENNReal.coe_mul, ENNReal.coe_natCast]; ring

/-- Exact real-valued formula on the subcritical range. -/
theorem targetExponent_coe {m : ℕ} {p : ℝ≥0} (h : m * p < d) :
    (targetExponent d m p : ℝ) = (d : ℝ) * p / ((d : ℝ) - m * p) := by
  simp only [targetExponent, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast,
    NNReal.coe_sub h.le]

/-- The first reciprocal drop preserves admissibility and leaves exactly
m further drops before the specified target exponent. -/
theorem subcritical_iteration_arithmetic {m : ℕ} {p : ℝ≥0}
    (hp : 1 ≤ p) (h : ((m+1 : ℕ) : ℝ≥0) * p < d) :
    p < d ∧ 1 ≤ Subcritical.criticalExponent d p ∧
      m * Subcritical.criticalExponent d p < d ∧
      targetExponent d m (Subcritical.criticalExponent d p) =
        targetExponent d (m+1) p := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hR : ((m : ℝ) + 1) * p < d := by exact_mod_cast h
  have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hp0 : (0 : ℝ) < p := by linarith
  have hpdR : (p : ℝ) < d := by nlinarith
  have hpd : p < d := by exact_mod_cast hpdR
  have hd0 : (0 : ℝ) < d := hp0.trans hpdR
  have hden : (0 : ℝ) < (d : ℝ) - p := sub_pos.mpr hpdR
  have hq := Subcritical.criticalExponent_coe hpd
  have hq1 : (1 : ℝ) ≤ Subcritical.criticalExponent d p := by
    rw [hq, le_div_iff₀ hden]
    nlinarith
  have hmqR : (m : ℝ) * Subcritical.criticalExponent d p < d := by
    rw [hq, ← mul_div_assoc, div_lt_iff₀ hden]
    nlinarith
  have hmq : m * Subcritical.criticalExponent d p < d := by exact_mod_cast hmqR
  refine ⟨hpd, by exact_mod_cast hq1, hmq, ?_⟩
  apply NNReal.eq
  rw [targetExponent_coe hmq, targetExponent_coe h, hq]
  push_cast
  have hden2 : (d : ℝ) - ((m : ℝ) + 1) * p ≠ 0 := ne_of_gt (by linarith)
  have hden3 : (d : ℝ) - m * ((d : ℝ) * p / ((d : ℝ) - p)) ≠ 0 := by
    rw [← hq]
    exact ne_of_gt (sub_pos.mpr hmqR)
  field_simp
  <;> ring

/-- Iteration on the canonical distributional graph; only first-order
extension operators are used, so no higher-order boundary smoothness is needed. -/
theorem subcritical_extension_inclusion (hΩ : FirstOrderExtensionDomain 𝕜 Ω)
    (m : ℕ) (p : ℝ≥0) [Fact (1 ≤ (p : ℝ≥0∞))]
    (hp : 1 ≤ p) (hmp : m * p < d) :
    LpInclusion 𝕜 Ω m p (targetExponent d m p) := by
  induction m generalizing p with
  | zero =>
    have hd : (d : ℝ≥0) ≠ 0 := ne_of_gt (by simpa using hmp)
    have heq : targetExponent d 0 p = p := by
      simp [targetExponent, hd, mul_div_cancel_left₀]
    rw [heq]
    refine ⟨1, fun u => ⟨Lp.memLp _, ?_⟩⟩
    simp only [ENNReal.coe_one, one_mul]
    rw [← Lp.enorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (PiLp.norm_apply_le u.val (zeroIndex d 0))
  | succ m ih =>
    obtain ⟨hpd, hq1, hmq, heq⟩ := subcritical_iteration_arithmetic hp hmp
    letI : Fact (1 ≤ (Subcritical.criticalExponent d p : ℝ≥0∞)) :=
      ⟨by exact_mod_cast hq1⟩
    rw [← heq]
    exact lpInclusion_step (firstOrder_subcritical hΩ p hp hpd)
      (ih (Subcritical.criticalExponent d p) hq1 hmq)

theorem subcritical_whole_space :
    Specs.ExpandedFA.Sobolev.HigherSobolevEmbeddings.SubcriticalWholeSpace := by
  intro 𝕜 _ d m p _ hp hmp
  exact subcritical_extension_inclusion wholeSpace_extension m p hp hmp

theorem subcritical_bounded_extension :
    Specs.ExpandedFA.Sobolev.HigherSobolevEmbeddings.SubcriticalBoundedExtension := by
  intro 𝕜 _ d m Ω _ hΩ p _ hp hmp
  exact subcritical_extension_inclusion hΩ m p hp hmp

/-- Lower the target exponent on a finite-volume set, retaining the estimate. -/
theorem lpInclusion_lowerTarget {m : ℕ} {r : ℝ≥0∞} (q : ℝ≥0) (hq : 1 ≤ q)
    (hqr : (q : ℝ≥0∞) ≤ r) (hΩ : Bornology.IsBounded (Ω : Set (Domain d)))
    (H : LpInclusion 𝕜 Ω m p r) : LpInclusion 𝕜 Ω m p q := by
  let μ := volume.restrict (Ω : Set (Domain d))
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hΩ.measure_lt_top.ne
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (zero_lt_one.trans_le hq)
  have hexp : 0 ≤ 1 / (q : ℝ) - 1 / r.toReal := by
    by_cases hr : r = ∞
    · simp [hr]
    · apply sub_nonneg.mpr
      exact one_div_le_one_div_of_le hq0 (by
        simpa using ENNReal.toReal_mono hr hqr)
  let B : ℝ≥0∞ := μ univ ^ (1 / (q : ℝ) - 1 / r.toReal)
  have hB : B ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hexp (measure_ne_top μ univ)
  obtain ⟨C, hC⟩ := H
  refine ⟨C * B.toNNReal, fun u => ?_⟩
  obtain ⟨hm, hb⟩ := hC u
  refine ⟨hm.mono_exponent hqr, ?_⟩
  calc
    _ ≤ eLpNorm (u.val (zeroIndex d m)) r μ * B := by
      simpa [B, μ] using eLpNorm_le_eLpNorm_mul_rpow_measure_univ hqr hm.aestronglyMeasurable
    _ ≤ ((C : ℝ≥0∞) * ENNReal.ofReal ‖u‖) * B := by gcongr
    _ = _ := by rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hB]; ring

/-- Lower the exponent of the entire derivative graph on a bounded domain. -/
theorem lpInclusion_lowerSource {m : ℕ} {r q : ℝ≥0∞} [Fact (1 ≤ r)]
    (hΩ : Bornology.IsBounded (Ω : Set (Domain d))) (hrp : r ≤ p)
    (hexp : 0 ≤ 1 / r.toReal - 1 / p.toReal)
    (H : LpInclusion 𝕜 Ω m r q) : LpInclusion 𝕜 Ω m p q := by
  let μ := volume.restrict (Ω : Set (Domain d))
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hΩ.measure_lt_top.ne
  let A : ℝ≥0∞ := μ univ ^ (1 / r.toReal - 1 / p.toReal)
  have hA : A ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hexp (measure_ne_top μ univ)
  obtain ⟨C, hC⟩ := H
  refine ⟨C * A.toNNReal, fun u => ?_⟩
  let v := C1Extension.Transport.lowerExponent hrp u
  have hv : v.val (zeroIndex d m) =ᵐ[μ] u.val (zeroIndex d m) :=
    C1Extension.Transport.lowerExponent_coe hrp u _
  obtain ⟨hm, hb⟩ := hC v
  refine ⟨hm.ae_eq hv, ?_⟩
  calc
    _ = eLpNorm (v.val (zeroIndex d m)) q μ := eLpNorm_congr_ae hv.symm
    _ ≤ (C : ℝ≥0∞) * ENNReal.ofReal ‖v‖ := hb
    _ ≤ (C : ℝ≥0∞) * (ENNReal.ofReal ‖u‖ * A) := by
      exact mul_le_mul_of_nonneg_left (Subcritical.lowerExponent_eNorm_le hrp u) (by positivity)
    _ = _ := by rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hA]; ring

/-- Transfer a first-order estimate on a containing open set through a
whole-space extension and restriction. -/
theorem lpInclusion_from_containing_domain {U : Opens (Domain d)} (hΩU : Ω ≤ U)
    {q : ℝ≥0∞} (H : LpInclusion 𝕜 U 1 p q)
    (E : SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d ⊤ 1 p)
    (hE : C1Extension.IsExtension Ω E) : LpInclusion 𝕜 Ω 1 p q := by
  obtain ⟨C, hC⟩ := H
  refine ⟨C * ‖E‖₊, fun u => ?_⟩
  let v := C1Extension.restrictSobolev (show U ≤ ⊤ from le_top) (E u)
  have hv : v.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
      u.val (zeroIndex d 1) :=
    ((C1Extension.restrictSobolev_coe le_top (E u) (zeroIndex d 1)).filter_mono
      (ae_mono (Measure.restrict_mono hΩU le_rfl))).trans (hE u)
  obtain ⟨hm, hb⟩ := hC v
  refine ⟨(hm.mono_measure (Measure.restrict_mono hΩU le_rfl)).ae_eq hv, ?_⟩
  calc
    _ = eLpNorm (v.val (zeroIndex d 1)) q (volume.restrict (Ω : Set (Domain d))) :=
      eLpNorm_congr_ae hv.symm
    _ ≤ eLpNorm (v.val (zeroIndex d 1)) q (volume.restrict (U : Set (Domain d))) :=
      eLpNorm_mono_measure _ (Measure.restrict_mono hΩU le_rfl)
    _ ≤ (C : ℝ≥0∞) * ENNReal.ofReal ‖v‖ := hb
    _ ≤ (C : ℝ≥0∞) * (ENNReal.ofReal ‖E‖ * ENNReal.ofReal ‖u‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [← ENNReal.ofReal_mul (norm_nonneg E)]
      exact ENNReal.ofReal_le_ofReal
        ((C1Extension.restrictSobolev_norm_le le_top (E u)).trans (E.le_opNorm u))
    _ = _ := by
      rw [show ENNReal.ofReal ‖E‖ = (‖E‖₊ : ℝ≥0∞) from ENNReal.ofReal_eq_coe_nnreal _]
      simp only [ENNReal.coe_mul, mul_assoc]

/-- The accepted interval estimate supplies the genuine one-dimensional
critical endpoint needed for the first-order iteration. -/
theorem interval_one_infinity (a b : ℝ) (hab : a < b) :
    LpInclusion 𝕜 (OneDimensional.lineDomain ⟨Ioo a b, isOpen_Ioo⟩) 1 1 ∞ := by
  let c : ℝ≥0 := ⟨(b-a)⁻¹ + 1, by positivity⟩
  refine ⟨c, fun u => ?_⟩
  obtain ⟨f, hf⟩ := OneDimensional.representative_existence 𝕜
    ⟨Ioo a b, isOpen_Ioo⟩ ordConnected_Ioo 1 u
  have H := OneDimensional.finite_interval_essential_supremum 𝕜 a b hab 1 u f hf
  have hnorm : (b-a)⁻¹ * ‖OneDimensional.baseLp u‖ + ‖OneDimensional.derivativeLp u‖ ≤
      (c : ℝ) * ‖u‖ := by
    have hb := PiLp.norm_apply_le u.val (zeroIndex 1 1)
    have hd := PiLp.norm_apply_le u.val OneDimensional.firstIndex
    have hinv : 0 ≤ (b-a)⁻¹ := by positivity
    change ‖OneDimensional.baseLp u‖ ≤ ‖u‖ at hb
    change ‖OneDimensional.derivativeLp u‖ ≤ ‖u‖ at hd
    change _ ≤ ((b-a)⁻¹ + 1) * ‖u‖
    nlinarith
  have hbound : eLpNorm (u.val (zeroIndex 1 1)) ∞
      (volume.restrict (OneDimensional.lineDomain ⟨Ioo a b, isOpen_Ioo⟩ : Set (Domain 1))) ≤
      (c : ℝ≥0∞) * ENNReal.ofReal ‖u‖ := by
    simp only [OneDimensional.reciprocalExponent, ENNReal.toReal_one, div_one,
      Real.rpow_neg_one, sub_self, Real.rpow_zero, one_mul] at H
    apply H.trans
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul c.coe_nonneg]
    exact ENNReal.ofReal_le_ofReal hnorm
  exact ⟨hbound.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top), hbound⟩

/-- First-order critical bounds on every bounded extension domain, including
p=d=1. The two-dimensional and higher cases lower the source exponent. -/
theorem firstOrder_critical (hΩb : Bornology.IsBounded (Ω : Set (Domain d)))
    (hΩ : FirstOrderExtensionDomain 𝕜 Ω) (hd : 1 ≤ d)
    [Fact (1 ≤ (d : ℝ≥0∞))] (q : ℝ≥0) (hq : 1 ≤ q) :
    LpInclusion 𝕜 Ω 1 d q := by
  by_cases hd1 : d = 1
  · subst d
    obtain ⟨r, hr, hball⟩ := hΩb.subset_ball_lt 1 (0 : Domain 1)
    have hΩI : Ω ≤ OneDimensional.lineDomain ⟨Ioo (-r) r, isOpen_Ioo⟩ := by
      intro x hx
      have hxcoord : |x 0| < r := by
        have hxnorm : ‖x‖ < r := by simpa using hball hx
        exact (show |x 0| ≤ ‖x‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x 0).trans_lt hxnorm
      exact abs_lt.mp hxcoord
    obtain ⟨E, hE⟩ := hΩ 1
    have H := lpInclusion_from_containing_domain hΩI
      (interval_one_infinity (𝕜 := 𝕜) (-r) r (by linarith)) E hE
    simpa only [Nat.cast_one] using lpInclusion_lowerTarget (p := 1) q hq le_top hΩb H
  · obtain ⟨r, hr, hrd, hqr⟩ :=
      Subcritical.choose_subcritical_exponent (show 2 ≤ d by omega) q hq
    letI : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hr⟩
    have H := firstOrder_subcritical hΩ r hr hrd
    have K := lpInclusion_lowerTarget q hq (by exact_mod_cast hqr) hΩb H
    apply lpInclusion_lowerSource hΩb (by exact_mod_cast hrd.le) _ K
    simp only [ENNReal.coe_toReal, ENNReal.toReal_natCast]
    exact sub_nonneg.mpr (one_div_le_one_div_of_le
      (by exact_mod_cast zero_lt_one.trans_le hr) (by exact_mod_cast hrd.le))

/-- In dimension zero an open domain is empty or the mass-one singleton.
Every finite target exponent therefore has the same component norm. -/
theorem zeroDimension_inclusion {Ω : Opens (Domain 0)} {m : ℕ}
    (q : ℝ≥0) (hq : 1 ≤ q) : LpInclusion 𝕜 Ω m p q := by
  by_cases h0 : (0 : Domain 0) ∈ (Ω : Set (Domain 0))
  · have htop : Ω = ⊤ := by
      ext x
      change x ∈ (Ω : Set (Domain 0)) ↔ True
      simpa only [Subsingleton.elim x 0, iff_true] using h0
    subst Ω
    have hμ : volume.restrict ((⊤ : Opens (Domain 0)) : Set (Domain 0)) =
        Measure.dirac (0 : Domain 0) := by
      rw [Opens.coe_top, Measure.restrict_univ, Measure.volume_pi_eq_dirac (0 : Domain 0)]
    have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le Fact.out)
    have hq0 : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast (ne_of_gt (zero_lt_one.trans_le hq))
    refine ⟨1, fun u => ?_⟩
    have hdir (f : Domain 0 → 𝕜) : eLpNorm f q
        (volume.restrict ((⊤ : Opens (Domain 0)) : Set (Domain 0))) =
        eLpNorm f p
          (volume.restrict ((⊤ : Opens (Domain 0)) : Set (Domain 0))) := by
      rw [hμ, eLpNorm_dirac _ _ hq0, eLpNorm_dirac _ _ hp0]
    have hn := hdir (u.val (zeroIndex 0 m))
    refine ⟨hn.trans_lt (Lp.memLp _), ?_⟩
    rw [hn, ← Lp.enorm_def, ← ofReal_norm]
    simp only [ENNReal.coe_one, one_mul]
    exact ENNReal.ofReal_le_ofReal (PiLp.norm_apply_le u.val (zeroIndex 0 m))
  · have hbot : Ω = ⊥ := by
      ext x
      change x ∈ (Ω : Set (Domain 0)) ↔ False
      simpa only [Subsingleton.elim x 0, iff_false] using h0
    subst Ω
    refine ⟨0, fun u => ?_⟩
    simp

/-- At a critical higher order, one subcritical step leaves another critical
problem with one less derivative. -/
theorem critical_iteration_arithmetic {m : ℕ} {p : ℝ≥0} (hm : 1 ≤ m)
    (hp : 1 ≤ p) (h : ((m+1 : ℕ) : ℝ≥0) * p = d) :
    p < d ∧ 1 ≤ Subcritical.criticalExponent d p ∧
      m * Subcritical.criticalExponent d p = d := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hR : ((m : ℝ) + 1) * p = d := by exact_mod_cast h
  have hpdR : (p : ℝ) < d := by nlinarith
  have hpd : p < d := by exact_mod_cast hpdR
  have hden : (0 : ℝ) < (d : ℝ) - p := sub_pos.mpr hpdR
  have hq := Subcritical.criticalExponent_coe hpd
  have hq1 : (1 : ℝ) ≤ Subcritical.criticalExponent d p := by
    rw [hq, le_div_iff₀ hden]
    nlinarith
  refine ⟨hpd, by exact_mod_cast hq1, ?_⟩
  apply NNReal.eq
  push_cast
  rw [hq, ← mul_div_assoc, div_eq_iff hden.ne']
  nlinarith

/-- Full critical iteration, including p=1, empty sets, and the zero-order
zero-dimensional case. Only finite target exponents are claimed. -/
theorem critical_bounded_extension :
    Specs.ExpandedFA.Sobolev.HigherSobolevEmbeddings.CriticalBoundedExtension := by
  intro 𝕜 _ d m Ω hΩb hΩ p q _ hp hq hmp
  induction m generalizing p with
  | zero =>
    have hd : d = 0 := by simpa using hmp.symm
    subst d
    exact zeroDimension_inclusion q hq
  | succ m ih =>
    by_cases hm : m = 0
    · subst m
      have hpEq : p = d := by simpa using hmp
      subst p
      have hd : 1 ≤ d := by exact_mod_cast hp
      letI : Fact (1 ≤ (d : ℝ≥0∞)) := ⟨by exact_mod_cast hd⟩
      simpa only [ENNReal.coe_natCast] using firstOrder_critical hΩb hΩ hd q hq
    · obtain ⟨hpd, hr1, hmr⟩ := critical_iteration_arithmetic
        (show 1 ≤ m by omega) hp hmp
      letI : Fact (1 ≤ (Subcritical.criticalExponent d p : ℝ≥0∞)) :=
        ⟨by exact_mod_cast hr1⟩
      exact lpInclusion_step (firstOrder_subcritical hΩ p hp hpd)
        (ih (Subcritical.criticalExponent d p) hr1 hmr)

/-- Reciprocal exponent arithmetic at the exact nonintegral Morrey threshold. -/
theorem targetExponent_morrey {n : ℕ} {p : ℝ≥0}
    (hp : 1 ≤ p) (hn : n * p < d) (hsuper : d < (n+1 : ℕ) * p) :
    (d : ℝ≥0) < targetExponent d n p ∧
      Morrey.exponent d (targetExponent d n p) =
        ((n+1 : ℕ) : ℝ) - (d : ℝ) / p := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hnR : (n : ℝ) * p < d := by exact_mod_cast hn
  have hd0 : (0 : ℝ) < d := lt_of_le_of_lt (mul_nonneg (Nat.cast_nonneg _) (by positivity)) hnR
  have hsR : (d : ℝ) < ((n : ℝ) + 1) * p := by exact_mod_cast hsuper
  have hden : (0 : ℝ) < (d : ℝ) - n * p := sub_pos.mpr hnR
  have hq : (d : ℝ) < targetExponent d n p := by
    rw [targetExponent_coe hn, lt_div_iff₀ hden]
    nlinarith
  refine ⟨by exact_mod_cast hq, ?_⟩
  simp only [Morrey.exponent, ENNReal.coe_toReal, targetExponent_coe hn, Nat.cast_add,
    Nat.cast_one]
  field_simp
  <;> ring

end ExpandedFA.Sobolev.Higher

namespace ExpandedFA.Sobolev.Higher
open ExpandedFA.Distributions

lemma euclideanNorm_single {d : ℕ} (i : Fin d) (r : ℝ) :
    Morrey.euclideanNorm (Pi.single i r) = |r| := by
  change ‖PiLp.single (β := fun _ : Fin d => ℝ) 2 i r‖ = |r|
  rw [PiLp.norm_single]
  exact Real.norm_eq_abs r

lemma logarithmicProfile_not_memLp_top (d : ℕ) (hd : 0 < d)
    (a : ℝ) (ha : 0 < a) :
    ¬ MemLp (logarithmicProfile (d := d) a) ∞
      (volume.restrict (logarithmicDomain d : Set (Domain d))) := by
  intro h
  have htop : eLpNormEssSup (logarithmicProfile (d := d) a)
      (volume.restrict (logarithmicDomain d : Set (Domain d))) < ⊤ := by
    simpa only [MemLp, eLpNorm_exponent_top h.aestronglyMeasurable] using h
  obtain ⟨C, hC⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp htop
  have hC' : ∀ᵐ x ∂volume, x ∈ (logarithmicDomain d : Set (Domain d)) →
      ‖logarithmicProfile a x‖ ≤ (C : ℝ) := by
    apply (ae_restrict_iff' (logarithmicDomain d).isOpen.measurableSet).mp
    exact hC.mono fun x hx => by exact_mod_cast hx
  let R : ℝ := max 1 (((C : ℝ) + 1) ^ a⁻¹) + 1
  have hR1 : 1 < R := by dsimp [R]; linarith [le_max_left (1 : ℝ) (((C : ℝ) + 1) ^ a⁻¹)]
  have hR0 : 0 ≤ R := le_of_lt (lt_trans zero_lt_one hR1)
  have hRC : (C : ℝ) < R ^ a := by
    have hbase : ((C : ℝ) + 1) ^ a⁻¹ < R := by
      dsimp [R]
      linarith [le_max_right (1 : ℝ) (((C : ℝ) + 1) ^ a⁻¹)]
    have ht := Real.rpow_lt_rpow (Real.rpow_nonneg (by positivity) _) hbase ha
    rw [Real.rpow_inv_rpow (by positivity) (ne_of_gt ha)] at ht
    linarith
  let S : Set (Domain d) := {x | 0 < Morrey.euclideanNorm x ∧
      Morrey.euclideanNorm x < Real.exp (-R)}
  have hc : Continuous (@Morrey.euclideanNorm d) :=
    continuous_norm.comp (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))
  have hSopen : IsOpen S :=
    (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
  have hSnonempty : S.Nonempty := by
    refine ⟨Pi.single ⟨0, hd⟩ (Real.exp (-R) / 2), ?_⟩
    dsimp [S]
    rw [euclideanNorm_single, abs_of_pos (by positivity)]
    constructor <;> nlinarith [Real.exp_pos (-R)]
  have hsmall : Real.exp (-R) < Real.exp (-1) := by
    exact Real.exp_lt_exp.mpr (by linarith)
  have hSbound : ∀ x ∈ S, (C : ℝ) < ‖logarithmicProfile a x‖ := by
    intro x hx
    have hx0 : x ≠ 0 := by
      intro hxzero
      have hxn := hx.1
      simp [hxzero, Morrey.euclideanNorm] at hxn
    have hlog : R < Real.log (1 / Morrey.euclideanNorm x) := by
      have ht := Real.log_lt_log hx.1 hx.2
      rw [Real.log_exp] at ht
      rw [one_div, Real.log_inv]
      linarith
    calc
      (C : ℝ) < R ^ a := hRC
      _ < (Real.log (1 / Morrey.euclideanNorm x)) ^ a :=
        Real.rpow_lt_rpow hR0 hlog ha
      _ ≤ ‖logarithmicProfile a x‖ := by
        rw [logarithmicProfile, if_neg hx0, Real.norm_eq_abs]
        exact le_abs_self _
  apply hSopen.measure_ne_zero volume hSnonempty
  apply measure_mono_null (s := S) (t := {x | ¬(x ∈
    (logarithmicDomain d : Set (Domain d)) →
    ‖logarithmicProfile a x‖ ≤ (C : ℝ))}) ?_ (ae_iff.mp hC')
  intro x hx hxb
  exact not_le_of_gt (hSbound x hx) (hxb (lt_trans hx.2 hsmall))

end ExpandedFA.Sobolev.Higher

namespace ExpandedFA.Sobolev.Higher
open scoped ContDiff
open ExpandedFA.Distributions
open SmoothApproximateIdentitiesSpec
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Interior mollification converges locally uniformly to any continuous
representative, with no finiteness assumption on the Sobolev exponent. -/
theorem regularize_tendstoUniformlyOn_continuous_rep
    (ρ : Domain d → ℝ) (hρ : IsMollifier ρ)
    (u : DomainLp 𝕜 Ω p) (f : Domain d → 𝕜) (hf : Continuous f)
    (hrep : u =ᵐ[volume.restrict (Ω : Set (Domain d))] f)
    {K : Set (Domain d)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    TendstoUniformlyOn (fun ε => Smoothing.regularize ρ ε u) f (𝓝[>] (0 : ℝ)) K := by
  let g : Domain d → 𝕜 := (Ω : Set (Domain d)).indicator f
  have hug : Smoothing.zeroExtend u =ᵐ[volume] g := by
    have hrep' := (ae_restrict_iff' Ω.isOpen.measurableSet).mp hrep
    filter_upwards [hrep'] with x hx
    by_cases hΩ : x ∈ Ω
    · simp only [Smoothing.zeroExtend, g, indicator_of_mem hΩ, hx hΩ]
    · simp only [Smoothing.zeroExtend, g, indicator_of_notMem hΩ]
  have hgmeas : AEStronglyMeasurable g volume :=
    hf.aestronglyMeasurable.indicator Ω.isOpen.measurableSet
  have hgcont : ∀ x ∈ K, ContinuousAt g x := by
    intro x hx
    apply hf.continuousAt.congr
    filter_upwards [Ω.isOpen.mem_nhds (hKΩ hx)] with y hy
    exact (indicator_of_mem hy f).symm
  have hgu : TendstoUniformlyOn (fun ε => MollifyValue ρ ε g) g (𝓝[>] (0 : ℝ)) K := by
    apply ExpandedFA.Distributions.mollify_uniformlyOn_of_translation_control
      ρ hρ g hgmeas K
    intro η hη
    have hu := hK.uniformContinuousAt_of_continuousAt g hgcont (Metric.dist_mem_uniformity hη)
    obtain ⟨r, hr, hmod⟩ := Metric.mem_uniformity_dist.mp hu
    exact ⟨r, hr, fun x hx y hy => (by simpa only [dist_comm] using
      (hmod (by simpa only [mem_ball, dist_comm] using hy) hx).le)⟩
  have hconv : ∀ ε, Smoothing.regularize ρ ε u = MollifyValue ρ ε g := by
    intro ε
    exact convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) Filter.EventuallyEq.rfl hug
  have hgu' := hgu.congr_right (fun x hx => indicator_of_mem (hKΩ hx) f)
  exact hgu'.congr (Filter.Eventually.of_forall (fun ε x _ => congrFun (hconv ε).symm x))

/-- Reconstruction of a differential from its coordinate values. -/
def coordinateDifferential (v : Fin d → 𝕜) : Domain d →L[ℝ] 𝕜 :=
  ∑ i, (ContinuousLinearMap.proj i : Domain d →L[ℝ] ℝ).smulRight (v i)

lemma coordinateDifferential_apply (v : Fin d → 𝕜) (x : Domain d) :
    coordinateDifferential v x = ∑ i, x i • v i := by
  simp [coordinateDifferential]

lemma coordinateDifferential_coordinates (L : Domain d →L[ℝ] 𝕜) :
    coordinateDifferential (fun i => L (coordinateVector i)) = L := by
  classical
  ext x
  rw [coordinateDifferential_apply]
  have heq : x = ∑ i : Fin d, x i • coordinateVector i := by
    ext j
    simp [coordinateVector, Pi.single_apply, Finset.sum_apply]
  conv_rhs => rw [heq, map_sum]
  simp

lemma tendstoUniformlyOn_sum {ι X E : Type*} [NormedAddCommGroup E]
    {l : Filter ι} {s : Set X} {n : ℕ}
    {f : Fin n → ι → X → E} {g : Fin n → X → E}
    (h : ∀ i, TendstoUniformlyOn (f i) (g i) l s) :
    TendstoUniformlyOn (fun a x => ∑ i, f i a x) (fun x => ∑ i, g i x) l s := by
  classical
  have hfin : ∀ t : Finset (Fin n),
      TendstoUniformlyOn (fun a x => ∑ i ∈ t, f i a x) (fun x => ∑ i ∈ t, g i x) l s := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using (tendsto_const_nhds.tendstoUniformlyOn_const s : TendstoUniformlyOn (fun _ _ => (0 : E)) (fun _ => 0) l s)
    | @insert i t hi ih =>
      simp only [Finset.sum_insert hi]
      convert (h i).add ih using 1
  simpa using hfin Finset.univ

lemma tendstoUniformlyOn_coordinateDifferential {ι X : Type*}
    {l : Filter ι} {s : Set X} {f : ι → X → Fin d → 𝕜} {g : X → Fin d → 𝕜}
    (h : ∀ i, TendstoUniformlyOn (fun a x => f a x i) (fun x => g x i) l s) :
    TendstoUniformlyOn (fun a x => coordinateDifferential (f a x))
      (fun x => coordinateDifferential (g x)) l s := by
  apply tendstoUniformlyOn_sum
  intro i
  exact (ContinuousLinearMap.smulRightL ℝ (Domain d) 𝕜 (ContinuousLinearMap.proj i)).uniformContinuous.comp_tendstoUniformlyOn (h i)

def coordinateIndex (i : Fin d) : DerivativeIndex d 1 :=
  boundedIndex (Pi.single i 1) (by simp)

@[simp] lemma classicalDerivative_coordinateIndex (i : Fin d) (f : Domain d → 𝕜) :
    Smoothing.classicalDerivative (coordinateIndex i) f =
      fun x => fderiv ℝ f x (coordinateVector i) := by
  simp [coordinateIndex, Smoothing.classicalDerivative,
    natIndex_boundedIndex, Lines.multiIndexWord_single, partialFunction]

/-- A continuous Sobolev function whose first weak derivatives have continuous
representatives is classically differentiable, with precisely that gradient. -/
theorem hasFDerivAt_of_continuous_weak_derivatives
    (u : SpaceValue 𝕜 d Ω 1 p) (f : Domain d → 𝕜) (g : Fin d → Domain d → 𝕜)
    (hf : Continuous f) (hg : ∀ i, Continuous (g i))
    (hrep : u.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))] f)
    (hgrep : ∀ i, u.val (coordinateIndex i) =ᵐ[volume.restrict (Ω : Set (Domain d))] g i)
    {x : Domain d} (hx : x ∈ Ω) :
    HasFDerivAt f (coordinateDifferential (fun i => g i x)) x := by
  obtain ⟨ρ,hρ⟩ := Smoothing.exists_mollifier d
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (Ω.isOpen.mem_nhds hx)
  let K : Set (Domain d) := closedBall x (r/2)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKΩ : K ⊆ Ω := (closedBall_subset_ball (half_lt_self hr)).trans hball
  have hKnhds : K ∈ 𝓝 x := closedBall_mem_nhds _ (half_pos hr)
  let v := fun ε => Smoothing.regularize ρ ε (u.val (zeroIndex d 1))
  let v' := fun ε y => coordinateDifferential (fun i => Smoothing.regularize ρ ε (u.val (coordinateIndex i)) y)
  have hv : TendstoUniformlyOn v f (𝓝[>] (0 : ℝ)) K :=
    regularize_tendstoUniformlyOn_continuous_rep ρ hρ _ f hf hrep hK hKΩ
  have hv' : TendstoUniformlyOn v' (fun y => coordinateDifferential (fun i => g i y))
      (𝓝[>] (0 : ℝ)) K :=
    tendstoUniformlyOn_coordinateDifferential (fun i =>
      regularize_tendstoUniformlyOn_continuous_rep ρ hρ _ (g i) (hg i) (hgrep i) hK hKΩ)
  apply hasFDerivAt_of_tendstoUniformlyOnFilter (f := v) (g := f)
    (hv'.tendstoUniformlyOnFilter.mono_right (le_principal_iff.mpr hKnhds))
  · have hid := Smoothing.interior_derivative_identity 𝕜 d Ω 1 p ρ hρ u K hK hKΩ
    have hpair : ∀ᶠ q : ℝ × Domain d in (𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x,
        0 < q.1 ∧ (∀ α : DerivativeIndex d 1, ∀ y ∈ K,
          Smoothing.classicalDerivative α (v q.1) y =
            Smoothing.regularize ρ q.1 (u.val α) y) ∧ q.2 ∈ K := by
      simpa only [and_assoc] using ((show ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε from self_mem_nhdsWithin).and hid).prod_mk (show ∀ᶠ y in 𝓝 x, y ∈ K from hKnhds)
    filter_upwards [hpair] with q hq
    have hvdiff := (Smoothing.regularize_contDiff ρ hρ hq.1 (u.val (zeroIndex d 1))).differentiable (by simp)
    have heq : fderiv ℝ (v q.1) q.2 = v' q.1 q.2 := by
      rw [← coordinateDifferential_coordinates (fderiv ℝ (v q.1) q.2)]
      congr 1
      funext i
      simpa using hq.2.1 (coordinateIndex i) q.2 hq.2.2
    rw [← heq]
    exact (hvdiff q.2).hasFDerivAt
  · filter_upwards [show ∀ᶠ y in 𝓝 x, y ∈ K from hKnhds] with y hy
    exact hv.tendsto_at hy

/-- Include one further coordinate differentiation in the finite jet. -/
def addCoordinateIndex {k : ℕ} (α : DerivativeIndex d k) (i : Fin d)
    (h : (∑ j, natIndex α j) + 1 ≤ k) : DerivativeIndex d k :=
  boundedIndex (natIndex α + Pi.single i 1) (by simpa [Finset.sum_add_distrib] using h)

@[simp] lemma natIndex_addCoordinateIndex {k : ℕ} (α : DerivativeIndex d k) (i : Fin d)
    (h : (∑ j, natIndex α j) + 1 ≤ k) :
    natIndex (addCoordinateIndex α i h) = natIndex α + Pi.single i 1 := rfl

lemma derivativeReduction_coordinate_zero {k : ℕ} (α : DerivativeIndex d k)
    (h : (∑ j, natIndex α j) + 1 ≤ k) :
    shiftIndex (natIndex α) h (zeroIndex d 1) = α := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  simp [shiftIndex, natIndex, zeroIndex]

lemma derivativeReduction_coordinate_add {k : ℕ} (α : DerivativeIndex d k)
    (h : (∑ j, natIndex α j) + 1 ≤ k) (i : Fin d) :
    shiftIndex (natIndex α) h (coordinateIndex i) = addCoordinateIndex α i h := by
  apply Subtype.ext
  funext j
  apply Fin.ext
  rfl

/-- Every continuous weak-jet component differentiates to the next component. -/
theorem continuousJet_hasFDerivAt {k : ℕ} (u : SpaceValue 𝕜 d Ω k p)
    (F : DerivativeIndex d k → Domain d → 𝕜) (hF : ∀ α, Continuous (F α))
    (hrep : ∀ α, u.val α =ᵐ[volume.restrict (Ω : Set (Domain d))] F α)
    (α : DerivativeIndex d k) (hα : (∑ j, natIndex α j) + 1 ≤ k)
    {x : Domain d} (hx : x ∈ Ω) :
    HasFDerivAt (F α) (coordinateDifferential (fun i => F (addCoordinateIndex α i hα) x)) x := by
  apply hasFDerivAt_of_continuous_weak_derivatives
    (derivativeReduction (natIndex α) hα u) (F α)
    (fun i => F (addCoordinateIndex α i hα)) (hF α) (fun i => hF _)
  · simpa [derivativeReduction, derivativeReduction_coordinate_zero] using hrep α
  · intro i
    simpa [derivativeReduction, derivativeReduction_coordinate_add] using hrep (addCoordinateIndex α i hα)
  · exact hx

lemma contDiffOn_coordinateDifferential {n : ℕ∞ω} {s : Set (Domain d)}
    {g : Fin d → Domain d → 𝕜} (hg : ∀ i, ContDiffOn ℝ n (g i) s) :
    ContDiffOn ℝ n (fun x => coordinateDifferential (fun i => g i x)) s := by
  apply ContDiffOn.sum
  intro i _
  exact (ContinuousLinearMap.smulRightL ℝ (Domain d) 𝕜 (ContinuousLinearMap.proj i)).contDiff.comp_contDiffOn (hg i)

/-- A continuous compatible weak jet is a common classical Cᵏ jet. -/
theorem continuousJet_contDiffOn {k : ℕ} (u : SpaceValue 𝕜 d Ω k p)
    (F : DerivativeIndex d k → Domain d → 𝕜) (hF : ∀ α, Continuous (F α))
    (hrep : ∀ α, u.val α =ᵐ[volume.restrict (Ω : Set (Domain d))] F α)
    (n : ℕ) (α : DerivativeIndex d k) (hα : (∑ j, natIndex α j) + n ≤ k) :
    ContDiffOn ℝ n (F α) Ω := by
  induction n generalizing α with
  | zero => exact contDiffOn_zero.mpr (hF α).continuousOn
  | succ n ih =>
    have hα' : (∑ j, natIndex α j) + 1 ≤ k := by omega
    have hd := fun (x : Domain d) (hx : x ∈ Ω) => continuousJet_hasFDerivAt u F hF hrep α hα' hx
    have hgradient : ContDiffOn ℝ n
        (fun x => coordinateDifferential (fun i => F (addCoordinateIndex α i hα') x)) Ω := by
      apply contDiffOn_coordinateDifferential
      intro i
      apply ih
      simpa [natIndex_addCoordinateIndex, Pi.add_apply, Finset.sum_add_distrib,
        add_assoc, add_comm, add_left_comm] using hα
    rw [show ((n+1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by rfl,
      contDiffOn_succ_iff_fderiv_of_isOpen Ω.isOpen]
    refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact hgradient.congr (fun x hx => (hd x hx).fderiv)

@[simp] lemma coordinateDifferential_coordinateVector (v : Fin d → 𝕜) (i : Fin d) :
    coordinateDifferential v (coordinateVector i) = v i := by
  classical
  simp [coordinateDifferential_apply, coordinateVector, Pi.single_apply]

lemma wordIndex_nil {k : ℕ} (h : [].length ≤ k) :
    Smoothing.wordIndex ([] : List (Fin d)) h = zeroIndex d k := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  rfl

lemma addCoordinateIndex_wordIndex {k : ℕ} (w : List (Fin d)) (i : Fin d)
    (hw : w.length ≤ k)
    (h : (∑ j, natIndex (Smoothing.wordIndex w hw) j) + 1 ≤ k) :
    addCoordinateIndex (Smoothing.wordIndex w hw) i h =
      Smoothing.wordIndex (i :: w) (by simpa [Smoothing.wordIndex, Smoothing.word_count_sum] using h) := by
  classical
  apply Subtype.ext
  funext j
  apply Fin.ext
  change w.count j + (Pi.single i 1 : Fin d → ℕ) j = (i :: w).count j
  by_cases hij : i = j
  · subst j; simp
  · simp [hij, Ne.symm hij]

/-- Ordered classical partials of the base representative coincide with the
same continuous weak jet; thus there is no independent choice of Cᵏ function. -/
theorem continuousJet_partialFunction {k : ℕ} (u : SpaceValue 𝕜 d Ω k p)
    (F : DerivativeIndex d k → Domain d → 𝕜) (hF : ∀ α, Continuous (F α))
    (hrep : ∀ α, u.val α =ᵐ[volume.restrict (Ω : Set (Domain d))] F α)
    (w : List (Fin d)) (hw : w.length ≤ k) :
    EqOn (partialFunction w (F (zeroIndex d k))) (F (Smoothing.wordIndex w hw)) Ω := by
  induction w with
  | nil =>
    intro x hx
    simp [partialFunction, wordIndex_nil]
  | cons i w ih =>
    have hw' : w.length ≤ k := by simpa only [List.length_cons] using (Nat.le_trans (Nat.le_succ w.length) hw)
    have hα : (∑ j, natIndex (Smoothing.wordIndex w hw') j) + 1 ≤ k := by
      simpa [Smoothing.wordIndex, Smoothing.word_count_sum] using hw
    intro x hx
    have heq : partialFunction w (F (zeroIndex d k)) =ᶠ[𝓝 x] F (Smoothing.wordIndex w hw') := by
      filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
      exact ih hw' hy
    change fderiv ℝ (partialFunction w (F (zeroIndex d k))) x (coordinateVector i) = _
    rw [heq.fderiv_eq]
    rw [(continuousJet_hasFDerivAt u F hF hrep _ hα hx).fderiv]
    rw [coordinateDifferential_coordinateVector]
    congr 1
    exact addCoordinateIndex_wordIndex w i hw' hα

theorem continuousJet_classicalDerivative {k : ℕ} (u : SpaceValue 𝕜 d Ω k p)
    (F : DerivativeIndex d k → Domain d → 𝕜) (hF : ∀ α, Continuous (F α))
    (hrep : ∀ α, u.val α =ᵐ[volume.restrict (Ω : Set (Domain d))] F α)
    (α : DerivativeIndex d k) :
    EqOn (F α) (Smoothing.classicalDerivative α (F (zeroIndex d k))) Ω := by
  have hw : (multiIndexWord (natIndex α)).reverse.length ≤ k := by simpa [natIndex] using α.property
  have hidx : Smoothing.wordIndex (multiIndexWord (natIndex α)).reverse hw = α := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    change (multiIndexWord (natIndex α)).reverse.count i = natIndex α i
    simp
  have heq := continuousJet_partialFunction u F hF hrep _ hw
  rw [hidx] at heq
  exact heq.symm

theorem continuousJet_compatibility {k : ℕ} (u : SpaceValue 𝕜 d Ω k p)
    (F : DerivativeIndex d k → Domain d → 𝕜) (hF : ∀ α, Continuous (F α))
    (hrep : ∀ α, u.val α =ᵐ[volume.restrict (Ω : Set (Domain d))] F α) :
    ContDiffOn ℝ k (F (zeroIndex d k)) Ω ∧
    ∀ α, EqOn (F α) (Smoothing.classicalDerivative α (F (zeroIndex d k))) Ω := by
  constructor
  · exact continuousJet_contDiffOn u F hF hrep k (zeroIndex d k) (by simp [natIndex, zeroIndex])
  · exact continuousJet_classicalDerivative u F hF hrep

/-- Compatibility for a lower-order jet extracted from a higher Sobolev class. -/
theorem continuousJet_compatibility_of_order_le {m k : ℕ}
    (u : SpaceValue 𝕜 d Ω m p) (hk : k ≤ m)
    (F : DerivativeIndex d k → Domain d → 𝕜) (hF : ∀ α, Continuous (F α))
    (hrep : ∀ α, u.val (orderIndex hk α) =ᵐ[volume.restrict (Ω : Set (Domain d))] F α) :
    ContDiffOn ℝ k (F (zeroIndex d k)) Ω ∧
    ∀ α, EqOn (F α) (Smoothing.classicalDerivative α (F (zeroIndex d k))) Ω := by
  let v : SpaceValue 𝕜 d Ω k p := derivativeReduction 0 (by simpa using hk) u
  apply continuousJet_compatibility v F hF
  intro α
  exact hrep α

/-- Continuous representatives with the uniform estimates form the genuine
common classical Hölder jet required by the embedding statement. -/
theorem holderJet_of_continuous_representatives {m k : ℕ}
    (u : SpaceValue 𝕜 d Ω m p) (hk : k ≤ m) (a C : ℝ)
    (F : DerivativeIndex d k → Domain d → 𝕜) (hF : ∀ β, Continuous (F β))
    (hrep : ∀ β, u.val (orderIndex hk β) =ᵐ[volume.restrict (Ω : Set (Domain d))] F β)
    (hsup : ∀ β, ∀ x ∈ closure (Ω : Set (Domain d)), ‖F β x‖ ≤ C * ‖u‖)
    (hholder : ∀ β, (∑ i, natIndex β i) = k →
      ∀ x ∈ closure (Ω : Set (Domain d)), ∀ y ∈ closure (Ω : Set (Domain d)),
        ‖F β x - F β y‖ ≤ C * ‖u‖ * Morrey.euclideanNorm (x - y) ^ a) :
    HolderJet u k hk a C := by
  have hc := continuousJet_compatibility_of_order_le u hk F hF hrep
  exact ⟨F, hc.1, fun β => (hF β).continuousOn, hrep, hc.2, hsup, hholder⟩

end ExpandedFA.Sobolev.Higher

namespace ExpandedFA.Sobolev.Higher
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem wholeSpace_full_morrey (hdp : (d : ℝ≥0∞) < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SpaceValue 𝕜 d ⊤ 1 p,
      ∃ f : Domain d → 𝕜, Continuous f ∧ Morrey.Represents u f ∧
        (∀ x, ‖f x‖ ≤ C * ‖u‖) ∧
        ∀ x y, ‖f x - f y‖ ≤ C * ‖u‖ *
          Morrey.euclideanNorm (x-y) ^ Morrey.exponent d p := by
  obtain ⟨B, hB, hMor⟩ := Morrey.whole_space 𝕜 d p hdp
  obtain ⟨ρ, hρ⟩ := Smoothing.exists_mollifier d
  obtain ⟨R, hR, hRs⟩ := hρ.2.1.isBounded.subset_ball_lt 0 (0 : Domain d)
  let N : ℝ := Fintype.card (Morrey.GradientIndex d)
  let A : ℝ := (eLpNorm (SmoothApproximateIdentitiesSpec.ScaledKernelValue ρ 1)
    p.conjExponent volume).toReal
  let H : ℝ := B * N
  let C : ℝ := A + H * ((d : ℝ) * R) ^ Morrey.exponent d p + H
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hH : 0 ≤ H := mul_nonneg hB hN
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hHC : H ≤ C := by dsimp [C]; nlinarith [Real.rpow_nonneg ((mul_nonneg (Nat.cast_nonneg d) hR.le)) (Morrey.exponent d p)]
  have ha : 0 < Morrey.exponent d p := Morrey.exponent_pos hdp
  refine ⟨C, hC, fun u => ?_⟩
  obtain ⟨f, hf, hrep, hb⟩ := hMor u
  have hfull (x y : Domain d) : ‖f x - f y‖ ≤ H * ‖u‖ *
      Morrey.euclideanNorm (x-y) ^ Morrey.exponent d p := by
    exact (hb x y).trans (by
      dsimp [H]
      calc
        _ ≤ B * (N * ‖u‖) * Morrey.euclideanNorm (x-y) ^ Morrey.exponent d p := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (Morrey.gradientNorm_le u) hB)
            (Real.rpow_nonneg (norm_nonneg _) _)
        _ = _ := by change _ = B * N * ‖u‖ * _; ring)
  have hdisp (x : Domain d) : ‖convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) volume x - f x‖ ≤
      H * ‖u‖ * ((d : ℝ) * R) ^ Morrey.exponent d p := by
    rw [← dist_eq_norm]
    apply dist_convolution_le (by positivity) ((subset_tsupport ρ).trans hRs)
      hρ.2.2.1 hρ.2.2.2 hf.aestronglyMeasurable
    intro y hy
    rw [dist_eq_norm]
    apply (hfull y x).trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hH (norm_nonneg _))
    apply Real.rpow_le_rpow (norm_nonneg _) _ ha.le
    exact (Morrey.euclideanNorm_le _).trans (mul_le_mul_of_nonneg_left
      (show ‖y-x‖ ≤ R by simpa [dist_eq_norm] using (Metric.mem_ball.mp hy).le)
      (Nat.cast_nonneg _))
  have heq (x : Domain d) : convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) volume x =
      Smoothing.regularize ρ 1 (u.val (zeroIndex d 1)) x := by
    have hae : Smoothing.zeroExtend (u.val (zeroIndex d 1)) =ᵐ[volume] f := by
      simpa only [Smoothing.zeroExtend, Opens.coe_top, Set.indicator_univ,
        Morrey.Represents, Measure.restrict_univ] using hrep
    have hk : SmoothApproximateIdentitiesSpec.ScaledKernelValue ρ 1 = ρ := by
      funext z
      change ((1 : ℝ) ^ d)⁻¹ * ρ ((1 : ℝ)⁻¹ • z) = ρ z
      simp
    change convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) volume x =
      convolution (SmoothApproximateIdentitiesSpec.ScaledKernelValue ρ 1)
        (Smoothing.zeroExtend (u.val (zeroIndex d 1))) (ContinuousLinearMap.lsmul ℝ ℝ) volume x
    rw [hk]
    exact congrFun (convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ)
      (Filter.EventuallyEq.rfl : ρ =ᵐ[volume] ρ) hae.symm) x
  refine ⟨f, hf, hrep, ?_, fun x y => (hfull x y).trans ?_⟩
  · intro x
    calc
      ‖f x‖ ≤ ‖f x - convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ +
          ‖convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ := norm_le_norm_sub_add _ _
      _ ≤ H * ‖u‖ * ((d : ℝ) * R) ^ Morrey.exponent d p + A * ‖u.val (zeroIndex d 1)‖ := by
        apply add_le_add
        · rw [norm_sub_rev]; exact hdisp x
        · rw [heq x]; exact Morrey.regularize_norm_le_lp ρ hρ (by norm_num) _ x
      _ ≤ H * ‖u‖ * ((d : ℝ) * R) ^ Morrey.exponent d p + A * ‖u‖ := by
        gcongr
        exact PiLp.norm_apply_le u.val _
      _ = (A + H * ((d : ℝ) * R) ^ Morrey.exponent d p) * ‖u‖ := by
        change H * ‖u‖ * _ + A * ‖u‖ = _
        ring
      _ ≤ C * ‖u‖ := mul_le_mul_of_nonneg_right
        (by dsimp [C]; linarith) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hHC (norm_nonneg _))
      (Real.rpow_nonneg (norm_nonneg _) _)

/-- Uniform supremum and Morrey bounds from a first-order extension. -/
theorem firstOrder_full_morrey (hΩ : FirstOrderExtensionDomain 𝕜 Ω)
    (hdp : (d : ℝ≥0∞) < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SpaceValue 𝕜 d Ω 1 p,
      ∃ f : Domain d → 𝕜, Continuous f ∧ Morrey.Represents u f ∧
        (∀ x ∈ closure (Ω : Set (Domain d)), ‖f x‖ ≤ C * ‖u‖) ∧
        ∀ x ∈ closure (Ω : Set (Domain d)), ∀ y ∈ closure (Ω : Set (Domain d)),
          ‖f x - f y‖ ≤ C * ‖u‖ *
            Morrey.euclideanNorm (x-y) ^ Morrey.exponent d p := by
  obtain ⟨E, hE⟩ := hΩ p
  obtain ⟨C, hC, H⟩ := wholeSpace_full_morrey (𝕜 := 𝕜) hdp
  refine ⟨C * ‖E‖, mul_nonneg hC (norm_nonneg E), fun u => ?_⟩
  obtain ⟨f, hf, hrep, hsup, hhold⟩ := H (E u)
  have hrep' : (E u).val (zeroIndex d 1) =ᵐ[volume] f := by
    simpa only [Morrey.Represents, Opens.coe_top, Measure.restrict_univ] using hrep
  refine ⟨f, hf, (hE u).symm.trans (ae_restrict_of_ae hrep'), fun x _ => ?_,
    fun x _ y _ => ?_⟩
  · exact (hsup x).trans (by nlinarith [E.le_opNorm u])
  · exact (hhold x y).trans (mul_le_mul_of_nonneg_right
      (by nlinarith [E.le_opNorm u]) (Real.rpow_nonneg (norm_nonneg _) _))

/-- First-order supercritical integrability, including the essential supremum. -/
theorem firstOrder_infinity (hΩ : FirstOrderExtensionDomain 𝕜 Ω)
    (hdp : (d : ℝ≥0∞) < p) : LpInclusion 𝕜 Ω 1 p ∞ := by
  obtain ⟨C, hC, H⟩ := firstOrder_full_morrey (𝕜 := 𝕜) hΩ hdp
  refine ⟨C.toNNReal, fun u => ?_⟩
  obtain ⟨f, hf, hrep, hsup, _⟩ := H u
  have hbound : ∀ᵐ x ∂volume.restrict (Ω : Set (Domain d)), ‖u.val (zeroIndex d 1) x‖ ≤ C * ‖u‖ := by
    filter_upwards [hrep, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
    rw [hx]
    exact hsup x (subset_closure hxΩ)
  have hn := eLpNormEssSup_le_of_ae_bound hbound
  have htarget : eLpNorm (u.val (zeroIndex d 1)) ∞ (volume.restrict (Ω : Set (Domain d))) ≤
      ENNReal.ofReal (C * ‖u‖) := by
    simpa only [eLpNorm_exponent_top (Lp.memLp _).aestronglyMeasurable] using hn
  refine ⟨htarget.trans_lt ENNReal.ofReal_lt_top, ?_⟩
  change _ ≤ ENNReal.ofReal C * ENNReal.ofReal ‖u‖
  simpa only [ENNReal.ofReal_mul hC] using htarget

/-- A smaller positive Holder exponent follows globally from the supremum
bound and the stronger Holder estimate. -/
theorem lower_holder_exponent {s : Set (Domain d)} {f : Domain d → 𝕜}
    {K a b : ℝ} (hK : 0 ≤ K) (ha : 0 < a) (hab : a ≤ b)
    (hsup : ∀ x ∈ s, ‖f x‖ ≤ K)
    (hhold : ∀ x ∈ s, ∀ y ∈ s, ‖f x - f y‖ ≤ K * Morrey.euclideanNorm (x-y) ^ b) :
    ∀ x ∈ s, ∀ y ∈ s, ‖f x - f y‖ ≤ (2*K) * Morrey.euclideanNorm (x-y) ^ a := by
  intro x hx y hy
  by_cases hxy : Morrey.euclideanNorm (x-y) ≤ 1
  · apply (hhold x hx y hy).trans
    apply (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge'
      (norm_nonneg _) hxy ha.le hab) hK).trans
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) _)
  · have hp : 1 ≤ Morrey.euclideanNorm (x-y) ^ a :=
      Real.one_le_rpow (le_of_not_ge hxy) ha.le
    calc
      ‖f x - f y‖ ≤ ‖f x‖ + ‖f y‖ := norm_sub_le _ _
      _ ≤ 2*K := by linarith [hsup x hx, hsup y hy]
      _ ≤ (2*K) * Morrey.euclideanNorm (x-y) ^ a := le_mul_of_one_le_right (by positivity) hp

/-- One continuous representative with its full Holder norm controlled. -/
def FullHolder (𝕜 : Type) [RCLike 𝕜] {d : ℕ} (Ω : Opens (Domain d))
    (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SpaceValue 𝕜 d Ω m p,
    ∃ f : Domain d → 𝕜, Continuous f ∧
      (u.val (zeroIndex d m) =ᵐ[volume.restrict (Ω : Set (Domain d))] f) ∧
      (∀ x ∈ closure (Ω : Set (Domain d)), ‖f x‖ ≤ C * ‖u‖) ∧
      ∀ x ∈ closure (Ω : Set (Domain d)), ∀ y ∈ closure (Ω : Set (Domain d)),
        ‖f x-f y‖ ≤ C * ‖u‖ * Morrey.euclideanNorm (x-y) ^ a

/-- Apply the first-order Morrey estimate after gaining an exponent on all
components of the first derivative graph. -/
theorem fullHolder_of_lpInclusion {n : ℕ} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hΩ : FirstOrderExtensionDomain 𝕜 Ω) (hdq : (d : ℝ≥0∞) < q)
    (H : LpInclusion 𝕜 Ω n p q) :
    FullHolder 𝕜 Ω (1+n) p (Morrey.exponent d q) := by
  obtain ⟨A, hA⟩ := H
  obtain ⟨B, hB, hMor⟩ := firstOrder_full_morrey (𝕜 := 𝕜) hΩ hdq
  let K : ℝ := Fintype.card (DerivativeIndex d 1) * (A : ℝ)
  have hK : 0 ≤ K := mul_nonneg (Nat.cast_nonneg _) A.coe_nonneg
  refine ⟨B*K, mul_nonneg hB hK, fun u => ?_⟩
  obtain ⟨v, hv, hn⟩ := lp_gain_order (m := 1) (n := n) A hA u
  have hnR : ‖v‖ ≤ K * ‖u‖ := by
    have hh := ENNReal.toReal_mono (by finiteness) hn
    simpa only [ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_mul,
      ENNReal.coe_toReal, ENNReal.toReal_natCast, K] using hh
  obtain ⟨f, hf, hrep, hs, hh⟩ := hMor v
  have hzero := hv (zeroIndex d 1)
  simp only [orderIndex_zeroIndex] at hzero
  refine ⟨f, hf, hzero.symm.trans hrep, fun x hx => ?_, fun x hx y hy => ?_⟩
  · exact (hs x hx).trans (by
      calc B * ‖v‖ ≤ B * (K * ‖u‖) := mul_le_mul_of_nonneg_left hnR hB
           _ = (B*K) * ‖u‖ := (mul_assoc _ _ _).symm)
  · exact (hh x hx y hy).trans (mul_le_mul_of_nonneg_right
      (by calc B * ‖v‖ ≤ B * (K * ‖u‖) := mul_le_mul_of_nonneg_left hnR hB
               _ = (B*K) * ‖u‖ := (mul_assoc _ _ _).symm)
      (Real.rpow_nonneg (norm_nonneg _) _))

/-- Keep the same representative at a smaller positive Holder exponent. -/
theorem fullHolder_lower {m : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (H : FullHolder 𝕜 Ω m p b) :
    FullHolder 𝕜 Ω m p a := by
  obtain ⟨C, hC, H⟩ := H
  refine ⟨2*C, by positivity, fun u => ?_⟩
  obtain ⟨f, hf, hr, hs, hh⟩ := H u
  refine ⟨f, hf, hr, fun x hx => (hs x hx).trans ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  · simpa only [mul_assoc] using lower_holder_exponent (mul_nonneg hC (norm_nonneg u)) ha hab hs hh

/-- Apply any higher-order representative estimate to the actual component
of a larger Sobolev graph. -/
theorem derivative_fullHolder {m n : ℕ} (β : DerivativeIndex d m)
    (hβ : (∑ i, natIndex β i) + n ≤ m) {a : ℝ}
    (H : FullHolder 𝕜 Ω n p a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SpaceValue 𝕜 d Ω m p,
      ∃ f : Domain d → 𝕜, Continuous f ∧
        (u.val β =ᵐ[volume.restrict (Ω : Set (Domain d))] f) ∧
        (∀ x ∈ closure (Ω : Set (Domain d)), ‖f x‖ ≤ C * ‖u‖) ∧
        ∀ x ∈ closure (Ω : Set (Domain d)), ∀ y ∈ closure (Ω : Set (Domain d)),
          ‖f x-f y‖ ≤ C * ‖u‖ * Morrey.euclideanNorm (x-y) ^ a := by
  obtain ⟨C, hC, H⟩ := H
  refine ⟨C, hC, fun u => ?_⟩
  let v := derivativeReduction (natIndex β) hβ u
  obtain ⟨f, hf, hr, hs, hh⟩ := H v
  have hv : v.val (zeroIndex d n) = u.val β := by
    have hi : shiftIndex (natIndex β) hβ (zeroIndex d n) = β := by
      apply Subtype.ext
      funext i
      apply Fin.ext
      simp [shiftIndex, natIndex, zeroIndex]
    change u.val (shiftIndex (natIndex β) hβ (zeroIndex d n)) = u.val β
    rw [hi]
  refine ⟨f, hf, ?_, fun x hx => (hs x hx).trans ?_, fun x hx y hy => (hh x hx y hy).trans ?_⟩
  · simpa only [hv] using hr
  · exact mul_le_mul_of_nonneg_left (derivativeReduction_norm_le (natIndex β) hβ u) hC
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (derivativeReduction_norm_le (natIndex β) hβ u) hC)
      (Real.rpow_nonneg (norm_nonneg _) _)

/-- The exact endpoint exponent when the dimension-to-integrability ratio
lies strictly between n and n+1. -/
theorem fullHolder_subcritical_gap (hΩ : FirstOrderExtensionDomain 𝕜 Ω)
    (n : ℕ) (p : ℝ≥0) [Fact (1 ≤ (p : ℝ≥0∞))]
    (hp : 1 ≤ p) (hn : n*p < d) (hsuper : d < (n+1 : ℕ)*p) :
    FullHolder 𝕜 Ω (n+1) p (((n+1 : ℕ) : ℝ) - (d : ℝ) / p) := by
  obtain ⟨hq, heq⟩ := targetExponent_morrey hp hn hsuper
  have hd0 : 0 < d := by
    exact_mod_cast (lt_of_le_of_lt (show (0 : ℝ≥0) ≤ n*p from bot_le) hn)
  have hd1 : (1 : ℝ≥0) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hq1 : (1 : ℝ≥0) ≤ targetExponent d n p := hd1.trans hq.le
  letI : Fact (1 ≤ (targetExponent d n p : ℝ≥0∞)) := ⟨by exact_mod_cast hq1⟩
  have H := fullHolder_of_lpInclusion hΩ (by exact_mod_cast hq)
    (subcritical_extension_inclusion hΩ n p hp hn)
  rw [heq] at H
  simpa only [Nat.add_comm 1 n] using H

/-- A full Holder bound controls the essential supremum of its class. -/
theorem fullHolder_infinity {m : ℕ} {a : ℝ} (H : FullHolder 𝕜 Ω m p a) :
    LpInclusion 𝕜 Ω m p ∞ := by
  obtain ⟨C, hC, H⟩ := H
  refine ⟨C.toNNReal, fun u => ?_⟩
  obtain ⟨f, hf, hrep, hsup, _⟩ := H u
  have hbound : ∀ᵐ x ∂volume.restrict (Ω : Set (Domain d)),
      ‖u.val (zeroIndex d m) x‖ ≤ C * ‖u‖ := by
    filter_upwards [hrep, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
    rw [hx]
    exact hsup x (subset_closure hxΩ)
  have hn := eLpNormEssSup_le_of_ae_bound hbound
  have htarget : eLpNorm (u.val (zeroIndex d m)) ∞
      (volume.restrict (Ω : Set (Domain d))) ≤ ENNReal.ofReal (C * ‖u‖) := by
    simpa only [eLpNorm_exponent_top (Lp.memLp _).aestronglyMeasurable] using hn
  refine ⟨htarget.trans_lt ENNReal.ofReal_lt_top, ?_⟩
  change _ ≤ ENNReal.ofReal C * ENNReal.ofReal ‖u‖
  simpa only [ENNReal.ofReal_mul hC] using htarget

/-- One further Sobolev order after boundedness gives a Lipschitz
representative, by applying the accepted infinity Morrey endpoint. -/
theorem fullHolder_successor_lipschitz {m : ℕ} {a : ℝ}
    (hΩ : FirstOrderExtensionDomain 𝕜 Ω) (H : FullHolder 𝕜 Ω m p a) :
    FullHolder 𝕜 Ω (m+1) p 1 := by
  have H' := fullHolder_of_lpInclusion hΩ (ENNReal.natCast_lt_top d)
    (fullHolder_infinity H)
  simpa only [Morrey.exponent_top, Nat.add_comm 1 m] using H'
end ExpandedFA.Sobolev.Higher

namespace ExpandedFA.Sobolev.Higher
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]
/-- At a critical remaining order on a bounded extension domain, any
Holder exponent below one is obtained from a finite target exponent. -/
theorem fullHolder_critical_bounded (hΩb : Bornology.IsBounded (Ω : Set (Domain d)))
    (hΩ : FirstOrderExtensionDomain 𝕜 Ω) (n : ℕ) (p : ℝ≥0)
    [Fact (1 ≤ (p : ℝ≥0∞))] (hp : 1 ≤ p) (hn : n*p = d)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    FullHolder 𝕜 Ω (n+1) p a := by
  have hden : 0 < 1-a := sub_pos.mpr ha1
  let q : ℝ≥0 := ⟨((d : ℝ)+1)/(1-a), div_nonneg (by positivity) hden.le⟩
  have hqR : (q : ℝ) = ((d : ℝ)+1)/(1-a) := rfl
  have hq1R : (1 : ℝ) ≤ q := by
    rw [hqR, le_div_iff₀ hden]
    nlinarith [show (0 : ℝ) ≤ d from Nat.cast_nonneg d]
  have hq1 : (1 : ℝ≥0) ≤ q := by exact_mod_cast hq1R
  have hqdR : (d : ℝ) < q := by
    rw [hqR, lt_div_iff₀ hden]
    nlinarith [show (0 : ℝ) ≤ d from Nat.cast_nonneg d]
  have hqd : (d : ℝ≥0∞) < q := by exact_mod_cast hqdR
  letI : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hq1⟩
  have hα : a ≤ Morrey.exponent d q := by
    simp only [Morrey.exponent, ENNReal.coe_toReal]
    have hqpos : (0 : ℝ) < q := by linarith
    have hmul : (1-a) * (q : ℝ) = (d : ℝ)+1 := by
      rw [hqR]
      field_simp
    have hdq : (d : ℝ) / q ≤ 1-a :=
      (div_le_iff₀ hqpos).mpr (by nlinarith)
    linarith
  have H := fullHolder_of_lpInclusion hΩ hqd
    (critical_bounded_extension 𝕜 d n Ω hΩb hΩ p q hp hq1 hn)
  have H' := fullHolder_lower ha hα H
  simpa only [Nat.add_comm 1 n] using H'
end ExpandedFA.Sobolev.Higher

namespace ExpandedFA.Sobolev.Higher
open Real
/-- The exact scalar radial integral underlying the critical logarithmic gradient. -/
lemma integrableOn_inv_mul_log_inv_rpow {b : ℝ} (hb : b < -1) :
    IntegrableOn (fun r : ℝ => r⁻¹ * (Real.log (1 / r)) ^ b)
      (Ioo 0 (Real.exp (-1))) volume := by
  let f : ℝ → ℝ := (Ioi (1 : ℝ)).indicator (fun t => t ^ b)
  have hf : Integrable f volume :=
    (integrable_indicator_iff measurableSet_Ioi).mpr
      (integrableOn_Ioi_rpow_of_lt hb zero_lt_one)
  have hg : Integrable (fun t : ℝ => f (-t)) volume := hf.comp_neg
  have hlog : IntegrableOn (fun r : ℝ => r⁻¹ * f (-Real.log r)) (Ioi 0) volume := by
    simpa only [smul_eq_mul] using
      (integrableOn_comp_log_Ioi_zero (fun t : ℝ => f (-t))).mpr hg
  refine (hlog.mono_set Ioo_subset_Ioi_self).congr_fun ?_ measurableSet_Ioo
  intro r hr
  have hlt : Real.log r < -1 := (Real.log_lt_iff_lt_exp hr.1).mpr hr.2
  have hmem : -Real.log r ∈ Ioi (1 : ℝ) := by simpa using neg_lt_neg hlt
  dsimp only
  rw [show f (-Real.log r) = (-Real.log r) ^ b from indicator_of_mem hmem _]
  simp only [one_div, Real.log_inv]

/-- Polar integration at the critical power, for any finite dimensional norm. -/
lemma integrableOn_critical_log_gradient
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {b : ℝ} (hb : b < -1) :
    IntegrableOn (fun x : E => (‖x‖ ^ Module.finrank ℝ E)⁻¹ *
      (Real.log (1 / ‖x‖)) ^ b) (Metric.ball 0 (Real.exp (-1))) μ := by
  apply (integrableOn_fun_norm_addHaar μ (f := fun r : ℝ =>
    (r ^ Module.finrank ℝ E)⁻¹ * (Real.log (1 / r)) ^ b)).mpr
  refine (integrableOn_inv_mul_log_inv_rpow hb).congr_fun ?_ measurableSet_Ioo
  intro r hr
  dsimp only
  rw [smul_eq_mul]
  have hd : 1 ≤ Module.finrank ℝ E := Module.finrank_pos
  have hr0 : r ≠ 0 := hr.1.ne'
  have hp : r ^ (Module.finrank ℝ E - 1) * (r ^ Module.finrank ℝ E)⁻¹ = r⁻¹ := by
    have hdim : Module.finrank ℝ E = (Module.finrank ℝ E - 1) + 1 := by omega
    conv_lhs => arg 2; arg 1; rw [hdim, pow_succ]
    field_simp
  rw [← mul_assoc, hp]

lemma logarithmic_gradient_power_integrable (d : ℕ) (hd : 0 < d)
    {b : ℝ} (hb : b < -1) :
    IntegrableOn (fun x : ExpandedFA.Distributions.Domain d =>
      (Morrey.euclideanNorm x ^ d)⁻¹ * (Real.log (1 / Morrey.euclideanNorm x)) ^ b)
      (logarithmicDomain d : Set (ExpandedFA.Distributions.Domain d)) volume := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hi := integrableOn_critical_log_gradient
    (E := EuclideanSpace ℝ (Fin d)) volume hb
  simpa [Function.comp_def, Morrey.euclideanNorm, logarithmicDomain,
    Metric.ball, dist_eq_norm] using
      ((PiLp.volume_preserving_toLp (Fin d)).integrableOn_comp_preimage
        (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding).mpr hi

lemma logarithmic_gradient_model_memLp (d : ℕ) (hd : 0 < d) (a : ℝ)
    (ha : a < 1 - 1 / (d : ℝ)) :
    MemLp (fun x : ExpandedFA.Distributions.Domain d => (Morrey.euclideanNorm x)⁻¹ *
      (Real.log (1 / Morrey.euclideanNorm x)) ^ (a - 1)) d
      (volume.restrict (logarithmicDomain d : Set (ExpandedFA.Distributions.Domain d))) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hb : (a - 1) * (d : ℝ) < -1 := by
    have ht := mul_lt_mul_of_pos_right ha hdR
    have hc : (1 / (d : ℝ)) * (d : ℝ) = 1 := by field_simp
    nlinarith
  have hi := logarithmic_gradient_power_integrable d hd hb
  have hn : Measurable (@Morrey.euclideanNorm d) :=
    (continuous_norm.comp (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))).measurable
  have hm : Measurable (fun x : ExpandedFA.Distributions.Domain d =>
      (Morrey.euclideanNorm x)⁻¹ * (Real.log (1 / Morrey.euclideanNorm x)) ^ (a - 1)) := by
    fun_prop
  apply (integrable_norm_rpow_iff hm.aestronglyMeasurable.restrict
    (by exact_mod_cast hd.ne') (by simp)).mp
  refine hi.congr ?_
  filter_upwards [ae_restrict_mem (logarithmicDomain d).isOpen.measurableSet] with x hx
  have hr0 : 0 ≤ Morrey.euclideanNorm x := norm_nonneg _
  have hlog : 0 ≤ Real.log (1 / Morrey.euclideanNorm x) := by
    by_cases hz : Morrey.euclideanNorm x = 0
    · simp [hz]
    · have hrpos : 0 < Morrey.euclideanNorm x := lt_of_le_of_ne hr0 (Ne.symm hz)
      have hrlt : Morrey.euclideanNorm x < 1 :=
        lt_trans hx (by exact Real.exp_lt_one_iff.mpr (by norm_num))
      exact (Real.log_pos (one_lt_div hrpos |>.mpr hrlt)).le
  rw [ENNReal.toReal_natCast, Real.rpow_natCast, norm_mul, norm_inv,
    Real.norm_eq_abs, abs_of_nonneg hr0, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hlog _), mul_pow, inv_pow]
  rw [Real.rpow_mul hlog, Real.rpow_natCast]

lemma logarithmicProfile_memLp (d : ℕ) (hd : 0 < d) (a : ℝ)
    (ha : a < 1 - 1 / (d : ℝ)) :
    MemLp (logarithmicProfile (d := d) a) d
      (volume.restrict (logarithmicDomain d : Set (ExpandedFA.Distributions.Domain d))) := by
  have hn : Measurable (@Morrey.euclideanNorm d) :=
    (continuous_norm.comp (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))).measurable
  have hm : Measurable (logarithmicProfile (d := d) a) := by
    unfold logarithmicProfile
    exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)
  apply (logarithmic_gradient_model_memLp d hd a ha).mono hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (logarithmicDomain d).isOpen.measurableSet] with x hx
  by_cases hz : x = 0
  · simp [hz, logarithmicProfile, Morrey.euclideanNorm]
  have hrpos : 0 < Morrey.euclideanNorm x := by
    apply lt_of_le_of_ne (norm_nonneg _) (Ne.symm ?_)
    simpa [Morrey.euclideanNorm] using hz
  have hrlt : Morrey.euclideanNorm x < 1 :=
    lt_trans hx (by exact Real.exp_lt_one_iff.mpr (by norm_num))
  have hlog : 0 < Real.log (1 / Morrey.euclideanNorm x) :=
    Real.log_pos (one_lt_div hrpos |>.mpr hrlt)
  have hlogle : Real.log (1 / Morrey.euclideanNorm x) ≤ (Morrey.euclideanNorm x)⁻¹ := by
    have ht := Real.log_le_sub_one_of_pos (one_div_pos.mpr hrpos)
    simpa only [one_div] using ht.trans (sub_le_self _ zero_le_one)
  rw [logarithmicProfile, if_neg hz, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hlog.le _), Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hrpos.le) (Real.rpow_nonneg hlog.le _))]
  calc
    (Real.log (1 / Morrey.euclideanNorm x)) ^ a =
      (Real.log (1 / Morrey.euclideanNorm x)) ^ (a - 1) *
        Real.log (1 / Morrey.euclideanNorm x) := by
          conv_lhs => rw [show a = (a - 1) + 1 by ring, Real.rpow_add hlog, Real.rpow_one]
    _ ≤ (Real.log (1 / Morrey.euclideanNorm x)) ^ (a - 1) *
        (Morrey.euclideanNorm x)⁻¹ :=
      mul_le_mul_of_nonneg_left hlogle (Real.rpow_nonneg hlog.le _)
    _ = _ := mul_comm _ _

def logarithmicPartial {d : ℕ} (a : ℝ) (i : Fin d)
    (x : ExpandedFA.Distributions.Domain d) : ℝ :=
  -a * (x i / Morrey.euclideanNorm x) * ((Morrey.euclideanNorm x)⁻¹ *
      (Real.log (1 / Morrey.euclideanNorm x)) ^ (a - 1))

lemma logarithmicPartial_memLp (d : ℕ) (hd : 0 < d) (a : ℝ)
    (ha : a < 1 - 1 / (d : ℝ)) (i : Fin d) :
    MemLp (logarithmicPartial a i) d
      (volume.restrict (logarithmicDomain d : Set (ExpandedFA.Distributions.Domain d))) := by
  have hn : Measurable (@Morrey.euclideanNorm d) :=
    (continuous_norm.comp (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))).measurable
  have hm : Measurable (logarithmicPartial (d := d) a i) := by
    unfold logarithmicPartial
    fun_prop
  apply ((logarithmic_gradient_model_memLp d hd a ha).const_mul (-a)).mono hm.aestronglyMeasurable
  filter_upwards with x
  have hc : |x i| ≤ Morrey.euclideanNorm x := by
    exact PiLp.norm_apply_le (WithLp.toLp 2 x) i
  have hquot : |x i / Morrey.euclideanNorm x| ≤ 1 := by
    rw [abs_div, abs_of_nonneg (show 0 ≤ Morrey.euclideanNorm x from norm_nonneg _)]
    by_cases hz : Morrey.euclideanNorm x = 0
    · simp [hz]
    · exact (div_le_one (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz))).mpr hc
  have hcalc : |-a| * |x i / Morrey.euclideanNorm x| *
      |(Morrey.euclideanNorm x)⁻¹ * (Real.log (1 / Morrey.euclideanNorm x)) ^ (a - 1)| ≤
      |-a * ((Morrey.euclideanNorm x)⁻¹ *
        (Real.log (1 / Morrey.euclideanNorm x)) ^ (a - 1))| := by
    calc
      |-a| * |x i / Morrey.euclideanNorm x| *
          |(Morrey.euclideanNorm x)⁻¹ * (Real.log (1 / Morrey.euclideanNorm x)) ^ (a - 1)| ≤
        |-a| * 1 *
          |(Morrey.euclideanNorm x)⁻¹ * (Real.log (1 / Morrey.euclideanNorm x)) ^ (a - 1)| := by
            gcongr
      _ = _ := by simp [abs_mul]
  simpa only [logarithmicPartial, norm_mul, Real.norm_eq_abs, abs_mul] using hcalc

end ExpandedFA.Sobolev.Higher

namespace ExpandedFA.Sobolev.Higher
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A common bound for the remaining Sobolev order gives a genuine classical
jet, rather than unrelated representatives of its components. -/
theorem holderJet_of_fullHolder {m k n : ℕ} (hk : k ≤ m) (hkn : k+n ≤ m)
    {a : ℝ} (H : FullHolder 𝕜 Ω n p a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SpaceValue 𝕜 d Ω m p, HolderJet u k hk a C := by
  obtain ⟨C,hC,H⟩ := H
  refine ⟨C,hC,fun u => ?_⟩
  have hcomponents (β : DerivativeIndex d k) :
      ∃ f : Domain d → 𝕜, Continuous f ∧
        (u.val (orderIndex hk β) =ᵐ[volume.restrict (Ω : Set (Domain d))] f) ∧
        (∀ x ∈ closure (Ω : Set (Domain d)), ‖f x‖ ≤ C * ‖u‖) ∧
        ∀ x ∈ closure (Ω : Set (Domain d)), ∀ y ∈ closure (Ω : Set (Domain d)),
          ‖f x-f y‖ ≤ C * ‖u‖ * Morrey.euclideanNorm (x-y) ^ a := by
    have hβ : (∑ i, natIndex β i) + n ≤ m :=
      (Nat.add_le_add_right β.property n).trans hkn
    let v := derivativeReduction (natIndex β) hβ u
    obtain ⟨f,hf,hr,hs,hh⟩ := H v
    have hv : v.val (zeroIndex d n) = u.val (orderIndex hk β) := by
      change u.val (shiftIndex (natIndex β) hβ (zeroIndex d n)) = _
      have hi : shiftIndex (natIndex β) hβ (zeroIndex d n) = orderIndex hk β := by
        apply Subtype.ext
        funext i
        apply Fin.ext
        simp [shiftIndex, orderIndex, natIndex, zeroIndex]
      rw [hi]
    refine ⟨f,hf,?_,fun x hx => (hs x hx).trans ?_,fun x hx y hy => (hh x hx y hy).trans ?_⟩
    · simpa only [hv] using hr
    · exact mul_le_mul_of_nonneg_left (derivativeReduction_norm_le (natIndex β) hβ u) hC
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (derivativeReduction_norm_le (natIndex β) hβ u) hC)
        (Real.rpow_nonneg (norm_nonneg _) _)
  choose F hF hr hs hh using hcomponents
  exact holderJet_of_continuous_representatives u hk a C F hF hr hs (fun β _ => hh β)

/-- The exact nonintegral gap gives the full C^{k,a} jet on any first-order
extension domain. -/
theorem nonintegral_holder_extension (hΩ : FirstOrderExtensionDomain 𝕜 Ω)
    {m k : ℕ} {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hgap : (m : ℝ) - (d : ℝ) / p.toReal = k+a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ hk : k ≤ m,
      ∀ u : SpaceValue 𝕜 d Ω m p, HolderJet u k hk a C := by
  have hkR : (k : ℝ) < m := by
    have hdterm : 0 ≤ (d : ℝ)/p.toReal := div_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg
    linarith
  have hklt : k < m := by exact_mod_cast hkR
  have hk1 : (k : ℝ)+1 ≤ m := by exact_mod_cast (show k+1 ≤ m by omega)
  have hpTop : p ≠ ∞ := by
    intro hp
    simp only [hp, ENNReal.toReal_top, div_zero, sub_zero] at hgap
    linarith
  have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le Fact.out)
  have hpR0 : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
  have hp1 : 1 ≤ p.toNNReal := by
    apply ENNReal.coe_le_coe.mp
    simpa only [ENNReal.coe_one, ENNReal.coe_toNNReal hpTop] using (Fact.out : 1 ≤ p)
  let n : ℕ := m-k-1
  have hmn : k+(n+1) = m := by dsimp [n]; omega
  have hmnR : (m : ℝ) = (k : ℝ) + (n+1 : ℕ) := by exact_mod_cast hmn.symm
  have hgap' : ((n+1 : ℕ) : ℝ) - (d : ℝ) / p.toReal = a := by linarith
  have hnR : (n : ℝ)*p.toReal < d := by
    have hdiv : (n : ℝ) < (d : ℝ)/p.toReal := by push_cast at hgap'; linarith
    exact (lt_div_iff₀ hpR0).mp hdiv
  have hsR : (d : ℝ) < ((n+1 : ℕ) : ℝ)*p.toReal := by
    have hdiv : (d : ℝ)/p.toReal < ((n+1 : ℕ) : ℝ) := by linarith
    exact (div_lt_iff₀ hpR0).mp hdiv
  have hn : n*p.toNNReal < d := by exact_mod_cast hnR
  have hs : (d : ℝ≥0) < (n+1 : ℕ)*p.toNNReal := by exact_mod_cast hsR
  haveI : Fact (1 ≤ (p.toNNReal : ℝ≥0∞)) := ⟨by exact_mod_cast hp1⟩
  have H := fullHolder_subcritical_gap hΩ n p.toNNReal hp1 hn hs
  have hexp : (((n+1 : ℕ) : ℝ) - (d : ℝ) / (p.toNNReal : ℝ)) = a := by
    exact hgap'
  rw [hexp] at H
  have H' : FullHolder 𝕜 Ω (n+1) p a := by
    simpa only [ENNReal.coe_toNNReal hpTop] using H
  obtain ⟨C,hC,hjet⟩ := holderJet_of_fullHolder (Nat.le_of_lt hklt) hmn.le H'
  exact ⟨C,hC,Nat.le_of_lt hklt,hjet⟩

theorem nonintegral_holder :
    Specs.ExpandedFA.Sobolev.HigherSobolevEmbeddings.NonintegralHolder := by
  intro 𝕜 _ d m k Ω hΩ p _ a ha ha1 hgap
  apply nonintegral_holder_extension _ ha ha1 hgap
  rcases hΩ with rfl | ⟨_,hΩ⟩
  · exact wholeSpace_extension
  · exact hΩ

end ExpandedFA.Sobolev.Higher

namespace ExpandedFA.Sobolev.Higher
open ExpandedFA.Distributions Lines

lemma coordinateLine_ne_zero_of_ne_zero {d : ℕ} (i : Fin d)
    (y : Transverse i) (hy : y ≠ 0) (t : ℝ) : coordinateLine i y t ≠ 0 := by
  intro hz
  apply hy
  funext j
  have hj := congrFun hz j.val
  simpa [coordinateLine, j.property] using hj

lemma log_inv_eq_log_sq (r : ℝ) :
    Real.log (1 / r) = -(1 / 2 : ℝ) * Real.log (r ^ 2) := by
  rw [one_div, Real.log_inv, Real.log_pow]
  ring

lemma logarithmic_line_hasDerivAt {d : ℕ} (a : ℝ) (i : Fin d)
    (y : Transverse i) (hy : y ≠ 0) (t : ℝ)
    (ht : t ∈ (fiber (logarithmicDomain d) i y : Set ℝ)) :
    HasDerivAt (fun s => logarithmicProfile a (coordinateLine i y s))
      (logarithmicPartial a i (coordinateLine i y t)) t := by
  let v : ℝ → EuclideanSpace ℝ (Fin d) :=
    fun s => WithLp.toLp 2 (coordinateLine i y s)
  have hv : HasDerivAt v (WithLp.toLp 2 (coordinateVector i)) t :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
      (coordinateLine_hasDerivAt i y t)
  have hinner : inner ℝ (v t) (WithLp.toLp 2 (coordinateVector i)) = t := by
    rw [PiLp.inner_apply, Finset.sum_eq_single i]
    · simp [v, coordinateVector, coordinateLine, RCLike.inner_apply]
    · intro j _ hji
      simp [coordinateVector, hji, RCLike.inner_apply]
    · simp
  have hsq : HasDerivAt (fun s => ‖v s‖ ^ 2) (2 * t) t := by
    simpa [hinner] using hv.norm_sq
  have hrpos : 0 < ‖v t‖ := by
    exact norm_pos_iff.mpr (by simpa [v] using coordinateLine_ne_zero_of_ne_zero i y hy t)
  have hlogpos : 0 < Real.log (1 / ‖v t‖) := by
    have hrt : ‖v t‖ < Real.exp (-1) := ht
    have hrlt : ‖v t‖ < 1 := hrt.trans (Real.exp_lt_one_iff.mpr (by norm_num))
    exact Real.log_pos ((one_lt_div hrpos).mpr hrlt)
  have hbase : -(1 / 2 : ℝ) * Real.log (‖v t‖ ^ 2) ≠ 0 := by
    rw [← log_inv_eq_log_sq]
    exact hlogpos.ne'
  have hlog := (hsq.log (pow_ne_zero 2 hrpos.ne')).const_mul (-(1 / 2 : ℝ))
  have hp := hlog.rpow_const (p := a) (Or.inl hbase)
  convert hp using 1
  · funext s
    rw [logarithmicProfile, if_neg (coordinateLine_ne_zero_of_ne_zero i y hy s)]
    congr 1
    exact log_inv_eq_log_sq _
  · dsimp only [logarithmicPartial, coordinateLine]
    simp only [dif_pos rfl]
    rw [← log_inv_eq_log_sq]
    change -a * (t / ‖v t‖) * ((‖v t‖)⁻¹ * (Real.log (1 / ‖v t‖)) ^ (a - 1)) = _
    field_simp

lemma logarithmic_line_contDiffOn {d : ℕ} (a : ℝ) (i : Fin d)
    (y : Transverse i) (hy : y ≠ 0) :
    ContDiffOn ℝ 1 (fun s => logarithmicProfile a (coordinateLine i y s))
      (fiber (logarithmicDomain d) i y : Set ℝ) := by
  let v : ℝ → EuclideanSpace ℝ (Fin d) :=
    fun s => WithLp.toLp 2 (coordinateLine i y s)
  have hv : ContDiff ℝ 1 v :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap.contDiff.comp
      ((coordinateLine_contDiff i y).of_le (by simp))
  have hvne (s : ℝ) : v s ≠ 0 := by
    simpa [v] using coordinateLine_ne_zero_of_ne_zero i y hy s
  have hsq : ContDiff ℝ 1 (fun s => ‖v s‖ ^ 2) := hv.norm_sq ℝ
  have hlog : ContDiffOn ℝ 1 (fun s => Real.log (‖v s‖ ^ 2))
      (fiber (logarithmicDomain d) i y : Set ℝ) :=
    hsq.contDiffOn.log (fun s _ => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hvne s)))
  have hbase : ∀ s ∈ (fiber (logarithmicDomain d) i y : Set ℝ),
      -(1 / 2 : ℝ) * Real.log (‖v s‖ ^ 2) ≠ 0 := by
    intro s hs
    rw [← log_inv_eq_log_sq]
    have hrpos : 0 < ‖v s‖ := norm_pos_iff.mpr (hvne s)
    have hrt : ‖v s‖ < Real.exp (-1) := hs
    have hrlt : ‖v s‖ < 1 := hrt.trans (Real.exp_lt_one_iff.mpr (by norm_num))
    exact (Real.log_pos ((one_lt_div hrpos).mpr hrlt)).ne'
  have hscaled : ContDiffOn ℝ 1 (fun s => -(1 / 2 : ℝ) * Real.log (‖v s‖ ^ 2))
      (fiber (logarithmicDomain d) i y : Set ℝ) := contDiffOn_const.mul hlog
  apply (hscaled.rpow_const_of_ne hbase).congr
  intro s _
  rw [logarithmicProfile, if_neg (coordinateLine_ne_zero_of_ne_zero i y hy s)]
  congr 1
  exact log_inv_eq_log_sq _

lemma logarithmic_profile_sobolev (d : ℕ) (hd : 1 < d) (a : ℝ)
    (ha : a < 1 - 1 / (d : ℝ)) [Fact (1 ≤ (d : ℝ≥0∞))] :
    ∃ u : Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.SpaceValue ℝ d (logarithmicDomain d) 1 d,
      u.val (zeroIndex d 1) =ᵐ[volume.restrict (logarithmicDomain d : Set (Domain d))]
        logarithmicProfile a := by
  let hf := logarithmicProfile_memLp d (by omega) a ha
  let u : DomainLp ℝ (logarithmicDomain d) d := hf.toLp (logarithmicProfile a)
  let g : Fin d → DomainLp ℝ (logarithmicDomain d) d := fun i =>
    (logarithmicPartial_memLp d (by omega) a ha i).toLp (logarithmicPartial a i)
  have hrep : u =ᵐ[volume.restrict (logarithmicDomain d : Set (Domain d))]
      logarithmicProfile a := MemLp.coeFn_toLp _
  have hacl : HasACLDerivatives (logarithmicDomain d) (logarithmicProfile a) g := by
    intro i
    letI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
    obtain ⟨j, hj⟩ := exists_ne i
    letI : Nonempty {j : Fin d // j ≠ i} := ⟨⟨j, hj⟩⟩
    have hgrep : g i =ᵐ[volume.restrict (logarithmicDomain d : Set (Domain d))]
        logarithmicPartial a i := MemLp.coeFn_toLp _
    filter_upwards [(volume : Measure (Transverse i)).ae_ne 0, ae_on_fibers i hgrep] with y hy hgy
    constructor
    · intro b c hbc
      exact ((logarithmic_line_contDiffOn a i y hy).mono hbc).absolutelyContinuousOnInterval
    · filter_upwards [hgy, ae_restrict_mem (fiber (logarithmicDomain d) i y).isOpen.measurableSet]
        with t ht htf
      rw [ht]
      exact logarithmic_line_hasDerivAt a i y hy t htf
  obtain ⟨v, hv⟩ := (acl_membership_characterization ℝ d (logarithmicDomain d) d u).mpr
    ⟨logarithmicProfile a, g, hrep, hacl⟩
  refine ⟨v, ?_⟩
  rw [hv]
  exact hrep

theorem logarithmic_counterexample :
    Specs.ExpandedFA.Sobolev.HigherSobolevEmbeddings.LogarithmicCounterexample := by
  intro d hd a ha ha' _
  exact ⟨logarithmic_profile_sobolev d hd a ha',
    logarithmicProfile_not_memLp_top d (by omega) a ha⟩

end ExpandedFA.Sobolev.Higher

namespace ExpandedFA.Sobolev.Higher
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Higher Holder iteration using an established critical-order estimate on
this domain. The main embedding supplies that estimate separately. -/
theorem fullHolder_positive_gap_of_critical (hΩ : FirstOrderExtensionDomain 𝕜 Ω)
    (hcrit : ∀ (n : ℕ) (r : ℝ≥0) [Fact (1 ≤ (r : ℝ≥0∞))], 1 ≤ r → n*r=d →
      ∀ a : ℝ, 0 < a → a < 1 → FullHolder 𝕜 Ω (n+1) r a)
    (m : ℕ) (r : ℝ≥0) [Fact (1 ≤ (r : ℝ≥0∞))] (hr : 1 ≤ r)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hgap : a < (m : ℝ)-(d : ℝ)/(r : ℝ) ∨
      (a = (m : ℝ)-(d : ℝ)/(r : ℝ) ∧ a < 1)) :
    FullHolder 𝕜 Ω m r a := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hdterm : 0 ≤ (d : ℝ)/(r : ℝ) := div_nonneg (Nat.cast_nonneg _) hr0.le
  induction m generalizing a with
  | zero => rcases hgap with h|⟨h,_⟩ <;> simp only [Nat.cast_zero, zero_sub] at * <;> linarith
  | succ m ih =>
    have hle : a ≤ ((m+1 : ℕ) : ℝ) - (d : ℝ)/(r : ℝ) :=
      hgap.elim le_of_lt (fun h => h.1.le)
    have hsuperR : (d : ℝ) < ((m+1 : ℕ) : ℝ)*(r : ℝ) := by
      apply (div_lt_iff₀ hr0).mp
      linarith
    have hsuper : (d : ℝ≥0) < (m+1 : ℕ)*r := by exact_mod_cast hsuperR
    rcases lt_trichotomy (m*r) (d : ℝ≥0) with hsub | hcritEq | hsuperPred
    · exact fullHolder_lower ha hle
        (fullHolder_subcritical_gap hΩ m r hr hsub hsuper)
    · have hprod : (m : ℝ)*(r : ℝ) = d := by exact_mod_cast hcritEq
      have hratio : (d : ℝ)/(r : ℝ) = m := (div_eq_iff hr0.ne').mpr (by nlinarith)
      have hlt : a < 1 := by
        rcases hgap with h | ⟨h,h'⟩
        · simp only [hratio, Nat.cast_add, Nat.cast_one] at h
          linarith
        · exact h'
      exact hcrit m r hr hcritEq a ha hlt
    · have hprod : (d : ℝ) < (m : ℝ)*(r : ℝ) := by exact_mod_cast hsuperPred
      have hgapPos : 0 < (m : ℝ)-(d : ℝ)/(r : ℝ) := by
        exact sub_pos.mpr ((div_lt_iff₀ hr0).mpr hprod)
      let b : ℝ := min (1/2) (((m : ℝ)-(d : ℝ)/(r : ℝ))/2)
      have hb : 0 < b := lt_min (by norm_num) (half_pos hgapPos)
      have hb1 : b ≤ 1 := (min_le_left _ _).trans (by norm_num)
      have hbgap : b < (m : ℝ)-(d : ℝ)/(r : ℝ) :=
        (min_le_right _ _).trans_lt (half_lt_self hgapPos)
      have H := ih b hb hb1 (Or.inl hbgap)
      exact fullHolder_lower ha ha1 (fullHolder_successor_lipschitz hΩ H)
end ExpandedFA.Sobolev.Higher

namespace ExpandedFA.Sobolev.Higher
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- At the infinity source exponent, every positive remaining order gives
all Holder exponents below one, including their full supremum estimates. -/
theorem fullHolder_infinity_source (hΩ : FirstOrderExtensionDomain 𝕜 Ω)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) : FullHolder 𝕜 Ω 1 ∞ a := by
  have H : FullHolder 𝕜 Ω 1 ∞ 1 := by
    simpa only [FullHolder, Morrey.Represents, Morrey.exponent_top] using
      (firstOrder_full_morrey (p := ∞) hΩ (ENNReal.natCast_lt_top d))
  exact fullHolder_lower ha ha1 H

/-- On bounded extension domains the positive integral gap has exactly the
stated sub-Lipschitz conclusion for the last derivative. -/
theorem integral_holder_bounded_extension
    (hΩb : Bornology.IsBounded (Ω : Set (Domain d)))
    (hΩ : FirstOrderExtensionDomain 𝕜 Ω) {m k : ℕ} (hk : 1 ≤ k)
    (hgap : (m : ℝ) - (d : ℝ) / p.toReal = k)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ hk' : k-1 ≤ m,
      ∀ u : SpaceValue 𝕜 d Ω m p, HolderJet u (k-1) hk' a C := by
  have hkR : (k : ℝ) ≤ m := by
    have hdterm : 0 ≤ (d : ℝ)/p.toReal := div_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg
    linarith
  have hkm : k ≤ m := by exact_mod_cast hkR
  have hk' : k-1 ≤ m := by omega
  by_cases hpTop : p = ∞
  · have heq : m=k := by
      simp only [hpTop, ENNReal.toReal_top, div_zero, sub_zero] at hgap
      exact_mod_cast hgap
    have H : FullHolder 𝕜 Ω 1 p a := by
      subst p
      exact fullHolder_infinity_source hΩ ha ha1.le
    obtain ⟨C,hC,Hjet⟩ := holderJet_of_fullHolder hk' (show k-1+1 ≤ m by omega) H
    exact ⟨C,hC,hk',Hjet⟩
  · have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le Fact.out)
    have hpR0 : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
    have hp1 : 1 ≤ p.toNNReal := by
      apply ENNReal.coe_le_coe.mp
      simpa only [ENNReal.coe_one, ENNReal.coe_toNNReal hpTop] using (Fact.out : 1 ≤ p)
    let n := m-k
    have hmn : k+n=m := by dsimp [n]; omega
    have hmnR : (m : ℝ) = (k : ℝ)+(n : ℝ) := by exact_mod_cast hmn.symm
    have heqR : (n : ℝ)*p.toReal = d := by
      have hdiv : (d : ℝ)/p.toReal = n := by linarith
      exact ((div_eq_iff hpR0.ne').mp hdiv).symm
    have heq : n*p.toNNReal=d := by
      apply NNReal.eq
      exact heqR
    haveI : Fact (1 ≤ (p.toNNReal : ℝ≥0∞)) := ⟨by exact_mod_cast hp1⟩
    have H : FullHolder 𝕜 Ω (n+1) p a := by
      simpa only [ENNReal.coe_toNNReal hpTop] using
        fullHolder_critical_bounded hΩb hΩ n p.toNNReal hp1 heq a ha ha1
    obtain ⟨C,hC,Hjet⟩ := holderJet_of_fullHolder hk' (show k-1+(n+1) ≤ m by omega) H
    exact ⟨C,hC,hk',Hjet⟩
end ExpandedFA.Sobolev.Higher

namespace ExpandedFA.Sobolev.Higher
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
variable {𝕜 : Type} [RCLike 𝕜]

/-- The genuine whole-line W^{1,1} endpoint controls the full supremum. -/
theorem oneDimension_whole_infinity :
    LpInclusion 𝕜 (⊤ : Opens (Domain 1)) 1 1 ∞ := by
  obtain ⟨ρ, hρ⟩ := Smoothing.exists_mollifier 1
  obtain ⟨R, hR, hRs⟩ := hρ.2.1.isBounded.subset_ball_lt 0 (0 : Domain 1)
  let A : ℝ := (eLpNorm (SmoothApproximateIdentitiesSpec.ScaledKernelValue ρ 1)
    (1 : ℝ≥0∞).conjExponent volume).toReal
  let C : ℝ := 1 + A
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C.toNNReal, fun u => ?_⟩
  obtain ⟨f, hf⟩ := OneDimensional.representative_existence 𝕜 ⊤ ordConnected_univ 1 u
  let F : Domain 1 → 𝕜 := fun x => f (x 0)
  have hfc : Continuous f := by
    simpa only [Opens.coe_top, closure_univ, continuousOn_univ] using hf.1
  have hF : Continuous F := hfc.comp (continuous_apply 0)
  have hr : u.val (zeroIndex 1 1) =ᵐ[volume] F := by
    have h := hf.2.1
    change u.val (zeroIndex 1 1) =ᵐ[volume.restrict (Set.univ : Set (Domain 1))] F at h
    simpa only [Measure.restrict_univ] using h
  have hdiff (x y : Domain 1) : ‖F x - F y‖ ≤ ‖u‖ := by
    have h := OneDimensional.primitive_increment_bound (I := (⊤ : Opens ℝ)) (p := 1) ordConnected_univ u hf
      (x := x 0) (y := y 0) (mem_univ _) (mem_univ _)
    simp only [OneDimensional.reciprocalExponent, ENNReal.toReal_one, div_one,
      sub_self, Real.rpow_zero, mul_one] at h
    exact h.trans (PiLp.norm_apply_le u.val OneDimensional.firstIndex)
  have hdisp (x : Domain 1) :
      ‖convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume x - F x‖ ≤ ‖u‖ := by
    rw [← dist_eq_norm]
    apply dist_convolution_le (norm_nonneg u) ((subset_tsupport ρ).trans hRs)
      hρ.2.2.1 hρ.2.2.2 hF.aestronglyMeasurable
    intro y _
    simpa only [dist_eq_norm] using hdiff y x
  have heq (x : Domain 1) : convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume x =
      Smoothing.regularize ρ 1 (u.val (zeroIndex 1 1)) x := by
    have hae : Smoothing.zeroExtend (u.val (zeroIndex 1 1)) =ᵐ[volume] F := by
      simpa only [Smoothing.zeroExtend, Opens.coe_top, Set.indicator_univ] using hr
    have hk : SmoothApproximateIdentitiesSpec.ScaledKernelValue ρ 1 = ρ := by
      funext z
      change ((1 : ℝ)^1)⁻¹ * ρ ((1 : ℝ)⁻¹ • z) = ρ z
      simp
    change convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume x =
      convolution (SmoothApproximateIdentitiesSpec.ScaledKernelValue ρ 1)
        (Smoothing.zeroExtend (u.val (zeroIndex 1 1))) (ContinuousLinearMap.lsmul ℝ ℝ) volume x
    rw [hk]
    exact congrFun (convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ)
      (Filter.EventuallyEq.rfl : ρ =ᵐ[volume] ρ) hae.symm) x
  have hsup (x : Domain 1) : ‖F x‖ ≤ C * ‖u‖ := by
    calc
      ‖F x‖ ≤ ‖F x - convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ +
          ‖convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ := norm_le_norm_sub_add _ _
      _ ≤ ‖u‖ + A * ‖u.val (zeroIndex 1 1)‖ := by
        apply add_le_add
        · rw [norm_sub_rev]; exact hdisp x
        · rw [heq x]; exact Morrey.regularize_norm_le_lp ρ hρ (by norm_num) _ x
      _ ≤ ‖u‖ + A * ‖u‖ := by
        gcongr
        exact PiLp.norm_apply_le u.val _
      _ = C * ‖u‖ := by change ‖u‖ + A * ‖u‖ = _; dsimp [C]; ring
  have hbound : ∀ᵐ x ∂volume.restrict ((⊤ : Opens (Domain 1)) : Set (Domain 1)),
      ‖u.val (zeroIndex 1 1) x‖ ≤ C * ‖u‖ := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using hr.mono (fun x hx => by rw [hx]; exact hsup x)
  have hn := eLpNormEssSup_le_of_ae_bound hbound
  have htarget : eLpNorm (u.val (zeroIndex 1 1)) ∞
      (volume.restrict ((⊤ : Opens (Domain 1)) : Set (Domain 1))) ≤ ENNReal.ofReal (C * ‖u‖) := by
    simpa only [eLpNorm_exponent_top (Lp.memLp _).aestronglyMeasurable] using hn
  refine ⟨htarget.trans_lt ENNReal.ofReal_lt_top, ?_⟩
  change _ ≤ ENNReal.ofReal C * ENNReal.ofReal ‖u‖
  simpa only [ENNReal.ofReal_mul hC] using htarget

/-- The elementary interpolation bound between L¹ and L∞, on any measure
space. The same common bound controls every intermediate finite norm. -/
theorem eLpNorm_le_of_L1_Linfty {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : X → 𝕜) (hf : AEStronglyMeasurable f μ) (q : ℝ≥0) (hq : 1 ≤ q)
    (K : ℝ≥0∞) (hK : K ≠ ∞) (h1 : eLpNorm f 1 μ ≤ K)
    (htop : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ K) : eLpNorm f q μ ≤ K := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have hq0 : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast (ne_of_gt (zero_lt_one.trans_le hq))
  have hsub : 0 ≤ (q : ℝ)-1 := sub_nonneg.mpr hqR
  have hpoint : ∀ᵐ x ∂μ, ‖f x‖ₑ ^ (q : ℝ) ≤ K ^ ((q : ℝ)-1) * ‖f x‖ₑ := by
    filter_upwards [htop] with x hx
    calc
      ‖f x‖ₑ ^ (q : ℝ) = ‖f x‖ₑ ^ ((q : ℝ)-1) * ‖f x‖ₑ := by
        calc
          _ = ‖f x‖ₑ ^ (((q : ℝ)-1)+1) := by congr 1; ring
          _ = ‖f x‖ₑ ^ ((q : ℝ)-1) * ‖f x‖ₑ ^ (1 : ℝ) :=
            ENNReal.rpow_add_of_nonneg _ _ hsub (by norm_num)
          _ = _ := by rw [ENNReal.rpow_one]
      _ ≤ K ^ ((q : ℝ)-1) * ‖f x‖ₑ := mul_le_mul' (ENNReal.rpow_le_rpow hx hsub) le_rfl
  have hint : (∫⁻ x, ‖f x‖ₑ ^ (q : ℝ) ∂μ) ≤ K ^ (q : ℝ) := by
    calc
      _ ≤ ∫⁻ x, K ^ ((q : ℝ)-1) * ‖f x‖ₑ ∂μ := lintegral_mono_ae hpoint
      _ = K ^ ((q : ℝ)-1) * eLpNorm f 1 μ := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hsub hK),
          ← eLpNorm_one_eq_lintegral_enorm hf]
      _ ≤ K ^ ((q : ℝ)-1) * K := mul_le_mul' le_rfl h1
      _ = K ^ (q : ℝ) := by
        calc
          _ = K ^ ((q : ℝ)-1) * K ^ (1 : ℝ) := by rw [ENNReal.rpow_one]
          _ = K ^ (((q : ℝ)-1)+1) :=
            (ENNReal.rpow_add_of_nonneg _ _ hsub (by norm_num)).symm
          _ = _ := by congr 1; ring
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 ENNReal.coe_ne_top hf]
  simp only [ENNReal.coe_toReal]
  calc
    _ ≤ (K ^ (q : ℝ)) ^ (1 / (q : ℝ)) := ENNReal.rpow_le_rpow hint (by positivity)
    _ = K := by rw [← ENNReal.rpow_mul, mul_one_div_cancel (ne_of_gt hqpos), ENNReal.rpow_one]

/-- Every finite Lq target is available at the one-dimensional whole-space
critical exponent. There is no finite-measure assumption on the line. -/
theorem oneDimension_whole_finite (q : ℝ≥0) (hq : 1 ≤ q) :
    LpInclusion 𝕜 (⊤ : Opens (Domain 1)) 1 1 q := by
  obtain ⟨C, H⟩ := oneDimension_whole_infinity (𝕜 := 𝕜)
  let D : ℝ≥0 := C+1
  have hCD : (C : ℝ≥0∞) ≤ D := by exact_mod_cast (show C ≤ D by dsimp [D]; exact le_add_of_nonneg_right (by positivity))
  have hD1 : (1 : ℝ≥0∞) ≤ D := by exact_mod_cast (show 1 ≤ D by dsimp [D]; exact le_add_of_nonneg_left (by positivity))
  refine ⟨D, fun u => ?_⟩
  let μ := volume.restrict ((⊤ : Opens (Domain 1)) : Set (Domain 1))
  let K : ℝ≥0∞ := D * ENNReal.ofReal ‖u‖
  have hK : K ≠ ∞ := ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
  have htop : ∀ᵐ x ∂μ, ‖u.val (zeroIndex 1 1) x‖ₑ ≤ K := by
    have hh := enorm_ae_le_eLpNormEssSup (u.val (zeroIndex 1 1)) μ
    have hb := (H u).2
    rw [eLpNorm_exponent_top (Lp.memLp _).aestronglyMeasurable] at hb
    exact hh.mono (fun x hx => hx.trans (hb.trans (mul_le_mul' hCD le_rfl)))
  have h1 : eLpNorm (u.val (zeroIndex 1 1)) 1 μ ≤ K := by
    calc
      _ ≤ ENNReal.ofReal ‖u‖ := by
        rw [← Lp.enorm_def, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (PiLp.norm_apply_le u.val _)
      _ ≤ K := le_mul_of_one_le_left (by positivity) hD1
  have hb := eLpNorm_le_of_L1_Linfty (u.val (zeroIndex 1 1)) (Lp.memLp _).aestronglyMeasurable q hq K hK h1 htop
  exact ⟨hb.trans_lt (lt_top_iff_ne_top.mpr hK), hb⟩
end ExpandedFA.Sobolev.Higher

namespace ExpandedFA.Sobolev.Higher
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}

lemma eLpNorm_nat_pow {f : Domain d → 𝕜} (hf : AEStronglyMeasurable f volume)
    (p : ℝ≥0∞) (N : ℕ) (hN : 0 < N) :
    eLpNorm (fun x => f x ^ N) p volume = (eLpNorm f (p * N) volume) ^ N := by
  have heq : eLpNorm (fun x => f x ^ N) p volume =
      eLpNorm (fun x => ‖f x‖ ^ N) p volume := by
    apply eLpNorm_congr_norm_ae (hf.pow N) (hf.norm.pow N)
    exact Filter.Eventually.of_forall (fun x => by simp)
  rw [heq]
  simpa only [Real.rpow_natCast, ENNReal.ofReal_natCast, ENNReal.rpow_natCast] using
    eLpNorm_norm_rpow (p := p) f hf (show (0 : ℝ) < N by exact_mod_cast hN)

lemma norm_fderiv_nat_pow {f : Domain d → 𝕜} (hf : ContDiff ℝ 1 f)
    (N : ℕ) (x : Domain d) :
    ‖fderiv ℝ (fun y => f y ^ N) x‖ ≤ N * ‖f x‖ ^ (N-1) * ‖fderiv ℝ f x‖ := by
  rw [(hf.differentiable one_ne_zero x).hasFDerivAt.pow N |>.fderiv]
  simp [norm_smul, norm_pow, nsmul_eq_mul, mul_assoc]

/-- Applying the ordinary first-order L¹ Sobolev inequality to a natural
power gives a critical-exponent recurrence, over either scalar field. -/
theorem critical_smooth_power_step (hd : 2 ≤ d)
    {f : Domain d → 𝕜} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (N : ℕ) (hN : 2 ≤ N) :
    (eLpNorm f ((NNReal.conjExponent (d : ℝ≥0) : ℝ≥0∞) * N) volume) ^ N ≤
      (eLpNormLESNormFDerivOneConst (volume : Measure (Domain d))
        (NNReal.conjExponent (d : ℝ≥0)) : ℝ≥0∞) * N *
      (eLpNorm f ((NNReal.conjExponent (d : ℝ≥0) : ℝ≥0∞) * (N-1 : ℕ)) volume) ^ (N-1) *
      eLpNorm (fderiv ℝ f) d volume := by
  let c : ℝ≥0 := NNReal.conjExponent d
  have hconj : NNReal.HolderConjugate (d : ℝ≥0) c :=
    NNReal.HolderConjugate.conjExponent (by exact_mod_cast (show 1 < d by omega))
  let hcd : ENNReal.HolderTriple (c : ℝ≥0∞) (d : ℝ≥0∞) 1 := hconj.symm.coe_ennreal
  have hfcN : HasCompactSupport (fun x => f x ^ N) :=
    hfc.comp_left (g := fun z : 𝕜 => z ^ N) (by simp [show N ≠ 0 by omega])
  have hgns := eLpNorm_le_eLpNorm_fderiv_one volume (hf.pow N) hfcN
    (by simpa using hconj)
  rw [eLpNorm_nat_pow hf.continuous.aestronglyMeasurable _ _ (by omega)] at hgns
  let A : ℝ≥0∞ := eLpNormLESNormFDerivOneConst (volume : Measure (Domain d)) c
  change _ ≤ A * N * _ * _
  calc
    _ ≤ A * eLpNorm (fderiv ℝ (fun x => f x ^ N)) 1 volume := hgns
    _ ≤ A * eLpNorm (fun x => (N : ℝ) * (‖f x‖ ^ (N-1) * ‖fderiv ℝ f x‖)) 1 volume := by
      apply mul_le_mul_right
      apply eLpNorm_mono ((hf.pow N).continuous_fderiv one_ne_zero).aestronglyMeasurable
      intro x
      simpa [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ N * (‖f x‖ ^ (N-1) * ‖fderiv ℝ f x‖)), mul_assoc] using norm_fderiv_nat_pow hf N x
    _ = A * ((N : ℝ≥0∞) * eLpNorm (fun x => ‖f x‖ ^ (N-1) * ‖fderiv ℝ f x‖) 1 volume) := by
      have he := eLpNorm_const_smul (N : ℝ) (fun x => ‖f x‖ ^ (N-1) * ‖fderiv ℝ f x‖) 1 volume
      simp only [Real.enorm_natCast] at he
      convert congrArg (A * ·) he using 1
    _ ≤ A * ((N : ℝ≥0∞) * (eLpNorm (fun x => ‖f x‖ ^ (N-1)) c volume *
        eLpNorm (fun x => ‖fderiv ℝ f x‖) d volume)) := by
      gcongr
      convert (eLpNorm_smul_le_mul_eLpNorm (p := (c : ℝ≥0∞)) (q := (d : ℝ≥0∞))
          ((hf.continuous.norm.pow (N-1)).aestronglyMeasurable)
          ((hf.continuous_fderiv one_ne_zero).norm.aestronglyMeasurable)) using 1
      exact hcd
    _ = _ := by
      have hp := eLpNorm_nat_pow (𝕜 := ℝ) hf.continuous.norm.aestronglyMeasurable
        (c : ℝ≥0∞) (N-1) (by omega)
      rw [eLpNorm_norm f hf.continuous.aestronglyMeasurable] at hp
      have hd_norm := eLpNorm_norm (μ := volume) (p := (d : ℝ≥0∞)) (fderiv ℝ f)
        ((hf.continuous_fderiv one_ne_zero).aestronglyMeasurable)
      rw [hp, hd_norm]
      simp only [mul_assoc, c]

lemma critical_ladder_base (hd : 2 ≤ d) :
    NNReal.conjExponent (d : ℝ≥0) * (d-1 : ℕ) = (d : ℝ≥0) := by
  have hdreal : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
  apply NNReal.coe_injective
  simp only [NNReal.coe_mul, NNReal.conjExponent, NNReal.coe_div, NNReal.coe_natCast]
  rw [NNReal.coe_sub (by exact_mod_cast (show 1 ≤ d by omega)), NNReal.coe_one,
    Nat.cast_sub (by omega)]
  simp only [NNReal.coe_natCast, Nat.cast_one]
  field_simp

/-- Compact smooth critical bounds at an unbounded ladder of finite exponents.
The constant is independent of compact support and of the scalar field. -/
theorem critical_compact_smooth_ladder (hd : 2 ≤ d) (N : ℕ) (hN : d-1 ≤ N) :
    ∃ C : ℝ≥0, ∀ (𝕜 : Type) [RCLike 𝕜] (f : Domain d → 𝕜),
      ContDiff ℝ 1 f → HasCompactSupport f →
      eLpNorm f ((NNReal.conjExponent (d : ℝ≥0) : ℝ≥0∞) * N) volume ≤
        (C : ℝ≥0∞) * (eLpNorm f d volume + eLpNorm (fderiv ℝ f) d volume) := by
  induction N, hN using Nat.le_induction with
  | base =>
    refine ⟨1, fun 𝕜 _ f hf hfc => ?_⟩
    have he := congrArg ((↑) : ℝ≥0 → ℝ≥0∞) (critical_ladder_base hd)
    simp only [ENNReal.coe_mul, ENNReal.coe_natCast] at he
    rw [he, ENNReal.coe_one, one_mul]
    exact le_add_right le_rfl
  | succ N hN ih =>
    obtain ⟨C,hC⟩ := ih
    let A : ℝ≥0 := eLpNormLESNormFDerivOneConst (volume : Measure (Domain d))
      (NNReal.conjExponent (d : ℝ≥0)) * (N+1)
    refine ⟨A+C, fun 𝕜 _ f hf hfc => ?_⟩
    let S : ℝ≥0∞ := eLpNorm f d volume + eLpNorm (fderiv ℝ f) d volume
    have hprev : eLpNorm f ((NNReal.conjExponent (d : ℝ≥0) : ℝ≥0∞) * N) volume ≤ C * S :=
      hC 𝕜 f hf hfc
    have hdS : eLpNorm (fderiv ℝ f) d volume ≤ S := le_add_left le_rfl
    have hstep := critical_smooth_power_step hd hf hfc (N+1) (by omega)
    simp only [Nat.add_sub_cancel] at hstep
    have hbound : eLpNorm f ((NNReal.conjExponent (d : ℝ≥0) : ℝ≥0∞) * (N+1)) volume ^ (N+1) ≤
        (((A+C : ℝ≥0) : ℝ≥0∞) * S) ^ (N+1) := by
      calc
        _ ≤ (A : ℝ≥0∞) * (eLpNorm f ((NNReal.conjExponent (d : ℝ≥0) : ℝ≥0∞) * N) volume) ^ N *
            eLpNorm (fderiv ℝ f) d volume := by
          simpa [A, ENNReal.coe_mul] using hstep
        _ ≤ (A : ℝ≥0∞) * ((C : ℝ≥0∞) * S) ^ N * S :=
          mul_le_mul' (mul_le_mul_right (pow_le_pow_left' hprev N) _) hdS
        _ = (A : ℝ≥0∞) * (C : ℝ≥0∞)^N * S^(N+1) := by
          simp only [mul_pow, pow_succ]; ring
        _ ≤ ((A+C : ℝ≥0) : ℝ≥0∞) ^ (N+1) * S^(N+1) := by
          apply mul_le_mul_left
          rw [pow_succ']
          apply mul_le_mul'
          · exact ENNReal.coe_le_coe.mpr (le_add_right le_rfl)
          · exact pow_le_pow_left' (ENNReal.coe_le_coe.mpr (le_add_left le_rfl)) N
        _ = _ := (mul_pow _ _ _).symm
    have hout := (ENNReal.pow_le_pow_left_iff (show N+1 ≠ 0 by omega)).mp hbound
    simpa only [Nat.cast_add, Nat.cast_one, S] using hout

/-- The discrete critical ladder reaches a first-order Morrey exponent above
any prescribed exponent strictly below one. -/
lemma critical_ladder_exponent_large (hd : 2 ≤ d) (a : ℝ) (ha : a < 1) :
    ∃ N : ℕ, d-1 ≤ N ∧
      (d : ℝ≥0) < NNReal.conjExponent (d : ℝ≥0) * N ∧
      a < 1 - (d : ℝ) / (NNReal.conjExponent (d : ℝ≥0) * N : ℝ≥0) := by
  let c : ℝ≥0 := NNReal.conjExponent d
  have hc : 1 ≤ c := (NNReal.HolderConjugate.conjExponent
    (show (1 : ℝ≥0) < d by exact_mod_cast (show 1 < d by omega))).symm.lt.le
  obtain ⟨N,hN⟩ := exists_nat_gt (max (d : ℝ) ((d : ℝ) / (1-a)))
  have hNd : (d : ℝ) < N := (le_max_left _ _).trans_lt hN
  have hNarith : (d : ℝ) / (1-a) < N := (le_max_right _ _).trans_lt hN
  have hNpos : (0 : ℝ) < N := (by positivity : (0 : ℝ) ≤ d).trans_lt hNd
  have hqN : (N : ℝ) ≤ (c : ℝ) * N := by
    simpa using mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ c by exact_mod_cast hc) hNpos.le
  have hqd : (d : ℝ) < (c : ℝ) * N := hNd.trans_le hqN
  have hdiv : (d : ℝ) < ((c : ℝ) * N) * (1-a) :=
    (div_lt_iff₀ (sub_pos.mpr ha)).mp (hNarith.trans_le hqN)
  have hNdNat : d < N := by exact_mod_cast hNd
  refine ⟨N, (Nat.sub_le d 1).trans hNdNat.le, ?_, ?_⟩
  · exact_mod_cast hqd
  · have hqpos : (0 : ℝ) < (c : ℝ) * N := hNpos.trans_le hqN
    have hratio : (d : ℝ) / ((c : ℝ) * N) < 1-a :=
      (div_lt_iff₀ hqpos).mpr (by nlinarith [hdiv])
    dsimp only [c] at hratio
    push_cast
    linarith

/-- A finite critical whole-space target whose subsequent Morrey exponent
exceeds any prescribed Hölder exponent below one. The estimate here is the
compact smooth analytic input; cutoff and mollification transfer it to W¹ᵈ. -/
theorem critical_compact_smooth_for_holder (hd : 2 ≤ d) (a : ℝ) (ha : a < 1) :
    ∃ q : ℝ≥0, (d : ℝ≥0) < q ∧ a < Morrey.exponent d q ∧
      ∃ C : ℝ≥0, ∀ (𝕜 : Type) [RCLike 𝕜] (f : Domain d → 𝕜),
        ContDiff ℝ 1 f → HasCompactSupport f →
        eLpNorm f q volume ≤ (C : ℝ≥0∞) *
          (eLpNorm f d volume + eLpNorm (fderiv ℝ f) d volume) := by
  obtain ⟨N,hN,hq,hqa⟩ := critical_ladder_exponent_large hd a ha
  refine ⟨NNReal.conjExponent (d : ℝ≥0) * N, hq, ?_, ?_⟩
  · simpa only [Morrey.exponent, ENNReal.coe_toReal] using hqa
  · simpa only [ENNReal.coe_mul, ENNReal.coe_natCast] using critical_compact_smooth_ladder hd N hN

end ExpandedFA.Sobolev.Higher

namespace ExpandedFA.Sobolev.Higher
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}

/-- Iterate a genuine first-order critical inclusion, using only the
first-order extension property at the preceding subcritical steps. The target
exponent may be finite or infinity, with no measure finiteness assumption. -/
theorem critical_extension_inclusion_of_firstOrder (hd : 1 ≤ d)
    (hΩ : FirstOrderExtensionDomain 𝕜 Ω) (q : ℝ≥0∞)
    [Fact (1 ≤ (d : ℝ≥0∞))] (Hcrit : LpInclusion 𝕜 Ω 1 d q)
    (n : ℕ) (r : ℝ≥0) [Fact (1 ≤ (r : ℝ≥0∞))]
    (hr : 1 ≤ r) (hn : n*r=d) : LpInclusion 𝕜 Ω n r q := by
  induction n generalizing r with
  | zero =>
    have hd0 : d=0 := by simpa only [Nat.cast_zero, zero_mul, Nat.cast_eq_zero] using hn.symm
    omega
  | succ n ih =>
    by_cases hn0 : n=0
    · subst n
      have hrEq : r=d := by simpa only [zero_add, Nat.cast_one, one_mul] using hn
      subst r
      simpa only [ENNReal.coe_natCast] using Hcrit
    · obtain ⟨hrd, hs1, hns⟩ := critical_iteration_arithmetic (show 1 ≤ n by omega) hr hn
      letI : Fact (1 ≤ (Subcritical.criticalExponent d r : ℝ≥0∞)) :=
        ⟨by exact_mod_cast hs1⟩
      exact lpInclusion_step (firstOrder_subcritical hΩ r hr hrd)
        (ih (Subcritical.criticalExponent d r) hs1 hns)

/-- A supercritical target of the genuine first-order critical inclusion
supplies the higher critical Holder bound at any smaller positive exponent. -/
theorem fullHolder_critical_of_firstOrder (hd : 1 ≤ d)
    (hΩ : FirstOrderExtensionDomain 𝕜 Ω) (q : ℝ≥0∞)
    [Fact (1 ≤ (d : ℝ≥0∞))] (Hcrit : LpInclusion 𝕜 Ω 1 d q)
    (hdq : (d : ℝ≥0∞) < q) (n : ℕ) (r : ℝ≥0)
    [Fact (1 ≤ (r : ℝ≥0∞))] (hr : 1 ≤ r) (hn : n*r=d)
    (a : ℝ) (ha : 0 < a) (hα : a ≤ Morrey.exponent d q) :
    FullHolder 𝕜 Ω (n+1) r a := by
  letI : Fact (1 ≤ q) := ⟨(show (1 : ℝ≥0∞) ≤ d by exact_mod_cast hd).trans hdq.le⟩
  have H := fullHolder_of_lpInclusion hΩ hdq
    (critical_extension_inclusion_of_firstOrder hd hΩ q Hcrit n r hr hn)
  have H' := fullHolder_lower ha hα H
  simpa only [Nat.add_comm 1 n] using H'
end ExpandedFA.Sobolev.Higher

namespace ExpandedFA.Sobolev.Higher
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- Compact scalar cutoffs approaching one, with uniform zeroth and first derivative bounds. -/
lemma exists_uniform_first_order_cutoffs (d : ℕ) :
    ∃ (M : ℝ≥0) (χ : ℕ → Domain d → ℝ),
      (∀ n, ContDiff ℝ 1 (χ n)) ∧ (∀ n, HasCompactSupport (χ n)) ∧
      (∀ n x, ‖χ n x‖ ≤ 1) ∧ (∀ n x, ‖fderiv ℝ (χ n) x‖ ≤ M) ∧
      ∀ x, Tendsto (fun n => χ n x) atTop (𝓝 1) := by
  let b : ContDiffBump (0 : Domain d) := ⟨1, 2, by norm_num, by norm_num⟩
  have hb : ContDiff ℝ 1 (b : Domain d → ℝ) := b.contDiff
  obtain ⟨R, hR⟩ := (b.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (hb.continuous_fderiv one_ne_zero)
  let M : ℝ≥0 := R.toNNReal
  have hM (x : Domain d) : ‖fderiv ℝ (b : Domain d → ℝ) x‖ ≤ M :=
    (hR x).trans R.le_coe_toNNReal
  let a : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  have ha1 (n : ℕ) : a n ≤ 1 := by
    dsimp [a]
    exact inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hat : Tendsto a atTop (𝓝 0) := by
    simpa only [a, inv_eq_one_div] using tendsto_one_div_add_atTop_nhds_zero_nat
  let χ : ℕ → Domain d → ℝ := fun n x => b (a n • x)
  have hc (n : ℕ) : ContDiff ℝ 1 (χ n) :=
    hb.comp (contDiff_id.const_smul (a n))
  refine ⟨M, χ, hc, ?_, ?_, ?_, ?_⟩
  · intro n
    exact b.hasCompactSupport.comp_homeomorph
      (Homeomorph.smul (Units.mk0 (a n) (ha n).ne'))
  · intro n x
    simpa only [χ, Real.norm_of_nonneg b.nonneg] using b.le_one (x := a n • x)
  · intro n x
    have hd : fderiv ℝ (χ n) x =
        (fderiv ℝ (b : Domain d → ℝ) (a n • x)).comp
          (a n • ContinuousLinearMap.id ℝ (Domain d)) := by
      exact ((hb.differentiable (by simp) _).hasFDerivAt.comp x
        (a n • ContinuousLinearMap.id ℝ (Domain d)).hasFDerivAt).fderiv
    rw [hd]
    calc
      _ ≤ ‖fderiv ℝ (b : Domain d → ℝ) (a n • x)‖ *
          ‖a n • ContinuousLinearMap.id ℝ (Domain d)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (M : ℝ) * 1 := by
        gcongr
        · exact hM _
        · rw [norm_smul, Real.norm_of_nonneg (ha n).le]
          exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (ha n).le).trans
            (by simpa using ha1 n)
      _ = _ := mul_one _
  · intro x
    have h := b.continuous.continuousAt.tendsto.comp (hat.smul_const x)
    have hb0 : b 0 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
    simpa only [χ, Function.comp_def, zero_smul, hb0] using h

lemma smooth_full_estimate_of_compact {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p q : ℝ≥0∞} (hp : 1 ≤ p) (C : ℝ≥0)
    (H : ∀ (f : Domain d → 𝕜), ContDiff ℝ 1 f → HasCompactSupport f →
      eLpNorm f q volume ≤ (C : ℝ≥0∞) *
        (eLpNorm f p volume + eLpNorm (fderiv ℝ f) p volume)) :
    ∃ K : ℝ≥0, ∀ (f : Domain d → 𝕜), ContDiff ℝ 1 f →
      MemLp f p volume → MemLp (fderiv ℝ f) p volume →
      eLpNorm f q volume ≤ (K : ℝ≥0∞) *
        (eLpNorm f p volume + eLpNorm (fderiv ℝ f) p volume) := by
  obtain ⟨M, χ, hχ, hsχ, hbχ, hdχ, htχ⟩ := exists_uniform_first_order_cutoffs d
  refine ⟨C * (1 + M), ?_⟩
  intro f hf hfp hdfp
  let v : ℕ → Domain d → 𝕜 := fun n x => χ n x • f x
  have hv (n : ℕ) : ContDiff ℝ 1 (v n) := (hχ n).smul hf
  have hs (n : ℕ) : HasCompactSupport (v n) := (hsχ n).smul_right
  have hvp (n : ℕ) : eLpNorm (v n) p volume ≤ eLpNorm f p volume := by
    apply eLpNorm_mono (hv n).continuous.aestronglyMeasurable
    intro x
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right (hbχ n x) (norm_nonneg _)).trans_eq (one_mul _)
  have hdv (n : ℕ) : eLpNorm (fderiv ℝ (v n)) p volume ≤
      eLpNorm (fderiv ℝ f) p volume + (M : ℝ≥0∞) * eLpNorm f p volume := by
    have hpw (x : Domain d) : ‖fderiv ℝ (v n) x‖ ≤
        ‖fderiv ℝ f x‖ + (M : ℝ) * ‖f x‖ := by
      change ‖fderiv ℝ (fun y => χ n y • f y) x‖ ≤ _
      rw [fderiv_fun_smul ((hχ n).differentiable one_ne_zero x)
        (hf.differentiable one_ne_zero x)]
      calc
        _ ≤ ‖χ n x • fderiv ℝ f x‖ + ‖(fderiv ℝ (χ n) x).smulRight (f x)‖ := norm_add_le _ _
        _ ≤ _ := by
          apply add_le_add
          · rw [norm_smul]
            exact (mul_le_mul_of_nonneg_right (hbχ n x) (norm_nonneg _)).trans_eq (one_mul _)
          · exact (le_of_eq (ContinuousLinearMap.norm_smulRight_apply _ _)).trans
              (mul_le_mul_of_nonneg_right (hdχ n x) (norm_nonneg _))
    calc
      _ ≤ eLpNorm (fun x => ‖fderiv ℝ f x‖ + (M : ℝ) * ‖f x‖) p volume :=
        eLpNorm_mono (hv n |>.continuous_fderiv one_ne_zero |>.aestronglyMeasurable)
          (fun x => (hpw x).trans_eq (Real.norm_of_nonneg (by positivity)).symm)
      _ ≤ eLpNorm (fun x => ‖fderiv ℝ f x‖) p volume +
          eLpNorm (fun x => (M : ℝ) * ‖f x‖) p volume := eLpNorm_add_le hp
      _ = _ := by
        rw [show (fun x => (M : ℝ) * ‖f x‖) = (M : ℝ) • (fun x => ‖f x‖) from rfl,
          eLpNorm_const_smul, eLpNorm_norm _ hdfp.aestronglyMeasurable,
          eLpNorm_norm _ hfp.aestronglyMeasurable]
        simp
  apply Subcritical.eLpNorm_le_of_ae_tendsto_bounds
    (fun n => (hv n).continuous.aestronglyMeasurable) hf.continuous.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa [v] using (htχ x).smul_const (f x))
    tendsto_const_nhds
  intro n
  calc
    _ ≤ (C : ℝ≥0∞) * (eLpNorm (v n) p volume + eLpNorm (fderiv ℝ (v n)) p volume) := H _ (hv n) (hs n)
    _ ≤ (C : ℝ≥0∞) * (eLpNorm f p volume +
        (eLpNorm (fderiv ℝ f) p volume + (M : ℝ≥0∞) * eLpNorm f p volume)) := by gcongr; exact hvp n; exact hdv n
    _ ≤ (C : ℝ≥0∞) * ((1 + M : ℝ≥0∞) *
        (eLpNorm f p volume + eLpNorm (fderiv ℝ f) p volume)) := by
      gcongr
      calc
        _ = (1 + M : ℝ≥0∞) * eLpNorm f p volume + eLpNorm (fderiv ℝ f) p volume := by ring
        _ ≤ (1 + M : ℝ≥0∞) * eLpNorm f p volume +
            (1 + M : ℝ≥0∞) * eLpNorm (fderiv ℝ f) p volume := by
          apply add_le_add le_rfl
          calc
            eLpNorm (fderiv ℝ f) p volume = 1 * eLpNorm (fderiv ℝ f) p volume := (one_mul _).symm
            _ ≤ (1 + M : ℝ≥0∞) * eLpNorm (fderiv ℝ f) p volume :=
              mul_le_mul' (le_add_of_nonneg_right (bot_le : (0 : ℝ≥0∞) ≤ M)) le_rfl
        _ = _ := by ring
    _ = _ := by simp only [ENNReal.coe_mul, ENNReal.coe_add, ENNReal.coe_one, mul_assoc]

/-- A compact smooth full-norm inequality extends to the canonical whole-space graph.
Only the input exponent must be finite; the target exponent is arbitrary. -/
theorem lpInclusion_of_compact_full_estimate {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) (C : ℝ≥0)
    (H : ∀ (f : Domain d → 𝕜), ContDiff ℝ 1 f → HasCompactSupport f →
      eLpNorm f q volume ≤ (C : ℝ≥0∞) *
        (eLpNorm f p volume + eLpNorm (fderiv ℝ f) p volume)) :
    LpInclusion 𝕜 (⊤ : Opens (Domain d)) 1 p q := by
  obtain ⟨K, hK⟩ := smooth_full_estimate_of_compact Fact.out C H
  refine ⟨K * (1 + d), ?_⟩
  intro u
  have hcomp (β : DerivativeIndex d 1) :
      eLpNorm (u.val β) p volume ≤ ENNReal.ofReal ‖u‖ := by
    have hh : eLpNorm (u.val β) p
        (volume.restrict ((⊤ : Opens (Domain d)) : Set (Domain d))) ≤ ENNReal.ofReal ‖u‖ := by
      rw [← Lp.enorm_def, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (PiLp.norm_apply_le u.val β)
    simpa using hh
  obtain ⟨ρ, hρ⟩ := Smoothing.exists_mollifier d
  let a : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  have hat : Tendsto a atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨by simpa only [a, inv_eq_one_div] using tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall ha⟩
  let f : ℕ → Domain d → 𝕜 := fun n =>
    Smoothing.regularize ρ (a n) (u.val (zeroIndex d 1))
  have hf (n : ℕ) : ContDiff ℝ 1 (f n) :=
    (Smoothing.regularize_contDiff ρ hρ (ha n) _).of_le (by simp)
  have hcoord (n : ℕ) (j : Fin d) :
      (fun x => fderiv ℝ (f n) x (coordinateVector j)) =
        Smoothing.regularize ρ (a n) (u.val (Subcritical.firstIndex j)) :=
    Subcritical.regularize_derivative_top u ρ hρ (ha n) j
  have hg (n : ℕ) (j : Fin d) : MemLp
      (fun x => fderiv ℝ (f n) x (coordinateVector j)) p volume := by
    rw [hcoord]
    exact Smoothing.regularize_memLp ρ hρ (ha n) _
  have hdf (n : ℕ) : eLpNorm (fderiv ℝ (f n)) p volume ≤
      (d : ℝ≥0∞) * ENNReal.ofReal ‖u‖ := by
    calc
      _ ≤ ∑ j : Fin d, eLpNorm (fun x => fderiv ℝ (f n) x (coordinateVector j)) p volume :=
        Subcritical.eLpNorm_fderiv_le_sum Fact.out (hf n)
      _ ≤ ∑ j : Fin d, eLpNorm (u.val (Subcritical.firstIndex j)) p volume := by
        apply Finset.sum_le_sum
        intro j _
        rw [hcoord]
        exact Subcritical.regularize_eLpNorm_le _ ρ hρ (ha n)
      _ ≤ ∑ _j : Fin d, ENNReal.ofReal ‖u‖ := Finset.sum_le_sum fun j _ => hcomp _
      _ = _ := by simp
  have hb (n : ℕ) : eLpNorm (f n) q volume ≤
      ((K * (1 + d) : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal ‖u‖ := by
    calc
      _ ≤ (K : ℝ≥0∞) * (eLpNorm (f n) p volume + eLpNorm (fderiv ℝ (f n)) p volume) :=
        hK _ (hf n) (Smoothing.regularize_memLp ρ hρ (ha n) _)
          (Subcritical.fderiv_memLp_of_coordinates (hf n) (hg n))
      _ ≤ (K : ℝ≥0∞) * (ENNReal.ofReal ‖u‖ + (d : ℝ≥0∞) * ENNReal.ofReal ‖u‖) := by
        gcongr
        · exact (Subcritical.regularize_eLpNorm_le _ ρ hρ (ha n)).trans (hcomp _)
        · exact hdf n
      _ = _ := by simp only [ENNReal.coe_mul, ENNReal.coe_add, ENNReal.coe_one, ENNReal.coe_natCast]; ring
  have ht : Tendsto (fun n => eLpNorm (f n - (u.val (zeroIndex d 1) : Domain d → 𝕜)) p volume)
      atTop (𝓝 0) := by
    have h := (Smoothing.regularize_zeroExtend_tendsto hp ρ hρ (u.val (zeroIndex d 1))).comp hat
    simpa only [Function.comp_def, f, Smoothing.zeroExtend, Opens.coe_top, Set.indicator_univ] using h
  have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le Fact.out)
  obtain ⟨ns, _, hns⟩ := (tendstoInMeasure_of_tendsto_eLpNorm hp0 ht).exists_seq_tendsto_ae
  have hbound : eLpNorm (u.val (zeroIndex d 1)) q volume ≤
      ((K * (1 + d) : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal ‖u‖ :=
    Subcritical.eLpNorm_le_of_ae_tendsto_bounds
      (fun n => (hf (ns n)).continuous.aestronglyMeasurable)
      (by simpa using (Lp.memLp (u.val (zeroIndex d 1))).aestronglyMeasurable)
      hns tendsto_const_nhds (fun n => hb (ns n))
  constructor
  · have hh := hbound.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top)
    simpa only [MemLp, Opens.coe_top, Measure.restrict_univ] using hh
  · simpa using hbound

end ExpandedFA.Sobolev.Higher

namespace ExpandedFA.Sobolev.Higher
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The critical-order estimate used in the higher-order iteration. -/
def CriticalHolderProperty (𝕜 : Type) [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) : Prop :=
  ∀ (n : ℕ) (r : ℝ≥0) [Fact (1 ≤ (r : ℝ≥0∞))], 1 ≤ r → n*r=d →
    ∀ a : ℝ, 0 < a → a < 1 → FullHolder 𝕜 Ω (n+1) r a

theorem fullHolder_mono_order {m n : ℕ} {a : ℝ} (hnm : n ≤ m)
    (H : FullHolder 𝕜 Ω n p a) : FullHolder 𝕜 Ω m p a := by
  exact derivative_fullHolder (zeroIndex d m) (by simpa using hnm) H

/-- The complete positive-gap representative estimate, including p=∞. -/
theorem fullHolder_positive_gap (hΩ : FirstOrderExtensionDomain 𝕜 Ω)
    (hcrit : CriticalHolderProperty 𝕜 Ω)
    (m : ℕ) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hgap : a < (m : ℝ)-(d : ℝ)/p.toReal ∨
      (a = (m : ℝ)-(d : ℝ)/p.toReal ∧ a < 1)) :
    FullHolder 𝕜 Ω m p a := by
  by_cases hpTop : p=∞
  · have hm : 1 ≤ m := by
      rcases hgap with h | ⟨h,_⟩
      all_goals simp only [hpTop, ENNReal.toReal_top, div_zero, sub_zero] at *
      · have : (0 : ℝ) < m := ha.trans h
        exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast this.ne')
      · have : (0 : ℝ) < m := by linarith
        exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast this.ne')
    subst p
    exact fullHolder_mono_order hm (fullHolder_infinity_source hΩ ha ha1)
  · have hp1 : 1 ≤ p.toNNReal := by
      apply ENNReal.coe_le_coe.mp
      simpa only [ENNReal.coe_one, ENNReal.coe_toNNReal hpTop] using (Fact.out : 1 ≤ p)
    haveI : Fact (1 ≤ (p.toNNReal : ℝ≥0∞)) := ⟨by exact_mod_cast hp1⟩
    have H : FullHolder 𝕜 Ω m (p.toNNReal : ℝ≥0∞) a :=
      fullHolder_positive_gap_of_critical hΩ hcrit m p.toNNReal hp1 a ha ha1 hgap
    simpa only [ENNReal.coe_toNNReal hpTop] using H

/-- Apply the full remaining-order estimate to a fixed actual derivative. -/
theorem derivative_holder_of_critical (hΩ : FirstOrderExtensionDomain 𝕜 Ω)
    (hcrit : CriticalHolderProperty 𝕜 Ω) (m : ℕ) (β : DerivativeIndex d m)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hgap : a < (m : ℝ) - (∑ i, natIndex β i) - (d : ℝ) / p.toReal ∨
      (a = (m : ℝ) - (∑ i, natIndex β i) - (d : ℝ) / p.toReal ∧ a < 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SpaceValue 𝕜 d Ω m p,
      ∃ f : Domain d → 𝕜, ContinuousOn f (closure (Ω : Set (Domain d))) ∧
        (u.val β =ᵐ[volume.restrict (Ω : Set (Domain d))] f) ∧
        (∀ x ∈ closure (Ω : Set (Domain d)), ‖f x‖ ≤ C * ‖u‖) ∧
        ∀ x ∈ closure (Ω : Set (Domain d)), ∀ y ∈ closure (Ω : Set (Domain d)),
          ‖f x-f y‖ ≤ C * ‖u‖ * Morrey.euclideanNorm (x-y) ^ a := by
  have hdegree : (∑ i, natIndex β i) ≤ m := β.property
  let n := m-(∑ i, natIndex β i)
  have hβ : (∑ i, natIndex β i) + n ≤ m := by dsimp [n]; omega
  have hnR : (n : ℝ) = (m : ℝ) - (∑ i, natIndex β i) := by
    dsimp [n]
    rw [Nat.cast_sub hdegree]
  have H := fullHolder_positive_gap hΩ hcrit n a ha ha1 (by simpa only [hnR] using hgap)
  obtain ⟨C,hC,H'⟩ := derivative_fullHolder β hβ H
  refine ⟨C,hC,fun u => ?_⟩
  obtain ⟨f,hf,hr,hs,hh⟩ := H' u
  exact ⟨f,hf.continuousOn,hr,hs,hh⟩

/-- The integral-gap jet, once the critical-order analytic estimate on the
domain has been established. -/
theorem integral_holder_of_critical (hΩ : FirstOrderExtensionDomain 𝕜 Ω)
    (hcrit : CriticalHolderProperty 𝕜 Ω) {m k : ℕ} (hk : 1 ≤ k)
    (hgap : (m : ℝ) - (d : ℝ) / p.toReal = k)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ hk' : k-1 ≤ m,
      ∀ u : SpaceValue 𝕜 d Ω m p, HolderJet u (k-1) hk' a C := by
  have hkR : (k : ℝ) ≤ m := by
    have hdterm : 0 ≤ (d : ℝ)/p.toReal := div_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg
    exact hgap.symm.le.trans (sub_le_self _ hdterm)
  have hkm : k ≤ m := by exact_mod_cast hkR
  have hk' : k-1 ≤ m := by omega
  let n := m-(k-1)
  have hkn : k-1+n=m := by dsimp [n]; omega
  have hknR : (m : ℝ) = (k : ℝ)-1+(n : ℝ) := by
    have hh := congrArg (fun j : ℕ => (j : ℝ)) hkn
    rw [Nat.cast_add, Nat.cast_sub hk, Nat.cast_one] at hh
    exact hh.symm
  have hn : (n : ℝ)-(d : ℝ)/p.toReal=1 := by linear_combination hgap - hknR
  have H := fullHolder_positive_gap hΩ hcrit n a ha ha1.le (Or.inl (by rw [hn]; exact ha1))
  obtain ⟨C,hC,Hjet⟩ := holderJet_of_fullHolder hk' hkn.le H
  exact ⟨C,hC,hk',Hjet⟩

end ExpandedFA.Sobolev.Higher

namespace ExpandedFA.Sobolev.Higher
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}

/-- Critical higher-order Holder bounds on the whole space. The positive
 dimensional input is a genuine full-norm critical inequality, not a
 finite-volume lowering of the source exponent. -/
theorem wholeSpace_criticalHolder :
    CriticalHolderProperty 𝕜 (⊤ : Opens (Domain d)) := by
  intro n r _ hr hn a ha ha1
  by_cases hd0 : d=0
  · subst d
    have hr0 : r ≠ 0 := ne_of_gt (zero_lt_one.trans_le hr)
    have hn0 : n=0 := by
      have h : (n : ℝ≥0)=0 := (mul_eq_zero.mp (show (n : ℝ≥0)*r=0 by simpa only [Nat.cast_zero] using hn)).resolve_right hr0
      exact_mod_cast h
    subst n
    have hdp : (0 : ℝ≥0∞) < r := by exact_mod_cast (zero_lt_one.trans_le hr)
    have H : FullHolder 𝕜 (⊤ : Opens (Domain 0)) 1 r 1 := by
      simpa only [FullHolder, Morrey.Represents, Morrey.exponent, Nat.cast_zero,
        zero_div, sub_zero] using firstOrder_full_morrey
          (𝕜 := 𝕜) (Ω := (⊤ : Opens (Domain 0))) wholeSpace_extension (by simpa only [Nat.cast_zero] using hdp)
    exact fullHolder_lower ha ha1.le H
  · have hd : 1 ≤ d := by omega
    haveI : Fact (1 ≤ (d : ℝ≥0∞)) := ⟨by exact_mod_cast hd⟩
    by_cases hd1 : d=1
    · subst d
      exact fullHolder_critical_of_firstOrder (𝕜 := 𝕜) (by omega)
        wholeSpace_extension ∞ (by simpa only [Nat.cast_one] using (oneDimension_whole_infinity (𝕜 := 𝕜)))
        (ENNReal.natCast_lt_top 1) n r hr hn a ha (by simpa only [Morrey.exponent_top] using ha1.le)
    · obtain ⟨q,hqd,hqa,C,hC⟩ := critical_compact_smooth_for_holder
        (show 2 ≤ d by omega) a ha1
      have Hcrit : LpInclusion 𝕜 (⊤ : Opens (Domain d)) 1 d q :=
        lpInclusion_of_compact_full_estimate (by simp) C (hC 𝕜)
      exact fullHolder_critical_of_firstOrder hd wholeSpace_extension q Hcrit
        (by exact_mod_cast hqd) n r hr hn a ha hqa.le

/-- Both source domain alternatives supply the analytic estimates used by
higher-order iteration, with no additional geometric assumptions. -/
theorem extension_and_criticalHolder
    (hΩ : Ω = ⊤ ∨ (Bornology.IsBounded (Ω : Set (Domain d)) ∧
      FirstOrderExtensionDomain 𝕜 Ω)) :
    FirstOrderExtensionDomain 𝕜 Ω ∧ CriticalHolderProperty 𝕜 Ω := by
  rcases hΩ with rfl | ⟨hΩb,hΩ⟩
  · exact ⟨wholeSpace_extension,wholeSpace_criticalHolder⟩
  · exact ⟨hΩ,fun n r _ hr hn a ha ha1 => fullHolder_critical_bounded hΩb hΩ n r hr hn a ha ha1⟩

theorem integral_holder :
    Specs.ExpandedFA.Sobolev.HigherSobolevEmbeddings.IntegralHolder := by
  intro 𝕜 _ d m k Ω hΩ p _ hk hgap a ha ha1
  obtain ⟨hExt,hCrit⟩ := extension_and_criticalHolder hΩ
  exact integral_holder_of_critical hExt hCrit hk hgap a ha ha1

theorem derivative_holder_embeddings :
    Specs.ExpandedFA.Sobolev.HigherSobolevEmbeddings.DerivativeHolderEmbeddings := by
  intro 𝕜 _ d m Ω hΩ p _ β a ha ha1 hgap
  obtain ⟨hExt,hCrit⟩ := extension_and_criticalHolder hΩ
  exact derivative_holder_of_critical hExt hCrit m β a ha ha1 hgap

/-- All higher-order clauses, including the logarithmic critical example,
on the original scalar fields, exponents, orders and source domains. -/
theorem higher_embeddings :
    Specs.ExpandedFA.Sobolev.HigherSobolevEmbeddings.HigherEmbeddings :=
  ⟨subcritical_whole_space, subcritical_bounded_extension, critical_bounded_extension,
    nonintegral_holder, integral_holder, derivative_holder_embeddings,
    logarithmic_counterexample, c1_extension_domains⟩

end ExpandedFA.Sobolev.Higher

namespace ExpandedFA.Sobolev.Higher
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- In particular W⁰,∞ is L∞, with no dimension or domain restriction. -/
theorem same_exponent_inclusion :
    Specs.ExpandedFA.Sobolev.HigherSobolevEmbeddings.SameExponentInclusion := by
  intro 𝕜 _ d m Ω p _
  refine ⟨1, fun u => ⟨Lp.memLp _, ?_⟩⟩
  simp only [ENNReal.coe_one, one_mul]
  rw [← Lp.enorm_def, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (PiLp.norm_apply_le u.val (zeroIndex d m))

end ExpandedFA.Sobolev.Higher
