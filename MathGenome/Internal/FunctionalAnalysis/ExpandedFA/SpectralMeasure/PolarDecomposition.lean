import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.PolarDecomposition
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel

/-!
Polar decomposition for arbitrary real or complex Hilbert spaces.

The real-coefficient Catalan series defines the positive square root at the
closed norm boundary. Its norm bound gives positivity of its complement;
the Cauchy product gives the square identity. The series belongs to the
bicommutant of its argument. Two commuting positive roots agree by applying
the zero-quadratic-value kernel criterion to their sum.

The norm identity extends T along |T| to an isometry on the closure of its
range. Composition with the orthogonal projection extends this isometry by
zero. Equality on the dense range and on the kernel proves uniqueness and,
for normal T, commutation. No PVM or separability assumption is needed.
The series argument adapts the supplied unaccepted PositiveSqrtExists and
PositiveSqrtUniqueCalculus drafts; all helpers are proved locally here.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped InnerProductSpace ComplexOrder
open Finset Filter Topology
namespace ExpandedFA.SpectralMeasure.PolarDecomposition
universe u v w
namespace SquareRootSeries

abbrev coeff := Spec.rootCoeff

lemma coeff_nonneg (n : ℕ) : 0 ≤ coeff n := by unfold coeff Spec.rootCoeff; positivity

@[simp] lemma coeff_zero : coeff 0 = 1 / 2 := by norm_num [Spec.rootCoeff]

lemma coeff_recurrence (n : ℕ) :
    2 * coeff (n + 1) = ∑ ij ∈ antidiagonal n, coeff ij.1 * coeff ij.2 := by
  rw [coeff, Spec.rootCoeff, catalan_succ']
  push_cast
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  have h := Finset.mem_antidiagonal.mp hij
  simp only [Spec.rootCoeff, pow_succ]
  rw [show n = ij.1 + ij.2 from h.symm, pow_add]
  field_simp
  ring

lemma convolution_partial_le (n : ℕ) :
    (∑ k ∈ range n, ∑ ij ∈ antidiagonal k, coeff ij.1 * coeff ij.2) ≤
      (∑ k ∈ range n, coeff k) ^ 2 := by
  have hd : (↑(range n) : Set ℕ).PairwiseDisjoint antidiagonal := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact hij ((Finset.mem_antidiagonal.mp hp).symm.trans (Finset.mem_antidiagonal.mp hq))
  rw [← Finset.sum_biUnion hd]
  calc
    _ ≤ ∑ ij ∈ (range n ×ˢ range n), coeff ij.1 * coeff ij.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro ij hij
        obtain ⟨k, hk, h⟩ := Finset.mem_biUnion.mp hij
        have he := Finset.mem_antidiagonal.mp h
        simp only [Finset.mem_product, Finset.mem_range] at *
        omega
      · intro ij _ _
        exact mul_nonneg (coeff_nonneg _) (coeff_nonneg _)
    _ = _ := by rw [Finset.sum_product, sq, Finset.sum_mul_sum]

lemma partial_sum_le_one (n : ℕ) : (∑ k ∈ range n, coeff k) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hnon : 0 ≤ ∑ k ∈ range n, coeff k := Finset.sum_nonneg fun i _ => coeff_nonneg i
    have he : 2 * (∑ k ∈ range (n + 1), coeff k) =
        1 + ∑ k ∈ range n, ∑ ij ∈ antidiagonal k, coeff ij.1 * coeff ij.2 := by
      rw [Finset.sum_range_succ']
      simp only [mul_add, coeff_zero]
      rw [Finset.mul_sum]
      simp_rw [coeff_recurrence]
      ring
    have hc := convolution_partial_le n
    nlinarith

lemma summable_coeff : Summable coeff :=
  summable_of_sum_range_le coeff_nonneg partial_sum_le_one

lemma tsum_coeff : ∑' n, coeff n = 1 := by
  have hc := summable_coeff
  have hcn : Summable (fun n => ‖coeff n‖) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (coeff_nonneg _)] using hc
  have hp := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hcn hcn
  simp_rw [← coeff_recurrence] at hp
  rw [tsum_mul_left] at hp
  have hs := hc.sum_add_tsum_nat_add 1
  simp only [sum_range_one, coeff_zero] at hs
  nlinarith

variable {𝕜 : Type u} {R : Type v} [RCLike 𝕜]
  [NormedRing R] [NormedAlgebra 𝕜 R] [CompleteSpace R]

/-- Positive powers avoid any assumption that the identity has norm one. -/
def term (B : R) (n : ℕ) : R := (coeff n : 𝕜) • B ^ (n + 1)

omit [CompleteSpace R] in
lemma norm_term_le {B : R} (hB : ‖B‖ ≤ 1) (n : ℕ) :
    ‖term (𝕜 := 𝕜) B n‖ ≤ coeff n := by
  rw [term, norm_smul, RCLike.norm_ofReal, abs_of_nonneg (coeff_nonneg n)]
  calc
    _ ≤ coeff n * ‖B‖ ^ (n + 1) :=
      mul_le_mul_of_nonneg_left (norm_pow_le' B (by omega)) (coeff_nonneg n)
    _ ≤ coeff n * 1 := mul_le_mul_of_nonneg_left
      (pow_le_one₀ (norm_nonneg B) hB) (coeff_nonneg n)
    _ = _ := mul_one _

omit [CompleteSpace R] in
lemma summable_norm_term {B : R} (hB : ‖B‖ ≤ 1) :
    Summable (fun n => ‖term (𝕜 := 𝕜) B n‖) :=
  summable_coeff.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_term_le hB)

omit [CompleteSpace R] in
lemma convolution_term (B : R) (n : ℕ) :
    (∑ ij ∈ antidiagonal n, term (𝕜 := 𝕜) B ij.1 * term (𝕜 := 𝕜) B ij.2) =
      (2 : 𝕜) • term (𝕜 := 𝕜) B (n + 1) := by
  calc
    _ = ∑ ij ∈ antidiagonal n,
        ((coeff ij.1 * coeff ij.2 : ℝ) : 𝕜) • B ^ (n + 2) := by
      apply Finset.sum_congr rfl
      intro ij hij
      have he := Finset.mem_antidiagonal.mp hij
      simp only [term, smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_add,
        RCLike.ofReal_mul]
      rw [show ij.1 + 1 + (ij.2 + 1) = n + 2 by omega, mul_comm]
    _ = (2 : 𝕜) • term (𝕜 := 𝕜) B (n + 1) := by
      rw [← Finset.sum_smul, ← map_sum, ← coeff_recurrence]
      simp only [term, smul_smul, RCLike.ofReal_mul, Nat.add_assoc]
      rw [RCLike.ofReal_ofNat]

lemma series_equation {B : R} (hB : ‖B‖ ≤ 1) :
    let X := ∑' n, term (𝕜 := 𝕜) B n
    X * X = (2 : 𝕜) • X - B := by
  dsimp only
  have hn := summable_norm_term (𝕜 := 𝕜) hB
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hn hn]
  simp_rw [convolution_term]
  have hshift : Summable (fun n => term (𝕜 := 𝕜) B (n + 1)) :=
    hn.of_norm.comp_injective (add_left_injective 1)
  rw [hshift.tsum_const_smul]
  have hs := hn.of_norm.sum_add_tsum_nat_add 1
  simp only [sum_range_one] at hs
  have ht : term (𝕜 := 𝕜) B 0 = (1 / 2 : 𝕜) • B := by
    simp only [term, coeff_zero, Nat.zero_add, pow_one, RCLike.ofReal_div, RCLike.ofReal_one,
      RCLike.ofReal_ofNat]
  rw [ht] at hs
  rw [← hs, smul_add, smul_smul]
  norm_num

end SquareRootSeries
variable {𝕜 : Type u} {H : Type v} {K : Type w} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

omit [CompleteSpace H] in
lemma quadratic_le (A : H →L[𝕜] H) (x : H) :
    RCLike.re ⟪A x, x⟫_𝕜 ≤ ‖A‖ * ‖x‖ ^ 2 := by
  calc
    _ ≤ ‖⟪A x, x⟫_𝕜‖ := RCLike.re_le_norm _
    _ ≤ ‖A x‖ * ‖x‖ := norm_inner_le_norm _ _
    _ ≤ (‖A‖ * ‖x‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_right (A.le_opNorm x) (norm_nonneg _)
    _ = _ := by ring

omit [CompleteSpace H] in
lemma norm_le_one_of_positive_le_one (B : H →L[𝕜] H)
    (hB : 0 ≤ B) (hB1 : B ≤ 1) : ‖B‖ ≤ 1 := by
  have hp := ContinuousLinearMap.nonneg_iff_isPositive.mp hB
  rw [B.norm_eq_iSup_rayleighQuotient hp.isSymmetric]
  apply ciSup_le
  intro x
  have hlo := hp.re_inner_nonneg_left x
  have hhi := (ContinuousLinearMap.le_def.mp hB1).re_inner_nonneg_left x
  simp only [sub_apply, one_apply_eq_self,
    inner_sub_left, map_sub, inner_self_eq_norm_sq] at hhi
  change |RCLike.re ⟪B x, x⟫_𝕜 / ‖x‖ ^ 2| ≤ 1
  rw [abs_of_nonneg (div_nonneg hlo (sq_nonneg _))]
  exact div_le_one_of_le₀ (by linarith) (sq_nonneg _)

lemma positive_one_sub (X : H →L[𝕜] H)
    (hX : IsSelfAdjoint X) (hXn : ‖X‖ ≤ 1) : (1 - X).IsPositive := by
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨(IsSelfAdjoint.one _).sub hX, fun x => ?_⟩
  change 0 ≤ RCLike.re ⟪(1 - X) x, x⟫_𝕜
  simp only [sub_apply, one_apply_eq_self,
    inner_sub_left, map_sub, inner_self_eq_norm_sq]
  have h := quadratic_le X x
  nlinarith [sq_nonneg ‖x‖]

lemma positiveSqrt_properties (A : H →L[𝕜] H) (hA : A.IsPositive) :
    (Spec.positiveSqrtValue A).IsPositive ∧
      Spec.positiveSqrtValue A * Spec.positiveSqrtValue A = A := by
  by_cases hz : A = 0
  · subst A
    simp [Spec.positiveSqrtValue]
  have hc : 0 < ‖A‖ := norm_pos_iff.mpr hz
  let C : H →L[𝕜] H := ((‖A‖⁻¹ : ℝ) : 𝕜) • A
  have hCp : C.IsPositive := hA.smul_of_nonneg
    (RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr hc.le))
  have hCn : ‖C‖ ≤ 1 := by
    simp only [C, norm_smul, RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.mpr hc.le),
      inv_mul_cancel₀ hc.ne', le_refl]
  have hBp := positive_one_sub C hCp.isSelfAdjoint hCn
  let B : H →L[𝕜] H := 1 - C
  have hBn : ‖B‖ ≤ 1 := norm_le_one_of_positive_le_one _
    (ContinuousLinearMap.nonneg_iff_isPositive.mpr hBp)
    (sub_le_self _ (ContinuousLinearMap.nonneg_iff_isPositive.mpr hCp))
  let X : H →L[𝕜] H := ∑' n, SquareRootSeries.term (𝕜 := 𝕜) B n
  have hn := SquareRootSeries.summable_norm_term (𝕜 := 𝕜) hBn
  have hXn : ‖X‖ ≤ 1 := by
    calc
      _ ≤ ∑' n, ‖SquareRootSeries.term (𝕜 := 𝕜) B n‖ := norm_tsum_le_tsum_norm hn
      _ ≤ ∑' n, SquareRootSeries.coeff n :=
        hn.tsum_le_tsum (SquareRootSeries.norm_term_le hBn) SquareRootSeries.summable_coeff
      _ = 1 := SquareRootSeries.tsum_coeff
  have hXs : IsSelfAdjoint X := by
    change star X = X
    dsimp only [X]
    rw [tsum_star]
    apply tsum_congr
    intro n
    simp only [SquareRootSeries.term, star_smul, star_pow, show star B = B from hBp.isSelfAdjoint.star_eq,
      RCLike.star_def, RCLike.conj_ofReal]
  have hcomp : (1 - X) * (1 - X) = C := by
    have he := SquareRootSeries.series_equation (𝕜 := 𝕜) hBn
    change X * X = (2 : 𝕜) • X - B at he
    calc
      _ = 1 - (2 : 𝕜) • X + X * X := by rw [two_smul]; noncomm_ring
      _ = C := by rw [he]; dsimp only [B]; abel
  change (((Real.sqrt ‖A‖ : ℝ) : 𝕜) • (1 - X)).IsPositive ∧ _
  refine ⟨(positive_one_sub X hXs hXn).smul_of_nonneg
    (RCLike.ofReal_nonneg.mpr (Real.sqrt_nonneg _)), ?_⟩
  have hr : ((Real.sqrt ‖A‖ : ℝ) : 𝕜) * (Real.sqrt ‖A‖ : ℝ) = (‖A‖ : 𝕜) := by
    rw [← RCLike.ofReal_mul, Real.mul_self_sqrt (norm_nonneg A)]
  change ((Real.sqrt ‖A‖ : 𝕜) • (1 - X)) * ((Real.sqrt ‖A‖ : 𝕜) • (1 - X)) = A
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, hr, hcomp]
  dsimp only [C]
  rw [smul_smul, ← RCLike.ofReal_mul, mul_inv_cancel₀ hc.ne', RCLike.ofReal_one, one_smul]

omit [CompleteSpace H] in
lemma positiveSqrt_commutes (A T : H →L[𝕜] H) (h : Commute T A) :
    Commute T (Spec.positiveSqrtValue A) := by
  apply Commute.smul_right
  apply (Commute.one_right T).sub_right
  apply Commute.tsum_right
  intro n
  exact (((Commute.one_right T).sub_right (h.smul_right _)).pow_right (n + 1)).smul_right _


omit [CompleteSpace H] in
lemma positive_quadratic_kernel (A : H →L[𝕜] H) (hA : A.IsPositive)
    (x : H) (hx : RCLike.re ⟪x, A x⟫_𝕜 = 0) : A x = 0 := by
  let c : PreInnerProductSpace.Core 𝕜 H :=
    { inner := fun x y => ⟪x, A y⟫_𝕜
      conj_inner_symm := fun x y => by rw [inner_conj_symm, hA.inner_left_eq_inner_right]
      re_inner_nonneg := hA.re_inner_nonneg_right
      add_left := fun x y z => inner_add_left x y (A z)
      smul_left := fun x y r => inner_smul_left x (A y) r }
  have h := @InnerProductSpace.Core.inner_mul_inner_self_le 𝕜 H _ _ _ c (A x) x
  change ‖⟪A x, A x⟫_𝕜‖ * ‖⟪x, A (A x)⟫_𝕜‖ ≤
    RCLike.re ⟪A x, A (A x)⟫_𝕜 * RCLike.re ⟪x, A x⟫_𝕜 at h
  rw [hx, mul_zero] at h
  have hs : ‖⟪x, A (A x)⟫_𝕜‖ = ‖⟪A x, A x⟫_𝕜‖ := by
    rw [← hA.inner_left_eq_inner_right]
  rw [hs] at h
  have hn : ‖⟪A x, A x⟫_𝕜‖ = 0 := by nlinarith [norm_nonneg (⟪A x, A x⟫_𝕜)]
  exact inner_self_eq_zero.mp (norm_eq_zero.mp hn)

lemma commuting_positive_roots_eq (R S : H →L[𝕜] H)
    (hR : R.IsPositive) (hS : S.IsPositive)
    (hsq : R * R = S * S) (hcomm : Commute R S) : R = S := by
  let D : H →L[𝕜] H := R - S
  have hD : IsSelfAdjoint D := hR.isSelfAdjoint.sub hS.isSelfAdjoint
  have hprod : (R + S) * D = 0 := by
    dsimp only [D]
    have hm := hcomm.eq
    noncomm_ring [hsq, hm]
  have hkernel (y : H) (hy : (R + S) y = 0) : D y = 0 := by
    have hsum : RCLike.re ⟪y, R y⟫_𝕜 + RCLike.re ⟪y, S y⟫_𝕜 = 0 := by
      rw [← map_add, ← inner_add_right]
      change RCLike.re ⟪y, (R + S) y⟫_𝕜 = 0
      rw [hy, inner_zero_right, map_zero]
    have hr : RCLike.re ⟪y, R y⟫_𝕜 = 0 :=
      le_antisymm (by linarith [hS.re_inner_nonneg_right y]) (hR.re_inner_nonneg_right y)
    have hs : RCLike.re ⟪y, S y⟫_𝕜 = 0 :=
      le_antisymm (by linarith [hR.re_inner_nonneg_right y]) (hS.re_inner_nonneg_right y)
    simp only [D, sub_apply, positive_quadratic_kernel R hR y hr,
      positive_quadratic_kernel S hS y hs, sub_self]
  apply sub_eq_zero.mp
  ext x
  change D x = 0
  have hCy : (R + S) (D x) = 0 :=
    congrArg (fun T : H →L[𝕜] H => T x) hprod
  have hDy := hkernel (D x) hCy
  apply (inner_self_eq_zero (𝕜 := 𝕜)).mp
  calc
    ⟪D x, D x⟫_𝕜 = ⟪x, D (D x)⟫_𝕜 := hD.isSymmetric x (D x)
    _ = 0 := by rw [hDy, inner_zero_right]

lemma positiveSqrt_unique (A S : H →L[𝕜] H) (hA : A.IsPositive)
    (hS : S.IsPositive) (hs : S * S = A) : S = Spec.positiveSqrtValue A := by
  obtain ⟨hp, hsq⟩ := positiveSqrt_properties A hA
  apply commuting_positive_roots_eq S _ hS hp (hs.trans hsq.symm)
  apply positiveSqrt_commutes
  rw [← hs]
  exact (Commute.refl S).mul_right (Commute.refl S)

theorem modulus_properties : Spec.ModulusProperties.{u, v, w} := by
  intro 𝕜 H K _ _ _ _ _ _ _ T
  have hp := ContinuousLinearMap.isPositive_adjoint_comp_self T
  obtain ⟨hS, hsq⟩ := positiveSqrt_properties _ hp
  exact ⟨hS, hsq, fun S hS hsq => positiveSqrt_unique _ S hp hS hsq⟩

lemma modulus_norm (T : H →L[𝕜] K) (x : H) :
    ‖Spec.modulusValue T x‖ = ‖T x‖ := by
  obtain ⟨hS, hsq, _⟩ := modulus_properties 𝕜 H K T
  have he := congrArg (fun A : H →L[𝕜] H => A x) hsq
  change Spec.modulusValue T (Spec.modulusValue T x) = T.adjoint (T x) at he
  have hi : ⟪Spec.modulusValue T x, Spec.modulusValue T x⟫_𝕜 = ⟪T x, T x⟫_𝕜 := by
    rw [hS.inner_left_eq_inner_right, he, ContinuousLinearMap.adjoint_inner_right]
  have := congrArg RCLike.re hi
  simp only [inner_self_eq_norm_sq] at this
  nlinarith [norm_nonneg (Spec.modulusValue T x), norm_nonneg (T x)]

lemma modulus_ker (T : H →L[𝕜] K) : (Spec.modulusValue T).ker = T.ker := by
  ext x
  change Spec.modulusValue T x = 0 ↔ T x = 0
  rw [← norm_eq_zero, modulus_norm, norm_eq_zero]

lemma modulus_range_closure (T : H →L[𝕜] K) :
    (Spec.modulusValue T).range.topologicalClosure = T.ker.orthogonal := by
  have hp := (modulus_properties 𝕜 H K T).1
  have h := ContinuousLinearMap.orthogonal_ker (Spec.modulusValue T)
  rw [← ContinuousLinearMap.star_eq_adjoint, hp.isSelfAdjoint.star_eq, modulus_ker] at h
  exact h.symm


/-- The original map with codomain restricted to the closure of its range. -/
def closureRangeMap (A : H →L[𝕜] H) : H →ₗ[𝕜] A.range.topologicalClosure :=
  A.toLinearMap.codRestrict A.range.topologicalClosure
    (fun x => A.range.le_topologicalClosure ⟨x, rfl⟩)

omit [CompleteSpace H] in
lemma closureRangeMap_dense (A : H →L[𝕜] H) : DenseRange (closureRangeMap A) := by
  rw [DenseRange, Subtype.dense_iff]
  rw [← Set.range_comp]
  change closure (A.range : Set H) ⊆ closure (A.range : Set H)
  exact subset_rfl

/-- The extension is an isometry even when the original range is not closed. -/
def rangeIsometry (T : H →L[𝕜] K) :
    (Spec.modulusValue T).range.topologicalClosure →ₗᵢ[𝕜] K :=
  T.toLinearMap.extendOfIsometry
    (e := closureRangeMap (Spec.modulusValue T))
    (closureRangeMap_dense _) (fun x => (modulus_norm T x).symm)

lemma rangeIsometry_apply (T : H →L[𝕜] K) (x : H) :
    rangeIsometry T (closureRangeMap (Spec.modulusValue T) x) = T x :=
  LinearMap.extendOfIsometry_eq _ _ _ x

/-- Extend the isometry by zero on the orthogonal summand. -/
def polarFactor (T : H →L[𝕜] K) : H →L[𝕜] K :=
  (rangeIsometry T).toContinuousLinearMap.comp
    (Spec.modulusValue T).range.topologicalClosure.orthogonalProjectionOnto

lemma polarFactor_on_range (T : H →L[𝕜] K)
    (x : (Spec.modulusValue T).range.topologicalClosure) :
    polarFactor T x = rangeIsometry T x := by
  simp only [polarFactor, ContinuousLinearMap.comp_apply,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    LinearIsometry.coe_toContinuousLinearMap]

lemma polarFactor_comp_modulus (T : H →L[𝕜] K) :
    (polarFactor T).comp (Spec.modulusValue T) = T := by
  ext x
  exact (polarFactor_on_range T (closureRangeMap (Spec.modulusValue T) x)).trans
    (rangeIsometry_apply T x)

lemma polarFactor_ker (T : H →L[𝕜] K) : (polarFactor T).ker = T.ker := by
  have hM := modulus_range_closure T
  have hker : (polarFactor T).ker =
      (Spec.modulusValue T).range.topologicalClosure.orthogonal := by
    ext x
    change rangeIsometry T ((Spec.modulusValue T).range.topologicalClosure.orthogonalProjectionOnto x) = 0 ↔ _
    rw [← (rangeIsometry T).map_zero, (rangeIsometry T).injective.eq_iff]
    exact Submodule.orthogonalProjectionOnto_eq_zero_iff
  rw [hker, hM, Submodule.orthogonal_orthogonal]

lemma polarFactor_isPartialIsometry (T : H →L[𝕜] K) :
    Spec.IsPartialIsometryValue (polarFactor T) := by
  intro x hx
  rw [polarFactor_ker] at hx
  have hx' : x ∈ (Spec.modulusValue T).range.topologicalClosure :=
    (modulus_range_closure T).symm ▸ hx
  rw [polarFactor_on_range T ⟨x, hx'⟩, (rangeIsometry T).norm_map]
  rfl

lemma rangeIsometry_range (T : H →L[𝕜] K) :
    (rangeIsometry T).toLinearMap.range = T.range.topologicalClosure := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, rfl⟩ := hy
    have hx : DenseRange (closureRangeMap (Spec.modulusValue T)) := closureRangeMap_dense _
    refine hx.induction_on (p := fun z => rangeIsometry T z ∈ T.range.topologicalClosure)
      x (T.range.isClosed_topologicalClosure.preimage (rangeIsometry T).continuous) ?_
    intro z
    rw [rangeIsometry_apply]
    exact T.range.le_topologicalClosure ⟨z, rfl⟩
  · apply T.range.topologicalClosure_minimal
    · rintro y ⟨x, rfl⟩
      exact ⟨closureRangeMap (Spec.modulusValue T) x, rangeIsometry_apply T x⟩
    · exact (rangeIsometry T).isometry.isClosedEmbedding.isClosed_range

lemma polarFactor_range (T : H →L[𝕜] K) :
    (polarFactor T).range = T.range.topologicalClosure := by
  rw [← rangeIsometry_range T]
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  · rintro y ⟨x, rfl⟩
    exact ⟨x, polarFactor_on_range T x⟩


lemma ext_of_comp_modulus_eq (T : H →L[𝕜] K) {U V : H →L[𝕜] K}
    (he : U.comp (Spec.modulusValue T) = V.comp (Spec.modulusValue T))
    (hz : ∀ x ∈ T.ker, U x = V x) : U = V := by
  have hr : ∀ x ∈ (Spec.modulusValue T).range.topologicalClosure, U x = V x := by
    have hle : (Spec.modulusValue T).range ≤ (U - V).ker := by
      rintro x ⟨y, rfl⟩
      change U (Spec.modulusValue T y) - V (Spec.modulusValue T y) = 0
      exact sub_eq_zero.mpr (congrArg (fun A : H →L[𝕜] K => A y) he)
    have hle' := (Spec.modulusValue T).range.topologicalClosure_minimal hle (U - V).isClosed_ker
    intro x hx
    exact sub_eq_zero.mp (hle' hx)
  let : CompleteSpace T.ker := T.isClosed_ker.completeSpace_coe
  ext x
  have hp := hz (T.ker.starProjection x) (T.ker.starProjection_apply_mem x)
  have hq := hr (x - T.ker.starProjection x)
    ((modulus_range_closure T).symm ▸ T.ker.sub_starProjection_mem_orthogonal x)
  have hx : x = T.ker.starProjection x + (x - T.ker.starProjection x) := by abel
  conv_lhs => rw [hx, map_add, hp, hq, ← map_add, ← hx]

lemma polarFactor_spec (T : H →L[𝕜] K) : Spec.IsPolarFactorValue T (polarFactor T) :=
  ⟨polarFactor_ker T, polarFactor_isPartialIsometry T,
    polarFactor_range T, polarFactor_comp_modulus T⟩

theorem polar_decomposition : Spec.PolarDecomposition.{u, v, w} := by
  intro 𝕜 H K _ _ _ _ _ _ _ T
  refine ⟨polarFactor T, polarFactor_spec T, ?_⟩
  intro U hU
  apply ext_of_comp_modulus_eq T (hU.2.2.2.trans (polarFactor_comp_modulus T).symm)
  intro x hx
  have hu : U x = 0 := by
    change x ∈ U.ker
    rwa [hU.1]
  have hv : polarFactor T x = 0 := by
    change x ∈ (polarFactor T).ker
    rwa [polarFactor_ker]
  exact hu.trans hv.symm

lemma normal_commutes_modulus (T : H →L[𝕜] H) (hT : IsStarNormal T) :
    Commute T (Spec.modulusValue T) := by
  apply positiveSqrt_commutes
  change Commute T (star T * T)
  exact (hT.star_comm_self.symm).mul_right (Commute.refl T)

theorem normal_commutation : Spec.NormalCommutation.{u, v} := by
  intro 𝕜 H _ _ _ _ T hT U hU
  have hs := normal_commutes_modulus T hT
  refine ⟨hs, ?_⟩
  change T.comp U = U.comp T
  apply ext_of_comp_modulus_eq T
  · ext x
    have he (y : H) : U (Spec.modulusValue T y) = T y :=
      congrArg (fun A : H →L[𝕜] H => A y) hU.2.2.2
    have hc (y : H) : T (Spec.modulusValue T y) = Spec.modulusValue T (T y) :=
      congrArg (fun A : H →L[𝕜] H => A y) hs.eq
    change T (U (Spec.modulusValue T x)) = U (T (Spec.modulusValue T x))
    rw [he, hc, he]
  · intro x hx
    have htx : T x = 0 := hx
    have hux : U x = 0 := by
      change x ∈ U.ker
      rwa [hU.1]
    simp [htx, hux]

theorem invertible_unitary : Spec.InvertibleUnitary.{u, v, w} := by
  intro 𝕜 H K _ _ _ _ _ _ _ T U hU
  have hk : U.ker = ⊥ := by
    rw [hU.1]
    exact LinearMap.ker_eq_bot.mpr T.injective
  have hn : ∀ x, ‖U x‖ = ‖x‖ := by
    intro x
    apply hU.2.1 x
    rw [hk, Submodule.bot_orthogonal_eq_top]
    trivial
  let I : H →ₗᵢ[𝕜] K := ⟨U.toLinearMap, hn⟩
  have hr : U.range = ⊤ := by
    rw [hU.2.2.1]
    have htr : T.toContinuousLinearMap.range = ⊤ := LinearMap.range_eq_top.mpr T.surjective
    rw [htr]
    exact top_unique (Submodule.le_topologicalClosure _)
  have hi : Function.Surjective I := LinearMap.range_eq_top.mp hr
  exact ⟨LinearIsometryEquiv.ofSurjective I hi, rfl⟩

theorem nonunitary_example : Spec.NonunitaryExample.{u} := by
  intro 𝕜 _
  refine ⟨0, 0, ?_, ?_⟩
  · refine ⟨rfl, ?_, ?_, ?_⟩
    · intro x hx
      have hx' : x = 0 := by simpa using hx
      simp [hx']
    · simp
    · simp
  · rintro ⟨e, he⟩
    have h : e (1 : 𝕜) = 0 := congrArg (fun A : 𝕜 →L[𝕜] 𝕜 => A 1) he
    have hn := e.norm_map (1 : 𝕜)
    simp [h] at hn

end ExpandedFA.SpectralMeasure.PolarDecomposition
