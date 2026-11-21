import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.BanachLimits
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.InvariantHahnBanach
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01SequenceSpaces
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Banach limits, including a choice extending Cesàro convergence.
First construct a positive unital shift-invariant functional by invariant
Hahn–Banach. Composing it with the Cesàro operator gives the additional choice.
Positivity and shift invariance give the ordinary liminf/limsup bounds. -/

noncomputable section
open Filter
open scoped Topology ENNReal
namespace ExpandedFA.P1.BanachLimits
open C01SequenceSpaces

local notation "B" => SequenceLInfinity ℝ

lemma coordinate_abs_le (x : B) (n : ℕ) : |x n| ≤ ‖x‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero x n

@[simp] lemma leftShift_apply (x : B) (n : ℕ) : leftShift x n = x (n + 1) := rfl

lemma shift_pow_apply (k : ℕ) (x : B) (n : ℕ) :
    (leftShift ^ k) x n = x (n + k) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    change (leftShift ^ k) x (n + 1) = _
    rw [ih]
    exact congrArg (fun j => x j) (by omega)

lemma shift_pow_norm_le (k : ℕ) (x : B) : ‖(leftShift ^ k) x‖ ≤ ‖x‖ := by
  apply lp.norm_le_of_forall_le (norm_nonneg _)
  intro n
  rw [shift_pow_apply]
  exact coordinate_abs_le x _

/-- Constants embedded in the very same sequence space as the conclusion. -/
def constant : ℝ →ₗ[ℝ] B where
  toFun a := a • (1 : B)
  map_add' a b := add_smul a b _
  map_smul' a b := by simp [mul_smul]

@[simp] lemma constant_apply (a : ℝ) (n : ℕ) : constant a n = a := by
  change a * (1 : ℝ) = a
  exact mul_one a

lemma shift_pow_constant (k : ℕ) (a : ℝ) : (leftShift ^ k) (constant a) = constant a := by
  apply lp.ext
  funext n
  simp [shift_pow_apply]

lemma norm_sub_constant_le (x : B) (hx : ∀ n, 0 ≤ x n) :
    ‖constant ‖x‖ - x‖ ≤ ‖x‖ := by
  apply lp.norm_le_of_forall_le (norm_nonneg _)
  intro n
  change |constant ‖x‖ n - x n| ≤ ‖x‖
  rw [constant_apply, abs_le]
  have h := (abs_le.mp (coordinate_abs_le x n)).2
  constructor <;> linarith [hx n]

/-- The algebraic invariant extension of the constant-value functional is
contractive. Its normalization forces positivity. -/
lemma exists_invariant_functional :
    ∃ F : B →L[ℝ] ℝ,
      (∀ x, |F x| ≤ ‖x‖) ∧
      (∀ a, F (constant a) = a) ∧
      (∀ x, (∀ n, 0 ≤ x n) → 0 ≤ F x) ∧
      (∀ x, F (leftShift x) = F x) := by
  let S := (Submonoid.powers leftShift).toSubsemigroup
  let Y := LinearMap.range constant
  let f : Y →ₗ[ℝ] ℝ :=
    { toFun := fun y => y.val 0
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hY : ∀ A ∈ S, ∀ y ∈ Y, A y ∈ Y := by
    intro A hA y hy
    obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff A leftShift).mp hA
    obtain ⟨a, rfl⟩ := hy
    exact ⟨a, shift_pow_constant k a |>.symm⟩
  have hcomm : ∀ A ∈ S, ∀ D ∈ S, Commute A D := by
    intro A hA D hD
    obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff A leftShift).mp hA
    obtain ⟨j, rfl⟩ := (Submonoid.mem_powers_iff D leftShift).mp hD
    exact (Commute.refl leftShift).pow_pow k j
  have hp : IsSublinear (fun x : B => ‖x‖) := by
    refine ⟨norm_add_le, ?_⟩
    intro t ht x
    change ‖t • x‖ = t * ‖x‖
    rw [norm_smul, Real.norm_of_nonneg ht]
  obtain ⟨G, hext, hbound, hinv⟩ := invariant_hahn_banach (fun x : B => ‖x‖) hp
    S hcomm (by
      intro A hA x
      obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff A leftShift).mp hA
      exact shift_pow_norm_le k x) Y hY f (by
      intro y
      exact (le_abs_self _).trans (coordinate_abs_le y.val 0)) (by
      intro A hA y
      obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff A leftShift).mp hA
      obtain ⟨a, ha⟩ := y.property
      change ((leftShift ^ k) y.val) 0 = y.val 0
      rw [← ha, shift_pow_constant])
  have habs : ∀ x, |G x| ≤ ‖x‖ := by
    intro x
    rw [abs_le]
    have h := hbound (-x)
    simp only [map_neg, norm_neg] at h
    exact ⟨by linarith, hbound x⟩
  let F := G.mkContinuous 1 (by intro x; simpa using habs x)
  have hconst : ∀ a, F (constant a) = a := by
    intro a
    exact (hext ⟨constant a, ⟨a, rfl⟩⟩).trans (constant_apply a 0)
  refine ⟨F, habs, hconst, ?_, ?_⟩
  · intro x hx
    have h := habs (constant ‖x‖ - x)
    change |F (constant ‖x‖ - x)| ≤ _ at h
    rw [map_sub, hconst] at h
    have h' := norm_sub_constant_le x hx
    have := (le_abs_self (‖x‖ - F x)).trans (h.trans h')
    linarith
  · intro x
    exact hinv leftShift (Submonoid.mem_powers _) x

/-- A positive normalized invariant functional respects eventual upper and
lower bounds: move the entire sequence past the exceptional finite head. -/
lemma eventual_bounds (F : B →ₗ[ℝ] ℝ)
    (hc : ∀ a, F (constant a) = a)
    (hp : ∀ x, (∀ n, 0 ≤ x n) → 0 ≤ F x)
    (hs : ∀ x, F (leftShift x) = F x) (x : B) (a : ℝ) :
    ((∀ᶠ n in atTop, x n ≤ a) → F x ≤ a) ∧
    ((∀ᶠ n in atTop, a ≤ x n) → a ≤ F x) := by
  have hpow (k : ℕ) (y : B) : F ((leftShift ^ k) y) = F y := by
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ', Module.End.mul_apply, hs, ih]
  constructor
  · intro h
    obtain ⟨N, hN⟩ := eventually_atTop.mp h
    have hpos := hp (constant a - (leftShift ^ N) x) (by
      intro n
      change 0 ≤ constant a n - (leftShift ^ N) x n
      rw [constant_apply, shift_pow_apply]
      exact sub_nonneg.mpr (hN (n + N) (by omega)))
    rw [map_sub, hc, hpow] at hpos
    linarith
  · intro h
    obtain ⟨N, hN⟩ := eventually_atTop.mp h
    have hpos := hp ((leftShift ^ N) x - constant a) (by
      intro n
      change 0 ≤ (leftShift ^ N) x n - constant a n
      rw [constant_apply, shift_pow_apply]
      exact sub_nonneg.mpr (hN (n + N) (by omega)))
    rw [map_sub, hc, hpow] at hpos
    linarith

lemma liminf_limsup_bounds (F : B →ₗ[ℝ] ℝ)
    (hc : ∀ a, F (constant a) = a)
    (hp : ∀ x, (∀ n, 0 ≤ x n) → 0 ≤ F x)
    (hs : ∀ x, F (leftShift x) = F x) (x : B) :
    liminf (fun n => x n) atTop ≤ F x ∧ F x ≤ limsup (fun n => x n) atTop := by
  constructor
  · apply liminf_le_of_le
      (show IsBoundedUnder (· ≥ ·) atTop (fun n => x n) from
        isBoundedUnder_of ⟨-‖x‖, fun n => (abs_le.mp (coordinate_abs_le x n)).1⟩)
    intro a ha
    exact (eventual_bounds F hc hp hs x a).2 ha
  · apply le_limsup_of_le
      (show IsBoundedUnder (· ≤ ·) atTop (fun n => x n) from
        isBoundedUnder_of ⟨‖x‖, fun n => (abs_le.mp (coordinate_abs_le x n)).2⟩)
    intro a ha
    exact (eventual_bounds F hc hp hs x a).1 ha

lemma extends_limit (F : B →ₗ[ℝ] ℝ)
    (hc : ∀ a, F (constant a) = a)
    (hp : ∀ x, (∀ n, 0 ≤ x n) → 0 ≤ F x)
    (hs : ∀ x, F (leftShift x) = F x) (x : B) (a : ℝ)
    (hx : Tendsto (fun n => x n) atTop (𝓝 a)) : F x = a := by
  obtain ⟨hl, hu⟩ := liminf_limsup_bounds F hc hp hs x
  rw [hx.liminf_eq] at hl
  rw [hx.limsup_eq] at hu
  exact le_antisymm hu hl

lemma cesaroMean_abs_le (x : B) (n : ℕ) : |cesaroMean x n| ≤ ‖x‖ := by
  have hsum : |∑ j ∈ Finset.range n, x j| ≤ (n : ℝ) * ‖x‖ := by
    calc
      _ ≤ ∑ j ∈ Finset.range n, |x j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.range n, ‖x‖ := Finset.sum_le_sum fun j _ => coordinate_abs_le x j
      _ = (n : ℝ) * ‖x‖ := by simp [nsmul_eq_mul]
  unfold cesaroMean
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
  by_cases hn : n = 0
  · simp [hn]
  · calc
      _ ≤ (n : ℝ)⁻¹ * ((n : ℝ) * ‖x‖) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = ‖x‖ := by rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn), one_mul]

/-- Cesàro averaging as an operator on the canonical bounded sequence space. -/
def cesaro : B →ₗ[ℝ] B where
  toFun x := ⟨cesaroMean x, memℓp_infty
    ⟨‖x‖, by rintro _ ⟨n, rfl⟩; exact cesaroMean_abs_le x n⟩⟩
  map_add' x y := by
    apply lp.ext
    funext n
    change cesaroMean (x + y) n = cesaroMean x n + cesaroMean y n
    change (n : ℝ)⁻¹ * (∑ j ∈ Finset.range n, (x j + y j)) = _
    rw [Finset.sum_add_distrib, mul_add]
    rfl
  map_smul' a x := by
    apply lp.ext
    funext n
    change cesaroMean (a • x) n = a * cesaroMean x n
    simp only [cesaroMean, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    ring

@[simp] lemma cesaro_apply (x : B) (n : ℕ) : cesaro x n = cesaroMean x n := rfl

lemma cesaro_norm_le (x : B) : ‖cesaro x‖ ≤ ‖x‖ :=
  lp.norm_le_of_forall_le (norm_nonneg _) (cesaroMean_abs_le x)

lemma cesaro_nonneg (x : B) (hx : ∀ n, 0 ≤ x n) : ∀ n, 0 ≤ cesaro x n := by
  intro n
  apply mul_nonneg (by positivity : 0 ≤ (n : ℝ)⁻¹)
  exact Finset.sum_nonneg fun j _ => hx j

/-- The error from shifting before averaging is just the endpoint difference. -/
lemma cesaro_shift_difference (x : B) (n : ℕ) :
    cesaroMean (leftShift x) n - cesaroMean x n = (n : ℝ)⁻¹ * (x n - x 0) := by
  have h := (Finset.sum_range_succ' (fun j => x j) n).symm.trans
    (Finset.sum_range_succ (fun j => x j) n)
  simp only [cesaroMean, leftShift_apply]
  rw [← mul_sub]
  congr 1
  linarith only [h]

lemma cesaro_shift_difference_tendsto (x : B) :
    Tendsto (fun n => (cesaro (leftShift x) - cesaro x) n) atTop (𝓝 0) := by
  have h : ∀ n, |x n - x 0| ≤ 2 * ‖x‖ := by
    intro n
    calc
      _ ≤ |x n| + |x 0| := abs_sub _ _
      _ ≤ ‖x‖ + ‖x‖ := add_le_add (coordinate_abs_le x n) (coordinate_abs_le x 0)
      _ = _ := by ring
  have ht := bdd_le_mul_tendsto_zero' (2 * ‖x‖) (Eventually.of_forall h)
    (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)))
  convert ht using 1
  funext n
  change cesaroMean (leftShift x) n - cesaroMean x n = _
  rw [cesaro_shift_difference, mul_comm]
  rfl

/-- Any functional extending the ordinary limit and normalized on constants
cannot be given by an ℓ¹ coordinate pairing. -/
lemma no_coordinate_representation (L : B →ₗ[ℝ] ℝ)
    (hext : ∀ (x : B) (a : ℝ), Tendsto (fun n => x n) atTop (𝓝 a) → L x = a) :
    ¬ ∃ a : SequenceLp ℝ 1, ∀ x : B, L x = ∑' n, a n * x n := by
  have he (j : ℕ) : L (lp.single ∞ j (1 : ℝ)) = 0 := by
    apply hext
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop j] with n hn
    simp [lp.single_apply, ne_of_gt hn]
  have hone : L (1 : B) = 1 := hext _ _ (by simp)
  rintro ⟨a, ha⟩
  have haz (j : ℕ) : a j = 0 := by
    have h := ha (lp.single ∞ j (1 : ℝ))
    simpa [he, lp.single_apply, Pi.single_apply, eq_comm] using h.symm
  have h := ha 1
  simp only [haz, zero_mul, tsum_zero] at h
  exact one_ne_zero (hone.symm.trans h)

/-- The complete corollary: one Banach limit can be chosen to extend all
convergent Cesàro means, while retaining every ordinary Banach-limit property. -/
theorem banach_limits : Spec.BanachLimitsType := by
  obtain ⟨F, hbound, hconst, hpos, hshift⟩ := exists_invariant_functional
  have hext := extends_limit F.toLinearMap hconst hpos hshift
  let G : B →ₗ[ℝ] ℝ := F.toLinearMap.comp cesaro
  have hGbound : ∀ x, ‖G x‖ ≤ 1 * ‖x‖ := by
    intro x
    exact (hbound (cesaro x)).trans (by simpa using cesaro_norm_le x)
  let L := G.mkContinuous 1 hGbound
  have hces : ∀ (x : B) (a : ℝ), Tendsto (cesaroMean x) atTop (𝓝 a) → L x = a := by
    intro x a hx
    exact hext (cesaro x) a hx
  have hlim : ∀ (x : B) (a : ℝ), Tendsto (fun n => x n) atTop (𝓝 a) → L x = a := by
    intro x a hx
    exact hces x a hx.cesaro
  have hc : ∀ a, L (constant a) = a := by
    intro a
    apply hlim
    simpa only [constant_apply] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => a) atTop (𝓝 a))
  have hp : ∀ x, (∀ n, 0 ≤ x n) → 0 ≤ L x := by
    intro x hx
    exact hpos (cesaro x) (cesaro_nonneg x hx)
  have hs : ∀ x, L (leftShift x) = L x := by
    intro x
    have h := hext (cesaro (leftShift x) - cesaro x) 0 (cesaro_shift_difference_tendsto x)
    rw [map_sub] at h
    change F (cesaro (leftShift x)) - F (cesaro x) = 0 at h
    exact sub_eq_zero.mp h
  refine ⟨L, hp, ?_, hlim, hs,
    liminf_limsup_bounds L.toLinearMap hc hp hs, hces,
    no_coordinate_representation L.toLinearMap hlim⟩
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound L zero_le_one hGbound
  · have hone : L (1 : B) = 1 := hlim _ _ (by simp)
    have h := L.le_opNorm (1 : B)
    simpa only [hone, norm_one, mul_one] using h

end ExpandedFA.P1.BanachLimits
