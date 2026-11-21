import MathGenome.Internal.LinearPDE.P201Specs.Common.QuadraticClassification
import MathGenome.Internal.LinearPDE.P201.Common.Operators
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.LinearAlgebra.QuadraticForm.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open scoped BigOperators
namespace P201.QuadraticClassification
open P201Specs P201Specs.Operators P201Specs.QuadraticClassification

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Restriction to an affine line is the usual quadratic polynomial. -/
lemma quadratic_on_line (Q : QuadraticForm ℝ E) (x y : E) (t : ℝ) :
    Q (x + t • y) = Q y * (t * t) + QuadraticMap.polar Q x y * t + Q x := by
  rw [QuadraticMap.map_add Q x (t • y), Q.map_smul, Q.polar_smul_right]
  simp only [smul_eq_mul]
  ring

/-- Opposite signs on independent vectors force a nonzero null vector. -/
lemma no_opposite_signs (Q : QuadraticForm ℝ E) (hQ : Q.Anisotropic)
    {x y : E} (hx : 0 < Q x) (hy : Q y < 0) : False := by
  let b := QuadraticMap.polar Q x y
  have hd : 0 < discrim (Q y) b (Q x) := by
    dsimp [discrim]
    nlinarith [sq_nonneg b, mul_neg_of_neg_of_pos hy hx]
  obtain ⟨t, ht⟩ := exists_quadratic_eq_zero (ne_of_lt hy)
    ⟨Real.sqrt (discrim (Q y) b (Q x)), by
      nlinarith [Real.sq_sqrt hd.le]⟩
  have hz : Q (x + t • y) = 0 := by rw [quadratic_on_line]; exact ht
  have hv : x + t • y = 0 := hQ _ hz
  have heq : x = (-t) • y := by
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_left hv
  have hnonpos : Q x ≤ 0 := by
    rw [heq, Q.map_smul]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg _) hy.le
  linarith

lemma anisotropic_iff_definite (Q : QuadraticForm ℝ E) :
    Q.Anisotropic ↔ Q.PosDef ∨ (-Q).PosDef := by
  classical
  refine ⟨?_, ?_⟩
  · intro hQ
    by_cases hp : Q.PosDef
    · exact Or.inl hp
    · right
      change ∀ x, x ≠ 0 → 0 < (-Q) x
      have hn : ∃ x, x ≠ 0 ∧ ¬ 0 < Q x := by
        simpa only [QuadraticMap.PosDef, not_forall, exists_prop] using hp
      obtain ⟨x, hx, hqx⟩ := hn
      have hneg : Q x < 0 := lt_of_le_of_ne (le_of_not_gt hqx)
        (fun h => hx (hQ x h))
      intro y hy
      have hny : Q y ≠ 0 := fun h => hy (hQ y h)
      have hle : Q y ≤ 0 := le_of_not_gt (fun h => no_opposite_signs Q hQ h hneg)
      change 0 < -Q y
      exact neg_pos.mpr (lt_of_le_of_ne hle hny)
  · rintro (hp | hn)
    · exact hp.anisotropic
    · intro x hx
      by_contra h
      have := hn x h
      change 0 < -Q x at this
      simp [hx] at this

theorem matrixFormRealization {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (ξ : Space n) :
    matrixForm a ξ = quadraticPrincipal a ξ := by
  simp only [matrixForm, LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toBilin_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr, quadraticPrincipal]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem ellipticIffDefinite : ellipticIffDefiniteStatement := by
  intro n hn a ha
  have h := anisotropic_iff_definite (matrixForm a)
  simp only [QuadraticMap.Anisotropic, QuadraticMap.PosDef,
    neg_apply, matrixFormRealization, neg_pos] at h
  constructor
  · intro he
    apply h.mp
    intro ξ hξ
    by_contra hne
    exact he ξ hne (by simp [hξ])
  · intro hd ξ hξ hz
    have hz' : quadraticPrincipal a ξ = 0 := neg_eq_zero.mp hz
    have := h.mpr hd ξ hz'
    exact hξ this

/-- A positive-leading quadratic with a negative value has exactly two real roots. -/
lemma two_roots_of_negative_value {a b c t : ℝ} (ha : 0 < a)
    (ht : a * (t * t) + b * t + c < 0) :
    ∃ r₁ r₂ : ℝ, r₁ < r₂ ∧ ∀ τ : ℝ,
      a * (τ * τ) + b * τ + c = 0 ↔ τ = r₁ ∨ τ = r₂ := by
  have hd : 0 < discrim a b c := by
    have hm := mul_neg_of_pos_of_neg ha ht
    have hs := sq_nonneg (2 * a * t + b)
    dsimp [discrim]
    nlinarith
  let d := Real.sqrt (discrim a b c)
  have hdpos : 0 < d := Real.sqrt_pos.mpr hd
  have hdsq : discrim a b c = d * d := by
    dsimp [d]
    nlinarith [Real.sq_sqrt hd.le]
  refine ⟨(-b - d) / (2 * a), (-b + d) / (2 * a), ?_, ?_⟩
  · apply (div_lt_div_iff_of_pos_right (by positivity : 0 < 2 * a)).mpr
    linarith
  · intro τ
    rw [quadratic_eq_zero_iff ha.ne' hdsq]
    exact or_comm

/-- In a diagonal form with only one positive coordinate, its zero-coordinate
hyperplane is strictly negative away from the origin. -/
lemma negative_on_coordinate_hyperplane {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (i₀ : ι) (hw : ∀ i, i ≠ i₀ → w i < 0)
    (v : ι → ℝ) (hv : v ≠ 0) (hzero : v i₀ = 0) :
    QuadraticMap.weightedSumSquares ℝ w v < 0 := by
  simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul]
  apply Finset.sum_neg'
  · intro i hi
    by_cases h : i = i₀
    · simp [h, hzero]
    · exact mul_nonpos_of_nonpos_of_nonneg (hw i h).le (mul_self_nonneg _)
  · obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
      simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hv
    refine ⟨j, Finset.mem_univ _, mul_neg_of_neg_of_pos (hw j ?_) (mul_self_pos.mpr hj)⟩
    intro h
    subst j
    exact hj hzero

/-- A signature-(1,n-1) form is nondegenerate. This step checks that no zero
quadratic directions have been silently admitted by the signature hypothesis. -/
lemma signature_separating {n : ℕ} (hn : 1 ≤ n) (Q : QuadraticForm ℝ (Space n))
    (hp : sigPos Q = 1) (hm : sigNeg Q = n - 1) :
    (QuadraticMap.associated Q).SeparatingLeft := by
  have hdim : Module.finrank ℝ (Space n) = n := by simp [Space]
  have hsum := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q)
  rw [hp, hm, hdim] at hsum
  have hz : Module.finrank ℝ Q.radical = 0 := by omega
  have hrad : Q.radical = ⊥ := Submodule.finrank_eq_zero.mp hz
  rw [LinearMap.separatingLeft_iff_ker_eq_bot,
    ← QuadraticMap.radical_eq_ker_associated]
  exact hrad

theorem timeDirectionRoots : timeDirectionRootsStatement := by
  classical
  intro n hn Q hp hm e he η hη
  obtain ⟨w, hw, ⟨T⟩⟩ :=
    Q.equivalent_one_neg_one_weighted_sum_squared (signature_separating hn Q hp hm)
  have hcard : {i | 0 < w i}.ncard = 1 := by
    rw [← QuadraticForm.sigPos_of_equiv_weightedSumSquares ⟨T⟩]
    exact hp
  obtain ⟨i₀, hi₀⟩ := Set.ncard_eq_one.mp hcard
  have hneg : ∀ i, i ≠ i₀ → w i < 0 := by
    intro i hi
    have hnot : ¬ 0 < w i := by
      intro h
      have : i ∈ ({i₀} : Set _) := hi₀ ▸ h
      exact hi (Set.mem_singleton_iff.mp this)
    rcases hw i with h | h
    · rw [h]; norm_num
    · rw [h] at hnot; norm_num at hnot
  have hevec : T e ≠ 0 := by
    intro hz
    have : e = 0 := T.toLinearEquiv.injective (by simpa using hz)
    simp [this] at he
  have hetime : T e i₀ ≠ 0 := by
    intro hz
    have h := negative_on_coordinate_hyperplane w i₀ hneg (T e) hevec hz
    rw [T.map_app] at h
    linarith
  let t₀ : ℝ := -(T η i₀) / T e i₀
  have hv : η + t₀ • e ≠ 0 := by
    intro hz
    apply hη
    refine ⟨-t₀, ?_⟩
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_left hz
  have hTv : T (η + t₀ • e) ≠ 0 := by
    intro hz
    exact hv (T.toLinearEquiv.injective (by simpa using hz))
  have htime : T (η + t₀ • e) i₀ = 0 := by
    change (T.toLinearEquiv (η + t₀ • e)) i₀ = 0
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    dsimp [t₀]
    field_simp [hetime]
    ring
  have hvalue : Q (η + t₀ • e) < 0 := by
    rw [← T.map_app]
    exact negative_on_coordinate_hyperplane w i₀ hneg _ hTv htime
  rw [quadratic_on_line] at hvalue
  obtain ⟨r₁, r₂, hlt, hroots⟩ := two_roots_of_negative_value he hvalue
  refine ⟨r₁, r₂, hlt, ?_⟩
  intro τ
  rw [quadratic_on_line]
  exact hroots τ

end P201.QuadraticClassification
