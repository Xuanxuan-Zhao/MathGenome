import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch10.CirclesReflections
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch10.TriplesCrossRatio
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

noncomputable section
namespace D12Complex.CirclesReflectionsDefinitions
abbrev sphereConj := D12Complex.CirclesReflections.sphereConj
abbrev extendedRealLine := D12Complex.CirclesReflections.extendedRealLine
abbrev circleEquation := D12Complex.CirclesReflections.circleEquation
abbrev IsGeneralizedCircle := D12Complex.CirclesReflections.IsGeneralizedCircle
abbrev euclideanCircle := D12Complex.CirclesReflections.euclideanCircle
abbrev extendedLine := D12Complex.CirclesReflections.extendedLine
abbrev RealCoefficientsUpToScalar := D12Complex.CirclesReflections.RealCoefficientsUpToScalar
abbrev reflectionVia := D12Complex.CirclesReflections.reflectionVia
end D12Complex.CirclesReflectionsDefinitions
namespace D12Complex.CirclesReflections
open Mobius

@[simp] theorem sphereConj_finite (z : ℂ) :
    sphereConj (sphereFinite z) = sphereFinite (star z) := rfl
@[simp] theorem sphereConj_infty : sphereConj sphereInfty = sphereInfty := rfl
@[simp] theorem sphereConj_involutive (p : RiemannSphere) :
    sphereConj (sphereConj p) = p := by
  induction p using OnePoint.rec with
  | infty => rfl
  | coe z => exact congrArg sphereFinite (star_star z)

@[simp] theorem finite_mem_realLine (z : ℂ) :
    sphereFinite z ∈ extendedRealLine ↔ z.im = 0 := Iff.rfl
@[simp] theorem infty_mem_realLine : sphereInfty ∈ extendedRealLine := trivial

theorem mem_realLine_iff_fixed (p : RiemannSphere) :
    p ∈ extendedRealLine ↔ sphereConj p = p := by
  induction p using OnePoint.rec with
  | infty => simp [sphereInfty, extendedRealLine, sphereConj]
  | coe z =>
    change z.im = 0 ↔ sphereFinite (star z) = sphereFinite z
    rw [sphereFinite_injective.eq_iff]
    constructor
    · intro h; apply Complex.ext <;> simp [h]
    · intro h; have hi := congrArg Complex.im h; simp at hi; linarith

/-- Conjugating every entry of a matrix conjugates its sphere map. -/
def conjugateCoefficients (M : Coefficients) : Coefficients := fun i j => star (M i j)

theorem regular_conjugate (M : Coefficients) (hM : Regular M) :
    Regular (conjugateCoefficients M) := by
  have he : (conjugateCoefficients M).det = star M.det := by
    simp [Matrix.det_fin_two, conjugateCoefficients]
  rw [Regular, he]
  simpa [Regular] using hM

theorem sphereConj_pair (x y : ℂ) :
    sphereConj (spherePair x y) = spherePair (star x) (star y) := by
  by_cases hy : y = 0 <;> simp [spherePair, hy, sphereConj, sphereFinite, sphereInfty]

theorem conjugate_map (M : Coefficients) (p : RiemannSphere) :
    mobiusMap (conjugateCoefficients M) (sphereConj p) = sphereConj (mobiusMap M p) := by
  induction p using OnePoint.rec with
  | infty => exact (sphereConj_pair _ _).symm
  | coe z =>
    change spherePair _ _ = sphereConj (spherePair _ _)
    rw [sphereConj_pair]
    simp [conjugateCoefficients]

/-- Preservation of the real locus forces commutation with conjugation,
by equality at the three distinct standard real points. -/
theorem commutes_conj_of_preserves (M : Coefficients) (hM : Regular M)
    (h : mobiusMap M '' extendedRealLine = extendedRealLine) :
    ∀ p, mobiusMap M (sphereConj p) = sphereConj (mobiusMap M p) := by
  have hfix (p : RiemannSphere) (hp : p ∈ extendedRealLine) :
      mobiusMap (conjugateCoefficients M) p = mobiusMap M p := by
    have hmp : mobiusMap M p ∈ extendedRealLine := by
      rw [← h]; exact Set.mem_image_of_mem _ hp
    calc
      mobiusMap (conjugateCoefficients M) p =
          mobiusMap (conjugateCoefficients M) (sphereConj p) :=
        congrArg _ ((mem_realLine_iff_fixed p).mp hp).symm
      _ = sphereConj (mobiusMap M p) := conjugate_map M p
      _ = mobiusMap M p := (mem_realLine_iff_fixed _).mp hmp
  have he := mobiusMap_eq_of_triple (conjugateCoefficients M) M (regular_conjugate M hM) hM
    (sphereFinite 0) (sphereFinite 1) sphereInfty
    (by simp [sphereFinite]) (OnePoint.coe_ne_infty _) (OnePoint.coe_ne_infty _)
    (hfix _ (by simp)) (hfix _ (by simp)) (hfix _ infty_mem_realLine)
  intro p
  calc
    mobiusMap M (sphereConj p) = mobiusMap (conjugateCoefficients M) (sphereConj p) :=
      congrFun he.symm _
    _ = sphereConj (mobiusMap M p) := conjugate_map M p


/-- A commuting sphere bijection preserves the full fixed locus, including infinity. -/
theorem preserves_of_commutes (M : Coefficients) (hM : Regular M)
    (hc : ∀ p, mobiusMap M (sphereConj p) = sphereConj (mobiusMap M p)) :
    mobiusMap M '' extendedRealLine = extendedRealLine := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    apply (mem_realLine_iff_fixed _).mpr
    rw [← hc, (mem_realLine_iff_fixed q).mp hq]
  · intro hp
    obtain ⟨q, rfl⟩ := (mobiusMap_bijective M hM).2 p
    refine ⟨q, (mem_realLine_iff_fixed q).mpr ?_, rfl⟩
    apply (mobiusMap_bijective M hM).1
    rw [hc, (mem_realLine_iff_fixed _).mp hp]

theorem preserves_realLine_iff_realCoefficients (M : Coefficients) (hM : Regular M) :
    mobiusMap M '' extendedRealLine = extendedRealLine ↔ RealCoefficientsUpToScalar M := by
  constructor
  · intro hp
    have hc := commutes_conj_of_preserves M hM hp
    have he : mobiusMap M = mobiusMap (conjugateCoefficients M) := by
      funext p
      calc
        mobiusMap M p = sphereConj (sphereConj (mobiusMap M p)) :=
          (sphereConj_involutive _).symm
        _ = sphereConj (mobiusMap M (sphereConj p)) := congrArg sphereConj (hc p).symm
        _ = mobiusMap (conjugateCoefficients M) p := by
          rw [← conjugate_map, sphereConj_involutive]
    obtain ⟨k, hk, hke⟩ := (mobiusMap_eq_iff M _ hM (regular_conjugate M hM)).mp he
    have hn : ∃ i j, M i j ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hM
      simp [Matrix.det_fin_two, hn]
    obtain ⟨i, j, hij⟩ := hn
    refine ⟨(M i j)⁻¹, inv_ne_zero hij, fun u v => ?_⟩
    apply Complex.conj_eq_iff_im.mp
    have huv : M u v = k * star (M u v) := congrFun (congrFun hke u) v
    have hij' : M i j = k * star (M i j) := congrFun (congrFun hke i) j
    change star ((M i j)⁻¹ * M u v) = (M i j)⁻¹ * M u v
    rw [show (M i j)⁻¹ * M u v = M u v / M i j by ring]
    rw [star_div₀]
    apply (div_eq_div_iff (by simpa using hij) hij).mpr
    linear_combination star (M u v) * hij' - star (M i j) * huv
  · rintro ⟨k, hk, hreal⟩
    have he : conjugateCoefficients (k • M) = k • M := by
      ext i j
      exact Complex.conj_eq_iff_im.mpr (hreal i j)
    apply preserves_of_commutes M hM
    intro p
    have hc := conjugate_map (k • M) p
    rw [he, mobiusMap_smul M k hk] at hc
    exact hc

theorem reflection_independent (C : Set RiemannSphere) (M N : Coefficients)
    (_hC : IsGeneralizedCircle C) (hM : Regular M) (hN : Regular N)
    (hMC : mobiusMap M '' C = extendedRealLine)
    (hNC : mobiusMap N '' C = extendedRealLine) : reflectionVia M = reflectionVia N := by
  let I := inverseCoefficients M
  have hI : Regular I := regular_inverseCoefficients M hM
  have hinv : mobiusMap I ∘ mobiusMap M = id := funext (mobiusMap_inverse M hM).1
  have himage : mobiusMap I '' extendedRealLine = C := by
    rw [← hMC, Set.image_image, ← Function.comp_def, hinv, Set.image_id]
  have hK : Regular (N * I) := regular_mul N I hN hI
  have hp : mobiusMap (N * I) '' extendedRealLine = extendedRealLine := by
    rw [mobiusMap_mul N I hN hI, Set.image_comp, himage, hNC]
  have hc := commutes_conj_of_preserves (N * I) hK hp
  funext p
  apply (mobiusMap_bijective N hN).1
  change mobiusMap N (mobiusMap I (sphereConj (mobiusMap M p))) =
    mobiusMap N (mobiusMap (inverseCoefficients N) (sphereConj (mobiusMap N p)))
  rw [(mobiusMap_inverse N hN).2]
  have he := hc (mobiusMap M p)
  rw [mobiusMap_mul N I hN hI] at he
  change mobiusMap N (mobiusMap I (sphereConj (mobiusMap M p))) =
    sphereConj (mobiusMap N (mobiusMap I (mobiusMap M p))) at he
  rw [show mobiusMap I (mobiusMap M p) = p from (mobiusMap_inverse M hM).1 p] at he
  exact he


/-- The real Hermitian form in homogeneous coordinates. -/
def circleForm (α : ℝ) (β : ℂ) (γ : ℝ) (x y : ℂ) : ℝ :=
  α * Complex.normSq x + 2 * (β * x * star y).re + γ * Complex.normSq y

theorem circleForm_scale (α : ℝ) (β : ℂ) (γ : ℝ) (x y k : ℂ) :
    circleForm α β γ (k*x) (k*y) = Complex.normSq k * circleForm α β γ x y := by
  simp only [circleForm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem circleForm_finite (α : ℝ) (β : ℂ) (γ : ℝ) (z : ℂ) :
    circleForm α β γ z 1 = α * Complex.normSq z + 2 * (β*z).re + γ := by
  simp [circleForm]

theorem circleEquation_pair (α : ℝ) (β : ℂ) (γ : ℝ) (x y : ℂ)
    (hxy : x ≠ 0 ∨ y ≠ 0) :
    spherePair x y ∈ circleEquation α β γ ↔ circleForm α β γ x y = 0 := by
  by_cases hy : y = 0
  · have hx : x ≠ 0 := hxy.resolve_right (not_ne_iff.mpr hy)
    simp [spherePair, hy, circleEquation, sphereInfty, circleForm,
      mul_eq_zero, (Complex.normSq_pos.mpr hx).ne']
  · have hs := circleForm_scale α β γ (x/y) 1 y
    have he : y * (x/y) = x := by field_simp
    simp only [he, mul_one, circleForm_finite] at hs
    change (if y = 0 then sphereInfty else sphereFinite (x/y)) ∈ _ ↔ _
    rw [ite_eq_right hy]
    change (α * Complex.normSq (x/y) + 2 * (β*(x/y)).re + γ = 0) ↔ _
    rw [hs, mul_eq_zero]
    simp [(Complex.normSq_pos.mpr hy).ne']

def pullbackAlpha (α : ℝ) (β : ℂ) (γ : ℝ) (M : Coefficients) : ℝ :=
  circleForm α β γ (M 0 0) (M 1 0)
def pullbackGamma (α : ℝ) (β : ℂ) (γ : ℝ) (M : Coefficients) : ℝ :=
  circleForm α β γ (M 0 1) (M 1 1)
def pullbackBeta (α : ℝ) (β : ℂ) (γ : ℝ) (M : Coefficients) : ℂ :=
  α * M 0 0 * star (M 0 1) + β * M 0 0 * star (M 1 1) +
  star β * M 1 0 * star (M 0 1) + γ * M 1 0 * star (M 1 1)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem circleForm_pullback (α : ℝ) (β : ℂ) (γ : ℝ) (M : Coefficients) (x y : ℂ) :
    circleForm α β γ (M 0 0*x + M 0 1*y) (M 1 0*x + M 1 1*y) =
    circleForm (pullbackAlpha α β γ M) (pullbackBeta α β γ M)
      (pullbackGamma α β γ M) x y := by
  simp only [circleForm, pullbackAlpha, pullbackBeta, pullbackGamma,
    Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem pullback_discriminant (α : ℝ) (β : ℂ) (γ : ℝ) (M : Coefficients) :
    Complex.normSq (pullbackBeta α β γ M) -
      pullbackAlpha α β γ M * pullbackGamma α β γ M =
    Complex.normSq M.det * (Complex.normSq β - α*γ) := by
  simp only [circleForm, pullbackAlpha, pullbackBeta, pullbackGamma, Matrix.det_fin_two,
    Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem circleEquation_preimage (α : ℝ) (β : ℂ) (γ : ℝ)
    (M : Coefficients) (hM : Regular M) :
    mobiusMap M ⁻¹' circleEquation α β γ = circleEquation
      (pullbackAlpha α β γ M) (pullbackBeta α β γ M) (pullbackGamma α β γ M) := by
  ext p
  induction p using OnePoint.rec with
  | infty =>
    change spherePair (M 0 0) (M 1 0) ∈ circleEquation α β γ ↔ _
    have hn : M 0 0 ≠ 0 ∨ M 1 0 ≠ 0 := by
      simpa using image_pair_nonzero M hM 1 0 (Or.inl one_ne_zero)
    rw [circleEquation_pair α β γ _ _ hn]
    rfl
  | coe z =>
    change spherePair (M 0 0*z+M 0 1) (M 1 0*z+M 1 1) ∈ circleEquation α β γ ↔ _
    have hn : M 0 0*z+M 0 1 ≠ 0 ∨ M 1 0*z+M 1 1 ≠ 0 := by
      simpa using image_pair_nonzero M hM z 1 (Or.inr one_ne_zero)
    rw [circleEquation_pair α β γ _ _ hn]
    have he := circleForm_pullback α β γ M z 1
    simp only [mul_one, circleForm_finite] at he
    rw [he]
    rfl

theorem preimage_generalizedCircle (M : Coefficients) (hM : Regular M)
    (C : Set RiemannSphere) (hC : IsGeneralizedCircle C) :
    IsGeneralizedCircle (mobiusMap M ⁻¹' C) := by
  rcases hC with ⟨α, β, γ, hd, rfl⟩
  refine ⟨pullbackAlpha α β γ M, pullbackBeta α β γ M, pullbackGamma α β γ M, ?_, ?_⟩
  · rw [pullback_discriminant]
    exact mul_pos (Complex.normSq_pos.mpr hM) hd
  · exact circleEquation_preimage α β γ M hM

theorem mobius_image_generalizedCircle (M : Coefficients) (C : Set RiemannSphere)
    (hM : Regular M) (hC : IsGeneralizedCircle C) :
    IsGeneralizedCircle (mobiusMap M '' C) := by
  have he : mobiusMap M '' C = mobiusMap (inverseCoefficients M) ⁻¹' C := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      change mobiusMap (inverseCoefficients M) (mobiusMap M q) ∈ C
      rwa [(mobiusMap_inverse M hM).1]
    · intro hp
      exact ⟨mobiusMap (inverseCoefficients M) p, hp, (mobiusMap_inverse M hM).2 p⟩
  rw [he]
  exact preimage_generalizedCircle _ (regular_inverseCoefficients M hM) C hC


/-- Completing the square gives an ordinary positive-radius circle. -/
theorem circleEquation_circle (α : ℝ) (β : ℂ) (γ : ℝ) (hα : α ≠ 0)
    (hd : 0 < Complex.normSq β - α*γ) :
    ∃ (c : ℂ) (r : ℝ), 0 < r ∧ circleEquation α β γ = euclideanCircle c r := by
  let c : ℂ := ⟨-β.re / α, β.im / α⟩
  let D := Complex.normSq β - α*γ
  let r := Real.sqrt (D / α^2)
  have ha2 : 0 < α^2 := sq_pos_of_ne_zero hα
  have hr : 0 < r := Real.sqrt_pos.mpr (div_pos hd ha2)
  have hr2 : α^2 * r^2 = D := by
    rw [show r^2 = D/α^2 from Real.sq_sqrt (div_nonneg hd.le ha2.le)]
    field_simp
  have hf (z : ℂ) :
      α^2 * Complex.normSq (z-c) =
      α*(α*Complex.normSq z + 2*(β*z).re + γ) + D := by
    simp only [c, D, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re]
    field_simp
    ring
  have hg (z : ℂ) : α*Complex.normSq z + 2*(β*z).re + γ = 0 ↔ ‖z-c‖ = r := by
    have he := hf z
    rw [← Complex.sq_norm] at he
    constructor
    · intro h
      have he' : α^2 * ‖z-c‖^2 = α^2 * r^2 := by rw [h] at he; linarith
      have hs : ‖z-c‖^2 = r^2 := mul_left_cancel₀ ha2.ne' he'
      nlinarith [norm_nonneg (z-c)]
    · intro h
      rw [h] at he
      have he' : α * (α*Complex.normSq z + 2*(β*z).re + γ) = 0 := by linarith
      exact (mul_eq_zero.mp he').resolve_left hα
  refine ⟨c, r, hr, ?_⟩
  ext p
  induction p using OnePoint.rec with
  | infty => simp [circleEquation, euclideanCircle, sphereFinite, hα]
  | coe z => simpa [circleEquation, euclideanCircle, sphereFinite] using hg z

/-- A nondegenerate equation with zero quadratic coefficient is an affine real line. -/
theorem circleEquation_line (β : ℂ) (γ : ℝ) (hβ : β ≠ 0) :
    ∃ c v : ℂ, v ≠ 0 ∧ circleEquation 0 β γ = extendedLine c v := by
  let c : ℂ := (-(γ/2) : ℝ) / β
  let v : ℂ := Complex.I / β
  have hv : v ≠ 0 := div_ne_zero Complex.I_ne_zero hβ
  have hbc : β*c = (-(γ/2) : ℝ) := by dsimp [c]; field_simp
  have hbv : β*v = Complex.I := by dsimp [v]; field_simp
  have hg (z : ℂ) : 2*(β*z).re + γ = 0 ↔ ∃ t : ℝ, z = c + t*v := by
    constructor
    · intro hz
      refine ⟨(β*z).im, ?_⟩
      apply (mul_right_injective₀ hβ)
      dsimp only
      rw [mul_add, show β*((((β*z).im : ℝ) : ℂ)*v) = (((β*z).im : ℝ) : ℂ)*(β*v) by ring,
        hbc, hbv]
      simp only [Complex.mul_re] at hz
      apply Complex.ext <;> simp; linarith
    · rintro ⟨t, rfl⟩
      rw [mul_add, show β*((t : ℂ)*v) = (t : ℂ)*(β*v) by ring, hbc, hbv]
      simp
      ring
  refine ⟨c, v, hv, ?_⟩
  ext p
  induction p using OnePoint.rec with
  | infty => simp [circleEquation, extendedLine, sphereInfty]
  | coe z => simpa [circleEquation, extendedLine, sphereFinite, sphereInfty] using hg z

theorem euclideanCircle_generalized (c : ℂ) (r : ℝ) (hr : 0 < r) :
    IsGeneralizedCircle (euclideanCircle c r) := by
  refine ⟨1, -star c, Complex.normSq c-r^2, ?_, ?_⟩
  · simp only [Complex.normSq_neg, Complex.star_def, Complex.normSq_conj, one_mul]
    nlinarith
  · have he (z : ℂ) :
        Complex.normSq z + 2*((-star c)*z).re + (Complex.normSq c-r^2) =
        ‖z-c‖^2-r^2 := by
      rw [Complex.sq_norm]
      simp only [Complex.normSq_apply, Complex.mul_re, Complex.neg_re, Complex.neg_im,
        Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im]
      ring
    ext p
    induction p using OnePoint.rec with
    | infty => simp [circleEquation, euclideanCircle, sphereFinite]
    | coe z =>
      change sphereFinite z ∈ euclideanCircle c r ↔ _
      simp only [euclideanCircle, Set.mem_image, Set.mem_ofPred_eq]
      simp only [sphereFinite, OnePoint.coe_injective.eq_iff, exists_eq_right]
      change ‖z-c‖ = r ↔ 1*Complex.normSq z + 2*((-star c)*z).re + _ = 0
      rw [one_mul, he]
      constructor <;> intro h <;> nlinarith [norm_nonneg (z-c)]

theorem extendedLine_generalized (c v : ℂ) (hv : v ≠ 0) :
    IsGeneralizedCircle (extendedLine c v) := by
  let β : ℂ := Complex.I / v
  let γ : ℝ := -2*(β*c).re
  have hb : β ≠ 0 := div_ne_zero Complex.I_ne_zero hv
  have hbv : β*v = Complex.I := by dsimp [β]; field_simp
  have hg (z : ℂ) : 2*(β*z).re+γ=0 ↔ ∃ t : ℝ, z=c+t*v := by
    constructor
    · intro hz
      refine ⟨(β*(z-c)).im, ?_⟩
      apply mul_right_injective₀ hb
      dsimp only
      rw [mul_add, show β*((((β*(z-c)).im : ℝ) : ℂ)*v) =
        (((β*(z-c)).im : ℝ) : ℂ)*(β*v) by ring, hbv]
      apply Complex.ext <;> simp [mul_sub]
      dsimp [γ] at hz
      simp only [Complex.mul_re] at hz
      linarith
    · rintro ⟨t, rfl⟩
      rw [mul_add, show β*((t : ℂ)*v) = (t : ℂ)*(β*v) by ring, hbv]
      simp [γ]
  refine ⟨0, β, γ, by simpa using Complex.normSq_pos.mpr hb, ?_⟩
  ext p
  induction p using OnePoint.rec with
  | infty => simp [circleEquation, extendedLine, sphereInfty]
  | coe z =>
    simpa [circleEquation, extendedLine, sphereFinite, sphereInfty] using (hg z).symm

theorem generalizedCircle_iff_geometric (C : Set RiemannSphere) :
    IsGeneralizedCircle C ↔
    (∃ (c : ℂ) (r : ℝ), 0 < r ∧ C = euclideanCircle c r) ∨
    (∃ c v : ℂ, v ≠ 0 ∧ C = extendedLine c v) := by
  constructor
  · rintro ⟨α, β, γ, hd, rfl⟩
    by_cases ha : α = 0
    · subst α
      right
      exact circleEquation_line β γ (Complex.normSq_pos.mp (by simpa using hd))
    · left
      exact circleEquation_circle α β γ ha hd
  · rintro (⟨c, r, hr, rfl⟩ | ⟨c, v, hv, rfl⟩)
    · exact euclideanCircle_generalized c r hr
    · exact extendedLine_generalized c v hv


theorem extendedRealLine_equation : extendedRealLine = circleEquation 0 Complex.I 0 := by
  ext p
  induction p using OnePoint.rec with
  | infty => simp [extendedRealLine, circleEquation]
  | coe z =>
    change z.im = 0 ↔ 0*Complex.normSq z + 2*(Complex.I*z).re + 0 = 0
    simp

theorem spherePair_mem_realLine (x y : ℂ) :
    spherePair x y ∈ extendedRealLine ↔ (x*star y).im = 0 := by
  by_cases hn : x ≠ 0 ∨ y ≠ 0
  · rw [extendedRealLine_equation, circleEquation_pair 0 Complex.I 0 x y hn]
    have he : circleForm 0 Complex.I 0 x y = -2*(x*star y).im := by
      simp only [circleForm, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.star_def, Complex.conj_re, Complex.conj_im]
      ring
    rw [he]
    constructor <;> intro h <;> linarith
  · push Not at hn
    rcases hn with ⟨rfl, rfl⟩
    simp [spherePair]

theorem euclideanCircle_to_realLine (c : ℂ) (r : ℝ) (hr : 0 < r) :
    ∃ M : Coefficients, Regular M ∧
      mobiusMap M '' euclideanCircle c r = extendedRealLine := by
  let M : Coefficients := !![Complex.I, -Complex.I*(c+r); 1, -(c-r)]
  have hd : M.det = 2*Complex.I*(r : ℂ) := by
    simp [M, Matrix.det_fin_two]
    ring
  have hM : Regular M := by
    rw [Regular, hd]
    exact mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (by exact_mod_cast hr.ne')
  have hp : mobiusMap M ⁻¹' extendedRealLine = euclideanCircle c r := by
    ext p
    induction p using OnePoint.rec with
    | infty =>
      change spherePair Complex.I 1 ∈ extendedRealLine ↔ sphereInfty ∈ euclideanCircle c r
      rw [spherePair_mem_realLine]
      simp [euclideanCircle, sphereFinite, sphereInfty]
    | coe z =>
      change spherePair (Complex.I*z + -Complex.I*(c+r)) (1*z + -(c-r)) ∈
        extendedRealLine ↔ sphereFinite z ∈ euclideanCircle c r
      rw [spherePair_mem_realLine]
      have he : ((Complex.I*z + -Complex.I*(c+r)) * star (1*z + -(c-r))).im =
          ‖z-c‖^2-r^2 := by
        rw [Complex.sq_norm]
        simp only [Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.add_re,
          Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
          Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, Complex.normSq_apply]
        ring
      rw [he]
      have hg : ‖z-c‖^2-r^2=0 ↔ ‖z-c‖=r := by
        constructor <;> intro h <;> nlinarith [norm_nonneg (z-c)]
      simpa [euclideanCircle, sphereFinite] using hg
  refine ⟨M, hM, ?_⟩
  rw [← hp]
  exact Set.image_preimage_eq _ (mobiusMap_bijective M hM).2

theorem extendedLine_to_realLine (c v : ℂ) (hv : v ≠ 0) :
    ∃ M : Coefficients, Regular M ∧
      mobiusMap M '' extendedLine c v = extendedRealLine := by
  let M : Coefficients := !![v⁻¹, -c/v; 0, 1]
  have hM : Regular M := by simpa [M, Regular, Matrix.det_fin_two] using inv_ne_zero hv
  have hp : mobiusMap M ⁻¹' extendedRealLine = extendedLine c v := by
    ext p
    induction p using OnePoint.rec with
    | infty => simp [M, mobiusMap, spherePair, sphereInfty, extendedLine, extendedRealLine]
    | coe z =>
      have he : mobiusMap M (sphereFinite z) = sphereFinite ((z-c)/v) := by
        rw [mobiusMap_finite M z (by simp [M])]
        congr 1
        simp [M]
        ring
      change mobiusMap M (sphereFinite z) ∈ extendedRealLine ↔ _
      rw [he, finite_mem_realLine]
      have hg : ((z-c)/v).im=0 ↔ ∃ t : ℝ, z=c+t*v := by
        constructor
        · intro hz
          refine ⟨((z-c)/v).re, ?_⟩
          have hreal : (((z-c)/v).re : ℂ) = (z-c)/v := by
            apply Complex.ext <;> simp [hz]
          rw [hreal, div_mul_cancel₀ _ hv]
          ring
        · rintro ⟨t, rfl⟩
          simp [hv]
      simpa [extendedLine, sphereFinite, sphereInfty] using hg
  refine ⟨M, hM, ?_⟩
  rw [← hp]
  exact Set.image_preimage_eq _ (mobiusMap_bijective M hM).2

theorem generalizedCircle_to_realLine (C : Set RiemannSphere) (hC : IsGeneralizedCircle C) :
    ∃ M : Coefficients, Regular M ∧ mobiusMap M '' C = extendedRealLine := by
  rcases (generalizedCircle_iff_geometric C).mp hC with
    ⟨c, r, hr, rfl⟩ | ⟨c, v, hv, rfl⟩
  · exact euclideanCircle_to_realLine c r hr
  · exact extendedLine_to_realLine c v hv

end D12Complex.CirclesReflections
