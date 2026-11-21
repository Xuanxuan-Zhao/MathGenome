import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C05.MorseIndex
import MathGenome.Internal.MultivariableAnalysis.D04.C03.TaylorPeano
import MathGenome.Internal.MultivariableAnalysis.D04.C03.PolynomialUniqueness
import Mathlib.Analysis.Asymptotics.Ring
import Mathlib.Tactic.Ring

noncomputable section
open Set Filter Topology Asymptotics
open scoped BigOperators Polynomial
namespace D04
abbrev hessianQuadraticForm : Specs.D04.C05.MorseIndex.hessianQuadraticFormType :=
  @Specs.D04.C05.MorseIndex.Model.hessianQuadraticForm
abbrev negativeMorseIndex : Specs.D04.C05.MorseIndex.negativeMorseIndexType :=
  @Specs.D04.C05.MorseIndex.Model.negativeMorseIndex
abbrev positiveMorseIndex : Specs.D04.C05.MorseIndex.positiveMorseIndexType :=
  @Specs.D04.C05.MorseIndex.Model.positiveMorseIndex

@[simp] theorem hessianQuadraticForm_apply {n : ℕ} (f : E n → ℝ) (a v : E n) :
    hessianQuadraticForm f a v =
      dotProduct (coordinates n v) ((hessian f a).mulVec (coordinates n v)) := by
  simp only [hessianQuadraticForm, Specs.D04.C05.MorseIndex.Model.hessianQuadraticForm,
    Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    QuadraticMap.comp_apply, Matrix.toLinearMap₂'_apply, dotProduct, Matrix.mulVec]
  change (∑ i, ∑ j, v i * (v j * hessian f a i j)) =
    ∑ i, v i * ∑ j, hessian f a i j * v j
  simp [Finset.mul_sum, mul_comm]

/-- A C¹ increment has the same quadratic leading term as its derivative. -/
theorem signedSquares_first_order {n : ℕ} (χ : E n → E n)
    (a : E n) (A : E n →L[ℝ] E n) (ε : Fin n → ℝ)
    (hχ : HasFDerivAt χ A a) (hz : χ a = 0) :
    (fun h => (∑ i, ε i * (χ (a+h) i)^2) - ∑ i, ε i * (A h i)^2)
      =o[𝓝 (0 : E n)] (fun h => ‖h‖^2) := by
  have he := hasFDerivAt_iff_isLittleO_nhds_zero.mp hχ
  have hlin : (fun h : E n => A h) =O[𝓝 0] (fun h => h) := A.isBigO_comp _ _
  have hbig : (fun h => χ (a+h)) =O[𝓝 (0 : E n)] (fun h => h) := by
    simpa [hz] using he.isBigO.add hlin
  have hi (i : Fin n) :
      (fun h => χ (a+h) i - A h i) =o[𝓝 (0 : E n)] (fun h => ‖h‖) := by
    have hp := ((PiLp.proj 2 (fun _ : Fin n => ℝ) i) : E n →L[ℝ] ℝ).isBigO_comp
      (fun h => χ (a+h) - χ a - A h) (𝓝 (0 : E n))
    simpa [hz] using (hp.trans_isLittleO he).norm_right
  have hbi (i : Fin n) :
      (fun h => χ (a+h) i + A h i) =O[𝓝 (0 : E n)] (fun h => ‖h‖) := by
    have hp := ((PiLp.proj 2 (fun _ : Fin n => ℝ) i) : E n →L[ℝ] ℝ).isBigO_comp
      (fun h => χ (a+h) + A h) (𝓝 (0 : E n))
    exact (hp.trans (hbig.add hlin)).norm_right
  have hs (i : Fin n) :
      (fun h => ε i * ((χ (a+h) i)^2 - (A h i)^2))
        =o[𝓝 (0 : E n)] (fun h => ‖h‖^2) := by
    convert ((hi i).mul_isBigO (hbi i)).const_mul_left (ε i) using 1 <;>
      (ext h; ring)
  convert (IsLittleO.sum (s := (Finset.univ : Finset (Fin n))) (fun i _ => hs i)) using 1
  funext h
  simp [Finset.sum_apply, Finset.sum_sub_distrib, mul_sub]

/-- A homogeneous quadratic function with a second-order little-o remainder
vanishes, also on the zero-dimensional Euclidean space. -/
theorem homogeneousQuadratic_zero_of_isLittleO {n : ℕ} (R : E n → ℝ)
    (hscale : ∀ (t : ℝ) v, R (t • v) = t^2 * R v)
    (ho : R =o[𝓝 0] (fun h => ‖h‖^2)) : ∀ v, R v = 0 := by
  intro v
  have ht : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 (0 : E n)) := by
    let L : ℝ →L[ℝ] E n := (ContinuousLinearMap.id ℝ ℝ).smulRight v
    change Tendsto L (𝓝 0) (𝓝 0)
    simpa only [map_zero] using L.continuous.tendsto 0
  have hc : (fun t : ℝ => t^2 * R v) =o[𝓝 0] (fun t => ‖v‖^2 * t^2) := by
    convert ho.comp_tendsto ht using 1
    · funext t; exact (hscale t v).symm
    · funext t
      dsimp only [Function.comp_apply]
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
  have hp : (Polynomial.C (R v) * Polynomial.X^2 : ℝ[X]) = 0 := by
    apply realPolynomial_zero_of_isLittleO 2
    · exact (Polynomial.natDegree_C_mul_le (R v) _).trans (Polynomial.natDegree_X_pow_le 2)
    · have hh : (fun t : ℝ => t^2 * R v) =o[𝓝[≠] 0] (fun t => t^2) :=
        hc.of_const_mul_right.mono nhdsWithin_le_nhds
      convert hh using 1
      ext t
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      ring
  simpa using congrArg (fun p : ℝ[X] => p.eval 1) hp

/-- Only first-order information about the coordinates is used in this
stationary second-order congruence. -/
theorem morse_hessian_congruence {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (a : E n)
    (hU : IsOpen U) (ha : a ∈ U) (hf : CrOn 2 U f) (hcrit : totalDerivative f a = 0)
    (χ : E n → E n) (A : E n →L[ℝ] E n) (ε : Fin n → ℝ)
    (hχ : HasFDerivAt χ A a) (hz : χ a = 0)
    (hNF : ∀ᶠ x in 𝓝 a, f x = f a + ∑ i, ε i * (χ x i)^2) :
    ∀ v, hessianQuadraticForm f a v = 2 * ∑ i, ε i * (A v i)^2 := by
  classical
  have hd := crOn_timesDifferentiableAt 2 U f hU hf a ha
  have hRp := taylorPeano_crOn 2 (by omega) U f a hU ha hf
  have hR : taylorRemainder 2 f a =o[𝓝 (0 : E n)] (fun h => ‖h‖^2) := by
    have hi := hRp.insert (taylorRemainder_zero_increment 2 f a)
    have hset : insert (0 : E n) ({0} : Set (E n))ᶜ = univ := by
      ext x
      by_cases hx : x = 0 <;> simp [hx]
    simpa only [hset, nhdsWithin_univ] using hi
  have hP : (fun h => f (a+h) - f a - (1/2 : ℝ) * hessianQuadraticForm f a h)
      =o[𝓝 (0 : E n)] (fun h => ‖h‖^2) := by
    apply hR.congr_left
    intro h
    change f (a+h) - taylorPolynomial 2 f a h = _
    rw [taylorPolynomial_two_hessian U f a hd h, hcrit,
      zero_apply, ← hessianQuadraticForm_apply]
    ring
  have hs := signedSquares_first_order χ a A ε hχ hz
  have hnear : ∀ᶠ h in 𝓝 (0 : E n), f (a+h) = f a + ∑ i, ε i * (χ (a+h) i)^2 := by
    have ht : Tendsto (fun h : E n => a+h) (𝓝 0) (𝓝 a) := by
      have hc : Continuous (fun h : E n => a+h) := continuous_const.add continuous_id
      convert hc.tendsto 0 using 1
      simp
    exact ht.eventually hNF
  have ho : (fun h => (1/2 : ℝ) * hessianQuadraticForm f a h - ∑ i, ε i * (A h i)^2)
      =o[𝓝 (0 : E n)] (fun h => ‖h‖^2) := by
    apply (hs.sub hP).congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [hnear] with h hh
    rw [hh]
    ring
  have hscale : ∀ (t : ℝ) v,
      (1/2 : ℝ) * hessianQuadraticForm f a (t • v) - ∑ i, ε i * (A (t • v) i)^2 =
      t^2 * ((1/2 : ℝ) * hessianQuadraticForm f a v - ∑ i, ε i * (A v i)^2) := by
    intro t v
    rw [QuadraticMap.map_smul]
    simp only [map_smul, PiLp.smul_apply, smul_eq_mul, mul_pow]
    rw [mul_sub, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro i _
      ring
  intro v
  have he := homogeneousQuadratic_zero_of_isLittleO _ hscale ho v
  linarith

/-- Derivatives of inverse C¹ local coordinates are inverse linear maps. -/
theorem coordinate_derivative_equiv {n : ℕ}
    (χ : OpenPartialHomeomorph (E n) (E n)) (a : E n)
    (ha : a ∈ χ.source) (hz : χ a = 0)
    (A B : E n →L[ℝ] E n) (hA : HasFDerivAt χ A a)
    (hB : HasFDerivAt χ.symm B 0) :
    ∃ L : E n ≃ₗ[ℝ] E n, ∀ v, L v = A v := by
  have hzero : (0 : E n) ∈ χ.target := hz ▸ χ.map_source ha
  have hi : χ.symm 0 = a := by rw [← hz]; exact χ.left_inv ha
  have hBA : B.comp A = ContinuousLinearMap.id ℝ (E n) := by
    have hB' : HasFDerivAt χ.symm B (χ a) := by simpa only [hz] using hB
    have hcomp := hB'.comp a hA
    have heq : (fun x => χ.symm (χ x)) =ᶠ[𝓝 a] id :=
      Filter.eventuallyEq_of_mem (χ.open_source.mem_nhds ha) (fun _ hx => χ.left_inv hx)
    exact (hcomp.congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_id a)
  have hAB : A.comp B = ContinuousLinearMap.id ℝ (E n) := by
    have hA' : HasFDerivAt χ A (χ.symm 0) := by simpa only [hi] using hA
    have hcomp := hA'.comp 0 hB
    have heq : (fun x => χ (χ.symm x)) =ᶠ[𝓝 (0 : E n)] id :=
      Filter.eventuallyEq_of_mem (χ.open_target.mem_nhds hzero) (fun _ hx => χ.right_inv hx)
    exact (hcomp.congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_id 0)
  refine ⟨{ A.toLinearMap with
    invFun := B
    left_inv := ?_
    right_inv := ?_ }, fun _ => rfl⟩
  · intro v
    exact DFunLike.congr_fun hBA v
  · intro v
    exact DFunLike.congr_fun hAB v

/-- Invariance of both inertia counts for every signed-square C¹ normal form.
The nondegeneracy hypothesis is retained from the source; the argument for the
congruence itself in fact does not need it. -/
theorem morse_index {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (a : E n)
    (hU : IsOpen U) (ha : a ∈ U) (hf : CrOn 2 U f) (hcrit : totalDerivative f a = 0)
    (_hnd : (hessian f a).det ≠ 0)
    (χ : OpenPartialHomeomorph (E n) (E n)) (hsource : a ∈ χ.source) (hz : χ a = 0)
    (hχ : CrOn 1 χ.source (χ : E n → E n))
    (hψ : CrOn 1 χ.target (χ.symm : E n → E n))
    (ε : Fin n → ℝ) (_hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hNF : ∀ x ∈ χ.source, f x = f a + ∑ i, ε i * (χ x i)^2) :
    negativeMorseIndex f a = {i | ε i < 0}.ncard ∧
    positiveMorseIndex f a = {i | 0 < ε i}.ncard := by
  classical
  obtain ⟨A, hA⟩ := hχ.1 a hsource
  have hzero : (0 : E n) ∈ χ.target := hz ▸ χ.map_source hsource
  obtain ⟨B, hB⟩ := hψ.1 0 hzero
  have hAd := (hasTotalDerivative_iff_hasFDerivAt χ.source χ A a χ.open_source hsource).mp hA
  have hBd := (hasTotalDerivative_iff_hasFDerivAt χ.target χ.symm B 0 χ.open_target hzero).mp hB
  obtain ⟨L, hL⟩ := coordinate_derivative_equiv χ a hsource hz A B hAd hBd
  have hquad := morse_hessian_congruence U f a hU ha hf hcrit χ A ε hAd hz
    (Filter.eventually_of_mem (χ.open_source.mem_nhds hsource) hNF)
  let e : (hessianQuadraticForm f a).IsometryEquiv
      (QuadraticMap.weightedSumSquares ℝ (fun i => 2 * ε i)) :=
    { L.trans (coordinates n) with
      map_app' := by
        intro v
        rw [hquad v]
        change QuadraticMap.weightedSumSquares ℝ (fun i => 2 * ε i)
          ((coordinates n) (L v)) = _
        rw [hL v]
        simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul, coordinates_apply]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring }
  have hneg := QuadraticForm.sigNeg_of_equiv_weightedSumSquares (w := fun i => 2 * ε i) ⟨e⟩
  have hpos := QuadraticForm.sigPos_of_equiv_weightedSumSquares (w := fun i => 2 * ε i) ⟨e⟩
  constructor
  · change sigNeg (hessianQuadraticForm f a) = _
    rw [hneg]
    congr 1
    ext i
    simp only [mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  · change sigPos (hessianQuadraticForm f a) = _
    rw [hpos]
    congr 1
    ext i
    simp only [mem_ofPred_eq]
    constructor <;> intro h <;> linarith

end D04
