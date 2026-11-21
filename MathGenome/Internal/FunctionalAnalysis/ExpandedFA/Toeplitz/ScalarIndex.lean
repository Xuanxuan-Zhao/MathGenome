import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Toeplitz.ScalarIndex
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Toeplitz.HankelCompactness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.HilbertSemiFredholmIndex

/-! Scalar Toeplitz index theorem on the upstream Hardy coefficient space:
compact parametrices, integer shift defects, and the continuous winding homotopy. -/
noncomputable section
open MeasureTheory
open scoped Real ENNReal Topology InnerProductSpace

namespace ExpandedFA.Toeplitz.ScalarIndex
open ExpandedFA.Toeplitz.Definitions
open ExpandedFA.Toeplitz.HankelCompactness
open ExpandedFA.Fredholm

/-- The continuous reciprocal exists because the symbol is nowhere zero. -/
def reciprocalSymbol (φ : NonvanishingLoop) : C(Definitions.Spec.Circle, ℂ) :=
  ⟨fun t => (φ.val t)⁻¹, φ.val.continuous.inv₀ φ.property⟩

@[simp] theorem symbol_mul_reciprocal (φ : NonvanishingLoop) :
    φ.val * reciprocalSymbol φ = 1 := by
  ext t
  exact mul_inv_cancel₀ (φ.property t)

@[simp] theorem reciprocal_mul_symbol (φ : NonvanishingLoop) :
    reciprocalSymbol φ * φ.val = 1 := by
  ext t
  exact inv_mul_cancel₀ (φ.property t)

@[simp] theorem multiplication_one :
    multiplication (continuousSymbol (1 : C(Definitions.Spec.Circle, ℂ))) =
      ContinuousLinearMap.id ℂ BoundaryL2 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [multiplication_values (continuousSymbol (1 : C(Definitions.Spec.Circle, ℂ))) f,
    continuous_symbol_values (1 : C(Definitions.Spec.Circle, ℂ))] with t hm h1
  simpa only [ContinuousLinearMap.id_apply, h1, ContinuousMap.one_apply, one_mul] using hm

@[simp] theorem toeplitz_one :
    toeplitz (continuousSymbol (1 : C(Definitions.Spec.Circle, ℂ))) =
      ContinuousLinearMap.id ℂ H2 := by
  apply ContinuousLinearMap.ext
  intro f
  change boundaryAnalysis (multiplication (continuousSymbol (1 : C(Definitions.Spec.Circle, ℂ)))
    (ExpandedFA.PartIV.HardyDisk.boundary f)) = f
  rw [multiplication_one, ContinuousLinearMap.id_apply, boundaryAnalysis_boundary]

/-- Both compact defects are proved for the same bounded reciprocal-symbol map. -/
theorem reciprocal_parametrix (φ : NonvanishingLoop) :
    IsCompactOperator
      ((toeplitz (continuousSymbol (reciprocalSymbol φ))).comp
        (toeplitz (continuousSymbol φ.val)) - ContinuousLinearMap.id ℂ H2) ∧
    IsCompactOperator
      ((toeplitz (continuousSymbol φ.val)).comp
        (toeplitz (continuousSymbol (reciprocalSymbol φ))) - ContinuousLinearMap.id ℂ H2) := by
  constructor
  · simpa only [reciprocal_mul_symbol, toeplitz_one] using
      product_defect_compact (reciprocalSymbol φ) φ.val
  · simpa only [symbol_mul_reciprocal, toeplitz_one] using
      product_defect_compact φ.val (reciprocalSymbol φ)

/-- Fredholmness here includes closed actual range and finite actual cokernel. -/
theorem fredholm_symbols : Spec.FredholmSymbols := by
  intro φ
  have h := reciprocal_parametrix φ
  exact isFredholm_of_compact_parametrix _ (toeplitz (continuousSymbol (reciprocalSymbol φ)))
    ((ExpandedFA.Compactness.compact_iff_isCompactOperator _).mpr h.1)
    ((ExpandedFA.Compactness.compact_iff_isCompactOperator _).mpr h.2)

/-- Actual continuous linear dependence on the uniform-norm continuous symbol. -/
def toeplitzSymbolMap : C(Definitions.Spec.Circle, ℂ) →L[ℂ] H2 →L[ℂ] H2 :=
  (ContinuousLinearMap.compL ℂ H2 BoundaryL2 H2 boundaryAnalysis).comp
    (((ContinuousLinearMap.compL ℂ H2 BoundaryL2 BoundaryL2).flip boundaryInclusion).comp
      (((ContinuousLinearMap.mul ℂ ℂ).holderL Definitions.Spec.circleMeasure ∞ 2 2).comp
        (ContinuousMap.toLp ∞ Definitions.Spec.circleMeasure ℂ)))

@[simp] theorem toeplitzSymbolMap_apply (φ : C(Definitions.Spec.Circle, ℂ)) :
    toeplitzSymbolMap φ = toeplitz (continuousSymbol φ) := rfl

/-- Local constancy of the native integer index on this continuous Fredholm path. -/
theorem homotopy_index : Spec.HomotopyIndex := by
  intro p hp hn h₀ h₁
  let A : unitInterval → H2 →L[ℂ] H2 := fun s => toeplitzSymbolMap (p s)
  have hA : Continuous A := toeplitzSymbolMap.continuous.comp hp
  have hf (s : unitInterval) : IsFredholm (A s) := fredholm_symbols ⟨p s, hn s⟩
  have hi : Continuous (fun s : unitInterval => (A s).toLinearMap.index) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact (hf s).to_native.index_continuousAt.comp hA.continuousAt
  exact isPreconnected_univ.constant hi.continuousOn (Set.mem_univ 0) (Set.mem_univ 1)

/-- The n-fold forward shift, built from its actual orthonormal coefficient modes. -/
def shiftModes (n k : ℕ) : H2 := lp.single 2 (k + n) 1

theorem shiftModes_orthonormal (n : ℕ) : Orthonormal ℂ (shiftModes n) := by
  rw [orthonormal_iff_ite]
  intro i j
  simp [shiftModes, lp.inner_single_left, lp.single_apply, Pi.single_apply,
    RCLike.inner_apply]

def forwardShift (n : ℕ) : H2 →ₗᵢ[ℂ] H2 :=
  (shiftModes_orthonormal n).orthogonalFamily.linearIsometry

@[simp] theorem forwardShift_single (n k : ℕ) (c : ℂ) :
    forwardShift n (lp.single 2 k c) = lp.single 2 (k + n) c := by
  simp [forwardShift, OrthogonalFamily.linearIsometry_apply_single, shiftModes,
    ← lp.single_smul]

@[simp] theorem forwardShift_adjoint_apply (n : ℕ) (f : H2) (k : ℕ) :
    (forwardShift n).toContinuousLinearMap.adjoint f k = f (k + n) := by
  have h := (forwardShift n).toContinuousLinearMap.adjoint_inner_right
    (lp.single 2 k (1 : ℂ)) f
  simpa [lp.inner_single_left, RCLike.inner_apply] using h

/-- The matrix of the compressed multiplier in the genuine Hardy coefficient basis. -/
theorem toeplitz_mode_single (m : ℤ) (j i : ℕ) (c : ℂ) :
    toeplitz (continuousSymbol (fourier (T := 2 * π) m)) (lp.single 2 j c) i =
      if (i : ℤ) = (j : ℤ) + m then c else 0 := by
  classical
  have h := boundaryInclusion.adjoint_inner_right
    (lp.single 2 i (1 : ℂ))
    (multiplication (continuousSymbol (fourier (T := 2 * π) m))
      (ExpandedFA.PartIV.HardyDisk.boundary (lp.single 2 j c)))
  change ⟪lp.single 2 i (1 : ℂ),
    toeplitz (continuousSymbol (fourier (T := 2 * π) m)) (lp.single 2 j c)⟫_ℂ = _ at h
  simp only [lp.inner_single_left, RCLike.inner_apply, map_one, mul_one] at h
  rw [h]
  change ⟪ExpandedFA.PartIV.HardyDisk.boundary (lp.single 2 i (1 : ℂ)),
    multiplication (continuousSymbol (fourier (T := 2 * π) m))
      (ExpandedFA.PartIV.HardyDisk.boundary (lp.single 2 j c))⟫_ℂ = _
  rw [boundary_single, boundary_single, one_smul, map_smul, mode_multiplication,
    inner_smul_right, (orthonormal_iff_ite.mp (orthonormal_fourier (T := 2 * π)))]
  split_ifs <;> simp_all

theorem positive_toeplitz_eq_shift (n : ℕ) :
    toeplitz (continuousSymbol (fourier (T := 2 * π) (n : ℤ))) =
      (forwardShift n).toContinuousLinearMap := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro j
  apply ContinuousLinearMap.ext
  intro c
  apply lp.ext
  funext i
  change toeplitz (continuousSymbol (fourier (T := 2 * π) (n : ℤ)))
    (lp.single 2 j c) i = forwardShift n (lp.single 2 j c) i
  rw [toeplitz_mode_single, forwardShift_single]
  simp only [lp.single_apply, Pi.single_apply]
  have he : ((i : ℤ) = (j : ℤ) + (n : ℤ)) ↔ i = j + n := by omega
  simp only [he]

theorem negative_toeplitz_eq_adjoint (n : ℕ) :
    toeplitz (continuousSymbol (fourier (T := 2 * π) (-(n : ℤ)))) =
      (forwardShift n).toContinuousLinearMap.adjoint := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro j
  apply ContinuousLinearMap.ext
  intro c
  apply lp.ext
  funext i
  change toeplitz (continuousSymbol (fourier (T := 2 * π) (-(n : ℤ))))
    (lp.single 2 j c) i = (forwardShift n).toContinuousLinearMap.adjoint (lp.single 2 j c) i
  rw [toeplitz_mode_single, forwardShift_adjoint_apply]
  simp only [lp.single_apply, Pi.single_apply]
  have he : ((i : ℤ) = (j : ℤ) + -(n : ℤ)) ↔ i + n = j := by omega
  simp only [he]

/-- The backward shift is onto the entire Hardy space. -/
theorem negative_shift_surjective (n : ℕ) :
    Function.Surjective (toeplitz (continuousSymbol (fourier (T := 2 * π) (-(n : ℤ))))) := by
  rw [negative_toeplitz_eq_adjoint]
  intro f
  refine ⟨forwardShift n f, ?_⟩
  exact congrArg (fun A : H2 →L[ℂ] H2 => A f) (forwardShift n).adjoint_comp_self

/-- First-n coefficients identify the entire backward-shift kernel. -/
def initialCoordinates (n : ℕ) :
    (forwardShift n).toContinuousLinearMap.adjoint.ker →ₗ[ℂ] (Fin n → ℂ) where
  toFun f i := f.val i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem initialCoordinates_bijective (n : ℕ) : Function.Bijective (initialCoordinates n) := by
  classical
  constructor
  · intro f g h
    apply Subtype.ext
    apply lp.ext
    funext k
    by_cases hk : k < n
    · exact congrFun h ⟨k, hk⟩
    · have hf := congrArg (fun x : H2 => x (k - n)) f.property
      have hg := congrArg (fun x : H2 => x (k - n)) g.property
      change (forwardShift n).toContinuousLinearMap.adjoint f.val (k - n) = 0 at hf
      change (forwardShift n).toContinuousLinearMap.adjoint g.val (k - n) = 0 at hg
      simp only [forwardShift_adjoint_apply] at hf hg
      rw [Nat.sub_add_cancel (by omega)] at hf hg
      exact hf.trans hg.symm
  · intro c
    let f : H2 := ∑ i : Fin n, lp.single 2 (i : ℕ) (c i)
    have hf : f ∈ (forwardShift n).toContinuousLinearMap.adjoint.ker := by
      rw [LinearMap.mem_ker]
      apply lp.ext
      funext k
      change (forwardShift n).toContinuousLinearMap.adjoint f k = 0
      rw [forwardShift_adjoint_apply]
      change ((∑ i : Fin n, lp.single 2 (i : ℕ) (c i)) : H2) (k + n) = 0
      simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Pi.single_apply]
      apply Finset.sum_eq_zero
      intro i _
      exact ite_eq_right (by have := i.isLt; omega)
    refine ⟨⟨f, hf⟩, ?_⟩
    funext i
    change ((∑ j : Fin n, lp.single 2 (j : ℕ) (c j)) : H2) (i : ℕ) = c i
    simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Pi.single_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      exact ite_eq_right (by intro h; exact hj (Fin.ext h.symm))
    · simp

theorem adjoint_shift_kernel_finrank (n : ℕ) :
    Module.finrank ℂ (forwardShift n).toContinuousLinearMap.adjoint.ker = n := by
  have h := (LinearEquiv.ofBijective (initialCoordinates n)
    (initialCoordinates_bijective n)).finrank_eq
  simpa using h

theorem shift_kernel_finrank (n : ℕ) :
    Module.finrank ℂ (forwardShift n).toContinuousLinearMap.ker = 0 := by
  rw [show (forwardShift n).toContinuousLinearMap.ker = ⊥ from
    LinearMap.ker_eq_bot.mpr (forwardShift n).injective]
  simp

theorem fourier_symbol_fredholm (m : ℤ) :
    IsFredholm (toeplitz (continuousSymbol (fourier (T := 2 * π) m))) :=
  fredholm_symbols ⟨fourier (T := 2 * π) m, fun t => (AddCircle.toCircle (m • t)).coe_ne_zero⟩

/-- Forward shifts have no kernel and n-dimensional actual cokernel, including n=0. -/
theorem positive_shift : Spec.PositiveShift := by
  intro n
  have hf := fourier_symbol_fredholm (n : ℤ)
  have hk : Module.finrank ℂ
      (toeplitz (continuousSymbol (fourier (T := 2 * π) (n : ℤ)))).ker = 0 := by
    rw [positive_toeplitz_eq_shift]
    exact shift_kernel_finrank n
  have hc : Module.finrank ℂ
      (H2 ⧸ (toeplitz (continuousSymbol (fourier (T := 2 * π) (n : ℤ)))).range) = n := by
    rw [(cokernelEquivAdjointKer _ hf.1).finrank_eq, positive_toeplitz_eq_shift]
    exact adjoint_shift_kernel_finrank n
  refine ⟨hf, hk, hc, ?_⟩
  change (Module.finrank ℂ _ : ℤ) - Module.finrank ℂ _ = -(n : ℤ)
  rw [hk, hc]
  simp

/-- Backward shifts have n-dimensional kernel and zero-dimensional cokernel. -/
theorem negative_shift : Spec.NegativeShift := by
  intro n
  have hf := fourier_symbol_fredholm (-(n : ℤ))
  have hk : Module.finrank ℂ
      (toeplitz (continuousSymbol (fourier (T := 2 * π) (-(n : ℤ))))).ker = n := by
    rw [negative_toeplitz_eq_adjoint]
    exact adjoint_shift_kernel_finrank n
  have hc : Module.finrank ℂ
      (H2 ⧸ (toeplitz (continuousSymbol (fourier (T := 2 * π) (-(n : ℤ))))).range) = 0 := by
    rw [(cokernelEquivAdjointKer _ hf.1).finrank_eq, negative_toeplitz_eq_adjoint,
      ContinuousLinearMap.adjoint_adjoint]
    exact shift_kernel_finrank n
  refine ⟨hf, hk, hc, ?_⟩
  change (Module.finrank ℂ _ : ℤ) - Module.finrank ℂ _ = (n : ℤ)
  rw [hk, hc]
  simp

/-- Lift the actual phase loop through the real covering of the additive circle. -/
theorem phase_lift (φ : NonvanishingLoop) :
    ∃ a : C(unitInterval, ℝ), ∀ t, (a t : Definitions.Spec.Circle) =
      Definitions.Spec.phasePath φ t := by
  let x := AddCircle.homeomorphCircle'.symm (Definitions.Spec.loopPhase φ 0)
  obtain ⟨a, ha, _⟩ := (AddCircle.isCoveringMap_coe (2 * π)).exists_path_lifts
    (Definitions.Spec.phasePath φ).toContinuousMap
    ((AddCircle.equivIco (2 * π) 0 x : Set.Ico (0 : ℝ) (0 + 2 * π)) : ℝ)
    (by
      change Definitions.Spec.phasePath φ 0 =
        (((AddCircle.equivIco (2 * π) 0 x : Set.Ico (0 : ℝ) (0 + 2 * π)) : ℝ) :
          Definitions.Spec.Circle)
      rw [AddCircle.coe_equivIco]
      exact (Definitions.Spec.phasePath φ).source)
  exact ⟨a, fun t => congrFun ha t⟩

/-- Removing winding makes the lifted phase agree at the interval endpoints. -/
theorem phase_lift_endpoints (φ : NonvanishingLoop) (a : C(unitInterval, ℝ))
    (ha : ∀ t, (a t : Definitions.Spec.Circle) = Definitions.Spec.phasePath φ t) :
    a 1 - (winding φ : ℝ) * (2 * π) = a 0 := by
  have h := winding_lift φ a ha
  have hp : (2 * π : ℝ) ≠ 0 := by positivity
  have := (eq_div_iff hp).mp h
  linarith

/-- The lifted interval phase after removing winding descends continuously to the circle. -/
theorem residual_phase (φ : NonvanishingLoop) :
    ∃ b : C(Definitions.Spec.Circle, ℝ), ∀ t,
      φ.val t = (‖φ.val t‖ : ℂ) * fourier (T := 2 * π) (winding φ) t *
        Complex.exp ((b t : ℂ) * Complex.I) := by
  obtain ⟨a, ha⟩ := phase_lift φ
  let q : ℝ → unitInterval := fun x => Set.projIcc 0 1 zero_le_one (x / (2 * π))
  have hq : Continuous q := continuous_projIcc.comp (by fun_prop)
  have hq0 : q 0 = 0 := by simp [q, Set.projIcc_left]
  have hq1 : q (2 * π) = 1 := by
    simp [q, Set.projIcc_right]
  let r : ℝ → ℝ := fun x => a (q x) - (winding φ : ℝ) * x
  have hr : Continuous r := (a.continuous.comp hq).sub (by fun_prop)
  have hre : r 0 = r (2 * π) := by
    dsimp [r]
    rw [hq0, hq1, mul_zero, sub_zero]
    exact (phase_lift_endpoints φ a ha).symm
  let b : C(Definitions.Spec.Circle, ℝ) :=
    ⟨AddCircle.liftIco (2 * π) 0 r,
      AddCircle.liftIco_zero_continuous hre hr.continuousOn⟩
  refine ⟨b, ?_⟩
  intro t
  let x : ℝ := AddCircle.equivIco (2 * π) 0 t
  have hx : x ∈ Set.Ico (0 : ℝ) (2 * π) := by
    simpa using (AddCircle.equivIco (2 * π) 0 t).property
  have hxt : (x : Definitions.Spec.Circle) = t := AddCircle.coe_equivIco
  have hxq : (q x : ℝ) = x / (2 * π) := by
    dsimp only [q]
    rw [Set.projIcc_of_mem]
    exact ⟨div_nonneg hx.1 (by positivity), (div_le_one (by positivity)).mpr hx.2.le⟩
  have htr : Definitions.Spec.angularTraversal (q x) = t := by
    change (1 : ℤ) • (((q x : ℝ) * (2 * π) : ℝ) : Definitions.Spec.Circle) +
      ((0 : ℝ) : Definitions.Spec.Circle) = t
    simp only [one_zsmul, AddCircle.coe_zero, add_zero]
    rw [hxq, div_mul_cancel₀ _ (by positivity : (2 * π : ℝ) ≠ 0)]
    exact hxt
  have hb : b t = a (q x) - (winding φ : ℝ) * x := rfl
  have hp := congrArg AddCircle.homeomorphCircle' (ha (q x))
  change AddCircle.homeomorphCircle' (a (q x) : Definitions.Spec.Circle) =
    AddCircle.homeomorphCircle' (AddCircle.homeomorphCircle'.symm
      (Definitions.Spec.loopPhase φ (Definitions.Spec.angularTraversal (q x)))) at hp
  rw [Homeomorph.apply_symm_apply, htr, AddCircle.homeomorphCircle'_apply_mk] at hp
  have hphase : Complex.exp ((a (q x) : ℂ) * Complex.I) =
      φ.val t / (‖φ.val t‖ : ℂ) := congrArg Subtype.val hp
  have hm : fourier (T := 2 * π) (winding φ) t =
      Complex.exp (((winding φ : ℤ) : ℂ) * (x : ℂ) * Complex.I) := by
    rw [← hxt, fourier_coe_apply]
    congr 1
    push_cast
    field_simp
  rw [hm, hb, mul_assoc, ← Complex.exp_add]
  have he : ((winding φ : ℤ) : ℂ) * (x : ℂ) * Complex.I +
      ((a (q x) - (winding φ : ℝ) * x : ℝ) : ℂ) * Complex.I =
      (a (q x) : ℂ) * Complex.I := by push_cast; ring
  rw [he, hphase]
  field_simp [Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (φ.property t))]

/-- An everywhere nonzero, uniform-norm continuous homotopy to the winding mode. -/
theorem mode_homotopy (φ : NonvanishingLoop) :
    ∃ p : unitInterval → C(Definitions.Spec.Circle, ℂ),
      Continuous p ∧ (∀ s t, p s t ≠ 0) ∧ p 0 = φ.val ∧
        p 1 = fourier (T := 2 * π) (winding φ) := by
  obtain ⟨b, hb⟩ := residual_phase φ
  let p : unitInterval → C(Definitions.Spec.Circle, ℂ) := fun s =>
    ⟨fun t => (((1 - (s : ℝ)) * ‖φ.val t‖ + (s : ℝ) : ℝ) : ℂ) *
      fourier (T := 2 * π) (winding φ) t *
      Complex.exp ((((1 - (s : ℝ)) * b t : ℝ) : ℂ) * Complex.I), by fun_prop⟩
  refine ⟨p, ?_, ?_, ?_, ?_⟩
  · apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : unitInterval × Definitions.Spec.Circle =>
      (((1 - (z.1 : ℝ)) * ‖φ.val z.2‖ + (z.1 : ℝ) : ℝ) : ℂ) *
      fourier (T := 2 * π) (winding φ) z.2 *
      Complex.exp ((((1 - (z.1 : ℝ)) * b z.2 : ℝ) : ℂ) * Complex.I))
    fun_prop
  · intro s t
    have hr : 0 < (1 - (s : ℝ)) * ‖φ.val t‖ + (s : ℝ) := by
      by_cases hs : (s : ℝ) = 1
      · simp [hs]
      · have hs1 : (s : ℝ) < 1 := lt_of_le_of_ne s.property.2 hs
        exact add_pos_of_pos_of_nonneg
          (mul_pos (sub_pos.mpr hs1) (norm_pos_iff.mpr (φ.property t))) s.property.1
    exact mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne')
      (AddCircle.toCircle ((winding φ) • t)).coe_ne_zero) (Complex.exp_ne_zero _)
  · ext t
    change (↑((1 - (0 : unitInterval) : ℝ) * ‖φ.val t‖ + (0 : unitInterval)) : ℂ) *
      fourier (T := 2 * π) (winding φ) t *
      Complex.exp (↑((1 - (0 : unitInterval) : ℝ) * b t) * Complex.I) = φ.val t
    simpa using (hb t).symm
  · ext t
    simp [p]

/-- Combine the shift calculations with a nonvanishing symbol homotopy. -/
theorem scalar_index_of_mode_homotopy
    (hpos : Spec.PositiveShift) (hneg : Spec.NegativeShift)
    (hreduce : ∀ φ : NonvanishingLoop,
      ∃ p : unitInterval → C(Definitions.Spec.Circle, ℂ),
        Continuous p ∧ (∀ s t, p s t ≠ 0) ∧ p 0 = φ.val ∧
          p 1 = fourier (T := 2 * π) (winding φ)) : Spec.ScalarIndex := by
  have hmode (m : ℤ) :
      ∃ h : IsFredholm (toeplitz (continuousSymbol (fourier (T := 2 * π) m))),
        fredholmIndex (toeplitz (continuousSymbol (fourier (T := 2 * π) m))) h = -m := by
    cases m with
    | ofNat n =>
      obtain ⟨h, _, _, hi⟩ := hpos n
      exact ⟨h, hi⟩
    | negSucc n =>
      rw [show Int.negSucc n = -((n + 1 : ℕ) : ℤ) by omega]
      obtain ⟨h, _, _, hi⟩ := hneg (n + 1)
      refine ⟨h, ?_⟩
      rw [neg_neg]
      exact hi
  intro φ
  obtain ⟨p, hp, hn, h0, h1⟩ := hreduce φ
  have hf0 := fredholm_symbols ⟨p 0, hn 0⟩
  have hf1 := fredholm_symbols ⟨p 1, hn 1⟩
  have hpath := homotopy_index p hp hn hf0 hf1
  obtain ⟨hm, hi⟩ := hmode (winding φ)
  have he := hpath
  change (Module.finrank ℂ (toeplitz (continuousSymbol (p 0))).ker : ℤ) -
      Module.finrank ℂ (H2 ⧸ (toeplitz (continuousSymbol (p 0))).range) =
    (Module.finrank ℂ (toeplitz (continuousSymbol (p 1))).ker : ℤ) -
      Module.finrank ℂ (H2 ⧸ (toeplitz (continuousSymbol (p 1))).range) at he
  rw [h0, h1] at he
  exact ⟨fredholm_symbols φ, he.trans hi⟩

/-- The scalar Toeplitz index theorem, with the source's minus-winding sign. -/
theorem scalar_index : Spec.ScalarIndex :=
  scalar_index_of_mode_homotopy positive_shift negative_shift mode_homotopy

end ExpandedFA.Toeplitz.ScalarIndex
