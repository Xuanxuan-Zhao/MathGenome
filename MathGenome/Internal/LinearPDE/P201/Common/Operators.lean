import MathGenome.Internal.LinearPDE.P201Specs.Common.Operators
import MathGenome.Internal.LinearPDE.P201.Common.SpatialInterfaces
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section
open scoped BigOperators InnerProductSpace FourierTransform SchwartzMap
namespace P201.Operators
open P201Specs P201Specs.Operators

-- Canonical definitions are re-exported at the end of this module.

theorem multiIndexCounts : ∀ {n : ℕ} (α : MultiIndex n),
  multiIndexOrder α = ∑ i : Fin n, α.count i := by
  intro n α
  exact (Multiset.sum_count_eq_card (fun _ _ => Finset.mem_univ _)).symm

private def phaseLinear {n : ℕ} (ξ : Space n) : Space n →L[ℝ] ℂ :=
  Complex.I • (Complex.ofRealCLM.comp ((innerSL ℝ).flip ξ))

private theorem phaseLinear_apply {n : ℕ} (ξ x : Space n) :
    phaseLinear ξ x = Complex.I * (inner ℝ x ξ : ℝ) := rfl

private theorem planeWave_hasFDerivAt {n : ℕ} (ξ x : Space n) :
    HasFDerivAt (planeWave ξ) (planeWave ξ x • phaseLinear ξ) x := by
  exact ((phaseLinear ξ).hasFDerivAt).cexp

private theorem planeWave_coordinate {n : ℕ} (ξ x : Space n) (i : Fin n) :
    fderiv ℝ (planeWave ξ) x (coordinate n i) =
      (Complex.I * (ξ i : ℂ)) * planeWave ξ x := by
  rw [(planeWave_hasFDerivAt ξ x).fderiv]
  simp only [smul_apply, phaseLinear_apply, smul_eq_mul]
  change planeWave ξ x * (Complex.I * (inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i) ξ : ℝ)) = _
  rw [EuclideanSpace.basisFun_inner]
  ring

private theorem partialWord_planeWave {n : ℕ} (l : List (Fin n)) (ξ : Space n) :
    P102.U4.partialWord (planeWave ξ) l =
      fun x => (l.map (fun i => Complex.I * (ξ i : ℂ))).prod * planeWave ξ x := by
  induction l with
  | nil => funext x; simp [P102.U4.partialWord]
  | cons i l ih =>
    funext x
    simp only [P102.U4.partialWord, ih, List.map_cons, List.prod_cons]
    rw [fderiv_const_mul (planeWave_hasFDerivAt ξ x).differentiableAt]
    simp only [smul_apply, smul_eq_mul, planeWave_coordinate]
    ring

theorem planeWaveDerivative : ∀ {n : ℕ} (α : MultiIndex n) (ξ x : Space n),
  multiPartial (planeWave ξ) α x = symbolMonomial α ξ * planeWave ξ x := by
  intro n α ξ x
  change P102.U4.multiPartial (planeWave ξ) α x = _
  rw [P102.U4.multiPartial, partialWord_planeWave]
  dsimp only
  congr 1
  change (((α.sort (· ≤ ·)) : Multiset (Fin n)).map (fun i => Complex.I * (ξ i : ℂ))).prod = _
  exact congrArg Multiset.prod (congrArg (Multiset.map (fun i => Complex.I * (ξ i : ℂ)))
    (Multiset.sort_eq _ _))

theorem exponentialSubstitution : ∀ {n m : ℕ} (a : Coefficients n m) (x ξ : Space n),
  Complex.exp (-(Complex.I * (inner ℝ x ξ : ℝ))) * applyOperator a (planeWave ξ) x =
    fullSymbol a x ξ := by
  intro n m a x ξ
  unfold applyOperator fullSymbol
  simp_rw [planeWaveDerivative, ← mul_assoc]
  rw [← Finset.sum_mul, mul_left_comm,
    show Complex.exp (-(Complex.I * (inner ℝ x ξ : ℝ))) * planeWave ξ x = 1 by
      rw [planeWave, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]]
  simp

private theorem monomial_smul {n : ℕ} (α : MultiIndex n) (r : ℝ) (ξ : Space n) :
    symbolMonomial α (r • ξ) = (r : ℂ) ^ α.card * symbolMonomial α ξ := by
  induction α using Multiset.induction_on with
  | empty => simp [symbolMonomial]
  | cons i α ih =>
    simp only [symbolMonomial, Multiset.map_cons, Multiset.prod_cons,
      Multiset.card_cons, pow_succ] at *
    rw [show Complex.I * ((r • ξ) i : ℂ) = (r : ℂ) * (Complex.I * (ξ i : ℂ)) by
      simp only [PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul]; ring, ih]
    ring

theorem homogeneousSymbolScaling : ∀ {n m : ℕ} (a : Coefficients n m)
    (k : ℕ) (r : ℝ) (x ξ : Space n),
  homogeneousSymbol a k x (r • ξ) = (r : ℂ) ^ k * homogeneousSymbol a k x ξ := by
  intro n m a k r x ξ
  unfold homogeneousSymbol
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  split_ifs with h
  · rw [monomial_smul, h]; ring
  · ring

theorem symbolDecomposition : ∀ {n m : ℕ} (a : Coefficients n m) (x ξ : Space n),
  fullSymbol a x ξ = ∑ k ∈ Finset.range (m + 1), homogeneousSymbol a k x ξ := by
  intro n m a x ξ
  unfold fullSymbol homogeneousSymbol
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  simp [Finset.mem_range.mpr (Nat.lt_succ_of_le α.property)]

theorem principalHomogeneous : ∀ {n m : ℕ} (a : Coefficients n m)
    (r : ℝ) (x ξ : Space n),
  principalSymbol a x (r • ξ) = (r : ℂ) ^ m * principalSymbol a x ξ := by
  intro n m a r x ξ
  exact homogeneousSymbolScaling a m r x ξ

private theorem schwartzWord_apply {n : ℕ} (l : List (Fin n))
    (f : SchwartzMap (Space n) ℂ) :
    (schwartzWord l f : Space n → ℂ) = P102.U4.partialWord f l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    funext x
    change fderiv ℝ (schwartzWord l f) x (coordinate n i) = _
    rw [ih]
    rfl

theorem schwartzPartialRealization : ∀ {n : ℕ} (α : MultiIndex n)
    (f : SchwartzMap (Space n) ℂ) (x : Space n),
  schwartzPartial α f x = multiPartial f α x := by
  intro n α f x
  exact congrFun (schwartzWord_apply (α.sort (· ≤ ·)) f) x

theorem constantSchwartzOperatorRealization : ∀ {n m : ℕ} (a : Index n m → ℂ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n),
  constantSchwartzOperator a f x = applyOperator (fun α _ => a α) f x := by
  intro n m a f x
  simp [constantSchwartzOperator, applyOperator, schwartzPartialRealization]

private theorem fourier_schwartzWord {n : ℕ} (l : List (Fin n))
    (f : SchwartzMap (Space n) ℂ) (ξ : Space n) :
    (𝓕 (schwartzWord l f)) ξ =
      (l.map (fun i => Complex.I * (((2 * Real.pi) • ξ) i : ℂ))).prod * (𝓕 f) ξ := by
  induction l with
  | nil => simp [schwartzWord]
  | cons i l ih =>
    rw [schwartzWord, SchwartzMap.fourier_lineDerivOp_eq]
    simp only [smul_apply, SchwartzMap.smulLeftCLM_apply_apply
      (by fun_prop : (fun y : Space n => inner ℝ y (coordinate n i)).HasTemperateGrowth),
      List.map_cons, List.prod_cons]
    rw [ih]
    simp only [P201.coordinate, P201Specs.coordinate, P102.U4.coordinateVector,
      EuclideanSpace.inner_basisFun_real, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul,
      Complex.ofReal_ofNat, Complex.real_smul, smul_eq_mul]
    ring

private theorem fourier_schwartzPartial {n : ℕ} (α : MultiIndex n)
    (f : SchwartzMap (Space n) ℂ) (ξ : Space n) :
    (𝓕 (schwartzPartial α f)) ξ =
      symbolMonomial α ((2 * Real.pi) • ξ) * (𝓕 f) ξ := by
  rw [schwartzPartial, fourier_schwartzWord]
  congr 1
  exact congrArg Multiset.prod (congrArg (Multiset.map _)
    (Multiset.sort_eq α (· ≤ ·)))

theorem fourierMultiplier : ∀ {n m : ℕ} (a : Index n m → ℂ)
    (f : SchwartzMap (Space n) ℂ) (ξ : Space n),
  (FourierTransform.fourierCLM ℂ (SchwartzMap (Space n) ℂ)) (constantSchwartzOperator a f) ξ =
    fourierSymbol a ξ * (FourierTransform.fourierCLM ℂ (SchwartzMap (Space n) ℂ)) f ξ := by
  intro n m a f ξ
  simp only [constantSchwartzOperator, map_sum, map_smul, sum_apply,
    smul_apply, fourierSymbol, fullSymbol, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro α _
  change a α * (𝓕 (schwartzPartial α.val f)) ξ = _
  rw [fourier_schwartzPartial, FourierTransform.fourierCLM_apply]
  ring

theorem fourierIntegralMultiplier : ∀ {n m : ℕ} (a : Index n m → ℂ)
    (f : SchwartzMap (Space n) ℂ) (ξ : Space n),
    fourierIntegral (constantSchwartzOperator a f) ξ = fourierSymbol a ξ * fourierIntegral f ξ := by
  intro n m a f ξ
  change P201Specs.fourierIntegral (constantSchwartzOperator a f) ξ =
    fourierSymbol a ξ * P201Specs.fourierIntegral f ξ
  rw [P201.fourierNormalization, P201.fourierNormalization]
  simpa only [FourierTransform.fourierCLM_apply, SchwartzMap.fourier_coe]
    using fourierMultiplier a f ξ

theorem fourierPrincipal : ∀ {n m : ℕ} (a : Index n m → ℂ) (ξ : Space n),
  fourierPrincipalSymbol a ξ = (2 * Real.pi : ℂ) ^ m * principalSymbol (fun α _ => a α) 0 ξ := by
  intro n m a ξ
  simpa only [fourierPrincipalSymbol, Complex.ofReal_mul, Complex.ofReal_ofNat]
    using principalHomogeneous (fun α _ => a α) (2 * Real.pi) 0 ξ

theorem semilinearIsQuasilinear : ∀ {X W E : Type} [AddCommGroup E] [Module ℝ E]
  (F : X → W → E → ℝ), SemilinearJetDependence F → QuasilinearJetDependence F := by
  intro X W E _ _ F h
  obtain ⟨a, b, h⟩ := h
  exact ⟨fun x _ => a x, b, h⟩

theorem semilinearExampleClassification : ∀ n, SemilinearJetDependence (semilinearExample n) := by
  intro n
  exact ⟨fun _ => Matrix.traceLinearMap (Fin n) ℝ ℝ,
    fun _ w => w.1 ^ 3, fun _ _ _ => rfl⟩

theorem quasilinearExampleClassification : ∀ n, QuasilinearJetDependence (quasilinearExample n) := by
  intro n
  refine ⟨fun _ w => (1 + w.1 ^ 2) • Matrix.traceLinearMap (Fin n) ℝ ℝ,
    fun _ _ => 0, ?_⟩
  intro x w H
  simp [quasilinearExample]

theorem mongeAmpereExampleClassification : ∀ n, 2 ≤ n → FullyNonlinearJetDependence (mongeAmpereExample n) := by
  intro n hn h
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨a, b, hab⟩ := h
  have h0 := hab 0 0 0
  have h1 := hab 0 0 1
  have h2 := hab 0 0 ((2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))
  simp only [mongeAmpereExample, Matrix.det_zero, zero_sub, map_zero, zero_add] at h0
  simp only [mongeAmpereExample, Matrix.det_one, sub_self] at h1
  simp only [mongeAmpereExample, Matrix.det_smul, Matrix.det_one, Fintype.card_fin,
    mul_one, map_smul, smul_eq_mul] at h2
  have hp : (2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn
  norm_num at hp
  linarith

theorem exampleRealizations : ∀ {n : ℕ} (u : Space n → ℝ) (x : Space n),
  semilinearExample n x (u x, gradient u x) (hessian u x) = laplacian u x + u x ^ 3 ∧
  quasilinearExample n x (u x, gradient u x) (hessian u x) = (1 + u x ^ 2) * laplacian u x ∧
  (mongeAmpereExample n x (u x, gradient u x) (hessian u x) = 0 ↔ (hessian u x).det = 1) := by
  intro n u x
  refine ⟨rfl, rfl, ?_⟩
  simp [mongeAmpereExample, sub_eq_zero]

theorem heatDegenerate : ∀ {n : ℕ} (κ τ : ℝ), heatQuadratic κ τ (0 : Space n) = 0 := by
  intro n κ τ
  simp [heatQuadratic]

theorem heatDiffusion : ∀ {n : ℕ} (κ : ℝ), IsForwardHeat κ →
  ∀ ξ : Space n, κ * ‖ξ‖ ^ 2 = -heatQuadratic κ 0 ξ := by
  intro n κ _ ξ
  simp [heatQuadratic]

theorem symbolMonomialCounts : ∀ {n : ℕ} (α : MultiIndex n) (ξ : Space n),
    symbolMonomial α ξ = ∏ i : Fin n, (Complex.I * (ξ i : ℂ)) ^ α.count i := by
  intro n α ξ
  unfold symbolMonomial
  rw [Finset.prod_multiset_map_count]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  simp only [Multiset.mem_toFinset] at hi ⊢
  simp [Multiset.count_eq_zero.mpr hi]

theorem linearIsSemilinear : ∀ {X W E : Type} [AddCommGroup W] [Module ℝ W]
    [AddCommGroup E] [Module ℝ E] (F : X → W → E → ℝ),
    LinearJetDependence F → SemilinearJetDependence F := by
  intro X W E _ _ _ _ F h
  obtain ⟨a, ha⟩ := h
  refine ⟨fun x => (a x).comp (LinearMap.inr ℝ W E), fun x w => a x (w, 0), ?_⟩
  intro x w H
  rw [ha]
  change a x (w, H) = a x (0, H) + a x (w, 0)
  rw [← map_add]
  congr 1
  simp

theorem heatUniformEllipticity : ∀ {n : ℕ} (Ω : Domain n) (κ : ℝ),
    IsForwardHeat κ → UniformPositiveEllipticity Ω
      (fun _ => κ • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  intro n Ω κ hκ
  refine ⟨κ, hκ, ?_⟩
  intro x hx ξ
  have he : quadraticPrincipal (κ • (1 : Matrix (Fin n) (Fin n) ℝ)) ξ = κ * ‖ξ‖ ^ 2 := by
    simp only [quadraticPrincipal, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]
    rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [Real.norm_eq_abs, pow_two, mul_assoc]
  exact le_of_eq he.symm

theorem heatDegeneracyInsufficient : ∀ n : ℕ,
    heatQuadratic (-1) 1 (0 : Space n) = 0 ∧ ¬ IsForwardHeat (-1) := by
  intro n
  simp [heatQuadratic, IsForwardHeat]

-- Public representations agree definitionally with the independent canonical values.
abbrev Index : P201Specs.Operators.IndexType := @P201Specs.Operators.Index
abbrev multiIndexOrder : P201Specs.Operators.multiIndexOrderType := @P201Specs.Operators.multiIndexOrder
abbrev Coefficients : P201Specs.Operators.CoefficientsType := @P201Specs.Operators.Coefficients
abbrev ScalarOperator : P201Specs.Operators.ScalarOperatorType := @P201Specs.Operators.ScalarOperator
abbrev operatorOrder : P201Specs.Operators.operatorOrderType := @P201Specs.Operators.operatorOrder
abbrev applyOperator : P201Specs.Operators.applyOperatorType := @P201Specs.Operators.applyOperator
abbrev LinearEquation : P201Specs.Operators.LinearEquationType := @P201Specs.Operators.LinearEquation
abbrev symbolMonomial : P201Specs.Operators.symbolMonomialType := @P201Specs.Operators.symbolMonomial
abbrev fullSymbol : P201Specs.Operators.fullSymbolType := @P201Specs.Operators.fullSymbol
abbrev homogeneousSymbol : P201Specs.Operators.homogeneousSymbolType := @P201Specs.Operators.homogeneousSymbol
abbrev principalSymbol : P201Specs.Operators.principalSymbolType := @P201Specs.Operators.principalSymbol
abbrev planeWave : P201Specs.Operators.planeWaveType := @P201Specs.Operators.planeWave
abbrev IsElliptic : P201Specs.Operators.IsEllipticType := @P201Specs.Operators.IsElliptic
abbrev quadraticPrincipal : P201Specs.Operators.quadraticPrincipalType := @P201Specs.Operators.quadraticPrincipal
abbrev UniformPositiveEllipticity : P201Specs.Operators.UniformPositiveEllipticityType := @P201Specs.Operators.UniformPositiveEllipticity
abbrev fourierSymbol : P201Specs.Operators.fourierSymbolType := @P201Specs.Operators.fourierSymbol
abbrev fourierPrincipalSymbol : P201Specs.Operators.fourierPrincipalSymbolType := @P201Specs.Operators.fourierPrincipalSymbol
abbrev schwartzWord : P201Specs.Operators.schwartzWordType := @P201Specs.Operators.schwartzWord
abbrev schwartzPartial : P201Specs.Operators.schwartzPartialType := @P201Specs.Operators.schwartzPartial
abbrev constantSchwartzOperator : P201Specs.Operators.constantSchwartzOperatorType := @P201Specs.Operators.constantSchwartzOperator
abbrev LowerJet : P201Specs.Operators.LowerJetType := @P201Specs.Operators.LowerJet
abbrev HighestJet : P201Specs.Operators.HighestJetType := @P201Specs.Operators.HighestJet
abbrev lowerJet : P201Specs.Operators.lowerJetType := @P201Specs.Operators.lowerJet
abbrev highestJet : P201Specs.Operators.highestJetType := @P201Specs.Operators.highestJet
abbrev JetEquation : P201Specs.Operators.JetEquationType := @P201Specs.Operators.JetEquation
abbrev LinearJetDependence : P201Specs.Operators.LinearJetDependenceType := @P201Specs.Operators.LinearJetDependence
abbrev SemilinearJetDependence : P201Specs.Operators.SemilinearJetDependenceType := @P201Specs.Operators.SemilinearJetDependence
abbrev QuasilinearJetDependence : P201Specs.Operators.QuasilinearJetDependenceType := @P201Specs.Operators.QuasilinearJetDependence
abbrev FullyNonlinearJetDependence : P201Specs.Operators.FullyNonlinearJetDependenceType := @P201Specs.Operators.FullyNonlinearJetDependence
abbrev SecondLowerJet : P201Specs.Operators.SecondLowerJetType := @P201Specs.Operators.SecondLowerJet
abbrev hessian : P201Specs.Operators.hessianType := @P201Specs.Operators.hessian
abbrev semilinearExample : P201Specs.Operators.semilinearExampleType := @P201Specs.Operators.semilinearExample
abbrev quasilinearExample : P201Specs.Operators.quasilinearExampleType := @P201Specs.Operators.quasilinearExample
abbrev mongeAmpereExample : P201Specs.Operators.mongeAmpereExampleType := @P201Specs.Operators.mongeAmpereExample
abbrev waveQuadratic : P201Specs.Operators.waveQuadraticType := @P201Specs.Operators.waveQuadratic
abbrev waveOperator : P201Specs.Operators.waveOperatorType := @P201Specs.Operators.waveOperator
abbrev heatOperator : P201Specs.Operators.heatOperatorType := @P201Specs.Operators.heatOperator
abbrev heatQuadratic : P201Specs.Operators.heatQuadraticType := @P201Specs.Operators.heatQuadratic
abbrev IsForwardHeat : P201Specs.Operators.IsForwardHeatType := @P201Specs.Operators.IsForwardHeat

end P201.Operators
