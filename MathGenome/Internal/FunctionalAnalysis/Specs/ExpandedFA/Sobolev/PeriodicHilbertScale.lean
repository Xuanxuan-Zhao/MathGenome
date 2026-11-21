import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.TorusFourierBasis
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.PeriodicDistributions
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! The period-one circle Hilbert scale, in its faithful Fourier-sequence model.
An element is its actual coefficient sequence, not a sequence of normalized
coordinates. Negative orders are included, with no L¹ or L² restriction.
The normalization equivalence equips this subtype with its weighted Hilbert norm.
-/
noncomputable section
open MeasureTheory Filter
open scoped Real ENNReal Topology ComplexConjugate

open MeasureTheory
open scoped ContDiff
namespace ExpandedFA.Sobolev.CircleBridge
open ExpandedFA.PartIV.Periodic

abbrev Circle := AddCircle (1 : ℝ)

def torusCircle : Torus 1 ≃ₜ Circle := Homeomorph.funUnique (Fin 1) Circle

def latticeInt : Lattice 1 ≃ ℤ := Equiv.funUnique (Fin 1) ℤ

@[simp] theorem torusCircle_apply (q : Torus 1) : torusCircle q = q 0 := rfl
@[simp] theorem torusCircle_symm_apply (q : Circle) (i : Fin 1) : torusCircle.symm q i = q := rfl
@[simp] theorem latticeInt_apply (n : Lattice 1) : latticeInt n = n 0 := rfl
@[simp] theorem latticeInt_symm_apply (n : ℤ) (i : Fin 1) : latticeInt.symm n i = n := rfl

 theorem torusCircle_measurePreserving :
    MeasurePreserving torusCircle (torusHaar 1) AddCircle.haarAddCircle := by
  exact measurePreserving_funUnique AddCircle.haarAddCircle (Fin 1)

 theorem circle_integral (f : Circle → ℂ) :
    (∫ q : Torus 1, f (torusCircle q) ∂torusHaar 1) =
      ∫ q : Circle, f q ∂AddCircle.haarAddCircle := by
  exact torusCircle_measurePreserving.integral_comp
    (MeasurableEquiv.funUnique (Fin 1) Circle).measurableEmbedding f

 theorem character_circle (n : Lattice 1) (q : Torus 1) :
    UnitAddTorus.mFourier n q = fourier (n 0) (torusCircle q) := by
  simp [UnitAddTorus.mFourier, torusCircle]

/-- A smooth test as an actual function on the one-dimensional quotient. -/
def circleTestSubmodule : Submodule ℂ (Circle → ℂ) where
  carrier := {f | ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => f (x : Circle))}
  zero_mem' := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => (0 : ℂ))
    exact contDiff_const
  add_mem' := by
    intro f g hf hg
    exact (show ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => f (x : Circle)) from hf).add hg
  smul_mem' := by
    intro c f hf
    exact (show ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => f (x : Circle)) from hf).const_smul c

abbrev CircleTest := ↥circleTestSubmodule

def testCircle (φ : Smooth ℂ 1) : CircleTest :=
  ⟨fun q => φ.val (torusCircle.symm q), by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => φ.val (quotient (fun _ : Fin 1 => x)))
    exact (contDiff_lift φ).comp (contDiff_pi.mpr fun _ => contDiff_id)⟩

def testTorus (φ : CircleTest) : Smooth ℂ 1 :=
  ⟨fun q => φ.val (torusCircle q), by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x : ExpandedFA.Distributions.Domain 1 =>
      φ.val (x 0 : Circle))
    exact (show ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => φ.val (x : Circle)) from φ.property).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).contDiff⟩

 def testCircleEquiv : Smooth ℂ 1 ≃ₗ[ℂ] CircleTest where
  toFun := testCircle
  invFun := testTorus
  left_inv φ := by
    apply Subtype.ext; funext q
    change φ.val (torusCircle.symm (torusCircle q)) = φ.val q
    rw [torusCircle.symm_apply_apply]
  right_inv φ := by apply Subtype.ext; funext q; simp [testCircle, testTorus]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem testFourierCoeff_circle (φ : Smooth ℂ 1) (n : Lattice 1) :
    testFourierCoeff φ n = fourierCoeff (testCircle φ).val (n 0) := by
  unfold testFourierCoeff fourierCoeff
  simp only [smul_eq_mul]
  rw [← circle_integral]
  apply integral_congr_ae
  filter_upwards [] with q
  rw [character_circle]
  simp only [Pi.neg_apply, testCircle]
  rw [torusCircle.symm_apply_apply]

@[simp] theorem quotient_circle_line (x : ℝ) :
    quotient (x • ExpandedFA.Distributions.coordinateVector (0 : Fin 1)) =
      torusCircle.symm (x : Circle) := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [quotient, ExpandedFA.Distributions.coordinateVector]

 theorem hasDerivAt_circleTest (φ : Smooth ℂ 1) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (testCircle φ).val (y : Circle))
      ((testCircle (FourierDecay.jet φ (fun _ : Fin 1 => 0))).val (x : Circle)) x := by
  simpa only [testCircle, zero_add, quotient_circle_line] using
    FourierDecay.hasDerivAt_shift φ (0 : Fin 1) 0 x

/-- The canonical smooth topology, expressed through the coordinate identification
of the one-dimensional torus and circle. -/
instance circleTestTopologicalSpace : TopologicalSpace CircleTest :=
  TopologicalSpace.induced testTorus inferInstance

@[simp] theorem testTorus_testCircle (φ : Smooth ℂ 1) :
    testTorus (testCircle φ) = φ := testCircleEquiv.left_inv φ

@[simp] theorem testCircle_testTorus (φ : CircleTest) :
    testCircle (testTorus φ) = φ := testCircleEquiv.right_inv φ

 def testCircleContinuousEquiv : Smooth ℂ 1 ≃L[ℂ] CircleTest where
  toLinearEquiv := testCircleEquiv
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    convert continuous_id (X := Smooth ℂ 1) using 1
    funext φ
    exact testCircleEquiv.left_inv φ
  continuous_invFun := continuous_induced_dom

abbrev CircleDistribution := CircleTest →L[ℂ] ℂ

/-- An actual continuous complex-linear functional on smooth circle functions. -/
 def circleDistribution (U : TorusDistribution ℂ 1) : CircleDistribution :=
  U.comp testCircleContinuousEquiv.symm.toContinuousLinearMap

@[simp] theorem circleDistribution_apply (U : TorusDistribution ℂ 1) (φ : CircleTest) :
    circleDistribution U φ = U (testTorus φ) := rfl

@[simp] theorem circleDistribution_testCircle (U : TorusDistribution ℂ 1) (φ : Smooth ℂ 1) :
    circleDistribution U (testCircle φ) = U φ := by
  change U (testCircleEquiv.symm (testCircleEquiv φ)) = U φ
  rw [testCircleEquiv.symm_apply_apply]

 def circleDistributionEquiv : TorusDistribution ℂ 1 ≃ₗ[ℂ] CircleDistribution where
  toFun := circleDistribution
  invFun U := U.comp testCircleContinuousEquiv.toContinuousLinearMap
  left_inv U := by
    ext φ
    exact circleDistribution_testCircle U φ
  right_inv U := by
    ext φ
    change U (testCircleEquiv (testCircleEquiv.symm φ)) = U φ
    rw [testCircleEquiv.apply_symm_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 def circleCharacter (n : ℤ) : CircleTest := testCircle (character (latticeInt.symm n))

@[simp] theorem circleCharacter_apply (n : ℤ) (q : Circle) :
    (circleCharacter n).val q = fourier n q := by
  change UnitAddTorus.mFourier (latticeInt.symm n) (torusCircle.symm q) = _
  rw [character_circle]
  simp

 theorem circleDistribution_coeff (U : TorusDistribution ℂ 1) (n : ℤ) :
    circleDistribution U (circleCharacter (-n)) = distributionCoeff U (latticeInt.symm n) := by
  rw [circleCharacter, circleDistribution_testCircle]
  rfl

 def circleTestDerivative (φ : CircleTest) : CircleTest :=
  testCircle (FourierDecay.jet (testTorus φ) (fun _ : Fin 1 => 0))

 theorem hasDerivAt_circleTestDerivative (φ : CircleTest) (x : ℝ) :
    HasDerivAt (fun y : ℝ => φ.val (y : Circle))
      ((circleTestDerivative φ).val (x : Circle)) x := by
  have h := hasDerivAt_circleTest (testTorus φ) x
  have heq : testCircle (testTorus φ) = φ := testCircleEquiv.right_inv φ
  simpa only [circleTestDerivative, heq] using h

 theorem circleTestDerivative_value (φ : CircleTest) (x : ℝ) :
    (circleTestDerivative φ).val (x : Circle) =
      deriv (fun y : ℝ => φ.val (y : Circle)) x :=
  (hasDerivAt_circleTestDerivative φ x).deriv.symm

 theorem circleDerivative_transport (U V : TorusDistribution ℂ 1)
    (h : ∀ φ : Smooth ℂ 1,
      V φ = -U (FourierDecay.jet φ (fun _ : Fin 1 => 0))) (φ : CircleTest) :
    circleDistribution V φ = -circleDistribution U (circleTestDerivative φ) := by
  change V (testTorus φ) = -circleDistribution U
    (testCircle (FourierDecay.jet (testTorus φ) (fun _ : Fin 1 => 0)))
  rw [circleDistribution_testCircle]
  exact h (testTorus φ)

def circleHigherTestDerivative (k : ℕ) (φ : CircleTest) : CircleTest :=
  testCircle (FourierDecay.jet (testTorus φ) (fun _ : Fin k => (0 : Fin 1)))

end ExpandedFA.Sobolev.CircleBridge


namespace ExpandedFA.Sobolev.PeriodicHilbertScale

def frequencyWeight (n : ℤ) : ℝ := 1 + 4 * π ^ 2 * (n : ℝ) ^ 2

theorem frequencyWeight_pos (n : ℤ) : 0 < frequencyWeight n := by
  dsimp [frequencyWeight]; positivity

def weight (s : ℝ) (n : ℤ) : ℝ := frequencyWeight n ^ (s / 2)

theorem weight_pos (s : ℝ) (n : ℤ) : 0 < weight s n :=
  Real.rpow_pos_of_pos (frequencyWeight_pos n) _

def weightedSubmodule (s : ℝ) : Submodule ℂ (ℤ → ℂ) where
  carrier := {a | Memℓp (fun n => (weight s n : ℂ) * a n) 2}
  zero_mem' := by
    change Memℓp (fun n : ℤ => (weight s n : ℂ) * 0) 2
    simpa only [mul_zero] using (zero_mem_ℓp' (E := fun _ : ℤ => ℂ) (p := 2))
  add_mem' := by
    intro a b ha hb
    change Memℓp (fun n => (weight s n : ℂ) * (a n + b n)) 2
    simpa only [Pi.add_def, mul_add] using ha.add hb
  smul_mem' := by
    intro c a ha
    change Memℓp (fun n => (weight s n : ℂ) * (c * a n)) 2
    simpa only [mul_left_comm] using ha.const_mul c

/-- Fourier coefficients of a periodic Sobolev element, for any real order. -/
def Hs (s : ℝ) := ↥(weightedSubmodule s)

instance (s : ℝ) : AddCommGroup (Hs s) := inferInstanceAs (AddCommGroup ↥(weightedSubmodule s))
instance (s : ℝ) : Module ℂ (Hs s) := inferInstanceAs (Module ℂ ↥(weightedSubmodule s))
instance (s : ℝ) : CoeFun (Hs s) (fun _ => ℤ → ℂ) := ⟨fun u => u.1⟩

/-- Multiplication by the positive square root of the Sobolev weight. -/
def normalize (s : ℝ) : Hs s ≃ₗ[ℂ] lp (fun _ : ℤ => ℂ) 2 where
  toFun u := ⟨fun n => (weight s n : ℂ) * u n, u.2⟩
  invFun a := ⟨fun n => a n / (weight s n : ℂ), by
    change Memℓp (fun n => (weight s n : ℂ) * (a n / (weight s n : ℂ))) 2
    convert lp.memℓp a using 1
    funext n
    have h : (weight s n : ℂ) ≠ 0 := by exact_mod_cast (weight_pos s n).ne'
    field_simp⟩
  left_inv u := by
    apply Subtype.ext; funext n
    change (weight s n : ℂ) * u n / (weight s n : ℂ) = u n
    have h : (weight s n : ℂ) ≠ 0 := by exact_mod_cast (weight_pos s n).ne'
    field_simp
  right_inv a := by
    apply lp.ext; funext n
    change (weight s n : ℂ) * (a n / (weight s n : ℂ)) = a n
    have h : (weight s n : ℂ) ≠ 0 := by exact_mod_cast (weight_pos s n).ne'
    field_simp
  map_add' u v := by apply lp.ext; funext n; exact mul_add _ _ _
  map_smul' c u := by apply lp.ext; funext n; exact mul_left_comm _ _ _

instance (s : ℝ) : NormedAddCommGroup (Hs s) :=
  NormedAddCommGroup.induced _ _ (normalize s).toLinearMap (normalize s).injective
instance (s : ℝ) : NormedSpace ℂ (Hs s) :=
  NormedSpace.induced ℂ _ _ (normalize s).toLinearMap
instance (s : ℝ) : InnerProductSpace ℂ (Hs s) :=
  InnerProductSpace.induced (normalize s).toLinearMap

def normalizedEquiv (s : ℝ) : Hs s ≃ₗᵢ[ℂ] lp (fun _ : ℤ => ℂ) 2 :=
  { normalize s with norm_map' := fun _ => rfl }

instance (s : ℝ) : CompleteSpace (Hs s) := (normalizedEquiv s).toIsometryEquiv.completeSpace

/-- Coefficient evaluation is continuous for every positive or negative order. -/
def coefficientCLM (s : ℝ) (n : ℤ) : Hs s →L[ℂ] ℂ :=
  (weight s n : ℂ)⁻¹ • ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).comp
    (normalizedEquiv s).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem coefficientCLM_apply (s : ℝ) (n : ℤ) (u : Hs s) :
    coefficientCLM s n u = u n := by
  have hs : (weight s n : ℂ) ≠ 0 := by exact_mod_cast (weight_pos s n).ne'
  change (weight s n : ℂ)⁻¹ * ((weight s n : ℂ) * u n) = u n
  field_simp

instance (s : ℝ) : InnerProductSpace ℝ (Hs s) := InnerProductSpace.complexToReal

/-- The real-valued circle space has conjugate-symmetric Fourier coefficients.
It is not the space of arbitrary real coefficient sequences. -/
def realSubmodule (s : ℝ) : Submodule ℝ (Hs s) where
  carrier := {u | ∀ n : ℤ, u (-n) = star (u n)}
  zero_mem' := by intro n; change (0 : ℂ) = star 0; simp
  add_mem' := by
    intro u v hu hv n
    change u (-n) + v (-n) = star (u n + v n)
    rw [hu, hv, star_add]
  smul_mem' := by
    intro c u hu n
    change (c : ℂ) * u (-n) = star ((c : ℂ) * u n)
    rw [hu, star_mul]
    simp [mul_comm]

abbrev RealHs (s : ℝ) := ↥(realSubmodule s)

theorem realSubmodule_closed (s : ℝ) : IsClosed (realSubmodule s : Set (Hs s)) := by
  change IsClosed {u : Hs s | ∀ n : ℤ, u (-n) = star (u n)}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro n
  have hc (k : ℤ) : Continuous (fun u : Hs s => u k) :=
    (coefficientCLM s k).continuous.congr (fun u => coefficientCLM_apply s k u)
  exact isClosed_eq (hc (-n)) (continuous_star.comp (hc n))

instance (s : ℝ) : CompleteSpace (RealHs s) := by
  let : IsClosed (realSubmodule s : Set (Hs s)) := realSubmodule_closed s
  infer_instance

/-- Coefficient access with the Sobolev order kept in the type. -/
def coefficient {s : ℝ} (u : Hs s) (n : ℤ) : ℂ := u n

/-- The actual finite Fourier synthesis on the period-one circle. -/
def fourierPolynomial (a : ℤ → ℂ) (F : Finset ℤ) (x : ℝ) : ℂ :=
  ∑ n ∈ F, a n * fourier (T := 1) n (x : AddCircle (1 : ℝ))


/-- Complex conjugation of an actual smooth periodic test. -/
def conjugateTest {d : ℕ} (φ : ExpandedFA.PartIV.Periodic.Smooth ℂ d) :
    ExpandedFA.PartIV.Periodic.Smooth ℂ d :=
  ⟨fun q => conj (φ.val q), Complex.conjCLE.contDiff.comp
    (ExpandedFA.PartIV.Periodic.contDiff_lift φ)⟩

open ExpandedFA.PartIV.Periodic CircleBridge

def circleConjugateTest (φ : CircleTest) : CircleTest :=
  testCircle (conjugateTest (testTorus φ))

namespace Spec

def SpaceType := ℝ → Type
def SpaceValue : SpaceType := Hs

def Identification : Prop :=
  (∀ (s : ℝ) (a : ℤ → ℂ), (∃ u : Hs s, (fun n => u n) = a) ↔
    Summable (fun n => frequencyWeight n ^ s * ‖a n‖ ^ 2)) ∧
  (∀ (s : ℝ) (u : Hs s), HasSum
    (fun n => frequencyWeight n ^ s * ‖u n‖ ^ 2) (‖u‖ ^ 2))

/-- At order zero, these coefficients are exactly the actual Fourier integrals
on the period-one circle, with normalized Haar measure. -/
def ZeroFourier : Prop :=
  ∃ U : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)) ≃ₗᵢ[ℂ] Hs 0,
    ∀ f n, U f n = fourierCoeff f n

def Duality : Prop :=
  ∀ s : ℝ, ∃ U : Hs (-s) ≃ₗᵢ[ℂ] (Hs s →L[ℂ] ℂ),
    ∀ v u, Summable (fun n : ℤ => ‖u n * v (-n)‖) ∧
      U v u = ∑' n : ℤ, u n * v (-n)

def Derivative : Prop :=
  ∀ s : ℝ, ∃ D : Hs s →L[ℂ] Hs (s - 1),
    (∀ u n, D u n = (2 * π * Complex.I * n : ℂ) * u n) ∧
    (∀ u, ‖D u‖ ≤ ‖u‖)

/-- Actual Fourier truncations, a uniform unit-ball error bound, and compactness.
The inclusion preserves every coefficient and is injective. -/
def CompactEmbedding : Prop :=
  ∀ s ε : ℝ, 0 < ε → ∃ J : Hs (s + ε) →L[ℂ] Hs s,
    (∀ u n, J u n = u n) ∧ Function.Injective J ∧
    IsCompactOperator J ∧
    ∃ P : ℕ → Hs (s + ε) →L[ℂ] Hs s,
      (∀ N u n, P N u n = if n.natAbs ≤ N then u n else 0) ∧
      (∀ N, FiniteDimensional ℂ (LinearMap.range (P N).toLinearMap)) ∧
      (∀ N, IsCompactOperator (P N)) ∧
      (∀ N u, ‖J u - P N u‖ ≤
        (1 + 4 * π ^ 2 * (N : ℝ) ^ 2) ^ (-ε / 2) * ‖u‖) ∧
      Tendsto P atTop (𝓝 J)

def RealIdentification : Prop :=
  (∀ (s : ℝ) (a : ℤ → ℂ), (∃ u : RealHs s, (fun n => u.val n) = a) ↔
    Summable (fun n => frequencyWeight n ^ s * ‖a n‖ ^ 2) ∧
      ∀ n : ℤ, a (-n) = star (a n)) ∧
  (∀ (s : ℝ) (u : RealHs s), HasSum
    (fun n => frequencyWeight n ^ s * ‖u.val n‖ ^ 2) (‖u‖ ^ 2))

def RealDuality : Prop :=
  ∀ s : ℝ, ∃ U : RealHs (-s) ≃ₗᵢ[ℝ] (RealHs s →L[ℝ] ℝ),
    ∀ v u, Summable (fun n : ℤ => ‖u.val n * v.val (-n)‖) ∧
      U v u = (∑' n : ℤ, u.val n * v.val (-n)).re

/-- The bilinear Fourier pairing of real elements is itself real. -/
def RealPairingReal : Prop :=
  ∀ (s : ℝ) (v : RealHs (-s)) (u : RealHs s),
    (∑' n : ℤ, u.val n * v.val (-n)).im = 0

def RealDerivative : Prop :=
  ∀ s : ℝ, ∃ D : RealHs s →L[ℝ] RealHs (s - 1),
    (∀ u n, (D u).val n = (2 * π * Complex.I * n : ℂ) * u.val n) ∧
    (∀ u, ‖D u‖ ≤ ‖u‖)

def RealCompactEmbedding : Prop :=
  ∀ s ε : ℝ, 0 < ε → ∃ J : RealHs (s + ε) →L[ℝ] RealHs s,
    (∀ u n, (J u).val n = u.val n) ∧ Function.Injective J ∧
    IsCompactOperator J ∧
    ∃ P : ℕ → RealHs (s + ε) →L[ℝ] RealHs s,
      (∀ N u n, (P N u).val n = if n.natAbs ≤ N then u.val n else 0) ∧
      (∀ N, FiniteDimensional ℝ (LinearMap.range (P N).toLinearMap)) ∧
      (∀ N, IsCompactOperator (P N)) ∧
      (∀ N u, ‖J u - P N u‖ ≤
        (1 + 4 * π ^ 2 * (N : ℝ) ^ 2) ^ (-ε / 2) * ‖u‖) ∧
      Tendsto P atTop (𝓝 J)

def HilbertStructure : Prop :=
  ∀ s : ℝ, Nonempty (InnerProductSpace ℂ (Hs s)) ∧ CompleteSpace (Hs s) ∧
    Nonempty (InnerProductSpace ℝ (RealHs s)) ∧ CompleteSpace (RealHs s)

def HigherDerivatives : Prop :=
  ∀ (k : ℕ) (s : ℝ), ∃ D : Hs s →L[ℂ] Hs (s - (k : ℝ)),
    (∀ u n, coefficient (D u) n = (2 * π * Complex.I * n : ℂ) ^ k * coefficient u n) ∧
    (∀ u, ‖D u‖ ≤ ‖u‖)

def RealHigherDerivatives : Prop :=
  ∀ (k : ℕ) (s : ℝ), ∃ D : RealHs s →L[ℝ] RealHs (s - (k : ℝ)),
    (∀ u n, coefficient (D u).val n = (2 * π * Complex.I * n : ℂ) ^ k * coefficient u.val n) ∧
    (∀ u, ‖D u‖ ≤ ‖u‖)

/-- The coefficient multiplier agrees with ordinary differentiation on every
finite Fourier synthesis, not merely on unnamed sequence spaces. -/
def PolynomialDifferentiation : Prop :=
  ∀ s : ℝ, ∃ D : Hs s →L[ℂ] Hs (s - 1),
    (∀ u n, D u n = (2 * π * Complex.I * n : ℂ) * u n) ∧
    ∀ (u : Hs s) (F : Finset ℤ) (x : ℝ),
      HasDerivAt (fourierPolynomial u F) (fourierPolynomial (D u) F x) x

/-- The quotient, smooth tests, Fourier integrals, and ordinary test derivatives
used below are those of the actual period-one circle. The smooth topology is
transported by the displayed continuous linear equivalence. -/
def CircleIdentification : Prop :=
  MeasurePreserving torusCircle (torusHaar 1) AddCircle.haarAddCircle ∧
  (∀ (φ : Smooth ℂ 1) (q : CircleBridge.Circle),
    (testCircleContinuousEquiv φ).val q = φ.val (torusCircle.symm q)) ∧
  (∀ (φ : Smooth ℂ 1) (n : Lattice 1),
    testFourierCoeff φ n = fourierCoeff (testCircle φ).val (n 0)) ∧
  (∀ (k : ℕ) (φ : CircleTest) (x : ℝ),
    (circleHigherTestDerivative k φ).val (x : CircleBridge.Circle) =
      iteratedDeriv k (fun y : ℝ => φ.val (y : CircleBridge.Circle)) x) ∧
  (∀ (φ : CircleTest) (L : ℕ) (C : ℝ), 0 ≤ C →
    (smoothPartialSeminorm ℂ 1 L (testTorus φ) ≤ C ↔
      ∀ k ≤ L, ∀ x ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDeriv k (fun y : ℝ => φ.val (y : CircleBridge.Circle)) x‖ ≤ C))

/-- A single compatible realization at every real order, including singular
negative-order elements. Its values are continuous scalar-linear functionals
on the original smooth circle tests. Every distribution with the weighted
summability occurs, and every coefficient is recovered. The last clauses identify
all derivatives, order-zero regular functions, and the Hilbert dual pairing. -/
def DistributionRealization : Prop :=
  ∃ R : (s : ℝ) → Hs s →ₗ[ℂ] CircleDistribution,
    (∀ (s : ℝ) (u : Hs s) (n : ℤ), R s u (circleCharacter (-n)) = u n) ∧
    (∀ s, Function.Injective (R s)) ∧
    (∀ (s : ℝ) (U : CircleDistribution), (∃ u : Hs s, R s u = U) ↔
      Summable (fun n : ℤ => frequencyWeight n ^ s * ‖U (circleCharacter (-n))‖ ^ 2)) ∧
    (∀ (s : ℝ) (u : Hs s) (φ : CircleTest),
      Summable (fun n : ℤ => ‖u n * fourierCoeff φ.val (-n)‖) ∧
      HasSum (fun n : ℤ => u n * fourierCoeff φ.val (-n)) (R s u φ)) ∧
    (∀ (s t : ℝ) (u : Hs s) (v : Hs t), (∀ n, u n = v n) → R s u = R t v) ∧
    (∀ (s : ℝ) (u : Hs s), (∀ n : ℤ, u (-n) = conj (u n)) ↔
      ∀ φ : CircleTest, R s u (circleConjugateTest φ) = conj (R s u φ)) ∧
    (∀ (s : ℝ) (U : CircleDistribution), (∃ u : RealHs s, R s u.val = U) ↔
      Summable (fun n : ℤ => frequencyWeight n ^ s * ‖U (circleCharacter (-n))‖ ^ 2) ∧
      (∀ φ : CircleTest, U (circleConjugateTest φ) = conj (U φ))) ∧
    (∀ (k : ℕ) (s : ℝ), ∃ D : Hs s →L[ℂ] Hs (s - (k : ℝ)),
      (∀ u n, D u n = (2 * π * Complex.I * n : ℂ) ^ k * u n) ∧
      (∀ u, ‖D u‖ ≤ ‖u‖) ∧
      ∀ (u : Hs s) (φ : CircleTest),
        R (s - (k : ℝ)) (D u) φ = (-1 : ℂ) ^ k * R s u (circleHigherTestDerivative k φ)) ∧
    (∀ (k : ℕ) (s : ℝ), ∃ D : RealHs s →L[ℝ] RealHs (s - (k : ℝ)),
      (∀ u n, (D u).val n = (2 * π * Complex.I * n : ℂ) ^ k * u.val n) ∧
      (∀ u, ‖D u‖ ≤ ‖u‖) ∧
      ∀ (u : RealHs s) (φ : CircleTest),
        R (s - (k : ℝ)) (D u).val φ =
          (-1 : ℂ) ^ k * R s u.val (circleHigherTestDerivative k φ)) ∧
    (∃ U : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)) ≃ₗᵢ[ℂ] Hs 0,
      (∀ f n, U f n = fourierCoeff f n) ∧
      ∀ f (φ : CircleTest), R 0 (U f) φ =
        ∫ x : CircleBridge.Circle, f x * φ.val x ∂AddCircle.haarAddCircle) ∧
    (∀ s : ℝ, ∃ V : Hs (-s) ≃ₗᵢ[ℂ] (Hs s →L[ℂ] ℂ),
      (∀ v u, Summable (fun n : ℤ => ‖u n * v (-n)‖) ∧
        V v u = ∑' n : ℤ, u n * v (-n)) ∧
      ∀ φ : CircleTest, ∃ v : Hs (-s),
        (∀ n, v n = fourierCoeff φ.val n) ∧ ∀ u : Hs s, V v u = R s u φ) ∧
    (∀ s : ℝ, ∃ V : RealHs (-s) ≃ₗᵢ[ℝ] (RealHs s →L[ℝ] ℝ),
      (∀ v u, Summable (fun n : ℤ => ‖u.val n * v.val (-n)‖) ∧
        V v u = (∑' n : ℤ, u.val n * v.val (-n)).re) ∧
      ∀ φ : CircleTest, (∀ x, conj (φ.val x) = φ.val x) → ∃ v : RealHs (-s),
        (∀ n, v.val n = fourierCoeff φ.val n) ∧
          ∀ u : RealHs s, V v u = (R s u.val φ).re)

end Spec
end ExpandedFA.Sobolev.PeriodicHilbertScale
