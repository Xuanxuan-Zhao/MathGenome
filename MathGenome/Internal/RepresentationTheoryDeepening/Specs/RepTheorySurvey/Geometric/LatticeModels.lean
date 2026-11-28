import Mathlib.Analysis.Complex.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Topology.Algebra.MvPolynomial
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.GrassmannianCharts

namespace RepTheorySurvey.Geometric
namespace LatticeModelSpecs

noncomputable section

open scoped MatrixGroups

abbrev O := PowerSeries ℂ
abbrev K := LaurentSeries ℂ
abbrev t : O := PowerSeries.X

instance coefficientTower : IsScalarTower ℂ O K where
  smul_assoc c f x := by
    change (HahnSeries.ofPowerSeries ℤ ℂ (c • f)) * x =
      c • (HahnSeries.ofPowerSeries ℤ ℂ f * x)
    have hc (y : K) : c • y = HahnSeries.single (0 : ℤ) c * y :=
      HahnSeries.single_zero_mul_eq_smul.symm
    simp only [PowerSeries.coe_smul, hc, mul_assoc]

def inclusion : O →+* K := algebraMap O K

def monomial (a : ℤ) : K := HahnSeries.single a 1

theorem monomial_eq_zpow (a : ℤ) : monomial a = inclusion t ^ a := by
  simpa [monomial, inclusion, LaurentSeries.coe_algebraMap, PowerSeries.coe_X] using
    (RatFunc.single_zpow (F := ℂ) a)

theorem monomial_ne_zero (a : ℤ) : monomial a ≠ 0 :=
  HahnSeries.single_ne_zero one_ne_zero

abbrev Coordinates (r : ℕ) := Fin r → K

/-- An O-lattice in K^r is a free O-submodule on r generators with full K-span. -/
abbrev Lattice (r : ℕ) :=
  { L : Submodule O (Coordinates r) //
    Nonempty (Module.Basis (Fin r) O L) ∧ Submodule.span K (L : Set (Coordinates r)) = ⊤ }

abbrev GL2Lattice := Lattice 2
abbrev TorusLattice (r : ℕ) := Fin r → Lattice 1
abbrev Coweight (r : ℕ) := Fin r → ℤ

def coordinateInclusion (r : ℕ) : (Fin r → O) →ₗ[O] Coordinates r :=
  LinearMap.pi fun i ↦ (Algebra.linearMap O K).comp (LinearMap.proj i)

theorem coordinateInclusion_injective (r : ℕ) :
    Function.Injective (coordinateInclusion r) := by
  intro x y h
  funext i
  exact HahnSeries.ofPowerSeries_injective (congrFun h i)

def standardLattice (r : ℕ) : Lattice r := by
  let f := coordinateInclusion r
  refine ⟨f.range, ⟨⟨(Pi.basisFun O (Fin r)).map
    (LinearEquiv.ofInjective f (coordinateInclusion_injective r))⟩, ?_⟩⟩
  rw [eq_top_iff, ← (Pi.basisFun K (Fin r)).span_eq]
  refine Submodule.span_le.mpr ?_
  rintro v ⟨i, rfl⟩
  apply Submodule.subset_span
  exact ⟨Pi.basisFun O (Fin r) i, by
    ext j
    classical
    simp [f, coordinateInclusion, Pi.basisFun_apply, Pi.single_apply]⟩

def loopLinearEquiv (r : ℕ) :
    GL (Fin r) K ≃* (Coordinates r ≃ₗ[K] Coordinates r) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv K _)

def mapLattice {r : ℕ} (e : Coordinates r ≃ₗ[K] Coordinates r) (L : Lattice r) :
    Lattice r := by
  let f := (e.restrictScalars O).toLinearMap
  refine ⟨L.val.map f, ⟨L.property.1.map (fun b ↦ b.map
    (L.val.equivMapOfInjective f e.injective)), ?_⟩⟩
  change Submodule.span K (e.toLinearMap '' (L.val : Set (Coordinates r))) = ⊤
  rw [← Submodule.map_span e.toLinearMap, L.property.2, Submodule.map_top,
    LinearMap.range_eq_top.mpr e.surjective]

instance latticeAction (r : ℕ) : MulAction (GL (Fin r) K) (Lattice r) where
  smul g L := mapLattice (loopLinearEquiv r g) L
  one_smul L := Subtype.ext (show (mapLattice (loopLinearEquiv r 1) L).val = L.val by
    rw [map_one]
    exact Submodule.map_id _)
  mul_smul g h L := Subtype.ext (show
    (mapLattice (loopLinearEquiv r (g * h)) L).val =
      (mapLattice (loopLinearEquiv r g) (mapLattice (loopLinearEquiv r h) L)).val by
    rw [map_mul]
    exact Submodule.map_comp ((loopLinearEquiv r h).restrictScalars O).toLinearMap
      ((loopLinearEquiv r g).restrictScalars O).toLinearMap L.val)

def diagonalEquiv {r : ℕ} (a : Coweight r) :
    Coordinates r ≃ₗ[K] Coordinates r where
  toFun x i := monomial (a i) * x i
  invFun x i := (monomial (a i))⁻¹ * x i
  left_inv x := by
    funext i
    simp [monomial_ne_zero]
  right_inv x := by
    funext i
    simp [monomial_ne_zero]
  map_add' x y := by funext i; exact mul_add ..
  map_smul' c x := by funext i; change _ * (c * _) = c * (_ * _); exact mul_left_comm ..

def diagonalLattice {r : ℕ} (a : Coweight r) : Lattice r :=
  mapLattice (diagonalEquiv a) (standardLattice r)

def torusMonomial (r : ℕ) (a : Coweight r) : Fin r → Kˣ :=
  fun i ↦ Units.mk0 (monomial (a i)) (monomial_ne_zero _)

def torusLatticeAt (r : ℕ) (a : Coweight r) : TorusLattice r :=
  fun i ↦ diagonalLattice (fun _ ↦ a i)

def positiveGLMap (r : ℕ) : GL (Fin r) O →* GL (Fin r) K :=
  Matrix.GeneralLinearGroup.map inclusion

def positiveTorusMap (r : ℕ) : (Fin r → Oˣ) →* (Fin r → Kˣ) where
  toFun u i := Units.map inclusion.toMonoidHom (u i)
  map_one' := by ext i; simp
  map_mul' u v := by ext i; simp

abbrev PositiveGL (r : ℕ) := (positiveGLMap r).range
abbrev PositiveTorus (r : ℕ) := (positiveTorusMap r).range

section Quotients

variable {Γ : Type*} [Group Γ] (H : Subgroup Γ)

abbrev Grassmannian := Γ ⧸ H

def coset (g : Γ) : Grassmannian H := Quotient.mk (QuotientGroup.leftRel H) g

def CosetRelation : Prop :=
  ∀ g g' : Γ, coset H g = coset H g' ↔
    g⁻¹ * g' ∈ H ∧ ∃ h : H, g' = g * (h : Γ)

variable {X : Type*} [MulAction Γ X]

/-- An H-stable space of second modifications, inside the space acted on by Γ. -/
def StableStage (S : Set X) : Prop := ∀ (h : H) ⦃x⦄, x ∈ S → (h : Γ) • x ∈ S

abbrev Representatives (A : Set (Grassmannian H)) (S : Set X) :=
  { p : Γ × X // coset H p.1 ∈ A ∧ p.2 ∈ S }

def twistRel (A : Set (Grassmannian H)) (S : Set X) :
    Setoid (Representatives H A S) where
  r p q := ∃ h : H, q.val.1 = p.val.1 * (h : Γ) ∧ q.val.2 = ((h⁻¹ : H) : Γ) • p.val.2
  iseqv := by
    constructor
    · intro p
      exact ⟨1, by simp, by simp⟩
    · rintro p q ⟨h, hg, hx⟩
      exact ⟨h⁻¹, by simp [hg, mul_assoc], by simp [hx, smul_smul]⟩
    · rintro p q z ⟨h, hg, hx⟩ ⟨k, kg, kx⟩
      exact ⟨h * k, by simp [kg, hg, mul_assoc], by simp [kx, hx, smul_smul]⟩

abbrev TwistedProduct (A : Set (Grassmannian H)) (S : Set X) (_ : StableStage H S) :=
  Quotient (twistRel H A S)

def firstProjection {A : Set (Grassmannian H)} {S : Set X} (hS : StableStage H S) :
    TwistedProduct H A S hS → A :=
  Quotient.lift (fun p ↦ ⟨coset H p.val.1, p.property.1⟩) (by
    rintro p q ⟨h, hg, _⟩
    apply Subtype.ext
    apply Quotient.sound
    exact QuotientGroup.leftRel_apply.mpr (by simp [hg, ← mul_assoc]))

def terminalMap {A : Set (Grassmannian H)} {S : Set X} (hS : StableStage H S) :
    TwistedProduct H A S hS → X :=
  Quotient.lift (fun p ↦ p.val.1 • p.val.2) (by
    rintro p q ⟨h, hg, hx⟩
    simp [hg, hx, smul_smul])

end Quotients

def scalarLattice (r : ℕ) (a : ℤ) : Lattice r :=
  diagonalLattice (fun _ ↦ a)

abbrev BoundedLattice (r N : ℕ) :=
  { L : Lattice r // (scalarLattice r (N : ℤ)).val ≤ L.val ∧
    L.val ≤ (scalarLattice r (-(N : ℤ))).val }

abbrev BoundedTorus (r N : ℕ) := Fin r → BoundedLattice 1 N

/-- The ring and coefficient vector space of n-jets. The zero truncation is also
used for the zero-dimensional window at bound zero. -/
def jetIdeal (n : ℕ) : Ideal O := Ideal.span {t ^ n}

abbrev JetRing (n : ℕ) := O ⧸ jetIdeal n

def jetReduction (n : ℕ) : O →ₐ[ℂ] JetRing n := Ideal.Quotient.mkₐ ℂ _

def truncCoefficients (n : ℕ) : O →ₗ[ℂ] (Fin n → ℂ) :=
  LinearMap.pi fun i ↦ PowerSeries.coeff i.val

theorem truncCoefficients_surjective (n : ℕ) : Function.Surjective (truncCoefficients n) := by
  intro x
  refine ⟨PowerSeries.mk fun i ↦ if h : i < n then x ⟨i, h⟩ else 0, ?_⟩
  funext i
  simp [truncCoefficients, i.isLt]

theorem truncCoefficients_ker (n : ℕ) :
    (truncCoefficients n).ker = (jetIdeal n).restrictScalars ℂ := by
  ext f
  rw [LinearMap.mem_ker, Submodule.restrictScalars_mem, jetIdeal, Ideal.mem_span_singleton]
  constructor
  · intro h
    refine ⟨PowerSeries.mk fun i ↦ PowerSeries.coeff (i + n) f, ?_⟩
    apply PowerSeries.ext
    intro i
    rw [PowerSeries.coeff_X_pow_mul']
    split
    · rw [PowerSeries.coeff_mk, Nat.sub_add_cancel ‹n ≤ i›]
    · exact congrFun h ⟨i, Nat.lt_of_not_ge ‹¬ n ≤ i›⟩
  · rintro ⟨q, rfl⟩
    funext i
    change PowerSeries.coeff i.val (t ^ n * q) = 0
    simp [PowerSeries.coeff_X_pow_mul', Nat.not_le_of_lt i.isLt]

def jetCoefficients (n : ℕ) : JetRing n ≃ₗ[ℂ] (Fin n → ℂ) :=
  ((jetIdeal n).restrictScalars ℂ).quotEquivOfEq _ (truncCoefficients_ker n).symm ≪≫ₗ
    (truncCoefficients n).quotKerEquivOfSurjective (truncCoefficients_surjective n)

@[simp] theorem jetCoefficients_reduce (n : ℕ) (f : O) (i : Fin n) :
    jetCoefficients n (jetReduction n f) i = PowerSeries.coeff i.val f := rfl

/-- The analytic topology on the ring of jets, in its n complex coordinates. -/
instance jetTopology (n : ℕ) : TopologicalSpace (JetRing n) :=
  TopologicalSpace.induced (jetCoefficients n) inferInstance

abbrev GLJets (r n : ℕ) (_ : 1 ≤ n) := GL (Fin r) (JetRing n)
abbrev TorusJets (r n : ℕ) (_ : 1 ≤ n) := Fin r → (JetRing n)ˣ

def reduceGL (r n : ℕ) (hn : 1 ≤ n) : GL (Fin r) O →* GLJets r n hn :=
  Matrix.GeneralLinearGroup.map (jetReduction n).toRingHom

def reduceTorus (r n : ℕ) (hn : 1 ≤ n) : (Fin r → Oˣ) →* TorusJets r n hn where
  toFun g i := Units.map (jetReduction n).toMonoidHom (g i)
  map_one' := by ext i; simp
  map_mul' g h := by ext i; simp

instance glJetTopology (r n : ℕ) (hn : 1 ≤ n) : TopologicalSpace (GLJets r n hn) :=
  TopologicalSpace.induced (fun g ↦ (g.val : Matrix (Fin r) (Fin r) (JetRing n))) inferInstance

instance torusJetTopology (r n : ℕ) (hn : 1 ≤ n) : TopologicalSpace (TorusJets r n hn) :=
  TopologicalSpace.induced (fun g i ↦ ((g i).val : JetRing n)) inferInstance

theorem monomial_add (a b : ℤ) : monomial (a+b) = monomial a * monomial b := by
  simp only [monomial_eq_zpow]
  exact zpow_add₀ (by rw [inclusion, LaurentSeries.coe_algebraMap, PowerSeries.coe_X]; exact
    HahnSeries.single_ne_zero one_ne_zero) _ _

theorem monomial_nat (m : ℕ) : monomial m = inclusion (t ^ m) := by
  rw [monomial_eq_zpow, zpow_natCast, map_pow]

def shiftedInclusion (r : ℕ) (a : ℤ) : (Fin r → O) →ₗ[O] Coordinates r :=
  ((diagonalEquiv (r := r) fun _ ↦ a).restrictScalars O).toLinearMap.comp
    (coordinateInclusion r)

theorem shiftedInclusion_injective (r : ℕ) (a : ℤ) :
    Function.Injective (shiftedInclusion r a) :=
  (diagonalEquiv (r := r) fun _ ↦ a).injective.comp (coordinateInclusion_injective r)

theorem scalarLattice_val (r : ℕ) (a : ℤ) :
    (scalarLattice r a).val = (shiftedInclusion r a).range :=
  (LinearMap.range_comp (coordinateInclusion r)
    ((diagonalEquiv (r := r) fun _ ↦ a).restrictScalars O).toLinearMap).symm

def shiftedCoordinates (r : ℕ) (a : ℤ) :
    (Fin r → O) ≃ₗ[O] (scalarLattice r a).val :=
  LinearEquiv.ofInjective (shiftedInclusion r a) (shiftedInclusion_injective r a) ≪≫ₗ
    LinearEquiv.ofEq _ _ (scalarLattice_val r a).symm

@[simp] theorem shiftedCoordinates_coe (r : ℕ) (a : ℤ) (x : Fin r → O) :
    ((shiftedCoordinates r a x : (scalarLattice r a).val) : Coordinates r) =
      shiftedInclusion r a x := rfl

theorem shiftedInclusion_add_nat (r : ℕ) (a : ℤ) (m : ℕ) (x : Fin r → O) :
    shiftedInclusion r (a + m) x = shiftedInclusion r a (t ^ m • x) := by
  funext i
  change monomial (a + m) * inclusion (x i) = monomial a * inclusion (t ^ m * x i)
  rw [monomial_add, monomial_nat, map_mul, mul_assoc]

theorem scalarLattice_add_nat_le (r : ℕ) (a : ℤ) (m : ℕ) :
    (scalarLattice r (a + m)).val ≤ (scalarLattice r a).val := by
  rw [scalarLattice_val r (a + m), scalarLattice_val r a]
  rintro _ ⟨x, rfl⟩
  exact ⟨t ^ m • x, (shiftedInclusion_add_nat r a m x).symm⟩

/-- In the interval from t^(a+m) L₀ to t^a L₀ the lower lattice is regarded
as a submodule of the upper lattice. -/
def windowLower (r : ℕ) (a : ℤ) (m : ℕ) : Submodule O (scalarLattice r a).val :=
  (scalarLattice r (a + m)).val.comap (scalarLattice r a).val.subtype

abbrev Window (r : ℕ) (a : ℤ) (m : ℕ) :=
  @HasQuotient.Quotient _ _ (@Submodule.hasQuotient O ((scalarLattice r a).val : Type)
    inferInstance inferInstance inferInstance) (windowLower r a m)

def windowOperator (r : ℕ) (a : ℤ) (m : ℕ) : Window r a m →ₗ[ℂ] Window r a m :=
  (t • (LinearMap.id : Window r a m →ₗ[O] Window r a m)).restrictScalars ℂ

def windowReduction (r : ℕ) (a : ℤ) (m : ℕ) :
    (scalarLattice r a).val →ₗ[O] (Fin r → JetRing m) :=
  (LinearMap.pi fun i : Fin r ↦
    (Ideal.Quotient.mkₐ O (jetIdeal m)).toLinearMap.comp (LinearMap.proj i)).comp
      (shiftedCoordinates r a).symm.toLinearMap

theorem windowReduction_surjective (r : ℕ) (a : ℤ) (m : ℕ) :
    Function.Surjective (windowReduction r a m) := by
  classical
  intro y
  choose x hx using fun i ↦ Ideal.Quotient.mk_surjective (y i)
  refine ⟨shiftedCoordinates r a x, ?_⟩
  funext i
  change Ideal.Quotient.mk (jetIdeal m) ((shiftedCoordinates r a).symm
    (shiftedCoordinates r a x) i) = y i
  rw [LinearEquiv.symm_apply_apply, hx]

theorem windowReduction_ker (r : ℕ) (a : ℤ) (m : ℕ) :
    (windowReduction r a m).ker = windowLower r a m := by
  classical
  ext v
  obtain ⟨x, rfl⟩ := (shiftedCoordinates r a).surjective v
  have hreduce : windowReduction r a m (shiftedCoordinates r a x) =
      fun i ↦ Ideal.Quotient.mk (jetIdeal m) (x i) := by
    funext i
    change Ideal.Quotient.mk (jetIdeal m) ((shiftedCoordinates r a).symm
      (shiftedCoordinates r a x) i) = _
    rw [LinearEquiv.symm_apply_apply]
  rw [LinearMap.mem_ker, hreduce]
  rw [windowLower, Submodule.mem_comap]
  change _ ↔ ((shiftedCoordinates r a x : (scalarLattice r a).val) : Coordinates r) ∈ _
  rw [shiftedCoordinates_coe, scalarLattice_val, LinearMap.mem_range]
  constructor
  · intro h
    have hdvd (i : Fin r) : t ^ m ∣ x i :=
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp (congrFun h i))
    choose y hy using hdvd
    refine ⟨y, ?_⟩
    rw [shiftedInclusion_add_nat]
    exact congrArg (shiftedInclusion r a) (funext fun i ↦ (hy i).symm)
  · rintro ⟨y, hy⟩
    rw [shiftedInclusion_add_nat] at hy
    have hx := shiftedInclusion_injective r a hy
    funext i
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have hi := congrFun hx i
    rw [jetIdeal, Ideal.mem_span_singleton, ← hi]
    exact dvd_mul_right _ _

private def quotientEquivOfKernel {R M V : Type} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup V] [Module R V] (P : Submodule R M) (f : M →ₗ[R] V)
    (h : f.ker = P) (hf : Function.Surjective f) : (M ⧸ P) ≃ₗ[R] V :=
  P.quotEquivOfEq _ h.symm ≪≫ₗ f.quotKerEquivOfSurjective hf

def windowJets (r : ℕ) (a : ℤ) (m : ℕ) : Window r a m ≃ₗ[O] (Fin r → JetRing m) :=
  @quotientEquivOfKernel O ((scalarLattice r a).val : Type) (Fin r → JetRing m)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (windowLower r a m) (windowReduction r a m) (windowReduction_ker r a m)
    (windowReduction_surjective r a m)

def windowCoordinates (r : ℕ) (a : ℤ) (m : ℕ) : Window r a m ≃ₗ[ℂ] (Fin r × Fin m → ℂ) :=
  (windowJets r a m).restrictScalars ℂ ≪≫ₗ
    LinearEquiv.piCongrRight (fun _ ↦ jetCoefficients m) ≪≫ₗ
    (LinearEquiv.piCurry ℂ (fun _ _ ↦ ℂ)).symm ≪≫ₗ
    LinearEquiv.piCongrLeft' ℂ (fun _ ↦ ℂ) (Equiv.sigmaEquivProd _ _)

def windowBasis (r : ℕ) (a : ℤ) (m : ℕ) : Module.Basis (Fin r × Fin m) ℂ (Window r a m) :=
  Module.Basis.ofEquivFun (windowCoordinates r a m)

instance windowFinite (r : ℕ) (a : ℤ) (m : ℕ) : FiniteDimensional ℂ (Window r a m) :=
  Module.Finite.of_basis (windowBasis r a m)

abbrev BoundedWindow (r N : ℕ) := Window r (-(N : ℤ)) (2*N)

theorem boundedExponent (N : ℕ) : -(N : ℤ) + ((2*N : ℕ) : ℤ) = N := by
  push_cast
  omega

private def quotientSubspace {R M : Type} [Ring R] [Algebra ℂ R]
    [AddCommGroup M] [Module R M] [Module ℂ M] [IsScalarTower ℂ R M]
    (P Q : Submodule R M) : Submodule ℂ (M ⧸ Q) :=
  (P.map Q.mkQ).restrictScalars ℂ

def latticeSubspace {r : ℕ} (a : ℤ) (m : ℕ) (L : Lattice r) :
    Submodule ℂ (Window r a m) :=
  @quotientSubspace O ((scalarLattice r a).val : Type)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (L.val.comap (scalarLattice r a).val.subtype) (windowLower r a m)

def boundedSubspace {r N : ℕ} (L : BoundedLattice r N) :
    Submodule ℂ (BoundedWindow r N) :=
  latticeSubspace (-(N : ℤ)) (2*N) L.val

section LoopActions

open scoped Matrix

def diagonalUnits (r : ℕ) : (Fin r → Kˣ) →* GL (Fin r) K :=
  (Units.map (Matrix.diagonalRingHom (Fin r) K).toMonoidHom).comp
    (MulEquiv.piUnits (M := fun _ : Fin r ↦ K)).symm.toMonoidHom

/-- The actual invertible diagonal matrix with entries t^(a_i). -/
def diagonalLoop (r : ℕ) (a : Coweight r) : GL (Fin r) K :=
  diagonalUnits r (torusMonomial r a)

@[simp] theorem loopLinearEquiv_apply {r : ℕ} (g : GL (Fin r) K) (x : Coordinates r) :
    loopLinearEquiv r g x = (g.val : Matrix (Fin r) (Fin r) K) *ᵥ x :=
  Matrix.GeneralLinearGroup.toLin_apply g x

theorem diagonalLoop_linear {r : ℕ} (a : Coweight r) :
    loopLinearEquiv r (diagonalLoop r a) = diagonalEquiv a := by
  apply LinearEquiv.ext
  intro v
  rw [loopLinearEquiv_apply]
  funext i
  change (Matrix.diagonal (fun j : Fin r ↦ monomial (a j)) *ᵥ v) i =
    monomial (a i) * v i
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]

@[simp] theorem diagonalLoop_smul_standard {r : ℕ} (a : Coweight r) :
    diagonalLoop r a • standardLattice r = diagonalLattice a := by
  change mapLattice (loopLinearEquiv r (diagonalLoop r a)) (standardLattice r) = _
  rw [diagonalLoop_linear]
  rfl

@[instance_reducible] def rankOneAction : MulAction Kˣ (Lattice 1) :=
  MulAction.compHom (Lattice 1) ((diagonalUnits 1).comp
    { toFun := fun u _ ↦ u
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl })

instance torusAction (r : ℕ) : MulAction (Fin r → Kˣ) (TorusLattice r) :=
  letI := rankOneAction
  inferInstance

theorem torusMonomial_smul_standard (r : ℕ) (a : Coweight r) :
    torusMonomial r a • (fun _ : Fin r ↦ standardLattice 1) = torusLatticeAt r a := by
  funext i
  change diagonalLoop 1 (fun _ ↦ a i) • standardLattice 1 = _
  exact diagonalLoop_smul_standard _

def CosetAction : Prop :=
  ∀ {Γ : Type} [Group Γ] (H : Subgroup Γ) (g k : Γ),
    g • coset H k = coset H (g * k)

theorem positiveGLMap_linear {r : ℕ} (g : GL (Fin r) O) (x : Fin r → O) :
    loopLinearEquiv r (positiveGLMap r g) (coordinateInclusion r x) =
      coordinateInclusion r ((g.val : Matrix (Fin r) (Fin r) O) *ᵥ x) := by
  rw [loopLinearEquiv_apply]
  funext i
  change ∑ j, (positiveGLMap r g).val i j * inclusion (x j) =
    inclusion (∑ j, g.val i j * x j)
  simp [positiveGLMap, Matrix.GeneralLinearGroup.map_apply, map_sum, map_mul]

theorem positiveGL_preserves_scalar {r : ℕ} (g : GL (Fin r) O) (a : ℤ) :
    positiveGLMap r g • scalarLattice r a = scalarLattice r a := by
  have h (k : GL (Fin r) O) :
      (positiveGLMap r k • scalarLattice r a).val ≤ (scalarLattice r a).val := by
    rintro _ ⟨v, hv, rfl⟩
    rw [scalarLattice_val] at hv ⊢
    obtain ⟨x, rfl⟩ := hv
    let e := loopLinearEquiv r (positiveGLMap r k)
    change e (shiftedInclusion r a x) ∈ (shiftedInclusion r a).range
    have hs (y : Fin r → O) : shiftedInclusion r a y = monomial a • coordinateInclusion r y :=
      rfl
    refine ⟨k.val *ᵥ x, ?_⟩
    rw [hs, hs, map_smul, positiveGLMap_linear]
  apply Subtype.ext
  refine le_antisymm (h g) ?_
  intro x hx
  let e := loopLinearEquiv r (positiveGLMap r g)
  have hpre : e.symm x ∈ (scalarLattice r a).val := by
    apply h g⁻¹
    have he : loopLinearEquiv r (positiveGLMap r g⁻¹) = e.symm := by
      rw [map_inv, map_inv]
      rfl
    exact ⟨x, hx, congrArg (fun f : Coordinates r ≃ₗ[K] Coordinates r ↦ f x) he⟩
  exact ⟨e.symm x, hpre, e.apply_symm_apply x⟩

theorem diagonalLattice_le {r : ℕ} {a b : Coweight r} (h : ∀ i, b i ≤ a i) :
    (diagonalLattice a).val ≤ (diagonalLattice b).val := by
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  let n (i : Fin r) := (a i - b i).toNat
  let y (i : Fin r) := t ^ n i * x i
  refine ⟨coordinateInclusion r y, ⟨y, rfl⟩, ?_⟩
  funext i
  change monomial (b i) * inclusion (t ^ n i * x i) = monomial (a i) * inclusion (x i)
  have hba : b i + (n i : ℤ) = a i := by
    have := h i
    dsimp [n]
    omega
  rw [map_mul, ← monomial_nat, ← mul_assoc, ← monomial_add, hba]

end LoopActions

abbrev DominantPair := {ab : ℤ × ℤ // ab.2 ≤ ab.1}

def pairCoweight (ab : DominantPair) : Coweight 2 :=
  fun i ↦ if i.val = 0 then ab.val.1 else ab.val.2

def gl2Orbit (ab : DominantPair) : Set GL2Lattice :=
  MulAction.orbit (PositiveGL 2) (diagonalLattice (pairCoweight ab))

def OrbitBound (ab : DominantPair) (N : ℕ) : Prop :=
  ∀ i : Fin 2, -(N : ℤ) ≤ pairCoweight ab i ∧ pairCoweight ab i ≤ (N : ℤ)

theorem gl2Orbit_bounded (ab : DominantPair) {N : ℕ} (hN : OrbitBound ab N)
    {L : GL2Lattice} (hL : L ∈ gl2Orbit ab) :
    (scalarLattice 2 (N : ℤ)).val ≤ L.val ∧ L.val ≤ (scalarLattice 2 (-(N : ℤ))).val := by
  obtain ⟨⟨_, ⟨g, rfl⟩⟩, rfl⟩ := hL
  have hi : (scalarLattice 2 (N : ℤ)).val ≤ (diagonalLattice (pairCoweight ab)).val :=
    diagonalLattice_le (fun i ↦ (hN i).2)
  have hs : (diagonalLattice (pairCoweight ab)).val ≤ (scalarLattice 2 (-(N : ℤ))).val :=
    diagonalLattice_le (fun i ↦ (hN i).1)
  let f := ((loopLinearEquiv 2 (positiveGLMap 2 g)).restrictScalars O).toLinearMap
  have hfix (a : ℤ) : (scalarLattice 2 a).val.map f = (scalarLattice 2 a).val :=
    congrArg Subtype.val (positiveGL_preserves_scalar g a)
  change (scalarLattice 2 (N : ℤ)).val ≤ (diagonalLattice (pairCoweight ab)).val.map f ∧
    (diagonalLattice (pairCoweight ab)).val.map f ≤ (scalarLattice 2 (-(N : ℤ))).val
  exact ⟨by simpa only [hfix] using Submodule.map_mono (f := f) hi,
    by simpa only [hfix] using Submodule.map_mono (f := f) hs⟩

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct Matrix
open LinearAlgebraicGroups (Points SchemeOver TestAlgebra testSpec)
open LinearAlgebraicGroups.Specs.GrassmannianCharts
open LinearAlgebraicGroups.GrassmannianCharts (chartMatrixEquiv graphPlane graphPlane_isPivot)

section Equations

variable {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}
variable {R : Type} [CommRing R]

/-- The universal inclusion of the plane in pivot coordinates: (u, A u). -/
def graphMatrix (I : Pivot ι d) (A : Matrix (Outside I) (Inside I) R) :
    Matrix ι (Inside I) R :=
  Matrix.of fun i j ↦ if hi : i ∈ I.val then (if i = j.val then 1 else 0) else A ⟨i, hi⟩ j

/-- The projected operator on the universal subspace: q_A D j_A. -/
def graphResidual (I : Pivot ι d) (D : Matrix ι ι R)
    (A : Matrix (Outside I) (Inside I) R) : Matrix (Outside I) (Inside I) R :=
  let B := D * graphMatrix I A
  B.submatrix Subtype.val id - A * B.submatrix Subtype.val id

omit [Fintype ι] in
theorem graphMatrix_inside (I : Pivot ι d) (A : Matrix (Outside I) (Inside I) R)
    (u : Inside I → R) (i : Inside I) : (graphMatrix I A *ᵥ u) i.val = u i := by
  classical
  simp [Matrix.mulVec, dotProduct, graphMatrix, i.property]

omit [Fintype ι] in
theorem graphMatrix_outside (I : Pivot ι d) (A : Matrix (Outside I) (Inside I) R)
    (u : Inside I → R) (j : Outside I) : (graphMatrix I A *ᵥ u) j.val = (A *ᵥ u) j := by
  simp [Matrix.mulVec, dotProduct, graphMatrix, j.property]

omit [Fintype ι] in
theorem graphColumns_eq_mulVec {k : Type} [Field k] (I : Pivot ι d) (S : TestAlgebra k)
    (A : Matrix (Outside I) (Inside I) S) (u : Inside I → S) :
    graphColumns I S A u = graphMatrix I A *ᵥ u := by
  funext i
  by_cases hi : i ∈ I.val
  · rw [show (graphMatrix I A *ᵥ u) i = _ from graphMatrix_inside I A u ⟨i, hi⟩]
    simp [graphColumns, hi]
  · rw [show (graphMatrix I A *ᵥ u) i = _ from graphMatrix_outside I A u ⟨i, hi⟩]
    simp [graphColumns, hi, Matrix.toLin'_apply]

theorem graphResidual_eq_zero (I : Pivot ι d) (D : Matrix ι ι R)
    (A : Matrix (Outside I) (Inside I) R) :
    graphResidual I D A = 0 ↔
      ∀ u : Inside I → R, ∃ v : Inside I → R,
        D *ᵥ (graphMatrix I A *ᵥ u) = graphMatrix I A *ᵥ v := by
  classical
  have hB (u : Inside I → R) (j : Outside I) :
      (graphResidual I D A *ᵥ u) j =
        (D *ᵥ (graphMatrix I A *ᵥ u)) j.val -
          (A *ᵥ (fun i : Inside I ↦ (D *ᵥ (graphMatrix I A *ᵥ u)) i.val)) j := by
    unfold graphResidual
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec u A,
      Matrix.mulVec_mulVec u D (graphMatrix I A)]
    rfl
  constructor
  · intro h u
    refine ⟨fun i ↦ (D *ᵥ (graphMatrix I A *ᵥ u)) i.val, ?_⟩
    funext i
    by_cases hi : i ∈ I.val
    · exact (graphMatrix_inside I A (fun j ↦ (D *ᵥ (graphMatrix I A *ᵥ u)) j.val) ⟨i, hi⟩).symm
    · rw [show (graphMatrix I A *ᵥ _) i = _ from graphMatrix_outside I A _ ⟨i, hi⟩]
      apply sub_eq_zero.mp
      rw [← hB u ⟨i, hi⟩, h, Matrix.zero_mulVec]
      rfl
  · intro h
    apply Matrix.ext_of_mulVec_single
    intro i
    obtain ⟨v, hv⟩ := h (Pi.single i 1)
    have hinside (j : Inside I) := congrFun hv j.val
    simp_rw [graphMatrix_inside] at hinside
    have houtside (j : Outside I) := congrFun hv j.val
    simp_rw [graphMatrix_outside] at houtside
    funext j
    rw [hB, show (fun i : Inside I ↦ _) = v from funext hinside, houtside,
      sub_self, Matrix.zero_mulVec]
    rfl

def graphPolynomial (I : Pivot ι d) (D : Matrix ι ι ℂ) :
    Matrix (Outside I) (Inside I) (chartAlgebra (k := ℂ) I) :=
  graphResidual I (D.map MvPolynomial.C)
    (Matrix.of fun j i ↦ MvPolynomial.X (j, i))

def stabilityIdeal (I : Pivot ι d) (D : Matrix ι ι ℂ) :
    Ideal (chartAlgebra (k := ℂ) I) :=
  Ideal.span (Set.range fun ji : Outside I × Inside I ↦ graphPolynomial I D ji.1 ji.2)

def reducedStabilityIdeal (I : Pivot ι d) (D : Matrix ι ι ℂ) :
    Ideal (chartAlgebra (k := ℂ) I) :=
  (stabilityIdeal I D).radical


omit [Fintype ι] in
theorem graphMatrix_map {S : Type} [CommRing S] (f : R →+* S)
    (I : Pivot ι d) (A : Matrix (Outside I) (Inside I) R) :
    (graphMatrix I A).map f = graphMatrix I (A.map f) := by
  ext i j
  by_cases hi : i ∈ I.val
  · by_cases hj : i = j.val <;> simp [graphMatrix, hi, hj]
  · simp [graphMatrix, hi]

theorem graphResidual_map {S : Type} [CommRing S] (f : R →+* S)
    (I : Pivot ι d) (D : Matrix ι ι R) (A : Matrix (Outside I) (Inside I) R) :
    (graphResidual I D A).map f = graphResidual I (D.map f) (A.map f) := by
  have hsub (M N : Matrix (Outside I) (Inside I) R) :
      (M - N).map f = M.map f - N.map f := by ext j i; exact map_sub f _ _
  simp only [graphResidual, hsub, Matrix.map_mul (f := f), ← Matrix.submatrix_map,
    graphMatrix_map f]

def chartVariables (I : Pivot ι d) (A : Matrix (Outside I) (Inside I) ℂ) :
    Outside I × Inside I → ℂ := fun ji ↦ A ji.1 ji.2

theorem graphPolynomial_eval (I : Pivot ι d) (D : Matrix ι ι ℂ)
    (A : Matrix (Outside I) (Inside I) ℂ) (j : Outside I) (i : Inside I) :
    MvPolynomial.aeval (chartVariables I A) (graphPolynomial I D j i) =
      graphResidual I D A j i := by
  let f := MvPolynomial.aeval (R := ℂ) (chartVariables I A)
  have hm : (graphPolynomial I D).map f = graphResidual I D A := by
    unfold graphPolynomial
    change (graphResidual I _ _).map f.toRingHom = _
    rw [graphResidual_map f.toRingHom]
    congr 1
    · ext i j
      simp [f]
    · ext i j
      simp [f, chartVariables]
  exact congrFun (congrFun hm j) i

theorem chartVariables_mem_zeroLocus (I : Pivot ι d) (D : Matrix ι ι ℂ)
    (A : Matrix (Outside I) (Inside I) ℂ) :
    chartVariables I A ∈ MvPolynomial.zeroLocus ℂ (stabilityIdeal I D) ↔
      graphResidual I D A = 0 := by
  change (∀ p ∈ stabilityIdeal I D, MvPolynomial.aeval (chartVariables I A) p = 0) ↔ _
  change stabilityIdeal I D ≤ RingHom.ker (MvPolynomial.aeval (chartVariables I A)).toRingHom ↔ _
  rw [stabilityIdeal, Ideal.span_le]
  constructor
  · intro h
    ext j i
    exact (graphPolynomial_eval I D A j i).symm.trans (h (Set.mem_range_self (j,i)))
  · rintro h _ ⟨⟨j,i⟩, rfl⟩
    change MvPolynomial.aeval (chartVariables I A) (graphPolynomial I D j i) = 0
    simp [graphPolynomial_eval, h]

end Equations

abbrev complexAlgebra : TestAlgebra ℂ := CommAlgCat.of ℂ ℂ

section Grassmannian

variable {V ι : Type} [AddCommGroup V] [Module ℂ V] [Fintype ι] [DecidableEq ι]

def grassmannianCharts (b : Module.Basis ι ℂ V) {d : ℕ} (hd : d ≤ Module.finrank ℂ V) :
    ChartSystem (k := ℂ) (V := V) b d :=
  (LinearAlgebraicGroups.GrassmannianCharts.construction ℂ V ι b d hd).choose

def grassmannianFamilies (b : Module.Basis ι ℂ V) {d : ℕ} (hd : d ≤ Module.finrank ℂ V) :
    SchemePoints (k := ℂ) (V := V) d (grassmannianCharts b hd).scheme (grassmannianCharts b hd).affinePoints :=
  (LinearAlgebraicGroups.GrassmannianCharts.construction ℂ V ι b d hd).choose_spec.choose

abbrev GrassmannianPoints (b : Module.Basis ι ℂ V) {d : ℕ}
    (hd : d ≤ Module.finrank ℂ V) := Points (grassmannianCharts b hd).scheme complexAlgebra

def grassmannianChartPoint (b : Module.Basis ι ℂ V) {d : ℕ}
    (hd : d ≤ Module.finrank ℂ V) (I : Pivot ι d) (A : Matrix (Outside I) (Inside I) ℂ) :
    GrassmannianPoints b hd :=
  (chartMatrixEquiv I complexAlgebra).symm A ≫ (grassmannianCharts b hd).chart I

/-- The analytic topology is final with respect to the ordinary complex graph charts. -/
instance grassmannianAnalyticTopology (b : Module.Basis ι ℂ V) {d : ℕ}
    (hd : d ≤ Module.finrank ℂ V) : TopologicalSpace (GrassmannianPoints b hd) :=
  ⨆ I : Pivot ι d, TopologicalSpace.coinduced (grassmannianChartPoint b hd I) inferInstance

def grassmannianPlane (b : Module.Basis ι ℂ V) {d : ℕ} (hd : d ≤ Module.finrank ℂ V)
    (p : GrassmannianPoints b hd) : Plane ℂ V d complexAlgebra :=
  (grassmannianCharts b hd).affinePoints.hom.app complexAlgebra p

def grassmannianSubspace (b : Module.Basis ι ℂ V) {d : ℕ} (hd : d ≤ Module.finrank ℂ V)
    (p : GrassmannianPoints b hd) : Submodule ℂ V :=
  (grassmannianPlane b hd p).toSubmodule.map (TensorProduct.lid ℂ V).toLinearMap

def operatorInCoordinates (b : Module.Basis ι ℂ V) (T : V →ₗ[ℂ] V) : Matrix ι ι ℂ :=
  LinearMap.toMatrix' (b.equivFun.toLinearMap.comp (T.comp b.equivFun.symm.toLinearMap))

def StablePlane (b : Module.Basis ι ℂ V) {d : ℕ} (hd : d ≤ Module.finrank ℂ V)
    (T : V →ₗ[ℂ] V) (p : GrassmannianPoints b hd) : Prop :=
  (grassmannianSubspace b hd p).map T ≤ grassmannianSubspace b hd p

def StablePoints (b : Module.Basis ι ℂ V) {d : ℕ} (hd : d ≤ Module.finrank ℂ V)
    (T : V →ₗ[ℂ] V) := {p : GrassmannianPoints b hd // StablePlane b hd T p}

omit [DecidableEq ι] in
theorem complexCoordinates (b : Module.Basis ι ℂ V) :
    coordinates b complexAlgebra = TensorProduct.lid ℂ V ≪≫ₗ b.equivFun := by
  apply LinearEquiv.toLinearMap_injective
  apply (b.baseChange ℂ).ext
  intro i
  change (coordinates b complexAlgebra) ((b.baseChange ℂ) i) =
    b.equivFun (TensorProduct.lid ℂ V ((b.baseChange ℂ) i))
  have hi : TensorProduct.lid ℂ V ((b.baseChange ℂ) i) = b i := by
    rw [Module.Basis.baseChange_apply, TensorProduct.lid_tmul, one_smul]
  rw [hi]
  unfold coordinates
  rw [LinearEquiv.trans_apply, Module.Basis.repr_self, Module.Basis.equivFun_apply,
    Module.Basis.repr_self]
  rfl

theorem grassmannianChartSubspace (b : Module.Basis ι ℂ V) {d : ℕ}
    (hd : d ≤ Module.finrank ℂ V) (I : Pivot ι d) (A : Matrix (Outside I) (Inside I) ℂ) :
    (grassmannianSubspace b hd (grassmannianChartPoint b hd I A)).map b.equivFun.toLinearMap =
      (Matrix.toLin' (graphMatrix I A)).range := by
  have h := (grassmannianCharts b hd).coordinates_eq I complexAlgebra
    ((chartMatrixEquiv I complexAlgebra).symm A)
  rw [← LinearAlgebraicGroups.GrassmannianCharts.chartMatrixEquiv_apply,
    Equiv.apply_symm_apply] at h
  change (grassmannianPlane b hd (grassmannianChartPoint b hd I A)).toSubmodule = _ at h
  rw [grassmannianSubspace, h, ← Submodule.map_comp, ← LinearEquiv.coe_trans,
    ← complexCoordinates, ← LinearMap.range_comp]
  apply congrArg LinearMap.range
  apply LinearMap.ext
  intro u
  simpa [graphInclusion, Matrix.toLin'_apply] using graphColumns_eq_mulVec I complexAlgebra A u

theorem stablePlane_chart_iff (b : Module.Basis ι ℂ V) {d : ℕ}
    (hd : d ≤ Module.finrank ℂ V) (T : V →ₗ[ℂ] V)
    (I : Pivot ι d) (A : Matrix (Outside I) (Inside I) ℂ) :
    StablePlane b hd T (grassmannianChartPoint b hd I A) ↔
      graphResidual I (operatorInCoordinates b T) A = 0 := by
  let e := b.equivFun
  let T' := e.toLinearMap.comp (T.comp e.symm.toLinearMap)
  let p := grassmannianChartPoint b hd I A
  let P := grassmannianSubspace b hd p
  have hcomp : e.toLinearMap.comp T = T'.comp e.toLinearMap := by
    ext x i
    exact congrArg (fun y ↦ e (T y) i) (e.symm_apply_apply x).symm
  change P.map T ≤ P ↔ _
  rw [← Submodule.map_le_map_iff_of_injective e.injective (P.map T) P,
    ← Submodule.map_comp, hcomp, Submodule.map_comp]
  change (P.map b.equivFun.toLinearMap).map T' ≤ P.map b.equivFun.toLinearMap ↔ _
  rw [show P.map b.equivFun.toLinearMap = _ from grassmannianChartSubspace b hd I A,
    Submodule.map_le_iff_le_comap, graphResidual_eq_zero]
  have hT (x : ι → ℂ) : T' x = operatorInCoordinates b T *ᵥ x := by
    rw [← Matrix.toLin'_apply, operatorInCoordinates, Matrix.toLin'_toMatrix']
  constructor
  · intro h u
    have hu := h (LinearMap.mem_range_self (Matrix.toLin' (graphMatrix I A)) u)
    rw [Submodule.mem_comap, LinearMap.mem_range] at hu
    obtain ⟨v, hv⟩ := hu
    use v
    simpa only [Matrix.toLin'_apply, hT] using hv.symm
  · intro h x hx
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, hv⟩ := h u
    rw [Submodule.mem_comap, LinearMap.mem_range]
    use v
    simpa only [Matrix.toLin'_apply, hT] using hv.symm

theorem grassmannianChartPoint_cover (b : Module.Basis ι ℂ V) {d : ℕ}
    (hd : d ≤ Module.finrank ℂ V) (p : GrassmannianPoints b hd) :
    ∃ (I : Pivot ι d) (A : Matrix (Outside I) (Inside I) ℂ),
      grassmannianChartPoint b hd I A = p := by
  obtain ⟨I, hi⟩ := LinearAlgebraicGroups.GrassmannianCharts.fieldPivotCoverage
    ℂ V ι b d hd ℂ (grassmannianPlane b hd p)
  obtain ⟨f, hf⟩ := ((grassmannianCharts b hd).factor_iff I complexAlgebra p).mpr hi
  exact ⟨I, chartMatrixEquiv I complexAlgebra f, by simpa [grassmannianChartPoint] using hf⟩

end Grassmannian

open TopologicalSpace

/-- The scheme point underlying a morphism from Spec ℂ over ℂ. -/
def pointLocation {X : SchemeOver ℂ} (p : Points X complexAlgebra) : X.left :=
  p.left (default : PrimeSpectrum ℂ)

def reducedClosureIdeal (X : SchemeOver ℂ) (S : Set (Points X complexAlgebra)) :
    X.left.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (pointLocation '' S))

def reducedClosureScheme (X : SchemeOver ℂ) (S : Set (Points X complexAlgebra)) :
    SchemeOver ℂ :=
  Over.mk ((reducedClosureIdeal X S).subschemeι ≫ X.hom)

def reducedClosureInclusion (X : SchemeOver ℂ) (S : Set (Points X complexAlgebra)) :
    reducedClosureScheme X S ⟶ X :=
  Over.homMk (reducedClosureIdeal X S).subschemeι rfl

def stableScheme {V ι : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup V]
    [Module ℂ V] (b : Module.Basis ι ℂ V) {d : ℕ} (hd : d ≤ Module.finrank ℂ V) (T : V →ₗ[ℂ] V) :
    SchemeOver ℂ :=
  reducedClosureScheme (grassmannianCharts b hd).scheme {p | StablePlane b hd T p}

theorem pointLocation_comp {X Y : SchemeOver ℂ} (p : Points X complexAlgebra) (j : X ⟶ Y) :
    pointLocation (p ≫ j) = j.left (pointLocation p) := rfl

theorem pointLocation_range {X : SchemeOver ℂ} (p : Points X complexAlgebra) :
    Set.range p.left = {pointLocation p} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change PrimeSpectrum ℂ at y
    rw [Unique.eq_default y]
    rfl
  · rintro (rfl : x = _)
    exact Set.mem_range_self _

theorem openChart_preimage_points {X Y : SchemeOver ℂ} (j : Y ⟶ X) [IsOpenImmersion j.left]
    (S : Set (Points X complexAlgebra)) :
    j.left ⁻¹' (pointLocation '' S) = pointLocation '' {q : Points Y complexAlgebra | q ≫ j ∈ S} := by
  ext y
  constructor
  · rintro ⟨p, hp, hpy⟩
    have hrange : Set.range p.left ⊆ Set.range j.left := by
      rw [pointLocation_range]
      exact Set.singleton_subset_iff.mpr ⟨y, hpy.symm⟩
    let q : Points Y complexAlgebra := Over.homMk (IsOpenImmersion.lift j.left p.left hrange) (by
      rw [← Over.w j, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w])
    have hq : q ≫ j = p :=
      Over.OverMorphism.ext (IsOpenImmersion.lift_fac j.left p.left hrange)
    exact ⟨q, by change q ≫ j ∈ S; rw [hq]; exact hp, j.left.isOpenEmbedding.injective
      ((pointLocation_comp q j).symm.trans ((congrArg pointLocation hq).trans hpy))⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q ≫ j, hq, pointLocation_comp q j⟩

theorem chart_location {ι : Type} [DecidableEq ι] {d : ℕ} (I : Pivot ι d)
    (A : Matrix (Outside I) (Inside I) ℂ) :
    pointLocation ((chartMatrixEquiv I complexAlgebra).symm A) =
      MvPolynomial.pointToPoint (k := ℂ) (chartVariables I A) := by
  let f : CommRingCat.of (chartAlgebra (k := ℂ) I) ⟶ CommRingCat.of ℂ :=
    CommRingCat.ofHom (MvPolynomial.aeval (chartVariables I A)).toRingHom
  change (Spec.map f) (default : PrimeSpectrum ℂ) = _
  change PrimeSpectrum.comap f.hom (default : PrimeSpectrum ℂ) = _
  apply PrimeSpectrum.ext
  ext p
  rw [show (default : PrimeSpectrum ℂ) = ⊥ from Subsingleton.elim _ _]
  change (f.hom p ∈ (⊥ : Ideal ℂ)) ↔ p ∈ MvPolynomial.vanishingIdeal ℂ {chartVariables I A}
  change MvPolynomial.aeval (chartVariables I A) p ∈ (⊥ : Ideal ℂ) ↔ _
  simp

open Scheme.IdealSheafData

def chartInclusion {V ι : Type} [AddCommGroup V] [Module ℂ V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ V) {d : ℕ}
    (hd : d ≤ Module.finrank ℂ V) (I : Pivot ι d) :
    Spec (CommRingCat.of (chartAlgebra (k := ℂ) I)) ⟶ (grassmannianCharts b hd).scheme.left :=
  ((grassmannianCharts b hd).chart I).left


section Subspaces

variable {V ι : Type} [AddCommGroup V] [Module ℂ V] [Fintype ι] [DecidableEq ι]

/-- Realize a d-dimensional subspace as a point of the ordinary Grassmannian. -/
def subspacePlane (b : Module.Basis ι ℂ V) {d : ℕ} (hd : d ≤ Module.finrank ℂ V)
    (P : Submodule ℂ V) (hP : Module.finrank ℂ P = d) : Plane ℂ V d complexAlgebra := by
  let Q := P.map (TensorProduct.lid ℂ V).symm.toLinearMap
  let q := P.equivMapOfInjective _ (TensorProduct.lid ℂ V).symm.injective
  letI : FiniteDimensional ℂ V := Module.Finite.of_basis b
  letI : FiniteDimensional ℂ (ℂ ⊗[ℂ] V) := Module.Finite.equiv (TensorProduct.lid ℂ V).symm
  refine
    { toSubmodule := Q
      finite_quotient := inferInstance
      projective_quotient := inferInstance
      rankAtStalk_eq := ?_ }
  intro p
  change Module.rankAtStalk (ℂ ⊗[ℂ] V ⧸ Q) p = _
  rw [Module.rankAtStalk_eq_finrank_of_free]
  have hdim : Module.finrank ℂ Q = d := q.finrank_eq.symm.trans hP
  have htotal := Q.finrank_quotient_add_finrank
  have he := (TensorProduct.lid ℂ V).finrank_eq
  change Module.finrank ℂ (ℂ ⊗[ℂ] V ⧸ Q) = Module.finrank ℂ V - d
  omega

def subspacePoint (b : Module.Basis ι ℂ V) {d : ℕ} (hd : d ≤ Module.finrank ℂ V)
    (P : Submodule ℂ V) (hP : Module.finrank ℂ P = d) : GrassmannianPoints b hd :=
  (grassmannianCharts b hd).affinePoints.inv.app complexAlgebra (subspacePlane b hd P hP)

theorem subspacePoint_subspace (b : Module.Basis ι ℂ V) {d : ℕ} (hd : d ≤ Module.finrank ℂ V)
    (P : Submodule ℂ V) (hP : Module.finrank ℂ P = d) :
    grassmannianSubspace b hd (subspacePoint b hd P hP) = P := by
  let e := ((grassmannianCharts b hd).affinePoints.app complexAlgebra).toEquiv
  have h : grassmannianPlane b hd (subspacePoint b hd P hP) = subspacePlane b hd P hP :=
    e.apply_symm_apply (subspacePlane b hd P hP)
  rw [grassmannianSubspace, h]
  change (P.map (TensorProduct.lid ℂ V).symm.toLinearMap).map (TensorProduct.lid ℂ V).toLinearMap = P
  rw [← Submodule.map_comp]
  rw [LinearEquiv.comp_symm, Submodule.map_id]

theorem grassmannianSubspace_injective (b : Module.Basis ι ℂ V) {d : ℕ}
    (hd : d ≤ Module.finrank ℂ V) : Function.Injective (grassmannianSubspace b hd) := by
  intro p q hpq
  apply ((grassmannianCharts b hd).affinePoints.app complexAlgebra).toEquiv.injective
  apply Module.Grassmannian.ext
  exact Submodule.map_injective_of_injective (TensorProduct.lid ℂ V).injective hpq

theorem grassmannianSubspace_finrank (b : Module.Basis ι ℂ V) {d : ℕ}
    (hd : d ≤ Module.finrank ℂ V) (p : GrassmannianPoints b hd) :
    Module.finrank ℂ (grassmannianSubspace b hd p) = d := by
  let Q := (grassmannianPlane b hd p).toSubmodule
  let : FiniteDimensional ℂ V := Module.Finite.of_basis b
  let : FiniteDimensional ℂ (ℂ ⊗[ℂ] V) := Module.Finite.equiv (TensorProduct.lid ℂ V).symm
  have h := (grassmannianPlane b hd p).rankAtStalk_eq (⊥ : PrimeSpectrum ℂ)
  change Module.rankAtStalk (ℂ ⊗[ℂ] V ⧸ Q) (⊥ : PrimeSpectrum ℂ) =
    Module.finrank ℂ V - d at h
  rw [Module.rankAtStalk_eq_finrank_of_free] at h
  have htotal : Module.finrank ℂ (ℂ ⊗[ℂ] V ⧸ Q) + Module.finrank ℂ Q =
      Module.finrank ℂ (ℂ ⊗[ℂ] V) := Q.finrank_quotient_add_finrank
  have he := (TensorProduct.lid ℂ V).finrank_eq
  have hdim : Module.finrank ℂ Q = d := by
    change Module.finrank ℂ (ℂ ⊗[ℂ] V ⧸ Q) = Module.finrank ℂ V - d at h
    omega
  exact (Q.equivMapOfInjective _ (TensorProduct.lid ℂ V).injective).finrank_eq.symm.trans hdim

end Subspaces

section BoundedStages

abbrev WindowDimension (r : ℕ) (a : ℤ) (m : ℕ) :=
  Fin (Module.finrank ℂ (Window r a m) + 1)

theorem windowDimension_le {r : ℕ} {a : ℤ} {m : ℕ} (d : WindowDimension r a m) :
    d.val ≤ Module.finrank ℂ (Window r a m) :=
  Nat.lt_succ_iff.mp d.isLt

abbrev WindowPoints (r : ℕ) (a : ℤ) (m : ℕ) (d : WindowDimension r a m) :=
  GrassmannianPoints (windowBasis r a m) (windowDimension_le d)

def windowStableScheme (r : ℕ) (a : ℤ) (m : ℕ) (d : WindowDimension r a m) : SchemeOver ℂ :=
  stableScheme (windowBasis r a m) (windowDimension_le d) (windowOperator r a m)

abbrev WindowStage (r : ℕ) (a : ℤ) (m : ℕ) :=
  Σ d : WindowDimension r a m,
    StablePoints (windowBasis r a m) (windowDimension_le d) (windowOperator r a m)

instance stablePointsTopology {V ι : Type} [AddCommGroup V] [Module ℂ V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ V) {d : ℕ} (hd : d ≤ Module.finrank ℂ V) (T : V →ₗ[ℂ] V) :
    TopologicalSpace (StablePoints b hd T) :=
  TopologicalSpace.induced (fun (p : StablePoints b hd T) ↦ p.val) (grassmannianAnalyticTopology b hd)

instance windowStageTopology (r : ℕ) (a : ℤ) (m : ℕ) : TopologicalSpace (WindowStage r a m) :=
  @instTopologicalSpaceSigma _ _ fun d ↦
    stablePointsTopology (windowBasis r a m) (windowDimension_le d) (windowOperator r a m)

private theorem quotientSubspace_stable {R M : Type} [CommRing R] [Algebra ℂ R]
    [AddCommGroup M] [Module R M] [Module ℂ M] [IsScalarTower ℂ R M]
    (P Q : Submodule R M) (c : R) :
    (quotientSubspace P Q).map ((c • (LinearMap.id : (M ⧸ Q) →ₗ[R] (M ⧸ Q))).restrictScalars ℂ)
      ≤ quotientSubspace P Q := by
  rw [Submodule.map_le_iff_le_comap]
  intro x hx
  exact (P.map Q.mkQ).smul_mem c hx

theorem latticeSubspace_stable {r : ℕ} (a : ℤ) (m : ℕ) (L : Lattice r) :
    (latticeSubspace a m L).map (windowOperator r a m) ≤ latticeSubspace a m L :=
  @quotientSubspace_stable O ((scalarLattice r a).val : Type)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (L.val.comap (scalarLattice r a).val.subtype) (windowLower r a m) t

def windowStagePoint {r : ℕ} (a : ℤ) (m : ℕ) (L : Lattice r) : WindowStage r a m := by
  let P := latticeSubspace a m L
  let d : WindowDimension r a m := ⟨Module.finrank ℂ P, Nat.lt_succ_of_le P.finrank_le⟩
  refine ⟨d, subspacePoint (windowBasis r a m) (windowDimension_le d) P rfl, ?_⟩
  unfold StablePlane
  rw [subspacePoint_subspace]
  exact latticeSubspace_stable a m L

abbrev BoundedStage (r N : ℕ) := WindowStage r (-(N : ℤ)) (2*N)

def boundedPoint {r N : ℕ} (L : BoundedLattice r N) : BoundedStage r N :=
  windowStagePoint (-(N : ℤ)) (2*N) L.val

instance boundedAnalyticTopology (r N : ℕ) : TopologicalSpace (BoundedLattice r N) :=
  TopologicalSpace.induced (boundedPoint (r := r) (N := N)) inferInstance

def boundedInclusion {r N M : ℕ} (h : N ≤ M) (L : BoundedLattice r N) : BoundedLattice r M :=
  ⟨L.val, (diagonalLattice_le fun _ ↦ Int.ofNat_le.mpr h).trans L.property.1,
    L.property.2.trans (diagonalLattice_le fun _ ↦ neg_le_neg (Int.ofNat_le.mpr h))⟩

/-- The topology on the union of the closed bounded stages. -/
instance latticeAnalyticTopology (r : ℕ) : TopologicalSpace (Lattice r) :=
  ⨆ N : ℕ, TopologicalSpace.coinduced (Subtype.val : BoundedLattice r N → Lattice r) inferInstance

/-- The torus uses an ordered product of rank-one stages, including the empty product. -/
@[instance_reducible] def torusAnalyticTopology (r : ℕ) : TopologicalSpace (TorusLattice r) :=
  ⨆ N : ℕ, TopologicalSpace.coinduced (fun (x : BoundedTorus r N) i ↦ (x i).val) inferInstance

def torusStageScheme (r N : ℕ)
    (d : Fin r → WindowDimension 1 (-(N : ℤ)) (2*N)) : SchemeOver ℂ :=
  CategoryTheory.Limits.piObj fun i ↦ windowStableScheme 1 (-(N : ℤ)) (2*N) (d i)

end BoundedStages

section Schubert

theorem orbitBound_exists (ab : DominantPair) : ∃ N : ℕ, OrbitBound ab N := by
  let N := max ab.val.1.natAbs ab.val.2.natAbs
  refine ⟨N, fun i ↦ ?_⟩
  have h₁ := Nat.le_max_left ab.val.1.natAbs ab.val.2.natAbs
  have h₂ := Nat.le_max_right ab.val.1.natAbs ab.val.2.natAbs
  unfold pairCoweight
  split <;> dsimp [N] <;> omega

def schubertOrbitPoints (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
    (d : WindowDimension 2 (-(N : ℤ)) (2*N)) :
    Set (WindowPoints 2 (-(N : ℤ)) (2*N) d) :=
  {p | ∃ L : GL2Lattice, ∃ hL : L ∈ gl2Orbit ab,
    grassmannianSubspace (windowBasis 2 (-(N : ℤ)) (2*N)) (windowDimension_le d) p =
      boundedSubspace (r := 2) (N := N) ⟨L, gl2Orbit_bounded ab hN hL⟩}

/-- The reduced Zariski closure of the positive-loop orbit, in dimension d of the bounded stage. -/
def schubertScheme (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
    (d : WindowDimension 2 (-(N : ℤ)) (2*N)) : SchemeOver ℂ :=
  reducedClosureScheme
    (grassmannianCharts (windowBasis 2 (-(N : ℤ)) (2*N)) (windowDimension_le d)).scheme
    (schubertOrbitPoints ab N hN d)

/-- The complex points of that closure, with topology inherited from the ordinary Grassmannian. -/
abbrev SchubertPoints (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
    (d : WindowDimension 2 (-(N : ℤ)) (2*N)) :=
  {p : WindowPoints 2 (-(N : ℤ)) (2*N) d //
    pointLocation p ∈ closure (pointLocation '' schubertOrbitPoints ab N hN d)}

end Schubert

open CategoryTheory.Limits

/-- In the reduced global stability scheme, the pivot chart is the spectrum of the
polynomial coordinate ring modulo the radical of the projected-operator ideal. -/
def StableAffineChart {V ι : Type} [AddCommGroup V] [Module ℂ V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ V) {d : ℕ}
    (hd : d ≤ Module.finrank ℂ V) (T : V →ₗ[ℂ] V) (I : Pivot ι d) : Prop :=
  let f := chartInclusion b hd I
  let J := reducedClosureIdeal (grassmannianCharts b hd).scheme {p | StablePlane b hd T p}
  let R := reducedStabilityIdeal I (operatorInCoordinates b T)
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk R))
  ∃ e : pullback f J.subschemeι ≅ Spec (CommRingCat.of (chartAlgebra (k := ℂ) I ⧸ R)),
    e.hom ≫ q = pullback.fst f J.subschemeι


def CosetRelationLaw : Prop :=
  ∀ {Γ : Type*} [Group Γ] (H : Subgroup Γ), CosetRelation H

def TwistedProductLaw : Prop :=
  ∀ {Γ X : Type*} [Group Γ] [MulAction Γ X] (H : Subgroup Γ)
    {A : Set (Grassmannian H)} {S : Set X} (hS : StableStage H S)
    (p q : Representatives H A S),
    (Quotient.mk (twistRel H A S) p : TwistedProduct H A S hS) =
      Quotient.mk (twistRel H A S) q ↔
        ∃ h : H, q.val.1 = p.val.1 * (h : Γ) ∧ p.val.2 = (h : Γ) • q.val.2

def StableAffineChartLaw : Prop :=
  ∀ {V ι : Type} [AddCommGroup V] [Module ℂ V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ V) {d : ℕ} (hd : d ≤ Module.finrank ℂ V)
    (T : V →ₗ[ℂ] V) (I : Pivot ι d), StableAffineChart b hd T I

def StableSchemePointComparison : Prop :=
  ∀ {V ι : Type} [AddCommGroup V] [Module ℂ V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ V) {d : ℕ} (hd : d ≤ Module.finrank ℂ V) (T : V →ₗ[ℂ] V),
    ∃ e : Points (stableScheme b hd T) complexAlgebra ≃ StablePoints b hd T,
      ∀ q, (e q).val = q ≫ reducedClosureInclusion
        (grassmannianCharts b hd).scheme {p | StablePlane b hd T p}

def SchubertClosureComparison : Prop :=
  ∀ (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
    (d : WindowDimension 2 (-(N : ℤ)) (2*N)),
    (∃ f : schubertScheme ab N hN d ⟶ windowStableScheme 2 (-(N : ℤ)) (2*N) d,
      IsClosedImmersion f.left) ∧
    (∃ e : Points (schubertScheme ab N hN d) complexAlgebra ≃ SchubertPoints ab N hN d,
      ∀ q, (e q).val = q ≫ reducedClosureInclusion
        (grassmannianCharts (windowBasis 2 (-(N : ℤ)) (2*N)) (windowDimension_le d)).scheme
        (schubertOrbitPoints ab N hN d))

namespace Expected

-- These type constants retain the two independent universes of the twisted product.
set_option linter.checkUnivs false

def OType := type_of% (@LatticeModelSpecs.O)
def KType := type_of% (@LatticeModelSpecs.K)
def tType := type_of% (@LatticeModelSpecs.t)
def inclusionType := type_of% (@LatticeModelSpecs.inclusion)
def monomialType := type_of% (@LatticeModelSpecs.monomial)
def CoordinatesType := type_of% (@LatticeModelSpecs.Coordinates)
def LatticeType := type_of% (@LatticeModelSpecs.Lattice)
def GL2LatticeType := type_of% (@LatticeModelSpecs.GL2Lattice)
def TorusLatticeType := type_of% (@LatticeModelSpecs.TorusLattice)
def CoweightType := type_of% (@LatticeModelSpecs.Coweight)
def coordinateInclusionType := type_of% (@LatticeModelSpecs.coordinateInclusion)
def standardLatticeType := type_of% (@LatticeModelSpecs.standardLattice)
def loopLinearEquivType := type_of% (@LatticeModelSpecs.loopLinearEquiv)
def latticeActionType := type_of% (@LatticeModelSpecs.latticeAction)
def torusActionType := type_of% (@LatticeModelSpecs.torusAction)
def diagonalLoopType := type_of% (@LatticeModelSpecs.diagonalLoop)
def diagonalLatticeType := type_of% (@LatticeModelSpecs.diagonalLattice)
def torusMonomialType := type_of% (@LatticeModelSpecs.torusMonomial)
def torusLatticeAtType := type_of% (@LatticeModelSpecs.torusLatticeAt)
def scalarLatticeType := type_of% (@LatticeModelSpecs.scalarLattice)
def positiveGLMapType := type_of% (@LatticeModelSpecs.positiveGLMap)
def positiveTorusMapType := type_of% (@LatticeModelSpecs.positiveTorusMap)
def PositiveGLType := type_of% (@LatticeModelSpecs.PositiveGL)
def PositiveTorusType := type_of% (@LatticeModelSpecs.PositiveTorus)
def GrassmannianType := type_of% (@LatticeModelSpecs.Grassmannian)
def cosetType := type_of% (@LatticeModelSpecs.coset)
def StableStageType := type_of% (@LatticeModelSpecs.StableStage)
def RepresentativesType := type_of% (@LatticeModelSpecs.Representatives)
def twistRelType := type_of% (@LatticeModelSpecs.twistRel)
def TwistedProductType := type_of% (@LatticeModelSpecs.TwistedProduct)
def firstProjectionType := type_of% (@LatticeModelSpecs.firstProjection)
def terminalMapType := type_of% (@LatticeModelSpecs.terminalMap)
def BoundedLatticeType := type_of% (@LatticeModelSpecs.BoundedLattice)
def BoundedTorusType := type_of% (@LatticeModelSpecs.BoundedTorus)
def WindowType := type_of% (@LatticeModelSpecs.Window)
def BoundedWindowType := type_of% (@LatticeModelSpecs.BoundedWindow)
def windowOperatorType := type_of% (@LatticeModelSpecs.windowOperator)
def latticeSubspaceType := type_of% (@LatticeModelSpecs.latticeSubspace)
def boundedSubspaceType := type_of% (@LatticeModelSpecs.boundedSubspace)
def windowCoordinatesType := type_of% (@LatticeModelSpecs.windowCoordinates)
def windowBasisType := type_of% (@LatticeModelSpecs.windowBasis)
def JetRingType := type_of% (@LatticeModelSpecs.JetRing)
def jetReductionType := type_of% (@LatticeModelSpecs.jetReduction)
def jetCoefficientsType := type_of% (@LatticeModelSpecs.jetCoefficients)
def jetTopologyType := type_of% (@LatticeModelSpecs.jetTopology)
def GLJetsType := type_of% (@LatticeModelSpecs.GLJets)
def TorusJetsType := type_of% (@LatticeModelSpecs.TorusJets)
def reduceGLType := type_of% (@LatticeModelSpecs.reduceGL)
def reduceTorusType := type_of% (@LatticeModelSpecs.reduceTorus)
def glJetTopologyType := type_of% (@LatticeModelSpecs.glJetTopology)
def torusJetTopologyType := type_of% (@LatticeModelSpecs.torusJetTopology)
def grassmannianChartsType := type_of% (@LatticeModelSpecs.grassmannianCharts)
def grassmannianFamiliesType := type_of% (@LatticeModelSpecs.grassmannianFamilies)
def GrassmannianPointsType := type_of% (@LatticeModelSpecs.GrassmannianPoints)
def grassmannianChartPointType := type_of% (@LatticeModelSpecs.grassmannianChartPoint)
def grassmannianAnalyticTopologyType := type_of% (@LatticeModelSpecs.grassmannianAnalyticTopology)
def grassmannianSubspaceType := type_of% (@LatticeModelSpecs.grassmannianSubspace)
def graphMatrixType := type_of% (@LatticeModelSpecs.graphMatrix)
def graphResidualType := type_of% (@LatticeModelSpecs.graphResidual)
def stabilityIdealType := type_of% (@LatticeModelSpecs.stabilityIdeal)
def reducedStabilityIdealType := type_of% (@LatticeModelSpecs.reducedStabilityIdeal)
def StablePlaneType := type_of% (@LatticeModelSpecs.StablePlane)
def StablePointsType := type_of% (@LatticeModelSpecs.StablePoints)
def stableSchemeType := type_of% (@LatticeModelSpecs.stableScheme)
def windowStableSchemeType := type_of% (@LatticeModelSpecs.windowStableScheme)
def WindowStageType := type_of% (@LatticeModelSpecs.WindowStage)
def boundedPointType := type_of% (@LatticeModelSpecs.boundedPoint)
def boundedAnalyticTopologyType := type_of% (@LatticeModelSpecs.boundedAnalyticTopology)
def boundedInclusionType := type_of% (@LatticeModelSpecs.boundedInclusion)
def latticeAnalyticTopologyType := type_of% (@LatticeModelSpecs.latticeAnalyticTopology)
def torusAnalyticTopologyType := type_of% (@LatticeModelSpecs.torusAnalyticTopology)
def torusStageSchemeType := type_of% (@LatticeModelSpecs.torusStageScheme)
def DominantPairType := type_of% (@LatticeModelSpecs.DominantPair)
def pairCoweightType := type_of% (@LatticeModelSpecs.pairCoweight)
def gl2OrbitType := type_of% (@LatticeModelSpecs.gl2Orbit)
def OrbitBoundType := type_of% (@LatticeModelSpecs.OrbitBound)
def schubertOrbitPointsType := type_of% (@LatticeModelSpecs.schubertOrbitPoints)
def schubertSchemeType := type_of% (@LatticeModelSpecs.schubertScheme)
def SchubertPointsType := type_of% (@LatticeModelSpecs.SchubertPoints)

end Expected

end
end LatticeModelSpecs
end RepTheorySurvey.Geometric
