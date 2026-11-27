import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.AmitsurAlgebras
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.AmitsurComplex

/-! The augmented Amitsur cochain complex of a commutative algebra with module coefficients. -/

open CategoryTheory
open scoped BigOperators TensorProduct ZeroObject

namespace DerivedFormalization.Descent.AmitsurComplex

universe u v w

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
variable (M : ModuleCat.{max u v w} A)

abbrev Degree (p : ℕ) : ModuleCat.{max u v w} A :=
  ModuleCat.of A (AmitsurAlgebras.Degree A B p ⊗[A] M)

/-- Extend an ordered algebra coface by the identity on the coefficient module. -/
noncomputable def coface {p : ℕ} (i : Fin (p + 2)) : Degree A B M p ⟶ Degree A B M (p + 1) :=
  ModuleCat.ofHom (TensorProduct.map
    (AmitsurAlgebras.coface (A := A) (B := B) i).toLinearMap LinearMap.id)

/-- Extend the algebra unit by the identity, identifying `A ⊗[A] M` with `M`. -/
noncomputable def augmentation : M ⟶ Degree A B M 0 :=
  ModuleCat.ofHom ((TensorProduct.map (AmitsurAlgebras.augmentation A B).toLinearMap
    LinearMap.id).comp (TensorProduct.lid A M).symm.toLinearMap)

@[simp]
theorem augmentation_apply (m : M) :
    augmentation A B M m = 1 ⊗ₜ[A] m := by
  simp [augmentation]

@[simp]
theorem coface_tmul {p : ℕ} (i : Fin (p + 2)) (b : AmitsurAlgebras.Degree A B p) (m : M) :
    coface A B M i (b ⊗ₜ[A] m) =
      (AmitsurAlgebras.coface (A := A) (B := B) i b) ⊗ₜ[A] m := by
  simp [coface]

/-- On a pure tensor, the coface inserts the unit in its designated position. -/
theorem coface_tprod_tmul {p : ℕ} (i : Fin (p + 2)) (b : Fin (p + 1) → B) (m : M) :
    coface A B M i (PiTensorProduct.tprod A b ⊗ₜ[A] m) =
      PiTensorProduct.tprod A (i.insertNth 1 b) ⊗ₜ[A] m := by
  rw [coface_tmul, AmitsurAlgebras.coface_tprod]

/-- The differential in nonnegative degree, starting with the positive zeroth coface. -/
noncomputable def differential (p : ℕ) : Degree A B M p ⟶ Degree A B M (p + 1) :=
  ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • coface A B M i

theorem differential_sq (p : ℕ) :
    differential A B M p ≫ differential A B M (p + 1) = 0 :=
  AlgebraicTopology.AlternatingCofaceMapComplex.d_squared
    (AmitsurAlgebras.diagram A B ⋙ AmitsurComplexSpec.tensorCoefficients A M) p

theorem augmentation_comp_differential :
    augmentation A B M ≫ differential A B M 0 = 0 := by
  have h : augmentation A B M ≫ coface A B M (0 : Fin 2) =
      augmentation A B M ≫ coface A B M (1 : Fin 2) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change coface A B M (0 : Fin 2) (augmentation A B M m) =
      coface A B M (1 : Fin 2) (augmentation A B M m)
    rw [augmentation_apply, coface_tmul, coface_tmul]
    simp
  rw [differential, Preadditive.comp_sum, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one, neg_zsmul,
    Preadditive.comp_neg, h, add_neg_cancel]

/-- The graded module is zero below the augmented term in degree `-1`. -/
noncomputable def term : ℤ → ModuleCat.{max u v w} A :=
  AmitsurComplexSpec.term A B M

/-- The differential to the next integer degree. -/
noncomputable def step : (q : ℤ) → term A B M q ⟶ term A B M (q + 1)
  | .ofNat p => differential A B M p
  | .negSucc 0 => augmentation A B M
  | .negSucc (_ + 1) => 0

theorem step_sq (q : ℤ) :
    step A B M q ≫ step A B M (q + 1) = 0 := by
  cases q with
  | ofNat p => exact differential_sq A B M p
  | negSucc n =>
    cases n with
    | zero => exact augmentation_comp_differential A B M
    | succ n =>
      change 0 ≫ step A B M (Int.negSucc (n + 1) + 1) = 0
      rw [Limits.zero_comp]

/-- The cochain complex indexed by the actual integer degrees of the augmentation. -/
noncomputable def complex : CochainComplex (ModuleCat.{max u v w} A) ℤ :=
  CochainComplex.of (term A B M) (step A B M) (step_sq A B M)

@[simp]
theorem complex_X_ofNat (p : ℕ) : (complex A B M).X (p : ℤ) = Degree A B M p := rfl

@[simp]
theorem complex_X_neg_one : (complex A B M).X (-1) = M := rfl

theorem complex_X_of_lt (q : ℤ) (hq : q < -1) : (complex A B M).X q = 0 := by
  cases q with
  | ofNat p =>
    change (p : ℤ) < -1 at hq
    omega
  | negSucc n =>
    cases n with
    | zero => omega
    | succ n => rfl

@[simp]
theorem complex_d_succ (q : ℤ) : (complex A B M).d q (q + 1) = step A B M q :=
  CochainComplex.of_d _ _ _

@[simp]
theorem complex_d_ofNat (p : ℕ) :
    (complex A B M).d (p : ℤ) (↑p + 1) = differential A B M p :=
  complex_d_succ A B M p

@[simp]
theorem complex_d_neg_one : (complex A B M).d (-1) 0 = augmentation A B M :=
  complex_d_succ A B M (-1)

theorem complex_d_of_ne (q r : ℤ) (h : q + 1 ≠ r) : (complex A B M).d q r = 0 :=
  (complex A B M).shape q r h

variable {M} {N : ModuleCat.{max u v w} A}

/-- In nonnegative degrees the coefficient map acts on the final tensor factor. -/
noncomputable def degreeMap (f : M ⟶ N) (p : ℕ) : Degree A B M p ⟶ Degree A B N p :=
  AmitsurComplexSpec.degreeMap A B f p

@[simp]
theorem degreeMap_tmul (f : M ⟶ N) (p : ℕ) (b : AmitsurAlgebras.Degree A B p) (m : M) :
    degreeMap A B f p (b ⊗ₜ[A] m) = b ⊗ₜ[A] f m := by
  simp [degreeMap, AmitsurComplexSpec.degreeMap]

/-- The map of augmented complexes associated to a linear map of coefficient modules. -/
noncomputable def map (f : M ⟶ N) : complex A B M ⟶ complex A B N :=
  AmitsurComplexSpec.map A B f

@[simp]
theorem map_f_ofNat (f : M ⟶ N) (p : ℕ) : (map A B f).f (p : ℤ) = degreeMap A B f p := rfl

@[simp]
theorem map_f_neg_one (f : M ⟶ N) : (map A B f).f (-1) = f := rfl

theorem degreeMap_differential (f : M ⟶ N) (p : ℕ) :
    degreeMap A B f p ≫ differential A B N p =
      differential A B M p ≫ degreeMap A B f (p + 1) :=
  AmitsurComplexSpec.degreeMap_differential A B f p

theorem augmentation_naturality (f : M ⟶ N) :
    f ≫ augmentation A B N = augmentation A B M ≫ degreeMap A B f 0 :=
  AmitsurComplexSpec.augmentation_naturality A B f

/-- The augmented Amitsur construction as a functor of the coefficient module. -/
noncomputable def functor : ModuleCat.{max u v w} A ⥤
    CochainComplex (ModuleCat.{max u v w} A) ℤ :=
  AmitsurComplexSpec.functor A B

@[simp]
theorem functor_obj (M : ModuleCat.{max u v w} A) :
    (functor A B).obj M = complex A B M := rfl

@[simp]
theorem functor_map (f : M ⟶ N) : (functor A B).map f = map A B f := rfl

/-- Allow the coefficients to live in a universe independent of the two rings. -/
noncomputable def liftedFunctor : ModuleCat.{w} A ⥤
    CochainComplex (ModuleCat.{max u v w} A) ℤ :=
  ModuleCat.uliftFunctor.{max u v} A ⋙ functor.{u, v, w} A B

/-- The augmented term of the lifted complex identifies with the original coefficients. -/
def liftedAugmentedTermEquiv (L : ModuleCat.{w} A) :
    ((liftedFunctor A B).obj L).X (-1) ≃ₗ[A] L :=
  AmitsurComplexSpec.liftedAugmentedTermEquiv A B L

/-- Identify each lifted tensor term with the tensor product with the original coefficients. -/
noncomputable def liftedDegreeEquiv (L : ModuleCat.{w} A) (p : ℕ) :
    ((liftedFunctor A B).obj L).X (p : ℤ) ≃ₗ[A] (AmitsurAlgebras.Degree A B p ⊗[A] L) :=
  AmitsurComplexSpec.liftedDegreeEquiv A B L p

theorem lifted_augmentation_apply (L : ModuleCat.{w} A) (m : L) :
    liftedDegreeEquiv A B L 0
      (((liftedFunctor A B).obj L).d (-1) 0 ((liftedAugmentedTermEquiv A B L).symm m)) =
      1 ⊗ₜ[A] m := by
  let L' := (ModuleCat.uliftFunctor.{max u v} A).obj L
  let m' : L' := ULift.up m
  change liftedDegreeEquiv A B L 0 ((complex A B L').d (-1) 0 m') = _
  calc
    _ = liftedDegreeEquiv A B L 0 (augmentation A B L' m') :=
      congrArg (fun f : L' ⟶ Degree A B L' 0 => liftedDegreeEquiv A B L 0 (f m'))
        (complex_d_neg_one A B L')
    _ = liftedDegreeEquiv A B L 0 (1 ⊗ₜ[A] m') :=
      congrArg (liftedDegreeEquiv A B L 0) (augmentation_apply A B L' m')
    _ = _ := rfl

theorem lifted_coface_tmul (L : ModuleCat.{w} A) {p : ℕ} (i : Fin (p + 2))
    (b : AmitsurAlgebras.Degree A B p) (m : L) :
    liftedDegreeEquiv A B L (p + 1)
      (coface A B ((ModuleCat.uliftFunctor.{max u v} A).obj L) i
        ((liftedDegreeEquiv A B L p).symm (b ⊗ₜ[A] m))) =
      AmitsurAlgebras.coface i b ⊗ₜ[A] m := by
  let L' := (ModuleCat.uliftFunctor.{max u v} A).obj L
  let m' : L' := ULift.up m
  change liftedDegreeEquiv A B L (p + 1)
    (coface A B L' i (b ⊗ₜ[A] m')) = _
  exact (congrArg (liftedDegreeEquiv A B L (p + 1)) (coface_tmul A B L' i b m')).trans rfl

end DerivedFormalization.Descent.AmitsurComplex
