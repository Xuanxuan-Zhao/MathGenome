import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.AmitsurComplex
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Batteries.Tactic.OpenPrivate

/-! Signed product totalization of the Amitsur bicomplex. -/

open CategoryTheory Limits
open scoped TensorProduct ZeroObject

namespace AmitsurTotalComplexSpec

universe u v w

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]

set_option linter.checkUnivs false in
abbrev Complex (A : Type u) [CommRing A] :=
  CochainComplex (ModuleCat.{max u v w} A) ℤ

open AmitsurComplexSpec (degree degreeMap differential)

private theorem degreeMap_comp {L M N : ModuleCat.{max u v w} A}
    (f : L ⟶ M) (g : M ⟶ N) (p : ℕ) :
    degreeMap A B (f ≫ g) p = degreeMap A B f p ≫ degreeMap A B g p := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro b m
  simp [degreeMap]

private theorem degreeMap_id (M : ModuleCat.{max u v w} A) (p : ℕ) :
    degreeMap A B (𝟙 M) p = 𝟙 _ :=
  ModuleCat.hom_ext TensorProduct.map_id

private theorem degreeMap_zero (M N : ModuleCat.{max u v w} A) (p : ℕ) :
    degreeMap A B (0 : M ⟶ N) p = 0 :=
  ModuleCat.hom_ext (TensorProduct.map_zero_right LinearMap.id)

variable (X : Complex.{u, v, w} A)

/-- The module in bidegree `(p,q)`. -/
abbrev cell (p : ℕ) (q : ℤ) := degree A B (X.X q) p

/-- Vertical differential before applying totalization signs. -/
noncomputable def vertical (p : ℕ) (q r : ℤ) :
    cell A B X p q ⟶ cell A B X p r :=
  degreeMap A B (X.d q r) p

/-- The horizontal Amitsur differential in a fixed row. -/
noncomputable def horizontal (p : ℕ) (q : ℤ) :
    cell A B X p q ⟶ cell A B X (p + 1) q :=
  differential A B (X.X q) p

theorem vertical_sq (p : ℕ) (q r s : ℤ) :
    vertical A B X p q r ≫ vertical A B X p r s = 0 := by
  rw [vertical, vertical, ← degreeMap_comp, X.d_comp_d, degreeMap_zero]

theorem horizontal_sq (p : ℕ) (q : ℤ) :
    horizontal A B X p q ≫ horizontal A B X (p + 1) q = 0 :=
  AlgebraicTopology.AlternatingCofaceMapComplex.d_squared
    (AmitsurAlgebrasSpec.diagram A B ⋙ AmitsurComplexSpec.tensorCoefficients A (X.X q)) p

theorem commute (p : ℕ) (q r : ℤ) :
    vertical A B X p q r ≫ horizontal A B X p r =
      horizontal A B X p q ≫ vertical A B X (p + 1) q r :=
  AmitsurComplexSpec.degreeMap_differential A B (X.d q r) p

noncomputable def column (p : ℕ) : Complex.{u, v, w} A where
  X := cell A B X p
  d := vertical A B X p
  shape q r h := by rw [vertical, X.shape q r h, degreeMap_zero]
  d_comp_d' q r s _ _ := vertical_sq A B X p q r s

noncomputable def columnStep (p : ℕ) : column A B X p ⟶ column A B X (p + 1) where
  f := horizontal A B X p
  comm' q r _ := (commute A B X p q r).symm

/-- A cochain complex of columns, with commuting horizontal and vertical maps. -/
noncomputable def bicomplex : CochainComplex (Complex.{u, v, w} A) ℕ :=
  CochainComplex.of (column A B X) (columnStep A B X) (fun p =>
    HomologicalComplex.hom_ext _ _ (horizontal_sq A B X p))

/-- Internal degree of column `p` on diagonal `n`. The zeroth column uses
`n` directly. -/
abbrev rowIndex (n : ℤ) : ℕ → ℤ
  | 0 => n
  | p + 1 => n - (p + 1 : ℕ)

theorem rowIndex_eq (n : ℤ) (p : ℕ) : rowIndex n p = n - p := by
  cases p <;> simp [rowIndex]

private theorem rowIndex_horizontal (n : ℤ) (p : ℕ) :
    rowIndex n p = rowIndex (n + 1) (p + 1) := by
  change rowIndex n p = (n + 1) - (p + 1 : ℕ)
  rw [rowIndex_eq]
  omega

abbrev term (n : ℤ) : ModuleCat.{max u v w} A :=
  ModuleCat.of A (∀ p : ℕ, cell A B X p (rowIndex n p))

/-- Horizontal map with its target row reindexed using the diagonal equality. -/
noncomputable def horizontalTo (p : ℕ) {q r : ℤ} (e : q = r) :
    cell A B X p q ⟶ cell A B X (p + 1) r :=
  horizontal A B X p q ≫ eqToHom (congrArg (cell A B X (p + 1)) e)

private theorem horizontalTo_sq (p : ℕ) {q r s : ℤ} (e : q = r) (e' : r = s) :
    horizontalTo A B X p e ≫ horizontalTo A B X (p + 1) e' = 0 := by
  subst r s
  simpa [horizontalTo] using horizontal_sq A B X p q

private theorem horizontalTo_comm (p : ℕ) {q r s t : ℤ} (e : q = s) (e' : r = t) :
    vertical A B X p q r ≫ horizontalTo A B X p e' =
      horizontalTo A B X p e ≫ vertical A B X (p + 1) s t := by
  subst s t
  simpa [horizontalTo] using commute A B X p q r

/-- The unsigned vertical contribution to the differential on diagonal `n`. -/
noncomputable def diagonalVertical (n : ℤ) (p : ℕ) :
    cell A B X p (rowIndex n p) ⟶ cell A B X p (rowIndex (n + 1) p) :=
  vertical A B X p _ _

/-- The horizontal contribution from input column `p` to output column `p+1`. -/
noncomputable def diagonalHorizontal (n : ℤ) (p : ℕ) :
    cell A B X p (rowIndex n p) ⟶ cell A B X (p + 1) (rowIndex (n + 1) (p + 1)) :=
  horizontalTo A B X p (rowIndex_horizontal n p)

private noncomputable def horizontalComponent (n : ℤ) :
    ∀ p : ℕ, term A B X n →ₗ[A] cell A B X p (rowIndex (n + 1) p)
  | 0 => 0
  | p + 1 => (diagonalHorizontal A B X n p).hom.comp (LinearMap.proj p)

/-- Output column `p` receives the horizontal map from its predecessor and the
vertical map from column `p` multiplied by `(-1)^p`. -/
noncomputable def step (n : ℤ) : term A B X n ⟶ term A B X (n + 1) :=
  ModuleCat.ofHom (LinearMap.pi fun p =>
    horizontalComponent A B X n p +
      (-1 : ℤ) ^ p • (diagonalVertical A B X n p).hom.comp (LinearMap.proj p))

@[simp] theorem step_zero (n : ℤ) (x : term A B X n) :
    step A B X n x 0 = diagonalVertical A B X n 0 (x 0) := by
  change 0 + (-1 : ℤ) ^ 0 • diagonalVertical A B X n 0 (x 0) = _
  simp

@[simp] theorem step_succ (n : ℤ) (p : ℕ) (x : term A B X n) :
    step A B X n x (p + 1) =
      diagonalHorizontal A B X n p (x p) +
        (-1 : ℤ) ^ (p + 1) • diagonalVertical A B X n (p + 1) (x (p + 1)) :=
  rfl

private theorem vertical_vertical (n : ℤ) (p : ℕ) (x : cell A B X p (rowIndex n p)) :
    diagonalVertical A B X (n + 1) p (diagonalVertical A B X n p x) = 0 :=
  DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (vertical_sq A B X p _ _ _)) x

private theorem horizontal_horizontal (n : ℤ) (p : ℕ) (x : cell A B X p (rowIndex n p)) :
    diagonalHorizontal A B X (n + 1) (p + 1) (diagonalHorizontal A B X n p x) = 0 :=
  DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (horizontalTo_sq A B X p (rowIndex_horizontal n p) (rowIndex_horizontal (n + 1) (p + 1)))) x

private theorem vertical_horizontal (n : ℤ) (p : ℕ) (x : cell A B X p (rowIndex n p)) :
    diagonalHorizontal A B X (n + 1) p (diagonalVertical A B X n p x) =
      diagonalVertical A B X (n + 1) (p + 1) (diagonalHorizontal A B X n p x) :=
  DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (horizontalTo_comm A B X p (rowIndex_horizontal n p) (rowIndex_horizontal (n + 1) p))) x

theorem step_sq (n : ℤ) : step A B X n ≫ step A B X (n + 1) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change step A B X (n + 1) (step A B X n x) = 0
  funext p
  cases p with
  | zero =>
    change step A B X (n + 1) (step A B X n x) 0 = 0
    rw [step_zero, step_zero, vertical_vertical]
  | succ p =>
    change step A B X (n + 1) (step A B X n x) (p + 1) = 0
    rw [step_succ, step_succ]
    cases p with
    | zero =>
      rw [step_zero, map_add, map_zsmul, vertical_vertical, vertical_horizontal]
      simp
    | succ p =>
      rw [step_succ, map_add, map_zsmul, horizontal_horizontal, vertical_horizontal,
        map_add, map_zsmul, vertical_vertical]
      simp only [zsmul_zero, add_zero, zero_add, pow_succ, mul_neg, mul_one, neg_zsmul,
        neg_neg, neg_add_cancel]

noncomputable abbrev total : Complex.{u, v, w} A :=
  CochainComplex.of (term A B X) (step A B X) (step_sq A B X)

@[simp] theorem total_d_succ (n : ℤ) :
    (total A B X).d n (n + 1) = step A B X n :=
  CochainComplex.of_d _ _ _

section Functoriality

variable {X} {Y Z : Complex.{u, v, w} A}

private theorem vertical_naturality (f : X ⟶ Y) (p : ℕ) (q r : ℤ) :
    degreeMap A B (f.f q) p ≫ vertical A B Y p q r =
      vertical A B X p q r ≫ degreeMap A B (f.f r) p := by
  rw [vertical, vertical, ← degreeMap_comp, ← degreeMap_comp, f.comm]

private theorem horizontalTo_naturality (f : X ⟶ Y) (p : ℕ) {q r : ℤ} (e : q = r) :
    degreeMap A B (f.f q) p ≫ horizontalTo A B Y p e =
      horizontalTo A B X p e ≫ degreeMap A B (f.f r) (p + 1) := by
  subst r
  simpa [horizontalTo, horizontal] using AmitsurComplexSpec.degreeMap_differential A B (f.f q) p

private noncomputable def component (f : X ⟶ Y) (n : ℤ) : term A B X n ⟶ term A B Y n :=
  ModuleCat.ofHom (LinearMap.pi fun p =>
    (degreeMap A B (f.f (rowIndex n p)) p).hom.comp (LinearMap.proj p))

private theorem component_apply (f : X ⟶ Y) (n : ℤ) (x : term A B X n) (p : ℕ) :
    component A B f n x p = degreeMap A B (f.f (rowIndex n p)) p (x p) := rfl

private theorem component_step (f : X ⟶ Y) (n : ℤ) :
    component A B f n ≫ step A B Y n = step A B X n ≫ component A B f (n + 1) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext p
  change step A B Y n (component A B f n x) p =
    component A B f (n + 1) (step A B X n x) p
  have hv (p : ℕ) := DFunLike.congr_fun
    (congrArg ModuleCat.Hom.hom (vertical_naturality A B f p (rowIndex n p) (rowIndex (n + 1) p))) (x p)
  have hh (p : ℕ) := DFunLike.congr_fun
    (congrArg ModuleCat.Hom.hom (horizontalTo_naturality A B f p (rowIndex_horizontal n p))) (x p)
  cases p with
  | zero =>
    rw [step_zero, component_apply, component_apply, step_zero]
    exact hv 0
  | succ p =>
    rw [step_succ, component_apply, component_apply, component_apply, step_succ, map_add, map_zsmul]
    exact congrArg₂ (· + ·) (hh p) (congrArg ((-1 : ℤ) ^ (p + 1) • ·) (hv (p + 1)))

noncomputable def map (f : X ⟶ Y) : total A B X ⟶ total A B Y :=
  CochainComplex.ofHom (component A B f) (fun n => by
    rw [total_d_succ, total_d_succ]
    exact component_step A B f n)

theorem map_apply (f : X ⟶ Y) (n : ℤ) (x : term A B X n) (p : ℕ) :
    (map A B f).f n x p = degreeMap A B (f.f (rowIndex n p)) p (x p) :=
  component_apply A B f n x p

/-- The product total complex as a functor on arbitrary cochain complexes. -/
noncomputable def functor : Complex.{u, v, w} A ⥤ Complex.{u, v, w} A where
  obj := total A B
  map := map A B
  map_id X := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext p
    change (map A B (𝟙 X)).f n x p = x p
    rw [map_apply]
    change degreeMap A B (𝟙 (X.X (rowIndex n p))) p (x p) = x p
    rw [degreeMap_id]
    rfl
  map_comp f g := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext p
    change (map A B (f ≫ g)).f n x p = (map A B g).f n ((map A B f).f n x) p
    rw [map_apply, map_apply, map_apply]
    rw [HomologicalComplex.comp_f, degreeMap_comp]
    rfl

end Functoriality

private noncomputable def augmentationComponent (n : ℤ) : X.X n ⟶ term A B X n :=
  ModuleCat.ofHom (LinearMap.pi fun
    | 0 => (AmitsurComplexSpec.augmentation A B (X.X n)).hom
    | _ + 1 => 0)

theorem augmentationComponent_zero (n : ℤ) (x : X.X n) :
    augmentationComponent A B X n x 0 = AmitsurComplexSpec.augmentation A B (X.X n) x :=
  rfl

theorem augmentationComponent_succ (n : ℤ) (x : X.X n) (p : ℕ) :
    augmentationComponent A B X n x (p + 1) = 0 :=
  rfl

open private AmitsurComplexSpec.augmentation_comp_differential from
  MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.AmitsurComplex

private theorem augmentation_horizontal (n : ℤ) (x : X.X n) :
    diagonalHorizontal A B X n 0 (AmitsurComplexSpec.augmentation A B (X.X n) x) = 0 := by
  have h : AmitsurComplexSpec.augmentation A B (X.X n) ≫ diagonalHorizontal A B X n 0 = 0 := by
    rw [diagonalHorizontal, horizontalTo, ← Category.assoc, horizontal,
      AmitsurComplexSpec.augmentation_comp_differential, Limits.zero_comp]
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) x

private theorem augmentationComponent_step (n : ℤ) :
    augmentationComponent A B X n ≫ step A B X n =
      X.d n (n + 1) ≫ augmentationComponent A B X (n + 1) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext p
  change step A B X n (augmentationComponent A B X n x) p =
    augmentationComponent A B X (n + 1) (X.d n (n + 1) x) p
  cases p with
  | zero =>
    rw [step_zero, augmentationComponent_zero, augmentationComponent_zero]
    exact (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
      (AmitsurComplexSpec.augmentation_naturality A B (X.d n (n + 1)))) x).symm
  | succ p =>
    rw [step_succ, augmentationComponent_succ, augmentationComponent_succ, map_zero, zsmul_zero, add_zero]
    cases p with
    | zero => rw [augmentationComponent_zero, augmentation_horizontal]
    | succ p => rw [augmentationComponent_succ, map_zero]

/-- The augmentation in column zero. All other column components vanish. -/
noncomputable def augmentation : X ⟶ total A B X :=
  CochainComplex.ofHom (augmentationComponent A B X)
    (fun n => by
      rw [total_d_succ]
      exact augmentationComponent_step A B X n)

/-- The augmentation is natural in the coefficient complex. -/
noncomputable def naturalAugmentation : 𝟭 (Complex.{u, v, w} A) ⟶ functor A B where
  app := augmentation A B
  naturality X Y f := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext p
    change augmentationComponent A B Y n (f.f n x) p =
      (map A B f).f n (augmentationComponent A B X n x) p
    rw [map_apply]
    cases p with
    | zero =>
      rw [augmentationComponent_zero, augmentationComponent_zero]
      exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
        (AmitsurComplexSpec.augmentation_naturality A B (f.f n))) x
    | succ p => rw [augmentationComponent_succ, augmentationComponent_succ, map_zero]

/-- The horizontal map from the augmented column to column zero. -/
noncomputable def augmentationToColumn : X ⟶ column A B X 0 where
  f q := AmitsurComplexSpec.augmentation A B (X.X q)
  comm' q r _ := (AmitsurComplexSpec.augmentation_naturality A B (X.d q r)).symm

/-- The augmented column is in degree `-1`, with zero columns below it. -/
noncomputable def augmentedColumn : ℤ → Complex.{u, v, w} A
  | .ofNat p => column A B X p
  | .negSucc 0 => X
  | .negSucc (_ + 1) => 0

noncomputable def augmentedColumnStep :
    (p : ℤ) → augmentedColumn A B X p ⟶ augmentedColumn A B X (p + 1)
  | .ofNat p => columnStep A B X p
  | .negSucc 0 => augmentationToColumn A B X
  | .negSucc (_ + 1) => 0

private theorem augmentedColumnStep_sq (p : ℤ) :
    augmentedColumnStep A B X p ≫ augmentedColumnStep A B X (p + 1) = 0 := by
  cases p with
  | ofNat p => exact HomologicalComplex.hom_ext _ _ (horizontal_sq A B X p)
  | negSucc p =>
    cases p with
    | zero =>
      exact HomologicalComplex.hom_ext _ _
        (fun q => AmitsurComplexSpec.augmentation_comp_differential A B (X.X q))
    | succ p =>
      change 0 ≫ augmentedColumnStep A B X (Int.negSucc (p + 1) + 1) = 0
      rw [Limits.zero_comp]

noncomputable def augmentedBicomplex : CochainComplex (Complex.{u, v, w} A) ℤ :=
  CochainComplex.of (augmentedColumn A B X) (augmentedColumnStep A B X) (augmentedColumnStep_sq A B X)

section FiniteColumns

/-- Terms of the quotient through column `k`, inclusive. -/
abbrev finiteTerm (k : ℕ) (n : ℤ) : ModuleCat.{max u v w} A :=
  ModuleCat.of A (∀ p : Fin (k + 1), cell A B X p (rowIndex n p))

noncomputable def restrict (k : ℕ) (n : ℤ) : term A B X n ⟶ finiteTerm A B X k n :=
  ModuleCat.ofHom (LinearMap.pi fun p => LinearMap.proj (p : ℕ))

@[simp] theorem restrict_apply (k : ℕ) (n : ℤ) (x : term A B X n) (p : Fin (k + 1)) :
    restrict A B X k n x p = x p := rfl

private noncomputable def extend (k : ℕ) (n : ℤ) : finiteTerm A B X k n ⟶ term A B X n :=
  ModuleCat.ofHom (LinearMap.pi fun p => if h : p < k + 1 then LinearMap.proj (⟨p, h⟩ : Fin (k + 1)) else 0)

private theorem extend_apply (k : ℕ) (n : ℤ) (x : finiteTerm A B X k n) (p : Fin (k + 1)) :
    extend A B X k n x p = x p := by
  let F (h : (p : ℕ) < k + 1) : finiteTerm A B X k n →ₗ[A] cell A B X p (rowIndex n p) :=
    LinearMap.proj (⟨p, h⟩ : Fin (k + 1))
  change ((if h : (p : ℕ) < k + 1 then F h else 0) :
    finiteTerm A B X k n →ₗ[A] cell A B X p (rowIndex n p)) x = x p
  rw [dite_eq_left p.isLt]
  rfl

@[simp] private theorem extend_restrict (k : ℕ) (n : ℤ) :
    extend A B X k n ≫ restrict A B X k n = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext p
  exact extend_apply A B X k n x p

private instance (k : ℕ) (n : ℤ) : IsSplitEpi (restrict A B X k n) :=
  IsSplitEpi.mk' ⟨extend A B X k n, extend_restrict A B X k n⟩

private theorem step_agree (k : ℕ) (n : ℤ) (x y : term A B X n)
    (h : ∀ p : Fin (k + 1), x p = y p) (p : Fin (k + 1)) :
    step A B X n x p = step A B X n y p := by
  obtain ⟨p, hp⟩ := p
  cases p with
  | zero => rw [step_zero, step_zero, h ⟨0, hp⟩]
  | succ p => rw [step_succ, step_succ, h ⟨p, by omega⟩, h ⟨p + 1, hp⟩]

/-- The differential induced on the initial segment of columns. -/
noncomputable def finiteStep (k : ℕ) (n : ℤ) :
    finiteTerm A B X k n ⟶ finiteTerm A B X k (n + 1) :=
  extend A B X k n ≫ step A B X n ≫ restrict A B X k (n + 1)

private theorem restrict_step (k : ℕ) (n : ℤ) :
    restrict A B X k n ≫ finiteStep A B X k n = step A B X n ≫ restrict A B X k (n + 1) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext p
  change step A B X n (extend A B X k n (restrict A B X k n x)) p = step A B X n x p
  exact step_agree A B X k n _ _ (extend_apply A B X k n _) p

private theorem finiteStep_sq (k : ℕ) (n : ℤ) :
    finiteStep A B X k n ≫ finiteStep A B X k (n + 1) = 0 := by
  apply (cancel_epi (restrict A B X k n)).mp
  rw [← Category.assoc, restrict_step, Category.assoc, restrict_step,
    ← Category.assoc, step_sq, Limits.zero_comp, Limits.comp_zero]

noncomputable abbrev finiteTotal (k : ℕ) : Complex.{u, v, w} A :=
  CochainComplex.of (finiteTerm A B X k) (finiteStep A B X k) (finiteStep_sq A B X k)

@[simp] theorem finiteTotal_d_succ (k : ℕ) (n : ℤ) :
    (finiteTotal A B X k).d n (n + 1) = finiteStep A B X k n :=
  CochainComplex.of_d _ _ _

noncomputable def truncate (k : ℕ) : total A B X ⟶ finiteTotal A B X k :=
  CochainComplex.ofHom (restrict A B X k) (fun n => by
    rw [total_d_succ, finiteTotal_d_succ]
    exact restrict_step A B X k n)

private noncomputable def finiteRestriction {k l : ℕ} (h : k ≤ l) (n : ℤ) :
    finiteTerm A B X l n ⟶ finiteTerm A B X k n :=
  ModuleCat.ofHom (LinearMap.pi fun p => LinearMap.proj (Fin.castLE (Nat.succ_le_succ h) p))

private theorem restrict_finiteRestriction {k l : ℕ} (h : k ≤ l) (n : ℤ) :
    restrict A B X l n ≫ finiteRestriction A B X h n = restrict A B X k n := rfl

/-- The tower maps drop all columns beyond the smaller cutoff. -/
noncomputable def projection {k l : ℕ} (h : k ≤ l) :
    finiteTotal A B X l ⟶ finiteTotal A B X k :=
  CochainComplex.ofHom (finiteRestriction A B X h) (fun n => by
    rw [finiteTotal_d_succ, finiteTotal_d_succ]
    apply (cancel_epi (restrict A B X l n)).mp
    rw [← Category.assoc, restrict_finiteRestriction, restrict_step, ← Category.assoc,
      restrict_step, Category.assoc, restrict_finiteRestriction])

end FiniteColumns

section AugmentedTotal

/-- Product of the nonnegative columns and column `-1` on diagonal `n`. -/
abbrev augmentedTerm (n : ℤ) : ModuleCat.{max u v w} A :=
  ModuleCat.of A (term A B X n × X.X (n + 1))

/-- Add the horizontal contribution from the augmented column to column zero
and use the vertical sign `-1` on the augmented column. -/
noncomputable def augmentedStep (n : ℤ) : augmentedTerm A B X n ⟶ augmentedTerm A B X (n + 1) :=
  ModuleCat.ofHom
    (((step A B X n).hom.comp (LinearMap.fst A _ _) +
      ((augmentation A B X).f (n + 1)).hom.comp (LinearMap.snd A _ _)).prod
      (-(X.d (n + 1) (n + 1 + 1)).hom.comp (LinearMap.snd A _ _)))

theorem augmentedStep_apply (n : ℤ) (x : augmentedTerm A B X n) :
    augmentedStep A B X n x =
      (step A B X n x.1 + (augmentation A B X).f (n + 1) x.2, -X.d (n + 1) (n + 1 + 1) x.2) :=
  rfl

private theorem augmentedStep_sq (n : ℤ) :
    augmentedStep A B X n ≫ augmentedStep A B X (n + 1) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change augmentedStep A B X (n + 1) (augmentedStep A B X n x) = 0
  rw [augmentedStep_apply, augmentedStep_apply]
  apply Prod.ext
  · change step A B X (n + 1) (step A B X n x.1 + (augmentation A B X).f (n + 1) x.2) +
      (augmentation A B X).f (n + 1 + 1) (-X.d (n + 1) (n + 1 + 1) x.2) = 0
    have hs : step A B X (n + 1) (step A B X n x.1) = 0 :=
      DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (step_sq A B X n)) x.1
    have ha : step A B X (n + 1) ((augmentation A B X).f (n + 1) x.2) =
        (augmentation A B X).f (n + 1 + 1) (X.d (n + 1) (n + 1 + 1) x.2) :=
      DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (augmentationComponent_step A B X (n + 1))) x.2
    rw [map_add, map_neg, hs, ha, zero_add, add_neg_cancel]
  · change -X.d (n + 1 + 1) (n + 1 + 1 + 1) (-X.d (n + 1) (n + 1 + 1) x.2) = 0
    rw [map_neg, neg_neg]
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (X.d_comp_d _ _ _)) x.2

noncomputable abbrev augmentedTotal : Complex.{u, v, w} A :=
  CochainComplex.of (augmentedTerm A B X) (augmentedStep A B X) (augmentedStep_sq A B X)

@[simp] theorem augmentedTotal_d_succ (n : ℤ) :
    (augmentedTotal A B X).d n (n + 1) = augmentedStep A B X n :=
  CochainComplex.of_d _ _ _

open CochainComplex.mappingCone

private noncomputable def toAugmented (n : ℤ) :
    (CochainComplex.mappingCone (augmentation A B X)).X n ⟶ augmentedTerm A B X n :=
  ModuleCat.ofHom (((snd (augmentation A B X)).v n n (add_zero n)).hom.prod
    ((fst (augmentation A B X)).1.v n (n + 1) rfl).hom)

private noncomputable def fromAugmented (n : ℤ) :
    augmentedTerm A B X n ⟶ (CochainComplex.mappingCone (augmentation A B X)).X n :=
  ModuleCat.ofHom (LinearMap.snd A _ _) ≫ (inl (augmentation A B X)).v (n + 1) n (by omega) +
    ModuleCat.ofHom (LinearMap.fst A _ _) ≫ (inr (augmentation A B X)).f n

private noncomputable def coneDegreeIso (n : ℤ) :
    (CochainComplex.mappingCone (augmentation A B X)).X n ≅ augmentedTerm A B X n where
  hom := toAugmented A B X n
  inv := fromAugmented A B X n
  hom_inv_id := by
    rw [fromAugmented, Preadditive.comp_add, ← Category.assoc, ← Category.assoc]
    change (fst (augmentation A B X)).1.v n (n + 1) rfl ≫
      (inl (augmentation A B X)).v (n + 1) n (by omega) +
      (snd (augmentation A B X)).v n n (add_zero n) ≫ (inr (augmentation A B X)).f n = _
    exact id_X (augmentation A B X) n (n + 1) rfl
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let φ := augmentation A B X
    let l := (inl φ).v (n + 1) n (by omega)
    let r := (inr φ).f n
    let π₁ := (snd φ).v n n (add_zero n)
    let π₂ := (fst φ).1.v n (n + 1) rfl
    have h₁ : π₁ (l x.2) = 0 := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
      (inl_v_snd_v φ (n + 1) n (by omega))) x.2
    have h₂ : π₁ (r x.1) = x.1 := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
      (inr_f_snd_v φ n)) x.1
    have h₃ : π₂ (l x.2) = x.2 := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
      (inl_v_fst_v φ (n + 1) n rfl)) x.2
    have h₄ : π₂ (r x.1) = 0 := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
      (inr_f_fst_v φ n (n + 1) rfl)) x.1
    apply Prod.ext
    · change π₁ (l x.2 + r x.1) = x.1
      rw [map_add, h₁, h₂, zero_add]
    · change π₂ (l x.2 + r x.1) = x.2
      rw [map_add, h₃, h₄, add_zero]

/-- The augmented product totalization is the mapping cone of the natural
augmentation, with its two canonical projections. -/
noncomputable def coneIso :
    CochainComplex.mappingCone (augmentation A B X) ≅ augmentedTotal A B X :=
  HomologicalComplex.Hom.isoOfComponents (coneDegreeIso A B X) (by
    intro n m h
    obtain rfl : m = n + 1 := h.symm
    rw [augmentedTotal_d_succ]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change augmentedStep A B X n (toAugmented A B X n x) =
      toAugmented A B X (n + 1) ((CochainComplex.mappingCone (augmentation A B X)).d n (n + 1) x)
    rw [augmentedStep_apply]
    apply Prod.ext
    · have h := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
        (d_snd_v (augmentation A B X) n (n + 1) rfl)) x
      rw [← total_d_succ]
      exact (add_comm _ _).trans h.symm
    · exact (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
        (d_fst_v (augmentation A B X) n (n + 1) (n + 1 + 1) rfl rfl)) x).symm)

end AugmentedTotal

section DeclarationTypes

set_option linter.checkUnivs false

private def declarationType {T : Sort*} (_ : T) := T

def RowIndexType := declarationType (@rowIndex)
def CellType := declarationType (@cell.{u, v, w})
def VerticalType := declarationType (@vertical.{u, v, w})
def HorizontalType := declarationType (@horizontal.{u, v, w})
def ColumnType := declarationType (@column.{u, v, w})
def ColumnStepType := declarationType (@columnStep.{u, v, w})
def BicomplexType := declarationType (@bicomplex.{u, v, w})
def AugmentationToColumnType := declarationType (@augmentationToColumn.{u, v, w})
def AugmentedColumnType := declarationType (@augmentedColumn.{u, v, w})
def AugmentedColumnStepType := declarationType (@augmentedColumnStep.{u, v, w})
def AugmentedBicomplexType := declarationType (@augmentedBicomplex.{u, v, w})
def TermType := declarationType (@term.{u, v, w})
def DiagonalVerticalType := declarationType (@diagonalVertical.{u, v, w})
def DiagonalHorizontalType := declarationType (@diagonalHorizontal.{u, v, w})
def StepType := declarationType (@step.{u, v, w})
def TotalType := declarationType (@total.{u, v, w})
def MapType := declarationType (@map.{u, v, w})
def FunctorType := declarationType (@functor.{u, v, w})
def AugmentationType := declarationType (@augmentation.{u, v, w})
def NaturalAugmentationType := declarationType (@naturalAugmentation.{u, v, w})
def FiniteTermType := declarationType (@finiteTerm.{u, v, w})
def FiniteStepType := declarationType (@finiteStep.{u, v, w})
def FiniteTotalType := declarationType (@finiteTotal.{u, v, w})
def TruncateType := declarationType (@truncate.{u, v, w})
def ProjectionType := declarationType (@projection.{u, v, w})
def AugmentedTermType := declarationType (@augmentedTerm.{u, v, w})
def AugmentedStepType := declarationType (@augmentedStep.{u, v, w})
def AugmentedTotalType := declarationType (@augmentedTotal.{u, v, w})
def ConeIsoType := declarationType (@coneIso.{u, v, w})

def RowIndexEq : Prop :=
  ∀ (n : ℤ) (p : ℕ),
    rowIndex n p = n - p

def VerticalTmul : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (X : Complex.{u, v, w} A) (p : ℕ) (q r : ℤ) (b : AmitsurAlgebrasSpec.degree A B p) (x : X.X q),
    vertical A B X p q r (b ⊗ₜ[A] x) = b ⊗ₜ[A] (X.d q r) x

def VerticalSq : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (X : Complex.{u, v, w} A) (p : ℕ) (q r s : ℤ),
    vertical A B X p q r ≫ vertical A B X p r s = 0

def HorizontalSq : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (X : Complex.{u, v, w} A) (p : ℕ) (q : ℤ),
    horizontal A B X p q ≫ horizontal A B X (p + 1) q = 0

def Commute : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (X : Complex.{u, v, w} A) (p : ℕ) (q r : ℤ),
    vertical A B X p q r ≫ horizontal A B X p r =
      horizontal A B X p q ≫ vertical A B X (p + 1) q r

def BicomplexDF : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (X : Complex.{u, v, w} A) (p : ℕ) (q : ℤ),
    ((bicomplex A B X).d p (p + 1)).f q = horizontal A B X p q

def AugmentedBicomplexXNegOne : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (X : Complex.{u, v, w} A),
    (augmentedBicomplex A B X).X (-1) = X

def AugmentedBicomplexDNegOne : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (X : Complex.{u, v, w} A),
    (augmentedBicomplex A B X).d (-1) 0 = augmentationToColumn A B X

def StepZero : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (X : Complex.{u, v, w} A) (n : ℤ) (x : term A B X n),
    step A B X n x 0 = diagonalVertical A B X n 0 (x 0)

def StepSucc : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (X : Complex.{u, v, w} A) (n : ℤ) (p : ℕ) (x : term A B X n),
    step A B X n x (p + 1) = diagonalHorizontal A B X n p (x p) +
      (-1 : ℤ) ^ (p + 1) • diagonalVertical A B X n (p + 1) (x (p + 1))

def StepSq : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (X : Complex.{u, v, w} A) (n : ℤ),
    step A B X n ≫ step A B X (n + 1) = 0

def TotalDSucc : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (X : Complex.{u, v, w} A) (n : ℤ),
    (total A B X).d n (n + 1) = step A B X n

def MapApply : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ {X Y : Complex.{u, v, w} A} (f : X ⟶ Y) (n : ℤ) (x : term A B X n) (p : ℕ),
    (map A B f).f n x p = AmitsurComplexSpec.degreeMap A B (f.f (rowIndex n p)) p (x p)

def AugmentationZero : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (X : Complex.{u, v, w} A) (n : ℤ) (x : X.X n),
    (augmentation A B X).f n x 0 = 1 ⊗ₜ[A] x

def AugmentationSucc : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (X : Complex.{u, v, w} A) (n : ℤ) (x : X.X n) (p : ℕ),
    (augmentation A B X).f n x (p + 1) = 0

def AugmentationNaturality : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ {X Y : Complex.{u, v, w} A} (f : X ⟶ Y),
    f ≫ augmentation A B Y = (augmentation A B X) ≫ map A B f

def FiniteTotalDSucc : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (X : Complex.{u, v, w} A) (k : ℕ) (n : ℤ),
    (finiteTotal A B X k).d n (n + 1) = finiteStep A B X k n

def TruncateApply : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (X : Complex.{u, v, w} A) (k : ℕ) (n : ℤ) (x : term A B X n) (p : Fin (k + 1)),
    (truncate A B X k).f n x p = x p

def TruncateSurjective : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (X : Complex.{u, v, w} A) (k : ℕ) (n : ℤ),
    Function.Surjective ((truncate A B X k).f n)

def TruncateEqZero : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (X : Complex.{u, v, w} A) (k : ℕ) (n : ℤ) (x : term A B X n),
    (truncate A B X k).f n x = 0 ↔ ∀ p ≤ k, x p = 0

def TruncateIsQuotient : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (X : Complex.{u, v, w} A) (k : ℕ),
    Nonempty (IsColimit (CokernelCofork.ofπ (truncate A B X k) (kernel.condition (truncate A B X k))))

def ProjectionApply : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (X : Complex.{u, v, w} A) {k l : ℕ} (h : k ≤ l) (n : ℤ) (x : finiteTerm A B X l n) (p : Fin (k + 1)),
    (projection A B X h).f n x p = x (Fin.castLE (Nat.succ_le_succ h) p)

def TruncateProjection : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (X : Complex.{u, v, w} A) {k l : ℕ} (h : k ≤ l),
    truncate A B X l ≫ projection A B X h = truncate A B X k

def ProjectionSurjective : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (X : Complex.{u, v, w} A) {k l : ℕ} (h : k ≤ l) (n : ℤ),
    Function.Surjective ((projection A B X h).f n)

def ProjectionId : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (X : Complex.{u, v, w} A) (k : ℕ),
    projection A B X (le_refl k) = 𝟙 _

def ProjectionComp : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (X : Complex.{u, v, w} A) {k l m : ℕ} (h : k ≤ l) (h' : l ≤ m),
    projection A B X h' ≫ projection A B X h = projection A B X (h.trans h')

def AugmentedStepApply : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (X : Complex.{u, v, w} A) (n : ℤ) (x : augmentedTerm A B X n),
    augmentedStep A B X n x =
      (step A B X n x.1 + (augmentation A B X).f (n + 1) x.2, -X.d (n + 1) (n + 1 + 1) x.2)

def AugmentedTotalDSucc : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (X : Complex.{u, v, w} A) (n : ℤ),
    (augmentedTotal A B X).d n (n + 1) = augmentedStep A B X n

def AugmentedStepZero : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (X : Complex.{u, v, w} A) (n : ℤ) (x : augmentedTerm A B X n),
    (augmentedStep A B X n x).1 0 =
      diagonalVertical A B X n 0 (x.1 0) + 1 ⊗ₜ[A] x.2

def AugmentedStepSucc : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (X : Complex.{u, v, w} A) (n : ℤ) (x : augmentedTerm A B X n) (p : ℕ),
    (augmentedStep A B X n x).1 (p + 1) = step A B X n x.1 (p + 1)

def ConeIsoHomApply : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (X : Complex.{u, v, w} A) (n : ℤ) (x : (CochainComplex.mappingCone (augmentation A B X)).X n),
    (coneIso A B X).hom.f n x =
      ((CochainComplex.mappingCone.snd (augmentation A B X)).v n n (add_zero n) x,
        (CochainComplex.mappingCone.fst (augmentation A B X)).1.v n (n + 1) rfl x)

end DeclarationTypes

end AmitsurTotalComplexSpec

namespace AmitsurTotalComplexSpec.Independent

universe u v w

open AmitsurComplexSpec (degreeMap)

section Transport

variable {V : Type*} [Category V] [HasZeroMorphisms V]
  {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex V c)
  {Y : ι → V} (e : ∀ i, K.X i ≅ Y i)

/-- Transport a differential through specified isomorphisms in each degree. -/
private abbrev transport : HomologicalComplex V c where
  X := Y
  d i j := (e i).inv ≫ K.d i j ≫ (e j).hom
  shape i j h := by rw [K.shape i j h, Limits.zero_comp, Limits.comp_zero]
  d_comp_d' i j k _ _ := by simp [Category.assoc]

private def transportIso : K ≅ transport K e :=
  HomologicalComplex.Hom.isoOfComponents e (by
    intros
    simp [transport])

@[simp] private theorem transportIso_hom_f (i : ι) :
    (transportIso K e).hom.f i = (e i).hom := rfl

@[simp] private theorem transportIso_inv_f (i : ι) :
    (transportIso K e).inv.f i = (e i).inv := rfl

end Transport

variable (A : Type u) [CommRing A]

/-- Coefficient complexes have their own carrier universe. -/
abbrev Input := CochainComplex (ModuleCat.{w} A) ℤ

/-- Move the coefficient complex to the common ambient module category. -/
def lift : Input.{u, w} A ⥤ Complex.{u, v, w} A :=
  (ModuleCat.uliftFunctor.{max u v, w} A).mapHomologicalComplex (ComplexShape.up ℤ)

variable (B : Type v) [CommRing B] [Algebra A B]
variable (X : Input.{u, w} A)


/-- The cell is the tensor product with the original coefficient module. -/
abbrev cell (p : ℕ) (q : ℤ) : ModuleCat.{max u v w} A :=
  ModuleCat.of A (AmitsurAlgebrasSpec.degree A B p ⊗[A] X.X q)

/-- Lower the right factor of the lifted cell. -/
noncomputable def cellEquiv (p : ℕ) (q : ℤ) :
    AmitsurTotalComplexSpec.cell A B ((lift.{u, v, w} A).obj X) p q ≃ₗ[A] cell A B X p q :=
  AmitsurComplexSpec.liftedDegreeEquiv A B (X.X q) p

variable {X}

noncomputable def tensorMap {M N : ModuleCat.{w} A} (f : M ⟶ N) (p : ℕ) :
    ModuleCat.of A (AmitsurAlgebrasSpec.degree A B p ⊗[A] M) ⟶
      ModuleCat.of A (AmitsurAlgebrasSpec.degree A B p ⊗[A] N) :=
  ModuleCat.ofHom (TensorProduct.map LinearMap.id f.hom)

private theorem tensorMap_transport {X Y : Input.{u, w} A} (p : ℕ) (q r : ℤ)
    (f : X.X q ⟶ Y.X r) (x : AmitsurTotalComplexSpec.cell A B ((lift.{u, v, w} A).obj X) p q) :
    tensorMap A B f p (cellEquiv A B X p q x) =
      cellEquiv A B Y p r
        (degreeMap A B ((ModuleCat.uliftFunctor.{max u v, w} A).map f) p x) := by
  let e := cellEquiv A B X p q
  let e' := cellEquiv A B Y p r
  have h : (tensorMap A B f p).hom.comp e.toLinearMap =
      e'.toLinearMap.comp
        (degreeMap A B ((ModuleCat.uliftFunctor.{max u v, w} A).map f) p).hom := by
    apply TensorProduct.ext'
    intro b m
    simp [tensorMap, degreeMap, e, e', cellEquiv, AmitsurComplexSpec.liftedDegreeEquiv]
    rfl
  exact DFunLike.congr_fun h x

variable (X)

/-- The vertical map is identity on the Amitsur tensor power. -/
noncomputable def vertical (p : ℕ) (q r : ℤ) : cell A B X p q ⟶ cell A B X p r :=
  tensorMap A B (X.d q r) p

/-- The horizontal map is the alternating sum of unit insertions. -/
noncomputable def horizontal (p : ℕ) (q : ℤ) :
    cell A B X p q ⟶ cell A B X (p + 1) q :=
  ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
    ModuleCat.ofHom (TensorProduct.map (AmitsurAlgebrasSpec.coface i).toLinearMap LinearMap.id)

private theorem horizontal_transport (p : ℕ) (q : ℤ) (x : AmitsurTotalComplexSpec.cell A B ((lift.{u, v, w} A).obj X) p q) :
    horizontal A B X p q (cellEquiv A B X p q x) =
      cellEquiv A B X (p + 1) q (AmitsurTotalComplexSpec.horizontal A B ((lift.{u, v, w} A).obj X) p q x) := by
  let e := cellEquiv A B X p q
  let e' := cellEquiv A B X (p + 1) q
  change ((horizontal A B X p q).hom.comp e.toLinearMap) x =
    (e'.toLinearMap.comp (AmitsurTotalComplexSpec.horizontal A B ((lift.{u, v, w} A).obj X) p q).hom) x
  congr 1
  apply TensorProduct.ext'
  intro b m
  simp [horizontal, AmitsurTotalComplexSpec.horizontal, AmitsurComplexSpec.differential,
    AmitsurComplexSpec.coface, e, e', cellEquiv, AmitsurComplexSpec.liftedDegreeEquiv]
  exact Finset.sum_congr rfl (fun _ _ => rfl)

/-- Inserting the unit on the original coefficient module, before any lift. -/
noncomputable def unit (q : ℤ) : X.X q →ₗ[A] cell A B X 0 q :=
  TensorProduct.mk A (AmitsurAlgebrasSpec.degree A B 0) (X.X q) 1

open private AmitsurComplexSpec.augmentation_apply from MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.AmitsurComplex

private theorem unit_transport (q : ℤ) (x : (((lift.{u, v, w} A).obj X)).X q) :
    cellEquiv A B X 0 q (AmitsurComplexSpec.augmentation A B ((((lift.{u, v, w} A).obj X)).X q) x) =
      unit A B X q (ULift.down x) := by
  rw [AmitsurComplexSpec.augmentation_apply]
  rfl

/-- The unsigned columns with the actual tensor module in every degree. -/
noncomputable abbrev column (p : ℕ) : Complex.{u, v, w} A :=
  transport (AmitsurTotalComplexSpec.column A B ((lift.{u, v, w} A).obj X) p)
    (fun q => (cellEquiv A B X p q).toModuleIso)

noncomputable def columnIso (p : ℕ) : AmitsurTotalComplexSpec.column A B ((lift.{u, v, w} A).obj X) p ≅ column A B X p :=
  transportIso _ _

theorem column_d (p : ℕ) (q r : ℤ) : (column A B X p).d q r = vertical A B X p q r := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let e := cellEquiv A B X p q
  have h := tensorMap_transport A B p q r (X.d q r) (e.symm x)
  rw [show cellEquiv A B X p _ (e.symm x) = x from e.apply_symm_apply x] at h
  exact h.symm

/-- The original cochain complex of columns, with commuting differentials. -/
noncomputable abbrev bicomplex : CochainComplex (Complex.{u, v, w} A) ℕ :=
  transport (AmitsurTotalComplexSpec.bicomplex A B ((lift.{u, v, w} A).obj X)) (columnIso A B X)

theorem bicomplex_d_f (p : ℕ) (q : ℤ) :
    ((bicomplex A B X).d p (p + 1)).f q = horizontal A B X p q := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let e := cellEquiv A B X p q
  have h := horizontal_transport A B X p q (e.symm x)
  rw [show cellEquiv A B X p _ (e.symm x) = x from e.apply_symm_apply x] at h
  have hp : ((AmitsurTotalComplexSpec.bicomplex A B ((lift.{u, v, w} A).obj X)).d p (p + 1)).f q =
      AmitsurTotalComplexSpec.horizontal A B ((lift.{u, v, w} A).obj X) p q :=
    congrArg (fun f : AmitsurTotalComplexSpec.column A B ((lift.{u, v, w} A).obj X) p ⟶
        AmitsurTotalComplexSpec.column A B ((lift.{u, v, w} A).obj X) (p + 1) => f.f q)
      (CochainComplex.of_d _ _ p)
  change cellEquiv A B X (p + 1) q
    (((AmitsurTotalComplexSpec.bicomplex A B ((lift.{u, v, w} A).obj X)).d p (p + 1)).f q (e.symm x)) = _
  rw [hp]
  exact h.symm

/-- The product along the diagonal (p+q=n). -/
abbrev term (n : ℤ) : ModuleCat.{max u v w} A :=
  ModuleCat.of A (∀ p : ℕ, cell A B X p (rowIndex n p))

noncomputable def termEquiv (n : ℤ) : AmitsurTotalComplexSpec.term A B ((lift.{u, v, w} A).obj X) n ≃ₗ[A] term A B X n :=
  LinearEquiv.piCongrRight fun p => cellEquiv A B X p (rowIndex n p)

noncomputable abbrev total : Complex.{u, v, w} A :=
  transport (AmitsurTotalComplexSpec.total A B ((lift.{u, v, w} A).obj X)) (fun n => (termEquiv A B X n).toModuleIso)

/-- The product comparison lowers each coefficient separately. -/
noncomputable def totalIso : AmitsurTotalComplexSpec.total A B ((lift.{u, v, w} A).obj X) ≅ total A B X :=
  transportIso _ _

theorem totalIso_hom_apply (n : ℤ) (x : AmitsurTotalComplexSpec.term A B ((lift.{u, v, w} A).obj X) n) (p : ℕ) :
    (totalIso A B X).hom.f n x p = cellEquiv A B X p (rowIndex n p) (x p) := rfl

noncomputable def diagonalVertical (n : ℤ) (p : ℕ) :
    cell A B X p (rowIndex n p) ⟶ cell A B X p (rowIndex (n + 1) p) :=
  vertical A B X p _ _

noncomputable def diagonalHorizontal (n : ℤ) (p : ℕ) :
    cell A B X p (rowIndex n p) ⟶ cell A B X (p + 1) (rowIndex (n + 1) (p + 1)) :=
  horizontal A B X p _ ≫ eqToHom (congrArg (cell A B X (p + 1)) (rowIndex_horizontal n p))

private theorem horizontalTo_transport (p : ℕ) {q r : ℤ} (h : q = r)
    (x : AmitsurTotalComplexSpec.cell A B ((lift.{u, v, w} A).obj X) p q) :
    (horizontal A B X p q ≫ eqToHom (congrArg (cell A B X (p + 1)) h))
        (cellEquiv A B X p q x) =
      cellEquiv A B X (p + 1) r (horizontalTo A B ((lift.{u, v, w} A).obj X) p h x) := by
  subst r
  simpa [horizontalTo] using horizontal_transport A B X p q x

theorem total_d_zero (n : ℤ) (x : term A B X n) :
    (total A B X).d n (n + 1) x 0 = diagonalVertical A B X n 0 (x 0) := by
  let y := (termEquiv A B X n).symm x
  change cellEquiv A B X 0 (n + 1) ((AmitsurTotalComplexSpec.total A B ((lift.{u, v, w} A).obj X)).d n (n + 1) y 0) = _
  rw [AmitsurTotalComplexSpec.total_d_succ, AmitsurTotalComplexSpec.step_zero]
  have h := tensorMap_transport A B 0 n (n + 1) (X.d n (n + 1)) (y 0)
  rw [show cellEquiv A B X 0 n (y 0) = x 0 from
    (cellEquiv A B X 0 n).apply_symm_apply (x 0)] at h
  exact h.symm

theorem total_d_succ (n : ℤ) (x : term A B X n) (p : ℕ) :
    (total A B X).d n (n + 1) x (p + 1) =
      diagonalHorizontal A B X n p (x p) +
      (-1 : ℤ) ^ (p + 1) • diagonalVertical A B X n (p + 1) (x (p + 1)) := by
  let y := (termEquiv A B X n).symm x
  change cellEquiv A B X (p + 1) (rowIndex (n + 1) (p + 1))
    ((AmitsurTotalComplexSpec.total A B ((lift.{u, v, w} A).obj X)).d n (n + 1) y (p + 1)) = _
  rw [AmitsurTotalComplexSpec.total_d_succ, AmitsurTotalComplexSpec.step_succ, map_add, map_zsmul]
  have hx (p : ℕ) : cellEquiv A B X p (rowIndex n p) (y p) = x p :=
    (cellEquiv A B X p (rowIndex n p)).apply_symm_apply (x p)
  have hh := horizontalTo_transport A B X p (rowIndex_horizontal n p) (y p)
  have hv := tensorMap_transport A B (p + 1) (rowIndex n (p + 1))
    (rowIndex (n + 1) (p + 1)) (X.d _ _) (y (p + 1))
  rw [hx] at hh hv
  exact congrArg₂ (· + ·) hh.symm (congrArg ((-1 : ℤ) ^ (p + 1) • ·) hv.symm)


section Functoriality

variable {X} {Y : Input.{u, w} A}

/-- On each coordinate this is tensoring the original cochain map. -/
noncomputable def map (f : X ⟶ Y) : total A B X ⟶ total A B Y :=
  (totalIso A B X).inv ≫ AmitsurTotalComplexSpec.map A B ((lift.{u, v, w} A).map f) ≫
    (totalIso A B Y).hom

theorem map_apply (f : X ⟶ Y) (n : ℤ) (x : term A B X n) (p : ℕ) :
    (map A B f).f n x p = tensorMap A B (f.f (rowIndex n p)) p (x p) := by
  let y := (termEquiv A B X n).symm x
  change cellEquiv A B Y p (rowIndex n p)
    ((AmitsurTotalComplexSpec.map A B ((lift.{u, v, w} A).map f)).f n y p) = _
  rw [AmitsurTotalComplexSpec.map_apply]
  have h := tensorMap_transport A B p _ _ (f.f (rowIndex n p)) (y p)
  rw [show cellEquiv A B X p (rowIndex n p) (y p) = x p from
    (cellEquiv A B X p (rowIndex n p)).apply_symm_apply (x p)] at h
  exact h.symm

/-- The totalization functor on the original category of coefficient complexes. -/
noncomputable def functor : Input.{u, w} A ⥤ Complex.{u, v, w} A where
  obj := total A B
  map := map A B
  map_id X := by
    have h : AmitsurTotalComplexSpec.map A B ((lift.{u, v, w} A).map (𝟙 X)) = 𝟙 _ :=
      (lift.{u, v, w} A ⋙ AmitsurTotalComplexSpec.functor A B).map_id X
    simp only [map, h, Category.id_comp, Iso.inv_hom_id]
  map_comp f g := by
    have h : AmitsurTotalComplexSpec.map A B ((lift.{u, v, w} A).map (f ≫ g)) =
        AmitsurTotalComplexSpec.map A B ((lift.{u, v, w} A).map f) ≫
        AmitsurTotalComplexSpec.map A B ((lift.{u, v, w} A).map g) :=
      (lift.{u, v, w} A ⋙ AmitsurTotalComplexSpec.functor A B).map_comp f g
    simp only [map, h, Category.assoc, Iso.hom_inv_id_assoc]

end Functoriality

/-- The natural comparison with totalization after lifting the input. -/
noncomputable def totalNatIso :
    lift.{u, v, w} A ⋙ AmitsurTotalComplexSpec.functor A B ≅ functor A B :=
  NatIso.ofComponents (totalIso A B) fun f => by
    change AmitsurTotalComplexSpec.map A B ((lift.{u, v, w} A).map f) ≫ (totalIso A B _).hom =
      (totalIso A B _).hom ≫ map A B f
    simp [map]

/-- The augmented cochain map in the common ambient module category. -/
noncomputable def naturalAugmentation : lift.{u, v, w} A ⟶ functor A B :=
  Functor.whiskerLeft (lift.{u, v, w} A) (AmitsurTotalComplexSpec.naturalAugmentation A B) ≫
    (totalNatIso A B).hom

noncomputable def augmentation : ((lift.{u, v, w} A).obj X) ⟶ total A B X :=
  (naturalAugmentation A B).app X

theorem augmentation_comparison :
    augmentation A B X = AmitsurTotalComplexSpec.augmentation A B ((lift.{u, v, w} A).obj X) ≫
      (totalIso A B X).hom := rfl

private theorem augmentation_lifted_zero (n : ℤ) (x : (((lift.{u, v, w} A).obj X)).X n) :
    (augmentation A B X).f n x 0 = unit A B X n (ULift.down x) := by
  rw [augmentation_comparison]
  change cellEquiv A B X 0 n
    (AmitsurTotalComplexSpec.augmentationComponent A B ((lift.{u, v, w} A).obj X) n x 0) = _
  rw [AmitsurTotalComplexSpec.augmentationComponent_zero]
  exact unit_transport A B X n x

private theorem augmentation_lifted_succ (n : ℤ) (x : (((lift.{u, v, w} A).obj X)).X n) (p : ℕ) :
    (augmentation A B X).f n x (p + 1) = 0 := by
  rw [augmentation_comparison]
  change cellEquiv A B X (p + 1) (rowIndex n (p + 1))
    (AmitsurTotalComplexSpec.augmentationComponent A B ((lift.{u, v, w} A).obj X) n x (p + 1)) = _
  rw [AmitsurTotalComplexSpec.augmentationComponent_succ, map_zero]

/-- The augmentation evaluated on an element of the original coefficient module. -/
noncomputable def augmentationComponent (n : ℤ) : X.X n →ₗ[A] term A B X n :=
  ((augmentation A B X).f n).hom.comp ULift.moduleEquiv.symm.toLinearMap

theorem augmentation_zero (n : ℤ) (x : X.X n) :
    augmentationComponent A B X n x 0 = 1 ⊗ₜ[A] x :=
  augmentation_lifted_zero A B X n (ULift.up x)

theorem augmentation_succ (n : ℤ) (x : X.X n) (p : ℕ) :
    augmentationComponent A B X n x (p + 1) = 0 :=
  augmentation_lifted_succ A B X n (ULift.up x) p

theorem augmentationComponent_comm (q r : ℤ) (x : X.X q) :
    (total A B X).d q r (augmentationComponent A B X q x) =
      augmentationComponent A B X r (X.d q r x) :=
  DFunLike.congr_fun (congrArg ModuleCat.Hom.hom ((augmentation A B X).comm q r)) (ULift.up x)

theorem augmentationComponent_naturality {X Y : Input.{u, w} A} (f : X ⟶ Y)
    (n : ℤ) (x : X.X n) :
    augmentationComponent A B Y n (f.f n x) =
      (map A B f).f n (augmentationComponent A B X n x) := by
  have h := (naturalAugmentation A B).naturality f
  exact DFunLike.congr_fun (congrArg (fun g => (g.f n).hom) h)
    (show ((lift.{u, v, w} A).obj X).X n from ULift.up x)

section FiniteColumns

abbrev finiteTerm (k : ℕ) (n : ℤ) : ModuleCat.{max u v w} A :=
  ModuleCat.of A (∀ p : Fin (k + 1), cell A B X p (rowIndex n p))

private noncomputable def finiteTermEquiv (k : ℕ) (n : ℤ) :
    AmitsurTotalComplexSpec.finiteTerm A B ((lift.{u, v, w} A).obj X) k n ≃ₗ[A] finiteTerm A B X k n :=
  LinearEquiv.piCongrRight fun p => cellEquiv A B X p (rowIndex n p)

noncomputable abbrev finiteTotal (k : ℕ) : Complex.{u, v, w} A :=
  transport (AmitsurTotalComplexSpec.finiteTotal A B ((lift.{u, v, w} A).obj X) k)
    (fun n => (finiteTermEquiv A B X k n).toModuleIso)

noncomputable def finiteTotalIso (k : ℕ) :
    AmitsurTotalComplexSpec.finiteTotal A B ((lift.{u, v, w} A).obj X) k ≅ finiteTotal A B X k :=
  transportIso _ _

theorem finiteTotalIso_hom_apply (k : ℕ) (n : ℤ)
    (x : AmitsurTotalComplexSpec.finiteTerm A B ((lift.{u, v, w} A).obj X) k n) (p : Fin (k + 1)) :
    (finiteTotalIso A B X k).hom.f n x p = cellEquiv A B X p (rowIndex n p) (x p) := rfl

noncomputable def truncate (k : ℕ) : total A B X ⟶ finiteTotal A B X k :=
  (totalIso A B X).inv ≫ AmitsurTotalComplexSpec.truncate A B ((lift.{u, v, w} A).obj X) k ≫
    (finiteTotalIso A B X k).hom

theorem truncate_comparison (k : ℕ) :
    (totalIso A B X).hom ≫ truncate A B X k =
      AmitsurTotalComplexSpec.truncate A B ((lift.{u, v, w} A).obj X) k ≫ (finiteTotalIso A B X k).hom := by
  simp [truncate]

@[simp] theorem truncate_apply (k : ℕ) (n : ℤ) (x : term A B X n) (p : Fin (k + 1)) :
    (truncate A B X k).f n x p = x p :=
  (cellEquiv A B X p (rowIndex n p)).apply_symm_apply (x p)

noncomputable def projection {k l : ℕ} (h : k ≤ l) :
    finiteTotal A B X l ⟶ finiteTotal A B X k :=
  (finiteTotalIso A B X l).inv ≫ AmitsurTotalComplexSpec.projection A B ((lift.{u, v, w} A).obj X) h ≫
    (finiteTotalIso A B X k).hom

theorem projection_comparison {k l : ℕ} (h : k ≤ l) :
    (finiteTotalIso A B X l).hom ≫ projection A B X h =
      AmitsurTotalComplexSpec.projection A B ((lift.{u, v, w} A).obj X) h ≫ (finiteTotalIso A B X k).hom := by
  simp [projection]

@[simp] theorem projection_apply {k l : ℕ} (h : k ≤ l) (n : ℤ)
    (x : finiteTerm A B X l n) (p : Fin (k + 1)) :
    (projection A B X h).f n x p = x (Fin.castLE (Nat.succ_le_succ h) p) :=
  (cellEquiv A B X p (rowIndex n p)).apply_symm_apply _

theorem truncate_projection {k l : ℕ} (h : k ≤ l) :
    truncate A B X l ≫ projection A B X h = truncate A B X k := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext p
  change (projection A B X h).f n ((truncate A B X l).f n x) p = _
  rw [projection_apply, truncate_apply, truncate_apply]
  rfl

theorem projection_id (k : ℕ) : projection A B X (le_refl k) = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext p
  exact projection_apply A B X (le_refl k) n x p

theorem projection_comp {k l m : ℕ} (h : k ≤ l) (h' : l ≤ m) :
    projection A B X h' ≫ projection A B X h = projection A B X (h.trans h') := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext p
  change (projection A B X h).f n ((projection A B X h').f n x) p = _
  rw [projection_apply, projection_apply, projection_apply]
  rfl

theorem truncate_surjective (k : ℕ) (n : ℤ) :
    Function.Surjective ((truncate A B X k).f n) := by
  intro x
  refine ⟨fun p => if h : p < k + 1 then x ⟨p, h⟩ else 0, ?_⟩
  funext p
  rw [truncate_apply, dite_eq_left p.isLt]

theorem projection_surjective {k l : ℕ} (h : k ≤ l) (n : ℤ) :
    Function.Surjective ((projection A B X h).f n) := by
  intro x
  obtain ⟨y, hy⟩ := truncate_surjective A B X k n x
  refine ⟨(truncate A B X l).f n y, ?_⟩
  exact (congrArg (fun f : total A B X ⟶ finiteTotal A B X k => f.f n y)
    (truncate_projection A B X h)).trans hy

theorem truncate_eq_zero (k : ℕ) (n : ℤ) (x : term A B X n) :
    (truncate A B X k).f n x = 0 ↔ ∀ p ≤ k, x p = 0 := by
  constructor
  · intro h p hp
    exact (truncate_apply A B X k n x ⟨p, Nat.lt_succ_of_le hp⟩).symm.trans
      (congrFun h ⟨p, Nat.lt_succ_of_le hp⟩)
  · intro h
    funext p
    exact (truncate_apply A B X k n x p).trans (h p (Nat.le_of_lt_succ p.isLt))

theorem truncate_is_quotient (k : ℕ) :
    Nonempty (IsColimit (CokernelCofork.ofπ (truncate A B X k) (kernel.condition (truncate A B X k)))) := by
  let f := truncate A B X k
  have : Epi f := HomologicalComplex.epi_of_epi_f f
    (fun n => (ModuleCat.epi_iff_surjective (f.f n)).mpr (truncate_surjective A B X k n))
  exact ⟨Abelian.epiIsCokernelOfKernel _ (limit.isLimit (parallelPair f 0))⟩

end FiniteColumns

section Augmented

/-- The map from column `-1` into column zero, carried by unit insertion. -/
noncomputable def augmentationToColumn :
    ((lift.{u, v, w} A).obj X) ⟶ column A B X 0 :=
  AmitsurTotalComplexSpec.augmentationToColumn A B ((lift.{u, v, w} A).obj X) ≫
    (columnIso A B X 0).hom

theorem augmentationToColumn_apply (q : ℤ) (x : X.X q) :
    (augmentationToColumn A B X).f q (ULift.up x) = 1 ⊗ₜ[A] x :=
  unit_transport A B X q (ULift.up x)

noncomputable def augmentedColumn : ℤ → Complex.{u, v, w} A
  | .ofNat p => column A B X p
  | .negSucc 0 => (lift.{u, v, w} A).obj X
  | .negSucc (_ + 1) => 0

private noncomputable def augmentedColumnIso (p : ℤ) :
    (AmitsurTotalComplexSpec.augmentedBicomplex A B ((lift.{u, v, w} A).obj X)).X p ≅
      augmentedColumn A B X p := by
  cases p with
  | ofNat p => exact columnIso A B X p
  | negSucc p => cases p <;> exact Iso.refl _

noncomputable abbrev augmentedBicomplex : CochainComplex (Complex.{u, v, w} A) ℤ :=
  transport (AmitsurTotalComplexSpec.augmentedBicomplex A B ((lift.{u, v, w} A).obj X))
    (augmentedColumnIso A B X)

theorem augmentedBicomplex_X_neg_one :
    (augmentedBicomplex A B X).X (-1) = (lift.{u, v, w} A).obj X := rfl

theorem augmentedBicomplex_d_neg_one :
    (augmentedBicomplex A B X).d (-1) 0 = augmentationToColumn A B X := by
  change (𝟙 _) ≫ (AmitsurTotalComplexSpec.augmentedBicomplex A B
    ((lift.{u, v, w} A).obj X)).d (-1) 0 ≫ (columnIso A B X 0).hom = _
  rw [Category.id_comp]
  exact congrArg (fun f : _ ⟶ _ => f ≫ (columnIso A B X 0).hom)
    (CochainComplex.of_d (AmitsurTotalComplexSpec.augmentedColumn A B ((lift.{u, v, w} A).obj X))
      (AmitsurTotalComplexSpec.augmentedColumnStep A B ((lift.{u, v, w} A).obj X)) (-1))

theorem augmentedBicomplex_d_ofNat (p : ℕ) :
    (augmentedBicomplex A B X).d (p : ℤ) (↑p + 1) = (bicomplex A B X).d p (p + 1) := by
  change (columnIso A B X p).inv ≫
    (AmitsurTotalComplexSpec.augmentedBicomplex A B ((lift.{u, v, w} A).obj X)).d
      (p : ℤ) (↑p + 1) ≫ (columnIso A B X (p + 1)).hom =
    (columnIso A B X p).inv ≫
      (AmitsurTotalComplexSpec.bicomplex A B ((lift.{u, v, w} A).obj X)).d
        p (p + 1) ≫ (columnIso A B X (p + 1)).hom
  have h : (AmitsurTotalComplexSpec.augmentedBicomplex A B ((lift.{u, v, w} A).obj X)).d
      (p : ℤ) (↑p + 1) = AmitsurTotalComplexSpec.columnStep A B ((lift.{u, v, w} A).obj X) p :=
    CochainComplex.of_d _ _ (p : ℤ)
  have h' : (AmitsurTotalComplexSpec.bicomplex A B ((lift.{u, v, w} A).obj X)).d
      p (p + 1) = AmitsurTotalComplexSpec.columnStep A B ((lift.{u, v, w} A).obj X) p :=
    CochainComplex.of_d _ _ p
  exact congrArg (fun f : _ ⟶ _ => (columnIso A B X p).inv ≫ f ≫ (columnIso A B X (p + 1)).hom)
    (h.trans h'.symm)

/-- The augmented diagonal has the original module in column `-1`. -/
abbrev augmentedTerm (n : ℤ) : ModuleCat.{max u v w} A :=
  ModuleCat.of A (term A B X n × X.X (n + 1))

private noncomputable def augmentedTermEquiv (n : ℤ) :
    AmitsurTotalComplexSpec.augmentedTerm A B ((lift.{u, v, w} A).obj X) n ≃ₗ[A]
      augmentedTerm A B X n :=
  (termEquiv A B X n).prodCongr ULift.moduleEquiv

noncomputable abbrev augmentedTotal : Complex.{u, v, w} A :=
  transport (AmitsurTotalComplexSpec.augmentedTotal A B ((lift.{u, v, w} A).obj X))
    (fun n => (augmentedTermEquiv A B X n).toModuleIso)

noncomputable def augmentedTotalIso :
    AmitsurTotalComplexSpec.augmentedTotal A B ((lift.{u, v, w} A).obj X) ≅ augmentedTotal A B X :=
  transportIso _ _

theorem augmentedTotalIso_hom_apply (n : ℤ)
    (x : AmitsurTotalComplexSpec.augmentedTerm A B ((lift.{u, v, w} A).obj X) n) :
    (augmentedTotalIso A B X).hom.f n x = (termEquiv A B X n x.1, ULift.down x.2) := rfl

theorem augmentedTotal_d (n : ℤ) (x : augmentedTerm A B X n) :
    (augmentedTotal A B X).d n (n + 1) x =
      ((total A B X).d n (n + 1) x.1 + augmentationComponent A B X (n + 1) x.2,
        -X.d (n + 1) (n + 1 + 1) x.2) := by
  let L := (lift.{u, v, w} A).obj X
  let y := (termEquiv A B X n).symm x.1
  let z : L.X (n + 1) := ULift.up x.2
  change augmentedTermEquiv A B X (n + 1)
    ((AmitsurTotalComplexSpec.augmentedTotal A B L).d n (n + 1) (y, z)) = _
  rw [AmitsurTotalComplexSpec.augmentedTotal_d_succ, AmitsurTotalComplexSpec.augmentedStep_apply]
  apply Prod.ext
  · change termEquiv A B X (n + 1)
      (AmitsurTotalComplexSpec.step A B L n y + (AmitsurTotalComplexSpec.augmentation A B L).f (n + 1) z)
      = _
    rw [map_add, ← AmitsurTotalComplexSpec.total_d_succ]
    rfl
  · rfl

private noncomputable def coneComparison :
    CochainComplex.mappingCone (AmitsurTotalComplexSpec.augmentation A B ((lift.{u, v, w} A).obj X)) ≅
      CochainComplex.mappingCone (augmentation A B X) :=
  HomologicalComplex.homotopyCofiber.mapArrowIso _ _ (fun j => ⟨j - 1, by change j - 1 + 1 = j; omega⟩)
    (Arrow.isoMk (Iso.refl _) (totalIso A B X)
      (by
        change 𝟙 _ ≫ augmentation A B X = _
        rw [Category.id_comp]
        exact augmentation_comparison A B X))

/-- The augmented signed product model is the cone of the natural augmentation. -/
noncomputable def coneIso : CochainComplex.mappingCone (augmentation A B X) ≅ augmentedTotal A B X :=
  (coneComparison A B X).symm ≪≫
    AmitsurTotalComplexSpec.coneIso A B ((lift.{u, v, w} A).obj X) ≪≫ augmentedTotalIso A B X

end Augmented


section CoordinateLemmas

theorem vertical_tmul (p : ℕ) (q r : ℤ) (b : AmitsurAlgebrasSpec.degree A B p) (x : X.X q) :
    vertical A B X p q r (b ⊗ₜ[A] x) = b ⊗ₜ[A] X.d q r x :=
  rfl

theorem horizontal_tmul (p : ℕ) (q : ℤ) (b : AmitsurAlgebrasSpec.degree A B p) (x : X.X q) :
    horizontal A B X p q (b ⊗ₜ[A] x) =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
        ((AmitsurAlgebrasSpec.coface i) b ⊗ₜ[A] x) := by
  simp [horizontal]

theorem vertical_sq (p : ℕ) (q r s : ℤ) :
    vertical A B X p q r ≫ vertical A B X p r s = 0 := by
  rw [← column_d, ← column_d, HomologicalComplex.d_comp_d]

theorem horizontal_sq (p : ℕ) (q : ℤ) :
    horizontal A B X p q ≫ horizontal A B X (p + 1) q = 0 := by
  have h := (bicomplex A B X).d_comp_d p (p + 1) (p + 1 + 1)
  have h' := congrArg (fun f => f.f q) h
  change ((bicomplex A B X).d p (p + 1)).f q ≫
    ((bicomplex A B X).d (p + 1) (p + 1 + 1)).f q = 0 at h'
  rwa [bicomplex_d_f, bicomplex_d_f] at h'

theorem commute (p : ℕ) (q r : ℤ) :
    vertical A B X p q r ≫ horizontal A B X p r =
      horizontal A B X p q ≫ vertical A B X (p + 1) q r := by
  have h := ((bicomplex A B X).d p (p + 1)).comm q r
  change ((bicomplex A B X).d p (p + 1)).f q ≫ (column A B X (p + 1)).d q r =
    (column A B X p).d q r ≫ ((bicomplex A B X).d p (p + 1)).f r at h
  rw [bicomplex_d_f, bicomplex_d_f, column_d, column_d] at h
  exact h.symm

theorem finiteTotal_d_restrict (k : ℕ) (n : ℤ) (x : term A B X n) (p : Fin (k + 1)) :
    (finiteTotal A B X k).d n (n + 1) ((truncate A B X k).f n x) p =
      (total A B X).d n (n + 1) x p := by
  have h := (truncate A B X k).comm n (n + 1)
  have hx := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) x
  exact (congrFun hx p).trans (truncate_apply A B X k (n + 1) ((total A B X).d n (n + 1) x) p)

theorem augmentedTotal_d_zero (n : ℤ) (x : augmentedTerm A B X n) :
    ((augmentedTotal A B X).d n (n + 1) x).1 0 =
      diagonalVertical A B X n 0 (x.1 0) + 1 ⊗ₜ[A] x.2 := by
  rw [augmentedTotal_d]
  change (total A B X).d n (n + 1) x.1 0 + augmentationComponent A B X (n + 1) x.2 0 = _
  rw [total_d_zero, augmentation_zero]

theorem augmentedTotal_d_succ (n : ℤ) (x : augmentedTerm A B X n) (p : ℕ) :
    ((augmentedTotal A B X).d n (n + 1) x).1 (p + 1) =
      (total A B X).d n (n + 1) x.1 (p + 1) := by
  rw [augmentedTotal_d]
  change (total A B X).d n (n + 1) x.1 (p + 1) +
    augmentationComponent A B X (n + 1) x.2 (p + 1) = _
  rw [augmentation_succ, add_zero]

theorem augmentedBicomplex_X_ofNat (p : ℕ) :
    (augmentedBicomplex A B X).X (p : ℤ) = (bicomplex A B X).X p := rfl

theorem augmentedBicomplex_X_of_lt (p : ℤ) (h : p < -1) :
    (augmentedBicomplex A B X).X p = 0 := by
  cases p with
  | ofNat p =>
    change (p : ℤ) < -1 at h
    omega
  | negSucc p => cases p with
    | zero => omega
    | succ p => rfl

end CoordinateLemmas

section IndependentDeclarationTypes

set_option linter.checkUnivs false

private def declarationType {T : Sort*} (_ : T) := T

def InputType := declarationType (@Input.{u, w})
def LiftType :=
  ∀ (A : Type u) [CommRing A], Input.{u, w} A ⥤ Complex.{u, v, w} A
def CellType := declarationType (@cell.{u, v, w})
def CellEquivType := declarationType (@cellEquiv.{u, v, w})
def TensorMapType := declarationType (@tensorMap.{u, v, w})
def VerticalType := declarationType (@vertical.{u, v, w})
def HorizontalType := declarationType (@horizontal.{u, v, w})
def UnitType := declarationType (@unit.{u, v, w})
def ColumnType := declarationType (@column.{u, v, w})
def ColumnIsoType := declarationType (@columnIso.{u, v, w})
def BicomplexType := declarationType (@bicomplex.{u, v, w})
def TermType := declarationType (@term.{u, v, w})
def TermEquivType := declarationType (@termEquiv.{u, v, w})
def TotalType := declarationType (@total.{u, v, w})
def TotalIsoType := declarationType (@totalIso.{u, v, w})
def DiagonalVerticalType := declarationType (@diagonalVertical.{u, v, w})
def DiagonalHorizontalType := declarationType (@diagonalHorizontal.{u, v, w})
def MapType := declarationType (@map.{u, v, w})
def FunctorType := declarationType (@functor.{u, v, w})
def TotalNatIsoType := declarationType (@totalNatIso.{u, v, w})
def NaturalAugmentationType := declarationType (@naturalAugmentation.{u, v, w})
def AugmentationType := declarationType (@augmentation.{u, v, w})
def AugmentationComponentType := declarationType (@augmentationComponent.{u, v, w})
def FiniteTermType := declarationType (@finiteTerm.{u, v, w})
def FiniteTotalType := declarationType (@finiteTotal.{u, v, w})
def FiniteTotalIsoType := declarationType (@finiteTotalIso.{u, v, w})
def TruncateType := declarationType (@truncate.{u, v, w})
def ProjectionType := declarationType (@projection.{u, v, w})
def AugmentationToColumnType := declarationType (@augmentationToColumn.{u, v, w})
def AugmentedColumnType := declarationType (@augmentedColumn.{u, v, w})
def AugmentedBicomplexType := declarationType (@augmentedBicomplex.{u, v, w})
def AugmentedTermType := declarationType (@augmentedTerm.{u, v, w})
def AugmentedTotalType := declarationType (@augmentedTotal.{u, v, w})
def AugmentedTotalIsoType := declarationType (@augmentedTotalIso.{u, v, w})
def ConeIsoType := declarationType (@coneIso.{u, v, w})

def ColumnD : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A) (p : ℕ) (q r : ℤ),
    (column A B X p).d q r = vertical A B X p q r

def BicomplexDF : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A) (p : ℕ) (q : ℤ),
    ((bicomplex A B X).d p (p + 1)).f q = horizontal A B X p q

def TotalIsoHomApply : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A) (n : ℤ) (x : AmitsurTotalComplexSpec.term A B ((lift.{u, v, w} A).obj X) n) (p : ℕ),
    (totalIso A B X).hom.f n x p = cellEquiv A B X p (rowIndex n p) (x p)

def TotalDZero : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A) (n : ℤ) (x : term A B X n),
    (total A B X).d n (n + 1) x 0 = diagonalVertical A B X n 0 (x 0)

def TotalDSucc : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A) (n : ℤ) (x : term A B X n) (p : ℕ),
    (total A B X).d n (n + 1) x (p + 1) =
        diagonalHorizontal A B X n p (x p) +
        (-1 : ℤ) ^ (p + 1) • diagonalVertical A B X n (p + 1) (x (p + 1))

def MapApply : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ {X Y : Input.{u, w} A} (f : X ⟶ Y) (n : ℤ) (x : term A B X n) (p : ℕ),
    (map A B f).f n x p = tensorMap A B (f.f (rowIndex n p)) p (x p)

def AugmentationComparison : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A),
    augmentation A B X = AmitsurTotalComplexSpec.augmentation A B ((lift.{u, v, w} A).obj X) ≫
        (totalIso A B X).hom

def AugmentationZero : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A) (n : ℤ) (x : X.X n),
    augmentationComponent A B X n x 0 = 1 ⊗ₜ[A] x

def AugmentationSucc : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A) (n : ℤ) (x : X.X n) (p : ℕ),
    augmentationComponent A B X n x (p + 1) = 0

def AugmentationComponentComm : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A) (q r : ℤ) (x : X.X q),
    (total A B X).d q r (augmentationComponent A B X q x) =
        augmentationComponent A B X r (X.d q r x)

def AugmentationComponentNaturality : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ {X Y : Input.{u, w} A} (f : X ⟶ Y)
      (n : ℤ) (x : X.X n),
    augmentationComponent A B Y n (f.f n x) =
        (map A B f).f n (augmentationComponent A B X n x)

def FiniteTotalIsoHomApply : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A) (k : ℕ) (n : ℤ)
      (x : AmitsurTotalComplexSpec.finiteTerm A B ((lift.{u, v, w} A).obj X) k n) (p : Fin (k + 1)),
    (finiteTotalIso A B X k).hom.f n x p = cellEquiv A B X p (rowIndex n p) (x p)

def TruncateComparison : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A) (k : ℕ),
    (totalIso A B X).hom ≫ truncate A B X k =
        AmitsurTotalComplexSpec.truncate A B ((lift.{u, v, w} A).obj X) k ≫ (finiteTotalIso A B X k).hom

def TruncateApply : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A) (k : ℕ) (n : ℤ) (x : term A B X n) (p : Fin (k + 1)),
    (truncate A B X k).f n x p = x p

def ProjectionComparison : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A) {k l : ℕ} (h : k ≤ l),
    (finiteTotalIso A B X l).hom ≫ projection A B X h =
        AmitsurTotalComplexSpec.projection A B ((lift.{u, v, w} A).obj X) h ≫ (finiteTotalIso A B X k).hom

def ProjectionApply : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A),
    ∀ {k l : ℕ} (h : k ≤ l) (n : ℤ)
      (x : finiteTerm A B X l n) (p : Fin (k + 1)),
    (projection A B X h).f n x p = x (Fin.castLE (Nat.succ_le_succ h) p)

def TruncateProjection : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A) {k l : ℕ} (h : k ≤ l),
    truncate A B X l ≫ projection A B X h = truncate A B X k

def ProjectionId : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A) (k : ℕ),
    projection A B X (le_refl k) = 𝟙 _

def ProjectionComp : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A) {k l m : ℕ} (h : k ≤ l) (h' : l ≤ m),
    projection A B X h' ≫ projection A B X h = projection A B X (h.trans h')

def TruncateSurjective : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A) (k : ℕ) (n : ℤ),
    Function.Surjective ((truncate A B X k).f n)

def ProjectionSurjective : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A) {k l : ℕ} (h : k ≤ l) (n : ℤ),
    Function.Surjective ((projection A B X h).f n)

def TruncateEqZero : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A) (k : ℕ) (n : ℤ) (x : term A B X n),
    (truncate A B X k).f n x = 0 ↔ ∀ p ≤ k, x p = 0

def TruncateIsQuotient : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A) (k : ℕ),
    Nonempty (IsColimit (CokernelCofork.ofπ (truncate A B X k) (kernel.condition (truncate A B X k))))

def AugmentationToColumnApply : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A) (q : ℤ) (x : X.X q),
    (augmentationToColumn A B X).f q (ULift.up x) = 1 ⊗ₜ[A] x

def AugmentedBicomplexXNegOne : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A),
    (augmentedBicomplex A B X).X (-1) = (lift.{u, v, w} A).obj X

def AugmentedBicomplexDNegOne : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A),
    (augmentedBicomplex A B X).d (-1) 0 = augmentationToColumn A B X

def AugmentedBicomplexDOfNat : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A) (p : ℕ),
    (augmentedBicomplex A B X).d (p : ℤ) (↑p + 1) = (bicomplex A B X).d p (p + 1)

def AugmentedTotalIsoHomApply : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A) (n : ℤ)
      (x : AmitsurTotalComplexSpec.augmentedTerm A B ((lift.{u, v, w} A).obj X) n),
    (augmentedTotalIso A B X).hom.f n x = (termEquiv A B X n x.1, ULift.down x.2)

def AugmentedTotalD : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A) (n : ℤ) (x : augmentedTerm A B X n),
    (augmentedTotal A B X).d n (n + 1) x =
        ((total A B X).d n (n + 1) x.1 + augmentationComponent A B X (n + 1) x.2,
          -X.d (n + 1) (n + 1 + 1) x.2)

def VerticalTmul : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A) (p : ℕ) (q r : ℤ) (b : AmitsurAlgebrasSpec.degree A B p) (x : X.X q),
    vertical A B X p q r (b ⊗ₜ[A] x) = b ⊗ₜ[A] X.d q r x

def HorizontalTmul : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A) (p : ℕ) (q : ℤ) (b : AmitsurAlgebrasSpec.degree A B p) (x : X.X q),
    horizontal A B X p q (b ⊗ₜ[A] x) =
        ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
          ((AmitsurAlgebrasSpec.coface i) b ⊗ₜ[A] x)

def VerticalSq : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A) (p : ℕ) (q r s : ℤ),
    vertical A B X p q r ≫ vertical A B X p r s = 0

def HorizontalSq : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A) (p : ℕ) (q : ℤ),
    horizontal A B X p q ≫ horizontal A B X (p + 1) q = 0

def Commute : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A) (p : ℕ) (q r : ℤ),
    vertical A B X p q r ≫ horizontal A B X p r =
        horizontal A B X p q ≫ vertical A B X (p + 1) q r

def FiniteTotalDRestrict : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A) (k : ℕ) (n : ℤ) (x : term A B X n) (p : Fin (k + 1)),
    (finiteTotal A B X k).d n (n + 1) ((truncate A B X k).f n x) p =
        (total A B X).d n (n + 1) x p

def AugmentedTotalDZero : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A) (n : ℤ) (x : augmentedTerm A B X n),
    ((augmentedTotal A B X).d n (n + 1) x).1 0 =
        diagonalVertical A B X n 0 (x.1 0) + 1 ⊗ₜ[A] x.2

def AugmentedTotalDSucc : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A) (n : ℤ) (x : augmentedTerm A B X n) (p : ℕ),
    ((augmentedTotal A B X).d n (n + 1) x).1 (p + 1) =
        (total A B X).d n (n + 1) x.1 (p + 1)

def AugmentedBicomplexXOfNat : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A) (p : ℕ),
    (augmentedBicomplex A B X).X (p : ℤ) = (bicomplex A B X).X p

def AugmentedBicomplexXOfLt : Prop :=
    ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
    ∀ (X : Input.{u, w} A) (p : ℤ) (_h : p < -1),
    (augmentedBicomplex A B X).X p = 0

end IndependentDeclarationTypes

end AmitsurTotalComplexSpec.Independent
