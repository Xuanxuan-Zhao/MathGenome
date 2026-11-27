import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.AmitsurComplex
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.AmitsurTotalComplex

/-! The Amitsur bicomplex, its signed product totalization, and its column quotients. -/

open CategoryTheory Limits
open scoped TensorProduct

namespace DerivedFormalization.Descent.AmitsurTotalComplex

universe u v w

set_option linter.checkUnivs false in
abbrev Complex := @AmitsurTotalComplexSpec.Complex.{u, v, w}

abbrev rowIndex := @AmitsurTotalComplexSpec.rowIndex
abbrev cell (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (X : Complex.{u, v, w} A) (p : ℕ) (q : ℤ) :=
  AmitsurComplex.Degree A B (X.X q) p
noncomputable def vertical (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (X : Complex.{u, v, w} A) (p : ℕ) (q r : ℤ) :
    cell A B X p q ⟶ cell A B X p r :=
  AmitsurComplex.degreeMap A B (X.d q r) p
noncomputable def horizontal (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (X : Complex.{u, v, w} A) (p : ℕ) (q : ℤ) :
    cell A B X p q ⟶ cell A B X (p + 1) q :=
  AmitsurComplex.differential A B (X.X q) p
noncomputable abbrev column := @AmitsurTotalComplexSpec.column.{u, v, w}
noncomputable abbrev columnStep := @AmitsurTotalComplexSpec.columnStep.{u, v, w}
noncomputable abbrev bicomplex := @AmitsurTotalComplexSpec.bicomplex.{u, v, w}
noncomputable abbrev augmentationToColumn := @AmitsurTotalComplexSpec.augmentationToColumn.{u, v, w}
noncomputable abbrev augmentedColumn := @AmitsurTotalComplexSpec.augmentedColumn.{u, v, w}
noncomputable abbrev augmentedColumnStep := @AmitsurTotalComplexSpec.augmentedColumnStep.{u, v, w}
noncomputable abbrev augmentedBicomplex := @AmitsurTotalComplexSpec.augmentedBicomplex.{u, v, w}
abbrev term := @AmitsurTotalComplexSpec.term.{u, v, w}
noncomputable abbrev diagonalVertical := @AmitsurTotalComplexSpec.diagonalVertical.{u, v, w}
noncomputable abbrev diagonalHorizontal := @AmitsurTotalComplexSpec.diagonalHorizontal.{u, v, w}
noncomputable abbrev step := @AmitsurTotalComplexSpec.step.{u, v, w}
noncomputable abbrev total := @AmitsurTotalComplexSpec.total.{u, v, w}
noncomputable abbrev map := @AmitsurTotalComplexSpec.map.{u, v, w}
noncomputable abbrev functor := @AmitsurTotalComplexSpec.functor.{u, v, w}
noncomputable abbrev augmentation := @AmitsurTotalComplexSpec.augmentation.{u, v, w}
noncomputable abbrev naturalAugmentation := @AmitsurTotalComplexSpec.naturalAugmentation.{u, v, w}
abbrev finiteTerm := @AmitsurTotalComplexSpec.finiteTerm.{u, v, w}
noncomputable abbrev finiteStep := @AmitsurTotalComplexSpec.finiteStep.{u, v, w}
noncomputable abbrev finiteTotal := @AmitsurTotalComplexSpec.finiteTotal.{u, v, w}
noncomputable abbrev truncate := @AmitsurTotalComplexSpec.truncate.{u, v, w}
noncomputable abbrev projection := @AmitsurTotalComplexSpec.projection.{u, v, w}
abbrev augmentedTerm := @AmitsurTotalComplexSpec.augmentedTerm.{u, v, w}
noncomputable abbrev augmentedStep := @AmitsurTotalComplexSpec.augmentedStep.{u, v, w}
noncomputable abbrev augmentedTotal := @AmitsurTotalComplexSpec.augmentedTotal.{u, v, w}
noncomputable abbrev coneIso := @AmitsurTotalComplexSpec.coneIso.{u, v, w}

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]

theorem rowIndex_eq (n : ℤ) (p : ℕ) :
  rowIndex n p = n - p :=
  AmitsurTotalComplexSpec.rowIndex_eq n p

theorem vertical_tmul (X : Complex.{u, v, w} A) (p : ℕ) (q r : ℤ) (b : AmitsurAlgebrasSpec.degree A B p) (x : X.X q) :
  vertical A B X p q r (b ⊗ₜ[A] x) = b ⊗ₜ[A] (X.d q r) x :=
  AmitsurComplex.degreeMap_tmul A B (X.d q r) p b x

theorem vertical_sq (X : Complex.{u, v, w} A) (p : ℕ) (q r s : ℤ) :
  vertical A B X p q r ≫ vertical A B X p r s = 0 :=
  AmitsurTotalComplexSpec.vertical_sq A B X p q r s

theorem horizontal_sq (X : Complex.{u, v, w} A) (p : ℕ) (q : ℤ) :
  horizontal A B X p q ≫ horizontal A B X (p + 1) q = 0 :=
  AmitsurComplex.differential_sq A B (X.X q) p

theorem commute (X : Complex.{u, v, w} A) (p : ℕ) (q r : ℤ) :
  vertical A B X p q r ≫ horizontal A B X p r =
    horizontal A B X p q ≫ vertical A B X (p + 1) q r :=
  AmitsurComplex.degreeMap_differential A B (X.d q r) p

theorem bicomplex_d_f (X : Complex.{u, v, w} A) (p : ℕ) (q : ℤ) :
  ((bicomplex A B X).d p (p + 1)).f q = horizontal A B X p q := by
  exact congrArg (fun f : column A B X p ⟶ column A B X (p + 1) => f.f q)
    (CochainComplex.of_d (column A B X) (columnStep A B X) p)

@[simp] theorem augmentedBicomplex_X_neg_one (X : Complex.{u, v, w} A) :
  (augmentedBicomplex A B X).X (-1) = X :=
  rfl

@[simp] theorem augmentedBicomplex_d_neg_one (X : Complex.{u, v, w} A) :
  (augmentedBicomplex A B X).d (-1) 0 = augmentationToColumn A B X :=
  CochainComplex.of_d (augmentedColumn A B X) (augmentedColumnStep A B X) (-1)

@[simp] theorem step_zero (X : Complex.{u, v, w} A) (n : ℤ) (x : term A B X n) :
  step A B X n x 0 = diagonalVertical A B X n 0 (x 0) :=
  AmitsurTotalComplexSpec.step_zero A B X n x

@[simp] theorem step_succ (X : Complex.{u, v, w} A) (n : ℤ) (p : ℕ) (x : term A B X n) :
  step A B X n x (p + 1) = diagonalHorizontal A B X n p (x p) +
    (-1 : ℤ) ^ (p + 1) • diagonalVertical A B X n (p + 1) (x (p + 1)) :=
  AmitsurTotalComplexSpec.step_succ A B X n p x

theorem step_sq (X : Complex.{u, v, w} A) (n : ℤ) :
  step A B X n ≫ step A B X (n + 1) = 0 :=
  AmitsurTotalComplexSpec.step_sq A B X n

@[simp] theorem total_d_succ (X : Complex.{u, v, w} A) (n : ℤ) :
  (total A B X).d n (n + 1) = step A B X n :=
  AmitsurTotalComplexSpec.total_d_succ A B X n

theorem map_apply {X Y : Complex.{u, v, w} A} (f : X ⟶ Y) (n : ℤ) (x : term A B X n) (p : ℕ) :
  (map A B f).f n x p = AmitsurComplex.degreeMap A B (f.f (rowIndex n p)) p (x p) :=
  AmitsurTotalComplexSpec.map_apply A B f n x p

@[simp] theorem augmentation_zero (X : Complex.{u, v, w} A) (n : ℤ) (x : X.X n) :
  (augmentation A B X).f n x 0 = 1 ⊗ₜ[A] x :=
  AmitsurComplex.augmentation_apply A B (X.X n) x

@[simp] theorem augmentation_succ (X : Complex.{u, v, w} A) (n : ℤ) (x : X.X n) (p : ℕ) :
  (augmentation A B X).f n x (p + 1) = 0 :=
  rfl

theorem augmentation_naturality {X Y : Complex.{u, v, w} A} (f : X ⟶ Y) :
  f ≫ augmentation A B Y = (augmentation A B X) ≫ map A B f :=
  (naturalAugmentation A B).naturality f

@[simp] theorem finiteTotal_d_succ (X : Complex.{u, v, w} A) (k : ℕ) (n : ℤ) :
  (finiteTotal A B X k).d n (n + 1) = finiteStep A B X k n :=
  AmitsurTotalComplexSpec.finiteTotal_d_succ A B X k n

@[simp] theorem truncate_apply (X : Complex.{u, v, w} A) (k : ℕ) (n : ℤ) (x : term A B X n) (p : Fin (k + 1)) :
  (truncate A B X k).f n x p = x p :=
  rfl

theorem truncate_surjective (X : Complex.{u, v, w} A) (k : ℕ) (n : ℤ) :
  Function.Surjective ((truncate A B X k).f n) := by
  intro x
  refine ⟨fun p => if h : p < k + 1 then x ⟨p, h⟩ else 0, ?_⟩
  funext p
  change (if h : (p : ℕ) < k + 1 then x ⟨p, h⟩ else 0) = x p
  rw [dite_eq_left p.isLt]

theorem truncate_eq_zero (X : Complex.{u, v, w} A) (k : ℕ) (n : ℤ) (x : term A B X n) :
  (truncate A B X k).f n x = 0 ↔ ∀ p ≤ k, x p = 0 := by
  constructor
  · intro h p hp
    exact congrFun h ⟨p, by omega⟩
  · intro h
    funext p
    exact h p (Nat.le_of_lt_succ p.isLt)

theorem truncate_is_quotient (X : Complex.{u, v, w} A) (k : ℕ) :
  Nonempty (IsColimit (CokernelCofork.ofπ (truncate A B X k) (kernel.condition (truncate A B X k)))) := by
  let f := truncate A B X k
  have : Epi f := HomologicalComplex.epi_of_epi_f f
    (fun n => (ModuleCat.epi_iff_surjective (f.f n)).mpr (truncate_surjective A B X k n))
  exact ⟨Abelian.epiIsCokernelOfKernel _ (limit.isLimit (parallelPair f 0))⟩

@[simp] theorem projection_apply (X : Complex.{u, v, w} A) {k l : ℕ} (h : k ≤ l) (n : ℤ) (x : finiteTerm A B X l n) (p : Fin (k + 1)) :
  (projection A B X h).f n x p = x (Fin.castLE (Nat.succ_le_succ h) p) :=
  rfl

theorem truncate_projection (X : Complex.{u, v, w} A) {k l : ℕ} (h : k ≤ l) :
  truncate A B X l ≫ projection A B X h = truncate A B X k :=
  HomologicalComplex.hom_ext _ _ (fun _ => rfl)

theorem projection_surjective (X : Complex.{u, v, w} A) {k l : ℕ} (h : k ≤ l) (n : ℤ) :
  Function.Surjective ((projection A B X h).f n) := by
  intro x
  obtain ⟨y, hy⟩ := truncate_surjective A B X k n x
  refine ⟨(truncate A B X l).f n y, ?_⟩
  exact (congrArg (fun f : total A B X ⟶ finiteTotal A B X k => f.f n y)
    (truncate_projection A B X h)).trans hy

theorem projection_id (X : Complex.{u, v, w} A) (k : ℕ) :
  projection A B X (le_refl k) = 𝟙 _ :=
  rfl

theorem projection_comp (X : Complex.{u, v, w} A) {k l m : ℕ} (h : k ≤ l) (h' : l ≤ m) :
  projection A B X h' ≫ projection A B X h = projection A B X (h.trans h') :=
  rfl

theorem augmentedStep_apply (X : Complex.{u, v, w} A) (n : ℤ) (x : augmentedTerm A B X n) :
  augmentedStep A B X n x =
    (step A B X n x.1 + (augmentation A B X).f (n + 1) x.2, -X.d (n + 1) (n + 1 + 1) x.2) :=
  AmitsurTotalComplexSpec.augmentedStep_apply A B X n x

@[simp] theorem augmentedTotal_d_succ (X : Complex.{u, v, w} A) (n : ℤ) :
  (augmentedTotal A B X).d n (n + 1) = augmentedStep A B X n :=
  AmitsurTotalComplexSpec.augmentedTotal_d_succ A B X n

theorem augmentedStep_zero (X : Complex.{u, v, w} A) (n : ℤ) (x : augmentedTerm A B X n) :
  (augmentedStep A B X n x).1 0 =
    diagonalVertical A B X n 0 (x.1 0) + 1 ⊗ₜ[A] x.2 := by
  rw [augmentedStep_apply]
  change step A B X n x.1 0 + (augmentation A B X).f (n + 1) x.2 0 = _
  rw [step_zero, augmentation_zero]

theorem augmentedStep_succ (X : Complex.{u, v, w} A) (n : ℤ) (x : augmentedTerm A B X n) (p : ℕ) :
  (augmentedStep A B X n x).1 (p + 1) = step A B X n x.1 (p + 1) := by
  rw [augmentedStep_apply]
  change step A B X n x.1 (p + 1) + (augmentation A B X).f (n + 1) x.2 (p + 1) = _
  rw [augmentation_succ, add_zero]

theorem coneIso_hom_apply (X : Complex.{u, v, w} A) (n : ℤ) (x : (CochainComplex.mappingCone (augmentation A B X)).X n) :
  (coneIso A B X).hom.f n x =
    ((CochainComplex.mappingCone.snd (augmentation A B X)).v n n (add_zero n) x,
      (CochainComplex.mappingCone.fst (augmentation A B X)).1.v n (n + 1) rfl x) :=
  rfl

end DerivedFormalization.Descent.AmitsurTotalComplex

namespace DerivedFormalization.Descent.AmitsurTotalComplex.Independent

open scoped ZeroObject

universe u v w

abbrev Input := @AmitsurTotalComplexSpec.Independent.Input.{u, w}
def lift : ∀ (A : Type u) [CommRing A], Input.{u, w} A ⥤ Complex.{u, v, w} A :=
  fun A _ => (ModuleCat.uliftFunctor.{max u v, w} A).mapHomologicalComplex (ComplexShape.up ℤ)
abbrev cell := @AmitsurTotalComplexSpec.Independent.cell.{u, v, w}
noncomputable abbrev cellEquiv := @AmitsurTotalComplexSpec.Independent.cellEquiv.{u, v, w}
noncomputable abbrev tensorMap := @AmitsurTotalComplexSpec.Independent.tensorMap.{u, v, w}
noncomputable abbrev vertical := @AmitsurTotalComplexSpec.Independent.vertical.{u, v, w}
noncomputable abbrev horizontal := @AmitsurTotalComplexSpec.Independent.horizontal.{u, v, w}
noncomputable abbrev unit := @AmitsurTotalComplexSpec.Independent.unit.{u, v, w}
noncomputable abbrev column := @AmitsurTotalComplexSpec.Independent.column.{u, v, w}
noncomputable abbrev columnIso := @AmitsurTotalComplexSpec.Independent.columnIso.{u, v, w}
noncomputable abbrev bicomplex := @AmitsurTotalComplexSpec.Independent.bicomplex.{u, v, w}
abbrev term := @AmitsurTotalComplexSpec.Independent.term.{u, v, w}
noncomputable abbrev termEquiv := @AmitsurTotalComplexSpec.Independent.termEquiv.{u, v, w}
noncomputable abbrev total := @AmitsurTotalComplexSpec.Independent.total.{u, v, w}
noncomputable abbrev totalIso := @AmitsurTotalComplexSpec.Independent.totalIso.{u, v, w}
noncomputable abbrev diagonalVertical := @AmitsurTotalComplexSpec.Independent.diagonalVertical.{u, v, w}
noncomputable abbrev diagonalHorizontal := @AmitsurTotalComplexSpec.Independent.diagonalHorizontal.{u, v, w}
noncomputable abbrev map := @AmitsurTotalComplexSpec.Independent.map.{u, v, w}
noncomputable abbrev functor := @AmitsurTotalComplexSpec.Independent.functor.{u, v, w}
noncomputable abbrev totalNatIso := @AmitsurTotalComplexSpec.Independent.totalNatIso.{u, v, w}
noncomputable abbrev naturalAugmentation := @AmitsurTotalComplexSpec.Independent.naturalAugmentation.{u, v, w}
noncomputable abbrev augmentation := @AmitsurTotalComplexSpec.Independent.augmentation.{u, v, w}
noncomputable abbrev augmentationComponent := @AmitsurTotalComplexSpec.Independent.augmentationComponent.{u, v, w}
abbrev finiteTerm := @AmitsurTotalComplexSpec.Independent.finiteTerm.{u, v, w}
noncomputable abbrev finiteTotal := @AmitsurTotalComplexSpec.Independent.finiteTotal.{u, v, w}
noncomputable abbrev finiteTotalIso := @AmitsurTotalComplexSpec.Independent.finiteTotalIso.{u, v, w}
noncomputable abbrev truncate := @AmitsurTotalComplexSpec.Independent.truncate.{u, v, w}
noncomputable abbrev projection := @AmitsurTotalComplexSpec.Independent.projection.{u, v, w}
noncomputable abbrev augmentationToColumn := @AmitsurTotalComplexSpec.Independent.augmentationToColumn.{u, v, w}
noncomputable abbrev augmentedColumn := @AmitsurTotalComplexSpec.Independent.augmentedColumn.{u, v, w}
noncomputable abbrev augmentedBicomplex := @AmitsurTotalComplexSpec.Independent.augmentedBicomplex.{u, v, w}
abbrev augmentedTerm := @AmitsurTotalComplexSpec.Independent.augmentedTerm.{u, v, w}
noncomputable abbrev augmentedTotal := @AmitsurTotalComplexSpec.Independent.augmentedTotal.{u, v, w}
noncomputable abbrev augmentedTotalIso := @AmitsurTotalComplexSpec.Independent.augmentedTotalIso.{u, v, w}
noncomputable abbrev coneIso := @AmitsurTotalComplexSpec.Independent.coneIso.{u, v, w}

theorem column_d :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A) (p : ℕ) (q r : ℤ),
  (column A B X p).d q r = vertical A B X p q r :=
  @AmitsurTotalComplexSpec.Independent.column_d

theorem bicomplex_d_f :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A) (p : ℕ) (q : ℤ),
  ((bicomplex A B X).d p (p + 1)).f q = horizontal A B X p q :=
  @AmitsurTotalComplexSpec.Independent.bicomplex_d_f

theorem totalIso_hom_apply :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A) (n : ℤ) (x : AmitsurTotalComplexSpec.term A B ((lift.{u, v, w} A).obj X) n) (p : ℕ),
  (totalIso A B X).hom.f n x p = cellEquiv A B X p (rowIndex n p) (x p) :=
  @AmitsurTotalComplexSpec.Independent.totalIso_hom_apply

theorem total_d_zero :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A) (n : ℤ) (x : term A B X n),
  (total A B X).d n (n + 1) x 0 = diagonalVertical A B X n 0 (x 0) :=
  @AmitsurTotalComplexSpec.Independent.total_d_zero

theorem total_d_succ :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A) (n : ℤ) (x : term A B X n) (p : ℕ),
  (total A B X).d n (n + 1) x (p + 1) =
      diagonalHorizontal A B X n p (x p) +
      (-1 : ℤ) ^ (p + 1) • diagonalVertical A B X n (p + 1) (x (p + 1)) :=
  @AmitsurTotalComplexSpec.Independent.total_d_succ

theorem map_apply :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ {X Y : Input.{u, w} A} (f : X ⟶ Y) (n : ℤ) (x : term A B X n) (p : ℕ),
  (map A B f).f n x p = tensorMap A B (f.f (rowIndex n p)) p (x p) :=
  @AmitsurTotalComplexSpec.Independent.map_apply

theorem augmentation_comparison :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A),
  augmentation A B X = AmitsurTotalComplexSpec.augmentation A B ((lift.{u, v, w} A).obj X) ≫
      (totalIso A B X).hom :=
  @AmitsurTotalComplexSpec.Independent.augmentation_comparison

theorem augmentation_zero :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A) (n : ℤ) (x : X.X n),
  augmentationComponent A B X n x 0 = 1 ⊗ₜ[A] x :=
  @AmitsurTotalComplexSpec.Independent.augmentation_zero

theorem augmentation_succ :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A) (n : ℤ) (x : X.X n) (p : ℕ),
  augmentationComponent A B X n x (p + 1) = 0 :=
  @AmitsurTotalComplexSpec.Independent.augmentation_succ

theorem augmentationComponent_comm :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A) (q r : ℤ) (x : X.X q),
  (total A B X).d q r (augmentationComponent A B X q x) =
      augmentationComponent A B X r (X.d q r x) :=
  @AmitsurTotalComplexSpec.Independent.augmentationComponent_comm

theorem augmentationComponent_naturality :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ {X Y : Input.{u, w} A} (f : X ⟶ Y)
    (n : ℤ) (x : X.X n),
  augmentationComponent A B Y n (f.f n x) =
      (map A B f).f n (augmentationComponent A B X n x) :=
  @AmitsurTotalComplexSpec.Independent.augmentationComponent_naturality

theorem finiteTotalIso_hom_apply :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A) (k : ℕ) (n : ℤ)
    (x : AmitsurTotalComplexSpec.finiteTerm A B ((lift.{u, v, w} A).obj X) k n) (p : Fin (k + 1)),
  (finiteTotalIso A B X k).hom.f n x p = cellEquiv A B X p (rowIndex n p) (x p) :=
  @AmitsurTotalComplexSpec.Independent.finiteTotalIso_hom_apply

theorem truncate_comparison :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A) (k : ℕ),
  (totalIso A B X).hom ≫ truncate A B X k =
      AmitsurTotalComplexSpec.truncate A B ((lift.{u, v, w} A).obj X) k ≫ (finiteTotalIso A B X k).hom :=
  @AmitsurTotalComplexSpec.Independent.truncate_comparison

@[simp] theorem truncate_apply :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A) (k : ℕ) (n : ℤ) (x : term A B X n) (p : Fin (k + 1)),
  (truncate A B X k).f n x p = x p :=
  @AmitsurTotalComplexSpec.Independent.truncate_apply

theorem projection_comparison :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A) {k l : ℕ} (h : k ≤ l),
  (finiteTotalIso A B X l).hom ≫ projection A B X h =
      AmitsurTotalComplexSpec.projection A B ((lift.{u, v, w} A).obj X) h ≫ (finiteTotalIso A B X k).hom :=
  @AmitsurTotalComplexSpec.Independent.projection_comparison

@[simp] theorem projection_apply :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A),
  ∀ {k l : ℕ} (h : k ≤ l) (n : ℤ)
    (x : finiteTerm A B X l n) (p : Fin (k + 1)),
  (projection A B X h).f n x p = x (Fin.castLE (Nat.succ_le_succ h) p) :=
  @AmitsurTotalComplexSpec.Independent.projection_apply

theorem truncate_projection :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A) {k l : ℕ} (h : k ≤ l),
  truncate A B X l ≫ projection A B X h = truncate A B X k :=
  @AmitsurTotalComplexSpec.Independent.truncate_projection

theorem projection_id :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A) (k : ℕ),
  projection A B X (le_refl k) = 𝟙 _ :=
  @AmitsurTotalComplexSpec.Independent.projection_id

theorem projection_comp :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A) {k l m : ℕ} (h : k ≤ l) (h' : l ≤ m),
  projection A B X h' ≫ projection A B X h = projection A B X (h.trans h') :=
  @AmitsurTotalComplexSpec.Independent.projection_comp

theorem truncate_surjective :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A) (k : ℕ) (n : ℤ),
  Function.Surjective ((truncate A B X k).f n) :=
  @AmitsurTotalComplexSpec.Independent.truncate_surjective

theorem projection_surjective :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A) {k l : ℕ} (h : k ≤ l) (n : ℤ),
  Function.Surjective ((projection A B X h).f n) :=
  @AmitsurTotalComplexSpec.Independent.projection_surjective

theorem truncate_eq_zero :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A) (k : ℕ) (n : ℤ) (x : term A B X n),
  (truncate A B X k).f n x = 0 ↔ ∀ p ≤ k, x p = 0 :=
  @AmitsurTotalComplexSpec.Independent.truncate_eq_zero

theorem truncate_is_quotient :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A) (k : ℕ),
  Nonempty (IsColimit (CokernelCofork.ofπ (truncate A B X k) (kernel.condition (truncate A B X k)))) :=
  @AmitsurTotalComplexSpec.Independent.truncate_is_quotient

theorem augmentationToColumn_apply :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A) (q : ℤ) (x : X.X q),
  (augmentationToColumn A B X).f q (ULift.up x) = 1 ⊗ₜ[A] x :=
  @AmitsurTotalComplexSpec.Independent.augmentationToColumn_apply

theorem augmentedBicomplex_X_neg_one :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A),
  (augmentedBicomplex A B X).X (-1) = (lift.{u, v, w} A).obj X :=
  @AmitsurTotalComplexSpec.Independent.augmentedBicomplex_X_neg_one

theorem augmentedBicomplex_d_neg_one :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A),
  (augmentedBicomplex A B X).d (-1) 0 = augmentationToColumn A B X :=
  @AmitsurTotalComplexSpec.Independent.augmentedBicomplex_d_neg_one

theorem augmentedBicomplex_d_ofNat :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A) (p : ℕ),
  (augmentedBicomplex A B X).d (p : ℤ) (↑p + 1) = (bicomplex A B X).d p (p + 1) :=
  @AmitsurTotalComplexSpec.Independent.augmentedBicomplex_d_ofNat

theorem augmentedTotalIso_hom_apply :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A) (n : ℤ)
    (x : AmitsurTotalComplexSpec.augmentedTerm A B ((lift.{u, v, w} A).obj X) n),
  (augmentedTotalIso A B X).hom.f n x = (termEquiv A B X n x.1, ULift.down x.2) :=
  @AmitsurTotalComplexSpec.Independent.augmentedTotalIso_hom_apply

theorem augmentedTotal_d :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A) (n : ℤ) (x : augmentedTerm A B X n),
  (augmentedTotal A B X).d n (n + 1) x =
      ((total A B X).d n (n + 1) x.1 + augmentationComponent A B X (n + 1) x.2,
        -X.d (n + 1) (n + 1 + 1) x.2) :=
  @AmitsurTotalComplexSpec.Independent.augmentedTotal_d

theorem vertical_tmul :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A) (p : ℕ) (q r : ℤ) (b : AmitsurAlgebrasSpec.degree A B p) (x : X.X q),
  vertical A B X p q r (b ⊗ₜ[A] x) = b ⊗ₜ[A] X.d q r x :=
  @AmitsurTotalComplexSpec.Independent.vertical_tmul

theorem horizontal_tmul :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A) (p : ℕ) (q : ℤ) (b : AmitsurAlgebrasSpec.degree A B p) (x : X.X q),
  horizontal A B X p q (b ⊗ₜ[A] x) =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
        ((AmitsurAlgebrasSpec.coface i) b ⊗ₜ[A] x) :=
  @AmitsurTotalComplexSpec.Independent.horizontal_tmul

theorem vertical_sq :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A) (p : ℕ) (q r s : ℤ),
  vertical A B X p q r ≫ vertical A B X p r s = 0 :=
  @AmitsurTotalComplexSpec.Independent.vertical_sq

theorem horizontal_sq :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A) (p : ℕ) (q : ℤ),
  horizontal A B X p q ≫ horizontal A B X (p + 1) q = 0 :=
  @AmitsurTotalComplexSpec.Independent.horizontal_sq

theorem commute :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A) (p : ℕ) (q r : ℤ),
  vertical A B X p q r ≫ horizontal A B X p r =
      horizontal A B X p q ≫ vertical A B X (p + 1) q r :=
  @AmitsurTotalComplexSpec.Independent.commute

theorem finiteTotal_d_restrict :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A) (k : ℕ) (n : ℤ) (x : term A B X n) (p : Fin (k + 1)),
  (finiteTotal A B X k).d n (n + 1) ((truncate A B X k).f n x) p =
      (total A B X).d n (n + 1) x p :=
  @AmitsurTotalComplexSpec.Independent.finiteTotal_d_restrict

theorem augmentedTotal_d_zero :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A) (n : ℤ) (x : augmentedTerm A B X n),
  ((augmentedTotal A B X).d n (n + 1) x).1 0 =
      diagonalVertical A B X n 0 (x.1 0) + 1 ⊗ₜ[A] x.2 :=
  @AmitsurTotalComplexSpec.Independent.augmentedTotal_d_zero

theorem augmentedTotal_d_succ :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A) (n : ℤ) (x : augmentedTerm A B X n) (p : ℕ),
  ((augmentedTotal A B X).d n (n + 1) x).1 (p + 1) =
      (total A B X).d n (n + 1) x.1 (p + 1) :=
  @AmitsurTotalComplexSpec.Independent.augmentedTotal_d_succ

theorem augmentedBicomplex_X_ofNat :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A) (p : ℕ),
  (augmentedBicomplex A B X).X (p : ℤ) = (bicomplex A B X).X p :=
  @AmitsurTotalComplexSpec.Independent.augmentedBicomplex_X_ofNat

theorem augmentedBicomplex_X_of_lt :
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B],
  ∀ (X : Input.{u, w} A) (p : ℤ) (_h : p < -1),
  (augmentedBicomplex A B X).X p = 0 :=
  @AmitsurTotalComplexSpec.Independent.augmentedBicomplex_X_of_lt

end DerivedFormalization.Descent.AmitsurTotalComplex.Independent
