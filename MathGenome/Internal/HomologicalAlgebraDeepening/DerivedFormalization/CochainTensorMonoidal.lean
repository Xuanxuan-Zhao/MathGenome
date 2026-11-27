import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainModels
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainTensorMonoidal

/-! The symmetric monoidal structures on cochains and their homotopy category. -/

namespace DerivedFormalization

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
open HomologicalComplex (ιTensorObj mapBifunctorDesc ι_mapBifunctorDesc)

universe u w w'

variable {R : Type u} [CommRing R]

noncomputable section

private abbrev shape := ComplexShape.up ℤ

/-- The image of a homogeneous pure tensor in the direct-sum totalization. -/
abbrev cochainTmul (X Y : Comp.{u} R) (i j : ℤ) {n : ℤ} (h : i + j = n)
    (x : X.X i) (y : Y.X j) : (tensorComplex X Y).X n :=
  ιTensorObj X Y i j n h (x ⊗ₜ[R] y)

/-- The unit is the stalk of the base ring in degree zero. -/
abbrev cochainTensorUnit (R : Type u) [CommRing R] : Comp.{u} R :=
  (stalk R).obj (ModuleCat.of R R)

/-- The degree-zero term of the tensor unit, identified with the base ring. -/
abbrev cochainTensorUnitZero (R : Type u) [CommRing R] :
    (cochainTensorUnit R).X 0 ≅ ModuleCat.of R R :=
  HomologicalComplex.singleObjXSelf shape 0 _

private lemma map_sign {M N : ModuleCat.{u} R} (f : M ⟶ N) (s : ℤˣ) (x : M) :
    f (s • x) = s • f x := by
  change f.hom (s • x) = s • f.hom x
  simp only [Units.smul_def, map_zsmul]

private lemma sign_apply {M N : ModuleCat.{u} R} (f : M ⟶ N) (s : ℤˣ) (x : M) :
    (s • f) x = s • f x := rfl

private lemma map_add_apply {M N : ModuleCat.{u} R} (f : M ⟶ N) (x y : M) :
    f (x + y) = f x + f y := map_add f.hom x y

private lemma tmul_sign_left (X Y : Comp.{u} R) (i j : ℤ) {n : ℤ} (h : i + j = n)
    (s : ℤˣ) (x : X.X i) (y : Y.X j) :
    cochainTmul X Y i j h (s • x) y = s • cochainTmul X Y i j h x y := by
  simp only [cochainTmul]
  rw [show (s • x) ⊗ₜ[R] y = s • (x ⊗ₜ[R] y) from (TensorProduct.smul_tmul' s x y).symm]
  exact map_sign _ _ _

private lemma tmul_sign_right (X Y : Comp.{u} R) (i j : ℤ) {n : ℤ} (h : i + j = n)
    (s : ℤˣ) (x : X.X i) (y : Y.X j) :
    cochainTmul X Y i j h x (s • y) = s • cochainTmul X Y i j h x y := by
  simp only [cochainTmul]
  rw [show x ⊗ₜ[R] (s • y) = (s • x) ⊗ₜ[R] y from (TensorProduct.smul_tmul s x y).symm]
  exact tmul_sign_left X Y i j h s x y

private lemma tensor_term_ext {X Y : Comp.{u} R} {n : ℤ} {M : ModuleCat.{u} R}
    {f g : (tensorComplex X Y).X n ⟶ M}
    (e : ∀ (i j : ℤ) (h : i + j = n) (x : X.X i) (y : Y.X j),
      f (cochainTmul X Y i j h x y) = g (cochainTmul X Y i j h x y)) :
    f = g := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  apply ModuleCat.hom_ext
  exact TensorProduct.ext' (e i j h)

private def cochainSwapComponent (X Y : Comp.{u} R) (n : ℤ) :
    (tensorComplex X Y).X n ⟶ (tensorComplex Y X).X n :=
  mapBifunctorDesc (fun i j (h : i + j = n) =>
    (i * j).negOnePow • ((β_ (X.X i) (Y.X j)).hom ≫
      ιTensorObj Y X j i n (by omega)))

private lemma cochainSwapComponent_apply (X Y : Comp.{u} R) (i j : ℤ) {n : ℤ}
    (h : i + j = n) (x : X.X i) (y : Y.X j) :
    cochainSwapComponent X Y n (cochainTmul X Y i j h x y) =
      (i * j).negOnePow • cochainTmul Y X j i (by omega : j + i = n) y x := by
  have e := ι_mapBifunctorDesc (K₁ := X) (K₂ := Y) (F := curriedTensor (ModuleCat R))
    (c := shape) (j := n) (fun p q (hq : p + q = n) =>
      (p * q).negOnePow • ((β_ (X.X p) (Y.X q)).hom ≫
        ιTensorObj Y X q p n (by omega))) i j h
  have he := ConcreteCategory.congr_hom e (x ⊗ₜ[R] y)
  simp only [ModuleCat.comp_apply, sign_apply] at he
  have hbraid : (β_ (X.X i) (Y.X j)).hom (x ⊗ₜ[R] y) = y ⊗ₜ[R] x := rfl
  rw [hbraid] at he
  exact he

private def cochainSwap (X Y : Comp.{u} R) : tensorComplex X Y ⟶ tensorComplex Y X where
  f := cochainSwapComponent X Y
  comm' n m (hnm : n + 1 = m) := by
    apply tensor_term_ext
    intro i j h x y
    simp only [ModuleCat.comp_apply, cochainSwapComponent_apply, map_sign, cochainTmul,
      tensor_d_apply i j n m h hnm, tensor_d_apply j i n m (by omega) hnm, map_add_apply,
      cochainSwapComponent_apply, map_sign, smul_add, smul_smul]
    rw [add_comm, add_mul, mul_add, one_mul, mul_one, Int.negOnePow_add, Int.negOnePow_add]
    rw [mul_left_comm i.negOnePow (i * j).negOnePow, Int.units_mul_self, mul_one]

private lemma cochainSwap_involutive (X Y : Comp.{u} R) :
    cochainSwap X Y ≫ cochainSwap Y X = 𝟙 (tensorComplex X Y) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply tensor_term_ext
  intro i j h x y
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.comp_apply,
    ModuleCat.id_apply, cochainSwap, cochainSwapComponent_apply, map_sign, smul_smul]
  rw [mul_comm j i, Int.units_mul_self, one_smul]

/-- Koszul symmetry of the direct-sum tensor of unbounded cochain complexes. -/
def cochainTensorBraiding (X Y : Comp.{u} R) : tensorComplex X Y ≅ tensorComplex Y X where
  hom := cochainSwap X Y
  inv := cochainSwap Y X
  hom_inv_id := cochainSwap_involutive X Y
  inv_hom_id := cochainSwap_involutive Y X

@[simp]
theorem cochainTensorBraiding_apply (X Y : Comp.{u} R) (i j : ℤ) {n : ℤ}
    (h : i + j = n) (x : X.X i) (y : Y.X j) :
    (cochainTensorBraiding X Y).hom.f n (cochainTmul X Y i j h x y) =
      (i * j).negOnePow • cochainTmul Y X j i (by omega : j + i = n) y x :=
  cochainSwapComponent_apply X Y i j h x y

private lemma tensorMap_tmul {X X' Y Y' : Comp.{u} R} (f : X ⟶ X') (g : Y ⟶ Y')
    (i j : ℤ) {n : ℤ} (h : i + j = n) (x : X.X i) (y : Y.X j) :
    (tensorMap f g).f n (cochainTmul X Y i j h x y) =
      cochainTmul X' Y' i j h (f.f i x) (g.f j y) := by
  subst n
  exact tensorMap_apply f g i j x y

private lemma braiding_natural {X X' Y Y' : Comp.{u} R} (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorMap f g ≫ (cochainTensorBraiding X' Y').hom =
      (cochainTensorBraiding X Y).hom ≫ tensorMap g f := by
  apply HomologicalComplex.hom_ext
  intro n
  apply tensor_term_ext
  intro i j h x y
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply, tensorMap_tmul,
    cochainTensorBraiding_apply, map_sign]

private abbrev moduleTensor (R : Type u) [CommRing R] := curriedTensor (ModuleCat.{u} R)

local instance (M : ModuleCat.{u} R) : PreservesColimitsOfSize.{w, w'} ((moduleTensor R).obj M) :=
  (ihom.adjunction M).leftAdjoint_preservesColimits

local instance (M : ModuleCat.{u} R) : PreservesColimitsOfSize.{w, w'} ((moduleTensor R).flip.obj M) :=
  preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)


private lemma left_triple_inclusion (X Y Z : Comp.{u} R) (i j k m n : ℤ)
    (h : i + j = m) (hn : m + k = n) (x : X.X i) (y : Y.X j) (z : Z.X k) :
    HomologicalComplex.mapBifunctor₁₂.ι (moduleTensor R) (moduleTensor R) X Y Z
      shape shape i j k n (by change (i + j) + k = n; omega) ((x ⊗ₜ[R] y) ⊗ₜ[R] z) =
      cochainTmul (tensorComplex X Y) Z m k hn (cochainTmul X Y i j h x y) z := by
  have e := HomologicalComplex.mapBifunctor₁₂.ι_eq (moduleTensor R) (moduleTensor R)
    X Y Z shape shape i j k m n h hn
  exact ConcreteCategory.congr_hom e ((x ⊗ₜ[R] y) ⊗ₜ[R] z)

private lemma right_triple_inclusion (X Y Z : Comp.{u} R) (i j k m n : ℤ)
    (h : j + k = m) (hn : i + m = n) (x : X.X i) (y : Y.X j) (z : Z.X k) :
    HomologicalComplex.mapBifunctor₂₃.ι (moduleTensor R) (moduleTensor R) X Y Z
      shape shape shape i j k n (by change (i + j) + k = n; omega) (x ⊗ₜ[R] (y ⊗ₜ[R] z)) =
      cochainTmul X (tensorComplex Y Z) i m hn x (cochainTmul Y Z j k h y z) := by
  have e := HomologicalComplex.mapBifunctor₂₃.ι_eq (moduleTensor R) (moduleTensor R)
    X Y Z shape shape shape i j k m n h hn
  exact ConcreteCategory.congr_hom e (x ⊗ₜ[R] (y ⊗ₜ[R] z))

/-- The associator rebrackets each homogeneous pure tensor. -/
@[simp]
theorem cochainTensorAssociator_apply (X Y Z : Comp.{u} R) (i j k : ℤ) {m l n : ℤ}
    (h : i + j = m) (hn : m + k = n) (h' : j + k = l) (hn' : i + l = n)
    (x : X.X i) (y : Y.X j) (z : Z.X k) :
    (α_ X Y Z).hom.f n
      (cochainTmul (tensorComplex X Y) Z m k hn (cochainTmul X Y i j h x y) z) =
    cochainTmul X (tensorComplex Y Z) i l hn' x (cochainTmul Y Z j k h' y z) := by
  have e := HomologicalComplex.ι_mapBifunctorAssociatorX_hom
    (curriedAssociatorNatIso (ModuleCat R)) X Y Z shape shape shape i j k n
    (by change (i + j) + k = n; omega)
  have he := ConcreteCategory.congr_hom e ((x ⊗ₜ[R] y) ⊗ₜ[R] z)
  simp only [ModuleCat.comp_apply] at he
  rw [left_triple_inclusion X Y Z i j k m n h hn] at he
  have ha : (((curriedAssociatorNatIso (ModuleCat R)).hom.app (X.X i)).app (Y.X j)).app (Z.X k)
      ((x ⊗ₜ[R] y) ⊗ₜ[R] z) = x ⊗ₜ[R] (y ⊗ₜ[R] z) := rfl
  rw [ha, right_triple_inclusion X Y Z i j k l n h' hn'] at he
  exact he

private lemma left_triple_ext {X Y Z : Comp.{u} R} {n : ℤ} {M : ModuleCat.{u} R}
    {f g : (tensorComplex (tensorComplex X Y) Z).X n ⟶ M}
    (e : ∀ (i j k : ℤ) (h : i + j + k = n) (x : X.X i) (y : Y.X j) (z : Z.X k),
      f (cochainTmul (tensorComplex X Y) Z (i + j) k h (cochainTmul X Y i j rfl x y) z) =
      g (cochainTmul (tensorComplex X Y) Z (i + j) k h (cochainTmul X Y i j rfl x y) z)) :
    f = g := by
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro i j k h
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro x y z
  exact e i j k h x y z

private lemma whiskerRight_tmul {X X' : Comp.{u} R} (f : X ⟶ X') (Y : Comp.{u} R)
    (i j : ℤ) {n : ℤ} (h : i + j = n) (x : X.X i) (y : Y.X j) :
    (f ▷ Y).f n (cochainTmul X Y i j h x y) =
      cochainTmul X' Y i j h (f.f i x) y := by
  change (tensorMap f (𝟙 Y)).f n _ = _
  simpa only [HomologicalComplex.id_f, ModuleCat.id_apply] using tensorMap_tmul f (𝟙 Y) i j h x y

private lemma whiskerLeft_tmul (X : Comp.{u} R) {Y Y' : Comp.{u} R} (g : Y ⟶ Y')
    (i j : ℤ) {n : ℤ} (h : i + j = n) (x : X.X i) (y : Y.X j) :
    (X ◁ g).f n (cochainTmul X Y i j h x y) =
      cochainTmul X Y' i j h x (g.f j y) := by
  change (tensorMap (𝟙 X) g).f n _ = _
  simpa only [HomologicalComplex.id_f, ModuleCat.id_apply] using tensorMap_tmul (𝟙 X) g i j h x y

private lemma cochain_hexagon_forward (X Y Z : Comp.{u} R) :
    (α_ X Y Z).hom ≫ (cochainTensorBraiding X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
      ((cochainTensorBraiding X Y).hom ▷ Z) ≫ (α_ Y X Z).hom ≫
        (Y ◁ (cochainTensorBraiding X Z).hom) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply left_triple_ext
  intro i j k h x y z
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
  rw [cochainTensorAssociator_apply X Y Z i j k rfl h rfl (by omega) x y z]
  erw [cochainTensorBraiding_apply X (tensorComplex Y Z) i (j + k) (by omega) x
    (cochainTmul Y Z j k rfl y z)]
  rw [map_sign]
  rw [cochainTensorAssociator_apply Y Z X j k i rfl (by omega)
        (show k + i = i + k by omega) (by omega) y z x]
  rw [whiskerRight_tmul, cochainTensorBraiding_apply, tmul_sign_left, map_sign, map_sign]
  rw [cochainTensorAssociator_apply Y X Z j i k (by omega) h rfl (by omega) y x z]
  erw [whiskerLeft_tmul Y (cochainTensorBraiding X Z).hom j (i + k) (by omega) y
    (cochainTmul X Z i k rfl x z)]
  rw [cochainTensorBraiding_apply, tmul_sign_right, smul_smul, mul_add, Int.negOnePow_add]

private lemma cochain_hexagon_reverse (X Y Z : Comp.{u} R) :
    (α_ X Y Z).inv ≫ (cochainTensorBraiding (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv =
      (X ◁ (cochainTensorBraiding Y Z).hom) ≫ (α_ X Z Y).inv ≫
        ((cochainTensorBraiding X Z).hom ▷ Y) := by
  have e : (α_ Z X Y) ≪≫ cochainTensorBraiding Z (X ⊗ Y) ≪≫ (α_ X Y Z) =
      whiskerRightIso (cochainTensorBraiding Z X) Y ≪≫ (α_ X Z Y) ≪≫
        whiskerLeftIso X (cochainTensorBraiding Z Y) :=
    Iso.ext (cochain_hexagon_forward Z X Y)
  have he := congrArg Iso.inv e
  simp only [Iso.trans_inv, whiskerLeftIso_inv, whiskerRightIso_inv, Category.assoc] at he
  exact he

/-- The cochain tensor with the Koszul braiding is symmetric monoidal. -/
instance cochainSymmetricCategory : SymmetricCategory (Comp.{u} R) where
  braiding := cochainTensorBraiding
  braiding_naturality_left f Z := braiding_natural f (𝟙 Z)
  braiding_naturality_right X _ _ f := braiding_natural (𝟙 X) f
  hexagon_forward := cochain_hexagon_forward
  hexagon_reverse := cochain_hexagon_reverse
  symmetry := cochainSwap_involutive

private lemma leftUnitorTerm (X : Comp.{u} R) (i : ℤ) :
    ιTensorObj (cochainTensorUnit R) X 0 i i (zero_add i) ≫ (λ_ X).hom.f i =
      ((cochainTensorUnitZero R).hom ▷ X.X i) ≫ (λ_ (X.X i)).hom := by
  apply (cancel_mono ((λ_ X).inv.f i)).mp
  have e := HomologicalComplex.congr_hom (λ_ X).hom_inv_id i
  change (λ_ X).hom.f i ≫ (λ_ X).inv.f i = 𝟙 _ at e
  rw [Category.assoc, e]
  erw [Category.comp_id]
  have hinv : (λ_ X).inv.f i = (HomologicalComplex.leftUnitor' X).inv i := rfl
  rw [Category.assoc, hinv, HomologicalComplex.leftUnitor'_inv]
  rw [Iso.hom_inv_id_assoc]
  change _ = ((cochainTensorUnitZero R).hom ▷ X.X i) ≫
    ((cochainTensorUnitZero R).inv ▷ X.X i) ≫ ιTensorObj (cochainTensorUnit R) X 0 i i (zero_add i)
  rw [← comp_whiskerRight_assoc, Iso.hom_inv_id, id_whiskerRight, Category.id_comp]

private lemma rightUnitorTerm (X : Comp.{u} R) (i : ℤ) :
    ιTensorObj X (cochainTensorUnit R) i 0 i (add_zero i) ≫ (ρ_ X).hom.f i =
      (X.X i ◁ (cochainTensorUnitZero R).hom) ≫ (ρ_ (X.X i)).hom := by
  apply (cancel_mono ((ρ_ X).inv.f i)).mp
  have e := HomologicalComplex.congr_hom (ρ_ X).hom_inv_id i
  change (ρ_ X).hom.f i ≫ (ρ_ X).inv.f i = 𝟙 _ at e
  rw [Category.assoc, e]
  erw [Category.comp_id]
  have hinv : (ρ_ X).inv.f i = (HomologicalComplex.rightUnitor' X).inv i := rfl
  rw [Category.assoc, hinv, HomologicalComplex.rightUnitor'_inv]
  rw [Iso.hom_inv_id_assoc]
  change _ = (X.X i ◁ (cochainTensorUnitZero R).hom) ≫
    (X.X i ◁ (cochainTensorUnitZero R).inv) ≫ ιTensorObj X (cochainTensorUnit R) i 0 i (add_zero i)
  rw [← whiskerLeft_comp_assoc, Iso.hom_inv_id, whiskerLeft_id, Category.id_comp]

/-- The left unitor is scalar multiplication on each homogeneous pure tensor. -/
@[simp]
theorem cochainTensorLeftUnitor_apply (X : Comp.{u} R) (i : ℤ) (r : R) (x : X.X i) :
    (λ_ X).hom.f i
      (cochainTmul (cochainTensorUnit R) X 0 i (zero_add i) ((cochainTensorUnitZero R).inv r) x) =
    r • x := by
  have e := ConcreteCategory.congr_hom (leftUnitorTerm X i)
    ((cochainTensorUnitZero R).inv r ⊗ₜ[R] x)
  simp only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.whiskerRight_apply,
    Iso.inv_hom_id_apply] at e
  exact e.trans (ModuleCat.MonoidalCategory.leftUnitor_hom_apply r x)

/-- The right unitor is scalar multiplication on each homogeneous pure tensor. -/
@[simp]
theorem cochainTensorRightUnitor_apply (X : Comp.{u} R) (i : ℤ) (x : X.X i) (r : R) :
    (ρ_ X).hom.f i
      (cochainTmul X (cochainTensorUnit R) i 0 (add_zero i) x ((cochainTensorUnitZero R).inv r)) =
    r • x := by
  have e := ConcreteCategory.congr_hom (rightUnitorTerm X i)
    (x ⊗ₜ[R] (cochainTensorUnitZero R).inv r)
  simp only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply,
    Iso.inv_hom_id_apply] at e
  exact e.trans (ModuleCat.MonoidalCategory.rightUnitor_hom_apply x r)

private abbrev quotientFunctor (R : Type u) [CommRing R] := homotopyQuotient.{u} R

private abbrev homotopyTensorObj (A B : K.{u} R) : K.{u} R :=
  (quotientFunctor R).obj (A.as ⊗ B.as)

private def homotopyTensorMap {A A' B B' : K.{u} R} (f : A ⟶ A') (g : B ⟶ B') :
    homotopyTensorObj A B ⟶ homotopyTensorObj A' B' :=
  (quotientFunctor R).map (tensorMap f.out g.out)

private lemma homotopyTensorMap_quotient {A A' B B' : Comp.{u} R}
    (f : A ⟶ A') (g : B ⟶ B') :
    homotopyTensorMap ((quotientFunctor R).map f) ((quotientFunctor R).map g) =
      (quotientFunctor R).map (f ⊗ₘ g) :=
  HomotopyCategory.eq_of_homotopy _ _ (tensorMapHomotopy
    (HomotopyCategory.homotopyOutMap f) (HomotopyCategory.homotopyOutMap g))

@[instance_reducible]
private def homotopyMonoidalStruct : MonoidalCategoryStruct (K.{u} R) where
  tensorObj := homotopyTensorObj
  tensorHom := homotopyTensorMap
  whiskerLeft A _ _ g := homotopyTensorMap (𝟙 A) g
  whiskerRight f B := homotopyTensorMap f (𝟙 B)
  tensorUnit := (quotientFunctor R).obj (𝟙_ (Comp.{u} R))
  associator A B C := (quotientFunctor R).mapIso (α_ A.as B.as C.as)
  leftUnitor A := (quotientFunctor R).mapIso (λ_ A.as)
  rightUnitor A := (quotientFunctor R).mapIso (ρ_ A.as)

section

attribute [local instance] homotopyMonoidalStruct

private lemma homotopy_tensor_map {A A' B B' : Comp.{u} R}
    (f : A ⟶ A') (g : B ⟶ B') :
    (quotientFunctor R).map f ⊗ₘ (quotientFunctor R).map g =
      (quotientFunctor R).map (f ⊗ₘ g) := homotopyTensorMap_quotient f g

private lemma homotopy_obj_surjective (A : K.{u} R) :
    ∃ X : Comp.{u} R, (quotientFunctor R).obj X = A :=
  HomotopyCategory.quotient_obj_surjective A

private lemma homotopy_tensor_obj (X Y : Comp.{u} R) :
    (quotientFunctor R).obj X ⊗ (quotientFunctor R).obj Y = (quotientFunctor R).obj (X ⊗ Y) := rfl

private lemma homotopy_tensor_unit :
    𝟙_ (K.{u} R) = (quotientFunctor R).obj (𝟙_ (Comp.{u} R)) := rfl

private lemma homotopy_associator_hom (X Y Z : Comp.{u} R) :
    (α_ ((quotientFunctor R).obj X) ((quotientFunctor R).obj Y) ((quotientFunctor R).obj Z)).hom =
      (quotientFunctor R).map (α_ X Y Z).hom := rfl

private lemma homotopy_leftUnitor_hom (X : Comp.{u} R) :
    (λ_ ((quotientFunctor R).obj X)).hom = (quotientFunctor R).map (λ_ X).hom := rfl

private lemma homotopy_rightUnitor_hom (X : Comp.{u} R) :
    (ρ_ ((quotientFunctor R).obj X)).hom = (quotientFunctor R).map (ρ_ X).hom := rfl

set_option backward.isDefEq.respectTransparency false in
@[instance_reducible]
private def homotopyMonoidalCategoryAux : MonoidalCategory (K.{u} R) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (id_tensorHom_id := by
      intro A B
      obtain ⟨A, rfl⟩ := homotopy_obj_surjective A
      obtain ⟨B, rfl⟩ := homotopy_obj_surjective B
      simp only [← (quotientFunctor R).map_id, homotopy_tensor_map, id_tensorHom_id]
      exact (quotientFunctor R).map_id (A ⊗ B))
    (tensorHom_comp_tensorHom := by
      intro A B C D E F f g f' g'
      obtain ⟨A, rfl⟩ := homotopy_obj_surjective A
      obtain ⟨B, rfl⟩ := homotopy_obj_surjective B
      obtain ⟨C, rfl⟩ := homotopy_obj_surjective C
      obtain ⟨D, rfl⟩ := homotopy_obj_surjective D
      obtain ⟨E, rfl⟩ := homotopy_obj_surjective E
      obtain ⟨F, rfl⟩ := homotopy_obj_surjective F
      obtain ⟨f, rfl⟩ := (quotientFunctor R).map_surjective f
      obtain ⟨g, rfl⟩ := (quotientFunctor R).map_surjective g
      obtain ⟨f', rfl⟩ := (quotientFunctor R).map_surjective f'
      obtain ⟨g', rfl⟩ := (quotientFunctor R).map_surjective g'
      simp only [← (quotientFunctor R).map_comp, homotopy_tensor_map, tensorHom_comp_tensorHom])
    (associator_naturality := by
      intro A B C D E F f g h
      obtain ⟨A, rfl⟩ := homotopy_obj_surjective A
      obtain ⟨B, rfl⟩ := homotopy_obj_surjective B
      obtain ⟨C, rfl⟩ := homotopy_obj_surjective C
      obtain ⟨D, rfl⟩ := homotopy_obj_surjective D
      obtain ⟨E, rfl⟩ := homotopy_obj_surjective E
      obtain ⟨F, rfl⟩ := homotopy_obj_surjective F
      obtain ⟨f, rfl⟩ := (quotientFunctor R).map_surjective f
      obtain ⟨g, rfl⟩ := (quotientFunctor R).map_surjective g
      obtain ⟨h, rfl⟩ := (quotientFunctor R).map_surjective h
      simpa only [homotopy_tensor_map, homotopy_associator_hom, ← (quotientFunctor R).map_comp]
        using congrArg ((quotientFunctor R).map) (associator_naturality f g h))
    (leftUnitor_naturality := by
      intro A B f
      obtain ⟨A, rfl⟩ := homotopy_obj_surjective A
      obtain ⟨B, rfl⟩ := homotopy_obj_surjective B
      obtain ⟨f, rfl⟩ := (quotientFunctor R).map_surjective f
      simpa only [homotopy_tensor_obj, homotopy_tensor_unit, ← (quotientFunctor R).map_id, homotopy_tensor_map,
        homotopy_leftUnitor_hom, ← (quotientFunctor R).map_comp, id_tensorHom]
        using congrArg ((quotientFunctor R).map) (leftUnitor_naturality f))
    (rightUnitor_naturality := by
      intro A B f
      obtain ⟨A, rfl⟩ := homotopy_obj_surjective A
      obtain ⟨B, rfl⟩ := homotopy_obj_surjective B
      obtain ⟨f, rfl⟩ := (quotientFunctor R).map_surjective f
      simpa only [homotopy_tensor_obj, homotopy_tensor_unit, ← (quotientFunctor R).map_id, homotopy_tensor_map,
        homotopy_rightUnitor_hom, ← (quotientFunctor R).map_comp, tensorHom_id]
        using congrArg ((quotientFunctor R).map) (rightUnitor_naturality f))
    (pentagon := by
      intro W X Y Z
      obtain ⟨W, rfl⟩ := homotopy_obj_surjective W
      obtain ⟨X, rfl⟩ := homotopy_obj_surjective X
      obtain ⟨Y, rfl⟩ := homotopy_obj_surjective Y
      obtain ⟨Z, rfl⟩ := homotopy_obj_surjective Z
      simpa only [homotopy_tensor_obj, homotopy_tensor_unit, ← (quotientFunctor R).map_id, homotopy_tensor_map,
        homotopy_associator_hom, homotopy_leftUnitor_hom, homotopy_rightUnitor_hom,
        ← (quotientFunctor R).map_comp, id_tensorHom, tensorHom_id]
        using congrArg ((quotientFunctor R).map) (pentagon W X Y Z))
    (triangle := by
      intro X Y
      obtain ⟨X, rfl⟩ := homotopy_obj_surjective X
      obtain ⟨Y, rfl⟩ := homotopy_obj_surjective Y
      simpa only [homotopy_tensor_obj, homotopy_tensor_unit, ← (quotientFunctor R).map_id, homotopy_tensor_map,
        homotopy_associator_hom, homotopy_leftUnitor_hom, homotopy_rightUnitor_hom,
        ← (quotientFunctor R).map_comp, id_tensorHom, tensorHom_id]
        using congrArg ((quotientFunctor R).map) (triangle X Y))

end

/-- The tensor product on the cochain homotopy category. -/
instance homotopyMonoidalCategory : MonoidalCategory (K.{u} R) :=
  homotopyMonoidalCategoryAux

private def homotopyBraiding (A B : K.{u} R) : A ⊗ B ≅ B ⊗ A :=
  (quotientFunctor R).mapIso (β_ A.as B.as)

private lemma homotopy_braiding_hom (X Y : Comp.{u} R) :
    (homotopyBraiding ((quotientFunctor R).obj X) ((quotientFunctor R).obj Y)).hom =
      (quotientFunctor R).map (β_ X Y).hom := rfl

private lemma homotopy_associator_inv (X Y Z : Comp.{u} R) :
    (α_ ((quotientFunctor R).obj X) ((quotientFunctor R).obj Y) ((quotientFunctor R).obj Z)).inv =
      (quotientFunctor R).map (α_ X Y Z).inv := rfl

private lemma homotopy_whiskerLeft (X : Comp.{u} R) {Y Z : Comp.{u} R} (f : Y ⟶ Z) :
    (quotientFunctor R).obj X ◁ (quotientFunctor R).map f = (quotientFunctor R).map (X ◁ f) := by
  change homotopyTensorMap (𝟙 ((quotientFunctor R).obj X)) ((quotientFunctor R).map f) = _
  rw [← (quotientFunctor R).map_id X, homotopyTensorMap_quotient]
  rfl

private lemma homotopy_whiskerRight {X Y : Comp.{u} R} (f : X ⟶ Y) (Z : Comp.{u} R) :
    (quotientFunctor R).map f ▷ (quotientFunctor R).obj Z = (quotientFunctor R).map (f ▷ Z) := by
  change homotopyTensorMap ((quotientFunctor R).map f) (𝟙 ((quotientFunctor R).obj Z)) = _
  rw [← (quotientFunctor R).map_id Z, homotopyTensorMap_quotient]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The cochain homotopy category has the descended Koszul symmetry. -/
instance homotopySymmetricCategory : SymmetricCategory (K.{u} R) where
  braiding := homotopyBraiding
  braiding_naturality_left {X Y} f Z := by
    obtain ⟨X, rfl⟩ := homotopy_obj_surjective X
    obtain ⟨Y, rfl⟩ := homotopy_obj_surjective Y
    obtain ⟨Z, rfl⟩ := homotopy_obj_surjective Z
    obtain ⟨f, rfl⟩ := (quotientFunctor R).map_surjective f
    simpa only [homotopy_whiskerRight, homotopy_whiskerLeft, homotopy_braiding_hom,
      ← (quotientFunctor R).map_comp] using
      congrArg ((quotientFunctor R).map) (BraidedCategory.braiding_naturality_left f Z)
  braiding_naturality_right X Y Z f := by
    obtain ⟨X, rfl⟩ := homotopy_obj_surjective X
    obtain ⟨Y, rfl⟩ := homotopy_obj_surjective Y
    obtain ⟨Z, rfl⟩ := homotopy_obj_surjective Z
    obtain ⟨f, rfl⟩ := (quotientFunctor R).map_surjective f
    simpa only [homotopy_whiskerRight, homotopy_whiskerLeft, homotopy_braiding_hom,
      ← (quotientFunctor R).map_comp] using
      congrArg ((quotientFunctor R).map) (BraidedCategory.braiding_naturality_right X f)
  hexagon_forward X Y Z := by
    obtain ⟨X, rfl⟩ := homotopy_obj_surjective X
    obtain ⟨Y, rfl⟩ := homotopy_obj_surjective Y
    obtain ⟨Z, rfl⟩ := homotopy_obj_surjective Z
    simpa only [homotopy_tensor_obj, homotopy_associator_hom, homotopy_braiding_hom,
      homotopy_whiskerRight, homotopy_whiskerLeft, ← (quotientFunctor R).map_comp] using
      congrArg ((quotientFunctor R).map) (BraidedCategory.hexagon_forward X Y Z)
  hexagon_reverse X Y Z := by
    obtain ⟨X, rfl⟩ := homotopy_obj_surjective X
    obtain ⟨Y, rfl⟩ := homotopy_obj_surjective Y
    obtain ⟨Z, rfl⟩ := homotopy_obj_surjective Z
    simpa only [homotopy_tensor_obj, homotopy_associator_inv, homotopy_braiding_hom,
      homotopy_whiskerRight, homotopy_whiskerLeft, ← (quotientFunctor R).map_comp] using
      congrArg ((quotientFunctor R).map) (BraidedCategory.hexagon_reverse X Y Z)
  symmetry X Y := by
    obtain ⟨X, rfl⟩ := homotopy_obj_surjective X
    obtain ⟨Y, rfl⟩ := homotopy_obj_surjective Y
    simpa only [homotopy_tensor_obj, homotopy_braiding_hom,
      ← (quotientFunctor R).map_comp, ← (quotientFunctor R).map_id] using
      congrArg ((quotientFunctor R).map) (SymmetricCategory.symmetry X Y)

set_option backward.isDefEq.respectTransparency false in
private def homotopyQuotientCoreMonoidal : (quotientFunctor R).CoreMonoidal where
  εIso := Iso.refl _
  μIso _ _ := Iso.refl _
  μIso_hom_natural_left f Z := by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp,
    homotopy_whiskerRight]
  μIso_hom_natural_right X f := by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp,
    homotopy_whiskerLeft]
  associativity X Y Z := by
    simp only [Iso.refl_hom, id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id]
    rfl
  left_unitality X := by
    simp only [Iso.refl_hom, id_whiskerRight, Category.id_comp]
    rfl
  right_unitality X := by
    simp only [Iso.refl_hom, whiskerLeft_id, Category.id_comp]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Passage to homotopy classes preserves the tensor, unit and all coherence maps. -/
instance homotopyQuotientBraided : (homotopyQuotient.{u} R).Braided where
  toMonoidal := (homotopyQuotientCoreMonoidal (R := R)).toMonoidal
  braided X Y := by
    change 𝟙 _ ≫ (quotientFunctor R).map (β_ X Y).hom =
      (quotientFunctor R).map (β_ X Y).hom ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]

/-- The canonical monoidal structure with the direct-sum cochain tensor. -/
abbrev cochainMonoidalCategory : MonoidalCategory (Comp.{u} R) :=
  HomologicalComplex.monoidalCategory (ModuleCat R) shape

open Specs.DerivedFormalization.CochainTensorMonoidal (HasKoszulBraiding)

/-- The canonical cochain monoidal structure admits the signed symmetry. -/
theorem cochainTensor_isSymmetric (R : Type u) [CommRing R] :
    ∃ s : SymmetricCategory (Comp.{u} R), HasKoszulBraiding s :=
  ⟨cochainSymmetricCategory, cochainTensorBraiding_apply⟩

/-- The signed structure passes to homotopy classes with identity comparisons. -/
theorem homotopyTensor_isSymmetric :
    Specs.DerivedFormalization.CochainTensorMonoidal.homotopySymmetricType.{u} := by
  intro R _
  refine ⟨cochainSymmetricCategory, homotopyMonoidalCategory, cochainTensorBraiding_apply,
    homotopySymmetricCategory, homotopyQuotientBraided, ?_, ?_⟩
  · exact ⟨rfl, rfl⟩
  · intro X Y
    exact ⟨rfl, rfl⟩

attribute [instance] cochainMonoidalCategory

end

end DerivedFormalization
