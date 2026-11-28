import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.DualTorusReconstruction
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Invariants.TorusWeights
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.HopfAlgebras
import Mathlib.LinearAlgebra.Dual.Lemmas
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.TorusSatake
noncomputable section

open CategoryTheory CategoryTheory.Functor LinearAlgebraicGroups
open CategoryTheory.Functor.LaxMonoidal
open LinearAlgebraicGroups.WeightDecomposition (weightSpace mem_weightSpace tensorCoactionMap)
open RepTheorySurvey.Invariants.TorusWeights (weightSum weightSum_lof degreePreserving)
open scoped MonoidalCategory TensorProduct ChangeOfRings DirectSum

namespace RepTheorySurvey.Geometric.DualTorusReconstruction

open Analytic TorusPerverseSpecs TorusOrderedConvolutionSpecs TorusFusionSpecs
  TorusSymmetricConvolutionSpecs TorusSatakeSpecs DualTorusReconstructionSpecs

open private linearMap_ext_weights from
  MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Invariants.TorusWeights

private def characterPoints (r : ℕ) :
    characterFunctor r ≅ convolutionPoints (coordinateAlgebra r) := by
  let e (A : Test) : (Characters r →* Aˣ) ≃*
      (convolutionPoints (coordinateAlgebra r)).obj A :=
    (MonoidHom.toHomUnitsMulEquiv (G := Characters r) (M := A)).symm.trans
      (MonoidAlgebra.liftMulEquiv ℚ A (Characters r))
  refine NatIso.ofComponents (fun A ↦ (e A).toGrpIso) ?_
  intro A B f
  apply GrpCat.ext
  intro u
  apply WithConv.ofConv_injective
  apply (MonoidAlgebra.lift ℚ B (Characters r)).symm.injective
  apply MonoidHom.ext
  intro m
  change MonoidAlgebra.lift ℚ B (Characters r)
      ((Units.coeHom B).comp ((Units.map f.hom.toMonoidHom).comp u))
        (MonoidAlgebra.of ℚ (Characters r) m) =
    f.hom (MonoidAlgebra.lift ℚ A (Characters r) ((Units.coeHom A).comp u)
      (MonoidAlgebra.of ℚ (Characters r) m))
  simp only [MonoidAlgebra.lift_of]
  rfl

private def pointsIso (r : ℕ) : characterFunctor r ≅ pointsFunctor r :=
  characterPoints r ≪≫ hopfSpecPointIso (coordinateAlgebra r)

private abbrev gen {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    {M : ModuleCat R} (s : S) (x : M) : (ModuleCat.extendScalars f).obj M :=
  s ⊗ₜ[R,f] x

private theorem gen_smul {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    {M : ModuleCat R} (s t : S) (x : M) :
    s • gen f t x = gen f (s * t) x := rfl

private theorem extend_μ_gen {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    {X Y : ModuleCat R} (a b : S) (x : X) (y : Y) :
    μ (ModuleCat.extendScalars f) X Y (gen f a x ⊗ₜ[S] gen f b y) =
      gen f (a * b) (x ⊗ₜ[R] y) := by
  let := f.toAlgebra
  exact TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul
    (R := R) (A := S) x y a b

private theorem extend_ε_gen {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (a : S) : ε (ModuleCat.extendScalars f) a = gen f a (1 : R) := rfl

private theorem scalar_naturality_gen {A B : Test} (f : A ⟶ B)
    (X : ModuleCat ℚ) (x : X) (b : B) :
    (scalarComparison f).hom.app X (gen (algebraMap ℚ B) b x) =
      gen f.hom.toRingHom b (gen (algebraMap ℚ A) 1 x) := by
  have h : algebraMap ℚ B = f.hom.toRingHom.comp (algebraMap ℚ A) := by
    ext q
    exact (f.hom.commutes q).symm
  have hh (t : ℚ →+* B) (e : algebraMap ℚ B = t) :
      (eqToIso (congrArg ModuleCat.extendScalars e)).hom.app X
        (gen (algebraMap ℚ B) b x) = gen t b x := by
    subst t
    rfl
  change (ModuleCat.extendScalarsComp (algebraMap ℚ A) f.hom.toRingHom).hom.app X
    ((eqToIso (congrArg ModuleCat.extendScalars h)).hom.app X
      (gen (algebraMap ℚ B) b x)) = _
  rw [hh _ h]
  calc
    _ = (ModuleCat.extendScalarsComp (algebraMap ℚ A) f.hom.toRingHom).hom.app X
        (b • gen (f.hom.toRingHom.comp (algebraMap ℚ A)) 1 x) := by rw [gen_smul, mul_one]
    _ = _ := by
      have h₁ := ModuleCat.extendScalarsComp_hom_app_one_tmul
        (algebraMap ℚ A) f.hom.toRingHom X x
      change (ModuleCat.extendScalarsComp (algebraMap ℚ A) f.hom.toRingHom).hom.app X
        (gen (f.hom.toRingHom.comp (algebraMap ℚ A)) 1 x) = _ at h₁
      rw [_root_.map_smul, h₁]
      change b • gen f.hom.toRingHom 1 (gen (algebraMap ℚ A) 1 x) = _
      rw [gen_smul, mul_one]

section WeightLines

variable {r : ℕ}
local notation "H" => coordinateAlgebra r
local notation "e" => MonoidAlgebra.of ℚ (Characters r)

private abbrev line (m : Characters r) : Representations r where
  space := ModuleCat.of ℚ ℚ
  finiteDimensional := inferInstance
  coaction :=
    { coaction := (TensorProduct.mk ℚ ℚ H).flip (e m)
      coassoc := fun q ↦ by
        change TensorProduct.assoc ℚ ℚ H H
            (((TensorProduct.mk ℚ ℚ H).flip (e m)).rTensor H (q ⊗ₜ[ℚ] e m)) =
          (Coalgebra.comul (R := ℚ) (A := H)).lTensor ℚ (q ⊗ₜ[ℚ] e m)
        rw [LinearMap.rTensor_tmul, LinearMap.flip_apply, TensorProduct.mk_apply,
          TensorProduct.assoc_tmul, LinearMap.lTensor_tmul,
          (MonoidAlgebra.isGroupLikeElem_of (R := ℚ) m).comul_eq_tmul_self]
      counit := fun q ↦ by
        change TensorProduct.rid ℚ ℚ
          ((Coalgebra.counit (R := ℚ) (A := H)).lTensor ℚ (q ⊗ₜ[ℚ] e m)) = q
        rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul,
          (MonoidAlgebra.isGroupLikeElem_of (R := ℚ) m).counit_eq_one, one_smul] }

private theorem line_weight (m : Characters r) (v : (line m).space) :
    v ∈ weightSpace (line m).coaction m := mem_weightSpace.mpr rfl

private def lineMap (X : Representations r) (m : Characters r)
    (v : weightSpace X.coaction m) : line m ⟶ X :=
  ⟨(LinearMap.id (R := ℚ) (M := ℚ)).smulRight v.val, by
    apply LinearMap.ext
    intro q
    change ℚ at q
    change (q • v.val) ⊗ₜ[ℚ] e m = X.coaction.coaction (q • v.val)
    rw [_root_.map_smul, mem_weightSpace.mp v.property, TensorProduct.smul_tmul']⟩

private theorem extendedHom_ext_weights (A : Test) (X : Representations r) {Y : ModuleCat A}
    {f g : (extend A).obj X.space ⟶ Y}
    (h : ∀ m (v : weightSpace X.coaction m),
      f (gen (algebraMap ℚ A) 1 v.val) = g (gen (algebraMap ℚ A) 1 v.val)) : f = g := by
  apply ((ModuleCat.extendRestrictScalarsAdj (algebraMap ℚ A)).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply linearMap_ext_weights X.coaction
  exact h

private abbrev Character (r : ℕ) (A : Test) := Characters r →* Aˣ

private def weightAction (A : Test) (u : Character r A) (X : Representations r) :
    (extend A).obj X.space ⟶ (extend A).obj X.space := by
  classical
  let f := algebraMap ℚ A
  let Y := (extend A).obj X.space
  let i := (ModuleCat.ExtendRestrictScalarsAdj.unit f).app X.space
  let d (m : Characters r) : Y ⟶ Y :=
    ModuleCat.ofHom ((u m : A) • LinearMap.id)
  let q := DirectSum.toModule ℚ (Characters r) ((ModuleCat.restrictScalars f).obj Y)
    fun m ↦ ((i ≫ (ModuleCat.restrictScalars f).map (d m) : X.space ⟶
      (ModuleCat.restrictScalars f).obj Y)).hom.comp (weightSpace X.coaction m).subtype
  exact ((ModuleCat.extendRestrictScalarsAdj f).homEquiv X.space Y).symm
    (ModuleCat.ofHom (X := X.space) (Y := (ModuleCat.restrictScalars f).obj Y)
      (q.comp (weightSum X.coaction).symm.toLinearMap))

private theorem weightAction_gen (A : Test) (u : Character r A) (X : Representations r)
    (m : Characters r) (v : weightSpace X.coaction m) (b : A) :
    weightAction A u X (gen (algebraMap ℚ A) b v.val) =
      gen (algebraMap ℚ A) ((u m : A) * b) v.val := by
  classical
  have h : weightAction A u X (gen (algebraMap ℚ A) 1 v.val) =
      (u m : A) • gen (algebraMap ℚ A) 1 v.val := by
    unfold weightAction
    erw [← ModuleCat.extendRestrictScalarsAdj_homEquiv_apply,
      Equiv.apply_symm_apply]
    have hv : (weightSum X.coaction).symm v.val = DirectSum.lof ℚ (Characters r) _ m v :=
      (weightSum X.coaction).symm_apply_eq.mpr (weightSum_lof X.coaction m v).symm
    erw [ModuleCat.ofHom_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hv,
      DirectSum.toModule_lof]
    rfl
  calc
    _ = b • weightAction A u X (gen (algebraMap ℚ A) 1 v.val) := by
      rw [← _root_.map_smul, gen_smul, mul_one]
    _ = _ := by rw [h, gen_smul, mul_one, gen_smul, mul_comm b]

private theorem weightAction_natural (A : Test) (u : Character r A)
    {X Y : Representations r} (f : X ⟶ Y) :
    (extend A).map ((underlying r).map f) ≫ weightAction A u Y =
      weightAction A u X ≫ (extend A).map ((underlying r).map f) := by
  apply extendedHom_ext_weights A X
  intro m v
  let w : weightSpace Y.coaction m :=
    ⟨f.val v.val, (degreePreserving X.coaction Y.coaction f.val).mp f.property m v.property⟩
  change weightAction A u Y (gen (algebraMap ℚ A) 1 w.val) =
    (extend A).map ((underlying r).map f) (weightAction A u X (gen (algebraMap ℚ A) 1 v.val))
  rw [weightAction_gen, weightAction_gen]
  rfl

private theorem weightAction_one (A : Test) (X : Representations r) :
    weightAction A 1 X = 𝟙 _ := by
  apply extendedHom_ext_weights A X
  intro m v
  rw [weightAction_gen]
  simp

private theorem weightAction_mul (A : Test) (u v : Character r A) (X : Representations r) :
    weightAction A (u * v) X = weightAction A v X ≫ weightAction A u X := by
  apply extendedHom_ext_weights A X
  intro m x
  rw [ModuleCat.comp_apply, weightAction_gen, weightAction_gen, weightAction_gen]
  simp

private theorem extendedTensor_ext_weights (A : Test) (X Y : Representations r) {Z : ModuleCat A}
    {f g : (extend A).obj X.space ⊗ (extend A).obj Y.space ⟶ Z}
    (h : ∀ m n (v : weightSpace X.coaction m) (w : weightSpace Y.coaction n),
      f (gen (algebraMap ℚ A) 1 v.val ⊗ₜ[A] gen (algebraMap ℚ A) 1 w.val) =
        g (gen (algebraMap ℚ A) 1 v.val ⊗ₜ[A] gen (algebraMap ℚ A) 1 w.val)) :
    f = g := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  have hx (m) (v : weightSpace X.coaction m) :
      f (gen (algebraMap ℚ A) 1 v.val ⊗ₜ[A] y) =
        g (gen (algebraMap ℚ A) 1 v.val ⊗ₜ[A] y) := by
    let i := TensorProduct.mk A ((extend A).obj X.space) ((extend A).obj Y.space)
      (gen (algebraMap ℚ A) 1 v.val)
    have hh : ModuleCat.ofHom (f.hom.comp i) = ModuleCat.ofHom (g.hom.comp i) :=
      extendedHom_ext_weights A Y (h m · v)
    exact ConcreteCategory.congr_hom hh y
  let i := (TensorProduct.mk A ((extend A).obj X.space) ((extend A).obj Y.space)).flip y
  have hh : ModuleCat.ofHom (f.hom.comp i) = ModuleCat.ofHom (g.hom.comp i) :=
    extendedHom_ext_weights A X hx
  exact ConcreteCategory.congr_hom hh x

end WeightLines

section MonoidalRepresentation

variable {r : ℕ} [MonoidalCategory (Representations r)] [(underlying r).Monoidal]

private abbrev representationFiber (A : Test) :=
  LaxMonoidalFunctor.of (underlying r ⋙ extend A)

private structure WeightRules : Prop where
  unit : ∀ q : (𝟙_ Coeff.{0}), ε (underlying r) q ∈
    weightSpace (𝟙_ (Representations r)).coaction 1
  tensor : ∀ (X Y : Representations r) (m n : Characters r)
    (v : weightSpace X.coaction m) (w : weightSpace Y.coaction n),
    μ (underlying r) X Y (v.val ⊗ₜ[ℚ] w.val) ∈ weightSpace (X ⊗ Y).coaction (m * n)

private theorem representation_ε_gen (A : Test) (a : A) :
    ε (representationFiber (r := r) A).toFunctor a =
      gen (algebraMap ℚ A) a (ε (underlying r) (1 : ℚ)) := by
  change (extend A).map (ε (underlying r)) (ε (extend A) a) = _
  rw [extend_ε_gen]
  rfl

private theorem representation_μ_gen (A : Test) (X Y : Representations r)
    (a b : A) (x : X.space) (y : Y.space) :
    μ (representationFiber (r := r) A).toFunctor X Y
      (gen (algebraMap ℚ A) a x ⊗ₜ[A] gen (algebraMap ℚ A) b y) =
      gen (algebraMap ℚ A) (a * b) (μ (underlying r) X Y (x ⊗ₜ[ℚ] y)) := by
  change (extend A).map (μ (underlying r) X Y)
    (μ (extend A) X.space Y.space (gen (algebraMap ℚ A) a x ⊗ₜ[A]
      gen (algebraMap ℚ A) b y)) = _
  rw [extend_μ_gen]
  rfl

private def weightEnd (rules : WeightRules (r := r)) (A : Test) (u : Character r A) :
    representationFiber (r := r) A ⟶ representationFiber (r := r) A :=
  ⟨{ app := weightAction A u
     naturality := fun _ _ f ↦ weightAction_natural A u f }, by
    constructor
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      let v : weightSpace (𝟙_ (Representations r)).coaction (1 : Characters r) :=
        ⟨ε (underlying r) (1 : ℚ), rules.unit 1⟩
      change weightAction A u _ (ε (representationFiber (r := r) A).toFunctor a) =
        ε (representationFiber (r := r) A).toFunctor a
      rw [representation_ε_gen]
      change weightAction A u _ (gen (algebraMap ℚ A) a v.val) = _
      rw [weightAction_gen]
      simp [v]
      rfl
    · intro X Y
      apply extendedTensor_ext_weights A X Y
      intro m n v w
      let z : weightSpace (X ⊗ Y).coaction (m * n) :=
        ⟨μ (underlying r) X Y (v.val ⊗ₜ[ℚ] w.val), rules.tensor X Y m n v w⟩
      change weightAction A u _ (μ (representationFiber (r := r) A).toFunctor X Y
        (gen (algebraMap ℚ A) 1 v.val ⊗ₜ[A] gen (algebraMap ℚ A) 1 w.val)) =
          μ (representationFiber (r := r) A).toFunctor X Y
            (weightAction A u X (gen (algebraMap ℚ A) 1 v.val) ⊗ₜ[A]
              weightAction A u Y (gen (algebraMap ℚ A) 1 w.val))
      rw [representation_μ_gen, weightAction_gen, weightAction_gen]
      erw [representation_μ_gen]
      change weightAction A u _ (gen (algebraMap ℚ A) (1 * 1) z.val) = _
      rw [weightAction_gen]
      simp [z]
      rfl⟩

private def weightAut (rules : WeightRules (r := r)) (A : Test) :
    Character r A →* Aut (representationFiber (r := r) A) where
  toFun u := Aut.of
    { hom := weightEnd rules A u
      inv := weightEnd rules A u⁻¹
      hom_inv_id := by
        apply LaxMonoidalFunctor.hom_ext
        apply NatTrans.ext
        funext X
        change weightAction A u X ≫ weightAction A u⁻¹ X = 𝟙 _
        rw [← weightAction_mul]
        exact (congrArg (fun w : Character r A ↦ weightAction A w X)
          (inv_mul_cancel u)).trans (weightAction_one A X)
      inv_hom_id := by
        apply LaxMonoidalFunctor.hom_ext
        apply NatTrans.ext
        funext X
        change weightAction A u⁻¹ X ≫ weightAction A u X = 𝟙 _
        rw [← weightAction_mul]
        exact (congrArg (fun w : Character r A ↦ weightAction A w X)
          (mul_inv_cancel u)).trans (weightAction_one A X) }
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    apply LaxMonoidalFunctor.hom_ext
    apply NatTrans.ext
    funext X
    exact weightAction_one A X
  map_mul' u v := by
    apply Aut.ext
    apply Iso.ext
    apply LaxMonoidalFunctor.hom_ext
    apply NatTrans.ext
    funext X
    exact weightAction_mul A u v X

private abbrev repApp {A : Test} (η : Aut (representationFiber (r := r) A))
    (X : Representations r) : (extend A).obj X.space ⟶ (extend A).obj X.space :=
  η.asIso.hom.hom.app X

private theorem coefficient_injective (A : Test) {X : ModuleCat.{0} ℚ} (x : X) (hx : x ≠ 0) :
    Function.Injective (fun b : A ↦ gen (algebraMap ℚ A) b x) := by
  obtain ⟨d, hd⟩ := Module.Projective.exists_dual_eq_one ℚ hx
  intro a b h
  have eq := congrArg ((extend A).map (ModuleCat.ofHom (X := X) (Y := 𝟙_ Coeff.{0}) d)) h
  change gen (algebraMap ℚ A) (M := 𝟙_ Coeff.{0}) a (d x) =
    gen (algebraMap ℚ A) (M := 𝟙_ Coeff.{0}) b (d x) at eq
  rw [hd, ← extend_ε_gen, ← extend_ε_gen] at eq
  exact (ConcreteCategory.bijective_of_isIso (ε (extend A))).injective eq

private def lineScalar (A : Test) (η : Aut (representationFiber (r := r) A))
    (m : Characters r) : A :=
  (Monoidal.εIso (extend A)).inv
    (repApp η (line m) (gen (algebraMap ℚ A) 1 (1 : ℚ)))

private theorem lineScalar_eq (A : Test) (η : Aut (representationFiber (r := r) A))
    (m : Characters r) :
    repApp η (line m) (gen (algebraMap ℚ A) 1 (1 : ℚ)) =
      gen (algebraMap ℚ A) (lineScalar A η m) (1 : ℚ) := by
  erw [← extend_ε_gen]
  exact (ConcreteCategory.congr_hom (Monoidal.εIso (extend A)).inv_hom_id _).symm

private theorem acts_on_weight (A : Test) (η : Aut (representationFiber (r := r) A))
    (X : Representations r) (m : Characters r) (v : weightSpace X.coaction m) :
    repApp η X (gen (algebraMap ℚ A) 1 v.val) =
      gen (algebraMap ℚ A) (lineScalar A η m) v.val := by
  let f := lineMap X m v
  have h := ConcreteCategory.congr_hom (η.asIso.hom.hom.naturality f)
    (gen (algebraMap ℚ A) 1 (1 : ℚ))
  have hv : f.val (1 : ℚ) = v.val := one_smul ℚ v.val
  change repApp η X (gen (algebraMap ℚ A) 1 (f.val (1 : ℚ))) =
    (extend A).map ((underlying r).map f)
      (repApp η (line m) (gen (algebraMap ℚ A) 1 (1 : ℚ))) at h
  rw [lineScalar_eq] at h
  change repApp η X (gen (algebraMap ℚ A) 1 (f.val (1 : ℚ))) =
    gen (algebraMap ℚ A) (lineScalar A η m) (f.val (1 : ℚ)) at h
  simpa only [hv] using h

private def scalars (rules : WeightRules (r := r)) (A : Test)
    (η : Aut (representationFiber (r := r) A)) : Characters r →* A where
  toFun := lineScalar A η
  map_one' := by
    let I := 𝟙_ (Representations r)
    let v : weightSpace I.coaction (1 : Characters r) :=
      ⟨ε (underlying r) (1 : ℚ), rules.unit 1⟩
    have hv : v.val ≠ 0 := by
      intro hz
      have he : ε (underlying r) (1 : ℚ) = ε (underlying r) (0 : ℚ) :=
        hz.trans (LinearMap.map_zero (ε (underlying r)).hom).symm
      exact (one_ne_zero : (1 : ℚ) ≠ 0)
        ((ConcreteCategory.bijective_of_isIso (ε (underlying r))).injective he)
    have hh := ConcreteCategory.congr_hom
      (NatTrans.IsMonoidal.unit (τ := η.asIso.hom.hom)) (1 : A)
    change repApp η I (ε (representationFiber (r := r) A).toFunctor (1 : A)) =
      ε (representationFiber (r := r) A).toFunctor (1 : A) at hh
    rw [representation_ε_gen] at hh
    change repApp η I (gen (algebraMap ℚ A) 1 v.val) = gen (algebraMap ℚ A) 1 v.val at hh
    rw [acts_on_weight A η I 1 v] at hh
    exact coefficient_injective A v.val hv hh
  map_mul' m n := by
    let X := line m
    let Y := line n
    let z : weightSpace (X ⊗ Y).coaction (m * n) :=
      ⟨μ (underlying r) X Y ((1 : ℚ) ⊗ₜ[ℚ] (1 : ℚ)),
        rules.tensor X Y m n ⟨1, line_weight m 1⟩ ⟨1, line_weight n 1⟩⟩
    have hz : z.val ≠ 0 := by
      intro hh
      have eq : (1 : ℚ) ⊗ₜ[ℚ] (1 : ℚ) = 0 :=
        (ConcreteCategory.bijective_of_isIso (μ (underlying r) X Y)).injective
          (hh.trans (LinearMap.map_zero (μ (underlying r) X Y).hom).symm)
      exact (one_ne_zero : (1 : ℚ) ≠ 0) (by
        simpa using congrArg (TensorProduct.lid ℚ ℚ) eq)
    have hh := ConcreteCategory.congr_hom
      (NatTrans.IsMonoidal.tensor (τ := η.asIso.hom.hom) X Y)
      (gen (algebraMap ℚ A) 1 (1 : ℚ) ⊗ₜ[A] gen (algebraMap ℚ A) 1 (1 : ℚ))
    change repApp η (X ⊗ Y) (μ (representationFiber (r := r) A).toFunctor X Y
      (gen (algebraMap ℚ A) 1 (1 : ℚ) ⊗ₜ[A] gen (algebraMap ℚ A) 1 (1 : ℚ))) =
        μ (representationFiber (r := r) A).toFunctor X Y
          (repApp η (line m) (gen (algebraMap ℚ A) 1 (1 : ℚ)) ⊗ₜ[A]
            repApp η (line n) (gen (algebraMap ℚ A) 1 (1 : ℚ))) at hh
    erw [representation_μ_gen A X Y 1 1 (1 : ℚ) (1 : ℚ)] at hh
    erw [one_mul, lineScalar_eq, lineScalar_eq] at hh
    erw [representation_μ_gen] at hh
    change repApp η (X ⊗ Y) (gen (algebraMap ℚ A) 1 z.val) =
      gen (algebraMap ℚ A) (lineScalar A η m * lineScalar A η n) z.val at hh
    rw [acts_on_weight A η (X ⊗ Y) (m * n) z] at hh
    exact coefficient_injective A z.val hz hh

private def representationReconstruction (rules : WeightRules (r := r)) (A : Test) :
    Character r A ≃* Aut (representationFiber (r := r) A) :=
  MulEquiv.ofBijective (weightAut rules A) (by
    constructor
    · intro u v h
      apply MonoidHom.ext
      intro m
      apply Units.ext
      let w : weightSpace (line m).coaction m := ⟨1, line_weight m 1⟩
      have hh := congrArg (fun η : Aut (representationFiber (r := r) A) ↦
        repApp η (line m) (gen (algebraMap ℚ A) 1 w.val)) h
      change weightAction A u (line m) (gen (algebraMap ℚ A) 1 w.val) =
        weightAction A v (line m) (gen (algebraMap ℚ A) 1 w.val) at hh
      rw [weightAction_gen, weightAction_gen, mul_one, mul_one] at hh
      exact coefficient_injective A (X := ModuleCat.of ℚ ℚ) (1 : ℚ) one_ne_zero hh
    · intro η
      let u := (scalars rules A η).toHomUnits
      refine ⟨u, ?_⟩
      apply Aut.ext
      apply Iso.ext
      apply LaxMonoidalFunctor.hom_ext
      apply NatTrans.ext
      funext X
      apply extendedHom_ext_weights A X
      intro m v
      change weightAction A u X (gen (algebraMap ℚ A) 1 v.val) =
        repApp η X (gen (algebraMap ℚ A) 1 v.val)
      rw [weightAction_gen, mul_one, acts_on_weight A η X m v]
      rfl)

end MonoidalRepresentation

section Precomposition

variable {C D K : Type*} [Category C] [Category D] [Category K]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory K]
  (e : C ≌ D) [e.functor.Monoidal] (F : D ⥤ K) [F.LaxMonoidal]

/-- Whiskering along a monoidal equivalence preserves and reflects the group of
monoidal natural automorphisms. -/
private def precomposeAut : Aut (LaxMonoidalFunctor.of F) ≃*
    Aut (LaxMonoidalFunctor.of (e.functor ⋙ F)) := by
  let h : Aut (LaxMonoidalFunctor.of F) →* Aut (LaxMonoidalFunctor.of (e.functor ⋙ F)) :=
    { toFun := fun a ↦ by
        let i : F ≅ F :=
          { hom := a.asIso.hom.hom, inv := a.asIso.inv.hom
            hom_inv_id := congrArg LaxMonoidalFunctor.Hom.hom a.asIso.hom_inv_id
            inv_hom_id := congrArg LaxMonoidalFunctor.Hom.hom a.asIso.inv_hom_id }
        haveI : i.hom.IsMonoidal := a.asIso.hom.isMonoidal
        let j := Functor.isoWhiskerLeft e.functor i
        haveI : j.hom.IsMonoidal := by
          change (Functor.whiskerLeft e.functor i.hom).IsMonoidal
          infer_instance
        exact Aut.of (@LaxMonoidalFunctor.isoMk _ _ _ _ _ _ _ _ j this)
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  refine MulEquiv.ofBijective h ⟨?_, ?_⟩
  · intro a b hab
    apply Aut.ext
    apply Iso.ext
    apply LaxMonoidalFunctor.hom_ext
    exact ((whiskeringLeft C D K).obj e.functor).map_injective
      (congrArg (fun α : Aut (LaxMonoidalFunctor.of (e.functor ⋙ F)) ↦ α.asIso.hom.hom) hab)
  · intro a
    let := e.inverseMonoidal
    have : e.IsMonoidal := inferInstance
    let i : e.inverse ⋙ (e.functor ⋙ F) ≅ F :=
      (Functor.associator e.inverse e.functor F).symm ≪≫
        Functor.isoWhiskerRight e.counitIso F ≪≫ F.leftUnitor
    have : i.hom.IsMonoidal := by
      dsimp only [i, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom]
      infer_instance
    let j : LaxMonoidalFunctor.of (e.functor ⋙ F) ≅
        LaxMonoidalFunctor.of (e.functor ⋙ F) := a.asIso
    let a₀ : e.functor ⋙ F ≅ e.functor ⋙ F :=
      { hom := j.hom.hom, inv := j.inv.hom
        hom_inv_id := congrArg LaxMonoidalFunctor.Hom.hom j.hom_inv_id
        inv_hom_id := congrArg LaxMonoidalFunctor.Hom.hom j.inv_hom_id }
    have : a₀.hom.IsMonoidal := j.hom.isMonoidal
    let t := i.symm ≪≫ Functor.isoWhiskerLeft e.inverse a₀ ≪≫ i
    have ht : t.hom.IsMonoidal := by
      change (i.inv ≫ Functor.whiskerLeft e.inverse a₀.hom ≫ i.hom).IsMonoidal
      infer_instance
    refine ⟨Aut.of (@LaxMonoidalFunctor.isoMk _ _ _ _ _ _ _ _ t ht), ?_⟩
    apply Aut.ext
    apply Iso.ext
    apply LaxMonoidalFunctor.hom_ext
    apply NatTrans.ext
    funext X
    change t.hom.app (e.functor.obj X) = a₀.hom.app X
    have ih (Y : D) : i.hom.app Y = F.map (e.counitIso.hom.app Y) := by
      simp [i]
    have ii (Y : D) : i.inv.app Y = F.map (e.counitIso.inv.app Y) := by
      simp [i]
    simp only [t, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, ih, ii]
    rw [show e.counitIso.inv.app (e.functor.obj X) =
        e.functor.map (e.unitIso.hom.app X) from e.counitInv_app_functor X,
      show e.counitIso.hom.app (e.functor.obj X) =
        e.functor.map (e.unitIso.inv.app X) from e.counit_app_functor X]
    change (e.functor ⋙ F).map (e.unitIso.hom.app X) ≫
        a₀.hom.app (e.inverse.obj (e.functor.obj X)) ≫
        (e.functor ⋙ F).map (e.unitIso.inv.app X) = a₀.hom.app X
    rw [← Category.assoc]
    refine (congrArg (· ≫ (e.functor ⋙ F).map (e.unitIso.inv.app X))
      (a₀.hom.naturality (e.unitIso.hom.app X))).trans ?_
    rw [Category.assoc, ← Functor.map_comp]
    simp

end Precomposition

section Satake

variable {r : ℕ} {D : OrderedGeometry r} {g : StageGeometry r} {c : ContinuousJets r}
  {P : OrderedProduct D g c} {U : OrderedConstraints P} {σ : SwapsConvolution P}
  {S : SymmetricConvolution U σ}

private theorem satakeWeightRules (T : RepresentationTensor r) :
    letI := T.monoidal
    letI := T.symmetric
    letI := T.forgetBraided
    WeightRules (r := r) := by
  let := T.monoidal
  let := T.symmetric
  let := T.forgetBraided
  constructor
  · intro q
    exact (mem_weightSpace (ρ := (𝟙_ (Representations r)).coaction)).mpr (T.unitCoaction q)
  · intro X Y m n v w
    apply (mem_weightSpace (ρ := (X ⊗ Y).coaction)).mpr
    have hh := DFunLike.congr_fun (T.tensorCoaction X Y) (v.val ⊗ₜ[ℚ] w.val)
    change (X ⊗ Y).coaction.coaction ((μ (underlying r) X Y).hom (v.val ⊗ₜ[ℚ] w.val)) =
      ((μ (underlying r) X Y).hom.rTensor (coordinateAlgebra r))
        (tensorCoactionMap X.coaction Y.coaction (v.val ⊗ₜ[ℚ] w.val)) at hh
    refine hh.trans ?_
    simp [tensorCoactionMap, mem_weightSpace.mp v.property, mem_weightSpace.mp w.property,
      map_mul]
    rfl

private def satakeScaling (E : SatakeEquivalence S) (A : Test) :
    Character r A ≃* FiberAut E A := by
  letI := S.monoidal
  letI := S.symmetric
  letI := E.globalBraided
  let T := E.representationTensor
  letI := T.monoidal
  letI := T.symmetric
  letI := T.forgetBraided
  letI := E.braided
  haveI : E.fiberIso.hom.IsMonoidal := E.fiberIso_monoidal
  let F := E.equivalence.functor
  let i : (fiber E A).toFunctor ≅ F ⋙ (representationFiber (r := r) A).toFunctor :=
    Functor.isoWhiskerRight E.fiberIso (extend A) ≪≫ Functor.associator F (underlying r) (extend A)
  have h : i.hom.IsMonoidal := by
    change (Functor.whiskerRight E.fiberIso.hom (extend A) ≫
      (Functor.associator F (underlying r) (extend A)).hom).IsMonoidal
    infer_instance
  let j : fiber E A ≅ LaxMonoidalFunctor.of (F ⋙ (representationFiber (r := r) A).toFunctor) :=
    @LaxMonoidalFunctor.isoMk _ _ _ _ _ _ _ _ i h
  exact (representationReconstruction (satakeWeightRules T) A).trans
    ((precomposeAut E.equivalence (representationFiber (r := r) A).toFunctor).trans
      (Aut.autMulEquivOfIso j.symm))

private theorem satakeScaling_app (E : SatakeEquivalence S) (A : Test)
    (u : Character r A) (V : Heart r g c) :
    fiberApp E (satakeScaling E A u) V =
      (extend A).map (E.fiberIso.hom.app V) ≫ weightAction A u (E.equivalence.functor.obj V) ≫
        (extend A).map (E.fiberIso.inv.app V) := by
  let := S.monoidal
  dsimp [satakeScaling, precomposeAut, Aut.autMulEquivOfIso]
  rfl

private theorem satakeScaling_gen (E : SatakeEquivalence S) (A : Test)
    (u : Character r A) (V : Heart r g c) (m : Characters r)
    (v : weightSpace (E.equivalence.functor.obj V).coaction m) (b : A) :
    let x := E.fiberIso.inv.app V v.val
    fiberApp E (satakeScaling E A u) V (gen (algebraMap ℚ A) b x) =
      gen (algebraMap ℚ A) ((u m : A) * b) x := by
  dsimp only
  rw [satakeScaling_app, ModuleCat.comp_apply, ModuleCat.ExtendScalars.map_tmul]
  have h := ConcreteCategory.congr_hom (E.fiberIso.inv_hom_id_app V) v.val
  change E.fiberIso.hom.app V (E.fiberIso.inv.app V v.val) = v.val at h
  rw [h]
  change (extend A).map (E.fiberIso.inv.app V)
    (weightAction A u (E.equivalence.functor.obj V) (gen (algebraMap ℚ A) b v.val)) = _
  rw [weightAction_gen]
  rfl

private theorem coefficient_change {A B : Test} (f : A ⟶ B)
    (X : ModuleCat ℚ) (a : A) (x : X) :
    gen f.hom.toRingHom 1 (gen (algebraMap ℚ A) a x) =
      gen f.hom.toRingHom (f.hom a) (gen (algebraMap ℚ A) 1 x) := by
  have h : gen (algebraMap ℚ A) a x = a • gen (algebraMap ℚ A) 1 x := by
    rw [gen_smul, mul_one]
  rw [h]
  let := f.hom.toRingHom.toAlgebra
  change (1 : B) ⊗ₜ[A] (a • gen (algebraMap ℚ A) 1 x) =
    f.hom a ⊗ₜ[A] gen (algebraMap ℚ A) 1 x
  rw [← TensorProduct.smul_tmul]
  congr 1
  exact mul_one (f.hom a)

private theorem satakeScaling_change (E : SatakeEquivalence S) {A B : Test} (f : A ⟶ B)
    (u : Character r A) (V : Heart r g c) :
    fiberApp E (satakeScaling E B ((characterFunctor r).map f u)) V ≫
        (scalarComparison f).hom.app ((globalSections r g c).obj V) =
      (scalarComparison f).hom.app ((globalSections r g c).obj V) ≫
        (ModuleCat.extendScalars f.hom.toRingHom).map (fiberApp E (satakeScaling E A u) V) := by
  apply (cancel_epi ((extend B).map (E.fiberIso.inv.app V))).mp
  apply extendedHom_ext_weights B (E.equivalence.functor.obj V)
  intro m v
  let x := E.fiberIso.inv.app V v.val
  change (scalarComparison f).hom.app ((globalSections r g c).obj V)
      (fiberApp E (satakeScaling E B ((characterFunctor r).map f u)) V
        (gen (algebraMap ℚ B) 1 x)) =
    (ModuleCat.extendScalars f.hom.toRingHom).map (fiberApp E (satakeScaling E A u) V)
      ((scalarComparison f).hom.app ((globalSections r g c).obj V) (gen (algebraMap ℚ B) 1 x))
  erw [satakeScaling_gen E B ((characterFunctor r).map f u) V m v 1,
    scalar_naturality_gen, scalar_naturality_gen, ModuleCat.ExtendScalars.map_tmul,
    satakeScaling_gen E A u V m v 1]
  simp only [mul_one]
  exact (coefficient_change f _ (u m : A) x).symm

private def satakeScalarExtension (E : SatakeEquivalence S) : FiberScalarExtension E where
  map {A B} f :=
    (satakeScaling E B).toMonoidHom.comp
      (((characterFunctor r).map f).hom.comp (satakeScaling E A).symm.toMonoidHom)
  map_id A η := by
    change satakeScaling E A ((characterFunctor r).map (𝟙 A) ((satakeScaling E A).symm η)) = η
    have he := ConcreteCategory.congr_hom ((characterFunctor r).map_id A)
      ((satakeScaling E A).symm η)
    exact (congrArg (satakeScaling E A) he).trans ((satakeScaling E A).apply_symm_apply η)
  map_comp {A B C} f h η := by
    change satakeScaling E C ((characterFunctor r).map (f ≫ h) ((satakeScaling E A).symm η)) =
      satakeScaling E C ((characterFunctor r).map h
        ((satakeScaling E B).symm (satakeScaling E B
          ((characterFunctor r).map f ((satakeScaling E A).symm η)))))
    erw [Functor.map_comp, MulEquiv.symm_apply_apply]
    rfl
  comparison {A B} f η V := by
    obtain ⟨u, rfl⟩ := (satakeScaling E A).surjective η
    change fiberApp E (satakeScaling E B ((characterFunctor r).map f
      ((satakeScaling E A).symm (satakeScaling E A u)))) V ≫ _ = _
    rw [MulEquiv.symm_apply_apply]
    exact satakeScaling_change E f u V

private theorem reconstruct (E : SatakeEquivalence S) : Reconstruction E := by
  refine ⟨satakeScalarExtension E, satakeScaling E, pointsIso r, ?_, ?_, ?_⟩
  · intro A B f u
    change satakeScaling E B ((characterFunctor r).map f
      ((satakeScaling E A).symm (satakeScaling E A u))) = _
    rw [MulEquiv.symm_apply_apply]
  · intro A u V a x b
    exact satakeScaling_gen E A u V (Multiplicative.ofAdd a) x b
  · intro A u
    refine ⟨fun a ↦ MonoidAlgebra.lift_of _ _, ?_⟩
    rfl

end Satake

theorem dualTorusReconstruction_conditional :
    TorusSatake → DualTorusReconstruction := by
  intro hs r
  obtain ⟨_, D, g, c, P, U, σ, S, flips, geom, exchange, ⟨E⟩⟩ := hs r
  exact ⟨D, g, c, P, U, σ, S, flips, geom, exchange, E, reconstruct E⟩

end RepTheorySurvey.Geometric.DualTorusReconstruction

theorem _root_.«RepTheorySurvey».«Geometric».«DualTorusReconstruction».«dualTorusReconstruction» : _root_.«RepTheorySurvey».«Geometric».«DualTorusReconstructionSpecs».«DualTorusReconstruction» :=
  @_root_.«RepTheorySurvey».«Geometric».«DualTorusReconstruction».«dualTorusReconstruction_conditional» (@_root_.«RepTheorySurvey».«Geometric».«TorusSatake».«torusSatake»)
