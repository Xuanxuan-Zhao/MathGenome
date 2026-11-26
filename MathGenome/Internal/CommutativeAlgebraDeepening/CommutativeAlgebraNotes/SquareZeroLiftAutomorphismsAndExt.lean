import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.SquareZeroLiftTorsor
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.SquareZeroLiftAutomorphismsAndExt
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

noncomputable section

namespace CommutativeAlgebraNotes.SquareZeroLift.Lift

universe u v w n l m
variable {A' : Type u} {A : Type v} {B : Type w} {N : Type n}
  [CommRing A'] [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup N] [Module B N] {e : BaseExtension A' A}
  {c : e.CoefficientMap (B := B) N} (L : Lift.{u,v,w,n,l} e c)

local notation "Der" => @Derivation A B N _ _ _ _ _ (Module.compHom N (algebraMap A B))

private theorem inclusion_injective : Function.Injective L.coefficientInclusion :=
  Subtype.val_injective.comp L.marking.symm.injective

@[simp] private theorem map_inclusion (y : N) : L.map (L.coefficientInclusion y) = 0 :=
  (L.marking.symm y).property

private theorem inclusion_smul (x : L.Ring) (y : N) :
    L.coefficientInclusion (L.map x • y) = x * L.coefficientInclusion y :=
  congrArg Subtype.val
    ((L.marking.symm.map_smul (L.map x) y).trans (L.map_smul x (L.marking.symm y)))

private theorem inclusion_mul_inclusion (x y : N) :
    L.coefficientInclusion x * L.coefficientInclusion y = 0 := by
  rw [← L.inclusion_smul, L.map_inclusion, zero_smul, map_zero]

private def translate (d : Der) : L.Ring →ₐ[A'] L.Ring where
  toFun x := x + L.coefficientInclusion (d (L.map x))
  map_one' := by simp [Derivation.map_one_eq_zero]
  map_zero' := by simp
  map_add' x y := by simp only [map_add]; abel
  map_mul' x y := by
    simp only [map_mul, Derivation.leibniz, map_add, L.inclusion_smul, add_mul, mul_add,
      L.inclusion_mul_inclusion, add_zero]
    rw [mul_comm (L.coefficientInclusion (d (L.map x))) y]
    abel
  commutes' a := by simp [L.over, Derivation.map_algebraMap]

@[simp] private theorem translate_apply (d : Der) (x : L.Ring) :
    L.translate d x = x + L.coefficientInclusion (d (L.map x)) := rfl

@[simp] private theorem map_translate (d : Der) (x : L.Ring) :
    L.map (L.translate d x) = L.map x := by simp

private theorem translate_add (d g : Der) (x : L.Ring) :
    L.translate (d + g) x = L.translate d (L.translate g x) := by
  conv_rhs => rw [L.translate_apply, L.map_translate, L.translate_apply]
  simp only [translate_apply, Derivation.add_apply, map_add]
  abel

private def ofDerivation (d : Der) : L.markedAutomorphisms :=
  ⟨AlgEquiv.ofAlgHom (L.translate d) (L.translate (-d))
      (by ext x; change L.translate d (L.translate (-d) x) = x
          rw [← L.translate_add, add_neg_cancel]; simp)
      (by ext x; change L.translate (-d) (L.translate d x) = x
          rw [← L.translate_add, neg_add_cancel]; simp),
    L.map_translate d, fun x => by change L.translate d x = x; simp [RingHom.mem_ker.mp x.property]⟩

private theorem ofDerivation_apply (d : Der) (x : L.Ring) :
    (L.ofDerivation d).val x = x + L.coefficientInclusion (d (L.map x)) := rfl

private def difference (f : L.markedAutomorphisms) : L.Ring →+ N where
  toFun x := L.marking ⟨f.val x - x, by rw [RingHom.mem_ker, map_sub, f.property.1, sub_self]⟩
  map_zero' := by
    rw [show (⟨f.val 0 - 0, _⟩ : L.ker) = 0 from Subtype.ext (by simp)]
    exact map_zero _
  map_add' x y := by
    rw [← map_add]
    congr 1
    apply Subtype.ext
    change f.val (x + y) - (x + y) = (f.val x - x) + (f.val y - y)
    rw [map_add]
    abel

private theorem inclusion_difference (f : L.markedAutomorphisms) (x : L.Ring) :
    L.coefficientInclusion (L.difference f x) = f.val x - x :=
  congrArg Subtype.val (L.marking.symm_apply_apply _)

private theorem difference_eq_of_map_eq (f : L.markedAutomorphisms) {x y : L.Ring}
    (h : L.map x = L.map y) : L.difference f x = L.difference f y := by
  have hk := f.property.2 (⟨x - y, by rw [RingHom.mem_ker, map_sub, h, sub_self]⟩ : L.ker)
  change f.val (x - y) = x - y at hk
  rw [map_sub] at hk
  apply L.inclusion_injective
  rw [L.inclusion_difference, L.inclusion_difference]
  calc
    _ = (f.val x - f.val y) + (f.val y - x) := by abel
    _ = _ := by rw [hk]; abel

private def descend (f : L.markedAutomorphisms) (b : B) : N :=
  L.difference f (L.surjective b).choose

private theorem descend_map (f : L.markedAutomorphisms) (x : L.Ring) :
    L.descend f (L.map x) = L.difference f x :=
  L.difference_eq_of_map_eq f (L.surjective (L.map x)).choose_spec

private theorem descend_mul (f : L.markedAutomorphisms) (a b : B) :
    L.descend f (a * b) = a • L.descend f b + b • L.descend f a := by
  obtain ⟨x, rfl⟩ := L.surjective a
  obtain ⟨y, rfl⟩ := L.surjective b
  apply L.inclusion_injective
  rw [← map_mul L.map, L.descend_map, L.descend_map, L.descend_map,
    map_add, L.inclusion_smul, L.inclusion_smul, L.inclusion_difference, map_mul]
  have hx : f.val x = x + L.coefficientInclusion (L.difference f x) := by
    rw [L.inclusion_difference, add_sub_cancel]
  have hy : f.val y = y + L.coefficientInclusion (L.difference f y) := by
    rw [L.inclusion_difference, add_sub_cancel]
  rw [hx, hy, add_mul, mul_add, mul_add, L.inclusion_mul_inclusion, add_zero]
  rw [mul_comm (L.coefficientInclusion (L.difference f x)) y]
  abel

private theorem descend_algebraMap (f : L.markedAutomorphisms) (a : A) :
    L.descend f (algebraMap A B a) = 0 := by
  obtain ⟨a, rfl⟩ := e.surjective a
  rw [← L.over, L.descend_map]
  apply L.inclusion_injective
  rw [L.inclusion_difference, map_zero, AlgEquiv.commutes, sub_self]

private def toDerivation (f : L.markedAutomorphisms) : Der := by
  letI : Module A N := Module.compHom N (algebraMap A B)
  exact Derivation.mk'
    { toFun := L.descend f
      map_add' := by
        intro x y
        obtain ⟨x, rfl⟩ := L.surjective x
        obtain ⟨y, rfl⟩ := L.surjective y
        rw [← map_add, L.descend_map, L.descend_map, L.descend_map, map_add]
      map_smul' := by
        intro a b
        rw [Algebra.smul_def]
        change L.descend f (algebraMap A B a * b) = algebraMap A B a • L.descend f b
        rw [L.descend_mul, L.descend_algebraMap, smul_zero, add_zero] }
    (L.descend_mul f)

/-- Translation of a marked lift by a derivation, with composition as the group law. -/
def derivationEquiv : Multiplicative Der ≃* L.markedAutomorphisms where
  toFun d := L.ofDerivation d.toAdd
  invFun f := Multiplicative.ofAdd (L.toDerivation f)
  left_inv d := by
    let : Module A N := Module.compHom N (algebraMap A B)
    change Multiplicative.ofAdd (L.toDerivation (L.ofDerivation d.toAdd)) = d
    apply congrArg Multiplicative.ofAdd
    apply Derivation.ext
    intro b
    obtain ⟨x, rfl⟩ := L.surjective b
    change L.descend (L.ofDerivation d.toAdd) (L.map x) = d.toAdd (L.map x)
    rw [L.descend_map]
    apply L.inclusion_injective
    rw [L.inclusion_difference, L.ofDerivation_apply, add_sub_cancel_left]
  right_inv f := by
    apply Subtype.ext
    ext x
    change (L.ofDerivation (L.toDerivation f)).val x = f.val x
    rw [L.ofDerivation_apply]
    change x + L.coefficientInclusion (L.descend f (L.map x)) = f.val x
    rw [L.descend_map, L.inclusion_difference, add_sub_cancel]
  map_mul' d g := by
    apply Subtype.ext
    ext x
    exact L.translate_add d.toAdd g.toAdd x

theorem derivationEquiv_apply (d : Multiplicative Der) (x : L.Ring) :
    (L.derivationEquiv d).val x = x + L.coefficientInclusion (d.toAdd (L.map x)) := rfl

theorem derivationEquiv_natural {M : Lift.{u,v,w,n,m} e c} (f : L.Iso M)
    (d : Multiplicative Der) (x : L.Ring) :
    f.equiv ((L.derivationEquiv d).val x) = (M.derivationEquiv d).val (f.equiv x) := by
  rw [L.derivationEquiv_apply, M.derivationEquiv_apply, map_add, f.over]
  congr 1
  have h := f.marked (L.marking.symm (d.toAdd (L.map x)))
  rw [L.marking.apply_symm_apply] at h
  exact congrArg Subtype.val (M.marking.symm_apply_eq.mpr h.symm).symm

end CommutativeAlgebraNotes.SquareZeroLift.Lift

namespace CommutativeAlgebraNotes.SquareZeroLift

open Specs.CommutativeAlgebraNotes.SquareZeroLiftAutomorphismsAndExt

universe u v w t n l

/-- Marked automorphisms act by the derivation of the residue, naturally in the lift. -/
theorem automorphisms : automorphismsType.{u,v,w,n,l} := by
  intro A' A B N _ _ _ _ _ _ e c
  exact ⟨Lift.derivationEquiv, Lift.derivationEquiv_apply,
    fun L _ f => L.derivationEquiv_natural f⟩

theorem liftTorsor : torsorType.{u,v,w,t,n,l} := Presentation.torsor

end CommutativeAlgebraNotes.SquareZeroLift

namespace CommutativeAlgebraNotes.SquareZeroLift.Presentation

open CategoryTheory Category Limits Pretriangulated
open Specs.CommutativeAlgebraNotes.SquareZeroLiftAutomorphismsAndExt
open scoped CategoryTheory

section Derived

universe r k j
variable {R : Type r} [CommRing R] [HasDerivedCategory.{j} (ModuleCat.{k} R)]
  {X Y M : ModuleCat.{k} R}

private abbrev shiftedSingleFunctor (R : Type r) [CommRing R]
    [HasDerivedCategory.{j} (ModuleCat.{k} R)] :=
  DerivedCategory.singleFunctor (ModuleCat.{k} R) 0 ⋙ shiftFunctor _ (1 : ℤ)

open HomologicalComplex CochainComplex

private def doubleIsoCone (d : X ⟶ Y) :
    twoTermComplex d ≅ mappingCone (degreeZeroMap d) := by
  let f := degreeZeroMap d
  let K := (CochainComplex.singleFunctor (ModuleCat.{k} R) 0).obj X
  let L := (CochainComplex.singleFunctor (ModuleCat.{k} R) 0).obj Y
  have hK (i : ℤ) (hi : i ≠ 0) : IsZero (K.X i) :=
    isZero_single_obj_X _ _ _ _ hi
  have hL (i : ℤ) (hi : i ≠ 0) : IsZero (L.X i) :=
    isZero_single_obj_X _ _ _ _ hi
  let a := (mappingCone.inl f).v 0 (-1) (by decide)
  let b := (mappingCone.inr f).f 0
  have ha : IsIso a := by
    refine ⟨⟨(mappingCone.fst f).1.v (-1) 0 (by decide),
      mappingCone.inl_v_fst_v f 0 (-1) (by decide), ?_⟩⟩
    have h := mappingCone.id_X f (-1) 0 (by decide)
    have hz : (mappingCone.inr f).f (-1) = 0 := (hL (-1) (by decide)).eq_of_src _ _
    rw [hz, comp_zero, add_zero] at h
    exact h
  have hb : IsIso b := by
    refine ⟨⟨(mappingCone.snd f).v 0 0 (by decide),
      mappingCone.inr_f_snd_v f 0, ?_⟩⟩
    have h := mappingCone.id_X f 0 1 (by decide)
    have hz : (mappingCone.inl f).v 1 0 (by decide) = 0 := (hK 1 (by decide)).eq_of_src _ _
    rw [hz, comp_zero, zero_add] at h
    exact h
  let eX := singleObjXSelf (ComplexShape.up ℤ) 0 X
  let eY := singleObjXSelf (ComplexShape.up ℤ) 0 Y
  have comm : (eX.inv ≫ a) ≫ (mappingCone f).d (-1) 0 = d ≫ eY.inv ≫ b := by
    have h := mappingCone.inl_v_d f 0 (-1) 1 (by decide) (by decide)
    have hz : K.d 0 1 = 0 := (hK 1 (by decide)).eq_of_tgt _ _
    change a ≫ (mappingCone f).d (-1) 0 = f.f 0 ≫ b -
      K.d 0 1 ≫ (mappingCone.inl f).v 1 0 (by decide) at h
    rw [hz, zero_comp, sub_zero] at h
    have hd : f.f 0 = eX.hom ≫ d ≫ eY.inv :=
      single_map_f_self (ComplexShape.up ℤ) 0 d
    rw [Category.assoc, h, hd]
    simp
  let q : twoTermComplex d ⟶ mappingCone f :=
    mkHomFromDouble (by decide) (by decide) (eX.inv ≫ a) (eY.inv ≫ b) comm
      (fun i hi => by
        apply ((mappingCone.isZero_X_iff f i).2 ⟨hK _ (by
          change 0 + 1 = i at hi
          omega), hL _ (by
          change 0 + 1 = i at hi
          omega)⟩).eq_of_tgt)
  letI : ∀ i, IsIso (q.f i) := fun i => by
    by_cases h₀ : i = -1
    · subst i
      dsimp only [q]
      rw [mkHomFromDouble_f₀]
      infer_instance
    by_cases h₁ : i = 0
    · subst i
      dsimp only [q]
      rw [mkHomFromDouble_f₁]
      infer_instance
    exact (isZero_double_X d (by decide) i h₀ h₁).isIso
      ((mappingCone.isZero_X_iff f i).2 ⟨hK _ (by omega), hL _ h₁⟩) _
  letI := HomologicalComplex.Hom.isIso_of_components q
  exact asIso q

private theorem coneTriangle_distinguished (d : X ⟶ Y) :
    coneTriangle d ∈ distTriang _ :=
  DerivedCategory.mappingCone_triangle_distinguished _

private theorem shiftedSingle_vanish [Projective Y]
    (f : (DerivedCategory.singleFunctor _ 0).obj Y ⟶ (shiftedSingleFunctor R).obj M) :
    f = 0 := by
  let e := ((DerivedCategory.singleFunctors (ModuleCat.{k} R)).shiftIso 1 (-1) 0 (by decide)).app M
  rw [← cancel_mono e.hom, zero_comp]
  exact DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective (f ≫ e.hom) (-1) (by decide)

private theorem coneClass_surjective (d : X ⟶ Y) [Projective Y] :
    Function.Surjective (fun f : X ⟶ M => (coneTriangle d).mor₃ ≫ shiftedSingleMap f) := by
  intro a
  have h : (coneTriangle d).mor₂ ≫ a = 0 := shiftedSingle_vanish _
  obtain ⟨b, hb⟩ := Triangle.yoneda_exact₃ _ (coneTriangle_distinguished d) a h
  obtain ⟨f, rfl⟩ := (shiftedSingleFunctor R).map_surjective b
  exact ⟨f, hb.symm⟩

private theorem coneClass_eq_zero_iff (d : X ⟶ Y) (f : X ⟶ M) :
    (coneTriangle d).mor₃ ≫ shiftedSingleMap f = 0 ↔ ∃ g : Y ⟶ M, f = d ≫ g := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := Triangle.yoneda_exact₂ (coneTriangle d).rotate.rotate
      (rot_of_distTriang _ (rot_of_distTriang _ (coneTriangle_distinguished d)))
      (shiftedSingleMap f) h
    obtain ⟨g, rfl⟩ := (shiftedSingleFunctor R).map_surjective b
    refine ⟨-g, (shiftedSingleFunctor R).map_injective ?_⟩
    change shiftedSingleMap f = (shiftedSingleFunctor R).map (d ≫ (-g))
    rw [Functor.map_comp, Functor.map_neg, Preadditive.comp_neg]
    change shiftedSingleMap f =
      (-((shiftedSingleFunctor R).map d)) ≫ (shiftedSingleFunctor R).map g at hb
    rw [Preadditive.neg_comp] at hb
    exact hb
  · rintro ⟨g, rfl⟩
    change (coneTriangle d).mor₃ ≫ (shiftedSingleFunctor R).map (d ≫ g) = 0
    rw [Functor.map_comp]
    have hzero : (coneTriangle d).mor₃ ≫ (shiftedSingleFunctor R).map d = 0 :=
      comp_distTriang_mor_zero₃₁ _ (coneTriangle_distinguished d)
    calc
      _ = ((coneTriangle d).mor₃ ≫ (shiftedSingleFunctor R).map d) ≫
          (shiftedSingleFunctor R).map g := (Category.assoc _ _ _).symm
      _ = 0 := by rw [hzero, zero_comp]

end Derived

section Presentation

universe u v w t n
variable {A' : Type u} {A : Type v} {B : Type w} {σ : Type t} {N : Type n}
  [CommRing A'] [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup N] [Module B N] {e : BaseExtension A' A} (p : Presentation e B σ)

open Algebra.Extension

private theorem differential_free : Module.Free B p.barExtension.CotangentSpace := by
  let E : p.barExtension.Ring ≃ₐ[A] MvPolynomial σ A := p.barPolynomialEquiv
  let P := Algebra.Extension.ofSurjective (p.barMap.comp E.symm.toAlgHom)
    (p.barMap_surjective.comp E.symm.surjective)
  let f : p.barExtension.Hom P :=
    { toRingHom := E.toRingEquiv.toRingHom
      toRingHom_algebraMap a := E.commutes a
      algebraMap_toRingHom x := by
        change p.barMap (E.symm (E x)) = p.barMap x
        rw [E.symm_apply_apply] }
  let g : P.Hom p.barExtension :=
    { toRingHom := E.symm.toRingEquiv.toRingHom
      toRingHom_algebraMap a := E.symm.commutes a
      algebraMap_toRingHom _ := rfl }
  have h₁ : g.comp f = .id _ := by
    apply Algebra.Extension.Hom.ext
    ext x
    exact E.symm_apply_apply x
  have h₂ : f.comp g = .id _ := by
    apply Algebra.Extension.Hom.ext
    ext x
    exact E.apply_symm_apply x
  let equiv : p.barExtension.CotangentSpace ≃ₗ[B] P.CotangentSpace :=
    { __ := CotangentSpace.map f
      invFun := CotangentSpace.map g
      left_inv := fun x => by
        change CotangentSpace.map g (CotangentSpace.map f x) = x
        rw [← CotangentSpace.map_comp_apply, h₁, CotangentSpace.map_id, LinearMap.id_apply]
      right_inv := fun x => by
        change CotangentSpace.map f (CotangentSpace.map g x) = x
        rw [← CotangentSpace.map_comp_apply, h₂, CotangentSpace.map_id, LinearMap.id_apply] }
  let : Algebra (MvPolynomial σ A) B := (p.barMap.comp E.symm.toAlgHom).toAlgebra
  let : Module.Free B P.CotangentSpace :=
    Module.Free.of_basis ((KaehlerDifferential.mvPolynomialBasis A σ).baseChange
      (R := MvPolynomial σ A) B)
  exact Module.Free.of_equiv equiv.symm

private theorem liftHomEquiv_precomp
    (g : p.barExtension.CotangentSpace →ₗ[B] N) :
    (conormalHomEquiv p (conormalRestriction p N g)) = conormalDifferential.{u,v,w,t,n} p ≫ differentialHomEquiv p g := by
  apply ModuleCat.hom_ext
  ext x
  rfl

private theorem derivedExtComparison : DerivedExtComparison p (N := N) := by
  let := HasDerivedCategory.standard (ModuleCat.{max u w t n} B)
  let d := conormalDifferential.{u,v,w,t,n} p
  let T := coneTriangle d
  let M := coefficientObject.{w,n,max u t} B N
  let W := (shiftedSingleFunctor B).obj M
  let φ : (p.BarConormal →ₗ[B] N) →ₗ[B] (T.obj₃ ⟶ W) :=
    ((CategoryTheory.Linear.leftComp B W T.mor₃).comp
      ((shiftedSingleFunctor B).mapLinearMap B)).comp (conormalHomEquiv p (N := N)).toLinearMap
  have hφ (g : p.BarConormal →ₗ[B] N) : φ g = T.mor₃ ≫ shiftedSingleMap (conormalHomEquiv p g) := rfl
  have hsurj : Function.Surjective φ := by
    let := p.differential_free
    let : Projective (differentialObject.{u,v,w,t,n} p) :=
      ModuleCat.projective_of_categoryTheory_projective _
    exact (coneClass_surjective (M := M) d).comp (conormalHomEquiv p (N := N)).surjective
  have hker : (conormalRestriction p N).range = LinearMap.ker φ := by
    ext g
    rw [LinearMap.mem_range, LinearMap.mem_ker, hφ, coneClass_eq_zero_iff]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨differentialHomEquiv p a, p.liftHomEquiv_precomp a⟩
    · rintro ⟨a, ha⟩
      obtain ⟨b, rfl⟩ := (differentialHomEquiv p (N := N)).surjective a
      refine ⟨b, (conormalHomEquiv p (N := N)).injective ?_⟩
      exact (p.liftHomEquiv_precomp b).trans ha.symm
  let E := (Submodule.quotEquivOfEq _ _ hker).trans (φ.quotKerEquivOfSurjective hsurj)
  have hE (g : p.BarConormal →ₗ[B] N) :
      E ((conormalRestriction p N).range.mkQ g) =
        T.mor₃ ≫ shiftedSingleMap (conormalHomEquiv p g) := by
    change φ.quotKerEquivOfSurjective hsurj
      (Submodule.quotEquivOfEq _ _ hker (Submodule.Quotient.mk g)) = _
    rw [Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
    exact hφ g
  let i := doubleIsoCone d
  let I : DerivedCategory.Q.obj (twoTermComplex d) ≅ T.obj₃ := DerivedCategory.Q.mapIso i
  refine ⟨i, E.trans (CategoryTheory.Linear.homCongr B I.symm (Iso.refl W)), ?_⟩
  intro g
  change (I.hom ≫ E ((conormalRestriction p N).range.mkQ g)) ≫ 𝟙 W =
    I.hom ≫ T.mor₃ ≫ shiftedSingleMap (conormalHomEquiv p g)
  rw [comp_id, hE]

/-- The conormal cokernel computes first derived Ext of the two-term complex. -/
theorem derivedExt : derivedExtType.{u,v,w,t,n} := by
  intro A' A B σ N _ _ _ _ _ _ e p
  exact derivedExtComparison p

end Presentation

end CommutativeAlgebraNotes.SquareZeroLift.Presentation
