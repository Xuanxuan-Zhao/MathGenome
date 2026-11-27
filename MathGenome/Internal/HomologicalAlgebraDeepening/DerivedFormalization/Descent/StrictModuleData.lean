import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.StrictModuleData
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.AmitsurAlgebras

/-! The category of strict module descent data and its ordered tensor identifications. -/

open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace DerivedFormalization.Descent.StrictModuleData

universe u v w z

noncomputable section

/-- The composition comparison sends the unit generator to the nested unit generator. -/
theorem extendComp_hom_one_tmul {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)
    (M : ModuleCat.{max u v w z} R) (x : M) :
    (StrictModuleDataSpec.extendComp.{max u v w z, u, v, w} f g).hom.app M
      ((1 : T) ⊗ₜ[R, g.comp f] x) =
      (1 : T) ⊗ₜ[S, g] (show (ModuleCat.extendScalars f).obj M from (1 : S) ⊗ₜ[R, f] x) := by
  have h :
      (ModuleCat.extendRestrictScalarsAdj.{max u v w z, u, w} (g.comp f)).homEquiv _ _
        ((StrictModuleDataSpec.extendComp.{max u v w z, u, v, w} f g).hom.app M) =
      (ModuleCat.extendRestrictScalarsAdj.{max u v w z, u, v} f).unit.app M ≫
        (ModuleCat.restrictScalars f).map
          ((ModuleCat.extendRestrictScalarsAdj.{max u v w z, v, w} g).unit.app _) ≫
        (ModuleCat.restrictScalarsComp f g).inv.app _ := by
    rw [Adjunction.homEquiv_unit, StrictModuleDataSpec.extendComp,
      conjugateIsoEquiv_symm_apply_hom, ← unit_conjugateEquiv_symm]
    simp only [Adjunction.comp_unit_app, Iso.symm_hom, Category.assoc]
    rfl
  refine (ModuleCat.extendRestrictScalarsAdj_homEquiv_apply.{max u v w z, u, w}
    ((StrictModuleDataSpec.extendComp.{max u v w z, u, v, w} f g).hom.app M) x).symm.trans ?_
  exact congrArg (fun k ↦ k x) h

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]

abbrev atPosition := @StrictModuleDataSpec.atPosition.{u, v, w} A B _ _ _
abbrev diagonal := StrictModuleDataSpec.diagonal A B
abbrev along := @StrictModuleDataSpec.along.{u, v, w} A B _ _ _
abbrev alongPosition := @StrictModuleDataSpec.alongPosition.{u, v, w} A B _ _ _
abbrev diagonalPosition := StrictModuleDataSpec.diagonalPosition.{u, v, w} A B
abbrev Theta := StrictModuleDataSpec.Theta.{u, v, w} A B
abbrev diagonalTheta := @StrictModuleDataSpec.diagonalTheta.{u, v, w} A B _ _ _
abbrev alongTheta := @StrictModuleDataSpec.alongTheta.{u, v, w} A B _ _ _
abbrev Datum := StrictModuleDataSpec.Datum.{u, v, w} A B
abbrev Hom := @StrictModuleDataSpec.Hom.{u, v, w} A B _ _ _

instance category : Category (Datum.{u, v, w} A B) :=
  StrictModuleDataSpec.category

abbrev forget := @StrictModuleDataSpec.forget.{u, v, w} A B _ _ _

open AmitsurAlgebras

/-- The binary tensor product in left-to-right order. -/
def binaryEquiv : B ⊗[A] B ≃ₐ[A] TensorPower A B 2 :=
  (Algebra.TensorProduct.congr (oneEquiv A B).symm (oneEquiv A B).symm).trans
    (appendEquiv A B 1 1)

@[simp] theorem binaryEquiv_tmul (a b : B) :
    binaryEquiv A B (a ⊗ₜ[A] b) = factor A B 0 a * factor A B 1 b := by
  simp only [binaryEquiv, AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, AlgEquiv.coe_toAlgHom]
  rw [appendEquiv_tmul, oneEquiv_symm_apply, oneEquiv_symm_apply, map_factor, map_factor]
  rfl

/-- The ternary tensor product in left-to-right order. -/
def ternaryEquiv : (B ⊗[A] B) ⊗[A] B ≃ₐ[A] TensorPower A B 3 :=
  (Algebra.TensorProduct.congr (binaryEquiv A B) (oneEquiv A B).symm).trans
    (appendEquiv A B 2 1)

@[simp] theorem ternaryEquiv_tmul (a b c : B) :
    ternaryEquiv A B ((a ⊗ₜ[A] b) ⊗ₜ[A] c) =
      factor A B 0 a * factor A B 1 b * factor A B 2 c := by
  simp only [ternaryEquiv, AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, AlgEquiv.coe_toAlgHom]
  rw [appendEquiv_tmul, binaryEquiv_tmul, oneEquiv_symm_apply, map_mul, map_factor,
    map_factor, map_factor]
  rfl

@[simp] theorem diagonal_factor (i : Fin 2) (b : B) :
    diagonal A B (factor A B i b) = b :=
  liftFactors_factor (fun _ ↦ AlgHom.id A B) i b

theorem orderedPowers : StrictModuleDataSpec.OrderedPowers.{u, v} := by
  intro A B _ _ _
  refine ⟨binaryEquiv A B, ternaryEquiv A B, binaryEquiv_tmul A B, ternaryEquiv_tmul A B,
    fun a b ↦ ?_, fun a b ↦ ?_⟩
  · change diagonal A B (binaryEquiv A B (a ⊗ₜ[A] b)) = a * b
    simp
  · let e := ternaryEquiv A B
    let bin := binaryEquiv A B (a ⊗ₜ[A] b)
    change map (StrictModuleDataSpec.pair 2) bin = e ((a ⊗ₜ[A] b) ⊗ₜ[A] 1) ∧
      map (StrictModuleDataSpec.pair 1) bin = e ((a ⊗ₜ[A] 1) ⊗ₜ[A] b) ∧
      map (StrictModuleDataSpec.pair 0) bin = e ((1 ⊗ₜ[A] a) ⊗ₜ[A] b)
    simp only [e, bin, binaryEquiv_tmul, ternaryEquiv_tmul, map_mul, map_factor, map_one,
      one_mul, mul_one]
    exact ⟨rfl, rfl, rfl⟩

abbrev restrict (N : ModuleCat.{max u v w} B) := StrictModuleDataSpec.restrict A B N

private instance (N : ModuleCat.{max u v w} B) : IsScalarTower A B (restrict A B N) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

open TensorProduct

/-- Reassociate extension of scalars when the extension ring is a binary tensor algebra
and the base acts in its first factor. -/
private def leftTensor {T : Type*} [CommRing T] [Algebra A T]
    (e : B ⊗[A] B ≃ₐ[A] T) (f : B →+* T) (h : ∀ b, e (b ⊗ₜ[A] 1) = f b)
    (N : ModuleCat.{max u v w} B) :
    ↑((ModuleCat.extendScalars f).obj N) ≃+ (restrict A B N ⊗[A] B) := by
  let D := (ModuleCat.restrictScalars f).obj (ModuleCat.of T T)
  let eLeft : B ⊗[A] B ≃ₗ[B] D :=
    { e.toAddEquiv with
      map_smul' := fun b z ↦ by
        change e (b • z) = f b * e z
        rw [Algebra.smul_def, map_mul, ← h b]
        rfl }
  let eTensor := TensorProduct.congr eLeft.symm (LinearEquiv.refl B (restrict A B N))
  let eComm := (AlgebraTensorModule.rightComm A B B B (restrict A B N) B).symm
  let eLid := AlgebraTensorModule.congr (TensorProduct.lid B (restrict A B N))
    (LinearEquiv.refl A B)
  exact (eTensor.trans (eComm.trans eLid)).toAddEquiv

private theorem leftTensor_symm_tmul {T : Type*} [CommRing T] [Algebra A T]
    (e : B ⊗[A] B ≃ₐ[A] T) (f : B →+* T) (h : ∀ b, e (b ⊗ₜ[A] 1) = f b)
    (N : ModuleCat.{max u v w} B) (b : B) (x : N) :
    (leftTensor A B e f h N).symm ((show restrict A B N from x) ⊗ₜ[A] b) = e (1 ⊗ₜ[A] b) ⊗ₜ[B,f] x :=
  rfl

/-- The first positioned module is `N ⊗[A] B`. -/
def firstTensor (N : ModuleCat.{max u v w} B) :
    ↑((atPosition A B (0 : Fin 2)).obj N) ≃+ (restrict A B N ⊗[A] B) :=
  leftTensor A B (binaryEquiv A B) (factor A B (0 : Fin 2)).toRingHom
    (fun b ↦ by simp) N

/-- The second positioned module is `B ⊗[A] N`. -/
def secondTensor (N : ModuleCat.{max u v w} B) :
    ↑((atPosition A B (1 : Fin 2)).obj N) ≃+ (B ⊗[A] restrict A B N) :=
  (leftTensor A B ((Algebra.TensorProduct.comm A B B).trans (binaryEquiv A B))
    (factor A B (1 : Fin 2)).toRingHom (fun b ↦ by simp) N).trans
      (TensorProduct.comm A (restrict A B N) B).toAddEquiv

@[simp] theorem firstTensor_symm_tmul (N : ModuleCat.{max u v w} B) (b : B) (x : N) :
    (firstTensor A B N).symm ((show restrict A B N from x) ⊗ₜ[A] b) =
      factor A B (1 : Fin 2) b ⊗ₜ[B, (factor A B (0 : Fin 2)).toRingHom] x := by
  calc
    _ = binaryEquiv A B (1 ⊗ₜ[A] b) ⊗ₜ[B, (factor A B (0 : Fin 2)).toRingHom] x :=
      leftTensor_symm_tmul A B _ _ _ N b x
    _ = _ := by rw [binaryEquiv_tmul, map_one, one_mul]

@[simp] theorem secondTensor_symm_tmul (N : ModuleCat.{max u v w} B) (b : B) (x : N) :
    (secondTensor A B N).symm (b ⊗ₜ[A] (show restrict A B N from x)) =
      factor A B (0 : Fin 2) b ⊗ₜ[B, (factor A B (1 : Fin 2)).toRingHom] x := by
  calc
    _ = ((Algebra.TensorProduct.comm A B B).trans (binaryEquiv A B)) (1 ⊗ₜ[A] b)
        ⊗ₜ[B, (factor A B (1 : Fin 2)).toRingHom] x :=
      leftTensor_symm_tmul A B _ _ (fun b ↦ by simp) N b x
    _ = _ := by rw [AlgEquiv.trans_apply, Algebra.TensorProduct.comm_tmul, binaryEquiv_tmul,
      map_one, mul_one]

theorem binaryModuleModels : StrictModuleDataSpec.BinaryModuleModels.{u, v, w} := by
  intro A B _ _ _ N
  refine ⟨firstTensor A B N, secondTensor A B N, firstTensor_symm_tmul A B N,
    secondTensor_symm_tmul A B N, ?_, ?_⟩
  · intro a b c x
    apply (firstTensor A B N).symm.injective
    simp only [AddEquiv.symm_apply_apply, firstTensor_symm_tmul]
    let f := (factor A B (0 : Fin 2)).toRingHom
    let D := (ModuleCat.restrictScalars f).obj (ModuleCat.of (TensorPower A B 2) (TensorPower A B 2))
    change (show D from (factor A B 0 a * factor A B 1 b) * factor A B 1 c) ⊗ₜ[B] x =
      (show D from factor A B 1 (b * c)) ⊗ₜ[B] (a • x)
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    change ((factor A B 0 a * factor A B 1 b) * factor A B 1 c) ⊗ₜ[B,f] x =
      (factor A B 0 a * factor A B 1 (b * c)) ⊗ₜ[B,f] x
    rw [map_mul]
    exact congrArg (fun z : TensorPower A B 2 ↦ (show D from z) ⊗ₜ[B] x) (mul_assoc _ _ _)
  · intro a b c x
    apply (secondTensor A B N).symm.injective
    simp only [AddEquiv.symm_apply_apply, secondTensor_symm_tmul]
    let f := (factor A B (1 : Fin 2)).toRingHom
    let D := (ModuleCat.restrictScalars f).obj (ModuleCat.of (TensorPower A B 2) (TensorPower A B 2))
    change (show D from (factor A B 0 a * factor A B 1 b) * factor A B 0 c) ⊗ₜ[B] x =
      (show D from factor A B 0 (a * c)) ⊗ₜ[B] (b • x)
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    change ((factor A B 0 a * factor A B 1 b) * factor A B 0 c) ⊗ₜ[B,f] x =
      (factor A B 1 b * factor A B 0 (a * c)) ⊗ₜ[B,f] x
    rw [map_mul]
    have he : (factor A B (0 : Fin 2) a * factor A B (1 : Fin 2) b) * factor A B (0 : Fin 2) c =
        factor A B (1 : Fin 2) b * (factor A B (0 : Fin 2) a * factor A B (0 : Fin 2) c) :=
      (congrArg (· * factor A B 0 c) (mul_comm _ _)).trans (mul_assoc _ _ _)
    exact congrArg (fun z : TensorPower A B 2 ↦ (show D from z) ⊗ₜ[B] x) he

end

end DerivedFormalization.Descent.StrictModuleData
