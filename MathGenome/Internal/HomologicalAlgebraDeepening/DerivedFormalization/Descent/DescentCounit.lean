import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.DescentCounit
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.StrictModuleData

/-! The equalizer construction for strict module descent along a flat algebra. -/

open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace DerivedFormalization.Descent.DescentCounit

open StrictModuleData AmitsurAlgebras TensorProduct
open DescentCounitSpec (generator generator_add generator_smul baseChangePosition)

universe u v r s t w

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 700000

section ScalarExtension

variable {R : Type r} {S : Type s} {T : Type t}
  [CommRing R] [CommRing S] [CommRing T]

private theorem extend_smul_tmul (f : R →+* S) (M : ModuleCat.{w} R)
    (a b : S) (x : M) :
    a • (b ⊗ₜ[R,f] x : (ModuleCat.extendScalars f).obj M) = (a * b) ⊗ₜ[R,f] x :=
  rfl

private theorem extend_tmul_smul (f : R →+* S) (M : ModuleCat.{w} R)
    (a : S) (b : R) (x : M) :
    a ⊗ₜ[R,f] (b • x) = (a * f b) ⊗ₜ[R,f] x := by
  let D := (ModuleCat.restrictScalars f).obj (ModuleCat.of S S)
  change (show D from a) ⊗ₜ[R] (b • x) = _
  rw [tmul_smul, smul_tmul']
  change (f b * a) ⊗ₜ[R,f] x = _
  rw [mul_comm]

private theorem extendCongr_hom_tmul {f g : R →+* S} (h : f = g)
    (M : ModuleCat.{w} R) (a : S) (x : M) :
    (StrictModuleDataSpec.extendCongr h).hom.app M (a ⊗ₜ[R,f] x) =
      a ⊗ₜ[R,g] x := by
  subst h
  rfl

private theorem extendCongr_inv_tmul {f g : R →+* S} (h : f = g)
    (M : ModuleCat.{w} R) (a : S) (x : M) :
    (StrictModuleDataSpec.extendCongr h).inv.app M (a ⊗ₜ[R,g] x) =
      a ⊗ₜ[R,f] x := by
  subst h
  rfl

private theorem extendComp_hom_tmul (f : R →+* S) (g : S →+* T)
    (M : ModuleCat.{max r s t w} R) (a : T) (x : M) :
    (StrictModuleDataSpec.extendComp.{max r s t w,r,s,t} f g).hom.app M
      (a ⊗ₜ[R, g.comp f] x) =
      a ⊗ₜ[S,g] (show (ModuleCat.extendScalars f).obj M from (1 : S) ⊗ₜ[R,f] x) := by
  let e := (StrictModuleDataSpec.extendComp.{max r s t w,r,s,t} f g).hom.app M
  let y : (ModuleCat.extendScalars f).obj M := (1 : S) ⊗ₜ[R,f] x
  calc
    e (a ⊗ₜ[R,g.comp f] x) = e (a • ((1 : T) ⊗ₜ[R,g.comp f] x :
        (ModuleCat.extendScalars (g.comp f)).obj M)) := by
      rw [extend_smul_tmul (g.comp f) M]
      exact congrArg (fun b : T ↦ e (b ⊗ₜ[R,g.comp f] x)) (mul_one a).symm
    _ = a • e ((1 : T) ⊗ₜ[R,g.comp f] x) := map_smul _ _ _
    _ = a • ((1 : T) ⊗ₜ[S,g] y : (ModuleCat.extendScalars g).obj _) := by
      rw [show e ((1 : T) ⊗ₜ[R,g.comp f] x) = (1 : T) ⊗ₜ[S,g] y from
        extendComp_hom_one_tmul.{r,s,t,w} f g M x]
    _ = a ⊗ₜ[S,g] y := by
      rw [extend_smul_tmul g (ModuleCat.extendScalars f |>.obj M)]
      exact congrArg (fun c : T ↦ c ⊗ₜ[S,g] y) (mul_one a)

private theorem extendComp_inv_tmul (f : R →+* S) (g : S →+* T)
    (M : ModuleCat.{max r s t w} R) (a : T) (b : S) (x : M) :
    (StrictModuleDataSpec.extendComp.{max r s t w,r,s,t} f g).inv.app M
      (a ⊗ₜ[S,g] (show (ModuleCat.extendScalars f).obj M from b ⊗ₜ[R,f] x)) =
      (a * g b) ⊗ₜ[R,g.comp f] x := by
  let e := (StrictModuleDataSpec.extendComp.{max r s t w,r,s,t} f g).app M
  apply e.toLinearEquiv.injective
  change e.hom (e.inv _) = e.hom _
  rw [← ModuleCat.comp_apply, e.inv_hom_id, ModuleCat.id_apply]
  let M' := (ModuleCat.extendScalars f).obj M
  let y : M' := (1 : S) ⊗ₜ[R,f] x
  have hy : b • y = (b ⊗ₜ[R,f] x : M') :=
    (extend_smul_tmul f M b 1 x).trans
      (congrArg (fun c : S ↦ c ⊗ₜ[R,f] x) (mul_one b))
  calc
    _ = a ⊗ₜ[S,g] (b • y) :=
      congrArg (fun z : M' ↦ a ⊗ₜ[S,g] z) hy.symm
    _ = (a * g b) ⊗ₜ[S,g] y := extend_tmul_smul g M' a b y
    _ = _ := (extendComp_hom_tmul.{r,s,t,w} f g M (a * g b) x).symm

end ScalarExtension

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

abbrev invariants := @DescentCounitSpec.invariants.{u,v,w} A B _ _ _
abbrev descend := @DescentCounitSpec.descend.{u,v,w} A B _ _ _
abbrev baseChangeTheta := @DescentCounitSpec.baseChangeTheta.{u,v,w} A B _ _ _
abbrev counitMap := @DescentCounitSpec.counitMap.{u,v,w} A B _ _ _

private theorem alongFactor {m n : ℕ} (f : Fin m → Fin n) (i : Fin m) :
    (factor A B (f i)).toRingHom =
      (AmitsurAlgebras.map f).toRingHom.comp (factor A B i).toRingHom :=
  (congrArg AlgHom.toRingHom (map_comp_factor f i)).symm

private theorem alongPosition_inv_tmul {m n : ℕ} (f : Fin m → Fin n) (i : Fin m)
    (N : ModuleCat.{max u v w} B) (a : TensorPower A B n) (b : TensorPower A B m) (x : N) :
    (alongPosition.{u,v,w} A B f i).inv.app N
      (a ⊗ₜ[TensorPower A B m, (AmitsurAlgebras.map f).toRingHom]
        (show (atPosition A B i).obj N from b ⊗ₜ[B, (factor A B i).toRingHom] x)) =
    (a * AmitsurAlgebras.map f b) ⊗ₜ[B, (factor A B (f i)).toRingHom] x := by
  let F := (factor A B i).toRingHom
  let G := (AmitsurAlgebras.map (A := A) (B := B) f).toRingHom
  let e := StrictModuleDataSpec.extendComp.{max u v w,v,max u v,max u v} F G
  change (StrictModuleDataSpec.extendCongr (alongFactor (A := A) (B := B) f i)).inv.app N
    (e.inv.app N (a ⊗ₜ[TensorPower A B m, G]
      (show (ModuleCat.extendScalars F).obj N from b ⊗ₜ[B,F] x))) = _
  rw [show e.inv.app N (a ⊗ₜ[TensorPower A B m,G]
    (show (ModuleCat.extendScalars F).obj N from b ⊗ₜ[B,F] x)) =
      (a * G b) ⊗ₜ[B,G.comp F] x from
    extendComp_inv_tmul.{v,max u v,max u v,w} F G N a b x]
  exact extendCongr_inv_tmul (alongFactor (A := A) (B := B) f i) N _ x

private instance (N : ModuleCat.{max u v w} B) : IsScalarTower A B (restrict A B N) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

private theorem secondTensor_factor_smul (N : ModuleCat.{max u v w} B)
    (b : B) (z : (atPosition A B (1 : Fin 2)).obj N) :
    secondTensor A B N (factor A B (0 : Fin 2) b • z) = b • secondTensor A B N z := by
  obtain ⟨z, rfl⟩ := (secondTensor A B N).symm.surjective z
  apply (secondTensor A B N).symm.injective
  rw [AddEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul a x =>
    rw [smul_tmul', secondTensor_symm_tmul, secondTensor_symm_tmul,
      extend_smul_tmul]
    exact congrArg (fun c : TensorPower A B 2 ↦ c ⊗ₜ[B,(factor A B (1 : Fin 2)).toRingHom] (show N from x))
      (map_mul (factor A B (0 : Fin 2)) b a).symm

/-- The coaction obtained by applying the descent comparison to `x ⊗ 1`. -/
def rho (X : Datum.{u,v,w} A B) : X.module →ₗ[B] B ⊗[A] restrict A B X.module where
  toFun x := secondTensor A B X.module (X.theta.hom (generator.{u,v,w} (0 : Fin 2) x))
  map_add' x y := by rw [generator_add.{u,v,w}, map_add, map_add]
  map_smul' b x := by
    rw [generator_smul.{u,v,w}, map_smul]
    exact secondTensor_factor_smul X.module b _

/-- The unit insertion used in the invariant equalizer. -/
def insertUnit (N : ModuleCat.{max u v w} B) :
    restrict A B N →ₗ[A] B ⊗[A] restrict A B N :=
  TensorProduct.mk A B (restrict A B N) 1

private def tensorMultiply (M : Type*) [AddCommGroup M] [Module A M]
    [Module B M] [IsScalarTower A B M] : B ⊗[A] M →ₗ[B] M :=
  AlgebraTensorModule.lift
    { toFun := fun b ↦ Algebra.lsmul A A M (A := B) b
      map_add' := fun b c ↦ map_add (Algebra.lsmul A A M (A := B)) b c
      map_smul' := fun b c ↦ LinearMap.ext fun x ↦ mul_smul b c x }

@[simp] private theorem tensorMultiply_tmul {M : Type*} [AddCommGroup M] [Module A M]
    [Module B M] [IsScalarTower A B M] (b : B) (x : M) :
    tensorMultiply (A := A) M (b ⊗ₜ[A] x) = b • x :=
  AlgebraTensorModule.lift_tmul _ _ _

/-- The B-linear scalar multiplication map from the tensor with the underlying A-module. -/
def multiply (N : ModuleCat.{max u v w} B) : B ⊗[A] restrict A B N →ₗ[B] N :=
  tensorMultiply (A := A) (restrict A B N)

@[simp] theorem multiply_tmul (N : ModuleCat.{max u v w} B) (b : B) (x : restrict A B N) :
    multiply N (b ⊗ₜ[A] x) = b • x :=
  tensorMultiply_tmul (A := A) b x

/-- The coaction viewed as an A-linear map on the restricted module. -/
abbrev rhoLinear (X : Datum.{u,v,w} A B) : restrict A B X.module →ₗ[A] B ⊗[A] restrict A B X.module :=
  (show restrict A B X.module →ₗ[B] B ⊗[A] restrict A B X.module from rho X).restrictScalars A

theorem invariants_eqLocus (X : Datum.{u,v,w} A B) :
    invariants X = LinearMap.eqLocus (rhoLinear X) (insertUnit X.module) := by
  ext x
  change (X.theta.hom (generator.{u,v,w} (N := X.module) (0 : Fin 2) x) =
    generator.{u,v,w} (N := X.module) (1 : Fin 2) x) ↔
    rho X x = (1 : B) ⊗ₜ[A] x
  have h := secondTensor_symm_tmul A B X.module 1 x
  rw [map_one] at h
  change (secondTensor A B X.module).symm ((1 : B) ⊗ₜ[A] x) =
    generator.{u,v,w} (N := X.module) (1 : Fin 2) x at h
  rw [← h, ← (secondTensor A B X.module).apply_eq_iff_eq, AddEquiv.apply_symm_apply]
  rfl

private theorem diagonalFactor (i : Fin 2) :
    (diagonal A B).toRingHom.comp (factor A B i).toRingHom = RingHom.id B := by
  ext b
  exact diagonal_factor A B i b

private theorem diagonalPosition_hom_tmul (i : Fin 2) (N : ModuleCat.{max u v w} B)
    (b : B) (p : TensorPower A B 2) (x : N) :
    (diagonalPosition.{u,v,w} A B i).hom.app N
      (b ⊗ₜ[TensorPower A B 2, (diagonal A B).toRingHom]
        (show (atPosition A B i).obj N from p ⊗ₜ[B, (factor A B i).toRingHom] x)) =
      (b * diagonal A B p) • x := by
  let F := (factor A B i).toRingHom
  let G := (diagonal A B).toRingHom
  let e := StrictModuleDataSpec.extendComp.{max u v w,v,max u v,v} F G
  let d := (ModuleCat.extendScalarsId.{v,max u v w} B).hom.app N
  let c := (StrictModuleDataSpec.extendCongr (diagonalFactor (A := A) (B := B) i)).hom.app N
  change d (c (e.inv.app N (b ⊗ₜ[TensorPower A B 2,G]
    (show (ModuleCat.extendScalars F).obj N from p ⊗ₜ[B,F] x)))) = _
  rw [show e.inv.app N (b ⊗ₜ[TensorPower A B 2,G]
      (show (ModuleCat.extendScalars F).obj N from p ⊗ₜ[B,F] x)) =
        (b * G p) ⊗ₜ[B,G.comp F] x from
      extendComp_inv_tmul.{v,max u v,v,w} F G N b p x]
  calc
    _ = d ((b * G p) ⊗ₜ[B,RingHom.id B] x) :=
      congrArg d (extendCongr_hom_tmul (diagonalFactor (A := A) (B := B) i) N (b * G p) x)
    _ = d ((b * G p) • ((1 : B) ⊗ₜ[B,RingHom.id B] x :
        (ModuleCat.extendScalars (RingHom.id B)).obj N)) := by
      rw [extend_smul_tmul (RingHom.id B) N]
      exact congrArg (fun a : B ↦ d (a ⊗ₜ[B,RingHom.id B] x)) (mul_one _).symm
    _ = _ := by
      rw [map_smul]
      exact congrArg ((b * G p) • ·) (ModuleCat.extendScalarsId_hom_app_one_tmul.{v,max u v w} N x)

private theorem diagonalPosition_inv_generator (i : Fin 2) (N : ModuleCat.{max u v w} B)
    (x : N) :
    (diagonalPosition.{u,v,w} A B i).inv.app N x =
      (1 : B) ⊗ₜ[TensorPower A B 2, (diagonal A B).toRingHom]
        (generator.{u,v,w} (A := A) i x) := by
  let e := (diagonalPosition.{u,v,w} A B i).app N
  apply e.toLinearEquiv.injective
  change e.hom (e.inv x) = e.hom _
  rw [← ModuleCat.comp_apply, e.inv_hom_id, ModuleCat.id_apply]
  change x = (diagonalPosition.{u,v,w} A B i).hom.app N
    ((1 : B) ⊗ₜ[TensorPower A B 2,(diagonal A B).toRingHom]
      (show (atPosition A B i).obj N from (1 : TensorPower A B 2)
        ⊗ₜ[B,(factor A B i).toRingHom] x))
  rw [diagonalPosition_hom_tmul, map_one, one_mul, one_smul]

private theorem multiply_as_diagonal (N : ModuleCat.{max u v w} B)
    (z : B ⊗[A] restrict A B N) :
    multiply N z = (diagonalPosition.{u,v,w} A B 1).hom.app N
      ((1 : B) ⊗ₜ[TensorPower A B 2,(diagonal A B).toRingHom] ((secondTensor A B N).symm z)) := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, tmul_add, hz, hz']
  | tmul b x =>
    rw [multiply_tmul, secondTensor_symm_tmul, diagonalPosition_hom_tmul,
      diagonal_factor, one_mul]

/-- The diagonal of a strict datum is the counit identity of the associated coaction. -/
theorem multiply_rho (X : Datum.{u,v,w} A B) (x : X.module) :
    multiply X.module (rho X x) = x := by
  rw [multiply_as_diagonal]
  change (diagonalPosition.{u,v,w} A B 1).hom.app X.module
    ((1 : B) ⊗ₜ[TensorPower A B 2,(diagonal A B).toRingHom]
      ((secondTensor A B X.module).symm
        (secondTensor A B X.module (X.theta.hom (generator.{u,v,w} (0 : Fin 2) x))))) = x
  rw [AddEquiv.symm_apply_apply]
  have h := congrArg (fun f ↦ f x) X.normalized
  change (diagonalPosition.{u,v,w} A B 1).hom.app X.module
    ((ModuleCat.extendScalars (diagonal A B).toRingHom).map X.theta.hom
      ((diagonalPosition.{u,v,w} A B 0).inv.app X.module x)) = x at h
  rw [diagonalPosition_inv_generator.{u,v,w} 0 X.module x] at h
  exact h

private def insertPosition {m n : ℕ} (f : Fin m → Fin n) (i : Fin m)
    (N : ModuleCat.{max u v w} B) :
    ↑((atPosition A B i).obj N) →+ ↑((atPosition A B (f i)).obj N) where
  toFun z := (alongPosition.{u,v,w} A B f i).inv.app N
    ((1 : TensorPower A B n) ⊗ₜ[TensorPower A B m,(AmitsurAlgebras.map f).toRingHom] z)
  map_zero' := by simp
  map_add' x y := by simp only [tmul_add, map_add]

private theorem insertPosition_tmul {m n : ℕ} (f : Fin m → Fin n) (i : Fin m)
    (N : ModuleCat.{max u v w} B) (p : TensorPower A B m) (x : N) :
    insertPosition.{u,v,w} f i N
      (p ⊗ₜ[B,(factor A B i).toRingHom] x) =
      AmitsurAlgebras.map f p ⊗ₜ[B,(factor A B (f i)).toRingHom] x := by
  change (alongPosition.{u,v,w} A B f i).inv.app N
    ((1 : TensorPower A B n) ⊗ₜ[TensorPower A B m,(AmitsurAlgebras.map f).toRingHom]
      (show (atPosition A B i).obj N from p ⊗ₜ[B,(factor A B i).toRingHom] x)) = _
  rw [alongPosition_inv_tmul, one_mul]

private theorem alongTheta_insert {n : ℕ} (f : Fin 2 → Fin n)
    {N : ModuleCat.{max u v w} B} (θ : Theta A B N) (z : (atPosition A B (0 : Fin 2)).obj N) :
    (StrictModuleDataSpec.alongTheta f θ).hom (insertPosition.{u,v,w} f 0 N z) = insertPosition.{u,v,w} f 1 N (θ.hom z) := by
  let e := (alongPosition.{u,v,w} A B f 0).app N
  change _ = (alongPosition.{u,v,w} A B f 1).inv.app N
    ((1 : TensorPower A B n) ⊗ₜ[TensorPower A B 2,(AmitsurAlgebras.map f).toRingHom] (θ.hom z))
  unfold StrictModuleDataSpec.alongTheta
  change (alongPosition.{u,v,w} A B f 1).inv.app N
    ((along A B f).map θ.hom (e.hom (e.inv
      ((1 : TensorPower A B n) ⊗ₜ[TensorPower A B 2,(AmitsurAlgebras.map f).toRingHom] z)))) = _
  rw [← ModuleCat.comp_apply, e.inv_hom_id, ModuleCat.id_apply]
  rfl

private theorem alongTheta_generator {n : ℕ} (f : Fin 2 → Fin n)
    {N : ModuleCat.{max u v w} B} (θ : Theta A B N) (x : N) :
    (StrictModuleDataSpec.alongTheta f θ).hom (generator.{u,v,w} (f 0) x) =
      insertPosition.{u,v,w} f 1 N (θ.hom (generator.{u,v,w} (0 : Fin 2) x)) := by
  have h := insertPosition_tmul.{u,v,w} (A := A) f 0 N 1 x
  rw [map_one] at h
  change insertPosition.{u,v,w} f 0 N (generator.{u,v,w} (0 : Fin 2) x) =
    generator.{u,v,w} (f 0) x at h
  rw [← h, alongTheta_insert.{u,v,w} (A := A)]

/-- The third positioned module, in coordinates (b_0\otimes(b_1\otimes x)). -/
private def thirdTensor (N : ModuleCat.{max u v w} B) :
    ↑((atPosition A B (2 : Fin 3)).obj N) ≃+ (B ⊗[A] (B ⊗[A] restrict A B N)) := by
  let D := B ⊗[A] B
  let T := TensorPower A B 3
  let f := (factor A B (2 : Fin 3)).toRingHom
  let T' := (ModuleCat.restrictScalars f).obj (ModuleCat.of T T)
  let e := (Algebra.TensorProduct.comm A B D).trans (ternaryEquiv A B)
  let eB : B ⊗[A] D ≃ₗ[B] T' :=
    { e.toAddEquiv with
      map_smul' := fun b z ↦ by
        have h : e (b ⊗ₜ[A] (1 : D)) = f b := by
          change ternaryEquiv A B (1 ⊗ₜ[A] b) = _
          change ternaryEquiv A B (((1 : B) ⊗ₜ[A] (1 : B)) ⊗ₜ[A] b) = _
          rw [ternaryEquiv_tmul, map_one, map_one, one_mul, one_mul]
          rfl
        change e (b • z) = f b * e z
        have hs : b • z = (b ⊗ₜ[A] (1 : D)) * z := by
          exact (Algebra.smul_def b z).trans (congrArg (fun q : B ⊗[A] D ↦ q * z)
            (show algebraMap B (B ⊗[A] D) b = _ from rfl))
        rw [hs, map_mul, h] }
  let eTensor := TensorProduct.congr eB.symm (LinearEquiv.refl B (restrict A B N))
  let eComm := (AlgebraTensorModule.rightComm A B B B (restrict A B N) D).symm
  let eLid := AlgebraTensorModule.congr (TensorProduct.lid B (restrict A B N))
    (LinearEquiv.refl A D)
  exact (eTensor.trans (eComm.trans eLid)).toAddEquiv.trans
    ((TensorProduct.comm A (restrict A B N) D).trans
      (TensorProduct.assoc A B B (restrict A B N))).toAddEquiv

private theorem thirdTensor_symm_tmul (N : ModuleCat.{max u v w} B)
    (a b : B) (x : restrict A B N) :
    (thirdTensor.{u,v,w} N).symm (a ⊗ₜ[A] (b ⊗ₜ[A] x)) =
      (factor A B (0 : Fin 3) a * factor A B (1 : Fin 3) b)
        ⊗ₜ[B,(factor A B (2 : Fin 3)).toRingHom] (show N from x) := by
  change ternaryEquiv A B ((a ⊗ₜ[A] b) ⊗ₜ[A] (1 : B))
    ⊗ₜ[B,(factor A B (2 : Fin 3)).toRingHom] (show N from x) = _
  rw [ternaryEquiv_tmul, map_one, mul_one]

private theorem thirdTensor_insert02 (N : ModuleCat.{max u v w} B)
    (z : B ⊗[A] restrict A B N) :
    thirdTensor.{u,v,w} N (insertPosition.{u,v,w} (StrictModuleDataSpec.pair 1) 1 N ((secondTensor A B N).symm z)) =
      AlgebraTensorModule.lTensor B B (insertUnit N) z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b x =>
    apply (thirdTensor.{u,v,w} N).symm.injective
    rw [AddEquiv.symm_apply_apply, AlgebraTensorModule.lTensor_tmul]
    change insertPosition.{u,v,w} (StrictModuleDataSpec.pair 1) 1 N
      ((secondTensor A B N).symm (b ⊗ₜ[A] x)) =
        (thirdTensor.{u,v,w} N).symm (b ⊗ₜ[A] ((1 : B) ⊗ₜ[A] x))
    rw [secondTensor_symm_tmul, insertPosition_tmul, map_factor, thirdTensor_symm_tmul,
      map_one, mul_one]
    rfl

private theorem thirdTensor_insert12 (N : ModuleCat.{max u v w} B)
    (a : B) (z : B ⊗[A] restrict A B N) :
    thirdTensor.{u,v,w} N (factor A B (0 : Fin 3) a •
      insertPosition.{u,v,w} (StrictModuleDataSpec.pair 0) 1 N ((secondTensor A B N).symm z)) =
      a ⊗ₜ[A] z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, smul_add, tmul_add, hx, hy]
  | tmul b x =>
    apply (thirdTensor.{u,v,w} N).symm.injective
    rw [AddEquiv.symm_apply_apply, secondTensor_symm_tmul, insertPosition_tmul, map_factor,
      thirdTensor_symm_tmul]
    rfl

private theorem alongTheta_after_insert01 (X : Datum.{u,v,w} A B)
    (z : B ⊗[A] restrict A B X.module) :
    thirdTensor.{u,v,w} X.module
      ((StrictModuleDataSpec.alongTheta (StrictModuleDataSpec.pair 0) X.theta).hom
        (insertPosition.{u,v,w} (StrictModuleDataSpec.pair 2) 1 X.module ((secondTensor A B X.module).symm z))) =
      AlgebraTensorModule.lTensor B B (rhoLinear X) z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b x =>
    rw [AlgebraTensorModule.lTensor_tmul, secondTensor_symm_tmul, insertPosition_tmul, map_factor]
    let f := StrictModuleDataSpec.pair 0
    have h : factor A B (0 : Fin 3) b • generator.{u,v,w} (A := A) (f 0) (show X.module from x) =
        factor A B (0 : Fin 3) b ⊗ₜ[B,(factor A B (f 0)).toRingHom] (show X.module from x) :=
      (extend_smul_tmul (factor A B (f 0)).toRingHom X.module _ 1 x).trans
        (congrArg (fun c : TensorPower A B 3 ↦ c ⊗ₜ[B,(factor A B (f 0)).toRingHom] (show X.module from x)) (mul_one _))
    change thirdTensor.{u,v,w} X.module ((StrictModuleDataSpec.alongTheta f X.theta).hom
      (factor A B (0 : Fin 3) b ⊗ₜ[B,(factor A B (f 0)).toRingHom] (show X.module from x))) = _
    rw [← h, map_smul, alongTheta_generator]
    have hρ : (secondTensor A B X.module).symm (rhoLinear X x) =
        X.theta.hom (generator.{u,v,w} (0 : Fin 2) (show X.module from x)) :=
      (secondTensor A B X.module).symm_apply_apply _
    rw [← hρ]
    exact thirdTensor_insert12 X.module b (rhoLinear X x)

/-- The cocycle of a strict datum places the coaction in the base-changed equalizer. -/
theorem rho_cocycle (X : Datum.{u,v,w} A B) (x : X.module) :
    AlgebraTensorModule.lTensor B B (rhoLinear X) (rho X x) =
      AlgebraTensorModule.lTensor B B (insertUnit X.module) (rho X x) := by
  rw [← alongTheta_after_insert01, ← thirdTensor_insert02]
  change thirdTensor.{u,v,w} X.module
    ((StrictModuleDataSpec.alongTheta (StrictModuleDataSpec.pair 0) X.theta).hom
      (insertPosition.{u,v,w} (StrictModuleDataSpec.pair 2) 1 X.module
        ((secondTensor A B X.module).symm
          (secondTensor A B X.module (X.theta.hom (generator.{u,v,w} (0 : Fin 2) x)))))) =
    thirdTensor.{u,v,w} X.module (insertPosition.{u,v,w} (StrictModuleDataSpec.pair 1) 1 X.module
      ((secondTensor A B X.module).symm
        (secondTensor A B X.module (X.theta.hom (generator.{u,v,w} (0 : Fin 2) x)))))
  rw [AddEquiv.symm_apply_apply, ← alongTheta_generator, ← alongTheta_generator]
  exact congrArg (thirdTensor.{u,v,w} X.module) (congrArg
    (fun k ↦ k (generator.{u,v,w} (A := A) (0 : Fin 3) x)) X.cocycle)

private theorem counitMap_one_tmul (X : Datum.{u,v,w} A B) (x : invariants X) :
    counitMap X ((1 : B) ⊗ₜ[A,algebraMap A B] (show (descend (A := A) (B := B)).obj X from x)) =
      (show X.module from x.val) := by
  let adj := ModuleCat.extendRestrictScalarsAdj.{max u v w,u,v} (algebraMap A B)
  let i : descend.obj X ⟶ restrict A B X.module :=
    ModuleCat.ofHom (Y := restrict A B X.module) (invariants X).subtype
  change (adj.homEquiv _ _).symm i _ = i x
  exact (ModuleCat.extendRestrictScalarsAdj_homEquiv_apply.{max u v w,u,v}
    ((adj.homEquiv _ _).symm i) x).symm.trans
      (congrArg (fun f ↦ f x) ((adj.homEquiv _ _).apply_symm_apply i))

/-- On pure tensors the counit acts by scalar multiplication. -/
theorem counitMap_tmul : DescentCounitSpec.CounitMapTmul.{u,v,w} := by
  intro A B _ _ _ X b x
  let M := (descend (A := A) (B := B)).obj X
  change counitMap X (b ⊗ₜ[A,algebraMap A B] (show M from x)) = _
  let z : (ModuleCat.extendScalars (algebraMap A B)).obj M :=
    (1 : B) ⊗ₜ[A,algebraMap A B] (show M from x)
  have h : b • z = b ⊗ₜ[A,algebraMap A B] (show M from x) :=
    (extend_smul_tmul (algebraMap A B) M b 1 x).trans
      (congrArg (fun c : B ↦ c ⊗ₜ[A,algebraMap A B] (show M from x)) (mul_one b))
  rw [← h, map_smul]
  exact congrArg (b • ·) (counitMap_one_tmul X x)

/-- The equalizer of the two maps obtained by tensoring the invariant equations. -/
private abbrev tensorInvariants (X : Datum.{u,v,w} A B) :=
  LinearMap.eqLocus (AlgebraTensorModule.lTensor B B (rhoLinear X))
    (AlgebraTensorModule.lTensor B B (insertUnit X.module))

private theorem rho_multiply_of_mem (X : Datum.{u,v,w} A B) (z : tensorInvariants X) :
    rho X (multiply X.module z.val) = z.val := by
  let M := B ⊗[A] restrict A B X.module
  let h := tensorMultiply (A := A) (B := B) M
  have hρ : h.comp (AlgebraTensorModule.lTensor B B (rhoLinear X)) =
      (rho X).comp (multiply X.module) := by
    apply AlgebraTensorModule.ext
    intro b x
    rw [LinearMap.comp_apply, AlgebraTensorModule.lTensor_tmul, LinearMap.comp_apply,
      multiply_tmul]
    change h (b ⊗ₜ[A] (rho X x)) = rho X (b • (show X.module from x))
    exact (tensorMultiply_tmul (A := A) b (rho X x)).trans ((rho X).map_smul b x).symm
  have h₁ : h.comp (AlgebraTensorModule.lTensor B B (insertUnit X.module)) = LinearMap.id := by
    apply AlgebraTensorModule.ext
    intro b x
    rw [LinearMap.comp_apply, AlgebraTensorModule.lTensor_tmul, LinearMap.id_apply]
    change h (b ⊗ₜ[A] ((1 : B) ⊗ₜ[A] x)) = _
    rw [show h (b ⊗ₜ[A] ((1 : B) ⊗ₜ[A] x)) = b • ((1 : B) ⊗ₜ[A] x) from
      tensorMultiply_tmul (A := A) b ((1 : B) ⊗ₜ[A] x)]
    rw [smul_tmul']
    exact congrArg (fun c : B ↦ c ⊗ₜ[A] x) (mul_one b)
  have hz : AlgebraTensorModule.lTensor B B (rhoLinear X) z.val =
      AlgebraTensorModule.lTensor B B (insertUnit X.module) z.val := z.property
  have hc := congrArg h hz
  change (h.comp (AlgebraTensorModule.lTensor B B (rhoLinear X))) z.val =
    (h.comp (AlgebraTensorModule.lTensor B B (insertUnit X.module))) z.val at hc
  rw [hρ, h₁] at hc
  exact hc

private def tensorInvariantsEquiv (X : Datum.{u,v,w} A B) :
    tensorInvariants X ≃ₗ[B] X.module :=
  LinearEquiv.ofLinearMap
    ((multiply X.module).comp (tensorInvariants X).subtype)
    ((rho X).codRestrict (tensorInvariants X) (rho_cocycle X))
    (LinearMap.ext fun x ↦ multiply_rho X x)
    (LinearMap.ext fun z ↦ Subtype.ext (rho_multiply_of_mem X z))

private def invariantTensorEquiv [Module.Flat A B] (X : Datum.{u,v,w} A B) :
    B ⊗[A] invariants X ≃ₗ[B] X.module :=
  (AlgebraTensorModule.congr (LinearEquiv.refl B B)
    (LinearEquiv.ofEq _ _ (invariants_eqLocus X))).trans
    ((LinearMap.tensorEqLocusEquiv B B (rhoLinear X) (insertUnit X.module)).trans
      (tensorInvariantsEquiv X))

private theorem invariantTensorEquiv_tmul [Module.Flat A B] (X : Datum.{u,v,w} A B)
    (b : B) (x : invariants X) :
    invariantTensorEquiv X (b ⊗ₜ[A] x) = b • (show X.module from x.val) := by
  simp only [invariantTensorEquiv, LinearEquiv.trans_apply, AlgebraTensorModule.congr_tmul,
    LinearEquiv.refl_apply, LinearMap.tensorEqLocusEquiv_apply, tensorInvariantsEquiv,
    LinearEquiv.coe_ofLinearMap, LinearMap.comp_apply, Submodule.subtype_apply,
    LinearMap.tensorEqLocus_tmul, LinearEquiv.coe_ofEq_apply, multiply_tmul]

/-- The bundled scalar extension compared to the ordinary tensor with the left algebra action. -/
private def baseChangeTensor (M : ModuleCat.{max u v w} A) :
    ↑((ModuleCat.extendScalars.{u,v,max u v w} (algebraMap A B)).obj M) ≃ₗ[B] B ⊗[A] M := by
  let D := (ModuleCat.restrictScalars.{v,u,v} (algebraMap A B)).obj (ModuleCat.of B B)
  letI : Module B D := (ModuleCat.of B B).isModule
  letI : IsScalarTower A B D := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let e : D ≃ₗ[B] B := LinearEquiv.refl B B
  exact AlgebraTensorModule.congr e (LinearEquiv.refl A M)

private theorem baseChangeTensor_tmul (M : ModuleCat.{max u v w} A) (b : B) (x : M) :
    baseChangeTensor (B := B) M (b ⊗ₜ[A,algebraMap A B] x) = b ⊗ₜ[A] x := rfl

/-- Flat scalar extension recovers the underlying module of a strict descent datum. -/
theorem isIso_counitMap : DescentCounitSpec.IsIsoCounit.{u,v,w} := by
  intro A B _ _ _ _ X
  let M := (descend (A := A) (B := B)).obj X
  let e := ((baseChangeTensor (B := B) M).trans (invariantTensorEquiv X)).toModuleIso
  have he : e.hom = counitMap X := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change invariantTensorEquiv X (baseChangeTensor (B := B) M ((1 : B) ⊗ₜ[A,algebraMap A B] x)) =
      counitMap X ((1 : B) ⊗ₜ[A,algebraMap A B] x)
    rw [baseChangeTensor_tmul, invariantTensorEquiv_tmul, one_smul]
    exact (counitMap_one_tmul X x).symm
  change IsIso (counitMap X)
  exact he ▸ (inferInstance : IsIso e.hom)

private theorem baseChangeFactor {n : ℕ} (i : Fin n) :
    algebraMap A (TensorPower A B n) =
      (factor A B i).toRingHom.comp (algebraMap A B) := by
  ext a
  exact ((factor A B i).commutes a).symm

private theorem baseChangePosition_inv_tmul {n : ℕ} (i : Fin n)
    (M : ModuleCat.{max u v w} A) (p : TensorPower A B n) (b : B) (x : M) :
    (baseChangePosition.{u,v,w} i).inv.app M
      (p ⊗ₜ[B,(factor A B i).toRingHom]
        (show (ModuleCat.extendScalars (algebraMap A B)).obj M from b ⊗ₜ[A,algebraMap A B] x)) =
      (p * factor A B i b) ⊗ₜ[A,algebraMap A (TensorPower A B n)] x := by
  let F := algebraMap A B
  let G := (factor A B i).toRingHom
  let e := StrictModuleDataSpec.extendComp.{max u v w,u,v,max u v} F G
  let h := baseChangeFactor (A := A) (B := B) i
  change (StrictModuleDataSpec.extendCongr h).inv.app M
    (e.inv.app M (p ⊗ₜ[B,G]
      (show (ModuleCat.extendScalars F).obj M from b ⊗ₜ[A,F] x))) = _
  have hp := extendComp_inv_tmul.{u,v,max u v,w} F G M p b x
  rw [show e.inv.app M (p ⊗ₜ[B,G]
    (show (ModuleCat.extendScalars F).obj M from b ⊗ₜ[A,F] x)) =
      (p * G b) ⊗ₜ[A,G.comp F] x from hp]
  exact extendCongr_inv_tmul h M _ x

private theorem baseChangePosition_hom_tmul {n : ℕ} (i : Fin n)
    (M : ModuleCat.{max u v w} A) (p : TensorPower A B n) (x : M) :
    (baseChangePosition.{u,v,w} i).hom.app M
      (p ⊗ₜ[A,algebraMap A (TensorPower A B n)] x) =
      p ⊗ₜ[B,(factor A B i).toRingHom]
        (show (ModuleCat.extendScalars (algebraMap A B)).obj M from (1 : B) ⊗ₜ[A,algebraMap A B] x) := by
  let F := algebraMap A B
  let G := (factor A B i).toRingHom
  let e := StrictModuleDataSpec.extendComp.{max u v w,u,v,max u v} F G
  let h := baseChangeFactor (A := A) (B := B) i
  change e.hom.app M ((StrictModuleDataSpec.extendCongr h).hom.app M
    (p ⊗ₜ[A,algebraMap A (TensorPower A B n)] x)) = _
  rw [extendCongr_hom_tmul h M p x]
  exact extendComp_hom_tmul.{u,v,max u v,w} F G M p x

/-- The canonical comparison moves the free tensor generator to the new position. -/
theorem baseChangeTheta_tmul : DescentCounitSpec.BaseChangeThetaTmul.{u,v,w} := by
  intro A B _ _ _ M b c x
  let e₀ := (baseChangePosition.{u,v,w} (A := A) (B := B) (0 : Fin 2)).app M
  let e₁ := (baseChangePosition.{u,v,w} (A := A) (B := B) (1 : Fin 2)).app M
  let M' := (ModuleCat.extendScalars (algebraMap A B)).obj M
  let y := factor A B (1 : Fin 2) c ⊗ₜ[B,(factor A B (0 : Fin 2)).toRingHom]
    (show M' from b ⊗ₜ[A,algebraMap A B] x)
  let z := factor A B (0 : Fin 2) b ⊗ₜ[B,(factor A B (1 : Fin 2)).toRingHom]
    (show M' from c ⊗ₜ[A,algebraMap A B] x)
  change e₁.hom (e₀.inv y) = z
  have h₀ := baseChangePosition_inv_tmul.{u,v,w} 0 M (factor A B (1 : Fin 2) c) b x
  have h₁ := baseChangePosition_inv_tmul.{u,v,w} 1 M (factor A B (0 : Fin 2) b) c x
  have hs : e₀.inv y = e₁.inv z := h₀.trans
    ((congrArg (fun p : TensorPower A B 2 ↦ p ⊗ₜ[A,algebraMap A (TensorPower A B 2)] x)
      (mul_comm _ _)).trans h₁.symm)
  rw [hs, ← ModuleCat.comp_apply, e₁.inv_hom_id, ModuleCat.id_apply]

/-- The canonical comparison takes the unit tensor in the first position to the unit tensor
in the second. -/
theorem baseChangeTheta_generator (M : ModuleCat.{max u v w} A) (x : M) :
    (baseChangeTheta.{u,v,w} (B := B) M).hom
      (generator.{u,v,w} (A := A) (0 : Fin 2)
        (show (ModuleCat.extendScalars (algebraMap A B)).obj M from (1 : B) ⊗ₜ[A,algebraMap A B] x)) =
    generator.{u,v,w} (A := A) (1 : Fin 2)
      (show (ModuleCat.extendScalars (algebraMap A B)).obj M from (1 : B) ⊗ₜ[A,algebraMap A B] x) := by
  have h := baseChangeTheta_tmul.{u,v,w} A B M 1 1 x
  simp only [map_one] at h
  exact h

/-- The counit intertwines the canonical position comparison and the given descent datum. -/
theorem counit_compatible : DescentCounitSpec.CounitCompatible.{u,v,w} := by
  intro A B _ _ _ X
  let M := (descend (A := A) (B := B)).obj X
  let e := (baseChangePosition.{u,v,w} (A := A) (B := B) (0 : Fin 2)).app M
  apply (cancel_epi e.hom).mp
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  have h := baseChangePosition_hom_tmul.{u,v,w} (0 : Fin 2) M (1 : TensorPower A B 2) x
  change e.hom ((1 : TensorPower A B 2) ⊗ₜ[A,algebraMap A (TensorPower A B 2)] x) =
    generator.{u,v,w} (A := A) (0 : Fin 2)
      (show (ModuleCat.extendScalars (algebraMap A B)).obj M from (1 : B) ⊗ₜ[A,algebraMap A B] x) at h
  simp only [ModuleCat.comp_apply]
  rw [h]
  let z : (ModuleCat.extendScalars (algebraMap A B)).obj M := (1 : B) ⊗ₜ[A,algebraMap A B] x
  change X.theta.hom (generator.{u,v,w} (0 : Fin 2) (counitMap X z)) =
    (atPosition A B (1 : Fin 2)).map (counitMap X)
      ((baseChangeTheta (B := B) M).hom (generator.{u,v,w} (A := A) (0 : Fin 2) z))
  rw [baseChangeTheta_generator.{u,v,w} M x]
  change X.theta.hom (generator.{u,v,w} (0 : Fin 2) (counitMap X z)) =
    generator.{u,v,w} (1 : Fin 2) (counitMap X z)
  rw [show counitMap X z = (show X.module from x.val) from counitMap_one_tmul X x]
  exact x.property

/-- Scalar multiplication on invariants is natural for strict maps. -/
theorem counit_natural : DescentCounitSpec.CounitNatural.{u,v,w} := by
  intro A B _ _ _ X Y f
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  let y : invariants Y := (descend.map f) x
  change counitMap Y ((1 : B) ⊗ₜ[A,algebraMap A B]
      (show (descend (A := A) (B := B)).obj Y from y)) =
    f.hom (counitMap X ((1 : B) ⊗ₜ[A,algebraMap A B] x))
  rw [counitMap_one_tmul Y y, counitMap_one_tmul X x]
  rfl

/-- The descended module, after flat base change, is naturally isomorphic to the underlying
module of the original datum. Its components commute with the descent comparisons by
`counit_compatible`. -/
def counitIso (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] :
    descend.{u,v,w} (A := A) (B := B) ⋙
      ModuleCat.extendScalars.{u,v,max u v w} (algebraMap A B) ≅ forget A B :=
  NatIso.ofComponents
    (fun X ↦
      letI := isIso_counitMap.{u,v,w} A B X
      asIso (counitMap X))
    (fun f ↦ counit_natural.{u,v,w} A B f)

@[simp] theorem counitIso_hom_app [Module.Flat A B] (X : Datum.{u,v,w} A B) :
    (counitIso A B).hom.app X = counitMap X := rfl

end

end DerivedFormalization.Descent.DescentCounit
