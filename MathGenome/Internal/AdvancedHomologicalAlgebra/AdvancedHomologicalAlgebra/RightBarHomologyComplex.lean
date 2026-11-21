import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.RightBarHomologyComplex
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupBarResolution
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupCoinvariants
import Mathlib.LinearAlgebra.Finsupp.Pi

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
open CategoryTheory
open scoped MonoidAlgebra
namespace AdvancedHomologicalAlgebra.RightBar
universe u v w
variable (k : Type u) (G : Type v) [CommRing k] [Group G]

@[simp] theorem inversion_single (g : G) (a : k) :
    inversion k G (MonoidAlgebra.single g a) =
      MulOpposite.op (MonoidAlgebra.single g⁻¹ a) := by
  simp [inversion]

@[simp] theorem inversion_symm_single (g : G) (a : k) :
    (inversion k G).symm (MulOpposite.op (MonoidAlgebra.single g a)) =
      MonoidAlgebra.single g⁻¹ a := by
  apply (inversion k G).injective
  simp

@[simp] theorem twist_group_smul (V : Rep k G) (g : G) (x : Twist k G V) :
    untwist k G V (MulOpposite.op (MonoidAlgebra.single g (1:k)) • x) =
      V.ρ g⁻¹ (untwist k G V x) := by
  change V.ρ.asModuleEquiv ((inversion k G).symm
    (MulOpposite.op (MonoidAlgebra.single g (1:k))) • (show V.ρ.asModule from x)) = _
  rw [inversion_symm_single, Representation.single_smul, one_smul]
  rfl

local instance inversionInvPair :
    RingHomInvPair (inversion k G).toRingHom (inversion k G).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (inversion k G)
local instance inversionInvPairSymm :
    RingHomInvPair (inversion k G).symm.toRingHom (inversion k G).toRingHom :=
  RingHomInvPair.of_ringEquiv (inversion k G).symm

/-- Inversion is a scalar equivalence between the left and right versions. -/
def twistEquiv (V : Rep k G) : V.ρ.asModule ≃ₛₗ[(inversion k G).toRingHom] Twist k G V where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change r • x = ((inversion k G).symm (inversion k G r)) • x
    rw [RingEquiv.symm_apply_apply]

theorem degree_free (n : ℕ) : Module.Free k[G]ᵐᵒᵖ (B k G n) := by
  letI := GroupBar.Large.degree_free.{u,v,0} k G n
  exact Module.Free.of_equiv (twistEquiv k G (GroupBar.Large.B.{u,v,0} k G n))

theorem boundary_squared (n : ℕ) :
    boundary k G n ∘ₗ boundary k G (n+1) = 0 := by
  ext x
  exact LinearMap.congr_fun
    (congrArg (fun f : GroupBar.Large.B.{u,v,0} k G (n+2) ⟶ GroupBar.Large.B.{u,v,0} k G n => f.hom.toLinearMap)
      (GroupBar.Large.boundary_squared.{u,v,0} k G n)) x

theorem boundary_augmentation (x : B k G 1) :
    augmentationLinear k G (boundary k G 0 x) = 0 := by
  exact (GroupBar.Large.exact_zero.{u,v,0} k G _).2 ⟨x, rfl⟩

theorem augmentation_inversion (r : k[G]) :
    GroupCoinvariants.augmentation k G ((inversion k G).symm (MulOpposite.op r)) =
      GroupCoinvariants.augmentation k G r := by
  induction r using MonoidAlgebra.induction_on with
  | of g => simp [MonoidAlgebra.of_apply]
  | add r s hr hs => simp [hr, hs]
  | smul a r hr =>
    simp [Algebra.smul_def, MonoidAlgebra.coe_algebraMap, MulOpposite.op_mul, hr, mul_comm]

private lemma trivial_asAlgebraHom {V : Type*} [AddCommGroup V] [Module k V]
    (r : k[G]) (a : V) :
    (Representation.trivial k G V).asAlgebraHom r a =
      GroupCoinvariants.augmentation k G r • a := by
  induction r using MonoidAlgebra.induction_on with
  | of g => simp [Representation.asAlgebraHom_single, MonoidAlgebra.of_apply]
  | add r s hr hs => simp [hr, hs, add_smul]
  | smul t r hr =>
    simp only [map_smul, LinearMap.smul_apply, hr]
    simp [Algebra.smul_def, mul_smul]

theorem augmentation_right_smul (r : k[G]) (x : B k G 0) :
    augmentationLinear k G (MulOpposite.op r • x) =
      MulOpposite.op r • augmentationLinear k G x := by
  have h := (Rep.toModuleMonoidAlgebra.map (GroupBar.Large.augmentation.{u,v,0} k G)).hom.map_smul
    ((inversion k G).symm (MulOpposite.op r)) (show (GroupBar.Large.B.{u,v,0} k G 0).ρ.asModule from x)
  change ULift.up (augmentationLinear k G (MulOpposite.op r • x)) =
    (Representation.trivial k G (ULift.{v} k)).asAlgebraHom
      ((inversion k G).symm (MulOpposite.op r)) (ULift.up (augmentationLinear k G x)) at h
  rw [trivial_asAlgebraHom, augmentation_inversion] at h
  exact congrArg ULift.down h

theorem rightResolution : Specification.rightResolutionType.{u,v} := by
  intro k G _ _
  exact ⟨(fun n => twist_group_smul k G (GroupBar.Large.B.{u,v,0} k G n)), degree_free k G, boundary_squared k G,
    boundary_augmentation k G, augmentation_right_smul k G,
    GroupBar.Large.augmentation_surjective.{u,v,0} k G, GroupBar.Large.exact_zero.{u,v,0} k G,
    GroupBar.Large.exact_succ.{u,v,0} k G⟩

section FreeTensor
variable {R : Type*} [Ring R] {ι N : Type*} [AddCommGroup N] [Module R N]
open P103.BalancedTensor

/-- Evaluation of finitely supported right coefficients on a left-module vector. -/
def freePair (m : N) : (ι →₀ Rᵐᵒᵖ) →+ (ι →₀ N) :=
  Finsupp.liftAddHom (fun i => {
    toFun := fun r => Finsupp.single i (r.unop • m)
    map_zero' := by simp
    map_add' := by intros; simp [add_smul, Finsupp.single_add] })

@[simp] lemma freePair_single (m : N) (i : ι) (r : Rᵐᵒᵖ) :
    freePair m (Finsupp.single i r) = Finsupp.single i (r.unop • m) := by
  simp [freePair]

def freePairing : Pairing R (A := ι →₀ Rᵐᵒᵖ) (B := N) (ι →₀ N) :=
  Pairing.ofFun (fun a m => freePair m a)
    (fun _ _ _ => map_add _ _ _)
    (by
      intro a m m'
      induction a using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb => simp [ha, hb, add_add_add_comm]
      | single i r => simp [smul_add, Finsupp.single_add])
    (by
      intro r a m
      induction a using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb => simp [smul_add, ha, hb]
      | single i t => simp [Finsupp.smul_single, smul_eq_mul, smul_smul])

def freeTensorEquiv : Tensor R (ι →₀ Rᵐᵒᵖ) N ≃+ (ι →₀ N) := by
  let f := lift (freePairing (R := R) (ι := ι) (N := N))
  let g : (ι →₀ N) →+ Tensor R (ι →₀ Rᵐᵒᵖ) N :=
    Finsupp.liftAddHom (fun i => pairing.toBiadditive (Finsupp.single i 1))
  have hg (i : ι) (m : N) : g (Finsupp.single i m) = tmul R (Finsupp.single i 1) m := by
    simp [g]
  refine { f with invFun := g, left_inv := ?_, right_inv := ?_ }
  · intro z
    induction z using P103.BalancedTensor.induction_on with
    | h0 => simp
    | ht a m =>
      induction a using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb => simp_all [add_tmul]
      | single i r =>
        change g (freePair m (Finsupp.single i r)) = _
        rw [freePair_single, hg, ← balance]
        congr 1
        simp [Finsupp.smul_single, smul_eq_mul]
    | ha x y hx hy => simp_all
  · intro a
    induction a using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp_all
    | single i m =>
      rw [hg]
      change freePair m (Finsupp.single i 1) = _
      simp

@[simp] lemma freeTensorEquiv_tmul_single (i : ι) (r : Rᵐᵒᵖ) (m : N) :
    freeTensorEquiv (tmul R (Finsupp.single i r) m) = Finsupp.single i (r.unop • m) := by
  exact freePair_single m i r

@[simp] lemma freeTensorEquiv_symm_single (i : ι) (m : N) :
    freeTensorEquiv.symm (Finsupp.single i m) = tmul R (Finsupp.single i 1) m := by
  apply freeTensorEquiv.injective
  simp
end FreeTensor

/-- A homogeneous tuple is determined by its first vertex and its successive increments. -/
private def tupleCoordinates (n : ℕ) :
    ULift.{0} (Fin (n+1) → G) ≃ (Fin n → G) × G where
  toFun c := (fun i => (c.down i.castSucc)⁻¹ * c.down i.succ, c.down 0)
  invFun p := ULift.up (p.2 • Fin.partialProd p.1)
  left_inv c := ULift.ext (Fin.partialProd_left_inv c.down)
  right_inv p := by
    apply Prod.ext
    · funext i
      simpa [smul_eq_mul, mul_inv_rev, mul_assoc] using Fin.partialProd_right_inv p.1 i
    · simp [smul_eq_mul]

private def leftCoordinatesScalar (n : ℕ) :
    GroupBar.Large.B.{u,v,0} k G n ≃ₗ[k] ((Fin n → G) →₀ k[G]) :=
  (MonoidAlgebra.mapDomainLinearEquiv k k (tupleCoordinates G n)).trans
    ((MonoidAlgebra.coeffLinearEquiv k).trans
      ((Finsupp.curryLinearEquiv k).trans
        (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv k).symm)))

private lemma leftCoordinatesScalar_single (n : ℕ) (c : Fin (n+1) → G) (a : k) :
    leftCoordinatesScalar k G n (GroupBar.Large.single.{u,v,0} k G c a) =
      Finsupp.single (fun i => (c i.castSucc)⁻¹ * c i.succ) (MonoidAlgebra.single (c 0) a) := by
  simp [leftCoordinatesScalar, tupleCoordinates, Finsupp.curryLinearEquiv, GroupBar.Large.single]

/-- Left bar coordinates over the original group algebra. -/
def leftCoordinates (n : ℕ) : (GroupBar.Large.B.{u,v,0} k G n).ρ.asModule ≃ₗ[k[G]]
    ((Fin n → G) →₀ k[G]) := by
  let e : GroupBar.Large.B.{u,v,0} k G n ≅ Rep.free k G (Fin n → G) :=
    Rep.mkIso (Representation.Equiv.mk (leftCoordinatesScalar k G n) (fun g => by
      apply MonoidAlgebra.lhom_ext'
      rintro ⟨c⟩
      apply LinearMap.ext_ring
      change leftCoordinatesScalar k G n
          ((GroupBar.Large.B.{u,v,0} k G n).ρ g (GroupBar.Large.single.{u,v,0} k G c 1)) =
        Representation.free k G (Fin n → G) g
          (leftCoordinatesScalar k G n (GroupBar.Large.single.{u,v,0} k G c 1))
      rw [GroupBar.Large.diagonal_action, leftCoordinatesScalar_single,
        leftCoordinatesScalar_single, Representation.free_single_single]
      simp [mul_inv_rev, mul_assoc]))
  exact (Rep.toModuleMonoidAlgebra.mapIso e).toLinearEquiv.trans
    (Representation.finsuppLEquivFreeAsModule k G (Fin n → G)).symm

/-- Coordinates of the right twist: invert the coefficients of the left coordinates. -/
def rightCoordinates (n : ℕ) : B k G n ≃ₗ[k[G]ᵐᵒᵖ] ((Fin n → G) →₀ k[G]ᵐᵒᵖ) where
  toAddEquiv :=
    (show B k G n ≃+ (GroupBar.Large.B.{u,v,0} k G n).ρ.asModule from AddEquiv.refl _).trans
      ((leftCoordinates k G n).toAddEquiv.trans (Finsupp.mapRange.addEquiv (inversion k G).toAddEquiv))
  map_smul' r x := by
    change Finsupp.mapRange.addEquiv (inversion k G).toAddEquiv
      (leftCoordinates k G n ((inversion k G).symm r • (show (GroupBar.Large.B.{u,v,0} k G n).ρ.asModule from x))) = _
    rw [map_smul]
    ext i
    change inversion k G ((inversion k G).symm r * (leftCoordinates k G n x) i) =
      r * inversion k G ((leftCoordinates k G n x) i)
    simp

/-- The free bar basis is the tuple of ordered partial products. -/
lemma leftCoordinates_symm_single (n : ℕ) (g : Fin n → G) (h : G) (a : k) :
    (leftCoordinates k G n).symm (Finsupp.single g (MonoidAlgebra.single h a)) =
      GroupBar.Large.single.{u,v,0} k G (h • Fin.partialProd g) a := by
  apply (leftCoordinates k G n).injective
  rw [LinearEquiv.apply_symm_apply]
  change Finsupp.single g (MonoidAlgebra.single h a) =
    leftCoordinatesScalar k G n (GroupBar.Large.single.{u,v,0} k G (h • Fin.partialProd g) a)
  rw [leftCoordinatesScalar_single]
  congr 1
  · funext i
    simpa [smul_eq_mul, mul_inv_rev, mul_assoc] using (Fin.partialProd_right_inv g i).symm
  · simp [smul_eq_mul]

@[simp] lemma rightCoordinates_symm_single (n : ℕ) (g : Fin n → G) (h : G) (a : k) :
    (rightCoordinates k G n).symm
      (Finsupp.single g (MulOpposite.op (MonoidAlgebra.single h a))) =
      (untwist k G _).symm (GroupBar.Large.single.{u,v,0} k G (h⁻¹ • Fin.partialProd g) a) := by
  change (leftCoordinates k G n).symm
    (Finsupp.mapRange.addEquiv (inversion k G).toAddEquiv |>.symm
      (Finsupp.single g (MulOpposite.op (MonoidAlgebra.single h a)))) = _
  simp only [Finsupp.mapRange.addEquiv_symm, Finsupp.mapRange.addEquiv_apply,
    Finsupp.mapRange_single]
  change (leftCoordinates k G n).symm (Finsupp.single g
    ((inversion k G).symm (MulOpposite.op (MonoidAlgebra.single h a)))) = _
  rw [inversion_symm_single, leftCoordinates_symm_single]
  rfl

section TensorCongr
open P103.BalancedTensor
variable {R A A' N : Type*} [Ring R] [AddCommGroup A] [AddCommGroup A']
  [AddCommGroup N] [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ A'] [Module R N]

def tensorCongr (e : A ≃ₗ[Rᵐᵒᵖ] A') : Tensor R A N ≃+ Tensor R A' N where
  __ := P103.BalancedTensor.map e.toLinearMap LinearMap.id
  invFun := P103.BalancedTensor.map e.symm.toLinearMap LinearMap.id
  left_inv z := by
    induction z using P103.BalancedTensor.induction_on with
    | h0 => simp
    | ht a m => simp
    | ha x y hx hy => simp_all
  right_inv z := by
    induction z using P103.BalancedTensor.induction_on with
    | h0 => simp
    | ht a m => simp
    | ha x y hx hy => simp_all

@[simp] lemma tensorCongr_tmul (e : A ≃ₗ[Rᵐᵒᵖ] A') (a : A) (m : N) :
    tensorCongr e (tmul R a m) = tmul R (e a) m := rfl
@[simp] lemma tensorCongr_symm_tmul (e : A ≃ₗ[Rᵐᵒᵖ] A') (a : A') (m : N) :
    (tensorCongr e).symm (tmul R a m) = tmul R (e.symm a) m := rfl
end TensorCongr

open P103.BalancedTensor

def tensorCoordinatesAdd (M : ModuleCat.{w} k[G]) (n : ℕ) :
    TensorChains k G M n ≃+ C k G M n :=
  (tensorCongr (rightCoordinates k G n)).trans
    (freeTensorEquiv.trans (Finsupp.mapRange.addEquiv
      (RestrictScalars.addEquiv k k[G] M).symm))

@[simp] theorem tensorCoordinatesAdd_symm_single (M : ModuleCat.{w} k[G]) (n : ℕ)
    (g : Fin n → G) (m : RestrictScalars k k[G] M) :
    (tensorCoordinatesAdd k G M n).symm (Finsupp.single g m) =
      tmul k[G] ((untwist k G _).symm (GroupBar.Large.single.{u,v,0} k G (barTuple G g) 1))
        (RestrictScalars.addEquiv k k[G] M m) := by
  simp only [tensorCoordinatesAdd, AddEquiv.symm_trans_apply, AddEquiv.trans_apply,
    Finsupp.mapRange.addEquiv_symm, Finsupp.mapRange.addEquiv_apply, Finsupp.mapRange_single,
    AddEquiv.symm_symm, freeTensorEquiv_symm_single, tensorCongr_symm_tmul]
  change tmul k[G] ((rightCoordinates k G n).symm
    (Finsupp.single g (MulOpposite.op (MonoidAlgebra.single (1:G) (1:k))))) (RestrictScalars.addEquiv k k[G] M m) = _
  rw [rightCoordinates_symm_single]
  simp only [inv_one, one_smul]

lemma twist_algebraMap_smul (V : Rep k G) (a : k) (x : Twist k G V) :
    MulOpposite.op (algebraMap k k[G] a) • x = a • x := by
  change (inversion k G).symm (MulOpposite.op (algebraMap k k[G] a)) •
    (show V.ρ.asModule from x) = a • (show V.ρ.asModule from x)
  have h : (inversion k G).symm (MulOpposite.op (algebraMap k k[G] a)) = algebraMap k k[G] a := by
    simp [MonoidAlgebra.coe_algebraMap]
  rw [h, algebraMap_smul]

/-- Sending a summand to its normalized homogeneous elementary tensor. -/
def symbolTensor (M : ModuleCat.{w} k[G]) (n : ℕ) (g : Fin n → G) :
    RestrictScalars k k[G] M →ₗ[k] TensorChains k G M n where
  toFun m := tmul k[G]
    ((untwist k G _).symm (GroupBar.Large.single.{u,v,0} k G (barTuple G g) 1))
    (RestrictScalars.addEquiv k k[G] M m)
  map_add' x y := by exact tmul_add _ _ _
  map_smul' a m := by
    change tmul k[G] _ (algebraMap k k[G] a • RestrictScalars.addEquiv k k[G] M m) =
      leftScale a (tmul k[G] _ (RestrictScalars.addEquiv k k[G] M m))
    rw [← balance, leftScale_tmul, twist_algebraMap_smul]

def chainsToTensor (M : ModuleCat.{w} k[G]) (n : ℕ) : C k G M n →ₗ[k] TensorChains k G M n :=
  Finsupp.lsum k (symbolTensor k G M n)

@[simp] lemma chainsToTensor_single (M : ModuleCat.{w} k[G]) (n : ℕ)
    (g : Fin n → G) (m : RestrictScalars k k[G] M) :
    chainsToTensor k G M n (Finsupp.single g m) =
      tmul k[G] ((untwist k G _).symm (GroupBar.Large.single.{u,v,0} k G (barTuple G g) 1))
        (RestrictScalars.addEquiv k k[G] M m) := by
  simp [chainsToTensor, symbolTensor]

lemma chainsToTensor_eq (M : ModuleCat.{w} k[G]) (n : ℕ) (x : C k G M n) :
    chainsToTensor k G M n x = (tensorCoordinatesAdd k G M n).symm x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp_all
  | single g m => simp

/-- The canonical k-linear tensor/direct-sum identification. -/
def tensorIso (M : ModuleCat.{w} k[G]) (n : ℕ) : TensorChains k G M n ≃ₗ[k] C k G M n :=
  (LinearEquiv.ofBijective (chainsToTensor k G M n)
    (by
      rw [show (⇑(chainsToTensor k G M n)) = ⇑(tensorCoordinatesAdd k G M n).symm from
        funext (chainsToTensor_eq k G M n)]
      exact (tensorCoordinatesAdd k G M n).symm.bijective)).symm

@[simp] theorem tensorIso_symm_single (M : ModuleCat.{w} k[G]) (n : ℕ)
    (g : Fin n → G) (m : RestrictScalars k k[G] M) :
    (tensorIso k G M n).symm (Finsupp.single g m) =
      tmul k[G] ((untwist k G _).symm (GroupBar.Large.single.{u,v,0} k G (barTuple G g) 1))
        (RestrictScalars.addEquiv k k[G] M m) := chainsToTensor_single k G M n g m

@[simp] theorem tensorIso_symbol (M : ModuleCat.{w} k[G]) (n : ℕ)
    (g : Fin n → G) (m : RestrictScalars k k[G] M) :
    tensorIso k G M n
      (tmul k[G] ((untwist k G _).symm (GroupBar.Large.single.{u,v,0} k G (barTuple G g) 1))
        (RestrictScalars.addEquiv k k[G] M m)) = Finsupp.single g m := by
  rw [← tensorIso_symm_single, LinearEquiv.apply_symm_apply]

/-- The differential transported from the genuine right-left tensor complex. -/
def chainBoundary (M : ModuleCat.{w} k[G]) (n : ℕ) : C k G M (n+1) →ₗ[k] C k G M n :=
  (tensorIso k G M n).toLinearMap ∘ₗ tensorBoundary k G M n ∘ₗ
    (tensorIso k G M (n+1)).symm.toLinearMap

lemma tensorBoundary_squared (M : ModuleCat.{w} k[G]) (n : ℕ) (z : TensorChains k G M (n+2)) :
    tensorBoundary k G M n (tensorBoundary k G M (n+1) z) = 0 := by
  induction z using P103.BalancedTensor.induction_on with
  | h0 => simp
  | ht b m =>
    change tmul k[G] (boundary k G n (boundary k G (n+1) b)) m = 0
    have h := LinearMap.congr_fun (boundary_squared k G n) b
    change boundary k G n (boundary k G (n+1) b) = 0 at h
    rw [h, zero_tmul]
  | ha x y hx hy => simp_all

theorem chainBoundary_squared (M : ModuleCat.{w} k[G]) (n : ℕ) :
    chainBoundary k G M n ∘ₗ chainBoundary k G M (n+1) = 0 := by
  ext x
  simp [chainBoundary, tensorBoundary_squared]

lemma chainBoundary_tensorIso (M : ModuleCat.{w} k[G]) (n : ℕ) (z : TensorChains k G M (n+1)) :
    chainBoundary k G M n (tensorIso k G M (n+1) z) =
      tensorIso k G M n (tensorBoundary k G M n z) := by
  simp [chainBoundary]

/-- The right bar chain complex, before tensoring. -/
def rightComplex : ChainComplex (ModuleCat k[G]ᵐᵒᵖ) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of k[G]ᵐᵒᵖ (B k G n))
    (fun n => ModuleCat.ofHom (boundary k G n)) (fun n => by
      apply ModuleCat.hom_ext
      exact boundary_squared k G n)

/-- The coefficient chain complex, with C₀ canonically equal to M. -/
def coefficientComplex (M : ModuleCat.{w} k[G]) : ChainComplex (ModuleCat k) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of k (C k G M n))
    (fun n => ModuleCat.ofHom (chainBoundary k G M n)) (fun n => by
      apply ModuleCat.hom_ext
      exact chainBoundary_squared k G M n)

/-- The degree-zero direct sum has exactly one summand. -/
def degreeZeroIso (M : ModuleCat.{w} k[G]) : C k G M 0 ≃ₗ[k] RestrictScalars k k[G] M :=
  Finsupp.uniqueLinearEquiv k _ (fun i => Fin.elim0 i)

@[simp] lemma degreeZeroIso_single (M : ModuleCat.{w} k[G]) (g : Fin 0 → G)
    (m : RestrictScalars k k[G] M) : degreeZeroIso k G M (Finsupp.single g m) = m := by
  simp [degreeZeroIso, Finsupp.uniqueLinearEquiv_apply, Subsingleton.elim g (fun i => Fin.elim0 i)]

lemma homogeneous_boundary_barTuple (n : ℕ) (g : Fin (n+1) → G) :
    GroupBar.Large.d.{u,v,0} k G n (GroupBar.Large.single.{u,v,0} k G (barTuple G g) 1) =
      (GroupBar.Large.B.{u,v,0} k G n).ρ (g 0) (GroupBar.Large.single.{u,v,0} k G (barTuple G (Fin.tail g)) 1) +
      ∑ j : Fin (n+1), (-1:k)^(j.val+1) •
        GroupBar.Large.single.{u,v,0} k G (barTuple G (j.contractNth (· * ·) g)) 1 := by
  rw [GroupBar.Large.boundary_single, Fin.sum_univ_succ, GroupBar.Large.diagonal_action]
  have h : Fin.partialProd g ∘ Fin.succ = g 0 • Fin.partialProd (Fin.tail g) := by
    funext i
    exact Fin.partialProd_succ' g i
  simp only [barTuple, GroupBar.Large.single, Fin.val_zero, pow_zero, mul_one, Fin.succAbove_zero,
    Fin.val_succ, ← Fin.partialProd_contractNth, MonoidAlgebra.smul_single, smul_eq_mul,
    mul_one, one_mul]
  rw [h]
  rfl

lemma twisted_boundary_barTuple (n : ℕ) (g : Fin (n+1) → G) :
    boundary k G n ((untwist k G _).symm (GroupBar.Large.single.{u,v,0} k G (barTuple G g) 1)) =
      MulOpposite.op (MonoidAlgebra.single (g 0)⁻¹ (1:k)) •
        (untwist k G _).symm (GroupBar.Large.single.{u,v,0} k G (barTuple G (Fin.tail g)) 1) +
      ∑ j : Fin (n+1), (-1:k)^(j.val+1) •
        (untwist k G _).symm
          (GroupBar.Large.single.{u,v,0} k G (barTuple G (j.contractNth (· * ·) g)) 1) := by
  apply (untwist k G (GroupBar.Large.B.{u,v,0} k G n)).injective
  simp only [map_add, map_sum, map_smul, twist_group_smul,
    LinearEquiv.apply_symm_apply, inv_inv]
  rw [twist_group_smul k G (GroupBar.Large.B.{u,v,0} k G n) ((g 0)⁻¹)]
  simp only [inv_inv, LinearEquiv.apply_symm_apply]
  exact homogeneous_boundary_barTuple k G n g

lemma tensor_sum_left {A N ι : Type*} [AddCommGroup A] [AddCommGroup N]
    [Module k[G]ᵐᵒᵖ A] [Module k[G] N] (s : Finset ι) (a : ι → A) (m : N) :
    tmul k[G] (∑ i ∈ s, a i) m = ∑ i ∈ s, tmul k[G] (a i) m :=
  map_sum (pairing.toBiadditive.flip m) a s

lemma chainBoundary_single_combined (M : ModuleCat.{w} k[G]) (n : ℕ)
    (g : Fin (n+1) → G) (m : RestrictScalars k k[G] M) :
    chainBoundary k G M n (Finsupp.single g m) =
      Finsupp.single (Fin.tail g) (GroupCoinvariants.coefficientRepresentation k G M (g 0)⁻¹ m) +
      ∑ j : Fin (n+1), (-1:k)^(j.val+1) •
        Finsupp.single (j.contractNth (· * ·) g) m := by
  rw [← tensorIso_symbol k G M (n+1) g m, chainBoundary_tensorIso]
  change tensorIso k G M n
    (tmul k[G] (boundary k G n ((untwist k G _).symm
      (GroupBar.Large.single.{u,v,0} k G (barTuple G g) 1))) (RestrictScalars.addEquiv k k[G] M m)) = _
  rw [twisted_boundary_barTuple, add_tmul, tensor_sum_left, map_add, map_sum]
  congr 1
  · rw [balance]
    exact tensorIso_symbol k G M n (Fin.tail g)
      (GroupCoinvariants.coefficientRepresentation k G M (g 0)⁻¹ m)
  · apply Finset.sum_congr rfl
    intro j _
    change tensorIso k G M n (((-1:k)^(j.val+1)) •
      (tmul k[G] ((untwist k G _).symm
        (GroupBar.Large.single.{u,v,0} k G (barTuple G (j.contractNth (· * ·) g)) 1))
        (RestrictScalars.addEquiv k k[G] M m))) = _
    rw [map_smul, tensorIso_symbol]

lemma contractNth_last (n : ℕ) (g : Fin (n+1) → G) :
    (Fin.last n).contractNth (· * ·) g = Fin.init g := by
  funext i
  rw [Fin.contractNth_apply_of_lt _ _ _ _ i.isLt]
  rfl

/-- The printed boundary, with internal and final faces separated. -/
theorem chainBoundary_single (M : ModuleCat.{w} k[G]) (n : ℕ)
    (g : Fin (n+1) → G) (m : RestrictScalars k k[G] M) :
    chainBoundary k G M n (Finsupp.single g m) =
      Finsupp.single (Fin.tail g) (GroupCoinvariants.coefficientRepresentation k G M (g 0)⁻¹ m) +
      (∑ i : Fin n, (-1:k)^(i.val+1) •
        Finsupp.single (i.castSucc.contractNth (· * ·) g) m) +
      (-1:k)^(n+1) • Finsupp.single (Fin.init g) m := by
  rw [chainBoundary_single_combined, Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, contractNth_last, add_assoc]

/-- The augmentation as a morphism of right group-algebra modules. -/
def rightAugmentation : B k G 0 →ₗ[k[G]ᵐᵒᵖ] GroupCoinvariants.TrivialRight k G where
  __ := (augmentationLinear k G).toAddMonoidHom
  map_smul' r x := augmentation_right_smul k G r.unop x

/-- HA-A10: the normalized right bar tensor model, with its inverse-action
boundary and its chain identity in every degree. -/
theorem barModel : Specification.barModelType.{u,v,w} := by
  intro k G _ _ M
  exact ⟨tensorIso k G M, chainBoundary k G M, degreeZeroIso k G M,
    tensorIso_symbol k G M, chainBoundary_tensorIso k G M,
    chainBoundary_single k G M, chainBoundary_squared k G M,
    degreeZeroIso_single k G M⟩

end AdvancedHomologicalAlgebra.RightBar
