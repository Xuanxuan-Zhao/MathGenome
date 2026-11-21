import MathGenome.Internal.AlgebraCore.Specs.P103.Ch03.MoritaEquivalence
import MathGenome.Internal.AlgebraCore.P103.Ch03.MoritaEvaluations
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
universe u v w x
namespace P103.Ch03.MoritaEquivalence
open CategoryTheory MulOpposite P103.BalancedTensor P103.Morita

section TensorFunctor
variable (R : Type u) (T : Type v) [Ring R] [Ring T]
variable (B : Type w) [AddCommGroup B] [Module R B] [Module Tᵐᵒᵖ B]
variable [SMulCommClass Tᵐᵒᵖ R B]

@[instance_reducible] local instance tensorAction (A : Type*) [AddCommGroup A] [Module Rᵐᵒᵖ A] :
    Module Tᵐᵒᵖ (Tensor R A B) := rightModule

/-- Tensoring with a bimodule is a functor on right module categories.
The universe of the module category can be any universe containing B. -/
@[reducible] def tensorFunctor : ModuleCat.{max u v w x} Rᵐᵒᵖ ⥤ ModuleCat.{max u v w x} Tᵐᵒᵖ where
  obj X := ModuleCat.of Tᵐᵒᵖ (Tensor R X B)
  map f := ModuleCat.ofHom (mapRightLinear f.hom LinearMap.id (fun _ _ => rfl))
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    exact map_id
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    exact map_comp f.hom LinearMap.id g.hom LinearMap.id

@[simp] theorem tensorFunctor_map_tmul {X Y : ModuleCat.{max u v w x} Rᵐᵒᵖ}
    (f : X ⟶ Y) (x : X) (b : B) :
    (tensorFunctor R T B).map f (tmul R x b) = tmul R (f x) b := rfl

@[simp] theorem tensorFunctor_smul_tmul (X : ModuleCat.{max u v w x} Rᵐᵒᵖ)
    (t : Tᵐᵒᵖ) (x : X) (b : B) :
    t • (tmul R x b : (tensorFunctor R T B).obj X) = tmul R x (t • b) := rfl
end TensorFunctor

section TensorCongruence
variable {R : Type u} [Ring R]
variable {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
variable {B : Type w} {B' : Type x} [AddCommGroup B] [AddCommGroup B']
variable [Module R B] [Module R B']

/-- An isomorphism of the left factor modules induces an additive tensor
isomorphism. No commutativity assumption on the ring is used. -/
def tensorCongrRight (e : B ≃ₗ[R] B') : Tensor R A B ≃+ Tensor R A B' where
  toFun := map LinearMap.id e.toLinearMap
  invFun := map LinearMap.id e.symm.toLinearMap
  map_add' := map_add _
  left_inv z := by
    induction z using P103.BalancedTensor.induction_on with
    | h0 => simp
    | ht a b => simp
    | ha z z' hz hz' => simp [hz, hz']
  right_inv z := by
    induction z using P103.BalancedTensor.induction_on with
    | h0 => simp
    | ht a b => simp
    | ha z z' hz hz' => simp [hz, hz']

@[simp] theorem tensorCongrRight_tmul (e : B ≃ₗ[R] B') (a : A) (b : B) :
    tensorCongrRight e (tmul R a b) = tmul R a (e b) := rfl
end TensorCongruence

section TensorCancellation
variable {R : Type u} {T : Type v} [Ring R] [Ring T]
variable {B : Type w} {C : Type x} [AddCommGroup B] [AddCommGroup C]
variable [Module R B] [Module Tᵐᵒᵖ B] [SMulCommClass Tᵐᵒᵖ R B]
variable [Module T C] [Module Rᵐᵒᵖ C] [SMulCommClass Rᵐᵒᵖ T C]

local instance bimoduleCommute : SMulCommClass R Tᵐᵒᵖ B where
  smul_comm r t b := (smul_comm t r b).symm

@[instance_reducible] local instance tensorLeftModule : Module R (Tensor T B C) := leftModule

/-- The left-linear evaluation needed to tensor an evaluation isomorphism. -/
def evaluationLinearEquiv (e : Tensor T B C ≃+ R)
    (he : ∀ r z, e (leftScale r z) = r * e z) : Tensor T B C ≃ₗ[R] R :=
  { e with map_smul' := fun r z => he r z }

variable (A : Type*) [AddCommGroup A] [Module Rᵐᵒᵖ A]
@[instance_reducible] local instance tensorInnerModule : Module Tᵐᵒᵖ (Tensor R A B) := rightModule
@[instance_reducible] local instance tensorOuterModule : Module Rᵐᵒᵖ (Tensor T (Tensor R A B) C) := rightModule

/-- Associativity, tensoring the evaluation, and the tensor unit give the
contraction of a composite tensor functor. -/
def cancelAddEquiv (e : Tensor T B C ≃+ R)
    (he : ∀ r z, e (leftScale r z) = r * e z) :
    Tensor T (Tensor R A B) C ≃+ A :=
  (assocWith (fun _ _ _ => rfl) (fun _ _ _ => rfl)).trans
    ((tensorCongrRight (evaluationLinearEquiv e he)).trans rightUnit)

@[simp] theorem cancelAddEquiv_tmul (e : Tensor T B C ≃+ R)
    (he : ∀ r z, e (leftScale r z) = r * e z) (a : A) (b : B) (c : C) :
    cancelAddEquiv A e he (tmul T (tmul R a b) c) = op (e (tmul T b c)) • a := by
  rfl

/-- The contraction also respects the unused right action. -/
def cancelLinearEquiv (e : Tensor T B C ≃+ R)
    (heL : ∀ r z, e (leftScale r z) = r * e z)
    (heR : ∀ (r : Rᵐᵒᵖ) z, e (rightScale r z) = e z * r.unop) :
    Tensor T (Tensor R A B) C ≃ₗ[Rᵐᵒᵖ] A :=
  { cancelAddEquiv A e heL with
    map_smul' := by
      intro r z
      change cancelAddEquiv A e heL (rightScale r z) = r • cancelAddEquiv A e heL z
      induction z using P103.BalancedTensor.induction_on with
      | h0 => simp
      | ha z z' hz hz' => simp [hz, hz', smul_add]
      | ht t c =>
        induction t using P103.BalancedTensor.induction_on with
        | h0 => simp
        | ha t t' ht ht' =>
          simp only [rightScale_tmul] at ht ht' ⊢
          simp [add_tmul, ht, ht', smul_add]
        | ht a b =>
          simp only [rightScale_tmul, cancelAddEquiv_tmul]
          rw [show e (tmul T b (r • c)) = e (tmul T b c) * r.unop from
            heR r (tmul T b c)]
          simp [smul_smul] }
end TensorCancellation

section MoritaFunctors
variable (R : Type u) [Ring R] (P : Type v) [AddCommGroup P] [Module Rᵐᵒᵖ P]

/-- Forward functor X ↦ X ⊗[R] Hom_R(P,R). -/
abbrev toEndModules : ModuleCat.{max u v w} Rᵐᵒᵖ ⥤
    ModuleCat.{max u v w} (S R P)ᵐᵒᵖ := tensorFunctor R (S R P) (Q R P)

/-- Inverse functor Y ↦ Y ⊗[End_R(P)] P. -/
abbrev fromEndModules : ModuleCat.{max u v w} (S R P)ᵐᵒᵖ ⥤
    ModuleCat.{max u v w} Rᵐᵒᵖ := tensorFunctor (S R P) R P

/-- The two evaluation identities which enforce the triangle laws. -/
theorem theta_smul (p : P) (q : Q R P) (p' : P) :
    theta R P p q • p' = op (q p') • p := rfl

theorem dual_theta (q : Q R P) (p : P) (q' : Q R P) :
    op (theta R P p q') • q = q p • q' :=
  P103.Ch03.MoritaEvaluations.functional_theta q q' p
end MoritaFunctors

section Evaluations
open P103.Ch03.MoritaEvaluations
variable {R : Type u} [Ring R] {P : Type v} [AddCommGroup P] [Module Rᵐᵒᵖ P]

private theorem evalIso_exists (hG : IsGenerator R P) :
    ∃ e : Tensor (S R P) (Q R P) P ≃+ R, ∀ z, e z = evalMap z := by
  obtain ⟨J, t, a, b, ht⟩ := finite_trace hG
  exact ⟨evalEquiv t a b ht, fun _ => rfl⟩

/-- The second evaluation isomorphism, whose underlying map is canonical. -/
def evalIso (hG : IsGenerator R P) : Tensor (S R P) (Q R P) P ≃+ R :=
  Classical.choose (evalIso_exists hG)

@[simp] theorem evalIso_apply (hG : IsGenerator R P) (z : Tensor (S R P) (Q R P) P) :
    evalIso hG z = evalMap z := Classical.choose_spec (evalIso_exists hG) z

theorem evalIso_left (hG : IsGenerator R P) (r : R) (z : Tensor (S R P) (Q R P) P) :
    evalIso hG (leftScale r z) = r * evalIso hG z := by
  simp only [evalIso_apply, evalMap_leftScale]

theorem evalIso_right (hG : IsGenerator R P) (r : Rᵐᵒᵖ)
    (z : Tensor (S R P) (Q R P) P) :
    evalIso hG (rightScale r z) = evalIso hG z * r.unop := by
  simp only [evalIso_apply, evalMap_rightScale]

variable [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P]
private theorem endIso_exists :
    ∃ e : Tensor R P (Q R P) ≃+ S R P, ∀ z, e z = endMap z := by
  obtain ⟨n, p, q, h⟩ := finite_dual_basis (R := R) (P := P)
  exact ⟨endEquiv p q h, fun _ => rfl⟩

/-- The first evaluation isomorphism, with composition multiplication. -/
def endIso : Tensor R P (Q R P) ≃+ S R P := Classical.choose (endIso_exists (R := R) (P := P))

@[simp] theorem endIso_apply (z : Tensor R P (Q R P)) :
    endIso z = endMap z := Classical.choose_spec (endIso_exists (R := R) (P := P)) z

theorem endIso_left (s : S R P) (z : Tensor R P (Q R P)) :
    endIso (leftScale s z) = s * endIso z := by
  simp only [endIso_apply, endMap_leftScale]

theorem endIso_right (s : (S R P)ᵐᵒᵖ) (z : Tensor R P (Q R P)) :
    endIso (rightScale s z) = endIso z * s.unop := by
  simp only [endIso_apply, endMap_rightScale]
end Evaluations

section CompositeIsomorphisms
attribute [local instance] tensorAction
variable {R : Type u} [Ring R] {P : Type v} [AddCommGroup P] [Module Rᵐᵒᵖ P]

/-- Evaluation contracts the composite on right R-modules. -/
def rightCompositeIso (hG : IsGenerator R P) :
    toEndModules.{u,v,w} R P ⋙ fromEndModules R P ≅ 𝟭 (ModuleCat.{max u v w} Rᵐᵒᵖ) :=
  NatIso.ofComponents (fun X =>
    (cancelLinearEquiv X (evalIso hG) (evalIso_left hG) (evalIso_right hG)).toModuleIso)
    (by
      intro X Y f
      apply ModuleCat.hom_ext
      apply LinearMap.toAddMonoidHom_injective
      apply P103.BalancedTensor.hom_ext
      intro t p
      change cancelAddEquiv Y (evalIso hG) (evalIso_left hG)
          (map (mapRightLinear f.hom LinearMap.id (fun _ _ => rfl)) LinearMap.id
            (tmul (S R P) t p)) =
        f (cancelAddEquiv X (evalIso hG) (evalIso_left hG) (tmul (S R P) t p))
      induction t using P103.BalancedTensor.induction_on with
      | h0 =>
        rw [zero_tmul]
        simp
      | ha t t' ht ht' =>
        rw [add_tmul]
        simp only [map_add, ht, ht']
      | ht x q =>
        change cancelAddEquiv Y (evalIso hG) (evalIso_left hG)
          (tmul (S R P) (tmul R (f x) q) p) =
          f (cancelAddEquiv X (evalIso hG) (evalIso_left hG) (tmul (S R P) (tmul R x q) p))
        simp only [cancelAddEquiv_tmul, map_smul])

@[simp] theorem rightCompositeIso_hom_tmul (hG : IsGenerator R P)
    (X : ModuleCat.{max u v w} Rᵐᵒᵖ) (x : X) (q : Q R P) (p : P) :
    (rightCompositeIso hG).hom.app X (tmul (S R P) (tmul R x q) p) = op (q p) • x := by
  change cancelAddEquiv X (evalIso hG) (evalIso_left hG) _ = _
  simp only [cancelAddEquiv_tmul, evalIso_apply, P103.Ch03.MoritaEvaluations.evalMap_tmul]

variable [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P]

/-- Evaluation contracts the composite on right endomorphism modules. -/
def endCompositeIso :
    fromEndModules.{u,v,w} R P ⋙ toEndModules R P ≅
      𝟭 (ModuleCat.{max u v w} (S R P)ᵐᵒᵖ) :=
  NatIso.ofComponents (fun Y =>
    (cancelLinearEquiv Y (endIso (R := R) (P := P)) endIso_left endIso_right).toModuleIso)
    (by
      intro X Y f
      apply ModuleCat.hom_ext
      apply LinearMap.toAddMonoidHom_injective
      apply P103.BalancedTensor.hom_ext
      intro t q
      change cancelAddEquiv Y endIso endIso_left
          (map (mapRightLinear f.hom LinearMap.id (fun _ _ => rfl)) LinearMap.id
            (tmul R t q)) =
        f (cancelAddEquiv X endIso endIso_left (tmul R t q))
      induction t using P103.BalancedTensor.induction_on with
      | h0 =>
        rw [zero_tmul]
        simp
      | ha t t' ht ht' =>
        rw [add_tmul]
        simp only [map_add, ht, ht']
      | ht y p =>
        change cancelAddEquiv Y endIso endIso_left
          (tmul R (tmul (S R P) (f y) p) q) =
          f (cancelAddEquiv X endIso endIso_left (tmul R (tmul (S R P) y p) q))
        simp only [cancelAddEquiv_tmul, map_smul])
@[simp] theorem endCompositeIso_hom_tmul
    (Y : ModuleCat.{max u v w} (S R P)ᵐᵒᵖ) (y : Y) (p : P) (q : Q R P) :
    (endCompositeIso (R := R) (P := P)).hom.app Y (tmul R (tmul (S R P) y p) q) =
      op (theta R P p q) • y := by
  change cancelAddEquiv Y endIso endIso_left _ = _
  simp only [cancelAddEquiv_tmul, endIso_apply, P103.Ch03.MoritaEvaluations.endMap_tmul]

/-- Compatibility of the two evaluations gives the forward triangle. -/
theorem evaluation_triangle (hG : IsGenerator R P) (X : ModuleCat.{max u v w} Rᵐᵒᵖ) :
    (toEndModules.{u,v,w} R P).map ((rightCompositeIso.{u,v,w} hG).hom.app X) =
      (endCompositeIso.{u,v,w} (R := R) (P := P)).hom.app
        ((toEndModules.{u,v,w} R P).obj X) := by
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply P103.BalancedTensor.hom_ext
  intro t q'
  induction t using P103.BalancedTensor.induction_on with
  | h0 => rw [zero_tmul]; exact (map_zero _).trans (map_zero _).symm
  | ha t t' ht ht' => rw [add_tmul]; simp only [map_add, ht, ht']
  | ht z p =>
    induction z using P103.BalancedTensor.induction_on with
    | h0 => rw [zero_tmul, zero_tmul]; exact (map_zero _).trans (map_zero _).symm
    | ha z z' hz hz' =>
      rw [add_tmul, add_tmul]
      simp only [map_add, hz, hz']
    | ht x q =>
      change tmul R ((rightCompositeIso hG).hom.app X (tmul (S R P) (tmul R x q) p)) q' =
        (endCompositeIso (R := R) (P := P)).hom.app ((toEndModules R P).obj X)
          (tmul R (tmul (S R P) (tmul R x q) p) q')
      rw [rightCompositeIso_hom_tmul, endCompositeIso_hom_tmul, balance]
      change tmul R x (q p • q') = tmul R x (op (theta R P p q') • q)
      rw [dual_theta]

/-- The tensor equivalence with the evaluation-induced unit and counit. -/
def rightEquivalence (hG : IsGenerator R P) :
    ModuleCat.{max u v w} Rᵐᵒᵖ ≌ ModuleCat.{max u v w} (S R P)ᵐᵒᵖ where
  functor := toEndModules R P
  inverse := fromEndModules R P
  unitIso := (rightCompositeIso hG).symm
  counitIso := endCompositeIso
  functor_unitIso_comp X := by
    rw [← evaluation_triangle hG X, ← Functor.map_comp, Iso.symm_hom, Iso.inv_hom_id_app]
    exact (toEndModules R P).map_id X

/-- Full forward Morita theorem, including tensor descriptions and contractions. -/
theorem right_equivalence : P103.Morita.EquivalenceSpec.rightEquivalenceType.{u,v,w} := by
  intro R _ P _ _ _ _ hG
  refine ⟨rightEquivalence hG, (fun _ => AddEquiv.refl _), (fun _ => AddEquiv.refl _),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · exact rightCompositeIso_hom_tmul hG
  · exact endCompositeIso_hom_tmul
end CompositeIsomorphisms

section MatrixProgenerator
variable (R : Type u) [Ring R]

/-- The right regular module is free of rank one over the opposite ring. -/
def regularRightEquiv : R ≃ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ where
  toFun := op
  invFun := unop
  left_inv := unop_op
  right_inv := op_unop
  map_add' := op_add
  map_smul' _ _ := rfl

/-- Standard coordinate basis, with coefficients multiplying on the right. -/
def rightVectorBasis (n : ℕ) : Module.Basis (Fin n) Rᵐᵒᵖ (Fin n → R) :=
  (Pi.basisFun Rᵐᵒᵖ (Fin n)).map
    (LinearEquiv.piCongrRight (fun _ => regularRightEquiv R)).symm

theorem rightVector_finite (n : ℕ) : Module.Finite Rᵐᵒᵖ (Fin n → R) :=
  Module.Finite.of_basis (rightVectorBasis R n)

theorem rightVector_projective (n : ℕ) : Module.Projective Rᵐᵒᵖ (Fin n → R) :=
  Module.Projective.of_basis (rightVectorBasis R n)

/-- A single nonempty coordinate supplies quotients of sums of copies of R^n. -/
theorem rightVector_generator (n : ℕ) (hn : 0 < n) : IsGenerator R (Fin n → R) := by
  classical
  intro M _ _
  let i : Fin n := ⟨0, hn⟩
  let k : M → (Fin n → R) →ₗ[Rᵐᵒᵖ] M := fun m =>
    { toFun := fun v => op (v i) • m
      map_add' := by intros; simp [add_smul]
      map_smul' := by intros; simp [smul_smul] }
  let f : (M →₀ (Fin n → R)) →ₗ[Rᵐᵒᵖ] M := Finsupp.lsum ℤ k
  refine ⟨M, f, fun m => ⟨Finsupp.single m (Pi.single i 1), ?_⟩⟩
  simp [f, k]

/-- Entries of a right-linear map are its values on standard columns.
This construction works for noncommutative R. -/
def rightVectorEndRing (n : ℕ) :
    Module.End Rᵐᵒᵖ (Fin n → R) ≃+* Matrix (Fin n) (Fin n) R :=
  (endVecRingEquivMatrixEnd (Fin n) Rᵐᵒᵖ R).trans
    ((RingEquiv.moduleEndSelfOp R).symm.mapMatrix)

@[simp] theorem rightVectorEndRing_apply (n : ℕ)
    (f : Module.End Rᵐᵒᵖ (Fin n → R)) (i j : Fin n) :
    rightVectorEndRing R n f i j = f (Pi.single j 1) i := rfl
end MatrixProgenerator

section LeftForm
open P103.Morita.EquivalenceSpec

/-- Passing to the opposite ring gives the left-module theorem. In particular,
the ring acting on the target is the opposite of the left endomorphism ring. -/
theorem left_equivalence : leftEquivalenceType.{u,v,w} := by
  intro R _ P _ _ _ _ hG
  letI : Module Rᵐᵒᵖᵐᵒᵖ P := Module.compHom P (RingEquiv.opOp R).symm.toRingHom
  letI : RingHomInvPair (RingEquiv.opOp R).toRingHom (RingEquiv.opOp R).symm.toRingHom :=
    RingHomInvPair.of_ringEquiv (RingEquiv.opOp R)
  letI : RingHomInvPair (RingEquiv.opOp R).symm.toRingHom (RingEquiv.opOp R).toRingHom :=
    RingHomInvPair.of_ringEquiv_symm (RingEquiv.opOp R)
  let e : @LinearEquiv R Rᵐᵒᵖᵐᵒᵖ _ _ (RingEquiv.opOp R).toRingHom
      (RingEquiv.opOp R).symm.toRingHom _ _ P P _ _ _ _ :=
    { Equiv.refl P with
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  letI : Module.Finite Rᵐᵒᵖᵐᵒᵖ P := Module.Finite.of_surjective e.toLinearMap e.surjective
  letI : Module.Projective Rᵐᵒᵖᵐᵒᵖ P := Module.Projective.of_equiv e
  have hG' : IsGenerator Rᵐᵒᵖ P := by
    intro M _ mM
    letI : Module R M := Module.compHom M (RingEquiv.opOp R).toRingHom
    obtain ⟨J, f, hf⟩ := hG M
    refine ⟨J, { f.toAddMonoidHom with map_smul' := ?_ }, hf⟩
    intro r z
    exact f.map_smul (unop (unop r)) z
  exact ⟨(ModuleCat.restrictScalarsEquivalenceOfRingEquiv (RingEquiv.opOp R)).symm.trans
    ((rightEquivalence.{u,v,w} hG').trans
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.conjRingEquiv.op))⟩
end LeftForm

section MatrixEquivalence
open P103.Morita.EquivalenceSpec
variable (R : Type u) [Ring R]

/-- The analogous coordinate quotient for left modules. -/
theorem leftVector_generator (n : ℕ) (hn : 0 < n) : IsLeftGenerator R (Fin n → R) := by
  classical
  intro M _ _
  let i : Fin n := ⟨0, hn⟩
  let k : M → (Fin n → R) →ₗ[R] M := fun m =>
    { toFun := fun v => v i • m
      map_add' := by intros; simp [add_smul]
      map_smul' := by intros; simp [smul_smul] }
  let f : (M →₀ (Fin n → R)) →ₗ[R] M := Finsupp.lsum ℤ k
  refine ⟨M, f, fun m => ⟨Finsupp.single m (Pi.single i 1), ?_⟩⟩
  simp [f, k]

/-- R and its positive-size matrix ring have equivalent right module categories. -/
def rightMatrixEquivalence (n : ℕ) (hn : 0 < n) :
    ModuleCat.{max u w} Rᵐᵒᵖ ≌ ModuleCat.{max u w} (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ := by
  letI := rightVector_finite R n
  letI := rightVector_projective R n
  exact (rightEquivalence.{u,u,w} (rightVector_generator R n hn)).trans
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv (rightVectorEndRing R n).op.symm)

/-- The left form uses the opposite endomorphism ring of the left free module. -/
theorem leftMatrixEquivalence (n : ℕ) (hn : 0 < n) :
    Nonempty (ModuleCat.{max u w} R ≌ ModuleCat.{max u w} (Matrix (Fin n) (Fin n) R)) := by
  obtain ⟨E⟩ := left_equivalence.{u,u,w} R (Fin n → R) (leftVector_generator R n hn)
  exact ⟨E.trans (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (matrixRingEquivEndVecMulOpposite (ι := Fin n) (A := R)))⟩

/-- Complete matrix specialization, including the chosen free progenerator
and the coefficient formula for its endomorphism-ring identification. -/
theorem matrix_equivalence : matrixEquivalenceType.{u,w} := by
  intro R _ n hn
  exact ⟨rightVector_finite R n, rightVector_projective R n, rightVector_generator R n hn,
    ⟨rightVectorEndRing R n, fun _ _ _ => rfl⟩,
    ⟨rightMatrixEquivalence R n hn⟩, leftMatrixEquivalence R n hn⟩
end MatrixEquivalence

end P103.Ch03.MoritaEquivalence
