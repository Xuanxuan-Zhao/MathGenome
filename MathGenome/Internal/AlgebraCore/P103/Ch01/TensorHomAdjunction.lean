import MathGenome.Internal.AlgebraCore.Specs.P103.Ch01.TensorHomAdjunction
import MathGenome.Internal.AlgebraCore.P103.Ch01.BalancedTensor
import MathGenome.Internal.AlgebraCore.P103.Ch01.Scalars

namespace P103.TensorHom
open P103.BalancedTensor
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
universe u v w x y

section Currying
variable {R : Type u} {S : Type v} [Ring R] [Ring S]
variable {A : Type w} {B : Type x} {C : Type y}
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [Module Rᵐᵒᵖ A] [Module R B] [Module Sᵐᵒᵖ B] [Module Sᵐᵒᵖ C]
variable [SMulCommClass Sᵐᵒᵖ R B]
variable [Module Sᵐᵒᵖ (Tensor R A B)]
local instance : Module Rᵐᵒᵖ (B →ₗ[Sᵐᵒᵖ] C) := homModule

variable (hT : ∀ (s : Sᵐᵒᵖ) (a : A) (b : B), s • tmul R a b = tmul R a (s • b))

/-- Evaluation on elementary tensors, curried in the first variable. -/
def curry (f : Tensor R A B →ₗ[Sᵐᵒᵖ] C) : Curried R S A B C := by
  letI := homModule (R := R) (S := S) (B := B) (C := C)
  exact {
    toFun := fun a => {
      toFun := fun b => f (tmul R a b)
      map_add' := fun b b' => by rw [tmul_add, map_add]
      map_smul' := fun s b => by simpa only [RingHom.id_apply] using (congrArg f (hT s a b).symm).trans (f.map_smul s _) }
    map_add' := fun a a' => by ext b; exact congrArg f (add_tmul a a' b) |>.trans (f.map_add _ _)
    map_smul' := fun r a => by
      ext b
      change f (tmul R (r • a) b) = f (tmul R a (r.unop • b))
      exact congrArg f (balance r.unop a b) }

@[simp] theorem curry_apply (f : Tensor R A B →ₗ[Sᵐᵒᵖ] C) (a : A) (b : B) :
    curry hT f a b = f (tmul R a b) := rfl

/-- Evaluation is a balanced biadditive pairing. -/
def evaluationPairing (g : Curried R S A B C) : Pairing R (A := A) (B := B) C :=
  Pairing.ofFun (fun a b => g a b)
    (by intros; simp)
    (by intros; simp)
    (by
      intro r a b
      have h := congrArg (fun q : B →ₗ[Sᵐᵒᵖ] C => q b) (g.map_smul (MulOpposite.op r) a)
      exact h)

/-- The inverse of currying, induced by the balanced evaluation pairing. -/
def uncurry (g : Curried R S A B C) : Tensor R A B →ₗ[Sᵐᵒᵖ] C where
  toFun := lift (evaluationPairing g)
  map_add' := map_add _
  map_smul' s z := by
    induction z using P103.BalancedTensor.induction_on with
    | h0 => simp
    | ht a b =>
      rw [hT]
      change g a (s • b) = s • g a b
      exact (g a).map_smul s b
    | ha z z' hz hz' => simp [smul_add, hz, hz']

@[simp] theorem uncurry_tmul (g : Curried R S A B C) (a : A) (b : B) :
    uncurry hT g (tmul R a b) = g a b := rfl

/-- The additive tensor--Hom isomorphism. -/
def tensorHomEquiv : (Tensor R A B →ₗ[Sᵐᵒᵖ] C) ≃+ Curried R S A B C where
  toFun := curry hT
  invFun := uncurry hT
  left_inv f := by
    apply LinearMap.toAddMonoidHom_injective
    apply P103.BalancedTensor.hom_ext
    intros
    rfl
  right_inv g := by
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    rfl
  map_add' f f' := by
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    rfl

end Currying

theorem satisfiesAdjunction : Spec.ExpectedAdjunction := by
  intro R S _ _ A B C _ _ _ _ _ _ _ _
  letI := rightModule (R := R) (A := A) (B := B) (S := Sᵐᵒᵖ)
  have hT : ∀ (s : Sᵐᵒᵖ) (a : A) (b : B), s • tmul R a b = tmul R a (s • b) :=
    fun _ _ _ => rfl
  exact ⟨inferInstance, hT, tensorHomEquiv hT, (fun _ _ _ => rfl), (fun _ _ _ => rfl)⟩

theorem satisfiesNaturality : Spec.ExpectedNaturality := by
  intro R S _ _ A B C A' B' C' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e e' he he' aMap bMap cMap tensorMap hMap f a b
  rw [he', LinearMap.comp_apply, LinearMap.comp_apply, hMap, he]

section ScalarExtension
variable {R : Type u} {S : Type v} [Ring R] [Ring S] (u : R →+* S)

/-- The regular left action and the restricted right action commute. -/
theorem extensionComm : letI := ringRightModule u; SMulCommClass S Rᵐᵒᵖ S := by
  letI := ringRightModule u
  refine ⟨fun s r t => ?_⟩
  change s * (t * u r.unop) = (s * t) * u r.unop
  exact (mul_assoc _ _ _).symm

@[instance_reducible] def extensionModule (M : Type w) [AddCommGroup M] [Module R M] :
    Module S (Extension u M) := by
  letI := ringRightModule u
  letI := extensionComm u
  exact leftModule

@[simp] theorem extensionModule_tmul (M : Type w) [AddCommGroup M] [Module R M]
    (s t : S) (m : M) :
    letI := extensionModule u M
    s • extensionTmul u t m = extensionTmul u (s * t) m := rfl

variable {M : Type w} {N : Type x} [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module S N] [Module S (Extension u M)]
variable (hM : ∀ (s t : S) (m : M),
  s • extensionTmul u t m = extensionTmul u (s * t) m)

/-- Evaluation on `1 ⊗ m`, for any tensor action with its elementary formula. -/
def extensionCurry (f : Extension u M →ₗ[S] N) : RestrictedHom u M N := by
  letI := ringRightModule u
  letI := P103.Scalars.restrictModule u N
  refine { toFun := fun m => f (extensionTmul u 1 m)
           map_add' := ?_
           map_smul' := ?_ }
  · intro m n
    change f (tmul R 1 (m + n)) = f (tmul R 1 m) + f (tmul R 1 n)
    rw [tmul_add, map_add]
  · intro r m
    change f (tmul R 1 (r • m)) = u r • f (tmul R 1 m)
    rw [← balance]
    change f (extensionTmul u (1 * u r) m) = u r • f (extensionTmul u 1 m)
    rw [one_mul]
    have ht := hM (u r) 1 m
    simp only [mul_one] at ht
    rw [← ht, f.map_smul]

/-- The balanced evaluation pairing for extension of scalars. -/
def extensionEvaluation (g : RestrictedHom u M N) :
    letI := ringRightModule u; Pairing R (A := S) (B := M) N := by
  letI := ringRightModule u
  letI := P103.Scalars.restrictModule u N
  refine Pairing.ofFun (fun s m => s • g m) ?_ ?_ ?_
  · intros; exact add_smul _ _ _
  · intros; rw [map_add, smul_add]
  · intro r s m
    change (s * u r) • g m = s • g (r • m)
    rw [g.map_smul]
    exact mul_smul s (u r) (g m)

/-- The map induced by `s ⊗ m ↦ s • g m`. -/
def extensionUncurry (g : RestrictedHom u M N) : Extension u M →ₗ[S] N := by
  letI := ringRightModule u
  refine { toAddHom := lift (extensionEvaluation u g)
           map_smul' := ?_ }
  intro s z
  change lift (extensionEvaluation u g) (s • z) = s • lift (extensionEvaluation u g) z
  induction z using P103.BalancedTensor.induction_on with
  | h0 => simp
  | ht t m =>
    change lift (extensionEvaluation u g) (s • extensionTmul u t m) =
      s • lift (extensionEvaluation u g) (extensionTmul u t m)
    rw [hM]
    exact mul_smul s t (g m)
  | ha z z' hz hz' => simp only [smul_add, map_add, hz, hz']

@[simp] theorem extensionCurry_apply (f : Extension u M →ₗ[S] N) (m : M) :
    extensionCurry u hM f m = f (extensionTmul u 1 m) := rfl

@[simp] theorem extensionUncurry_tmul (g : RestrictedHom u M N) (s : S) (m : M) :
    extensionUncurry u hM g (extensionTmul u s m) = s • g m := rfl

/-- Scalar extension is left adjoint to scalar restriction. -/
def extensionHomEquiv : (Extension u M →ₗ[S] N) ≃+ RestrictedHom u M N := by
  letI := ringRightModule u
  letI := P103.Scalars.restrictModule u N
  exact {
  toFun := extensionCurry u hM
  invFun := extensionUncurry u hM
  left_inv f := by
    apply LinearMap.toAddMonoidHom_injective
    apply P103.BalancedTensor.hom_ext
    intro s m
    change s • f (extensionTmul u 1 m) = f (extensionTmul u s m)
    rw [← f.map_smul, hM, mul_one]
  right_inv g := by
    ext m
    change (1 : S) • g m = g m
    exact one_smul S (g m)
  map_add' f f' := by
    ext m
    rfl }

end ScalarExtension

section ScalarExtensionMaps
variable {R : Type u} {S : Type v} [Ring R] [Ring S] (u : R →+* S)
variable {M : Type w} {M' : Type x} [AddCommGroup M] [AddCommGroup M']
variable [Module R M] [Module R M'] [Module S (Extension u M)] [Module S (Extension u M')]
variable (hM : ∀ (s t : S) (m : M), s • extensionTmul u t m = extensionTmul u (s * t) m)
variable (hM' : ∀ (s t : S) (m : M'), s • extensionTmul u t m = extensionTmul u (s * t) m)

/-- Extension of a linear map, for any compatible tensor actions. -/
def extensionMap (f : M →ₗ[R] M') : Extension u M →ₗ[S] Extension u M' := by
  letI := ringRightModule u
  refine { toAddHom := P103.BalancedTensor.map (LinearMap.id : S →ₗ[Rᵐᵒᵖ] S) f
           map_smul' := ?_ }
  intro s z
  change P103.BalancedTensor.map LinearMap.id f (s • z) =
    s • P103.BalancedTensor.map LinearMap.id f z
  induction z using P103.BalancedTensor.induction_on with
  | h0 => simp
  | ht t m =>
    change P103.BalancedTensor.map LinearMap.id f (s • extensionTmul u t m) =
      s • P103.BalancedTensor.map LinearMap.id f (extensionTmul u t m)
    rw [hM]
    change extensionTmul u (s * t) (f m) = s • extensionTmul u t (f m)
    exact (hM' s t (f m)).symm
  | ha z z' hz hz' => simp only [smul_add, map_add, hz, hz']

@[simp] theorem extensionMap_tmul (f : M →ₗ[R] M') (s : S) (m : M) :
    extensionMap u hM hM' f (extensionTmul u s m) = extensionTmul u s (f m) := rfl

end ScalarExtensionMaps

/-- Scalar extension's additive Hom equivalence with its two formulas. -/
theorem satisfiesExtension : Spec.ExpectedExtension := by
  intro R S _ _ u M N _ _ _ _
  refine ⟨extensionModule u M, ?_⟩
  letI := extensionModule u M
  refine ⟨fun s t m => rfl, extensionHomEquiv u (fun s t m => rfl), ?_, ?_⟩
  · intros; rfl
  · intros; rfl

/-- The scalar-extension maps satisfy the generator, composition and identity laws. -/
theorem satisfiesExtensionMaps : Spec.ExpectedExtensionMaps := by
  intro R S _ _ u M M' M'' _ _ _ _ _ _ _ _ _ hM hM' hM''
  letI := ringRightModule u
  refine ⟨extensionMap u hM hM', extensionMap u hM' hM'', extensionMap u hM hM'',
    (fun _ _ _ => rfl), (fun _ _ _ => rfl), (fun _ _ _ => rfl), ?_, ?_⟩
  · intro f g
    apply LinearMap.toAddMonoidHom_injective
    apply P103.BalancedTensor.hom_ext
    intros
    rfl
  · intro J hJ
    apply LinearMap.toAddMonoidHom_injective
    apply P103.BalancedTensor.hom_ext
    exact hJ

/-- The scalar-extension Hom equivalence commutes with maps in both variables. -/
theorem satisfiesExtensionNaturality : Spec.ExpectedExtensionNaturality := by
  intro R S _ _ u M M' N N' _ _ _ _ _ _ _ _ _ _ e e' he he' a b F hF f x
  rw [he', he]
  change b (f (F (extensionTmul u 1 x))) = b (f (extensionTmul u 1 (a x)))
  rw [hF]


section UnitCounit
variable {R S : Type*} [Ring R] [Ring S] (u : R →+* S)

/-- The adjunction unit, with its restricted codomain action. -/
def extensionUnit (M : Type*) [AddCommGroup M] [Module R M]
    [Module S (Extension u M)]
    (hM : ∀ (s t : S) (x : M), s • extensionTmul u t x = extensionTmul u (s*t) x) :
    letI := P103.Scalars.restrictModule u (Extension u M)
    M →ₗ[R] Extension u M :=
  extensionCurry u hM LinearMap.id

/-- The adjunction counit is evaluation of scalar multiplication. -/
def extensionCounit (N : Type*) [AddCommGroup N] [Module S N] :
    letI := P103.Scalars.restrictModule u N
    ∀ [Module S (Extension u N)]
      (hN : ∀ (s t : S) (x : N), s • extensionTmul u t x = extensionTmul u (s*t) x),
      Extension u N →ₗ[S] N := by
  letI := P103.Scalars.restrictModule u N
  intro _ hN
  exact extensionUncurry u hN LinearMap.id

end UnitCounit

theorem satisfiesUnit : Spec.ExpectedUnit := by
  intro R S _ _ u M _ _ _ hM
  exact ⟨extensionUnit u M hM, fun _ => rfl⟩

theorem satisfiesCounit : Spec.ExpectedCounit := by
  intro R S _ _ u N _ _
  letI := P103.Scalars.restrictModule u N
  intro _ hN
  exact ⟨extensionCounit u N hN, fun _ _ => rfl⟩

theorem satisfiesExtensionTriangle : Spec.ExpectedExtensionTriangle := by
  intro R S _ _ u M _ _ _ hT
  letI := P103.Scalars.restrictModule u (Extension u M)
  intro _ eta heta Feta hFeta eps heps
  apply LinearMap.toAddMonoidHom_injective
  letI := ringRightModule u
  apply P103.BalancedTensor.hom_ext
  intro s x
  change eps (Feta (extensionTmul u s x)) = extensionTmul u s x
  rw [hFeta, heps, heta, hT, mul_one]

theorem satisfiesRestrictionTriangle : Spec.ExpectedRestrictionTriangle := by
  intro R S _ _ u N _ _
  letI := P103.Scalars.restrictModule u N
  intro _
  letI := P103.Scalars.restrictModule u (Extension u N)
  intro eta heta eps heps
  apply LinearMap.ext
  intro x
  change eps (eta x) = x
  rw [heta, heps, one_smul]

/-- Equivariance is detected on elementary tensors in the first variable. -/
theorem satisfiesFirstOuterScalars : Spec.ExpectedFirstOuterScalars := by
  intro R S T _ _ _ A B C _ _ _ _ _ _ _ _ _ _ _ _ hT e he f
  constructor
  · intro hf t a b
    rw [he, he, ← hT, hf]
  · intro hg t z
    induction z using P103.BalancedTensor.induction_on with
    | h0 => simp
    | ht a b =>
      rw [hT]
      simpa only [he] using hg t a b
    | ha z z' hz hz' => simp only [smul_add, map_add, hz, hz']

/-- Equivariance is detected on elementary tensors in the second variable. -/
theorem satisfiesSecondOuterScalars : Spec.ExpectedSecondOuterScalars := by
  intro R S T _ _ _ A B C _ _ _ _ _ _ _ _ _ _ _ _ hT e he f
  constructor
  · intro hf t a b
    rw [he, he, ← hT, hf]
  · intro hg t z
    induction z using P103.BalancedTensor.induction_on with
    | h0 => simp
    | ht a b =>
      rw [hT]
      simpa only [he] using hg t a b
    | ha z z' hz hz' => simp only [smul_add, map_add, hz, hz']

/-- Equivariance is preserved in both directions by scalar extension's Hom equivalence. -/
theorem satisfiesExtensionOuterScalars : Spec.ExpectedExtensionOuterScalars := by
  intro R S T _ _ _ u M N _ _ _ _ _ _ _ _ _ hT e he heInv f
  constructor
  · intro hf t x
    rw [he, he, ← hT, hf]
  · intro hg t z
    have hf (s : S) (x : M) : f (extensionTmul u s x) = s • e f x := by
      simpa only [e.symm_apply_apply] using heInv (e f) s x
    letI := ringRightModule u
    induction z using P103.BalancedTensor.induction_on with
    | h0 => simp
    | ht s x =>
      change f (t • extensionTmul u s x) = t • f (extensionTmul u s x)
      rw [hT, hf, hg, hf]
      exact (smul_comm t s (e f x)).symm
    | ha z z' hz hz' => simp only [smul_add, map_add, hz, hz']


/-- Identity preservation for the scalar-extension functor. -/
theorem satisfiesExtensionIdentity : Spec.ExpectedExtensionIdentity := by
  intro R S _ _ u M _ _ _ hM
  letI := ringRightModule u
  refine ⟨extensionMap u hM hM, (fun _ _ _ => rfl), ?_⟩
  apply LinearMap.toAddMonoidHom_injective
  apply P103.BalancedTensor.hom_ext
  intros
  rfl

theorem satisfiesUnitNaturality : Spec.ExpectedUnitNaturality := by
  intro R S _ _ u M M' _ _ _ _ _ _
  letI := P103.Scalars.restrictModule u (Extension u M)
  letI := P103.Scalars.restrictModule u (Extension u M')
  intro eta heta eta' heta' f F hF
  apply LinearMap.ext
  intro x
  change F (eta x) = eta' (f x)
  rw [heta, heta', hF]

theorem satisfiesCounitNaturality : Spec.ExpectedCounitNaturality := by
  intro R S _ _ u N N' _ _ _ _
  letI := P103.Scalars.restrictModule u N
  letI := P103.Scalars.restrictModule u N'
  intro _ _ eps heps eps' heps' g F hF
  apply LinearMap.toAddMonoidHom_injective
  letI := ringRightModule u
  apply P103.BalancedTensor.hom_ext
  intro s x
  change g (eps (extensionTmul u s x)) = eps' (F (extensionTmul u s x))
  rw [heps, hF, heps', g.map_smul]



/-- Bimodule maps induce actual maps used by tensor--Hom naturality. -/
theorem satisfiesTensorMaps : Spec.ExpectedTensorMaps := by
  intro R S _ _ A B A' B' _ _ _ _ _ _ _ _ _ _ _ _ _ _ hT hT' aMap bMap hbMap
  refine ⟨{ toAddHom := P103.BalancedTensor.map aMap bMap, map_smul' := ?_ },
    fun _ _ => rfl⟩
  intro s z
  change P103.BalancedTensor.map aMap bMap (s • z) =
    s • P103.BalancedTensor.map aMap bMap z
  induction z using P103.BalancedTensor.induction_on with
  | h0 => simp
  | ht a b =>
    rw [hT]
    change tmul R (aMap a) (bMap (s • b)) = s • tmul R (aMap a) (bMap b)
    rw [hbMap, hT']
  | ha z z' hz hz' => simp only [smul_add, map_add, hz, hz']


end P103.TensorHom
