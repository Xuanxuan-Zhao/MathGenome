import MathGenome.Internal.AlgebraCore.Specs.P103.Ch01.BalancedTensor
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch01.Scalars

/-! Tensor--Hom and scalar extension over arbitrary unital rings.
All right modules are represented by modules over the opposite ring. -/
namespace P103.TensorHom
open P103.BalancedTensor
set_option linter.unusedVariables false
universe u v w x y

section HomAction
variable {R : Type u} {S : Type v} [Ring R] [Ring S]
variable {B : Type w} {C : Type x} [AddCommGroup B] [AddCommGroup C]
variable [Module R B] [Module Sᵐᵒᵖ B] [Module Sᵐᵒᵖ C]
variable [SMulCommClass Sᵐᵒᵖ R B]

/-- Precomposition by the left action on the bimodule. -/
def homScale (r : Rᵐᵒᵖ) (g : B →ₗ[Sᵐᵒᵖ] C) : B →ₗ[Sᵐᵒᵖ] C where
  toFun b := g (r.unop • b)
  map_add' b b' := by simp [smul_add]
  map_smul' s b := by
    change g (r.unop • (s • b)) = s • g (r.unop • b)
    rw [← smul_comm s r.unop b, g.map_smul]

/-- The right action `(g · r)(b) = g (r b)`. -/
@[instance_reducible] def homModule : Module Rᵐᵒᵖ (B →ₗ[Sᵐᵒᵖ] C) where
  smul := homScale
  one_smul g := by
    change homScale 1 g = g
    ext b
    change g ((1 : R) • b) = g b
    rw [one_smul]
  mul_smul r r' g := by
    change homScale (r * r') g = homScale r (homScale r' g)
    ext b
    change g ((r'.unop * r.unop) • b) = g (r'.unop • (r.unop • b))
    rw [mul_smul]
  smul_zero r := by change homScale r 0 = 0; rfl
  smul_add r g g' := by change homScale r (g + g') = homScale r g + homScale r g'; rfl
  add_smul r r' g := by
    change homScale (r + r') g = homScale r g + homScale r' g
    ext b
    change g ((r.unop + r'.unop) • b) = g (r.unop • b) + g (r'.unop • b)
    rw [add_smul, map_add]
  zero_smul g := by
    change homScale 0 g = 0
    ext b
    change g ((0 : R) • b) = 0
    rw [zero_smul, map_zero]

end HomAction

section Types
variable (R : Type u) (S : Type v) [Ring R] [Ring S]
variable (A : Type w) (B : Type x) (C : Type y)
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [Module Rᵐᵒᵖ A] [Module R B] [Module Sᵐᵒᵖ B] [Module Sᵐᵒᵖ C]
variable [SMulCommClass Sᵐᵒᵖ R B]

abbrev Curried := letI := homModule (R := R) (S := S) (B := B) (C := C)
  A →ₗ[Rᵐᵒᵖ] (B →ₗ[Sᵐᵒᵖ] C)

/-- The full additive isomorphism, with the two evaluation formulas. -/
def AdjunctionStatement : Prop :=
  ∃ m : Module Sᵐᵒᵖ (Tensor R A B),
    letI := m
    (∀ (s : Sᵐᵒᵖ) (a : A) (b : B), s • tmul R a b = tmul R a (s • b)) ∧
    ∃ e : (Tensor R A B →ₗ[Sᵐᵒᵖ] C) ≃+ Curried R S A B C,
      (∀ f a b, e f a b = f (tmul R a b)) ∧
      (∀ g a b, e.symm g (tmul R a b) = g a b)
end Types

namespace Spec

def ExpectedAdjunction : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S]
    (A : Type w) (B : Type x) (C : Type y)
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module Rᵐᵒᵖ A] [Module R B] [Module Sᵐᵒᵖ B] [Module Sᵐᵒᵖ C]
    [SMulCommClass Sᵐᵒᵖ R B], AdjunctionStatement R S A B C

/-- Naturality in all three variables. The scalar maps of any commuting outer
module actions are particular cases of these additive maps. -/
def ExpectedNaturality : Prop :=
  ∀ (R S : Type*) [Ring R] [Ring S] (A B C A' B' C' : Type*)
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    [Module Rᵐᵒᵖ A] [Module R B] [Module Sᵐᵒᵖ B] [Module Sᵐᵒᵖ C]
    [Module Rᵐᵒᵖ A'] [Module R B'] [Module Sᵐᵒᵖ B'] [Module Sᵐᵒᵖ C']
    [SMulCommClass Sᵐᵒᵖ R B] [SMulCommClass Sᵐᵒᵖ R B']
    [Module Sᵐᵒᵖ (Tensor R A B)] [Module Sᵐᵒᵖ (Tensor R A' B')]
    (e : (Tensor R A B →ₗ[Sᵐᵒᵖ] C) ≃+ Curried R S A B C)
    (e' : (Tensor R A' B' →ₗ[Sᵐᵒᵖ] C') ≃+ Curried R S A' B' C')
    (he : ∀ f a b, e f a b = f (tmul R a b))
    (he' : ∀ f a b, e' f a b = f (tmul R a b))
    (aMap : A' →ₗ[Rᵐᵒᵖ] A) (bMap : B' →ₗ[Sᵐᵒᵖ] B)
    (cMap : C →ₗ[Sᵐᵒᵖ] C')
    (tensorMap : Tensor R A' B' →ₗ[Sᵐᵒᵖ] Tensor R A B)
    (hMap : ∀ a b, tensorMap (tmul R a b) = tmul R (aMap a) (bMap b))
    (f : Tensor R A B →ₗ[Sᵐᵒᵖ] C),
    ∀ a b, e' (cMap.comp (f.comp tensorMap)) a b = cMap (e f (aMap a) (bMap b))

end Spec

section ExtensionTypes
variable {R : Type u} {S : Type v} [Ring R] [Ring S] (u : R →+* S)

/-- The right R-action on S is multiplication by the image of u. -/
abbrev ringRightModule : Module Rᵐᵒᵖ S := Module.compHom S u.op

abbrev Extension (M : Type w) [AddCommGroup M] [Module R M] :=
  letI := ringRightModule u
  Tensor R S M

def extensionTmul {M : Type w} [AddCommGroup M] [Module R M] (s : S) (m : M) :
    Extension u M := letI := ringRightModule u; tmul R s m

abbrev RestrictedHom (M : Type w) (N : Type x) [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S N] :=
  letI := P103.Scalars.restrictModule u N
  M →ₗ[R] N

/-- Scalar extension's Hom equivalence, including its inverse formula. -/
def ExtensionStatement (M : Type w) (N : Type x) [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S N] : Prop :=
  ∃ m : Module S (Extension u M),
    letI := m
    (∀ (s t : S) (x : M), s • extensionTmul u t x = extensionTmul u (s * t) x) ∧
    ∃ e : (Extension u M →ₗ[S] N) ≃+ RestrictedHom u M N,
      (∀ f x, e f x = f (extensionTmul u 1 x)) ∧
      (∀ g s x, e.symm g (extensionTmul u s x) = s • g x)

end ExtensionTypes
namespace Spec

def ExpectedExtension : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S] (u : R →+* S)
    (M : Type w) (N : Type x) [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S N], ExtensionStatement u M N

/-- Extension on arrows has its elementary formula, and satisfies the functor
laws. Restriction on arrows is the shared scalar-restriction construction. -/
def ExpectedExtensionMaps : Prop :=
  ∀ (R S : Type*) [Ring R] [Ring S] (u : R →+* S)
    (M M' M'' : Type*) [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M'']
    [Module R M] [Module R M'] [Module R M'']
    [Module S (Extension u M)] [Module S (Extension u M')] [Module S (Extension u M'')]
    (hM : ∀ (s t : S) (x : M), s • extensionTmul u t x = extensionTmul u (s*t) x)
    (hM' : ∀ (s t : S) (x : M'), s • extensionTmul u t x = extensionTmul u (s*t) x)
    (hM'' : ∀ (s t : S) (x : M''), s • extensionTmul u t x = extensionTmul u (s*t) x),
    ∃ (F : (M →ₗ[R] M') → (Extension u M →ₗ[S] Extension u M'))
      (G : (M' →ₗ[R] M'') → (Extension u M' →ₗ[S] Extension u M''))
      (H : (M →ₗ[R] M'') → (Extension u M →ₗ[S] Extension u M'')),
      (∀ f s x, F f (extensionTmul u s x) = extensionTmul u s (f x)) ∧
      (∀ g s x, G g (extensionTmul u s x) = extensionTmul u s (g x)) ∧
      (∀ h s x, H h (extensionTmul u s x) = extensionTmul u s (h x)) ∧
      (∀ f g, H (g.comp f) = (G g).comp (F f)) ∧
      (∀ J : Extension u M →ₗ[S] Extension u M,
        (∀ s x, J (extensionTmul u s x) = extensionTmul u s x) → J = LinearMap.id)

/-- Naturality of the scalar-extension Hom equivalence in both modules. -/
def ExpectedExtensionNaturality : Prop :=
  ∀ (R S : Type*) [Ring R] [Ring S] (u : R →+* S) (M M' N N' : Type*)
    [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N] [AddCommGroup N']
    [Module R M] [Module R M'] [Module S N] [Module S N']
    [Module S (Extension u M)] [Module S (Extension u M')]
    (e : (Extension u M →ₗ[S] N) ≃+ RestrictedHom u M N)
    (e' : (Extension u M' →ₗ[S] N') ≃+ RestrictedHom u M' N')
    (he : ∀ f x, e f x = f (extensionTmul u 1 x))
    (he' : ∀ f x, e' f x = f (extensionTmul u 1 x))
    (a : M' →ₗ[R] M) (b : N →ₗ[S] N')
    (F : Extension u M' →ₗ[S] Extension u M)
    (hF : ∀ s x, F (extensionTmul u s x) = extensionTmul u s (a x))
    (f : Extension u M →ₗ[S] N),
    ∀ x, e' (b.comp (f.comp F)) x = b (e f (a x))

end Spec

namespace Spec

/-- The unit is linear into scalar restriction of scalar extension. -/
def ExpectedUnit : Prop :=
  ∀ (R S : Type*) [Ring R] [Ring S] (u : R →+* S)
    (M : Type*) [AddCommGroup M] [Module R M]
    [Module S (Extension u M)]
    (hT : ∀ (s t : S) (x : M), s • extensionTmul u t x = extensionTmul u (s*t) x),
    letI := P103.Scalars.restrictModule u (Extension u M)
    ∃ eta : M →ₗ[R] Extension u M, ∀ x, eta x = extensionTmul u 1 x

/-- The counit evaluates multiplication on a restricted module. -/
def ExpectedCounit : Prop :=
  ∀ (R S : Type*) [Ring R] [Ring S] (u : R →+* S)
    (N : Type*) [AddCommGroup N] [Module S N],
    letI := P103.Scalars.restrictModule u N
    ∀ [Module S (Extension u N)]
      (hT : ∀ (s t : S) (x : N), s • extensionTmul u t x = extensionTmul u (s*t) x),
      ∃ eps : Extension u N →ₗ[S] N, ∀ s x, eps (extensionTmul u s x) = s • x

/-- The extension triangle `epsilon_(F M) ∘ F(eta_M) = id`.
The maps are characterized by their canonical formulas; their existence is
certified by ExpectedUnit, ExpectedCounit, and ExpectedExtensionMaps. -/
def ExpectedExtensionTriangle : Prop :=
  ∀ (R S : Type*) [Ring R] [Ring S] (u : R →+* S)
    (M : Type*) [AddCommGroup M] [Module R M]
    [Module S (Extension u M)]
    (hT : ∀ (s t : S) (x : M), s • extensionTmul u t x = extensionTmul u (s*t) x),
    letI := P103.Scalars.restrictModule u (Extension u M)
    ∀ [Module S (Extension u (Extension u M))]
      (eta : M →ₗ[R] Extension u M)
      (heta : ∀ x, eta x = extensionTmul u 1 x)
      (Feta : Extension u M →ₗ[S] Extension u (Extension u M))
      (hFeta : ∀ s x, Feta (extensionTmul u s x) = extensionTmul u s (eta x))
      (eps : Extension u (Extension u M) →ₗ[S] Extension u M)
      (heps : ∀ s x, eps (extensionTmul u s x) = s • x),
      eps.comp Feta = LinearMap.id

/-- The restriction triangle `Res(epsilon_N) ∘ eta_(Res N) = id`. -/
def ExpectedRestrictionTriangle : Prop :=
  ∀ (R S : Type*) [Ring R] [Ring S] (u : R →+* S)
    (N : Type*) [AddCommGroup N] [Module S N],
    letI := P103.Scalars.restrictModule u N
    ∀ [Module S (Extension u N)],
    letI := P103.Scalars.restrictModule u (Extension u N)
    ∀ (eta : N →ₗ[R] Extension u N)
      (heta : ∀ x, eta x = extensionTmul u 1 x)
      (eps : Extension u N →ₗ[S] N)
      (heps : ∀ s x, eps (extensionTmul u s x) = s • x),
      (letI := P103.Scalars.restrictModule u (Extension u N)
       (P103.Scalars.restrictLinearMap u eps).comp eta) = LinearMap.id

end Spec


namespace Spec

/-- Currying preserves equivariance for a commuting action on the first factor.
Taking `T` to be an opposite ring includes unused right scalar actions. -/
def ExpectedFirstOuterScalars : Prop :=
  ∀ (R S T : Type*) [Ring R] [Ring S] [Ring T] (A B C : Type*)
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module Rᵐᵒᵖ A] [Module R B] [Module Sᵐᵒᵖ B] [Module Sᵐᵒᵖ C]
    [SMulCommClass Sᵐᵒᵖ R B]
    [Module T A] [Module T C] [Module T (Tensor R A B)]
    [Module Sᵐᵒᵖ (Tensor R A B)]
    (hT : ∀ (t : T) (a : A) (b : B), t • tmul R a b = tmul R (t • a) b)
    (e : (Tensor R A B →ₗ[Sᵐᵒᵖ] C) ≃+ Curried R S A B C)
    (he : ∀ f a b, e f a b = f (tmul R a b))
    (f : Tensor R A B →ₗ[Sᵐᵒᵖ] C),
    (∀ (t : T) z, f (t • z) = t • f z) ↔
      (∀ (t : T) a b, e f (t • a) b = t • e f a b)

/-- Currying preserves equivariance for any additional action on the second factor. -/
def ExpectedSecondOuterScalars : Prop :=
  ∀ (R S T : Type*) [Ring R] [Ring S] [Ring T] (A B C : Type*)
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module Rᵐᵒᵖ A] [Module R B] [Module Sᵐᵒᵖ B] [Module Sᵐᵒᵖ C]
    [SMulCommClass Sᵐᵒᵖ R B]
    [Module T B] [Module T C] [Module T (Tensor R A B)]
    [Module Sᵐᵒᵖ (Tensor R A B)]
    (hT : ∀ (t : T) (a : A) (b : B), t • tmul R a b = tmul R a (t • b))
    (e : (Tensor R A B →ₗ[Sᵐᵒᵖ] C) ≃+ Curried R S A B C)
    (he : ∀ f a b, e f a b = f (tmul R a b))
    (f : Tensor R A B →ₗ[Sᵐᵒᵖ] C),
    (∀ (t : T) z, f (t • z) = t • f z) ↔
      (∀ (t : T) a b, e f a (t • b) = t • e f a b)

/-- Scalar extension's adjunction preserves every extra commuting scalar action. -/
def ExpectedExtensionOuterScalars : Prop :=
  ∀ (R S T : Type*) [Ring R] [Ring S] [Ring T] (u : R →+* S) (M N : Type*)
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    [Module T M] [Module T N] [SMulCommClass T S N]
    [Module S (Extension u M)] [Module T (Extension u M)]
    (hT : ∀ (t : T) (s : S) (x : M),
      t • extensionTmul u s x = extensionTmul u s (t • x))
    (e : (Extension u M →ₗ[S] N) ≃+ RestrictedHom u M N)
    (he : ∀ f x, e f x = f (extensionTmul u 1 x))
    (heInv : ∀ g s x, e.symm g (extensionTmul u s x) = s • g x)
    (f : Extension u M →ₗ[S] N),
    (∀ (t : T) z, f (t • z) = t • f z) ↔
      (∀ (t : T) x, e f (t • x) = t • e f x)

end Spec


namespace Spec

/-- Scalar extension sends identity arrows to identity arrows. -/
def ExpectedExtensionIdentity : Prop :=
  ∀ (R S : Type*) [Ring R] [Ring S] (u : R →+* S)
    (M : Type*) [AddCommGroup M] [Module R M] [Module S (Extension u M)]
    (hM : ∀ (s t : S) (x : M), s • extensionTmul u t x = extensionTmul u (s*t) x),
    ∃ F : (M →ₗ[R] M) → (Extension u M →ₗ[S] Extension u M),
      (∀ f s x, F f (extensionTmul u s x) = extensionTmul u s (f x)) ∧
      F LinearMap.id = LinearMap.id

/-- The unit commutes with every module map and its scalar extension. -/
def ExpectedUnitNaturality : Prop :=
  ∀ (R S : Type*) [Ring R] [Ring S] (u : R →+* S) (M M' : Type*)
    [AddCommGroup M] [AddCommGroup M'] [Module R M] [Module R M']
    [Module S (Extension u M)] [Module S (Extension u M')],
    letI := P103.Scalars.restrictModule u (Extension u M)
    letI := P103.Scalars.restrictModule u (Extension u M')
    ∀ (eta : M →ₗ[R] Extension u M) (heta : ∀ x, eta x = extensionTmul u 1 x)
      (eta' : M' →ₗ[R] Extension u M') (heta' : ∀ x, eta' x = extensionTmul u 1 x)
      (f : M →ₗ[R] M') (F : Extension u M →ₗ[S] Extension u M')
      (hF : ∀ s x, F (extensionTmul u s x) = extensionTmul u s (f x)),
      (P103.Scalars.restrictLinearMap u F).comp eta = eta'.comp f

/-- The counit commutes with every module map and extension of its restriction. -/
def ExpectedCounitNaturality : Prop :=
  ∀ (R S : Type*) [Ring R] [Ring S] (u : R →+* S) (N N' : Type*)
    [AddCommGroup N] [AddCommGroup N'] [Module S N] [Module S N'],
    letI := P103.Scalars.restrictModule u N
    letI := P103.Scalars.restrictModule u N'
    ∀ [Module S (Extension u N)] [Module S (Extension u N')]
      (eps : Extension u N →ₗ[S] N)
      (heps : ∀ s x, eps (extensionTmul u s x) = s • x)
      (eps' : Extension u N' →ₗ[S] N')
      (heps' : ∀ s x, eps' (extensionTmul u s x) = s • x)
      (g : N →ₗ[S] N') (F : Extension u N →ₗ[S] Extension u N')
      (hF : ∀ s x, F (extensionTmul u s x) = extensionTmul u s (g x)),
      g.comp eps = eps'.comp F

end Spec


namespace Spec

/-- A pair of module maps, the second respecting both bimodule actions, induces
an actual linear map of tensors for the unused right action. -/
def ExpectedTensorMaps : Prop :=
  ∀ (R S : Type*) [Ring R] [Ring S] (A B A' B' : Type*)
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup A'] [AddCommGroup B']
    [Module Rᵐᵒᵖ A] [Module R B] [Module Sᵐᵒᵖ B]
    [Module Rᵐᵒᵖ A'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass Sᵐᵒᵖ R B] [SMulCommClass Sᵐᵒᵖ R B']
    [Module Sᵐᵒᵖ (Tensor R A B)] [Module Sᵐᵒᵖ (Tensor R A' B')]
    (hT : ∀ (s : Sᵐᵒᵖ) (a : A) (b : B), s • tmul R a b = tmul R a (s • b))
    (hT' : ∀ (s : Sᵐᵒᵖ) (a : A') (b : B'), s • tmul R a b = tmul R a (s • b))
    (aMap : A →ₗ[Rᵐᵒᵖ] A') (bMap : B →ₗ[R] B')
    (hbMap : ∀ (s : Sᵐᵒᵖ) (b : B), bMap (s • b) = s • bMap b),
    ∃ F : Tensor R A B →ₗ[Sᵐᵒᵖ] Tensor R A' B',
      ∀ a b, F (tmul R a b) = tmul R (aMap a) (bMap b)

end Spec

end P103.TensorHom
