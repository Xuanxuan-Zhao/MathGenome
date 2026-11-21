import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch07.ExteriorDerivative
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Topology.LocallyConstant.Algebra

/-! M11.01, paper.tex 2185–2211. The forms below are exactly the shared smooth
intrinsic exterior sections. A Calculus is constructed, not added to the
hypotheses on a manifold. The quotient is of closed smooth forms by exact smooth
forms; no support or boundary restriction is imposed. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section

namespace SmoothManifolds.DeRhamData
open ModelData AtlasData TangentData BundleOperationsData CovectorData ExteriorData ExteriorDerivativeData
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} (C : CotangentBundle S) (B : ∀ k, FormBundle C k)

/-- A realization of the intrinsic smooth de Rham complex. The submodule
membership equivalence prevents replacing smooth forms by a smaller space. -/
structure Calculus where
  forms : ∀ k, Submodule ℝ (Field S k)
  mem_forms : ∀ k ω, ω ∈ forms k ↔ IsForm (B k) ω
  D : ∀ k, Field S k → Field S (k+1)
  axioms : DerivativeAxioms C B D
  coordinates : ∀ k ω, IsForm (B k) ω → HasExteriorDerivative C ω (D k ω)

namespace Calculus
variable {C B} (K : Calculus C B)

def d (k : ℕ) : K.forms k →ₗ[ℝ] K.forms (k+1) where
  toFun ω := ⟨K.D k ω.val, (K.mem_forms _ _).mpr
    (K.axioms.smooth k ω.val ((K.mem_forms _ _).mp ω.property))⟩
  map_add' α β := Subtype.ext (K.axioms.add k α.val β.val
    ((K.mem_forms _ _).mp α.property) ((K.mem_forms _ _).mp β.property))
  map_smul' r α := Subtype.ext (K.axioms.smul k r α.val
    ((K.mem_forms _ _).mp α.property))

def closed (k : ℕ) : Submodule ℝ (K.forms k) := LinearMap.ker (K.d k)

/-- Explicit instances avoid repeated inference through the nested exterior fibers. -/
instance closedAddCommGroup (k : ℕ) : AddCommGroup (K.closed k) :=
  @Submodule.addCommGroup ℝ (K.forms k) inferInstance
    (Submodule.addCommGroup (K.forms k)) (Submodule.module (K.forms k)) (K.closed k)

instance closedModule (k : ℕ) : Module ℝ (K.closed k) :=
  @Submodule.module ℝ (K.forms k) inferInstance
    (Submodule.addCommMonoid (K.forms k)) (Submodule.module (K.forms k)) (K.closed k)

def exact : (k : ℕ) → Submodule ℝ (K.forms k)
  | 0 => ⊥
  | k+1 => LinearMap.range (K.d k)

/-- Exact forms viewed inside closed forms. The theorem exact_closed below
proves that this is the full image, not merely its intersection with the kernel. -/
def boundaries (k : ℕ) : Submodule ℝ (K.closed k) :=
  (K.exact k).comap (K.closed k).subtype

def Cohomology (k : ℕ) := ↥(K.closed k) ⧸ K.boundaries k

instance cohomologyAddCommGroup (k : ℕ) : AddCommGroup (K.Cohomology k) :=
  @Submodule.Quotient.addCommGroup ℝ (K.closed k) inferInstance
    (K.closedAddCommGroup k) (K.closedModule k) (K.boundaries k)

instance cohomologyModule (k : ℕ) : Module ℝ (K.Cohomology k) :=
  @Submodule.Quotient.module ℝ (K.closed k) inferInstance
    (K.closedAddCommGroup k) (K.closedModule k) (K.boundaries k)

def classOf (k : ℕ) : K.closed k →ₗ[ℝ] K.Cohomology k :=
  (K.boundaries k).mkQ

/-- The convention Ω^k=0 for negative k, using an actual zero real vector space. -/
def FormsZ : ℤ → Type u
  | .ofNat k => K.forms k
  | .negSucc _ => ULift.{u} (Fin 0) → ℝ

/-- All negative degree groups vanish, as in the zero extension of the complex. -/
def CohomologyZ : ℤ → Type u
  | .ofNat k => K.Cohomology k
  | .negSucc _ => ULift.{u} (Fin 0) → ℝ

/-- A degreewise bilinear product induced by the actual wedge of closed forms. -/
structure GradedProduct where
  mul : ∀ k l, K.Cohomology k → K.Cohomology l → K.Cohomology (k+l)
  one : K.Cohomology 0

def ProductAddLeft (P : K.GradedProduct) : Prop :=
  ∀ k l x y z, P.mul k l (x+y) z = P.mul k l x z + P.mul k l y z

def ProductAddRight (P : K.GradedProduct) : Prop :=
  ∀ k l x y z, P.mul k l x (y+z) = P.mul k l x y + P.mul k l x z

def ProductSmulLeft (P : K.GradedProduct) : Prop :=
  ∀ k l (r : ℝ) x y, P.mul k l (r • x) y = r • P.mul k l x y

def ProductSmulRight (P : K.GradedProduct) : Prop :=
  ∀ k l (r : ℝ) x y, P.mul k l x (r • y) = r • P.mul k l x y

def ProductRepresentatives (P : K.GradedProduct) : Prop :=
  ∀ k l (α : K.closed k) (β : K.closed l),
    ∃ γ : K.closed (k+l), γ.val.val = fieldWedge α.val.val β.val.val ∧
      P.mul k l (K.classOf k α) (K.classOf l β) = K.classOf (k+l) γ

def ProductOneRepresentative (P : K.GradedProduct) : Prop :=
  ∃ ε : K.closed 0,
    ε.val.val = FormPullbackData.scalarField S (fun _ => 1) ∧ P.one = K.classOf 0 ε

def ProductAssoc (P : K.GradedProduct) : Prop :=
  ∀ k l m (x : K.Cohomology k) (y : K.Cohomology l) (z : K.Cohomology m),
    cast (congrArg (fun j => K.Cohomology j) (Nat.add_assoc k l m))
      (P.mul (k+l) m (P.mul k l x y) z) = P.mul k (l+m) x (P.mul l m y z)

def ProductComm (P : K.GradedProduct) : Prop :=
  ∀ k l (x : K.Cohomology k) (y : K.Cohomology l),
    P.mul k l x y = (-1 : ℝ)^(k*l) •
      cast (congrArg (fun j => K.Cohomology j) (Nat.add_comm l k)) (P.mul l k y x)

def ProductOneMul (P : K.GradedProduct) : Prop :=
  ∀ k (x : K.Cohomology k),
    cast (congrArg (fun j => K.Cohomology j) (Nat.zero_add k)) (P.mul 0 k P.one x) = x

def ProductMulOne (P : K.GradedProduct) : Prop :=
  ∀ k (x : K.Cohomology k), P.mul k 0 x P.one = x

def IsGradedProduct (P : K.GradedProduct) : Prop :=
  K.ProductAddLeft P ∧
  K.ProductAddRight P ∧
  K.ProductSmulLeft P ∧
  K.ProductSmulRight P ∧
  K.ProductRepresentatives P ∧
  K.ProductOneRepresentative P ∧
  K.ProductAssoc P ∧
  K.ProductComm P ∧
  K.ProductOneMul P ∧
  K.ProductMulOne P

end Calculus

/-- Characterization on every closed representative of the induced pullback.
The existential includes closedness and smoothness of the actual pulled-back field. -/
def IsCohomologyPullback
    {m : ℕ} {b : ModelKind} {N : Type u} [TopologicalSpace N]
    {T : SmoothManifold m b N} {A : CotangentBundle T} {E : ∀ k, FormBundle A k}
    (K : Calculus C B) (J : Calculus A E) (f : M → N)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (F : ∀ k, J.Cohomology k →ₗ[ℝ] K.Cohomology k) : Prop :=
  ∀ k (α : J.closed k), ∃ β : K.closed k,
    β.val.val = FormPullbackData.pullbackField S T f L α.val.val ∧
      F k (J.classOf k α) = K.classOf k β

end SmoothManifolds.DeRhamData

namespace Specs.SmoothManifolds.DeRham.Algebra
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.TangentData
  _root_.SmoothManifolds.BundleOperationsData _root_.SmoothManifolds.CovectorData _root_.SmoothManifolds.ExteriorData
  _root_.SmoothManifolds.DeRhamData
universe u

/-- Global construction, under the original manifold hypotheses. -/
def complex_existsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (B : ∀ k, FormBundle C k),
    Nonempty (Calculus C B)

def square_zeroType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) (k : ℕ) (ω : K.forms k), K.d (k+1) (K.d k ω) = 0

def exact_closedType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) (k : ℕ), K.exact k ≤ K.closed k

def class_zero_iff_exactType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) (k : ℕ) (ω : K.closed k),
    K.classOf k ω = 0 ↔ ω.val ∈ K.exact k

def above_dimensionType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) (k : ℕ), n < k → Subsingleton (K.Cohomology k)

def negative_degreesType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) (j : ℕ),
    Subsingleton (K.FormsZ (.negSucc j)) ∧ Subsingleton (K.CohomologyZ (.negSucc j))

/-- The canonical H⁰ identification sends the class of a zero-form to its
scalar coefficient. Exact zero-forms are zero, so every class has that value. -/
def h0_locally_constantType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B),
    ∃ e : K.Cohomology 0 ≃ₗ[ℝ] LocallyConstant M ℝ,
      ∀ (ω : K.closed 0) (p : M),
        e (K.classOf 0 ω) p =
          exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace S p)) (ω.val.val p)

/-- Constants can be chosen independently on every connected component. -/
def h0_componentsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B), Nonempty (K.Cohomology 0 ≃ₗ[ℝ] (ConnectedComponents M → ℝ))

def h0_connectedType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B), Nonempty (K.Cohomology 0 ≃ₗ[ℝ] ℝ)

def empty_cohomologyType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M] [IsEmpty M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) (k : ℕ), Subsingleton (K.Cohomology k)

/-- Wedge descends to an associative, unital, graded-commutative real algebra. -/
def product_existsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B), ∃ P : K.GradedProduct, K.IsGradedProduct P

def pullback_existsType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (A : CotangentBundle T)
    (B : ∀ k, FormBundle C k) (E : ∀ k, FormBundle A k)
    (K : Calculus C B) (J : Calculus A E)
    (f : M → N), MapData.IsSmoothMap S T f →
    ∀ (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)),
    (∀ p, DifferentialData.IsDifferential S T f p (L p)) →
    ∃ F : ∀ k, J.Cohomology k →ₗ[ℝ] K.Cohomology k,
      IsCohomologyPullback C B K J f L F

def pullback_idType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (K : Calculus C B)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace S p),
    (∀ p, DifferentialData.IsDifferential S S id p (L p)) →
    ∀ F : ∀ k, K.Cohomology k →ₗ[ℝ] K.Cohomology k,
    IsCohomologyPullback C B K K id L F → ∀ k x, F k x = x

def pullback_compType : Prop :=
  ∀ {n m r : ℕ} {a b c : ModelKind} {M N P : Type u}
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (U : SmoothManifold r c P)
    (C : CotangentBundle S) (A : CotangentBundle T) (V : CotangentBundle U)
    (B : ∀ k, FormBundle C k) (E : ∀ k, FormBundle A k) (W : ∀ k, FormBundle V k)
    (K : Calculus C B) (J : Calculus A E) (I : Calculus V W)
    (f : M → N) (g : N → P), MapData.IsSmoothMap S T f → MapData.IsSmoothMap T U g →
    ∀ (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
      (R : (q : N) → TangentSpace T q →ₗ[ℝ] TangentSpace U (g q))
      (H : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace U (g (f p))),
    (∀ p, DifferentialData.IsDifferential S T f p (L p)) →
    (∀ q, DifferentialData.IsDifferential T U g q (R q)) →
    (∀ p, DifferentialData.IsDifferential S U (g ∘ f) p (H p)) →
    ∀ (F : ∀ k, J.Cohomology k →ₗ[ℝ] K.Cohomology k)
      (G : ∀ k, I.Cohomology k →ₗ[ℝ] J.Cohomology k)
      (Q : ∀ k, I.Cohomology k →ₗ[ℝ] K.Cohomology k),
    IsCohomologyPullback C B K J f L F → IsCohomologyPullback A E J I g R G →
    IsCohomologyPullback C B K I (g ∘ f) H Q → ∀ k x, Q k x = F k (G k x)

def pullback_productType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (A : CotangentBundle T)
    (B : ∀ k, FormBundle C k) (E : ∀ k, FormBundle A k)
    (K : Calculus C B) (J : Calculus A E) (P : K.GradedProduct) (Q : J.GradedProduct)
    (f : M → N)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (F : ∀ k, J.Cohomology k →ₗ[ℝ] K.Cohomology k),
    K.IsGradedProduct P → J.IsGradedProduct Q →
    IsCohomologyPullback C B K J f L F →
    (F 0 Q.one = P.one) ∧
      ∀ k l x y, F (k+l) (Q.mul k l x y) = P.mul k l (F k x) (F l y)

end Specs.SmoothManifolds.DeRham.Algebra
