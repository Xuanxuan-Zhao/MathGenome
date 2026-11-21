import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GroupBarResolution
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GroupCoinvariants
import Mathlib.Algebra.MonoidAlgebra.Opposite

/-! HA-A10, right bar resolution (source lines 3449–3482).
Right modules mean left modules over the opposite group ring. -/
noncomputable section
open CategoryTheory
open scoped MonoidAlgebra
namespace AdvancedHomologicalAlgebra.RightBar
universe u v w
variable (k : Type u) (G : Type v) [CommRing k] [Group G]

/-- The anti-involution of the group ring, written as a ring isomorphism. -/
def inversion : k[G] ≃+* k[G]ᵐᵒᵖ :=
  ((MonoidAlgebra.mapDomainRingEquiv k (MulEquiv.inv' G)).trans
    (MonoidAlgebra.mapRingEquiv Gᵐᵒᵖ (RingEquiv.toOpposite k))).trans
    MonoidAlgebra.opRingEquiv.symm

/-- The original underlying module, with right action obtained by inversion. -/
def Twist (V : Rep k G) := V.ρ.asModule
deriving AddCommGroup, Module k

instance (V : Rep k G) : Module k[G]ᵐᵒᵖ (Twist k G V) :=
  Module.compHom V.ρ.asModule (inversion k G).symm.toRingHom

instance (V : Rep k G) : SMulCommClass k k[G]ᵐᵒᵖ (Twist k G V) where
  smul_comm a r x :=
    ((V.ρ.asAlgebraHom ((inversion k G).symm r)).map_smul a x).symm

/-- Forgetting the twist changes no underlying k-linear data. -/
def untwist (V : Rep k G) : Twist k G V ≃ₗ[k] V := LinearEquiv.refl _ _

/-- Every equivariant map also preserves the twisted right actions. -/
def twistMap {V W : Rep k G} (f : V ⟶ W) :
    Twist k G V →ₗ[k[G]ᵐᵒᵖ] Twist k G W where
  toFun := f.hom
  map_add' := f.hom.map_add
  map_smul' r x :=
    (Rep.toModuleMonoidAlgebra.map f).hom.map_smul ((inversion k G).symm r) x

abbrev B (n : ℕ) := Twist k G (GroupBar.Large.B.{u,v,0} k G n)
abbrev boundary (n : ℕ) : B k G (n+1) →ₗ[k[G]ᵐᵒᵖ] B k G n :=
  twistMap k G (GroupBar.Large.boundary.{u,v,0} k G n)

/-- The augmentation has values in the actual trivial right module. -/
def augmentationLinear : B k G 0 →ₗ[k] GroupCoinvariants.TrivialRight k G :=
  GroupBar.Large.ε.{u,v,0} k G

/-- Nonhomogeneous chains, a direct sum of copies of the original module
with its canonical restricted k-scalars. -/
abbrev C (M : ModuleCat.{w} k[G]) (n : ℕ) :=
  (Fin n → G) →₀ RestrictScalars k k[G] M

/-- The normalized homogeneous tuple represented by a bar symbol. -/
abbrev barTuple {n : ℕ} (g : Fin n → G) : Fin (n+1) → G := Fin.partialProd g

abbrev TensorChains (M : ModuleCat.{w} k[G]) (n : ℕ) :=
  P103.BalancedTensor.Tensor k[G] (B k G n) M
instance (M : ModuleCat.{w} k[G]) (n : ℕ) : Module k (TensorChains k G M n) :=
  P103.BalancedTensor.leftModule

abbrev tensorBoundary (M : ModuleCat.{w} k[G]) (n : ℕ) :
    TensorChains k G M (n+1) →ₗ[k] TensorChains k G M n :=
  P103.BalancedTensor.mapLeftLinear (boundary k G n) LinearMap.id
    (fun a x => (GroupBar.Large.d.{u,v,0} k G n).map_smul a x)

namespace Specification
/-- Full right-resolution assertion. The exactness is elementwise and includes
the augmentation and every nonnegative degree. -/
def rightResolutionType : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
    (∀ (n : ℕ) (g : G) (x : B k G n),
      untwist k G _ (MulOpposite.op (MonoidAlgebra.single g (1:k)) • x) =
        (GroupBar.Large.B.{u,v,0} k G n).ρ g⁻¹ (untwist k G _ x)) ∧
    (∀ n, Module.Free k[G]ᵐᵒᵖ (B k G n)) ∧
    (∀ n, boundary k G n ∘ₗ boundary k G (n+1) = 0) ∧
    (∀ x : B k G 1, augmentationLinear k G (boundary k G 0 x) = 0) ∧
    (∀ (r : k[G]) (x : B k G 0),
      augmentationLinear k G (MulOpposite.op r • x) =
        MulOpposite.op r • augmentationLinear k G x) ∧
    Function.Surjective (augmentationLinear k G) ∧
    (∀ x : B k G 0, augmentationLinear k G x = 0 ↔
      ∃ y : B k G 1, boundary k G 0 y = x) ∧
    (∀ (n : ℕ) (x : B k G (n+1)), boundary k G n x = 0 ↔
      ∃ y : B k G (n+2), boundary k G (n+1) y = x)
/-- The tensor model is identified k-linearly with the displayed direct sum.
The boundary is the tensor of the deletion map, its first coefficient is acted
on by the inverse, and each internal contraction multiplies in the original
left-to-right order. The final face is written separately, including degree one. -/
def barModelType : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G] (M : ModuleCat.{w} k[G]),
    ∃ e : ∀ n, TensorChains k G M n ≃ₗ[k] C k G M n,
    ∃ δ : ∀ n, C k G M (n+1) →ₗ[k] C k G M n,
    ∃ e₀ : C k G M 0 ≃ₗ[k] RestrictScalars k k[G] M,
      (∀ n (g : Fin n → G) (m : RestrictScalars k k[G] M),
        e n (P103.BalancedTensor.tmul k[G]
          ((untwist k G _).symm (GroupBar.Large.single.{u,v,0} k G (barTuple G g) 1))
          (RestrictScalars.addEquiv k k[G] M m)) = Finsupp.single g m) ∧
      (∀ n z, δ n (e (n+1) z) = e n (tensorBoundary k G M n z)) ∧
      (∀ n (g : Fin (n+1) → G) (m : RestrictScalars k k[G] M),
        δ n (Finsupp.single g m) =
          Finsupp.single (Fin.tail g) (GroupCoinvariants.coefficientRepresentation k G M (g 0)⁻¹ m) +
          (∑ i : Fin n, (-1:k)^(i.val+1) •
            Finsupp.single (i.castSucc.contractNth (· * ·) g) m) +
          (-1:k)^(n+1) • Finsupp.single (Fin.init g) m) ∧
      (∀ n, δ n ∘ₗ δ (n+1) = 0) ∧
      (∀ (g : Fin 0 → G) m, e₀ (Finsupp.single g m) = m)
end Specification
end AdvancedHomologicalAlgebra.RightBar
