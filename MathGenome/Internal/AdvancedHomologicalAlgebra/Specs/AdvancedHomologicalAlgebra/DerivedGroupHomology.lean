import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.RightBarHomologyComplex
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.TorBalance
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.HomologySequence

/-! HA-A10, notes/002/advanced-homological-algebra.tex:3403–3520.
The ring is commutative, the group arbitrary, and coefficients are arbitrary
left group-algebra modules. No flatness hypothesis on coefficients is used.
The complexes below retain the original noncommutative balanced tensor. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
open scoped MonoidAlgebra
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch10.HomologySequence
namespace AdvancedHomologicalAlgebra.DerivedGroupHomology
universe u v w x y
variable (k : Type u) (G : Type v) [CommRing k] [Group G]

/-- Inverse twist of the homogeneous bar complex, including all its maps. -/
def rightTwistFunctor : Rep k G ⥤ ModuleCat k[G]ᵐᵒᵖ where
  obj V := ModuleCat.of k[G]ᵐᵒᵖ (RightBar.Twist k G V)
  map f := ModuleCat.ofHom (RightBar.twistMap k G f)
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

instance : (rightTwistFunctor k G).Additive where
  map_add := by intros; ext; rfl

def barChain : ChainComplex (ModuleCat.{max u v} k[G]ᵐᵒᵖ) ℕ :=
  ((rightTwistFunctor k G).mapHomologicalComplex (.down ℕ)).obj (GroupBar.Large.complex.{u,v,0} k G)

abbrev trivial : ModuleCat.{u} k[G]ᵐᵒᵖ :=
  ModuleCat.of k[G]ᵐᵒᵖ (GroupCoinvariants.TrivialRight k G)

/-- This complex uses precisely the deletion differential tensored with M. -/
abbrev chains (M : ModuleCat.{w} k[G]) := tensorComplex (barChain k G) M
abbrev chainMap {M N : ModuleCat.{w} k[G]} (f : M ⟶ N) :=
  tensorSecondMap (barChain k G) f.hom
abbrev barHomology (M : ModuleCat.{w} k[G]) (n : ℕ) := Homology (chains k G M) n
abbrev barHomologyMap {M N : ModuleCat.{w} k[G]} (f : M ⟶ N) (n : ℕ) :=
  homologyMap (chainMap k G f) n

abbrev canonicalResolution : ProjectiveChoice k[G]ᵐᵒᵖ (trivial k G) :=
  P103.Ch11.ExtTorDefinitions.resolutionFamily k[G]ᵐᵒᵖ (trivial k G)

abbrev torChainMap {M N : ModuleCat.{w} k[G]} (f : M ⟶ N) :=
  tensorSecondMap (canonicalResolution k G).val.complex f.hom

abbrev torZero (M : ModuleCat.{w} k[G]) :=
  P103.Ch11.ExtTorDefinitions.torZero (canonicalResolution k G).val M

/-- The comparison is induced by an augmented comparison from the actual
P103 resolution to the specified inverse-twisted bar. -/
def BarCoordinates (b : ∀ (M : ModuleCat.{w} k[G]) (n : ℕ),
    GroupCoinvariants.GroupHomology k G M n ≃ₗ[ℤ] barHomology k G M n) : Prop :=
  ∃ (P : ProjectiveChoice k[G]ᵐᵒᵖ (trivial k G))
    (h : P.val.complex = barChain k G)
    (_ : HEq P.val.ε.toAddMonoidHom (RightBar.augmentationLinear k G).toAddMonoidHom)
    (l : (canonicalResolution k G).val.complex ⟶ P.val.complex),
    ChainLift (canonicalResolution k G).val P.val LinearMap.id l ∧
    ∀ M n, (b M n).toLinearMap =
      homologyMap (tensorFirstMap (l ≫ eqToHom h) M) n

/-- Identifies degree zero using `k ⊗_{k[G]} M → M_G` on pure tensors. -/
def CoinvariantCoordinates (e : ∀ M : ModuleCat.{w} k[G],
    GroupCoinvariants.GroupHomology k G M 0 → GroupCoinvariants.Coinvariants k G M) : Prop :=
  ∀ (M : ModuleCat.{w} k[G]) (a : GroupCoinvariants.TrivialRight k G) (m : M),
    e M ((torZero k G M).symm (P103.BalancedTensor.tmul k[G] a m)) =
      GroupCoinvariants.trivialScalar k G a • GroupCoinvariants.quotientMap k G M
        ((RestrictScalars.addEquiv k k[G] M).symm m)

/-- The actual Tor coefficient functor, using the established canonical theory. -/
abbrev homologyFunctor (n : ℕ) : ModuleCat.{w} k[G] ⥤ ModuleCat.{max u v w} ℤ :=
  ((P103.Ch11.ExtTorDefinitions.theory.{max u v,u,w} k[G]).torMaps n).coefficients
    ((P103.Ch11.ExtTorDefinitions.theory.{max u v,u,w} k[G]).rightResolutions (trivial k G))

/-- Coinvariants as abelian groups, obtained by exact restriction of scalars. -/
def coinvariantGroups : ModuleCat.{w} k[G] ⥤ ModuleCat.{max u w} ℤ :=
  GroupCoinvariants.coinvariantsFunctor k G ⋙ ModuleCat.uliftFunctor.{u,w} k ⋙
    ModuleCat.restrictScalars (Int.castRingHom k)

abbrev tensorCoefficients : ModuleCat.{w} k[G] ⥤ ModuleCat.{max u w} ℤ :=
  P103.Specs.Ch11.TorBalance.leftTensorFunctor (GroupCoinvariants.TrivialRight k G)

/-- A coefficient homomorphism acts on every summand by its restricted k-linear map. -/
abbrev coefficientLinearMap {M N : ModuleCat.{w} k[G]} (f : M ⟶ N) :
    RestrictScalars k k[G] M →ₗ[k] RestrictScalars k k[G] N :=
  (Rep.ofModuleMonoidAlgebra.map f).hom.toLinearMap

abbrev directSumMap {M N : ModuleCat.{w} k[G]} (f : M ⟶ N) (n : ℕ) :
    RightBar.C k G M n →ₗ[k] RightBar.C k G N n :=
  Finsupp.mapRange.linearMap (coefficientLinearMap k G f)

section Scalars
open scoped ModuleCat.Algebra

abbrev scalarCoefficientMap (M : ModuleCat.{w} k[G]) (r : k) : M ⟶ M :=
  r • 𝟙 M

/-- The outer k-action on Tor, from the action of central coefficient endomorphisms. -/
@[instance_reducible]
def torModule (M : ModuleCat.{w} k[G]) (n : ℕ) :
    Module k (GroupCoinvariants.GroupHomology k G M n) where
  smul r z := (homologyFunctor k G n).map (scalarCoefficientMap k G M r) z
  one_smul z := by
    change (homologyFunctor k G n).map (1 • 𝟙 M) z = z
    simp
  mul_smul r s z := by
    change (homologyFunctor k G n).map ((r*s) • 𝟙 M) z =
      (homologyFunctor k G n).map (r • 𝟙 M) ((homologyFunctor k G n).map (s • 𝟙 M) z)
    have h : (r*s) • 𝟙 M = (s • 𝟙 M) ≫ (r • 𝟙 M) := by
      simp [Linear.comp_smul, smul_smul, mul_comm r s]
    rw [h, Functor.map_comp]
    rfl
  smul_zero r := map_zero ((homologyFunctor k G n).map (scalarCoefficientMap k G M r)).hom
  smul_add r z w := map_add ((homologyFunctor k G n).map (scalarCoefficientMap k G M r)).hom z w
  zero_smul z := by
    change (homologyFunctor k G n).map (0 • 𝟙 M) z = 0
    simp
  add_smul r s z := by
    change (homologyFunctor k G n).map ((r+s) • 𝟙 M) z =
      (homologyFunctor k G n).map (r • 𝟙 M) z + (homologyFunctor k G n).map (s • 𝟙 M) z
    rw [add_smul, Functor.map_add]
    rfl

attribute [local instance] torModule

/-- The canonical Tor, with its central k-scalars and ordinary coefficient maps. -/
def kHomologyFunctor (n : ℕ) : ModuleCat.{w} k[G] ⥤ ModuleCat.{max u v w} k where
  obj M := ModuleCat.of k (GroupCoinvariants.GroupHomology k G M n)
  map {M N} f := ModuleCat.ofHom (X := ModuleCat.of k (GroupCoinvariants.GroupHomology k G M n))
    (Y := ModuleCat.of k (GroupCoinvariants.GroupHomology k G N n)) {
    toFun := (homologyFunctor k G n).map f
    map_add' := map_add ((homologyFunctor k G n).map f).hom
    map_smul' := fun r z => by
      change (homologyFunctor k G n).map f ((homologyFunctor k G n).map (r • 𝟙 M) z) =
        (homologyFunctor k G n).map (r • 𝟙 N) ((homologyFunctor k G n).map f z)
      have h : (r • 𝟙 M) ≫ f = f ≫ (r • 𝟙 N) := by simp
      have h₂ := congrArg (homologyFunctor k G n).map h
      simp only [Functor.map_comp] at h₂
      exact ConcreteCategory.congr_hom h₂ (show (homologyFunctor k G n).obj M from z) }
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change (homologyFunctor k G n).map (𝟙 M) z = z
    simp
  map_comp {M N P} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change (homologyFunctor k G n).map (f ≫ g) z =
      (homologyFunctor k G n).map g ((homologyFunctor k G n).map f z)
    rw [Functor.map_comp]
    rfl

end Scalars

namespace Specification

/-- The right bar augmentation is a projective resolution, with no change to
its terms or differential. -/
def ResolutionType : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
    ∃ P : LeftResolution k[G]ᵐᵒᵖ (GroupCoinvariants.TrivialRight k G),
      P.complex = barChain k G ∧ P.IsProjective ∧
      HEq P.ε.toAddMonoidHom (RightBar.augmentationLinear k G).toAddMonoidHom

/-- A single family of comparisons, natural for every coefficient map. -/
def BarComparisonType : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
    ∃ e : ∀ (M : ModuleCat.{w} k[G]) (n : ℕ),
      GroupCoinvariants.GroupHomology k G M n ≃ₗ[ℤ] barHomology k G M n,
      BarCoordinates k G e ∧
      ∀ {M N : ModuleCat.{w} k[G]} (f : M ⟶ N) (n : ℕ) z,
        e N n ((homologyFunctor k G n).map f z) = barHomologyMap k G f n (e M n z)

/-- Zeroth group homology is naturally the original quotient by span_k(gm-m). -/
def ZeroType : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
    ∃ e : ∀ M : ModuleCat.{w} k[G],
      GroupCoinvariants.GroupHomology k G M 0 ≃+ GroupCoinvariants.Coinvariants k G M,
      CoinvariantCoordinates k G (fun M z => e M z) ∧
      ∀ {M N : ModuleCat.{w} k[G]} (f : M ⟶ N) z,
        e N ((homologyFunctor k G 0).map f z) = GroupCoinvariants.coinvariantsMap k G f (e M z)

/-- Degree zero with the original k-module structure on the coinvariant quotient. -/
def ZeroLinearType : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
    ∃ e : kHomologyFunctor.{u,v,w} k G 0 ≅
      GroupCoinvariants.coinvariantsFunctor k G ⋙ ModuleCat.uliftFunctor.{max u v,w} k,
      CoinvariantCoordinates k G (fun M z => (e.hom.app M z).down)

/-- The chain coefficient sequence, with every positive connecting arrow,
the lift-and-boundary formula, and naturality under maps of coefficient SESs. -/
def BarSequenceType : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
    (∀ (S : ShortComplex (ModuleCat.{w} k[G])), S.ShortExact →
      P103.Specs.Ch10.HomologySequence.DegreewiseExact
        (chainMap k G S.f) (chainMap k G S.g)) ∧
    ∃ δ : ∀ (S : ShortComplex (ModuleCat.{w} k[G])), S.ShortExact →
      ∀ n : ℕ, barHomology k G S.X₃ (n+1) →ₗ[ℤ] barHomology k G S.X₁ n,
      (∀ (S) (hS : S.ShortExact) (n : ℕ),
        P103.Specs.Ch10.HomologySequence.Connecting
          (chainMap k G S.f) (chainMap k G S.g) (n+1) n (δ S hS n) ∧
        P103.Specs.Ch10.HomologySequence.SequenceExact
          (chainMap k G S.f) (chainMap k G S.g) (n+1) n (δ S hS n)) ∧
      (∀ (S T : ShortComplex (ModuleCat.{w} k[G])) (hS : S.ShortExact) (hT : T.ShortExact) (f : S ⟶ T) (n : ℕ),
        (barHomologyMap k G f.τ₁ n).comp (δ S hS n) =
          (δ T hT n).comp (barHomologyMap k G f.τ₃ (n+1)))

/-- The displayed inverse-action bar differential is the differential of the
very complex used for the Tor comparison. -/
def ExplicitModelType : Prop :=
  RightBar.Specification.barModelType.{u,v,w} ∧
    ∀ (k : Type u) (G : Type v) [CommRing k] [Group G] (M : ModuleCat.{w} k[G])
      (n : ℕ) (z : RightBar.TensorChains k G M (n+1)),
      ((chains k G M).d (n+1) n).hom z = RightBar.tensorBoundary k G M n z

/-- The homology sequence uses the actual Tor maps. The connecting maps are
identified with positive bar lift-and-boundary under one natural comparison;
the degree-zero endpoint is the original coinvariant quotient. -/
def CoefficientSequenceType : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
    ∃ e : ∀ (M : ModuleCat.{w} k[G]) (n : ℕ),
      GroupCoinvariants.GroupHomology k G M n ≃ₗ[ℤ] barHomology k G M n,
    ∃ δ : ∀ (S : ShortComplex (ModuleCat.{w} k[G])), S.ShortExact →
      ∀ n : ℕ, GroupCoinvariants.GroupHomology k G S.X₃ (n+1) →ₗ[ℤ]
        GroupCoinvariants.GroupHomology k G S.X₁ n,
      BarCoordinates k G e ∧
      (∀ {M N : ModuleCat.{w} k[G]} (f : M ⟶ N) (n : ℕ) z,
        e N n ((homologyFunctor k G n).map f z) = barHomologyMap k G f n (e M n z)) ∧
      (∀ (S : ShortComplex (ModuleCat.{w} k[G])) (hS : S.ShortExact) (n : ℕ),
        DegreewiseExact (torChainMap k G S.f) (torChainMap k G S.g) ∧
        Connecting (torChainMap k G S.f) (torChainMap k G S.g) (n+1) n (δ S hS n) ∧
        P103.Specs.Ch10.HomologySequence.Connecting
          (chainMap k G S.f) (chainMap k G S.g) (n+1) n
          ((e S.X₁ n).toLinearMap.comp ((δ S hS n).comp (e S.X₃ (n+1)).symm.toLinearMap)) ∧
        Function.Exact ((homologyFunctor k G (n+1)).map S.f)
          ((homologyFunctor k G (n+1)).map S.g) ∧
        Function.Exact ((homologyFunctor k G (n+1)).map S.g) (δ S hS n) ∧
        Function.Exact (δ S hS n) ((homologyFunctor k G n).map S.f)) ∧
      (∀ (S T : ShortComplex (ModuleCat.{w} k[G]))
        (hS : S.ShortExact) (hT : T.ShortExact) (f : S ⟶ T) (n : ℕ),
        ((homologyFunctor k G n).map f.τ₁).hom.comp (δ S hS n) =
          (δ T hT n).comp ((homologyFunctor k G (n+1)).map f.τ₃).hom) ∧
      (∀ (S : ShortComplex (ModuleCat.{w} k[G])) (_ : S.ShortExact),
        Function.Exact (GroupCoinvariants.coinvariantsMap k G S.f)
          (GroupCoinvariants.coinvariantsMap k G S.g) ∧
        Function.Surjective (GroupCoinvariants.coinvariantsMap k G S.g))

/-- The tensor functor in the coefficient variable is the original quotient
coinvariant functor (with its underlying abelian groups). -/
def TensorFunctorType : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
    ∃ t : coinvariantGroups.{u,v,w} k G ≅ tensorCoefficients.{u,v,w} k G,
      ∀ (M : ModuleCat.{w} k[G]) (a : GroupCoinvariants.TrivialRight k G) (m : M),
        (t.inv.app M (P103.BalancedTensor.tmul k[G] a m)).down =
          GroupCoinvariants.trivialScalar k G a • GroupCoinvariants.quotientMap k G M
            ((RestrictScalars.addEquiv k k[G] M).symm m)

/-- The canonical tensor/direct-sum coordinates are natural, identify bar
symbols with their summands, and transport the actual Tor differential to
the printed formula. Thus the explicit complex is a natural homology model. -/
def NaturalExplicitType : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
    ∃ e : ∀ (M : ModuleCat.{w} k[G]) (n : ℕ),
      RightBar.TensorChains k G M n ≃ₗ[k] RightBar.C k G M n,
      (∀ (M : ModuleCat.{w} k[G]) (n : ℕ) (g : Fin n → G) (m : RestrictScalars k k[G] M),
        e M n (P103.BalancedTensor.tmul k[G]
          ((RightBar.untwist k G _).symm (GroupBar.Large.single.{u,v,0} k G (RightBar.barTuple G g) 1))
          (RestrictScalars.addEquiv k k[G] M m)) = Finsupp.single g m) ∧
      (∀ {M N : ModuleCat.{w} k[G]} (f : M ⟶ N) (n : ℕ) z,
        e N n (((chainMap k G f).f n).hom z) = directSumMap k G f n (e M n z)) ∧
      (∀ (M : ModuleCat.{w} k[G]) (n : ℕ) (g : Fin (n+1) → G) (m : RestrictScalars k k[G] M),
        e M n (((chains k G M).d (n+1) n).hom ((e M (n+1)).symm (Finsupp.single g m))) =
          Finsupp.single (Fin.tail g) (GroupCoinvariants.coefficientRepresentation k G M (g 0)⁻¹ m) +
          (∑ i : Fin n, (-1:k)^(i.val+1) •
            Finsupp.single (i.castSucc.contractNth (· * ·) g) m) +
          (-1:k)^(n+1) • Finsupp.single (Fin.init g) m)

open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison
open Specs.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty
open Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

local instance coinvariantsAdditive : (GroupCoinvariants.coinvariantsFunctor k G :
    ModuleCat.{w} k[G] ⥤ ModuleCat.{w} k).Additive := by
  letI : (Rep.ofModuleMonoidAlgebra : ModuleCat.{w} k[G] ⥤ Rep.{w} k G).Additive :=
    ⟨by intros; ext x; rfl⟩
  unfold GroupCoinvariants.coinvariantsFunctor
  infer_instance

section Derived
variable [HasDerivedCategory.{x} (ModuleCat.{max u v w} k[G])] [HasDerivedCategory.{y} (ModuleCat.{max u v w} k)]
  [(minus (ModuleCat.{max u v w} k[G])).IsTriangulated] [(minus (ModuleCat.{max u v w} k)).IsTriangulated]
abbrev ambientCoinvariants : ModuleCat.{max u v w} k[G] ⥤ ModuleCat.{max u v w} k :=
  GroupCoinvariants.coinvariantsFunctor k G

abbrev liftCoefficients : ModuleCat.{w} k[G] ⥤ ModuleCat.{max u v w} k[G] :=
  ModuleCat.uliftFunctor.{max u v,w} k[G]

/-- Carrier lift on the original P103 Tor complex, induced by x ⊗ m ↦ x ⊗ up m. -/
def liftTorChainMap (M : ModuleCat.{w} k[G]) :
    tensorComplex (canonicalResolution k G).val.complex M ⟶
      tensorComplex (canonicalResolution k G).val.complex ((liftCoefficients k G).obj M) where
  f n := ModuleCat.ofHom (tensorMap LinearMap.id
    (ULift.moduleEquiv.symm.toLinearMap : M →ₗ[k[G]] (liftCoefficients k G).obj M))
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    rfl

/-- Apply H⁰ to the actual derived counit on the coefficient stalk. -/
def counitZero
    (D : ExactLeftData.{(max u v w)+1,max u v w,(max u v w)+1,max u v w,x,y}
      (ambientCoinvariants.{u,v,w} k G))
    (M : ModuleCat.{max u v w} k[G]) :
    (leftValue (ambientCoinvariants.{u,v,w} k G) D 0).obj M ⟶
      (ambientCoinvariants.{u,v,w} k G).obj M := by
  let A := ModuleCat.{max u v w} k[G]
  let B := ModuleCat.{max u v w} k
  let F := ambientCoinvariants.{u,v,w} k G
  let K := (CochainComplex.singleFunctor A 0).obj M
  let P := minusStalkValue M
  let FK := (F.mapHomologicalComplex (.up ℤ)).obj K
  let Q := HomotopyCategory.quotient B (.up ℤ)
  let e₁ : (minusSingle A).obj M ≅ (QMinus A).obj P :=
    DerivedCategory.Minus.ι.preimageIso ((DerivedCategory.singleFunctorIsoCompQh A 0).app M)
  let e₂ : ((minusUValue F).obj P).obj ≅ (DerivedCategory.Qh (C := B)).obj (Q.obj FK) :=
    DerivedCategory.Qh.mapIso
      ((F.mapHomotopyCategory (.up ℤ)).mapIso
        ((HomotopyCategory.singleFunctorPostcompQuotientIso A 0).app M) ≪≫
        (F.mapHomotopyCategoryFactors (.up ℤ)).app K)
  let e₃ : ((minusUValue F).obj P).obj ≅
      (DerivedCategory.singleFunctor B 0).obj (F.obj M) :=
    e₂ ≪≫ (DerivedCategory.quotientCompQhIso B).symm.app FK ≪≫
      DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app M)
  exact (DerivedCategory.homologyFunctor B 0).map
    (DerivedCategory.Minus.ι.map (D.functor.map e₁.hom ≫ D.counit.app P) ≫ e₃.hom) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).hom.app (F.obj M)

abbrev OriginalDerivedCoordinates
    (D : ExactLeftData.{(max u v w)+1,max u v w,(max u v w)+1,max u v w,x,y}
      (ambientCoinvariants.{u,v,w} k G)) :=
  ∀ n : ℕ, liftCoefficients.{u,v,w} k G ⋙
    leftValue (ambientCoinvariants.{u,v,w} k G) D n ≅ kHomologyFunctor k G n

/-- Normalize first on the whole ambient coefficient category, where the
projective resolutions are available. The counit in degree zero and the
ordinary coefficient connectors characterize the all-degree comparison.
Its restriction to original coefficients uses the actual tensor lift. -/
def DerivedCoordinates
    (D : ExactLeftData.{(max u v w)+1,max u v w,(max u v w)+1,max u v w,x,y}
      (ambientCoinvariants.{u,v,w} k G))
    (e : OriginalDerivedCoordinates k G D) : Prop :=
  ∃ E : ∀ n : ℕ, leftValue (ambientCoinvariants.{u,v,w} k G) D n ≅
      kHomologyFunctor.{u,v,max u v w} k G n,
    (∀ (M : ModuleCat.{max u v w} k[G])
      (a : GroupCoinvariants.TrivialRight k G) (m : M),
      counitZero k G D M ((E 0).inv.app M
        ((torZero k G M).symm (P103.BalancedTensor.tmul k[G] a m))) =
          GroupCoinvariants.trivialScalar k G a • GroupCoinvariants.quotientMap k G M
            ((RestrictScalars.addEquiv k k[G] M).symm m)) ∧
    (∀ (S : ShortComplex (ModuleCat.{max u v w} k[G])) (hS : S.ShortExact) (n : ℕ),
      Connecting (torChainMap k G S.f) (torChainMap k G S.g) (n+1) n
        (((E (n+1)).inv.app S.X₃ ≫ leftBoundary (ambientCoinvariants k G) D hS n ≫
          (E n).hom.app S.X₁).hom.toAddMonoidHom.toIntLinearMap)) ∧
    ∀ (M : ModuleCat.{w} k[G]) (n : ℕ) z,
      (E n).hom.app ((liftCoefficients k G).obj M) z =
        homologyMap (liftTorChainMap k G M) n ((e n).hom.app M z)

/-- The Tor functor in the coefficient variable agrees k-linearly with
the genuine left derived functor of the original quotient coinvariants. -/
def DerivedValuesStatement (D : ExactLeftData.{(max u v w)+1,max u v w,(max u v w)+1,max u v w,x,y} (ambientCoinvariants.{u,v,w} k G)) : Prop :=
  ∃ e : OriginalDerivedCoordinates k G D, DerivedCoordinates k G D e

/-- The actual coefficient-derived boundary transported to the canonical Tor objects. -/
def transportedDerivedBoundary (D : ExactLeftData.{(max u v w)+1,max u v w,(max u v w)+1,max u v w,x,y} (ambientCoinvariants.{u,v,w} k G))
    (e : ∀ n : ℕ, liftCoefficients.{u,v,w} k G ⋙ leftValue (ambientCoinvariants.{u,v,w} k G) D n ≅ kHomologyFunctor k G n)
    (S : ShortComplex (ModuleCat.{w} k[G])) (hS : S.ShortExact) (n : ℕ) :
    (kHomologyFunctor k G (n+1)).obj S.X₃ ⟶ (kHomologyFunctor k G n).obj S.X₁ :=
  (e (n+1)).inv.app S.X₃ ≫ leftBoundary (ambientCoinvariants.{u,v,w} k G) D
      (hS.map_of_exact (liftCoefficients.{u,v,w} k G)) n ≫ (e n).hom.app S.X₁

/-- One comparison works for all coefficients, in every degree and for every
coefficient short exact sequence. It transports the derived boundary to the
positive lift-and-boundary map on the same bar model that computes Tor. -/
def DerivedComparisonStatement (D : ExactLeftData.{(max u v w)+1,max u v w,(max u v w)+1,max u v w,x,y} (ambientCoinvariants.{u,v,w} k G)) : Prop :=
  ∃ e : OriginalDerivedCoordinates k G D,
  ∃ b : ∀ (M : ModuleCat.{w} k[G]) (n : ℕ), GroupCoinvariants.GroupHomology k G M n ≃ₗ[ℤ] barHomology k G M n,
    DerivedCoordinates k G D e ∧ BarCoordinates k G b ∧
    (∀ {M N : ModuleCat.{w} k[G]} (f : M ⟶ N) (n : ℕ) z,
      b N n ((homologyFunctor k G n).map f z) = barHomologyMap k G f n (b M n z)) ∧
    ∀ (S : ShortComplex (ModuleCat.{w} k[G])) (hS : S.ShortExact) (n : ℕ),
      Connecting (torChainMap k G S.f) (torChainMap k G S.g) (n+1) n
        (transportedDerivedBoundary k G D e S hS n).hom.toAddMonoidHom.toIntLinearMap ∧
      P103.Specs.Ch10.HomologySequence.Connecting
        (chainMap k G S.f) (chainMap k G S.g) (n+1) n
        ((b S.X₁ n).toLinearMap.comp
          (((transportedDerivedBoundary k G D e S hS n).hom.toAddMonoidHom.toIntLinearMap).comp
            (b S.X₃ (n+1)).symm.toLinearMap))

end Derived

def DerivedValuesType : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G]
    [HasDerivedCategory.{x} (ModuleCat.{max u v w} k[G])] [HasDerivedCategory.{y} (ModuleCat.{max u v w} k)]
    (hA : (minus (ModuleCat.{max u v w} k[G])).IsTriangulated) (hE : (minus (ModuleCat.{max u v w} k)).IsTriangulated),
    letI := hA; letI := hE
    ∀ D : ExactLeftData.{(max u v w)+1,max u v w,(max u v w)+1,max u v w,x,y} (ambientCoinvariants.{u,v,w} k G),
      DerivedValuesStatement.{u,v,w,x,y} k G D

def DerivedComparisonType : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G]
    [HasDerivedCategory.{x} (ModuleCat.{max u v w} k[G])] [HasDerivedCategory.{y} (ModuleCat.{max u v w} k)]
    (hA : (minus (ModuleCat.{max u v w} k[G])).IsTriangulated) (hE : (minus (ModuleCat.{max u v w} k)).IsTriangulated),
    letI := hA; letI := hE
    ∀ D : ExactLeftData.{(max u v w)+1,max u v w,(max u v w)+1,max u v w,x,y} (ambientCoinvariants.{u,v,w} k G),
      DerivedComparisonStatement.{u,v,w,x,y} k G D

/-- With the standard localizations, the coefficient-derived functor exists
and the comparison applies for every commutative ring and discrete group. -/
def DerivedCoinvariantsType : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
    letI := HasDerivedCategory.standard (ModuleCat.{max u v w} k[G])
    letI := HasDerivedCategory.standard (ModuleCat.{max u v w} k)
    ∃ (hA : (minus (ModuleCat.{max u v w} k[G])).IsTriangulated) (hE : (minus (ModuleCat.{max u v w} k)).IsTriangulated),
      letI := hA
      letI := hE
      ∃ D : ExactLeftData.{(max u v w)+1,max u v w,(max u v w)+1,max u v w,(max u v w)+1,(max u v w)+1} (ambientCoinvariants.{u,v,w} k G),
        DerivedComparisonStatement.{u,v,w,(max u v w)+1,(max u v w)+1} k G D

end Specification
end AdvancedHomologicalAlgebra.DerivedGroupHomology
