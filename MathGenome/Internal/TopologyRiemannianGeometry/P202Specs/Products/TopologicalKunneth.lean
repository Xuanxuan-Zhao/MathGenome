import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.EilenbergZilber
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.ExtTorDefinitions
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.TorBalance
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
Full independent statement of paper.tex, cor:p202-topological-kunneth.
The homology groups are the existing ordinary singular homology groups, not
new abstract modules. Tor is computed by the P103 projective-resolution model;
its coefficient action is P103's torModule. No finiteness or connectivity
assumptions are imposed. Existence of resolutions and of their functorial Tor
maps is part of the conclusion, so these parameters cannot make it vacuous.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory
open scoped TensorProduct DirectSum
namespace P202Specs.TopologicalKunneth
open P202Specs.SingularChains P202Specs.AlexanderWhitney
open P202Specs.EilenbergZilber
open P103.Specs.Ch10.Comparison P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch11.TorBalance
universe u w
variable (R : Type u) [CommRing R]

/-- Ordinary singular homology in nonnegative degree, using the existing
integer-indexed complex extended by zero. -/
abbrev H (X : TopCat.{w}) (n : ℕ) := homology R R X (n : ℤ)

def hMap {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ) : H R X n →ₗ[R] H R Y n :=
  (HomologicalComplex.homologyMap ((ordinaryFunctor R R).map f) (n : ℤ)).hom

abbrev TensorSummand (X Y : TopCat.{w}) (i : ℕ × ℕ) :=
  H R X i.1 ⊗[R] H R Y i.2
abbrev TensorSum (X Y : TopCat.{w}) (n : ℕ) :=
  ⨁ i : Diagonal n, TensorSummand R X Y i.val

def tensorSumMap {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ) :
    TensorSum R X Y n →ₗ[R] TensorSum R X' Y' n :=
  DirectSum.lmap (fun i : Diagonal n => TensorProduct.map
    (hMap R f i.val.1) (hMap R g i.val.2))

/-- A single choice for every space and homology degree. These are actual
projective resolutions of the displayed homology modules. -/
abbrev Models := ∀ (X : TopCat.{w}) (p : ℕ),
  ProjectiveChoice Rᵐᵒᵖ ((commRightFunctor R).obj (ModuleCat.of R (H R X p)))

abbrev TailDiagonal (n : ℕ) := {i : ℕ × ℕ // i.1 + i.2 + 1 = n}

abbrev TorSummand (P : Models R) (X Y : TopCat.{w}) (i : ℕ × ℕ) :=
  TorWith (P X i.1).val (H R Y i.2) 1

/-- The Tor action parameter is retained in the type so that typeclass
inference can recover the precise coefficient module structure. -/
def TorSum (P : Models R) (_T : TorMaps.{u,max u w,max u w} R 1)
    (X Y : TopCat.{w}) (n : ℕ) :=
  ⨁ i : TailDiagonal n, TorSummand R P X Y i.val

instance torSumAddCommGroup (P : Models R)
    (T : TorMaps.{u,max u w,max u w} R 1) (X Y : TopCat.{w}) (n : ℕ) :
    AddCommGroup (TorSum R P T X Y n) := by
  unfold TorSum
  infer_instance

instance torSumModule (P : Models R)
    (T : TorMaps.{u,max u w,max u w} R 1) (X Y : TopCat.{w}) (n : ℕ) :
    Module R (TorSum R P T X Y n) := by
  letI (i : TailDiagonal n) : Module R (TorSummand R P X Y i.val) :=
    torModule T (P X i.val.1) (ModuleCat.of R (H R Y i.val.2))
  unfold TorSum
  infer_instance

/-- Functorial Tor on homology, including the canonical commutative right
action in its first variable. Integer linearity suffices to state naturality;
the actual sequence and its splitting below are R-linear. -/
def torSumMap (P : Models R) (T : TorMaps.{u,max u w,max u w} R 1)
    {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ) :
    TorSum R P T X Y n →ₗ[ℤ] TorSum R P T X' Y' n :=
  DirectSum.lmap (fun i : TailDiagonal n =>
    T.map (P X i.val.1) (P X' i.val.1)
      ((commRightFunctor R).map (ModuleCat.ofHom (hMap R f i.val.1)))
      (ModuleCat.ofHom (hMap R g i.val.2)))

/-- The external product on ordinary homology, transported through the
specified ordinary/nonnegative homology isomorphism. Its value is fixed by
shuffle on every pair of cycle representatives in ExternalProduct.represents. -/
def ordinaryExternal (e : ExternalProduct.{u,w} R) (X Y : TopCat.{w}) (p q : ℕ) :
    H R X p ⊗[R] H R Y q →ₗ[R] H R (productSpace X Y) (p+q) :=
  (ordinaryHomologyIso R (productSpace X Y) (p+q)).inv.hom.comp
    ((e.map X Y p q).comp (TensorProduct.map
      (ordinaryHomologyIso R X p).hom.hom (ordinaryHomologyIso R Y q).hom.hom))

/-- One simultaneous natural short exact sequence. Only existence of a
section is required, separately for each degree and pair of spaces. -/
structure NaturalSequence (P : Models R) (T : TorMaps.{u,max u w,max u w} R 1) where
  external : ExternalProduct.{u,w} R
  α : ∀ (X Y : TopCat.{w}) (n : ℕ), TensorSum R X Y n →ₗ[R] H R (productSpace X Y) n
  β : ∀ (X Y : TopCat.{w}) (n : ℕ),
    H R (productSpace X Y) n →ₗ[R] TorSum R P T X Y n
  injective_α : ∀ X Y n, Function.Injective (α X Y n)
  exact : ∀ X Y n, Function.Exact (α X Y n) (β X Y n)
  surjective_β : ∀ X Y n, Function.Surjective (β X Y n)
  α_external : ∀ (X Y : TopCat.{w}) (p q : ℕ) (a : H R X p) (b : H R Y q),
    α X Y (p+q) (DirectSum.lof R _ _ (⟨(p,q), rfl⟩ : Diagonal (p+q)) (a ⊗ₜ[R] b)) =
      ordinaryExternal R external X Y p q (a ⊗ₜ[R] b)
  naturality_α : ∀ {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ),
    (hMap R (productMap f g) n).comp (α X Y n) =
      (α X' Y' n).comp (tensorSumMap R f g n)
  naturality_β : ∀ {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ)
      (x : H R (productSpace X Y) n),
    torSumMap R P T f g n (β X Y n x) =
      β X' Y' n (hMap R (productMap f g) n x)
  splits : ∀ (X Y : TopCat.{w}) (n : ℕ),
    ∃ s : TorSum R P T X Y n →ₗ[R] H R (productSpace X Y) n,
      (β X Y n).comp s = LinearMap.id

/-- The full topological Künneth conclusion with no additional premises. -/
def kunneth_type : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R],
    ∃ (P : Models.{u,w} R) (T : TorMaps.{u,max u w,max u w} R 1),
      Nonempty (NaturalSequence R P T) ∧
        ∀ (X Y : TopCat.{w}), Subsingleton (TorSum R P T X Y 0)

end P202Specs.TopologicalKunneth
