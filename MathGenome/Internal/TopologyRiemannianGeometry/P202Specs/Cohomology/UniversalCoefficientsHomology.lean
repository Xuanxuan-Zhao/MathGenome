import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.RelativeSingularChains
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.UniversalCoefficientsHomology
import MathGenome.Internal.AlgebraCore.P103.Ch01.BalancedTensor
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.UniversalCoefficientsSplitting
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Ulift

/-! Homological T27 for the fixed singular complexes.
All commutative tensor products carry the ordinary R-module action.
The final family specifies natural split exact sequences for every space and
subspace pair, including the ordinary degree-zero endpoint. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
open scoped TensorProduct
namespace P202Specs.UniversalCoefficientsHomology
universe u v w t s
open P202Specs.SingularChains P202Specs.RelativeSingularChains
namespace Algebraic
export P103.Specs.Ch10.Complexes
  (cycles boundaries cycleBoundaries Homology homologyClass cyclesMap homologyMap)
end Algebraic
variable (R : Type u) [CommRing R]
variable (A : Type v) [AddCommGroup A] [Module R A]

/-- Tensoring modules with the coefficient module, using the usual scalar action. -/
def tensorFunctor : ModuleCat.{t} R ⥤ ModuleCat.{max t v} R where
  obj V := ModuleCat.of R (V ⊗[R] A)
  map f := ModuleCat.ofHom (f.hom.rTensor A)
  map_id V := by ext x a; rfl
  map_comp f g := by ext x a; rfl
instance : (tensorFunctor.{u,v,t} R A).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x a
    change (f.hom x + g.hom x) ⊗ₜ[R] a = _
    exact TensorProduct.add_tmul _ _ _

abbrev tensorComplex {ι : Type*} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{t} R) c) :=
  ((tensorFunctor R A).mapHomologicalComplex c).obj C

private lemma boundary_on_single (X : TopCat.{w}) (n : ℕ)
    (s : Simplex X (n+1)) (a : A) :
    boundary R A X n (Finsupp.single s a) =
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val • Finsupp.single (face i s) a := by
  change ((AlgebraicTopology.AlternatingFaceMapComplex.obj
    (simplicialChains R A X)).d (n+1) n).hom _ = _
  rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  simp [simplicialChains, finsuppFunctor, LinearMap.sum_apply, LinearMap.smul_apply]

/-- Changing coefficients on singular chains is pointwise on finite sums. -/
def coefficientMap {B : Type v} [AddCommGroup B] [Module R B]
    (g : A →ₗ[R] B) (X : TopCat.{w}) : complex R A X ⟶ complex R B X :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (Finsupp.mapRange.linearMap g)) (by
    intro n
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro s a
    change boundary R B X n ((Finsupp.mapRange.linearMap g) (Finsupp.single s a)) =
      (Finsupp.mapRange.linearMap g) (boundary R A X n (Finsupp.single s a))
    have hs : (Finsupp.mapRange.linearMap g) (Finsupp.single s a) =
        Finsupp.single s (g a) := by simp [Finsupp.mapRange.linearMap]
    rw [hs, boundary_on_single, boundary_on_single]
    simp [Finsupp.mapRange.linearMap])

/-- The coefficient map respects every subspace inclusion. -/
lemma coefficientMap_inclusion {B : Type v} [AddCommGroup B] [Module R B]
    (g : A →ₗ[R] B) (P : Pair.{w}) :
    inclusion (chainFunctor R A) P ≫ coefficientMap R A g P.space =
      coefficientMap R A g P.sub ≫ inclusion (chainFunctor R B) P := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro s a
  change (Finsupp.mapRange.linearMap g)
      (Finsupp.mapDomain ((TopCat.toSSet.map P.inclusion).app _) (Finsupp.single s a)) =
    Finsupp.mapDomain ((TopCat.toSSet.map P.inclusion).app _)
      ((Finsupp.mapRange.linearMap g) (Finsupp.single s a))
  simp [Finsupp.mapRange.linearMap]

/-- The genuine induced map of the categorical relative quotient. -/
def relativeCoefficientMap {B : Type v} [AddCommGroup B] [Module R B]
    (g : A →ₗ[R] B) (P : Pair.{w}) : nonnegative R A P ⟶ nonnegative R B P :=
  cokernel.map _ _ (coefficientMap R A g P.sub) (coefficientMap R A g P.space)
    (coefficientMap_inclusion R A g P)

section OrdinaryCoefficientMaps
variable {B : Type v} [AddCommGroup B] [Module R B]

lemma coefficientMap_natural (g : A →ₗ[R] B) {X Y : TopCat.{w}} (f : X ⟶ Y) :
    chainMap R A f ≫ coefficientMap R A g Y =
      coefficientMap R A g X ≫ chainMap R B f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro s a
  change (Finsupp.mapRange.linearMap g)
      (Finsupp.mapDomain ((TopCat.toSSet.map f).app _) (Finsupp.single s a)) =
    Finsupp.mapDomain ((TopCat.toSSet.map f).app _)
      ((Finsupp.mapRange.linearMap g) (Finsupp.single s a))
  simp [Finsupp.mapRange.linearMap]

def ordinaryCoefficientMap (g : A →ₗ[R] B) (X : TopCat.{w}) :
    ordinaryComplex R A X ⟶ ordinaryComplex R B X :=
  HomologicalComplex.extendMap (coefficientMap R A g X) (degreeEmbedding 0)

lemma ordinaryCoefficientMap_natural (g : A →ₗ[R] B) {X Y : TopCat.{w}} (f : X ⟶ Y) :
    (ordinaryFunctor R A).map f ≫ ordinaryCoefficientMap R A g Y =
      ordinaryCoefficientMap R A g X ≫ (ordinaryFunctor R B).map f := by
  change HomologicalComplex.extendMap (chainMap R A f) (degreeEmbedding 0) ≫ _ =
    _ ≫ HomologicalComplex.extendMap (chainMap R B f) (degreeEmbedding 0)
  unfold ordinaryCoefficientMap
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
    coefficientMap_natural]

lemma ordinaryCoefficientMap_inclusion (g : A →ₗ[R] B) (P : Pair.{w}) :
    inclusion (ordinaryFunctor R A) P ≫ ordinaryCoefficientMap R A g P.space =
      ordinaryCoefficientMap R A g P.sub ≫ inclusion (ordinaryFunctor R B) P :=
  ordinaryCoefficientMap_natural R A g P.inclusion

def relativeOrdinaryCoefficientMap (g : A →ₗ[R] B) (P : Pair.{w}) :
    ordinary R A P ⟶ ordinary R B P :=
  cokernel.map _ _ (ordinaryCoefficientMap R A g P.sub)
    (ordinaryCoefficientMap R A g P.space) (ordinaryCoefficientMap_inclusion R A g P)

end OrdinaryCoefficientMaps

/-- The comparison on relative chains is required to descend the absolute
comparison, commute with differentials, and be natural in pairs. -/
structure RelativeTensorData where
  equiv : ∀ (P : Pair.{w}) (n : ℕ),
    ((nonnegative R R P).X n ⊗[R] A) ≃ₗ[R] (nonnegative R A P).X n
  projection : ∀ (P : Pair.{w}) (n : ℕ) (c : Chains R P.space n ⊗[R] A),
    equiv P n (((projection (chainFunctor R R) P).f n).hom.rTensor A c) =
      (projection (chainFunctor R A) P).f n (tensorEquiv R A P.space n c)
  boundary : ∀ (P : Pair.{w}) (n : ℕ) (c : (nonnegative R R P).X (n+1) ⊗[R] A),
    equiv P n (((nonnegative R R P).d (n+1) n).hom.rTensor A c) =
      (nonnegative R A P).d (n+1) n (equiv P (n+1) c)
  natural_pair : ∀ (P Q : Pair.{w}) (f : P ⟶ Q) (n : ℕ)
    (c : (nonnegative R R P).X n ⊗[R] A),
    equiv Q n (((relativeMap (chainFunctor R R) f).f n).hom.rTensor A c) =
      (relativeMap (chainFunctor R A) f).f n (equiv P n c)

/-- One simultaneous family, so that naturality in coefficients refers to
the same comparisons as naturality in pairs. -/
structure RelativeTensorFamily where
  data : ∀ (A : Type v) [AddCommGroup A] [Module R A], RelativeTensorData.{u,v,w} R A
  natural_coefficient : ∀ (A B : Type v) [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (g : A →ₗ[R] B) (P : Pair.{w}) (n : ℕ)
    (c : (nonnegative R R P).X n ⊗[R] A),
    (data B).equiv P n (TensorProduct.map LinearMap.id g c) =
      (relativeCoefficientMap R A g P).f n ((data A).equiv P n c)

/-- Categorical homology and the explicit quotient used by P103. -/
def quotientHomologyEquiv {ι : Type*} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{t} R) c) (n : ι) :
    C.homology n ≃ₗ[R] Algebraic.Homology C n := by
  let e := (C.sc n).moduleCatHomologyIso.toLinearEquiv
  have h : (C.sc n).moduleCatToCycles.range = Algebraic.cycleBoundaries C n := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x, rfl⟩
    · rintro ⟨x, hx⟩; exact ⟨x, Subtype.ext hx⟩
  exact e.trans (Submodule.quotEquivOfEq _ _ h)

/-- A comparison on the fixed integer and natural gradings, including its
value on every cycle representative. -/
structure NonnegativeHomologyData
    (N : ChainComplex (ModuleCat.{t} R) ℕ) (Z : ChainComplex (ModuleCat.{t} R) ℤ)
    (e : ∀ n : ℕ, Z.X (n : ℤ) ≃ₗ[R] N.X n) where
  equiv : ∀ n : ℕ, Z.homology (n : ℤ) ≃ₗ[R] N.homology n
  formula : ∀ (n : ℕ) (z : Algebraic.cycles Z (n : ℤ)),
    ∃ z' : Algebraic.cycles N n, z'.val = e n z.val ∧
      quotientHomologyEquiv R N n
        (equiv n ((quotientHomologyEquiv R Z n).symm (Algebraic.homologyClass Z n z))) =
          Algebraic.homologyClass N n z'

section NonnegativeComparison
variable (N : ChainComplex (ModuleCat.{t} R) ℕ)
  (Z : ChainComplex (ModuleCat.{t} R) ℤ)
  (e : ∀ n : ℕ, Z.X (n : ℤ) ≃ₗ[R] N.X n)
  (hd : ∀ (n : ℕ) (x : Z.X (n+1 : ℕ)),
    e n (Z.d (n+1 : ℕ) n x) = N.d (n+1) n (e (n+1) x))
  (hzero : Z.d 0 (-1) = 0)

/-- Cycles agree also at degree zero, where the ordinary outgoing map is zero. -/
def nonnegativeCyclesEquiv (n : ℕ) : Algebraic.cycles Z (n : ℤ) ≃ₗ[R] Algebraic.cycles N n where
  toFun z := ⟨e n z.val, by
    cases n with
    | zero =>
      change N.d 0 ((ComplexShape.down ℕ).next 0) (e 0 z.val) = 0
      rw [ChainComplex.next_nat_zero, N.shape 0 0 (by simp)]
      rfl
    | succ n =>
      change N.d (n+1) ((ComplexShape.down ℕ).next (n+1)) (e (n+1) z.val) = 0
      rw [ChainComplex.next_nat_succ, ← hd]
      have hz := z.property
      change Z.d (n+1 : ℕ) ((ComplexShape.down ℤ).next (n+1 : ℕ)) z.val = 0 at hz
      have hn : (ComplexShape.down ℤ).next (n+1 : ℕ) = (n : ℤ) := by
        rw [ChainComplex.next]; omega
      rw [hn] at hz
      rw [hz, map_zero]⟩
  invFun z := ⟨(e n).symm z.val, by
    cases n with
    | zero =>
      change Z.d 0 ((ComplexShape.down ℤ).next 0) ((e 0).symm z.val) = 0
      rw [ChainComplex.next]
      rw [show (0 : ℤ)-1 = -1 by omega, hzero]
      rfl
    | succ n =>
      change Z.d (n+1 : ℕ) ((ComplexShape.down ℤ).next (n+1 : ℕ))
        ((e (n+1)).symm z.val) = 0
      have hn : (ComplexShape.down ℤ).next (n+1 : ℕ) = (n : ℤ) := by
        rw [ChainComplex.next]; omega
      rw [hn]
      apply (e n).injective
      rw [hd, LinearEquiv.apply_symm_apply, map_zero]
      have hz := z.property
      change N.d (n+1) ((ComplexShape.down ℕ).next (n+1)) z.val = 0 at hz
      rwa [ChainComplex.next_nat_succ] at hz⟩
  left_inv z := Subtype.ext ((e n).symm_apply_apply z.val)
  right_inv z := Subtype.ext ((e n).apply_symm_apply z.val)
  map_add' x y := Subtype.ext ((e n).map_add _ _)
  map_smul' r x := Subtype.ext ((e n).map_smul r _)

lemma nonnegativeCyclesEquiv_boundary (n : ℕ) (z : Algebraic.cycles Z (n : ℤ)) :
    z ∈ Algebraic.cycleBoundaries Z (n : ℤ) ↔
      nonnegativeCyclesEquiv R N Z e hd hzero n z ∈ Algebraic.cycleBoundaries N n := by
  change (∃ x, Z.d ((ComplexShape.down ℤ).prev (n : ℤ)) (n : ℤ) x = z.val) ↔
    (∃ x, N.d ((ComplexShape.down ℕ).prev n) n x = e n z.val)
  rw [ChainComplex.prev, ChainComplex.prev,
    show (n : ℤ)+1 = (n+1 : ℕ) by omega]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨e (n+1) x, ?_⟩
    rw [← hd]
    exact congrArg (e n) hx
  · rintro ⟨x, hx⟩
    refine ⟨(e (n+1)).symm x, ?_⟩
    apply (e n).injective
    rw [hd, LinearEquiv.apply_symm_apply]
    exact hx

/-- The comparison of the explicit quotient homology models. -/
def nonnegativeQuotientHomologyEquiv (n : ℕ) :
    Algebraic.Homology Z (n : ℤ) ≃ₗ[R] Algebraic.Homology N n :=
  Submodule.Quotient.equiv _ _ (nonnegativeCyclesEquiv R N Z e hd hzero n) (by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (nonnegativeCyclesEquiv_boundary R N Z e hd hzero n x).mp hx
    · intro hz
      refine ⟨(nonnegativeCyclesEquiv R N Z e hd hzero n).symm z, ?_,
        (nonnegativeCyclesEquiv R N Z e hd hzero n).apply_symm_apply z⟩
      exact (nonnegativeCyclesEquiv_boundary R N Z e hd hzero n _).mpr (by simpa using hz))

/-- The comparison on the actual categorical homology objects. -/
def nonnegativeHomologyEquiv (n : ℕ) : Z.homology (n : ℤ) ≃ₗ[R] N.homology n :=
  (quotientHomologyEquiv R Z n).trans
    ((nonnegativeQuotientHomologyEquiv R N Z e hd hzero n).trans
      (quotientHomologyEquiv R N n).symm)
def nonnegativeHomologyData : NonnegativeHomologyData R N Z e where
  equiv := nonnegativeHomologyEquiv R N Z e hd hzero
  formula n z := ⟨nonnegativeCyclesEquiv R N Z e hd hzero n z, rfl, by
    simp only [nonnegativeHomologyEquiv, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply]
    rfl⟩
end NonnegativeComparison

/-- A commutative left module viewed as a right module. No action is inferred
from a coincidental instance on the carrier type. -/
abbrev oppositeFunctor : ModuleCat.{t} R ⥤ ModuleCat.{t} Rᵐᵒᵖ :=
  ModuleCat.restrictScalars (RingEquiv.toOpposite R).symm.toRingHom

abbrev oppositeComplex {ι : Type*} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{t} R) c) :=
  ((oppositeFunctor R).mapHomologicalComplex c).obj C

/-- The canonical balanced-to-commutative tensor comparison, for the actual
right action obtained by restriction of scalars. -/
def balancedTensorEquiv (V : ModuleCat.{t} R) :
    P103.BalancedTensor.Tensor R ((oppositeFunctor R).obj V) A ≃+ (V ⊗[R] A) := by
  letI : Module R ((oppositeFunctor R).obj V) := V.isModule
  letI : IsCentralScalar R ((oppositeFunctor R).obj V) := ⟨fun _ _ => rfl⟩
  exact P103.BalancedTensor.commAddEquiv

@[simp] lemma balancedTensorEquiv_tmul (V : ModuleCat.{t} R) (x : V) (a : A) :
    balancedTensorEquiv R A V (P103.BalancedTensor.tmul R x a) = x ⊗ₜ[R] a := rfl

/-- Its naturality includes both the chain and coefficient variables. -/
lemma balancedTensorEquiv_natural {V W : ModuleCat.{t} R} (f : V ⟶ W)
    {B : Type v} [AddCommGroup B] [Module R B] (g : A →ₗ[R] B)
    (x : P103.BalancedTensor.Tensor R ((oppositeFunctor R).obj V) A) :
    balancedTensorEquiv R B W
        (P103.Specs.Ch11.ExtTorDefinitions.tensorMap ((oppositeFunctor R).map f).hom g x) =
      TensorProduct.map f.hom g (balancedTensorEquiv R A V x) := by
  induction x using P103.BalancedTensor.induction_on with
  | h0 => simp
  | ht x a => rfl
  | ha x y hx hy => simp only [map_add, hx, hy]

/-- Compatibility with the coefficient action used by P103's scalar theorem. -/
lemma balancedTensorEquiv_scalar (V : ModuleCat.{t} R) (r : R)
    (x : P103.BalancedTensor.Tensor R ((oppositeFunctor R).obj V) A) :
    balancedTensorEquiv R A V
      (P103.Specs.Ch11.ExtTorDefinitions.tensorMap LinearMap.id (r • LinearMap.id) x) =
      r • balancedTensorEquiv R A V x := by
  induction x using P103.BalancedTensor.induction_on with
  | h0 => simp
  | ht x a =>
    change x ⊗ₜ[R] (r • a) = r • (x ⊗ₜ[R] a)
    exact TensorProduct.tmul_smul r x a
  | ha x y hx hy => simp only [map_add, smul_add, hx, hy]

/-- Chain isomorphism from P103's balanced tensor model to the ordinary
commutative tensor complex with its scalars restricted to integers. -/
def balancedTensorComplexIso (C : ChainComplex (ModuleCat.{t} R) ℕ) :
    P103.Specs.Ch11.ExtTorDefinitions.tensorComplex (oppositeComplex R C) A ≅
      ((ModuleCat.restrictScalars (Int.castRingHom R)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (tensorComplex R A C) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (balancedTensorEquiv R A (C.X n)).toIntLinearEquiv.toModuleIso) (by
      intro i j _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (balancedTensorEquiv_natural R A (C.d i j) LinearMap.id x).symm)

/-- The balanced homology model compared with actual categorical homology,
with representatives and the coefficient-induced scalar action specified. -/
structure BalancedHomologyData (C : ChainComplex (ModuleCat.{t} R) ℕ)
    (D : ChainComplex (ModuleCat.{s} R) ℕ)
    (e : ∀ n, (C.X n ⊗[R] A) ≃ₗ[R] D.X n) where
  equiv : ∀ n, P103.Specs.Ch10.Complexes.Homology
    (P103.Specs.Ch11.ExtTorDefinitions.tensorComplex (oppositeComplex R C) A) n ≃+
      D.homology n
  formula : ∀ n (z : Algebraic.cycles
      (P103.Specs.Ch11.ExtTorDefinitions.tensorComplex (oppositeComplex R C) A) n),
    ∃ z' : Algebraic.cycles D n,
      z'.val = e n (balancedTensorEquiv R A (C.X n) z.val) ∧
      quotientHomologyEquiv R D n (equiv n (Algebraic.homologyClass _ n z)) =
        Algebraic.homologyClass D n z'
  scalar : ∀ n (r : R) x,
    equiv n (Algebraic.homologyMap
      (P103.Specs.Ch11.ExtTorDefinitions.tensorSecondMap (oppositeComplex R C)
        (r • (LinearMap.id : A →ₗ[R] A))) n x) = r • equiv n x

local instance oppositeRingInv :
    RingHomInvPair (RingEquiv.toOpposite R).toRingHom
      (RingEquiv.toOpposite R).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (RingEquiv.toOpposite R)
local instance oppositeRingInv' :
    RingHomInvPair (RingEquiv.toOpposite R).symm.toRingHom
      (RingEquiv.toOpposite R).toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (RingEquiv.toOpposite R)

/-- The identity on elements, semilinear for the specified ring equivalence. -/
def oppositeTermEquiv (V : ModuleCat.{t} R) :
    V ≃ₛₗ[(RingEquiv.toOpposite R).toRingHom] (oppositeFunctor R).obj V where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restriction to the canonical right action commutes with cycles. -/
def oppositeCyclesEquiv {ι : Type*} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{t} R) c) (n : ι) :
    Algebraic.cycles C n ≃ₛₗ[(RingEquiv.toOpposite R).toRingHom]
      Algebraic.cycles (oppositeComplex R C) n where
  toFun z := ⟨z.val, z.property⟩
  invFun z := ⟨z.val, z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The canonical semilinear equivalence on quotient homology. -/
def oppositeQuotientHomologyEquiv {ι : Type*} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{t} R) c) (n : ι) :
    Algebraic.Homology C n ≃ₛₗ[(RingEquiv.toOpposite R).toRingHom]
      Algebraic.Homology (oppositeComplex R C) n :=
  Submodule.Quotient.equiv _ _ (oppositeCyclesEquiv R C n) (by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hz
      exact ⟨(oppositeCyclesEquiv R C n).symm z, hz, rfl⟩)

/-- The same map as a right-linear equivalence. Its target is the actual
categorical homology with the explicitly restricted opposite action. -/
def oppositeHomologyEquiv {ι : Type*} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{t} R) c) (n : ι) :
    Algebraic.Homology (oppositeComplex R C) n ≃ₗ[Rᵐᵒᵖ]
      (oppositeFunctor R).obj (C.homology n) := by
  let e := (oppositeQuotientHomologyEquiv R C n).symm
  let q := (quotientHomologyEquiv R C n).symm
  exact
    { toFun := fun x => q (e x)
      invFun := fun x => e.symm (q.symm x)
      left_inv := fun x => by simp
      right_inv := fun x => by simp
      map_add' := fun x y => by rw [e.map_add, q.map_add]
      map_smul' := fun r x => by
        change q (e (r • x)) = (MulOpposite.unop r) • q (e x)
        rw [e.map_smulₛₗ, q.map_smul]
        rfl }

/-- Canonical identification of the left balanced tensor with the usual
commutative tensor of the actual homology object. -/
def homologyTensorEquiv {ι : Type*} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{t} R) c) (n : ι) :
    P103.BalancedTensor.Tensor R (Algebraic.Homology (oppositeComplex R C) n) A ≃+
      (C.homology n ⊗[R] A) :=
  (((P103.Specs.Ch11.ExtTorDefinitions.tensorFunctor A).mapIso
    (oppositeHomologyEquiv R C n).toModuleIso).toLinearEquiv.toAddEquiv).trans
      (balancedTensorEquiv R A (C.homology n))

structure SplitExactSequence (L : Type*) (M : Type*) (N : Type*)
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    [Module R L] [Module R M] [Module R N] where
  α : L →ₗ[R] M
  β : M →ₗ[R] N
  injective_α : Function.Injective α
  exact : Function.Exact α β
  surjective_β : Function.Surjective β
  split : ∃ σ : N →ₗ[R] M, β.comp σ = LinearMap.id


namespace AlgebraicUCT
open P103.Specs.Ch11.UniversalCoefficientsHomology
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch10.Horseshoe
open P103.Specs.Ch10.Comparison

/-- Scalar-compatible sections for the standard coefficient endomorphisms.
The `UniversalCoefficients` argument already contains simultaneous naturality
in complexes, coefficients, projective choices, and genuine induced Tor maps. -/
def ScalarSplittings (U : UniversalCoefficients.{u,t,v} R)
    (C : Complex.{u,t} R) (hC : FlatTermsAndBoundaries.{u,t,v} C) : Prop :=
  ∀ M : ModuleCat.{v} R,
    (∃ ρ : Algebraic.Homology (P103.Specs.Ch11.ExtTorDefinitions.tensorComplex C M) 0 →ₗ[ℤ]
        P103.BalancedTensor.Tensor R (Algebraic.Homology C 0) M,
      ρ.comp (U.zero C hC M).α = LinearMap.id ∧
      ∀ r x, ρ (Algebraic.homologyMap (tensorSecondMap C (scalarMap M r).hom) 0 x) =
        tensorMap LinearMap.id (scalarMap M r).hom (ρ x)) ∧
    ∀ (n : ℕ) (P : ProjectiveChoice Rᵐᵒᵖ
      (ModuleCat.of Rᵐᵒᵖ (Algebraic.Homology C n))) (T : TorMaps.{u,t,v} R 1),
      letI := torModule T P M
      ∃ σ : TorWith P.val M 1 →ₗ[ℤ]
          Algebraic.Homology (P103.Specs.Ch11.ExtTorDefinitions.tensorComplex C M) (n+1),
        (U.positive C hC M n P).β.comp σ = LinearMap.id ∧
        ∀ r x, σ (r • x) =
          Algebraic.homologyMap (tensorSecondMap C (scalarMap M r).hom) (n+1) (σ x)

end AlgebraicUCT

namespace Expected

def pidHypotheses [IsDomain R] [IsPrincipalIdealRing R] : Prop :=
  (∀ X : TopCat.{w},
    P103.Specs.Ch11.UniversalCoefficientsHomology.FlatTermsAndBoundaries.{u,max u w,v}
      (oppositeComplex R (complex R R X)) ∧
    Nonempty (P103.Specs.Ch11.UniversalCoefficientsSplitting.BoundarySections
      (oppositeComplex R (complex R R X)))) ∧
  (∀ P : Pair.{w},
    P103.Specs.Ch11.UniversalCoefficientsHomology.FlatTermsAndBoundaries.{u,max u w,v}
      (oppositeComplex R (nonnegative R R P)) ∧
    Nonempty (P103.Specs.Ch11.UniversalCoefficientsSplitting.BoundarySections
      (oppositeComplex R (nonnegative R R P))))

def balancedHomologyComparison : Prop :=
  ∀ (C : ChainComplex (ModuleCat.{t} R) ℕ) (D : ChainComplex (ModuleCat.{s} R) ℕ)
    (e : ∀ n, (C.X n ⊗[R] A) ≃ₗ[R] D.X n),
    (∀ i j x, e j ((C.d i j).hom.rTensor A x) = D.d i j (e i x)) →
    Nonempty (BalancedHomologyData R A C D e)

/-- One algebraic natural family for all spaces and pairs, with the verified
hypotheses and scalar-compatible splittings, used in the topological transport
of the edge maps below. -/
def algebraicModel [IsDomain R] [IsPrincipalIdealRing R] : Prop :=
  ∃ U : P103.Specs.Ch11.UniversalCoefficientsHomology.UniversalCoefficients.{u,max u w,v} R,
    (∀ X : TopCat.{w}, ∃ h :
      P103.Specs.Ch11.UniversalCoefficientsHomology.FlatTermsAndBoundaries.{u,max u w,v}
        (oppositeComplex R (complex R R X)),
      AlgebraicUCT.ScalarSplittings R U (oppositeComplex R (complex R R X)) h) ∧
    (∀ P : Pair.{w}, ∃ h :
      P103.Specs.Ch11.UniversalCoefficientsHomology.FlatTermsAndBoundaries.{u,max u w,v}
        (oppositeComplex R (nonnegative R R P)),
      AlgebraicUCT.ScalarSplittings R U (oppositeComplex R (nonnegative R R P)) h)

def absoluteTensorHomology : Prop :=
  ∀ X : TopCat.{w}, Nonempty (BalancedHomologyData R A
    (complex R R X) (complex R A X) (tensorEquiv R A X))

def relativeTensorHomology : Prop :=
  ∃ F : RelativeTensorFamily.{u,v,w} R,
    ∀ (A : Type v) [AddCommGroup A] [Module R A] (P : Pair.{w}),
      Nonempty (BalancedHomologyData R A
        (nonnegative R R P) (nonnegative R A P) (F.data A |>.equiv P))

def ordinaryHomology : Prop :=
  ∀ X : TopCat.{w}, Nonempty (NonnegativeHomologyData R
    (complex R A X) (ordinaryComplex R A X)
    (fun n => (ordinaryNonnegativeIso R A X n).toLinearEquiv))

def relativeHomology : Prop :=
  ∀ P : Pair.{w}, Nonempty (NonnegativeHomologyData R
    (nonnegative R A P) (ordinary R A P)
    (fun n => (ordinaryDegreeIso R A P n).toLinearEquiv))

def relativeTensor : Prop := Nonempty (RelativeTensorData.{u,v,w} R A)

def absoluteTensor : Prop :=
  ∀ X : TopCat.{w}, ∃ e : tensorComplex R A (complex R R X) ≅
      ((ModuleCat.uliftFunctor.{u} R).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (complex R A X),
    ∀ (n : ℕ) (c : Chains R X n ⊗[R] A), (e.hom.f n c).down = tensorEquiv R A X n c

end Expected
/-! Fully quantified types for the chain and homology comparison results. -/
def relative_tensor_family_type : Prop :=
  ∀ (R : Type u) [CommRing R], Nonempty (RelativeTensorFamily.{u,v,w} R)

def absolute_tensor_type : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A],
    Expected.absoluteTensor.{u,v,w} R A

def ordinary_homology_type : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A],
    Expected.ordinaryHomology.{u,v,w} R A

def relative_homology_type : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A],
    Expected.relativeHomology.{u,v,w} R A

def balanced_homology_comparison_type : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A],
    Expected.balancedHomologyComparison.{u,v,t,s} R A

def absolute_tensor_homology_type : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A],
    Expected.absoluteTensorHomology.{u,v,w} R A

def relative_tensor_homology_type : Prop :=
  ∀ (R : Type u) [CommRing R], Expected.relativeTensorHomology.{u,v,w} R

def pid_hypotheses_type : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R],
    Expected.pidHypotheses.{u,v,w} R

def algebraic_model_type : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R],
    Expected.algebraicModel.{u,v,w} R

namespace TopologicalUCT
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch10.Comparison

/-- One family of linear split sequences for spaces and all subspace pairs.
All maps on the right are the genuine induced Tor maps. -/
structure Family (T : TorMaps.{u,max u w,v} R 1)
    (F : RelativeTensorFamily.{u,v,w} R) where
  absolute : ∀ (A : ModuleCat.{v} R) (X : TopCat.{w}) (n : ℕ)
    (Q : ProjectiveChoice Rᵐᵒᵖ ((oppositeFunctor R).obj (homology R R X n))),
    letI := torModule T Q A
    SplitExactSequence R (homology R R X (n+1 : ℕ) ⊗[R] A)
      (homology R A X (n+1 : ℕ)) (TorWith Q.val A 1)
  relative : ∀ (A : ModuleCat.{v} R) (P : Pair.{w}) (n : ℕ)
    (Q : ProjectiveChoice Rᵐᵒᵖ ((oppositeFunctor R).obj (relativeHomology R R P n))),
    letI := torModule T Q A
    SplitExactSequence R (relativeHomology R R P (n+1 : ℕ) ⊗[R] A)
      (relativeHomology R A P (n+1 : ℕ)) (TorWith Q.val A 1)
  absoluteZero : ∀ (A : ModuleCat.{v} R) (X : TopCat.{w}),
    (homology R R X 0 ⊗[R] A) ≃ₗ[R] homology R A X 0
  relativeZero : ∀ (A : ModuleCat.{v} R) (P : Pair.{w}),
    (relativeHomology R R P 0 ⊗[R] A) ≃ₗ[R] relativeHomology R A P 0
  absoluteZeroTor : ∀ (A : ModuleCat.{v} R) (X : TopCat.{w})
    (Q : ProjectiveChoice Rᵐᵒᵖ ((oppositeFunctor R).obj (homology R R X (-1)))),
    Subsingleton (TorWith Q.val A 1)
  relativeZeroTor : ∀ (A : ModuleCat.{v} R) (P : Pair.{w})
    (Q : ProjectiveChoice Rᵐᵒᵖ ((oppositeFunctor R).obj (relativeHomology R R P (-1)))),
    Subsingleton (TorWith Q.val A 1)
  absolute_formula : ∀ (A : ModuleCat.{v} R) (X : TopCat.{w}) (n : ℕ)
    (Q : ProjectiveChoice Rᵐᵒᵖ ((oppositeFunctor R).obj (homology R R X n)))
    (z : Algebraic.cycles (ordinaryComplex R R X) (n+1 : ℕ)) (a : A),
    letI := torModule T Q A
    ∃ z' : Algebraic.cycles (ordinaryComplex R A X) (n+1 : ℕ),
      (ordinaryNonnegativeIso R A X (n+1)).hom z'.val =
        tensorEquiv R A X (n+1) ((ordinaryNonnegativeIso R R X (n+1)).hom z.val ⊗ₜ[R] a) ∧
      quotientHomologyEquiv R (ordinaryComplex R A X) (n+1 : ℕ)
        ((absolute A X n Q).α
          ((quotientHomologyEquiv R (ordinaryComplex R R X) (n+1 : ℕ)).symm
            (Algebraic.homologyClass _ _ z) ⊗ₜ[R] a)) = Algebraic.homologyClass _ _ z'
  relative_formula : ∀ (A : ModuleCat.{v} R) (P : Pair.{w}) (n : ℕ)
    (Q : ProjectiveChoice Rᵐᵒᵖ ((oppositeFunctor R).obj (relativeHomology R R P n)))
    (z : Algebraic.cycles (ordinary R R P) (n+1 : ℕ)) (a : A),
    letI := torModule T Q A
    ∃ z' : Algebraic.cycles (ordinary R A P) (n+1 : ℕ),
      (ordinaryDegreeIso R A P (n+1)).hom z'.val =
        (F.data A).equiv P (n+1) ((ordinaryDegreeIso R R P (n+1)).hom z.val ⊗ₜ[R] a) ∧
      quotientHomologyEquiv R (ordinary R A P) (n+1 : ℕ)
        ((relative A P n Q).α
          ((quotientHomologyEquiv R (ordinary R R P) (n+1 : ℕ)).symm
            (Algebraic.homologyClass _ _ z) ⊗ₜ[R] a)) = Algebraic.homologyClass _ _ z'
  absolute_zero_formula : ∀ (A : ModuleCat.{v} R) (X : TopCat.{w})
    (z : Algebraic.cycles (ordinaryComplex R R X) 0) (a : A),
    ∃ z' : Algebraic.cycles (ordinaryComplex R A X) 0,
      (ordinaryNonnegativeIso R A X 0).hom z'.val =
        tensorEquiv R A X 0 ((ordinaryNonnegativeIso R R X 0).hom z.val ⊗ₜ[R] a) ∧
      quotientHomologyEquiv R (ordinaryComplex R A X) 0
        (absoluteZero A X
          ((quotientHomologyEquiv R (ordinaryComplex R R X) 0).symm
            (Algebraic.homologyClass _ _ z) ⊗ₜ[R] a)) = Algebraic.homologyClass _ _ z'
  relative_zero_formula : ∀ (A : ModuleCat.{v} R) (P : Pair.{w})
    (z : Algebraic.cycles (ordinary R R P) 0) (a : A),
    ∃ z' : Algebraic.cycles (ordinary R A P) 0,
      (ordinaryDegreeIso R A P 0).hom z'.val =
        (F.data A).equiv P 0 ((ordinaryDegreeIso R R P 0).hom z.val ⊗ₜ[R] a) ∧
      quotientHomologyEquiv R (ordinary R A P) 0
        (relativeZero A P
          ((quotientHomologyEquiv R (ordinary R R P) 0).symm
            (Algebraic.homologyClass _ _ z) ⊗ₜ[R] a)) = Algebraic.homologyClass _ _ z'
  absolute_natural_left : ∀ (A B : ModuleCat.{v} R) {X Y : TopCat.{w}}
    (f : X ⟶ Y) (g : A ⟶ B) (n : ℕ)
    (Q : ProjectiveChoice Rᵐᵒᵖ ((oppositeFunctor R).obj (homology R R X n)))
    (Q' : ProjectiveChoice Rᵐᵒᵖ ((oppositeFunctor R).obj (homology R R Y n))) x,
    letI := torModule T Q A
    letI := torModule T Q' B
    HomologicalComplex.homologyMap
      ((ordinaryFunctor R A).map f ≫ ordinaryCoefficientMap R A g.hom Y) (n+1 : ℕ)
        ((absolute A X n Q).α x) =
      (absolute B Y n Q').α
        (TensorProduct.map (HomologicalComplex.homologyMap ((ordinaryFunctor R R).map f)
          (n+1 : ℕ)).hom g.hom x)
  absolute_natural_right : ∀ (A B : ModuleCat.{v} R) {X Y : TopCat.{w}}
    (f : X ⟶ Y) (g : A ⟶ B) (n : ℕ)
    (Q : ProjectiveChoice Rᵐᵒᵖ ((oppositeFunctor R).obj (homology R R X n)))
    (Q' : ProjectiveChoice Rᵐᵒᵖ ((oppositeFunctor R).obj (homology R R Y n))) x,
    letI := torModule T Q A
    letI := torModule T Q' B
    T.map Q Q' ((oppositeFunctor R).map
      (HomologicalComplex.homologyMap ((ordinaryFunctor R R).map f) n)) g
        ((absolute A X n Q).β x) =
      (absolute B Y n Q').β (HomologicalComplex.homologyMap
        ((ordinaryFunctor R A).map f ≫ ordinaryCoefficientMap R A g.hom Y) (n+1 : ℕ) x)
  relative_natural_left : ∀ (A B : ModuleCat.{v} R) {P P' : Pair.{w}}
    (f : P ⟶ P') (g : A ⟶ B) (n : ℕ)
    (Q : ProjectiveChoice Rᵐᵒᵖ ((oppositeFunctor R).obj (relativeHomology R R P n)))
    (Q' : ProjectiveChoice Rᵐᵒᵖ ((oppositeFunctor R).obj (relativeHomology R R P' n))) x,
    letI := torModule T Q A
    letI := torModule T Q' B
    HomologicalComplex.homologyMap
      (relativeMap (ordinaryFunctor R A) f ≫ relativeOrdinaryCoefficientMap R A g.hom P')
        (n+1 : ℕ) ((relative A P n Q).α x) =
      (relative B P' n Q').α
        (TensorProduct.map (HomologicalComplex.homologyMap (relativeMap (ordinaryFunctor R R) f)
          (n+1 : ℕ)).hom g.hom x)
  relative_natural_right : ∀ (A B : ModuleCat.{v} R) {P P' : Pair.{w}}
    (f : P ⟶ P') (g : A ⟶ B) (n : ℕ)
    (Q : ProjectiveChoice Rᵐᵒᵖ ((oppositeFunctor R).obj (relativeHomology R R P n)))
    (Q' : ProjectiveChoice Rᵐᵒᵖ ((oppositeFunctor R).obj (relativeHomology R R P' n))) x,
    letI := torModule T Q A
    letI := torModule T Q' B
    T.map Q Q' ((oppositeFunctor R).map
      (HomologicalComplex.homologyMap (relativeMap (ordinaryFunctor R R) f) n)) g
        ((relative A P n Q).β x) =
      (relative B P' n Q').β (HomologicalComplex.homologyMap
        (relativeMap (ordinaryFunctor R A) f ≫ relativeOrdinaryCoefficientMap R A g.hom P')
        (n+1 : ℕ) x)
  absolute_zero_natural : ∀ (A B : ModuleCat.{v} R) {X Y : TopCat.{w}}
    (f : X ⟶ Y) (g : A ⟶ B) x,
    HomologicalComplex.homologyMap
      ((ordinaryFunctor R A).map f ≫ ordinaryCoefficientMap R A g.hom Y) 0
        (absoluteZero A X x) =
      absoluteZero B Y (TensorProduct.map
        (HomologicalComplex.homologyMap ((ordinaryFunctor R R).map f) 0).hom g.hom x)
  relative_zero_natural : ∀ (A B : ModuleCat.{v} R) {P P' : Pair.{w}}
    (f : P ⟶ P') (g : A ⟶ B) x,
    HomologicalComplex.homologyMap
      (relativeMap (ordinaryFunctor R A) f ≫ relativeOrdinaryCoefficientMap R A g.hom P') 0
        (relativeZero A P x) =
      relativeZero B P' (TensorProduct.map
        (HomologicalComplex.homologyMap (relativeMap (ordinaryFunctor R R) f) 0).hom g.hom x)

/-- The unique linear short exact sequence with a zero right endpoint. -/
def zeroSequenceOfEquiv {L M N : Type*}
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    [Module R L] [Module R M] [Module R N] [Subsingleton N]
    (e : L ≃ₗ[R] M) : SplitExactSequence R L M N where
  α := e.toLinearMap
  β := 0
  injective_α := e.injective
  exact := by
    intro x
    constructor
    · intro _; exact e.surjective x
    · intro _; rfl
  surjective_β := fun x => ⟨0, Subsingleton.elim _ _⟩
  split := ⟨0, by ext x; exact Subsingleton.elim _ _⟩

namespace Family
variable {R} {T : TorMaps.{u,max u w,v} R 1} {F : RelativeTensorFamily.{u,v,w} R}

def absoluteAtZero (S : Family R T F) (A : ModuleCat.{v} R) (X : TopCat.{w})
    (Q : ProjectiveChoice Rᵐᵒᵖ ((oppositeFunctor R).obj (homology R R X (-1)))) :
    letI := torModule T Q A
    SplitExactSequence R (homology R R X 0 ⊗[R] A) (homology R A X 0) (TorWith Q.val A 1) := by
  letI := torModule T Q A
  letI := S.absoluteZeroTor A X Q
  exact zeroSequenceOfEquiv R (S.absoluteZero A X)

def relativeAtZero (S : Family R T F) (A : ModuleCat.{v} R) (P : Pair.{w})
    (Q : ProjectiveChoice Rᵐᵒᵖ ((oppositeFunctor R).obj (relativeHomology R R P (-1)))) :
    letI := torModule T Q A
    SplitExactSequence R (relativeHomology R R P 0 ⊗[R] A) (relativeHomology R A P 0)
      (TorWith Q.val A 1) := by
  letI := torModule T Q A
  letI := S.relativeZeroTor A P Q
  exact zeroSequenceOfEquiv R (S.relativeZero A P)

/-- The absolute sequence in every nonnegative degree, with its actual H_(n-1) term. -/
def absoluteAll (S : Family R T F) (A : ModuleCat.{v} R) (X : TopCat.{w}) (n : ℕ) :
    ∀ (Q : ProjectiveChoice Rᵐᵒᵖ ((oppositeFunctor R).obj (homology R R X ((n : ℤ)-1)))),
    letI := torModule T Q A
    SplitExactSequence R (homology R R X (n : ℤ) ⊗[R] A) (homology R A X (n : ℤ))
      (TorWith Q.val A 1) := by
  cases n with
  | zero => exact S.absoluteAtZero A X
  | succ n =>
    rw [show ((n+1 : ℕ) : ℤ)-1 = (n : ℤ) by omega]
    exact S.absolute A X n

/-- The relative sequence in every nonnegative degree, including the zero tail. -/
def relativeAll (S : Family R T F) (A : ModuleCat.{v} R) (P : Pair.{w}) (n : ℕ) :
    ∀ (Q : ProjectiveChoice Rᵐᵒᵖ ((oppositeFunctor R).obj (relativeHomology R R P ((n : ℤ)-1)))),
    letI := torModule T Q A
    SplitExactSequence R (relativeHomology R R P (n : ℤ) ⊗[R] A)
      (relativeHomology R A P (n : ℤ)) (TorWith Q.val A 1) := by
  cases n with
  | zero => exact S.relativeAtZero A P
  | succ n =>
    rw [show ((n+1 : ℕ) : ℤ)-1 = (n : ℤ) by omega]
    exact S.relative A P n

@[simp] lemma absoluteAtZero_β (S : Family R T F) (A : ModuleCat.{v} R) (X : TopCat.{w})
    (Q : ProjectiveChoice Rᵐᵒᵖ ((oppositeFunctor R).obj (homology R R X (-1)))) :
    letI := torModule T Q A
    (S.absoluteAtZero A X Q).β = 0 := rfl

@[simp] lemma relativeAtZero_β (S : Family R T F) (A : ModuleCat.{v} R) (P : Pair.{w})
    (Q : ProjectiveChoice Rᵐᵒᵖ ((oppositeFunctor R).obj (relativeHomology R R P (-1)))) :
    letI := torModule T Q A
    (S.relativeAtZero A P Q).β = 0 := rfl

end Family

end TopologicalUCT

def topological_uct_type : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R],
    ∃ (T : P103.Specs.Ch11.ExtTorDefinitions.TorMaps.{u,max u w,v} R 1)
      (F : RelativeTensorFamily.{u,v,w} R), Nonempty (TopologicalUCT.Family R T F)

end P202Specs.UniversalCoefficientsHomology
