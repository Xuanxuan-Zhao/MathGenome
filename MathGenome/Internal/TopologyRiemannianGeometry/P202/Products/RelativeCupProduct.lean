import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.RelativeCupProduct
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Products.CupProduct
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Cohomology.Pairs
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SmallChainEquivalence
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.HomologySequenceLemmas

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
open scoped TensorProduct Simplicial
namespace P202.RelativeCupProduct
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CohomologyPairs P202Specs.CupProduct P202Specs.RelativeCupProduct
universe u w
variable (R : Type u) [CommRing R]

/-- Restriction of the left factor to U forces the cup to vanish on U. -/
lemma cup_vanishes_left (P : Pair.{w}) (p q : ℕ)
    (a : Cochain R P.space p) (b : Cochain R P.space q)
    (ha : a ∈ vanishingCochains R R P p) :
    cup R P.space p q a b ∈ vanishingCochains R R P (p+q) := by
  change pullback R P.inclusion (p+q) (cup R P.space p q a b) = 0
  rw [P202.CupProduct.cup_natural]
  change pullback R P.inclusion p a = 0 at ha
  rw [ha, map_zero, LinearMap.zero_apply]

/-- Restriction of the right factor to V forces the cup to vanish on V. -/
lemma cup_vanishes_right (P : Pair.{w}) (p q : ℕ)
    (a : Cochain R P.space p) (b : Cochain R P.space q)
    (hb : b ∈ vanishingCochains R R P q) :
    cup R P.space p q a b ∈ vanishingCochains R R P (p+q) := by
  change pullback R P.inclusion (p+q) (cup R P.space p q a b) = 0
  rw [P202.CupProduct.cup_natural]
  change pullback R P.inclusion q b = 0 at hb
  rw [hb, map_zero]

lemma range_le_ker_of_vanishing (P : Pair.{w}) (n : ℕ) (a : Cochain R P.space n)
    (ha : a ∈ vanishingCochains R R P n) :
    ((chainMap R R P.inclusion).f n).hom.range ≤ a.ker := by
  rintro c ⟨d, rfl⟩
  exact congrArg (fun f : Cochain R P.sub n => f d) ha

theorem cochainVanishing : cochainVanishing_type.{u,w} := by
  intro R _ P p q a b ha hb c hc
  have hl := range_le_ker_of_vanishing R P.leftPair (p+q) _
    (cup_vanishes_left R P.leftPair p q a b ha)
  have hr := range_le_ker_of_vanishing R P.rightPair (p+q) _
    (cup_vanishes_right R P.rightPair p q a b hb)
  exact (sup_le hl hr) hc

/-- The comparison to the sum quotient respects passage to absolute cochains. -/
lemma comparison_absolute (P : TwoSubspaces.{w}) :
    unionComparison R P ≫ sumToAbsolute R P = relativeToAbsolute R R P.unionPair := by
  change (dualComplexFunctor R R (ComplexShape.down ℤ)).map (sumToUnion R P).op ≫
    (dualComplexFunctor R R (ComplexShape.down ℤ)).map (sumProjection R P).op = _
  rw [← Functor.map_comp, ← op_comp]
  congr 1
  exact congrArg Quiver.Hom.op (cokernel.π_desc _ _ _)

lemma sumToAbsolute_injective (P : TwoSubspaces.{w}) (n : ℤ) :
    Function.Injective ((sumToAbsolute R P).f n) := by
  intro a b hab
  apply LinearMap.ext
  intro c
  obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective ((sumProjection R P).f n)).mp
    inferInstance c
  exact congrArg (fun f : (ordinaryComplex R R P.space).X n →ₗ[R] R => f x) hab

/-- Coordinate cochains of actual relative cochains vanish on the subspace. -/
lemma relativeValue_vanishes (P : Pair.{w}) (n : ℕ)
    (a : (relativeCochains R R P).X (n : ℤ)) :
    ordinaryCochainsEquiv R R P.space n ((relativeToAbsolute R R P).f (n : ℤ) a) ∈
      vanishingCochains R R P n := by
  have hz := congrArg (fun f : relativeCochains R R P ⟶ ordinaryCochains R R P.sub =>
    f.f (n : ℤ) a) (cochainSequence R R P).zero
  change (restriction R R P).f (n : ℤ) ((relativeToAbsolute R R P).f (n : ℤ) a) = 0 at hz
  change pullback R P.inclusion n _ = 0
  rw [← P202.CupProduct.ordinaryCochainsEquiv_pullback]
  change ordinaryCochainsEquiv R R P.sub n
    ((restriction R R P).f (n : ℤ) ((relativeToAbsolute R R P).f (n : ℤ) a)) = 0
  rw [hz, map_zero]

/-- Raising only the coefficient universe permits categorical descent in the
same module category as the singular chains. -/
def raisedOrdinaryCochain (X : TopCat.{w}) (n : ℕ) (a : Cochain R X n) :
    (ordinaryComplex R R X).X (n : ℤ) →ₗ[R] ULift.{w} R :=
  (ULift.moduleEquiv (R := R) (M := R)).symm.toLinearMap.comp
    (show (ordinaryComplex R R X).X (n : ℤ) →ₗ[R] R from
      (ordinaryCochainsEquiv R R X n).symm a)

lemma ordinary_restriction_zero (P : Pair.{w}) (n : ℕ)
    (a : Cochain R P.space n) (ha : a ∈ vanishingCochains R R P n) :
    (inclusion (ordinaryFunctor R R) P).f (n : ℤ) ≫
      ModuleCat.ofHom (raisedOrdinaryCochain R P.space n a) = 0 := by
  have hz : ((ordinaryCochainFunctor R R).map P.inclusion.op).f (n : ℤ)
      ((ordinaryCochainsEquiv R R P.space n).symm a) = 0 := by
    apply (ordinaryCochainsEquiv R R P.sub n).injective
    rw [P202.CupProduct.ordinaryCochainsEquiv_pullback, LinearEquiv.apply_symm_apply, map_zero]
    exact ha
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let c : (ordinaryComplex R R P.space).X (n : ℤ) →ₗ[R] R :=
    (ordinaryCochainsEquiv R R P.space n).symm a
  have hx := congrArg (fun f : (ordinaryComplex R R P.sub).X (n : ℤ) →ₗ[R] R => f x) hz
  change ULift.up (c ((inclusion (ordinaryFunctor R R) P).f (n : ℤ) x)) = 0
  change c ((inclusion (ordinaryFunctor R R) P).f (n : ℤ) x) = 0 at hx
  rw [hx]
  rfl

lemma sumInclusion_raised_zero (P : TwoSubspaces.{w}) (n : ℕ)
    (a : Cochain R P.space n)
    (hl : a ∈ vanishingCochains R R P.leftPair n)
    (hr : a ∈ vanishingCochains R R P.rightPair n) :
    (sumInclusion R P).f (n : ℤ) ≫
      ModuleCat.ofHom (raisedOrdinaryCochain R P.space n a) = 0 := by
  apply HomologicalComplex.biprodX_ext_from
  · simp only [comp_zero, ← Category.assoc, sumInclusion, biprod_inl_desc_f]
    exact ordinary_restriction_zero R P.leftPair n a hl
  · simp only [comp_zero, ← Category.assoc, sumInclusion, biprod_inr_desc_f]
    exact ordinary_restriction_zero R P.rightPair n a hr

/-- Descent of a cochain annihilating both subspace chain modules to the
actual categorical cokernel. No vanishing on arbitrary union simplices is used. -/
def sumCochainOfVanishing (P : TwoSubspaces.{w}) (n : ℕ)
    (a : Cochain R P.space n)
    (hl : a ∈ vanishingCochains R R P.leftPair n)
    (hr : a ∈ vanishingCochains R R P.rightPair n) :
    (sumCochains R P).X (n : ℤ) :=
  (ULift.moduleEquiv (R := R) (M := R)).toLinearMap.comp
    ((PreservesCokernel.iso (HomologicalComplex.eval _ _ (n : ℤ))
      (sumInclusion R P)).hom ≫
      cokernel.desc _ (ModuleCat.ofHom (raisedOrdinaryCochain R P.space n a))
        (sumInclusion_raised_zero R P n a hl hr)).hom

@[simp] lemma sumCochainOfVanishing_value (P : TwoSubspaces.{w}) (n : ℕ)
    (a : Cochain R P.space n)
    (hl : a ∈ vanishingCochains R R P.leftPair n)
    (hr : a ∈ vanishingCochains R R P.rightPair n) :
    ordinaryCochainsEquiv R R P.space n
      ((sumToAbsolute R P).f (n : ℤ) (sumCochainOfVanishing R P n a hl hr)) = a := by
  have he : (sumProjection R P).f (n : ℤ) ≫
      ((PreservesCokernel.iso (HomologicalComplex.eval _ _ (n : ℤ))
        (sumInclusion R P)).hom ≫
        cokernel.desc _ (ModuleCat.ofHom (raisedOrdinaryCochain R P.space n a))
          (sumInclusion_raised_zero R P n a hl hr)) =
      ModuleCat.ofHom (raisedOrdinaryCochain R P.space n a) := by
    have h := PreservesCokernel.π_iso_hom (HomologicalComplex.eval _ _ (n : ℤ))
      (sumInclusion R P)
    erw [← Category.assoc, h, cokernel.π_desc]
  apply (ordinaryCochainsEquiv R R P.space n).eq_symm_apply.mp
  apply LinearMap.ext
  intro x
  exact congrArg ULift.down (congrArg (fun f => f x) he)

def relativeValueLinear (P : Pair.{w}) (n : ℕ) :
    (relativeCochains R R P).X (n : ℤ) →ₗ[R] Cochain R P.space n :=
  (ordinaryCochainsEquiv R R P.space n).toLinearMap.comp
    ((relativeToAbsolute R R P).f (n : ℤ)).hom

def sumValueLinear (P : TwoSubspaces.{w}) (n : ℕ) :
    (sumCochains R P).X (n : ℤ) →ₗ[R] Cochain R P.space n :=
  (ordinaryCochainsEquiv R R P.space n).toLinearMap.comp
    ((sumToAbsolute R P).f (n : ℤ)).hom

lemma sumValueLinear_injective (P : TwoSubspaces.{w}) (n : ℕ) :
    Function.Injective (sumValueLinear R P n) :=
  (ordinaryCochainsEquiv R R P.space n).injective.comp (sumToAbsolute_injective R P (n : ℤ))

def cochainCupFun (P : TwoSubspaces.{w}) (p q : ℕ)
    (a : (relativeCochains R R P.leftPair).X (p : ℤ))
    (b : (relativeCochains R R P.rightPair).X (q : ℤ)) :
    (sumCochains R P).X ((p+q : ℕ) : ℤ) :=
  sumCochainOfVanishing R P (p+q)
    (cup R P.space p q (relativeValueLinear R P.leftPair p a) (relativeValueLinear R P.rightPair q b))
    (cup_vanishes_left R P.leftPair p q _ _ (relativeValue_vanishes R P.leftPair p a))
    (cup_vanishes_right R P.rightPair p q _ _ (relativeValue_vanishes R P.rightPair q b))

@[simp] lemma cochainCupFun_value (P : TwoSubspaces.{w}) (p q : ℕ)
    (a : (relativeCochains R R P.leftPair).X (p : ℤ))
    (b : (relativeCochains R R P.rightPair).X (q : ℤ)) :
    sumValueLinear R P (p+q) (cochainCupFun R P p q a b) =
      cup R P.space p q (relativeValueLinear R P.leftPair p a)
        (relativeValueLinear R P.rightPair q b) :=
  sumCochainOfVanishing_value R P (p+q) _ _ _

/-- The front/back formula is bilinear already on relative cochains. -/
def cochainCup (P : TwoSubspaces.{w}) (p q : ℕ) :
    (relativeCochains R R P.leftPair).X (p : ℤ) →ₗ[R]
      (relativeCochains R R P.rightPair).X (q : ℤ) →ₗ[R]
        (sumCochains R P).X ((p+q : ℕ) : ℤ) where
  toFun a :=
    { toFun := cochainCupFun R P p q a
      map_add' := by
        intro b c
        apply sumValueLinear_injective R P (p+q)
        simp only [map_add, cochainCupFun_value]
      map_smul' := by
        intro r b
        apply sumValueLinear_injective R P (p+q)
        simp only [map_smul, cochainCupFun_value, RingHom.id_apply] }
  map_add' := by
    intro a b
    apply LinearMap.ext
    intro c
    apply sumValueLinear_injective R P (p+q)
    change sumValueLinear R P (p+q) (cochainCupFun R P p q (a+b) c) =
      sumValueLinear R P (p+q) (cochainCupFun R P p q a c + cochainCupFun R P p q b c)
    simp only [map_add, cochainCupFun_value, LinearMap.add_apply]
  map_smul' := by
    intro r a
    apply LinearMap.ext
    intro b
    apply sumValueLinear_injective R P (p+q)
    change sumValueLinear R P (p+q) (cochainCupFun R P p q (r • a) b) =
      sumValueLinear R P (p+q) (r • cochainCupFun R P p q a b)
    simp only [map_smul, cochainCupFun_value, LinearMap.smul_apply]

theorem cochainProduct : cochainProduct_type.{u,w} := by
  intro R _ P p q
  exact ⟨cochainCup R P p q, cochainCupFun_value R P p q⟩

@[simp] lemma cochainCup_value (P : TwoSubspaces.{w}) (p q : ℕ)
    (a : (relativeCochains R R P.leftPair).X (p : ℤ))
    (b : (relativeCochains R R P.rightPair).X (q : ℤ)) :
    sumValueLinear R P (p+q) (cochainCup R P p q a b) =
      cup R P.space p q (relativeValueLinear R P.leftPair p a)
        (relativeValueLinear R P.rightPair q b) := cochainCupFun_value R P p q a b

/-- Values commute with the differential because the projections are chain maps. -/
lemma relativeValueLinear_d (P : Pair.{w}) (n : ℕ)
    (a : (relativeCochains R R P).X (n : ℤ)) :
    relativeValueLinear R P (n+1)
      ((relativeCochains R R P).d (n : ℤ) ((n+1 : ℕ) : ℤ) a) =
      delta R P.space n (relativeValueLinear R P n a) := by
  unfold relativeValueLinear
  change ordinaryCochainsEquiv R R P.space (n+1) _ = _
  exact (congrArg (ordinaryCochainsEquiv R R P.space (n+1))
    (congrArg (fun f => f a) ((relativeToAbsolute R R P).comm _ _).symm)).trans
      (P202.CupProduct.ordinaryCochainsEquiv_d R P.space n _)

lemma sumValueLinear_d (P : TwoSubspaces.{w}) (n : ℕ)
    (a : (sumCochains R P).X (n : ℤ)) :
    sumValueLinear R P (n+1)
      ((sumCochains R P).d (n : ℤ) ((n+1 : ℕ) : ℤ) a) =
      delta R P.space n (sumValueLinear R P n a) := by
  unfold sumValueLinear
  change ordinaryCochainsEquiv R R P.space (n+1) _ = _
  exact (congrArg (ordinaryCochainsEquiv R R P.space (n+1))
    (congrArg (fun f => f a) ((sumToAbsolute R P).comm _ _).symm)).trans
      (P202.CupProduct.ordinaryCochainsEquiv_d R P.space n _)

lemma relativeCocycleValue_delta (P : Pair.{w}) (n : ℕ)
    (a : (relativeCochains R R P).cycles (n : ℤ)) :
    delta R P.space n (relativeCocycleValue R P n a) = 0 := by
  change delta R P.space n (relativeValueLinear R P n ((relativeCochains R R P).iCycles (n : ℤ) a)) = 0
  rw [← relativeValueLinear_d]
  have hz := congrArg (fun f => f a)
    ((relativeCochains R R P).iCycles_d (n : ℤ) ((n+1 : ℕ) : ℤ))
  change (relativeCochains R R P).d _ _ ((relativeCochains R R P).iCycles (n : ℤ) a) = 0 at hz
  rw [hz, map_zero]

/-- The categorical cycles object contains every element killed by the differential. -/
def cycleOfElement (K : CochainComplex (ModuleCat.{max u w} R) ℤ) (n : ℕ)
    (a : K.X (n : ℤ)) (ha : K.d (n : ℤ) ((n+1 : ℕ) : ℤ) a = 0) : K.cycles (n : ℤ) :=
  ((K.sc (n : ℤ)).moduleCatCyclesIso.inv)
    ⟨a, by
      change K.d (n : ℤ) (((ComplexShape.down ℤ).symm).next (n : ℤ)) a = 0
      rw [((ComplexShape.down ℤ).symm).next_eq' (by simp :
        ((ComplexShape.down ℤ).symm).Rel (n : ℤ) ((n+1 : ℕ) : ℤ))]
      exact ha⟩

@[simp] lemma iCycles_cycleOfElement
    (K : CochainComplex (ModuleCat.{max u w} R) ℤ) (n : ℕ)
    (a : K.X (n : ℤ)) (ha : K.d (n : ℤ) ((n+1 : ℕ) : ℤ) a = 0) :
    K.iCycles (n : ℤ) (cycleOfElement R K n a ha) = a := by
  exact congrArg (fun f => f
    (⟨a, by
      change K.d (n : ℤ) (((ComplexShape.down ℤ).symm).next (n : ℤ)) a = 0
      rw [((ComplexShape.down ℤ).symm).next_eq' (by simp :
        ((ComplexShape.down ℤ).symm).Rel (n : ℤ) ((n+1 : ℕ) : ℤ))]
      exact ha⟩ : (K.sc (n : ℤ)).g.hom.ker))
    (K.sc (n : ℤ)).moduleCatCyclesIso_inv_iCycles

lemma sumCocycleValue_injective (P : TwoSubspaces.{w}) (n : ℕ) :
    Function.Injective (sumCocycleValue R P n) := by
  intro a b hab
  apply (ModuleCat.mono_iff_injective ((sumCochains R P).iCycles (n : ℤ))).mp inferInstance
  exact sumValueLinear_injective R P n hab

def relativeCycleCup (P : TwoSubspaces.{w}) (p q : ℕ)
    (a : (relativeCochains R R P.leftPair).cycles (p : ℤ))
    (b : (relativeCochains R R P.rightPair).cycles (q : ℤ)) :
    (sumCochains R P).cycles ((p+q : ℕ) : ℤ) :=
  cycleOfElement R (sumCochains R P) (p+q)
    (cochainCup R P p q ((relativeCochains R R P.leftPair).iCycles (p : ℤ) a)
      ((relativeCochains R R P.rightPair).iCycles (q : ℤ) b)) (by
        apply sumValueLinear_injective R P (p+q+1)
        rw [sumValueLinear_d, cochainCup_value, map_zero]
        exact P202.CupProduct.cup_cocycle R P.space p q _ _
          (relativeCocycleValue_delta R P.leftPair p a)
          (relativeCocycleValue_delta R P.rightPair q b))

@[simp] lemma relativeCycleCup_value (P : TwoSubspaces.{w}) (p q : ℕ)
    (a : (relativeCochains R R P.leftPair).cycles (p : ℤ))
    (b : (relativeCochains R R P.rightPair).cycles (q : ℤ)) :
    sumCocycleValue R P (p+q) (relativeCycleCup R P p q a b) =
      cup R P.space p q (relativeCocycleValue R P.leftPair p a)
        (relativeCocycleValue R P.rightPair q b) := by
  unfold sumCocycleValue relativeCycleCup
  rw [iCycles_cycleOfElement]
  exact cochainCupFun_value R P p q _ _

def sumCycleValueLinear (P : TwoSubspaces.{w}) (n : ℕ) :
    (sumCochains R P).cycles (n : ℤ) →ₗ[R] Cochain R P.space n :=
  (sumValueLinear R P n).comp (((sumCochains R P).iCycles (n : ℤ)).hom)

def relativeCycleValueLinear (P : Pair.{w}) (n : ℕ) :
    (relativeCochains R R P).cycles (n : ℤ) →ₗ[R] Cochain R P.space n :=
  (relativeValueLinear R P n).comp (((relativeCochains R R P).iCycles (n : ℤ)).hom)

@[simp] lemma sumCocycleValue_add (P : TwoSubspaces.{w}) (n : ℕ)
    (a b : (sumCochains R P).cycles (n : ℤ)) :
    sumCocycleValue R P n (a+b) = sumCocycleValue R P n a + sumCocycleValue R P n b :=
  (sumCycleValueLinear R P n).map_add a b

@[simp] lemma sumCocycleValue_smul (P : TwoSubspaces.{w}) (n : ℕ) (r : R)
    (a : (sumCochains R P).cycles (n : ℤ)) :
    sumCocycleValue R P n (r • a) = r • sumCocycleValue R P n a :=
  (sumCycleValueLinear R P n).map_smul r a

@[simp] lemma relativeCocycleValue_add (P : Pair.{w}) (n : ℕ)
    (a b : (relativeCochains R R P).cycles (n : ℤ)) :
    relativeCocycleValue R P n (a+b) = relativeCocycleValue R P n a + relativeCocycleValue R P n b :=
  (relativeCycleValueLinear R P n).map_add a b

@[simp] lemma relativeCocycleValue_smul (P : Pair.{w}) (n : ℕ) (r : R)
    (a : (relativeCochains R R P).cycles (n : ℤ)) :
    relativeCocycleValue R P n (r • a) = r • relativeCocycleValue R P n a :=
  (relativeCycleValueLinear R P n).map_smul r a

/-- The product of relative cocycles is bilinear in the sum cycles object. -/
def relativeCycleCupLinear (P : TwoSubspaces.{w}) (p q : ℕ) :
    (relativeCochains R R P.leftPair).cycles (p : ℤ) →ₗ[R]
      (relativeCochains R R P.rightPair).cycles (q : ℤ) →ₗ[R]
        (sumCochains R P).cycles ((p+q : ℕ) : ℤ) where
  toFun a :=
    { toFun := relativeCycleCup R P p q a
      map_add' := by
        intro b c
        apply sumCocycleValue_injective R P (p+q)
        simp only [sumCocycleValue_add, relativeCycleCup_value, relativeCocycleValue_add, map_add]
      map_smul' := by
        intro r b
        apply sumCocycleValue_injective R P (p+q)
        simp only [sumCocycleValue_smul, relativeCycleCup_value, relativeCocycleValue_smul, map_smul, RingHom.id_apply] }
  map_add' := by
    intro a b
    apply LinearMap.ext
    intro c
    apply sumCocycleValue_injective R P (p+q)
    change sumCocycleValue R P (p+q) (relativeCycleCup R P p q (a+b) c) =
      sumCocycleValue R P (p+q) (relativeCycleCup R P p q a c + relativeCycleCup R P p q b c)
    simp only [sumCocycleValue_add, relativeCycleCup_value, relativeCocycleValue_add, map_add, LinearMap.add_apply]
  map_smul' := by
    intro r a
    apply LinearMap.ext
    intro b
    apply sumCocycleValue_injective R P (p+q)
    change sumCocycleValue R P (p+q) (relativeCycleCup R P p q (r • a) b) =
      sumCocycleValue R P (p+q) (r • relativeCycleCup R P p q a b)
    simp only [sumCocycleValue_smul, relativeCycleCup_value, relativeCocycleValue_smul, map_smul, LinearMap.smul_apply]

/-- In positive degrees, a zero relative class has a relative primitive. -/
lemma relative_class_zero_iff (P : Pair.{w}) (n : ℕ)
    (a : (relativeCochains R R P).cycles ((n+1 : ℕ) : ℤ)) :
    (relativeCochains R R P).homologyπ ((n+1 : ℕ) : ℤ) a = 0 ↔
      ∃ c : (relativeCochains R R P).X (n : ℤ),
        (relativeCochains R R P).d (n : ℤ) ((n+1 : ℕ) : ℤ) c =
          (relativeCochains R R P).iCycles ((n+1 : ℕ) : ℤ) a := by
  change ((relativeCochains R R P).sc ((n+1 : ℕ) : ℤ)).homologyπ a = 0 ↔ _
  rw [P202.CupProduct.shortComplex_homologyπ_eq_zero_iff]
  have hp : ((ComplexShape.down ℤ).symm).prev ((n+1 : ℕ) : ℤ) = (n : ℤ) :=
    ((ComplexShape.down ℤ).symm).prev_eq' (by simp)
  change (∃ x : (relativeCochains R R P).X (((ComplexShape.down ℤ).symm).prev ((n+1 : ℕ) : ℤ)),
    (relativeCochains R R P).d _ ((n+1 : ℕ) : ℤ) x = _) ↔ _
  erw [hp]
  rfl

/-- There are no negative relative cochains, so a zero class in degree zero
already has zero cocycle representative. -/
lemma relative_class_zero_degree_zero (P : Pair.{w})
    (a : (relativeCochains R R P).cycles 0)
    (ha : (relativeCochains R R P).homologyπ 0 a = 0) : a = 0 := by
  obtain ⟨x, hx⟩ := (P202.CupProduct.shortComplex_homologyπ_eq_zero_iff R
    ((relativeCochains R R P).sc 0) a).mp ha
  have hp : ((ComplexShape.down ℤ).symm).prev 0 = -1 :=
    ((ComplexShape.down ℤ).symm).prev_eq' (by simp)
  have hz := (P202.CohomologyPairs.negative R R).2 P
    (((ComplexShape.down ℤ).symm).prev 0) (by rw [hp]; omega)
  have : Subsingleton (((relativeCochains R R P).sc 0).X₁) :=
    ModuleCat.subsingleton_of_isZero hz.1
  have hx0 : x = 0 := Subsingleton.elim _ _
  rw [hx0, map_zero] at hx
  apply (ModuleCat.mono_iff_injective ((relativeCochains R R P).iCycles 0)).mp inferInstance
  exact hx.symm.trans (((relativeCochains R R P).iCycles 0).hom.map_zero).symm

/-- A primitive in the sum dual, checked after its injective ordinary inclusion,
proves that the actual sum cohomology class is zero. -/
lemma sum_class_zero_of_primitive (P : TwoSubspaces.{w}) (t n : ℕ) (h : t=n+1)
    (a : (sumCochains R P).cycles (t : ℤ))
    (c : (sumCochains R P).X (n : ℤ))
    (hc : castCochain R h (sumCocycleValue R P t a) =
      delta R P.space n (sumValueLinear R P n c)) :
    (sumCochains R P).homologyπ (t : ℤ) a = 0 := by
  subst t
  apply (P202.CupProduct.shortComplex_homologyπ_eq_zero_iff R
    ((sumCochains R P).sc ((n+1 : ℕ) : ℤ)) a).mpr
  have hp : ((ComplexShape.down ℤ).symm).prev ((n+1 : ℕ) : ℤ) = (n : ℤ) :=
    ((ComplexShape.down ℤ).symm).prev_eq' (by simp)
  change ∃ x : (sumCochains R P).X (((ComplexShape.down ℤ).symm).prev ((n+1 : ℕ) : ℤ)),
    (sumCochains R P).d _ ((n+1 : ℕ) : ℤ) x = _
  rw [hp]
  refine ⟨c, ?_⟩
  apply sumValueLinear_injective R P (n+1)
  rw [sumValueLinear_d]
  exact hc.symm

abbrev relativeClassMap (P : Pair.{w}) (n : ℕ) :
    (relativeCochains R R P).cycles (n : ℤ) →ₗ[R] HR R P n :=
  ((relativeCochains R R P).homologyπ (n : ℤ)).hom

lemma relativeClassMap_surjective (P : Pair.{w}) (n : ℕ) :
    Function.Surjective (relativeClassMap R P n) :=
  (ModuleCat.epi_iff_surjective ((relativeCochains R R P).homologyπ (n : ℤ))).mp inferInstance

def sumCycleCupClass (P : TwoSubspaces.{w}) (p q : ℕ) :
    (relativeCochains R R P.leftPair).cycles (p : ℤ) →ₗ[R]
      (relativeCochains R R P.rightPair).cycles (q : ℤ) →ₗ[R]
        (sumCochains R P).homology ((p+q : ℕ) : ℤ) :=
  (LinearMap.llcomp R _ _ _ (((sumCochains R P).homologyπ ((p+q : ℕ) : ℤ)).hom)).comp
    (relativeCycleCupLinear R P p q)

lemma sumCycleCupClass_left_zero_positive (P : TwoSubspaces.{w}) (p q : ℕ)
    (a : (relativeCochains R R P.leftPair).cycles ((p+1 : ℕ) : ℤ))
    (b : (relativeCochains R R P.rightPair).cycles (q : ℤ))
    (ha : relativeClassMap R P.leftPair (p+1) a = 0) :
    sumCycleCupClass R P (p+1) q a b = 0 := by
  obtain ⟨c, hc⟩ := (relative_class_zero_iff R P.leftPair p a).mp ha
  apply sum_class_zero_of_primitive R P (p+1+q) (p+q) (by omega)
    (relativeCycleCup R P (p+1) q a b)
    (cochainCup R P p q c ((relativeCochains R R P.rightPair).iCycles (q : ℤ) b))
  rw [relativeCycleCup_value, cochainCup_value]
  have hd : relativeCocycleValue R P.leftPair (p+1) a =
      delta R P.space p (relativeValueLinear R P.leftPair p c) := by
    exact (congrArg (relativeValueLinear R P.leftPair (p+1)) hc.symm).trans
      (relativeValueLinear_d R P.leftPair p c)
  rw [hd]
  exact P202.CupProduct.cup_boundary_left R P.space p q _ _
    (relativeCocycleValue_delta R P.rightPair q b)

lemma sumCycleCupClass_right_zero_positive (P : TwoSubspaces.{w}) (p q : ℕ)
    (a : (relativeCochains R R P.leftPair).cycles (p : ℤ))
    (b : (relativeCochains R R P.rightPair).cycles ((q+1 : ℕ) : ℤ))
    (hb : relativeClassMap R P.rightPair (q+1) b = 0) :
    sumCycleCupClass R P p (q+1) a b = 0 := by
  obtain ⟨c, hc⟩ := (relative_class_zero_iff R P.rightPair q b).mp hb
  apply sum_class_zero_of_primitive R P (p+(q+1)) (p+q) (by omega)
    (relativeCycleCup R P p (q+1) a b)
    ((-1 : ℤ)^p • cochainCup R P p q
      ((relativeCochains R R P.leftPair).iCycles (p : ℤ) a) c)
  rw [relativeCycleCup_value, map_zsmul, cochainCup_value, map_zsmul]
  have hd : relativeCocycleValue R P.rightPair (q+1) b =
      delta R P.space q (relativeValueLinear R P.rightPair q c) := by
    exact (congrArg (relativeValueLinear R P.rightPair (q+1)) hc.symm).trans
      (relativeValueLinear_d R P.rightPair q c)
  rw [hd]
  exact P202.CupProduct.cup_boundary_right R P.space p q _ _
    (relativeCocycleValue_delta R P.leftPair p a)

lemma sumCycleCupClass_left_zero (P : TwoSubspaces.{w}) (p q : ℕ)
    (a : (relativeCochains R R P.leftPair).cycles (p : ℤ))
    (ha : relativeClassMap R P.leftPair p a = 0) :
    sumCycleCupClass R P p q a = 0 := by
  apply LinearMap.ext
  intro b
  cases p with
  | zero =>
    rw [relative_class_zero_degree_zero R P.leftPair a ha, map_zero, LinearMap.zero_apply]
  | succ p => exact sumCycleCupClass_left_zero_positive R P p q a b ha

lemma sumCycleCupClass_right_zero (P : TwoSubspaces.{w}) (p q : ℕ)
    (a : (relativeCochains R R P.leftPair).cycles (p : ℤ))
    (b : (relativeCochains R R P.rightPair).cycles (q : ℤ))
    (hb : relativeClassMap R P.rightPair q b = 0) :
    sumCycleCupClass R P p q a b = 0 := by
  cases q with
  | zero => rw [relative_class_zero_degree_zero R P.rightPair b hb, map_zero]
  | succ q => exact sumCycleCupClass_right_zero_positive R P p q a b hb

/-- Cup product on actual relative cohomology into the cohomology of the actual
sum quotient. This construction does not require either subspace to be open. -/
def sumHCup (P : TwoSubspaces.{w}) (p q : ℕ) :
    HR R P.leftPair p →ₗ[R] HR R P.rightPair q →ₗ[R]
      (sumCochains R P).homology ((p+q : ℕ) : ℤ) :=
  P202.CupProduct.descendBilinear (relativeClassMap R P.leftPair p)
    (relativeClassMap R P.rightPair q) (relativeClassMap_surjective R P.leftPair p)
    (relativeClassMap_surjective R P.rightPair q) (sumCycleCupClass R P p q)
    (sumCycleCupClass_left_zero R P p q) (sumCycleCupClass_right_zero R P p q)

@[simp] lemma sumHCup_rep (P : TwoSubspaces.{w}) (p q : ℕ)
    (a : (relativeCochains R R P.leftPair).cycles (p : ℤ))
    (b : (relativeCochains R R P.rightPair).cycles (q : ℤ)) :
    sumHCup R P p q (relativeClassMap R P.leftPair p a) (relativeClassMap R P.rightPair q b) =
      (sumCochains R P).homologyπ ((p+q : ℕ) : ℤ) (relativeCycleCup R P p q a b) :=
  P202.CupProduct.descendBilinear_apply _ _ _ _ _ _ _ a b

/-- Pushforward preserves the sum of the two subspace chain images. -/
lemma sumInclusion_square {P Q : TwoSubspaces.{w}} (f : P.Map Q) :
    sumInclusion R P ≫ (ordinaryFunctor R R).map f.map =
      biprod.map ((ordinaryFunctor R R).map f.leftMap.restrict)
        ((ordinaryFunctor R R).map f.rightMap.restrict) ≫ sumInclusion R Q := by
  apply biprod.hom_ext' <;>
    simp only [sumInclusion, biprod.inl_desc_assoc, biprod.inr_desc_assoc,
      biprod.inl_map_assoc, biprod.inr_map_assoc, biprod.inl_desc, biprod.inr_desc]
  · exact inclusion_square (ordinaryFunctor R R) f.leftMap
  · exact inclusion_square (ordinaryFunctor R R) f.rightMap

def sumChainMap {P Q : TwoSubspaces.{w}} (f : P.Map Q) : sumQuotient R P ⟶ sumQuotient R Q :=
  cokernel.map _ _ (biprod.map ((ordinaryFunctor R R).map f.leftMap.restrict)
    ((ordinaryFunctor R R).map f.rightMap.restrict)) ((ordinaryFunctor R R).map f.map)
    (sumInclusion_square R f)

@[reassoc (attr := simp)] lemma sumProjection_map {P Q : TwoSubspaces.{w}} (f : P.Map Q) :
    sumProjection R P ≫ sumChainMap R f =
      (ordinaryFunctor R R).map f.map ≫ sumProjection R Q := cokernel.π_desc _ _ _

def sumCochainMap {P Q : TwoSubspaces.{w}} (f : P.Map Q) : sumCochains R Q ⟶ sumCochains R P :=
  (dualComplexFunctor R R (ComplexShape.down ℤ)).map (sumChainMap R f).op

lemma sumCochainMap_absolute {P Q : TwoSubspaces.{w}} (f : P.Map Q) :
    sumCochainMap R f ≫ sumToAbsolute R P =
      sumToAbsolute R Q ≫ (ordinaryCochainFunctor R R).map f.map.op := by
  change (dualComplexFunctor R R (ComplexShape.down ℤ)).map (sumChainMap R f).op ≫
      (dualComplexFunctor R R (ComplexShape.down ℤ)).map (sumProjection R P).op =
    (dualComplexFunctor R R (ComplexShape.down ℤ)).map (sumProjection R Q).op ≫
      (dualComplexFunctor R R (ComplexShape.down ℤ)).map ((ordinaryFunctor R R).map f.map).op
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, sumProjection_map]

lemma sumChainMap_union {P Q : TwoSubspaces.{w}} (f : P.Map Q) :
    sumChainMap R f ≫ sumToUnion R Q =
      sumToUnion R P ≫ relativeMap (ordinaryFunctor R R) f.unionMap := by
  apply (cancel_epi (sumProjection R P)).mp
  simp only [← Category.assoc, sumProjection_map]
  simp only [Category.assoc, sumToUnion, sumProjection, cokernel.π_desc, cokernel.π_desc_assoc]
  exact (projection_map (ordinaryFunctor R R) f.unionMap).symm

lemma unionComparison_natural {P Q : TwoSubspaces.{w}} (f : P.Map Q) :
    (relativeCochainFunctor R R).map f.unionMap.op ≫ unionComparison R P =
      unionComparison R Q ≫ sumCochainMap R f := by
  change (dualComplexFunctor R R (ComplexShape.down ℤ)).map
      (relativeMap (ordinaryFunctor R R) f.unionMap).op ≫
      (dualComplexFunctor R R (ComplexShape.down ℤ)).map (sumToUnion R P).op =
    (dualComplexFunctor R R (ComplexShape.down ℤ)).map (sumToUnion R Q).op ≫
      (dualComplexFunctor R R (ComplexShape.down ℤ)).map (sumChainMap R f).op
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, sumChainMap_union]

/-- Naturality of the cochain formula on actual relative cocycle representatives. -/
lemma relativeCocycleValue_pullback {P Q : Pair.{w}} (f : P ⟶ Q) (n : ℕ)
    (a : (relativeCochains R R Q).cycles (n : ℤ)) :
    relativeCocycleValue R P n
      (HomologicalComplex.cyclesMap ((relativeCochainFunctor R R).map f.op) (n : ℤ) a) =
      pullback R f.map n (relativeCocycleValue R Q n a) := by
  unfold relativeCocycleValue
  rw [← P202.CupProduct.ordinaryCochainsEquiv_pullback]
  congr 1
  have hc := congrArg (fun k => k a)
    (HomologicalComplex.cyclesMap_i ((relativeCochainFunctor R R).map f.op) (n : ℤ))
  have hs := congrArg (fun k => k.f (n : ℤ) ((relativeCochains R R Q).iCycles (n : ℤ) a))
    (cochainSequenceMap R R f).comm₁₂
  exact (congrArg ((relativeToAbsolute R R P).f (n : ℤ)) hc).trans hs

lemma sumCocycleValue_pullback {P Q : TwoSubspaces.{w}} (f : P.Map Q) (n : ℕ)
    (a : (sumCochains R Q).cycles (n : ℤ)) :
    sumCocycleValue R P n
      (HomologicalComplex.cyclesMap (sumCochainMap R f) (n : ℤ) a) =
      pullback R f.map n (sumCocycleValue R Q n a) := by
  unfold sumCocycleValue
  rw [← P202.CupProduct.ordinaryCochainsEquiv_pullback]
  congr 1
  have hc := congrArg (fun k => k a)
    (HomologicalComplex.cyclesMap_i (sumCochainMap R f) (n : ℤ))
  have hs := congrArg (fun k => k.f (n : ℤ) ((sumCochains R Q).iCycles (n : ℤ) a))
    (sumCochainMap_absolute R f)
  exact (congrArg ((sumToAbsolute R P).f (n : ℤ)) hc).trans hs

lemma relativePullback_class {P Q : Pair.{w}} (f : P ⟶ Q) (n : ℕ)
    (a : (relativeCochains R R Q).cycles (n : ℤ)) :
    relativePullback R f n (relativeClassMap R Q n a) = relativeClassMap R P n
      (HomologicalComplex.cyclesMap ((relativeCochainFunctor R R).map f.op) (n : ℤ) a) :=
  (congrArg (fun k => k a)
    (HomologicalComplex.homologyπ_naturality ((relativeCochainFunctor R R).map f.op) (n : ℤ)))

lemma sumHCup_natural {P Q : TwoSubspaces.{w}} (f : P.Map Q) (p q : ℕ)
    (a : HR R Q.leftPair p) (b : HR R Q.rightPair q) :
    homologyMap (sumCochainMap R f) ((p+q : ℕ) : ℤ) (sumHCup R Q p q a b) =
      sumHCup R P p q (relativePullback R f.leftMap p a) (relativePullback R f.rightMap q b) := by
  obtain ⟨a, rfl⟩ := relativeClassMap_surjective R Q.leftPair p a
  obtain ⟨b, rfl⟩ := relativeClassMap_surjective R Q.rightPair q b
  rw [sumHCup_rep, relativePullback_class, relativePullback_class, sumHCup_rep]
  have hπ := congrArg (fun k => k (relativeCycleCup R Q p q a b))
    (HomologicalComplex.homologyπ_naturality (sumCochainMap R f) ((p+q : ℕ) : ℤ))
  refine hπ.trans ?_
  change (sumCochains R P).homologyπ ((p+q : ℕ) : ℤ)
      (HomologicalComplex.cyclesMap (sumCochainMap R f) ((p+q : ℕ) : ℤ)
        (relativeCycleCup R Q p q a b)) = _
  congr 1
  apply sumCocycleValue_injective R P (p+q)
  rw [sumCocycleValue_pullback, relativeCycleCup_value, P202.CupProduct.cup_natural,
    relativeCycleCup_value, relativeCocycleValue_pullback, relativeCocycleValue_pullback]
  rfl

/-- Absolute compatibility of the intermediate product follows on representatives. -/
lemma sumHCup_absolute (P : TwoSubspaces.{w}) (p q : ℕ)
    (a : HR R P.leftPair p) (b : HR R P.rightPair q)
    (ordinaryRing : CohomologyRing R P.space) :
    homologyMap (sumToAbsolute R P) ((p+q : ℕ) : ℤ) (sumHCup R P p q a b) =
      ordinaryRing.product p q (forget R P.leftPair p a) (forget R P.rightPair q b) := by
  obtain ⟨a, rfl⟩ := relativeClassMap_surjective R P.leftPair p a
  obtain ⟨b, rfl⟩ := relativeClassMap_surjective R P.rightPair q b
  let a' := HomologicalComplex.cyclesMap (relativeToAbsolute R R P.leftPair) (p : ℤ) a
  let b' := HomologicalComplex.cyclesMap (relativeToAbsolute R R P.rightPair) (q : ℤ) b
  have hforget (T : Pair.{w}) (n : ℕ) (c : (relativeCochains R R T).cycles (n : ℤ)) :
      forget R T n (relativeClassMap R T n c) =
        (ordinaryCochains R R T.space).homologyπ (n : ℤ)
          (HomologicalComplex.cyclesMap (relativeToAbsolute R R T) (n : ℤ) c) :=
    (congrArg (fun k => k c) (HomologicalComplex.homologyπ_naturality
      (relativeToAbsolute R R T) (n : ℤ)))
  rw [hforget, hforget, sumHCup_rep]
  obtain ⟨c, hc, hprod⟩ := ordinaryRing.represents p q a' b'
  rw [hprod]
  have hπ := congrArg (fun k => k (relativeCycleCup R P p q a b))
    (HomologicalComplex.homologyπ_naturality (sumToAbsolute R P) ((p+q : ℕ) : ℤ))
  refine hπ.trans ?_
  change (ordinaryCochains R R P.space).homologyπ ((p+q : ℕ) : ℤ)
      (HomologicalComplex.cyclesMap (sumToAbsolute R P) ((p+q : ℕ) : ℤ)
        (relativeCycleCup R P p q a b)) = _
  congr 1
  apply P202.CupProduct.cocycleValue_injective R P.space (p+q)
  have hval : ∀ (T : Pair.{w}) (n : ℕ) (z : (relativeCochains R R T).cycles (n : ℤ)),
      cocycleValue R T.space n
        (HomologicalComplex.cyclesMap (relativeToAbsolute R R T) (n : ℤ) z) =
        relativeCocycleValue R T n z := by
    intro T n z
    exact congrArg (ordinaryCochainsEquiv R R T.space n)
      (congrArg (fun k => k z) (HomologicalComplex.cyclesMap_i (relativeToAbsolute R R T) (n : ℤ)))
  have hvsum : cocycleValue R P.space (p+q)
      (HomologicalComplex.cyclesMap (sumToAbsolute R P) ((p+q : ℕ) : ℤ)
        (relativeCycleCup R P p q a b)) =
      sumCocycleValue R P (p+q) (relativeCycleCup R P p q a b) := by
    exact congrArg (ordinaryCochainsEquiv R R P.space (p+q))
      (congrArg (fun k => k (relativeCycleCup R P p q a b))
        (HomologicalComplex.cyclesMap_i (sumToAbsolute R P) ((p+q : ℕ) : ℤ)))
  rw [hvsum, relativeCycleCup_value, hc]
  exact congrArg₂ (fun x y => cup R P.space p q x y) (hval P.leftPair p a).symm (hval P.rightPair q b).symm

/-- Transport through the canonical comparison, once it is proved invertible. -/
def cupProductOfComparison (hcmp : comparison_type.{u,w}) : NaturalRelativeCupProduct.{u,w} R := by
  let μ (P : TwoSubspaces.{w}) (h : P.IsOpen) (p q : ℕ) :
      HR R P.leftPair p ⊗[R] HR R P.rightPair q →ₗ[R] HR R P.unionPair (p+q) := by
    letI := hcmp R P h ((p+q : ℕ) : ℤ)
    exact (inv (homologyMap (unionComparison R P) ((p+q : ℕ) : ℤ))).hom.comp
      (TensorProduct.lift (sumHCup R P p q))
  have hμ (P : TwoSubspaces.{w}) (h : P.IsOpen) (p q : ℕ)
      (a : HR R P.leftPair p) (b : HR R P.rightPair q) :
      homologyMap (unionComparison R P) ((p+q : ℕ) : ℤ) (μ P h p q (a ⊗ₜ[R] b)) =
        sumHCup R P p q a b := by
    letI := hcmp R P h ((p+q : ℕ) : ℤ)
    change homologyMap (unionComparison R P) ((p+q : ℕ) : ℤ)
      (inv (homologyMap (unionComparison R P) ((p+q : ℕ) : ℤ))
        ((TensorProduct.lift (sumHCup R P p q)) (a ⊗ₜ[R] b))) = _
    rw [IsIso.inv_hom_id_apply, TensorProduct.lift.tmul]
  refine { product := μ, represents := ?_, naturality := ?_, absolute := ?_ }
  · intro P h p q a b
    exact ⟨relativeCycleCup R P p q a b, relativeCycleCup_value R P p q a b,
      (hμ P h p q _ _).trans (sumHCup_rep R P p q a b)⟩
  · intro P Q hP hQ f p q a b
    letI := hcmp R P hP ((p+q : ℕ) : ℤ)
    apply (ModuleCat.mono_iff_injective
      (homologyMap (unionComparison R P) ((p+q : ℕ) : ℤ))).mp inferInstance
    have hn : homologyMap ((relativeCochainFunctor R R).map f.unionMap.op) ((p+q : ℕ) : ℤ) ≫
        homologyMap (unionComparison R P) ((p+q : ℕ) : ℤ) =
      homologyMap (unionComparison R Q) ((p+q : ℕ) : ℤ) ≫
        homologyMap (sumCochainMap R f) ((p+q : ℕ) : ℤ) := by
      rw [← homologyMap_comp, ← homologyMap_comp, unionComparison_natural]
    have hn' := congrArg (fun k => k (μ Q hQ p q (a ⊗ₜ[R] b))) hn
    change homologyMap (unionComparison R P) ((p+q : ℕ) : ℤ)
      (relativePullback R f.unionMap (p+q) (μ Q hQ p q (a ⊗ₜ[R] b))) =
      homologyMap (sumCochainMap R f) ((p+q : ℕ) : ℤ)
        (homologyMap (unionComparison R Q) ((p+q : ℕ) : ℤ)
          (μ Q hQ p q (a ⊗ₜ[R] b))) at hn'
    rw [hn', hμ Q hQ p q, hμ P hP p q]
    exact sumHCup_natural R f p q a b
  · intro P h p q a b ordinaryRing
    have ha : homologyMap (unionComparison R P) ((p+q : ℕ) : ℤ) ≫
        homologyMap (sumToAbsolute R P) ((p+q : ℕ) : ℤ) =
      homologyMap (relativeToAbsolute R R P.unionPair) ((p+q : ℕ) : ℤ) := by
      rw [← homologyMap_comp, comparison_absolute]
    have ha' := congrArg (fun k => k (μ P h p q (a ⊗ₜ[R] b))) ha
    change homologyMap (sumToAbsolute R P) ((p+q : ℕ) : ℤ)
      (homologyMap (unionComparison R P) ((p+q : ℕ) : ℤ) (μ P h p q (a ⊗ₜ[R] b))) =
      forget R P.unionPair (p+q) (μ P h p q (a ⊗ₜ[R] b)) at ha'
    rw [← ha', hμ P h p q]
    exact sumHCup_absolute R P p q a b ordinaryRing

/-- The singular basis in ordinary integer grading. -/
def ordinaryChainBasis (X : TopCat.{w}) (n : ℕ) :
    Module.Basis (Simplex X n) R ((ordinaryComplex R R X).X (n : ℤ)) :=
  Finsupp.basisSingleOne.map (ordinaryNonnegativeIso R R X n).symm.toLinearEquiv

lemma ordinaryChainBasis_map (P : Pair.{w}) (n : ℕ) (s : Simplex P.sub n) :
    (inclusion (ordinaryFunctor R R) P).f (n : ℤ) (ordinaryChainBasis R P.sub n s) =
      ordinaryChainBasis R P.space n ((TopCat.toSSet.map P.inclusion).app (op ⦋n⦌) s) := by
  change ((extendMap (chainMap R R P.inclusion) (degreeEmbedding 0)).f (n : ℤ)) _ = _
  rw [extendMap_f _ _ (by change (0 : ℤ) + n = n; omega)]
  change (ordinaryNonnegativeIso R R P.space n).inv
    ((chainMap R R P.inclusion).f n
      ((ordinaryNonnegativeIso R R P.sub n).hom
        ((ordinaryNonnegativeIso R R P.sub n).inv (Finsupp.single s 1)))) = _
  rw [Iso.inv_hom_id_apply]
  change (ordinaryNonnegativeIso R R P.space n).inv (Finsupp.mapDomain _ (Finsupp.single s 1)) = _
  rw [Finsupp.mapDomain_single]
  rfl

-- An explicit product basis handles the biproduct in each chain degree.
def sumDomainIso (P : TwoSubspaces.{w}) (n : ℤ) :
    (((ordinaryComplex R R P.leftPair.sub) ⊞ (ordinaryComplex R R P.rightPair.sub)).X n) ≅
      ModuleCat.of R (((ordinaryComplex R R P.leftPair.sub).X n) ×
        ((ordinaryComplex R R P.rightPair.sub).X n)) :=
  biprodXIso _ _ n ≪≫ ModuleCat.biprodIsoProd _ _

def sumDomainBasis (P : TwoSubspaces.{w}) (n : ℕ) :
    Module.Basis (Simplex P.leftPair.sub n ⊕ Simplex P.rightPair.sub n) R
      (((ordinaryComplex R R P.leftPair.sub) ⊞ (ordinaryComplex R R P.rightPair.sub)).X (n : ℤ)) :=
  ((ordinaryChainBasis R P.leftPair.sub n).prod (ordinaryChainBasis R P.rightPair.sub n)).map
    (sumDomainIso R P (n : ℤ)).symm.toLinearEquiv

lemma sumDomainIso_inl (P : TwoSubspaces.{w}) (n : ℤ) :
    ModuleCat.ofHom (LinearMap.inl R ((ordinaryComplex R R P.leftPair.sub).X n)
      ((ordinaryComplex R R P.rightPair.sub).X n)) ≫ (sumDomainIso R P n).inv =
      (biprod.inl : ordinaryComplex R R P.leftPair.sub ⟶ _).f n := by
  have h : ModuleCat.ofHom (LinearMap.inl R ((ordinaryComplex R R P.leftPair.sub).X n)
      ((ordinaryComplex R R P.rightPair.sub).X n)) ≫
      (ModuleCat.biprodIsoProd _ _).inv = biprod.inl := by
    apply biprod.hom_ext <;> simp <;> rfl
  simp only [sumDomainIso, Iso.trans_inv, ← Category.assoc, h]
  exact HomologicalComplex.inl_biprodXIso_inv (ordinaryComplex R R P.leftPair.sub)
    (ordinaryComplex R R P.rightPair.sub) n

lemma sumDomainIso_inr (P : TwoSubspaces.{w}) (n : ℤ) :
    ModuleCat.ofHom (LinearMap.inr R ((ordinaryComplex R R P.leftPair.sub).X n)
      ((ordinaryComplex R R P.rightPair.sub).X n)) ≫ (sumDomainIso R P n).inv =
      (biprod.inr : ordinaryComplex R R P.rightPair.sub ⟶ _).f n := by
  have h : ModuleCat.ofHom (LinearMap.inr R ((ordinaryComplex R R P.leftPair.sub).X n)
      ((ordinaryComplex R R P.rightPair.sub).X n)) ≫
      (ModuleCat.biprodIsoProd _ _).inv = biprod.inr := by
    apply biprod.hom_ext <;> simp <;> rfl
  simp only [sumDomainIso, Iso.trans_inv, ← Category.assoc, h]
  exact HomologicalComplex.inr_biprodXIso_inv (ordinaryComplex R R P.leftPair.sub)
    (ordinaryComplex R R P.rightPair.sub) n

lemma sumDomainBasis_left (P : TwoSubspaces.{w}) (n : ℕ) (s : Simplex P.leftPair.sub n) :
    sumDomainBasis R P n (.inl s) =
      (biprod.inl : ordinaryComplex R R P.leftPair.sub ⟶ _).f (n : ℤ)
        (ordinaryChainBasis R P.leftPair.sub n s) := by
  change (sumDomainIso R P (n : ℤ)).inv
    (((ordinaryChainBasis R P.leftPair.sub n).prod (ordinaryChainBasis R P.rightPair.sub n)) _) = _
  rw [Module.Basis.prod_apply]
  exact congrArg (fun k => k (ordinaryChainBasis R P.leftPair.sub n s))
    (sumDomainIso_inl R P (n : ℤ))

lemma sumDomainBasis_right (P : TwoSubspaces.{w}) (n : ℕ) (s : Simplex P.rightPair.sub n) :
    sumDomainBasis R P n (.inr s) =
      (biprod.inr : ordinaryComplex R R P.rightPair.sub ⟶ _).f (n : ℤ)
        (ordinaryChainBasis R P.rightPair.sub n s) := by
  change (sumDomainIso R P (n : ℤ)).inv
    (((ordinaryChainBasis R P.leftPair.sub n).prod (ordinaryChainBasis R P.rightPair.sub n)) _) = _
  rw [Module.Basis.prod_apply]
  exact congrArg (fun k => k (ordinaryChainBasis R P.rightPair.sub n s))
    (sumDomainIso_inr R P (n : ℤ))

/-- Killing the two subspace basis images leaves a projective cokernel. -/
instance sumQuotient_projective_nonnegative (P : TwoSubspaces.{w}) (n : ℕ) :
    Projective ((sumQuotient R P).X (n : ℤ)) := by
  have hp := P202.SmallChainEquivalence.projective_cokernel_of_basis
    (sumDomainBasis R P n) (ordinaryChainBasis R P.space n)
    ((sumInclusion R P).f (n : ℤ))
    (Sum.elim ((TopCat.toSSet.map P.leftPair.inclusion).app (op ⦋n⦌))
      ((TopCat.toSSet.map P.rightPair.inclusion).app (op ⦋n⦌))) (by
        intro s
        cases s with
        | inl s =>
          rw [sumDomainBasis_left]
          change ((biprod.inl : ordinaryComplex R R P.leftPair.sub ⟶ _).f (n : ℤ) ≫
            (sumInclusion R P).f (n : ℤ)) _ = _
          rw [← comp_f, sumInclusion, biprod.inl_desc]
          exact ordinaryChainBasis_map R P.leftPair n s
        | inr s =>
          rw [sumDomainBasis_right]
          change ((biprod.inr : ordinaryComplex R R P.rightPair.sub ⟶ _).f (n : ℤ) ≫
            (sumInclusion R P).f (n : ℤ)) _ = _
          rw [← comp_f, sumInclusion, biprod.inr_desc]
          exact ordinaryChainBasis_map R P.rightPair n s)
  exact Projective.of_iso
    (PreservesCokernel.iso (HomologicalComplex.eval (ModuleCat R) _ (n : ℤ))
      (sumInclusion R P)).symm hp

lemma sumQuotient_negative (P : TwoSubspaces.{w}) (n : ℤ) (hn : n < 0) :
    IsZero ((sumQuotient R P).X n) := by
  have h := P202.SingularChains.ordinary_negative_chains R R P.space n hn
  have : Epi ((sumInclusion R P).f n) := h.epi _
  letI : Epi ((HomologicalComplex.eval (ModuleCat R) _ n).map (sumInclusion R P)) := this
  exact (isZero_cokernel_of_epi _).of_iso
    (PreservesCokernel.iso (HomologicalComplex.eval (ModuleCat R) _ n) (sumInclusion R P))

instance sumQuotient_projective (P : TwoSubspaces.{w}) (n : ℤ) :
    Projective ((sumQuotient R P).X n) := by
  by_cases h : 0 ≤ n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    exact sumQuotient_projective_nonnegative R P m
  · exact (sumQuotient_negative R P n (by omega)).projective

/-- Duality preserves a quasi-isomorphism of bounded-below projective complexes. -/
lemma dual_quasiIso_of_projective
    (C D : ChainComplex (ModuleCat.{max u w} R) ℤ)
    [∀ n, Projective (C.X n)] [∀ n, Projective (D.X n)]
    (hC : ∀ n : ℤ, n < 0 → IsZero (C.X n))
    (hD : ∀ n : ℤ, n < 0 → IsZero (D.X n))
    (f : C ⟶ D) [QuasiIso f] :
    QuasiIso ((dualComplexFunctor R R (ComplexShape.down ℤ)).map f.op) := by
  have hCi : CochainComplex.IsStrictlyGE C.op 0 := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    exact (hC n hn).op
  have hDi : CochainComplex.IsStrictlyGE D.op 0 := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    exact (hD n hn).op
  have (n : ℤ) : Injective (C.op.X n) := by
    change Injective (op (C.X n))
    infer_instance
  have (n : ℤ) : Injective (D.op.X n) := by
    change Injective (op (D.X n))
    infer_instance
  have := CochainComplex.isKInjective_of_injective C.op 0
  have := CochainComplex.isKInjective_of_injective D.op 0
  let fo : D.op ⟶ C.op := (opFunctor (ModuleCat.{max u w} R) (.down ℤ)).map f.op
  have : QuasiIso fo := inferInstance
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff fo).mp inferInstance
  let ed := (dualFunctor R R).mapHomotopyEquiv e
  have hd : QuasiIso (((dualFunctor R R).mapHomologicalComplex (.up ℤ)).map fo) := by
    rw [← he]
    exact ed.quasiIso_hom
  exact hd

lemma ordinary_relative_projective (P : Pair.{w}) (n : ℤ) :
    Projective ((ordinary R R P).X n) := by
  by_cases hn : n < 0
  · exact ((P202.RelativeSingularChains.ordinary_negative R R P n hn).1).projective
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ n)
    obtain ⟨b, _⟩ := P202.RelativeSingularChains.quotient_basis R P n
    exact Projective.of_iso (ordinaryDegreeIso R R P n).symm
      (ModuleCat.projective_of_free b)


lemma unionComparison_quasiIso_of_chain (P : TwoSubspaces.{w})
    [QuasiIso (sumToUnion R P)] : QuasiIso (unionComparison R P) := by
  letI (n : ℤ) := ordinary_relative_projective R P.unionPair n
  exact dual_quasiIso_of_projective R (sumQuotient R P) (ordinary R R P.unionPair)
    (sumQuotient_negative R P)
    (fun n hn => (P202.RelativeSingularChains.ordinary_negative R R P.unionPair n hn).1)
    (sumToUnion R P)


open P202Specs.SmallChainHomology P202.SmallChainEquivalence

lemma range_cokernel_condition {ι : Type*} {c : ComplexShape ι}
    {A B X : HomologicalComplex (ModuleCat.{w} R) c}
    (f : A ⟶ X) (g : B ⟶ X)
    (h : ∀ n, (f.f n).hom.range ≤ (g.f n).hom.range) :
    f ≫ cokernel.π g = 0 := by
  ext n a
  obtain ⟨b, hb⟩ := h n ⟨a, rfl⟩
  change (cokernel.π g).f n (f.f n a) = 0
  rw [← hb]
  exact congrArg (fun k => k.f n b) (cokernel.condition g)

lemma shortExact_of_equal_range {ι : Type*} {c : ComplexShape ι}
    {A B X : HomologicalComplex (ModuleCat.{w} R) c}
    (f : A ⟶ X) (g : B ⟶ X) [Mono f]
    (h : ∀ n, (f.f n).hom.range = (g.f n).hom.range) :
    (ShortComplex.mk f (cokernel.π g)
      (range_cokernel_condition R f g (fun n => (h n).le))).ShortExact := by
  refine { mono_f := inferInstance, epi_g := inferInstance, exact := ?_ }
  apply HomologicalComplex.exact_of_degreewise_exact
  intro n
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
  change (f.f n).hom.range = ((cokernel.π g).f n).hom.ker
  rw [h n]
  exact ((ShortComplex.cokernelSequence_exact g).map
    (HomologicalComplex.eval (ModuleCat R) c n)).moduleCat_range_eq_ker

lemma range_biprod_desc_f {ι : Type*} {c : ComplexShape ι}
    {A B X : HomologicalComplex (ModuleCat.{w} R) c}
    (f : A ⟶ X) (g : B ⟶ X) (n : ι) :
    ((biprod.desc f g).f n).hom.range = (f.f n).hom.range ⊔ (g.f n).hom.range := by
  apply le_antisymm
  · rintro x ⟨a, rfl⟩
    rw [biprod.desc_eq]
    change f.f n ((biprod.fst : A ⊞ B ⟶ A).f n a) +
      g.f n ((biprod.snd : A ⊞ B ⟶ B).f n a) ∈ _
    exact Submodule.add_mem _ (Submodule.mem_sup_left ⟨_, rfl⟩) (Submodule.mem_sup_right ⟨_, rfl⟩)
  · apply sup_le
    · rintro x ⟨a, rfl⟩
      refine ⟨(biprod.inl : A ⟶ A ⊞ B).f n a, ?_⟩
      exact congrArg (fun k : A ⟶ X => k.f n a) (biprod.inl_desc f g)
    · rintro x ⟨a, rfl⟩
      refine ⟨(biprod.inr : B ⟶ A ⊞ B).f n a, ?_⟩
      exact congrArg (fun k : B ⟶ X => k.f n a) (biprod.inr_desc f g)

lemma range_biprod_desc_post_f {ι : Type*} {c : ComplexShape ι}
    {A B X : HomologicalComplex (ModuleCat.{w} R) c}
    (f : A ⟶ X) (g : B ⟶ X) (n : ι) {Y : ModuleCat.{w} R}
    (k : X.X n ⟶ Y) :
    (((biprod.desc f g).f n) ≫ k).hom.range =
      ((f.f n) ≫ k).hom.range ⊔ ((g.f n) ≫ k).hom.range := by
  change (k.hom.comp ((biprod.desc f g).f n).hom).range = _
  rw [LinearMap.range_comp, range_biprod_desc_f, Submodule.map_sup]
  simp only [ModuleCat.hom_comp, ← LinearMap.range_comp]

lemma ordinary_inclusion_post_range (P : P202Specs.RelativeSingularChains.Pair.{w}) (n : ℕ) :
    (((inclusion (ordinaryFunctor R R) P).f (n : ℤ)) ≫
      (ordinaryNonnegativeIso R R P.space n).hom).hom.range =
      ((chainMap R R P.inclusion).f n).hom.range := by
  rw [ordinary_inclusion_degree]
  change (((chainMap R R P.inclusion).f n).hom.comp
    (ordinaryNonnegativeIso R R P.sub n).hom.hom).range = _
  exact LinearMap.range_comp_of_range_eq_top _
    (ordinaryNonnegativeIso R R P.sub n).toLinearEquiv.range

lemma sumInclusion_post_range (P : TwoSubspaces.{w}) (n : ℕ) :
    (((sumInclusion R P).f (n : ℤ)) ≫
      (ordinaryNonnegativeIso R R P.space n).hom).hom.range = sumChains R P n := by
  rw [sumInclusion, range_biprod_desc_post_f, ordinary_inclusion_post_range,
    ordinary_inclusion_post_range]
  rfl

def unionCover (P : TwoSubspaces.{w}) (hP : P.IsOpen) : OpenCover P.unionPair.sub Bool where
  sets i := match i with
    | false => Subtype.val ⁻¹' P.left
    | true => Subtype.val ⁻¹' P.right
  isOpen i := by
    cases i
    · exact hP.1.preimage continuous_subtype_val
    · exact hP.2.preimage continuous_subtype_val
  covers x := by
    rcases x.property with hx | hx
    · exact ⟨false, hx⟩
    · exact ⟨true, hx⟩

abbrev sumSmallInclusion (P : TwoSubspaces.{w}) (hP : P.IsOpen) :
    smallComplex R (unionCover P hP) ⟶ complex R R P.space :=
  smallInclusion R (unionCover P hP) ≫ chainMap R R P.unionPair.inclusion

instance sumSmallInclusion_mono (P : TwoSubspaces.{w}) (hP : P.IsOpen) :
    Mono (sumSmallInclusion R P hP) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  apply (ModuleCat.mono_iff_injective _).mpr
  intro c d h
  apply Subtype.ext
  exact P202.RelativeSingularChains.inclusion_injective R R P.unionPair n h

lemma smallSimplex_image_iff (P : TwoSubspaces.{w}) (hP : P.IsOpen) (n : ℕ)
    (s : Simplex P.space n) :
    s ∈ Set.range (fun t : SmallSimplex (unionCover P hP) n =>
      (TopCat.toSSet.map P.unionPair.inclusion).app (op ⦋n⦌) t.val) ↔
        InSubspace P.leftPair n s ∨ InSubspace P.rightPair n s := by
  constructor
  · rintro ⟨⟨t, ht⟩, rfl⟩
    obtain ⟨i, hi⟩ := ht
    cases i
    · left
      intro x
      exact hi ⟨x, rfl⟩
    · right
      intro x
      exact hi ⟨x, rfl⟩
  · intro hs
    have hW : InSubspace P.unionPair n s := by
      intro x
      exact hs.elim (fun h => Or.inl (h x)) (fun h => Or.inr (h x))
    obtain ⟨t, ht⟩ := (P202.RelativeSingularChains.simplex_image P.unionPair n s).mpr hW
    refine ⟨⟨t, ?_⟩, ht⟩
    rcases hs with hs | hs
    · refine ⟨false, ?_⟩
      rintro y ⟨x, rfl⟩
      have h := hs x
      rw [← ht] at h
      exact h
    · refine ⟨true, ?_⟩
      rintro y ⟨x, rfl⟩
      have h := hs x
      rw [← ht] at h
      exact h

lemma sumSmallInclusion_basis (P : TwoSubspaces.{w}) (hP : P.IsOpen) (n : ℕ)
    (s : SmallSimplex (unionCover P hP) n) :
    (sumSmallInclusion R P hP).f n (smallBasis R (unionCover P hP) n s) =
      Finsupp.single ((TopCat.toSSet.map P.unionPair.inclusion).app (op ⦋n⦌) s.val) 1 := by
  change Finsupp.mapDomain _ (smallBasis R (unionCover P hP) n s).val = _
  rw [smallBasis_coe]
  exact Finsupp.mapDomain_single

lemma sumSmallInclusion_range (P : TwoSubspaces.{w}) (hP : P.IsOpen) (n : ℕ) :
    ((sumSmallInclusion R P hP).f n).hom.range = sumChains R P n := by
  classical
  let b := smallBasis R (unionCover P hP) n
  let f := ((sumSmallInclusion R P hP).f n).hom
  have hf : f.range = Submodule.span R (Set.range (fun s => f (b s))) := by
    rw [LinearMap.range_eq_map, ← b.span_eq, Submodule.map_span]
    congr 1
    exact (Set.range_comp' _ _).symm
  rw [hf]
  change Submodule.span R (Set.range (fun s => (sumSmallInclusion R P hP).f n
    (smallBasis R (unionCover P hP) n s))) = _
  simp_rw [sumSmallInclusion_basis]
  change _ = (Finsupp.lmapDomain R R ((TopCat.toSSet.map P.leftPair.inclusion).app (op ⦋n⦌))).range ⊔
    (Finsupp.lmapDomain R R ((TopCat.toSSet.map P.rightPair.inclusion).app (op ⦋n⦌))).range
  rw [Finsupp.range_lmapDomain, Finsupp.range_lmapDomain, ← Submodule.span_union]
  congr 1
  ext c
  constructor
  · rintro ⟨s, rfl⟩
    have hs := (smallSimplex_image_iff P hP n _).mp ⟨s, rfl⟩
    rcases hs with hs | hs
    · obtain ⟨t, ht⟩ := (P202.RelativeSingularChains.simplex_image P.leftPair n _).mpr hs
      exact Or.inl ⟨t, congrArg (fun s => Finsupp.single s (1 : R)) ht⟩
    · obtain ⟨t, ht⟩ := (P202.RelativeSingularChains.simplex_image P.rightPair n _).mpr hs
      exact Or.inr ⟨t, congrArg (fun s => Finsupp.single s (1 : R)) ht⟩
  · rintro (⟨s, rfl⟩ | ⟨s, rfl⟩)
    · have hs := (P202.RelativeSingularChains.simplex_image P.leftPair n _).mp ⟨s, rfl⟩
      obtain ⟨t, ht⟩ := (smallSimplex_image_iff P hP n _).mpr (Or.inl hs)
      exact ⟨t, congrArg (fun s => Finsupp.single s (1 : R)) ht⟩
    · have hs := (P202.RelativeSingularChains.simplex_image P.rightPair n _).mp ⟨s, rfl⟩
      obtain ⟨t, ht⟩ := (smallSimplex_image_iff P hP n _).mpr (Or.inr hs)
      exact ⟨t, congrArg (fun s => Finsupp.single s (1 : R)) ht⟩

/-- Extension by zero puts the small union chains in the ordinary integer grading. -/
abbrev sumSmallInt (P : TwoSubspaces.{w}) (hP : P.IsOpen) :
    (smallComplex R (unionCover P hP)).extend (degreeEmbedding 0) ⟶
      ordinaryComplex R R P.space :=
  HomologicalComplex.extendMap (sumSmallInclusion R P hP) (degreeEmbedding 0)

lemma sumSmallInt_range (P : TwoSubspaces.{w}) (hP : P.IsOpen) (n : ℕ) :
    (((sumSmallInt R P hP).f (n : ℤ)) ≫
      (ordinaryNonnegativeIso R R P.space n).hom).hom.range = sumChains R P n := by
  rw [sumSmallInt, HomologicalComplex.extendMap_f _ _
    (show (degreeEmbedding 0).f n = (n : ℤ) by change (0 : ℤ) + n = n; omega)]
  change ((_ ≫ (sumSmallInclusion R P hP).f n ≫
    (ordinaryNonnegativeIso R R P.space n).inv) ≫
      (ordinaryNonnegativeIso R R P.space n).hom).hom.range = _
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hs : Function.Surjective
      ((smallComplex R (unionCover P hP)).extendXIso (degreeEmbedding 0)
        (show (degreeEmbedding 0).f n = (n : ℤ) by change (0 : ℤ) + n = n; omega)).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  rw [ModuleCat.hom_comp, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr hs)]
  exact sumSmallInclusion_range R P hP n

lemma sumSmallInt_negative (P : TwoSubspaces.{w}) (hP : P.IsOpen)
    (z : ℤ) (hz : z < 0) :
    IsZero (((smallComplex R (unionCover P hP)).extend (degreeEmbedding 0)).X z) := by
  apply HomologicalComplex.isZero_extend_X
  intro n
  change (0 : ℤ) + (n : ℤ) ≠ z
  omega

instance sumSmallInt_mono (P : TwoSubspaces.{w}) (hP : P.IsOpen) :
    Mono (sumSmallInt R P hP) :=
  P202.RelativeSingularChains.extend_mono (sumSmallInclusion R P hP) (degreeEmbedding 0)

/-- The small-chain comparison on the union, in ordinary integer grading. -/
abbrev smallIntToUnion (P : TwoSubspaces.{w}) (hP : P.IsOpen) :
    (smallComplex R (unionCover P hP)).extend (degreeEmbedding 0) ⟶
      ordinaryComplex R R P.unionPair.sub :=
  HomologicalComplex.extendMap (smallInclusion R (unionCover P hP)) (degreeEmbedding 0)

instance smallIntToUnion_quasiIso (P : TwoSubspaces.{w}) (hP : P.IsOpen) :
    QuasiIso (smallIntToUnion R P hP) := by
  have h : QuasiIso (smallInclusion R (unionCover P hP)) := by
    rw [quasiIso_iff]
    intro n
    apply (quasiIsoAt_iff_isIso_homologyMap _ n).mpr
    exact P202.SmallChainHomology.absoluteComparison R P.unionPair.sub Bool (unionCover P hP) n
  exact inferInstanceAs (QuasiIso (HomologicalComplex.extendMap
    (smallInclusion R (unionCover P hP)) (degreeEmbedding 0)))

lemma smallIntToUnion_factor (P : TwoSubspaces.{w}) (hP : P.IsOpen) :
    smallIntToUnion R P hP ≫ inclusion (ordinaryFunctor R R) P.unionPair =
      sumSmallInt R P hP := by
  exact (HomologicalComplex.extendMap_comp _ _ (degreeEmbedding 0)).symm


lemma range_eq_of_post_iso {A B X Y : ModuleCat.{w} R}
    (f : A ⟶ X) (g : B ⟶ X) (e : X ≅ Y)
    (h : (f ≫ e.hom).hom.range = (g ≫ e.hom).hom.range) :
    f.hom.range = g.hom.range := by
  apply le_antisymm
  · rintro x ⟨a, rfl⟩
    have hx : (f ≫ e.hom) a ∈ (g ≫ e.hom).hom.range := by
      rw [← h]
      exact ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := hx
    exact ⟨b, e.toLinearEquiv.injective hb⟩
  · rintro x ⟨a, rfl⟩
    have hx : (g ≫ e.hom) a ∈ (f ≫ e.hom).hom.range := by
      rw [h]
      exact ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := hx
    exact ⟨b, e.toLinearEquiv.injective hb⟩

lemma sumSmallInt_sum_range (P : TwoSubspaces.{w}) (hP : P.IsOpen) (z : ℤ) :
    ((sumSmallInt R P hP).f z).hom.range = ((sumInclusion R P).f z).hom.range := by
  by_cases hz : 0 ≤ z
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz
    apply range_eq_of_post_iso R _ _ (ordinaryNonnegativeIso R R P.space n)
    rw [sumSmallInt_range, sumInclusion_post_range]
  · have hX := P202.SingularChains.ordinary_negative_chains R R P.space z (by omega)
    rw [hX.eq_of_tgt ((sumSmallInt R P hP).f z) 0,
      hX.eq_of_tgt ((sumInclusion R P).f z) 0]
    simp only [ModuleCat.hom_zero, LinearMap.range_zero]

/-- The canonical quotient comparison is a quasi-isomorphism for open U and V. -/
theorem sumToUnion_quasiIso (P : TwoSubspaces.{w}) (hP : P.IsOpen) :
    QuasiIso (sumToUnion R P) := by
  let S := ShortComplex.mk (sumSmallInt R P hP) (sumProjection R P)
    (range_cokernel_condition R (sumSmallInt R P hP) (sumInclusion R P)
      (fun n => (sumSmallInt_sum_range R P hP n).le))
  have hS : S.ShortExact := shortExact_of_equal_range R
    (sumSmallInt R P hP) (sumInclusion R P) (sumSmallInt_sum_range R P hP)
  have hT : (sequence (ordinaryFunctor R R) P.unionPair).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact _,
      mono_f := (by change Mono (inclusion (ordinaryFunctor R R) P.unionPair); infer_instance),
      epi_g := inferInstance }
  let φ : S ⟶ sequence (ordinaryFunctor R R) P.unionPair :=
    ShortComplex.Hom.mk (smallIntToUnion R P hP) (𝟙 _) (sumToUnion R P)
      (by simpa [S] using smallIntToUnion_factor R P hP)
      (by simpa [S, sumToUnion] using (cokernel.π_desc (sumInclusion R P)
        (projection (ordinaryFunctor R R) P.unionPair) _).symm)
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ φ hS hT
    (inferInstanceAs (QuasiIso (smallIntToUnion R P hP))) (inferInstanceAs (QuasiIso (𝟙 _)))


/-- The canonical comparison is invertible on cohomology for the open pair. -/
theorem comparison : comparison_type.{u,w} := by
  intro R _ P hP n
  letI := sumToUnion_quasiIso R P hP
  letI := unionComparison_quasiIso_of_chain R P
  infer_instance

/-- The natural bilinear relative cup product, with its front/back formula. -/
theorem product : product_type.{u,w} := by
  intro R _
  exact ⟨cupProductOfComparison R comparison⟩

/-- The individual-pair LES has no openness restriction. -/
theorem pairLongExact : pairLongExact_type.{u,w} := by
  intro R _
  exact P202.CohomologyPairs.long_exact R R

end P202.RelativeCupProduct
