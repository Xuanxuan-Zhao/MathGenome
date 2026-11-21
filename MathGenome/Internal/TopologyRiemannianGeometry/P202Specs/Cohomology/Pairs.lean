import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.PrismHomotopy
import Mathlib.Algebra.Homology.Opposite

/-! Algebraic (unrestricted) cochains, paper.tex 1740–1750 and 1775–1794.
All pairs are arbitrary subspaces. The coefficient module need not be injective.
Integer grading uses the ordinary, not augmented, singular chains. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
namespace P202Specs.CohomologyPairs
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.ChainLES
universe u v w t
variable (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]

/-- Algebraic dual with values in the given module, in any universe. -/
abbrev dualFunctor : (ModuleCat.{t} R)ᵒᵖ ⥤ ModuleCat.{max t v} R where
  obj V := ModuleCat.of R (V.unop →ₗ[R] A)
  map f := ModuleCat.ofHom (LinearMap.lcomp R A f.unop.hom)
  map_id V := by ext a x; rfl
  map_comp f g := by ext a x; rfl

instance : (dualFunctor.{u,v,t} R A).Additive where
  map_add := by
    intros
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    ext x
    exact a.map_add _ _

/-- Reversing arrows reverses the shape; the differential is precomposition,
with no extra sign. -/
abbrev dualComplexFunctor (c : ComplexShape t) :
    (HomologicalComplex (ModuleCat.{w} R) c)ᵒᵖ ⥤
      HomologicalComplex (ModuleCat.{max w v} R) c.symm :=
  HomologicalComplex.opFunctor _ c ⋙ (dualFunctor R A).mapHomologicalComplex c.symm

abbrev ordinaryCochainFunctor : TopCat.{w}ᵒᵖ ⥤
    CochainComplex (ModuleCat.{max u v w} R) ℤ :=
  (ordinaryFunctor R R).op ⋙ dualComplexFunctor R A (ComplexShape.down ℤ)

abbrev relativeCochainFunctor : Pair.{w}ᵒᵖ ⥤
    CochainComplex (ModuleCat.{max u v w} R) ℤ :=
  (relativeFunctor (ordinaryFunctor R R)).op ⋙ dualComplexFunctor R A (ComplexShape.down ℤ)

abbrev ordinaryCochains (X : TopCat.{w}) := (ordinaryCochainFunctor R A).obj (op X)
abbrev relativeCochains (P : Pair.{w}) := (relativeCochainFunctor R A).obj (op P)
abbrev ordinaryCohomology (X : TopCat.{w}) (q : ℤ) := (ordinaryCochains R A X).homology q
abbrev relativeCohomology (P : Pair.{w}) (q : ℤ) := (relativeCochains R A P).homology q

abbrev ordinaryCohomologyFunctor (q : ℤ) :=
  ordinaryCochainFunctor R A ⋙ HomologicalComplex.homologyFunctor _ _ q
abbrev relativeCohomologyFunctor (q : ℤ) :=
  relativeCochainFunctor R A ⋙ HomologicalComplex.homologyFunctor _ _ q

/-- In natural degrees, the literal Hom of the module quotient. -/
abbrev quotientCochains (P : Pair.{w}) (q : ℕ) := chainQuotient R R P q →ₗ[R] A

/-- A cochain vanishes on the subspace when it annihilates every subspace chain. -/
def vanishingCochains (P : Pair.{w}) (q : ℕ) : Submodule R (Chains R P.space q →ₗ[R] A) :=
  LinearMap.ker (LinearMap.lcomp R A ((chainMap R R P.inclusion).f q).hom)

abbrev relativeToAbsolute (P : Pair.{w}) : relativeCochains R A P ⟶ ordinaryCochains R A P.space :=
  (dualComplexFunctor R A (ComplexShape.down ℤ)).map (projection (ordinaryFunctor R R) P).op

abbrev restriction (P : Pair.{w}) : ordinaryCochains R A P.space ⟶ ordinaryCochains R A P.sub :=
  (dualComplexFunctor R A (ComplexShape.down ℤ)).map (inclusion (ordinaryFunctor R R) P).op

def cochainSequence (P : Pair.{w}) :
    ShortComplex (CochainComplex (ModuleCat.{max u v w} R) ℤ) :=
  ShortComplex.mk (relativeToAbsolute R A P) (restriction R A P) (by
    dsimp only [relativeToAbsolute, restriction]
    rw [← Functor.map_comp, ← op_comp]
    change (dualComplexFunctor R A (ComplexShape.down ℤ)).map
      ((sequence (ordinaryFunctor R R) P).f ≫ (sequence (ordinaryFunctor R R) P).g).op = 0
    rw [ShortComplex.zero, op_zero, Functor.map_zero])

/-- Pullback is a morphism of the three-term cochain sequences. -/
def cochainSequenceMap {P Q : Pair.{w}} (f : P ⟶ Q) :
    cochainSequence R A Q ⟶ cochainSequence R A P :=
  ShortComplex.Hom.mk ((relativeCochainFunctor R A).map f.op)
    ((ordinaryCochainFunctor R A).map f.map.op)
    ((ordinaryCochainFunctor R A).map f.restrict.op)
    (by
      change (dualComplexFunctor R A (ComplexShape.down ℤ)).map
          (relativeMap (ordinaryFunctor R R) f).op ≫
        (dualComplexFunctor R A (ComplexShape.down ℤ)).map (projection (ordinaryFunctor R R) P).op =
        (dualComplexFunctor R A (ComplexShape.down ℤ)).map (projection (ordinaryFunctor R R) Q).op ≫
        (dualComplexFunctor R A (ComplexShape.down ℤ)).map ((ordinaryFunctor R R).map f.map).op
      rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, projection_map])
    (by
      change (dualComplexFunctor R A (ComplexShape.down ℤ)).map ((ordinaryFunctor R R).map f.map).op ≫
        (dualComplexFunctor R A (ComplexShape.down ℤ)).map (inclusion (ordinaryFunctor R R) P).op =
        (dualComplexFunctor R A (ComplexShape.down ℤ)).map (inclusion (ordinaryFunctor R R) Q).op ≫
        (dualComplexFunctor R A (ComplexShape.down ℤ)).map ((ordinaryFunctor R R).map f.restrict).op
      rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, inclusion_square])

/-- Ordinary cochains in a natural degree are exactly the algebraic duals
of the free singular chain modules. -/
def ordinaryCochainsEquiv (X : TopCat.{w}) (q : ℕ) :
    (ordinaryCochains R A X).X (q : ℤ) ≃ₗ[R] (Chains R X q →ₗ[R] A) :=
  LinearEquiv.arrowCongr (ordinaryNonnegativeIso R R X q).toLinearEquiv (LinearEquiv.refl R A)

/-- Hom of the actual quotient in each nonnegative degree. -/
def quotientCochainsEquiv (P : Pair.{w}) (q : ℕ) :
    (relativeCochains R A P).X (q : ℤ) ≃ₗ[R] quotientCochains R A P q :=
  LinearEquiv.arrowCongr
    (((ordinaryDegreeIso R R P q).toLinearEquiv).trans (chainQuotientEquiv R R P q))
    (LinearEquiv.refl R A)

/-- The explicit cocycle modulo coboundary representation of cohomology. -/
abbrev cohomologyQuotient (K : CochainComplex (ModuleCat.{t} R) ℤ) (q : ℤ) :=
  (K.sc q).g.hom.ker ⧸ (K.sc q).moduleCatToCycles.range

def cohomologyQuotientEquiv (K : CochainComplex (ModuleCat.{t} R) ℤ) (q : ℤ) :
    K.homology q ≃ₗ[R] cohomologyQuotient R K q :=
  (K.sc q).moduleCatHomologyIso.toLinearEquiv

namespace Expected

def coboundary : Prop :=
  ∀ (X : TopCat.{w}) (i j : ℤ) (a : (ordinaryComplex R R X).X i →ₗ[R] A)
    (c : (ordinaryComplex R R X).X j),
    (show (ordinaryComplex R R X).X j →ₗ[R] A from (ordinaryCochains R A X).d i j a) c = a ((ordinaryComplex R R X).d j i c)

def relativeCoboundary : Prop :=
  ∀ (P : Pair.{w}) (i j : ℤ) (a : (ordinary R R P).X i →ₗ[R] A)
    (c : (ordinary R R P).X j),
    (show (ordinary R R P).X j →ₗ[R] A from (relativeCochains R A P).d i j a) c = a ((ordinary R R P).d j i c)

def restrictionSurjective : Prop :=
  ∀ (P : Pair.{w}) (q : ℤ), Function.Surjective ((restriction R A P).f q)

def shortExact : Prop :=
  ∀ (P : Pair.{w}), DegreewiseShortExact (cochainSequence R A P)

def negative : Prop :=
  (∀ (X : TopCat.{w}) (q : ℤ), q < 0 →
    IsZero ((ordinaryCochains R A X).X q) ∧ IsZero (ordinaryCohomology R A X q)) ∧
  (∀ (P : Pair.{w}) (q : ℤ), q < 0 →
    IsZero ((relativeCochains R A P).X q) ∧ IsZero (relativeCohomology R A P q))

/-- Full natural long exact sequence, with the lift-and-coboundary formula and
independence of both lift and cocycle representative. -/
def longExact : Prop :=
  ∃ h : ∀ P : Pair.{w}, DegreewiseShortExact (cochainSequence R A P),
    (∀ P, (∀ q, (HomologicalComplex.HomologySequence.composableArrows₂
        (cochainSequence R A P) q).Exact) ∧
      (∀ q : ℤ, (segment (h P) q (q+1) (by simp)).Exact) ∧
      LiftsExist (cochainSequence R A P) (h P) ∧
      LiftFormula (cochainSequence R A P) (h P) ∧
      Independence (cochainSequence R A P) (h P)) ∧
    (∀ (P Q : Pair.{w}) (f : P ⟶ Q),
      (∀ q, homologyMap (relativeToAbsolute R A Q) q ≫
          (ordinaryCohomologyFunctor R A q).map f.map.op =
        (relativeCohomologyFunctor R A q).map f.op ≫
          homologyMap (relativeToAbsolute R A P) q) ∧
      (∀ q, homologyMap (restriction R A Q) q ≫
          (ordinaryCohomologyFunctor R A q).map f.restrict.op =
        (ordinaryCohomologyFunctor R A q).map f.map.op ≫
          homologyMap (restriction R A P) q) ∧
      (∀ q : ℤ, connecting (h Q) q (q+1) (by simp) ≫
          (relativeCohomologyFunctor R A (q+1)).map f.op =
        (ordinaryCohomologyFunctor R A q).map f.restrict.op ≫
          connecting (h P) q (q+1) (by simp)))

def homotopyInvariant : Prop :=
  (∀ {X Y : TopCat.{w}} {f g : X ⟶ Y}, TopCat.Homotopy f g → ∀ q : ℤ,
    (ordinaryCohomologyFunctor R A q).map f.op = (ordinaryCohomologyFunctor R A q).map g.op) ∧
  (∀ {P Q : Pair.{w}} {f g : P ⟶ Q}, P202Specs.PrismHomotopy.PairHomotopy f g → ∀ q : ℤ,
    (relativeCohomologyFunctor R A q).map f.op = (relativeCohomologyFunctor R A q).map g.op)

/-- The functor laws on the actual induced cohomology maps. -/
def functoriality : Prop :=
  (∀ (X : TopCat.{w}) (q : ℤ), (ordinaryCohomologyFunctor R A q).map (𝟙 X).op = 𝟙 _) ∧
  (∀ {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (q : ℤ),
    (ordinaryCohomologyFunctor R A q).map (f ≫ g).op =
      (ordinaryCohomologyFunctor R A q).map g.op ≫ (ordinaryCohomologyFunctor R A q).map f.op) ∧
  (∀ (P : Pair.{w}) (q : ℤ), (relativeCohomologyFunctor R A q).map (𝟙 P).op = 𝟙 _) ∧
  (∀ {P Q T : Pair.{w}} (f : P ⟶ Q) (g : Q ⟶ T) (q : ℤ),
    (relativeCohomologyFunctor R A q).map (f ≫ g).op =
      (relativeCohomologyFunctor R A q).map g.op ≫ (relativeCohomologyFunctor R A q).map f.op)

/-- Explicit identification with cochains vanishing on the subspace chains. -/
def quotientVanishing : Prop :=
  ∀ (P : Pair.{w}) (q : ℕ), ∃ e : quotientCochains R A P q ≃ₗ[R] vanishingCochains R A P q,
    ∀ (a : quotientCochains R A P q) (c : Chains R P.space q),
      (e a).val c = a (Submodule.Quotient.mk c)

/-- The vanishing condition can be checked on individual simplices with image in Y. -/
def vanishingOnSimplices : Prop :=
  ∀ (P : Pair.{w}) (q : ℕ) (a : Chains R P.space q →ₗ[R] A),
    a ∈ vanishingCochains R A P q ↔
      ∀ s : Simplex P.space q, InSubspace P q s → a (Finsupp.single s 1) = 0

/-- Pullback is precomposition with the induced chain map. -/
def pullback : Prop :=
  (∀ {X Y : TopCat.{w}} (f : X ⟶ Y) (q : ℤ)
    (a : (ordinaryComplex R R Y).X q →ₗ[R] A) (c : (ordinaryComplex R R X).X q),
    (show (ordinaryComplex R R X).X q →ₗ[R] A from
      ((ordinaryCochainFunctor R A).map f.op).f q a) c =
        a (((ordinaryFunctor R R).map f).f q c)) ∧
  (∀ {P Q : Pair.{w}} (f : P ⟶ Q) (q : ℤ)
    (a : (ordinary R R Q).X q →ₗ[R] A) (c : (ordinary R R P).X q),
    (show (ordinary R R P).X q →ₗ[R] A from
      ((relativeCochainFunctor R A).map f.op).f q a) c =
        a ((relativeMap (ordinaryFunctor R R) f).f q c))

/-- The coordinate identification respects the source's signed singular boundary. -/
def naturalCoboundary : Prop :=
  ∀ (X : TopCat.{w}) (q : ℕ) (a : Chains R X q →ₗ[R] A) (c : Chains R X (q+1)),
    ordinaryCochainsEquiv R A X (q+1)
      ((ordinaryCochains R A X).d (q : ℤ) ((q+1 : ℕ) : ℤ)
        ((ordinaryCochainsEquiv R A X q).symm a)) c = a (boundary R R X q c)

/-- The quotient identification agrees with the actual inclusion of relative
cochains into ordinary cochains, on every chain. -/
def quotientIdentification : Prop :=
  ∀ (P : Pair.{w}) (q : ℕ) (a : (relativeCochains R A P).X (q : ℤ))
    (c : Chains R P.space q),
    quotientCochainsEquiv R A P q a (Submodule.Quotient.mk c) =
      ordinaryCochainsEquiv R A P.space q ((relativeToAbsolute R A P).f (q : ℤ) a) c

end Expected
/-! Independent complete expected types and canonical construction values. -/

def coboundary_type : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A],
    Expected.coboundary.{u,v,w} R A

def relative_coboundary_type : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A],
    Expected.relativeCoboundary.{u,v,w} R A

def natural_coboundary_type : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A],
    Expected.naturalCoboundary.{u,v,w} R A

def restriction_surjective_type : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A],
    Expected.restrictionSurjective.{u,v,w} R A

def short_exact_type : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A],
    Expected.shortExact.{u,v,w} R A

def long_exact_type : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A],
    Expected.longExact.{u,v,w} R A

def pullback_type : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A],
    Expected.pullback.{u,v,w} R A

def functoriality_type : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A],
    Expected.functoriality.{u,v,w} R A

def homotopy_invariant_type : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A],
    Expected.homotopyInvariant.{u,v,w} R A

def negative_type : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A],
    Expected.negative.{u,v,w} R A

def quotient_vanishing_type : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A],
    Expected.quotientVanishing.{u,v,w} R A

def vanishing_on_simplices_type : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A],
    Expected.vanishingOnSimplices.{u,v,w} R A

def quotient_identification_type : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A],
    Expected.quotientIdentification.{u,v,w} R A

def ordinaryCochainFunctor_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A],
    TopCat.{w}ᵒᵖ ⥤ CochainComplex (ModuleCat.{max u v w} R) ℤ

def ordinaryCochainFunctor_value : ordinaryCochainFunctor_type.{u,v,w} :=
  fun R _ A _ _ => ordinaryCochainFunctor R A

def relativeCochainFunctor_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A],
    Pair.{w}ᵒᵖ ⥤ CochainComplex (ModuleCat.{max u v w} R) ℤ

def relativeCochainFunctor_value : relativeCochainFunctor_type.{u,v,w} :=
  fun R _ A _ _ => relativeCochainFunctor R A

def ordinaryCohomologyFunctor_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A],
    ∀ q : ℤ, TopCat.{w}ᵒᵖ ⥤ ModuleCat.{max u v w} R

def ordinaryCohomologyFunctor_value : ordinaryCohomologyFunctor_type.{u,v,w} :=
  fun R _ A _ _ q => ordinaryCohomologyFunctor R A q

def relativeCohomologyFunctor_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A],
    ∀ q : ℤ, Pair.{w}ᵒᵖ ⥤ ModuleCat.{max u v w} R

def relativeCohomologyFunctor_value : relativeCohomologyFunctor_type.{u,v,w} :=
  fun R _ A _ _ q => relativeCohomologyFunctor R A q

def ordinaryCochainsEquiv_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A],
    ∀ (X : TopCat.{w}) (q : ℕ), (ordinaryCochains R A X).X (q : ℤ) ≃ₗ[R] (Chains R X q →ₗ[R] A)

def ordinaryCochainsEquiv_value : ordinaryCochainsEquiv_type.{u,v,w} :=
  fun R _ A _ _ X q => ordinaryCochainsEquiv R A X q

def quotientCochainsEquiv_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A],
    ∀ (P : Pair.{w}) (q : ℕ), (relativeCochains R A P).X (q : ℤ) ≃ₗ[R] quotientCochains R A P q

def quotientCochainsEquiv_value : quotientCochainsEquiv_type.{u,v,w} :=
  fun R _ A _ _ P q => quotientCochainsEquiv R A P q

def cohomologyQuotientEquiv_type :=
  ∀ (R : Type u) [CommRing R] (K : CochainComplex (ModuleCat.{t} R) ℤ) (q : ℤ),
    K.homology q ≃ₗ[R] cohomologyQuotient R K q

def cohomologyQuotientEquiv_value : cohomologyQuotientEquiv_type.{u,t} :=
  fun R _ K q => cohomologyQuotientEquiv R K q

def cochainSequence_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A],
    ∀ P : Pair.{w}, ShortComplex (CochainComplex (ModuleCat.{max u v w} R) ℤ)

def cochainSequence_value : cochainSequence_type.{u,v,w} :=
  fun R _ A _ _ P => cochainSequence R A P

def abelianOrdinaryCochainFunctor_type :=
  ∀ (A : Type v) [AddCommGroup A],
    TopCat.{w}ᵒᵖ ⥤ CochainComplex (ModuleCat.{max v w} ℤ) ℤ

def abelianOrdinaryCochainFunctor_value : abelianOrdinaryCochainFunctor_type.{v,w} :=
  fun A _ => ordinaryCochainFunctor ℤ A

def abelianRelativeCochainFunctor_type :=
  ∀ (A : Type v) [AddCommGroup A],
    Pair.{w}ᵒᵖ ⥤ CochainComplex (ModuleCat.{max v w} ℤ) ℤ

def abelianRelativeCochainFunctor_value : abelianRelativeCochainFunctor_type.{v,w} :=
  fun A _ => relativeCochainFunctor ℤ A

end P202Specs.CohomologyPairs
