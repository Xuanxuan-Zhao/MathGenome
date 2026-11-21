import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Cohomology.Pairs
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Cohomology.FreeChainDual
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.Excision
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.MayerVietoris

/-! Independent statements for paper.tex 1775–1804. Cochains are unrestricted
algebraic Hom, with no injectivity or finiteness hypothesis on coefficients.
The open-cover comparison is made on chains before dualizing. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
universe u v w
namespace P202Specs.CohomologyExcisionMV
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CohomologyPairs P202Specs.ChainLES
open P202Specs.MayerVietoris

/-- Excision for the actual contravariant relative cohomology maps, in all
integer degrees. Specializing R to ℤ includes every abelian coefficient group. -/
def excision_type : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type w) [AddCommGroup A] [Module R A]
    (D : P202Specs.Excision.Data.{v}) (q : ℤ),
    IsIso ((relativeCohomologyFunctor R A q).map D.inclusion.op)

def excision_naturality_type : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type w) [AddCommGroup A] [Module R A]
    (D E : P202Specs.Excision.Data.{v}) (f : P202Specs.Excision.Map D E) (q : ℤ),
    (relativeCohomologyFunctor R A q).map f.pairMap.op ≫
        (relativeCohomologyFunctor R A q).map D.inclusion.op =
      (relativeCohomologyFunctor R A q).map E.inclusion.op ≫
        (relativeCohomologyFunctor R A q).map f.excised.op

variable (R : Type u) [CommRing R] (A : Type w) [AddCommGroup A] [Module R A]

abbrev coverChains := theoryFunctor.{u,v} R .ordinary

/-- A presentation of the small complex: identify duplicate simplices in U∩V
with the sign (i,-j). This is the categorical cokernel of that chain map. -/
abbrev coverQuotient (C : CoverPair.{v,w}) := cokernel (chainFirst (coverChains R) C)

lemma chainFirst_chainSum (C : CoverPair.{v,w}) :
    chainFirst (coverChains R) C ≫ chainSum (coverChains R) C = 0 := by
  simp only [chainFirst, chainSum, biprod.lift_desc, Preadditive.neg_comp]
  rw [← Functor.map_comp, ← Functor.map_comp]
  have h : C.toLeft ≫ C.leftInclusion = C.toRight ≫ C.rightInclusion := by
    apply PairMap.ext
    rfl
  rw [h, add_neg_cancel]

/-- The canonical comparison sends a class represented by (a,b) to a+b. -/
def coverComparison (C : CoverPair.{v,w}) : coverQuotient R C ⟶ (coverChains R).obj C.pair :=
  cokernel.desc _ (chainSum (coverChains R) C) (chainFirst_chainSum R C)

abbrev coverCochains (C : CoverPair.{v,w}) :=
  (dualComplexFunctor R A (.down ℤ)).obj (op (coverQuotient R C))

abbrev coverDualComparison (C : CoverPair.{v,w}) :
    ordinaryCochains R A C.pair.space ⟶ coverCochains R A C :=
  (dualComplexFunctor R A (.down ℤ)).map (coverComparison R C).op

/-- Dual of the presentation; short exactness is a conclusion of the theorem. -/
def coverCochainSequence (C : CoverPair.{v,w}) :
    ShortComplex (CochainComplex (ModuleCat.{max u v w} R) ℤ) :=
  ShortComplex.mk
    ((dualComplexFunctor R A (.down ℤ)).map (cokernel.π (chainFirst (coverChains R) C)).op)
    ((dualComplexFunctor R A (.down ℤ)).map (chainFirst (coverChains R) C).op)
    (by rw [← Functor.map_comp, ← op_comp, cokernel.condition, op_zero, Functor.map_zero])

abbrev cohomologyMiddle (C : CoverPair.{v,w}) (q : ℤ) :=
  ordinaryCohomology R A C.leftPair.space q ⊞ ordinaryCohomology R A C.rightPair.space q

/-- The first map is the two ordinary restrictions. -/
def restrictions (C : CoverPair.{v,w}) (q : ℤ) :
    ordinaryCohomology R A C.pair.space q ⟶ cohomologyMiddle R A C q :=
  biprod.lift ((ordinaryCohomologyFunctor R A q).map C.leftInclusion.map.op)
    ((ordinaryCohomologyFunctor R A q).map C.rightInclusion.map.op)

/-- The next map takes the difference of the two restrictions. -/
def difference (C : CoverPair.{v,w}) (q : ℤ) :
    cohomologyMiddle R A C q ⟶ ordinaryCohomology R A C.intersectionPair.space q :=
  biprod.desc ((ordinaryCohomologyFunctor R A q).map C.toLeft.map.op)
    (- (ordinaryCohomologyFunctor R A q).map C.toRight.map.op)

abbrev CohomologyConnecting := ∀ (C : CoverPair.{v,w}) (q : ℤ),
  ordinaryCohomology R A C.intersectionPair.space q ⟶ ordinaryCohomology R A C.pair.space (q+1)

def CohomologyExact (δ : CohomologyConnecting R A) : Prop :=
  (∀ (C : CoverPair.{v,w}) (q : ℤ), (ComposableArrows.mk₅ (restrictions R A C q) (difference R A C q) (δ C q)
    (restrictions R A C (q+1)) (difference R A C (q+1))).Exact) ∧
  ∀ (C : CoverPair.{v,w}) (q : ℤ), (ComposableArrows.mk₂ (restrictions R A C q) (difference R A C q)).Exact

def CohomologyNatural (δ : CohomologyConnecting R A) : Prop :=
  ∀ (C D : CoverPair.{v,w}) (f : CoverMap C D),
    (∀ q, restrictions R A D q ≫
        biprod.map ((ordinaryCohomologyFunctor R A q).map f.onLeft.map.op)
          ((ordinaryCohomologyFunctor R A q).map f.onRight.map.op) =
      (ordinaryCohomologyFunctor R A q).map f.map.map.op ≫ restrictions R A C q) ∧
    (∀ q, difference R A D q ≫
        (ordinaryCohomologyFunctor R A q).map f.onIntersection.map.op =
      biprod.map ((ordinaryCohomologyFunctor R A q).map f.onLeft.map.op)
        ((ordinaryCohomologyFunctor R A q).map f.onRight.map.op) ≫ difference R A C q) ∧
    ∀ q, δ D q ≫ (ordinaryCohomologyFunctor R A (q+1)).map f.map.map.op =
      (ordinaryCohomologyFunctor R A q).map f.onIntersection.map.op ≫ δ C q

/-- The long exact sequence is specifically the one from the cochain connecting
map, transported by restriction from full cochains to small cochains. The source
of that connecting map is literally the cochains on the intersection. -/
def CohomologyConnectingFormula
    (h : ∀ C : CoverPair.{v,w}, DegreewiseShortExact (coverCochainSequence R A C))
    (δ : CohomologyConnecting R A) : Prop :=
  ∀ C q, δ C q ≫ homologyMap (coverDualComparison R A C) (q+1) =
    connecting (h C) q (q+1) (by simp)

/-- Full ordinary cohomological Mayer–Vietoris, including degree zero, empty
pieces and intersection, all abelian coefficients, and cover-map naturality.
The degreewise split chain comparison is part of the conclusion, so this type
cannot be met by simply dualizing an exact sequence of homology groups. -/
def mayer_vietoris_type : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type w) [AddCommGroup A] [Module R A],
    (∀ C : CoverPair.{v,w},
      (∃ e : HomotopyEquiv (coverQuotient R C) ((coverChains R).obj C.pair),
        e.hom = coverComparison R C) ∧
      (∀ q : ℤ, ∃ r : (middle (coverChains R) C).X q ⟶
          ((coverChains R).obj C.intersectionPair).X q,
        (chainFirst (coverChains R) C).f q ≫ r = 𝟙 _) ∧
      QuasiIso (coverDualComparison R A C)) ∧
    ∃ h : ∀ C : CoverPair.{v,w}, DegreewiseShortExact (coverCochainSequence R A C),
      (∀ C, LiftsExist (coverCochainSequence R A C) (h C) ∧
        LiftFormula (coverCochainSequence R A C) (h C) ∧
        Independence (coverCochainSequence R A C) (h C)) ∧
      ∃ δ : CohomologyConnecting R A,
        CohomologyExact R A δ ∧ CohomologyNatural R A δ ∧
          CohomologyConnectingFormula R A h δ

end P202Specs.CohomologyExcisionMV
