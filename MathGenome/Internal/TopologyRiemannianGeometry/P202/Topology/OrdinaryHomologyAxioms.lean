import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.OrdinaryHomologyAxioms
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SingularChains
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SingularDegreeZero
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.PrismHomotopy
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.RelativeSingularChains
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.ChainLongExactSequence
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.Excision
import Mathlib.Topology.ContinuousMap.Sigma
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Products

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
open scoped Simplicial
namespace P202.OrdinaryHomologyAxioms
open P202Specs.SingularChains P202Specs.OrdinaryHomologyAxioms
open P202Specs.RelativeSingularChains
universe u v w

variable {I : Type v} (X : I → TopCat.{v})

/-- A simplex in a topological disjoint union has a unique summand. -/
def simplexSigmaEquiv (n : ℕ) :
    Simplex (TopCat.of (Σ i, X i)) n ≃ Σ i, Simplex (X i) n :=
  (simplexEquiv _ n).trans
    ((ContinuousMap.sigmaCodHomeomorph
      (Convexity.StdSimplex ℝ (Fin (n+1))) (fun i => X i)).toEquiv.trans
      (Equiv.sigmaCongrRight (fun i => (simplexEquiv (X i) n).symm)))

lemma simplexSigmaEquiv_symm (n : ℕ) (i : I) (s : Simplex (X i) n) :
    (simplexSigmaEquiv X n).symm ⟨i,s⟩ =
      (TopCat.toSSet.map (TopCat.sigmaι X i)).app (op ⦋n⦌) s := by
  change (simplexEquiv (TopCat.of (Σ i, X i)) n).symm
    ((ContinuousMap.sigmaMk (X := fun i => X i) i).comp (simplexEquiv (X i) n s)) = _
  apply (simplexEquiv _ n).injective
  rw [Equiv.apply_symm_apply, P202.SingularChains.simplexEquiv_postcomp]
  rfl

variable (R : Type u) [CommRing R] (M : Type w) [AddCommGroup M] [Module R M]

/-- Degreewise coproduct universal property, obtained directly from the simplex basis. -/
def chainsIsColimit (n : ℕ) :
    IsColimit (Cofan.mk ((complex R M (TopCat.of (Σ i, X i))).X n)
      (fun i => (chainMap R M (TopCat.sigmaι X i)).f n)) where
  desc c := ModuleCat.ofHom ((Finsupp.lsum R (fun s : Σ i, Simplex (X i) n =>
    (c.ι.app ⟨s.1⟩).hom.comp (Finsupp.lsingle s.2))).comp
      (Finsupp.lmapDomain M R (simplexSigmaEquiv X n)))
  fac c j := by
    rcases j with ⟨i⟩
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro s m
    change (Finsupp.lsum R _) (Finsupp.mapDomain (simplexSigmaEquiv X n)
      (((chainMap R M (TopCat.sigmaι X i)).f n).hom (Finsupp.single s m))) = _
    rw [P202.SingularChains.chainMap_single, ← simplexSigmaEquiv_symm X]
    simp only [Finsupp.mapDomain_single, Equiv.apply_symm_apply, Finsupp.lsum_single]
    rfl
  uniq c f hf := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro s m
    obtain ⟨⟨i,t⟩, rfl⟩ := (simplexSigmaEquiv X n).symm.surjective s
    have h := congrArg (fun g => g.hom (Finsupp.single t m)) (hf ⟨i⟩)
    change f.hom (((chainMap R M (TopCat.sigmaι X i)).f n).hom
      (Finsupp.single t m)) = _ at h
    rw [P202.SingularChains.chainMap_single, ← simplexSigmaEquiv_symm X] at h
    change f.hom _ = (Finsupp.lsum R _) (Finsupp.mapDomain (simplexSigmaEquiv X n)
      (Finsupp.single ((simplexSigmaEquiv X n).symm ⟨i,t⟩) m))
    rw [Finsupp.mapDomain_single, Equiv.apply_symm_apply, Finsupp.lsum_single]
    exact h

/-- The ordinary nonnegative complex has the direct sum universal property. -/
def chainIsColimit : IsColimit (chainCofan R X M) :=
  HomologicalComplex.isColimitOfEval _ _ (fun n =>
    (isColimitMapCoconeCofanMkEquiv _ _ _).symm (chainsIsColimit X R M n))

section ExactCoproducts
universe a b t
variable {C : Type a} [Category.{b} C] [Abelian C] {J : Type t}
  [HasColimitsOfShape (Discrete J) C] [HasExactColimitsOfShape (Discrete J) C]

/-- Exact coproducts commute with homology, keeping the maps of the cofan. -/
def shortComplexHomologyIsColimit (F : Discrete J ⥤ ShortComplex C)
    (c : Cocone F)
    (h₁ : IsColimit (ShortComplex.π₁.mapCocone c))
    (h₂ : IsColimit (ShortComplex.π₂.mapCocone c))
    (h₃ : IsColimit (ShortComplex.π₃.mapCocone c)) :
    IsColimit ((ShortComplex.homologyFunctor C).mapCocone c) := by
  let S := (ShortComplex.functorEquivalence (Discrete J) C).inverse.obj F
  let e₁ : colimit S.X₁ ≅ c.pt.X₁ :=
    (colimit.isColimit _).coconePointUniqueUpToIso h₁
  let e₂ : colimit S.X₂ ≅ c.pt.X₂ :=
    (colimit.isColimit _).coconePointUniqueUpToIso h₂
  let e₃ : colimit S.X₃ ≅ c.pt.X₃ :=
    (colimit.isColimit _).coconePointUniqueUpToIso h₃
  have he₁ (j) : colimit.ι S.X₁ j ≫ e₁.hom = (c.ι.app j).τ₁ :=
    (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom h₁ j
  have he₂ (j) : colimit.ι S.X₂ j ≫ e₂.hom = (c.ι.app j).τ₂ :=
    (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom h₂ j
  have he₃ (j) : colimit.ι S.X₃ j ≫ e₃.hom = (c.ι.app j).τ₃ :=
    (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom h₃ j
  let e : S.map colim ≅ c.pt := ShortComplex.isoMk e₁ e₂ e₃ (by
    change e₁.hom ≫ c.pt.f = colimMap S.f ≫ e₂.hom
    apply colimit.hom_ext
    intro j
    rw [← Category.assoc, he₁, ι_colimMap_assoc, he₂]
    exact (c.ι.app j).comm₁₂) (by
    change e₂.hom ≫ c.pt.g = colimMap S.g ≫ e₃.hom
    apply colimit.hom_ext
    intro j
    rw [← Category.assoc, he₂, ι_colimMap_assoc, he₃]
    exact (c.ι.app j).comm₂₃)
  let E : S.homology ≅ F ⋙ ShortComplex.homologyFunctor C :=
    Discrete.natIso (fun j => (S.mapHomologyIso ((evaluation (Discrete J) C).obj j)).symm)
  let total : colimit (F ⋙ ShortComplex.homologyFunctor C) ≅ c.pt.homology :=
    colim.mapIso E.symm ≪≫ (S.mapHomologyIso colim).symm ≪≫
      (ShortComplex.homologyFunctor C).mapIso e
  apply IsColimit.ofIsoColimit (colimit.isColimit _)
    (Cocone.ext (c' := (ShortComplex.homologyFunctor C).mapCocone c) total ?_)
  intro j
  let τ : (evaluation (Discrete J) C).obj j ⟶ colim :=
    { app := fun D => colimit.ι D j
      naturality := fun D D' f => (ι_colimMap f j).symm }
  change colimit.ι _ j ≫ colimMap E.inv ≫
    (S.mapHomologyIso colim).inv ≫ ShortComplex.homologyMap e.hom =
      ShortComplex.homologyMap (c.ι.app j)
  rw [ι_colimMap_assoc]
  change (S.mapHomologyIso ((evaluation (Discrete J) C).obj j)).hom ≫
    τ.app S.homology ≫ (S.mapHomologyIso colim).inv ≫
      ShortComplex.homologyMap e.hom = _
  calc
    _ = ShortComplex.homologyMap (S.mapNatTrans τ) ≫
        ShortComplex.homologyMap e.hom := by
      rw [ShortComplex.homologyMap_mapNatTrans]
      simp only [Category.assoc]
    _ = _ := by
      rw [← ShortComplex.homologyMap_comp]
      congr 1
      apply ShortComplex.Hom.ext
      · exact he₁ j
      · exact he₂ j
      · exact he₃ j

/-- Homology of a coproduct of complexes is the coproduct of their homologies. -/
def complexHomologyIsColimit {ι : Type*} {shape : ComplexShape ι}
    (F : Discrete J ⥤ HomologicalComplex C shape) (c : Cocone F)
    (hc : IsColimit c) (n : ι) :
    IsColimit ((HomologicalComplex.homologyFunctor C shape n).mapCocone c) := by
  change IsColimit ((ShortComplex.homologyFunctor C).mapCocone
    ((shortComplexFunctor C shape n).mapCocone c))
  apply shortComplexHomologyIsColimit
  · exact isColimitOfPreserves (eval C shape (shape.prev n)) hc
  · exact isColimitOfPreserves (eval C shape n) hc
  · exact isColimitOfPreserves (eval C shape (shape.next n)) hc

end ExactCoproducts

/-- Extension by zero preserves coproducts, including the empty coproduct. -/
lemma extensionPreservesCoproducts :
    PreservesColimitsOfShape (Discrete I)
      ((degreeEmbedding 0).extendFunctor (ModuleCat.{max w v} R)) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  by_cases hn : n < 0
  · apply Functor.preservesColimitsOfShape_of_isZero
    rw [Functor.isZero_iff]
    intro K
    apply HomologicalComplex.isZero_extend_X
    intro i hi
    change (0 : ℤ) + i = n at hi
    omega
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ n)
    exact preservesColimitsOfShape_of_natIso
      ((degreeEmbedding 0).extendFunctorCompEvalIso
        (ModuleCat.{max w v} R) (i := k) (by change (0 : ℤ) + k = k; omega)).symm

/-- The integer-graded ordinary complex is the same direct sum, extended by zero. -/
def ordinaryChainIsColimit : IsColimit (ordinaryChainCofan R X M) := by
  letI := extensionPreservesCoproducts (I := I) (R := R)
  exact isColimitCofanMkObjOfIsColimit
    ((degreeEmbedding 0).extendFunctor (ModuleCat.{max w v} R))
    (fun i => complex R M (X i))
    (fun i => chainMap R M (TopCat.sigmaι X i)) (chainIsColimit X R M)

/-- Exactness of module coproducts at the coefficient and space universes in use. -/
lemma moduleExactCoproducts :
    HasExactColimitsOfShape (Discrete I) (ModuleCat.{max w v} R) := by
  letI : HasCoproducts.{v} AddCommGrpCat.{max w v} := hasCoproducts_shrink
  letI : AB4OfSize.{v} AddCommGrpCat.{max w v} := AB4OfSize_shrink.{v, max w v} _
  exact HasExactColimitsOfShape.domain_of_functor (Discrete I)
    (forget₂ (ModuleCat.{max w v} R) AddCommGrpCat)

/-- The maps induced by summand inclusions exhibit homology as a direct sum. -/
def homologyIsColimit (n : ℤ) : IsColimit (homologyCofan R X M n) := by
  letI : HasCoproducts.{v} (ModuleCat.{max w v} R) := hasCoproducts_shrink
  letI := moduleExactCoproducts (I := I) (R := R)
  exact (isColimitMapCoconeCofanMkEquiv _ _ _)
    (complexHomologyIsColimit _ _ (ordinaryChainIsColimit X R M) n)

/-- The universal-property statement identifies the usual algebraic direct sum.
The isomorphism is induced by the canonical summand inclusions. -/
def homologyDirectSumIso (n : ℤ) :
    ModuleCat.of R (DirectSum I (fun i => P202Specs.SingularChains.homology R M (X i) n)) ≅
      homology R M (TopCat.of (Σ i, X i)) n := by
  classical
  exact (ModuleCat.coproductCoconeIsColimit (fun i => homology R M (X i) n)).coconePointUniqueUpToIso (homologyIsColimit X R M n)

open Classical in
@[reassoc (attr := simp)]
lemma homologyDirectSumIso_inclusion (n : ℤ) (i : I) :
    ModuleCat.ofHom (DirectSum.lof R I (fun i => homology R M (X i) n) i) ≫
      (homologyDirectSumIso X R M n).hom =
        (homologyFunctor R M n).map (TopCat.sigmaι X i) := by
  classical
  exact (ModuleCat.coproductCoconeIsColimit (fun i => homology R M (X i) n)).comp_coconePointUniqueUpToIso_hom (homologyIsColimit X R M n) ⟨i⟩

/-- Additivity through the actual inclusions, for arbitrary modules and index types. -/
theorem chainAdditivity : chainAdditivity_type.{u,v,w} := by
  intro R _ I X M _ _
  exact ⟨chainIsColimit X R M⟩

/-- Ordinary chains in all integer degrees have the same coproduct property. -/
theorem ordinaryChainAdditivity : ordinaryChainAdditivity_type.{u,v,w} := by
  intro R _ I X M _ _
  exact ⟨ordinaryChainIsColimit X R M⟩

/-- Ordinary homology takes arbitrary disjoint unions to direct sums. -/
theorem homologyAdditivity : homologyAdditivity_type.{u,v,w} := by
  intro R _ I X M _ _ n
  exact ⟨homologyIsColimit X R M n⟩

/-- The preceding constructions satisfy the ordinary homology axioms.
The full statement keeps the ring, coefficient and space universes explicit. -/
theorem ordinaryAxioms :
  (∀ (R : Type u) [CommRing R] (M : Type w) [AddCommGroup M] [Module R M]
    (n : ℤ),
    (∀ X : TopCat.{v}, (homologyFunctor R M n).map (𝟙 X) = 𝟙 _) ∧
    (∀ {X Y Z : TopCat.{v}} (f : X ⟶ Y) (g : Y ⟶ Z),
      (homologyFunctor R M n).map (f ≫ g) =
        (homologyFunctor R M n).map f ≫ (homologyFunctor R M n).map g)) ∧
  P202Specs.PrismHomotopy.Expected.homology.{u,w,v} ∧
  P202Specs.PrismHomotopy.Expected.relativeHomology.{u,w,v} ∧
  (∀ (R : Type u) [CommRing R] (M : Type w) [AddCommGroup M] [Module R M],
    ordinaryLESType.{u,w,v} R M) ∧
  P202Specs.Excision.isomorphism_type.{u,v} ∧ P202Specs.Excision.naturality_type.{u,v} ∧
  P202Specs.SingularDegreeZero.Expected.pointOrdinaryZero.{u,w,v} ∧
  P202Specs.SingularDegreeZero.Expected.pointOrdinaryOther.{u,w,v} := by
  refine ⟨?_, P202.PrismHomotopy.homology, P202.PrismHomotopy.relativeHomology,
    ?_, P202.Excision.isomorphism, P202.Excision.naturality,
    P202.SingularDegreeZero.pointOrdinaryZero, P202.SingularDegreeZero.pointOrdinaryOther⟩
  · intro R _ M _ _ n
    exact ⟨(homologyFunctor R M n).map_id, fun f g => (homologyFunctor R M n).map_comp f g⟩
  · intro R _ M _ _
    exact P202.RelativeSingularChains.ordinary_les R M

end P202.OrdinaryHomologyAxioms
