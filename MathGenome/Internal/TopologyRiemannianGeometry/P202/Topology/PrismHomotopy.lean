import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.PrismHomotopy
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SingularDegreeZero
import Mathlib.Topology.Homotopy.TopCat.ToSSet
import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Simplicial
namespace P202.PrismHomotopy
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.PrismHomotopy
universe u v w
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

/-- Applying the finite-support functor to the simplicial prism. The symmetry
changes Mathlib's negative prism to the positive prism of the source. -/
def chainPrism {X Y : TopCat.{w}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g) :
    _root_.Homotopy (chainMap R M g) (chainMap R M f) :=
  (H.toSSet.toSimplicialObjectHomotopy.whiskerRight (finsuppFunctor R M)).toChainHomotopy.symm

theorem nonnegative : Expected.nonnegative.{u,v,w} := by
  intro R _ M _ _ X Y f g H
  exact ⟨chainPrism R M H⟩

/-- The prism is zero on the newly inserted coefficient object. -/
def augmentedPrism {X Y : TopCat.{w}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g) :
    _root_.Homotopy (augmentedShiftedMap R M g) (augmentedShiftedMap R M f) where
  hom i j := match i, j with
    | 0, _ => 0
    | _, 0 => 0
    | i+1, j+1 => (chainPrism R M H).hom i j
  zero i j hij := by
    cases i <;> cases j <;> simp only
    exact (chainPrism R M H).zero _ _ (by simpa using hij)
  comm i := by
    cases i with
    | zero =>
      rw [dNext_eq_zero _ _ (by simp), prevD_eq _ (show (ComplexShape.down ℕ).Rel 1 0 by simp)]
      simp [augmentedShiftedMap]
    | succ i =>
      rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (i+1) i by simp),
        prevD_eq _ (show (ComplexShape.down ℕ).Rel (i+2) (i+1) by simp)]
      cases i with
      | zero =>
        have h := (chainPrism R M H).comm 0
        rw [dNext_eq_zero _ _ (by simp), prevD_eq _ (show (ComplexShape.down ℕ).Rel 1 0 by simp)] at h
        simpa [augmentedShiftedMap, augmentedShifted] using h
      | succ i =>
        have h := (chainPrism R M H).comm (i+1)
        rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (i+1) i by simp),
          prevD_eq _ (show (ComplexShape.down ℕ).Rel (i+2) (i+1) by simp)] at h
        simpa [augmentedShiftedMap, augmentedShifted] using h

def ordinaryPrism {X Y : TopCat.{w}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g) :
    _root_.Homotopy ((ordinaryFunctor R M).map g) ((ordinaryFunctor R M).map f) :=
  (chainPrism R M H).extend (degreeEmbedding 0)

def reducedPrism {X Y : TopCat.{w}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g) :
    _root_.Homotopy ((reducedFunctor R M).map g) ((reducedFunctor R M).map f) :=
  (augmentedPrism R M H).extend (degreeEmbedding (-1))

lemma reducedPrism_minus_one {X Y : TopCat.{w}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g) :
    (reducedPrism R M H).hom (-1) 0 = 0 := by
  unfold reducedPrism
  rw [Homotopy.extend_hom_eq _ _ (i := 0) (j := 1) (by rfl) (by rfl)]
  simp [augmentedPrism]

theorem ordinary : Expected.ordinary.{u,v,w} := by
  intro R _ M _ _ X Y f g H
  exact ⟨ordinaryPrism R M H⟩

theorem reduced : Expected.reduced.{u,v,w} := by
  intro R _ M _ _ X Y f g H
  exact ⟨reducedPrism R M H, reducedPrism_minus_one R M H⟩

/-- Restriction of a homotopy preserving subspaces. -/
def restrictHomotopy {P Q : Pair.{w}} {f g : P ⟶ Q} (H : PairHomotopy f g) :
    TopCat.Homotopy f.restrict g.restrict where
  toFun p := ⟨H.homotopy (p.1, p.2.val), H.preserves p.1 p.2⟩
  continuous_toFun := (H.homotopy.continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left x := Subtype.ext (H.homotopy.map_zero_left x.val)
  map_one_left x := Subtype.ext (H.homotopy.map_one_left x.val)

open MonoidalCategory Functor.LaxMonoidal in
lemma simplicialHomotopy_subspace {P Q : Pair.{w}} {f g : P ⟶ Q}
    (H : PairHomotopy f g) :
    (TopCat.toSSet.map P.inclusion ▷ _) ≫ H.homotopy.toSSet.h =
      (restrictHomotopy H).toSSet.h ≫ TopCat.toSSet.map Q.inclusion := by
  have hh : (P.inclusion ▷ TopCat.I) ≫ H.homotopy.h =
      (restrictHomotopy H).h ≫ Q.inclusion := by ext x; rfl
  dsimp [TopCat.Homotopy.toSSet]
  rw [← whisker_exchange_assoc, μ_natural_left_assoc, ← TopCat.toSSet.map_comp,
    hh, TopCat.toSSet.map_comp]
  simp only [Category.assoc]

open Opposite MonoidalCategory in
lemma simplexPrism_subspace {P Q : Pair.{w}} {f g : P ⟶ Q}
    (H : PairHomotopy f g) (n : ℕ) (i : Fin (n+1)) :
    (TopCat.toSSet.map P.inclusion).app (op ⦋n⦌) ≫
      H.homotopy.toSSet.toSimplicialObjectHomotopy.h i =
    (restrictHomotopy H).toSSet.toSimplicialObjectHomotopy.h i ≫
      (TopCat.toSSet.map Q.inclusion).app (op ⦋n+1⦌) := by
  ext s
  change ((SSet.yonedaEquiv.symm ((TopCat.toSSet.map P.inclusion).app _ s) ▷ _ ≫
      H.homotopy.toSSet.h).app _ _) =
    (((SSet.yonedaEquiv.symm s ▷ _ ≫ (restrictHomotopy H).toSSet.h) ≫
      TopCat.toSSet.map Q.inclusion).app _ _)
  rw [← SSet.yonedaEquiv_symm_comp, comp_whiskerRight, Category.assoc,
    simplicialHomotopy_subspace, Category.assoc]

lemma chainPrism_subspace {P Q : Pair.{w}} {f g : P ⟶ Q}
    (H : PairHomotopy f g) (i j : ℕ) :
    (chainMap R M P.inclusion).f i ≫ (chainPrism R M H.homotopy).hom i j =
    (chainPrism R M (restrictHomotopy H)).hom i j ≫ (chainMap R M Q.inclusion).f j := by
  by_cases hij : i+1 = j
  · subst j
    simp only [chainPrism, Homotopy.symm_hom,
      CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy,
      CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom_eq,
      neg_neg, Preadditive.comp_sum, Preadditive.sum_comp,
      Preadditive.comp_zsmul, Preadditive.zsmul_comp]
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    simpa [chainMap, chainFunctor, CategoryTheory.SimplicialObject.Homotopy.whiskerRight] using
      congrArg ((finsuppFunctor R M).map) (simplexPrism_subspace H i k)
  · rw [(chainPrism R M H.homotopy).zero i j (by simpa using hij),
      (chainPrism R M (restrictHomotopy H)).zero i j (by simpa using hij)]
    simp

lemma augmentedPrism_subspace {P Q : Pair.{w}} {f g : P ⟶ Q}
    (H : PairHomotopy f g) (i j : ℕ) :
    (augmentedShiftedMap R M P.inclusion).f i ≫ (augmentedPrism R M H.homotopy).hom i j =
    (augmentedPrism R M (restrictHomotopy H)).hom i j ≫
      (augmentedShiftedMap R M Q.inclusion).f j := by
  cases i <;> cases j <;> simp [augmentedPrism, augmentedShiftedMap, chainPrism_subspace]

section Extension
variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {A B D E : HomologicalComplex C c}
  {f g : A ⟶ B} {f' g' : D ⟶ E}

/-- Extension by zero preserves compatibility of homotopy components. -/
lemma extendPrism_natural (e : c.Embedding c') [e.IsRelIff]
    (s : D ⟶ A) (t : E ⟶ B) (h : _root_.Homotopy f g) (h' : _root_.Homotopy f' g')
    (w : ∀ i j, s.f i ≫ h.hom i j = h'.hom i j ≫ t.f j) (i' j' : ι') :
    (extendMap s e).f i' ≫ (h.extend e).hom i' j' =
      (h'.extend e).hom i' j' ≫ (extendMap t e).f j' := by
  by_cases hi : ∃ i, e.f i = i'
  · obtain ⟨i, rfl⟩ := hi
    by_cases hj : ∃ j, e.f j = j'
    · obtain ⟨j, rfl⟩ := hj
      rw [extendMap_f _ _ rfl, extendMap_f _ _ rfl,
        Homotopy.extend_hom_eq _ _ rfl rfl, Homotopy.extend_hom_eq _ _ rfl rfl]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc (s.f i), w]
      simp only [Category.assoc]
    · exact (isZero_extend_X _ _ _ (by tauto)).eq_of_tgt _ _
  · exact (isZero_extend_X _ _ _ (by tauto)).eq_of_src _ _
end Extension

lemma ordinaryPrism_subspace {P Q : Pair.{w}} {f g : P ⟶ Q}
    (H : PairHomotopy f g) (i j : ℤ) :
    (inclusion (ordinaryFunctor R M) P).f i ≫ (ordinaryPrism R M H.homotopy).hom i j =
    (ordinaryPrism R M (restrictHomotopy H)).hom i j ≫
      (inclusion (ordinaryFunctor R M) Q).f j :=
  extendPrism_natural _ _ _ _ _ (chainPrism_subspace R M H) i j

lemma reducedPrism_subspace {P Q : Pair.{w}} {f g : P ⟶ Q}
    (H : PairHomotopy f g) (i j : ℤ) :
    (inclusion (reducedFunctor R M) P).f i ≫ (reducedPrism R M H.homotopy).hom i j =
    (reducedPrism R M (restrictHomotopy H)).hom i j ≫
      (inclusion (reducedFunctor R M) Q).f j :=
  extendPrism_natural _ _ _ _ _ (augmentedPrism_subspace R M H) i j

section Quotient
variable {C : Type*} [Category* C] [Abelian C]
  {ι : Type*} {c : ComplexShape ι}
  (K : TopCat.{w} ⥤ HomologicalComplex C c)
  {P Q : Pair.{w}} {f g : P ⟶ Q}
  (h : _root_.Homotopy (K.map g.map) (K.map f.map))
  (hs : _root_.Homotopy (K.map g.restrict) (K.map f.restrict))
  (w : ∀ i j, (inclusion K P).f i ≫ h.hom i j = hs.hom i j ≫ (inclusion K Q).f j)

/-- The induced degreewise map on the cokernel. -/
def quotientPrismComponent (i j : ι) :
    (relativeComplex K P).X i ⟶ (relativeComplex K Q).X j :=
  (degreeQuotientIso K P i).hom ≫
    cokernel.desc ((inclusion K P).f i) (h.hom i j ≫ (projection K Q).f j) (by
      rw [← Category.assoc, w, Category.assoc]
      have hz := congrArg (fun a => a.f j) (cokernel.condition (inclusion K Q))
      change (inclusion K Q).f j ≫ (projection K Q).f j = 0 at hz
      rw [hz, comp_zero])

@[reassoc (attr := simp)]
lemma projection_quotientPrismComponent (i j : ι) :
    (projection K P).f i ≫ quotientPrismComponent K h hs w i j =
      h.hom i j ≫ (projection K Q).f j := by
  unfold quotientPrismComponent
  rw [← Category.assoc]
  change ((HomologicalComplex.eval C c i).map (cokernel.π (inclusion K P)) ≫
    (PreservesCokernel.iso _ _).hom) ≫ _ = _
  rw [PreservesCokernel.π_iso_hom]
  exact cokernel.π_desc _ _ _

/-- Passing a compatible homotopy to relative complexes. -/
def quotientPrism : _root_.Homotopy (relativeMap K g) (relativeMap K f) where
  hom := quotientPrismComponent K h hs w
  zero i j hij := by
    apply (cancel_epi ((projection K P).f i)).mp
    simp [h.zero i j hij]
  comm i := by
    apply (cancel_epi ((projection K P).f i)).mp
    have wf (k : P ⟶ Q) : (projection K P).f i ≫ (relativeMap K k).f i =
        (K.map k.map).f i ≫ (projection K Q).f i :=
      congrArg (fun a => a.f i) (projection_map K k)
    rw [wf, Preadditive.comp_add, Preadditive.comp_add, wf]
    rw [← dNext_comp_left, ← prevD_comp_left]
    simp_rw [projection_quotientPrismComponent]
    rw [dNext_comp_right, prevD_comp_right,
      ← Preadditive.add_comp, ← Preadditive.add_comp, ← h.comm]
end Quotient

theorem relative : Expected.relative.{u,v,w} := by
  intro R _ M _ _ P Q f g H
  refine ⟨ordinaryPrism R M H.homotopy, reducedPrism R M H.homotopy,
    quotientPrism (ordinaryFunctor R M) (ordinaryPrism R M H.homotopy)
      (ordinaryPrism R M (restrictHomotopy H)) (ordinaryPrism_subspace R M H),
    quotientPrism (reducedFunctor R M) (reducedPrism R M H.homotopy)
      (reducedPrism R M (restrictHomotopy H)) (reducedPrism_subspace R M H),
    reducedPrism_minus_one R M H.homotopy, ?_, ?_⟩
  · exact projection_quotientPrismComponent (ordinaryFunctor R M)
      (ordinaryPrism R M H.homotopy) (ordinaryPrism R M (restrictHomotopy H))
      (ordinaryPrism_subspace R M H)
  · exact projection_quotientPrismComponent (reducedFunctor R M)
      (reducedPrism R M H.homotopy) (reducedPrism R M (restrictHomotopy H))
      (reducedPrism_subspace R M H)

theorem relativeHomology : Expected.relativeHomology.{u,v,w} := by
  intro R _ M _ _ P Q f g H n
  obtain ⟨_, _, a, b, _⟩ := relative R M H
  exact ⟨(a.homologyMap_eq n).symm, (b.homologyMap_eq n).symm⟩

theorem homology : Expected.homology.{u,v,w} := by
  intro R _ M _ _ X Y f g H n
  exact ⟨((ordinaryPrism R M H).homologyMap_eq n).symm,
    ((reducedPrism R M H).homologyMap_eq n).symm⟩

/-- The inverse is the map induced by the chosen homotopy inverse. -/
lemma homologyIso {X Y : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : TopCat.Homotopy (f ≫ g) (𝟙 X))
    (hgf : TopCat.Homotopy (g ≫ f) (𝟙 Y)) (n : ℤ) :
    IsIso ((homologyFunctor R M n).map f) ∧
      IsIso ((reducedHomologyFunctor R M n).map f) := by
  have h₁ := homology R M hfg n
  have h₂ := homology R M hgf n
  constructor
  · exact ⟨⟨(homologyFunctor R M n).map g,
      by simpa using h₁.1, by simpa using h₂.1⟩⟩
  · exact ⟨⟨(reducedHomologyFunctor R M n).map g,
      by simpa using h₁.2, by simpa using h₂.2⟩⟩

theorem equivalence : Expected.equivalence.{u,v,w} := by
  intro R _ M _ _ X Y f g hfg hgf n
  exact homologyIso R M f g hfg hgf n

theorem contractible : Expected.contractible.{u,v,w} := by
  intro R _ M _ _ X _ _ n
  obtain ⟨x, ⟨H⟩⟩ := id_nullhomotopic X
  let p : X ⟶ P202Specs.SingularDegreeZero.point.{w} :=
    TopCat.ofHom (ContinuousMap.const _ PUnit.unit)
  let q : P202Specs.SingularDegreeZero.point.{w} ⟶ X :=
    TopCat.ofHom (ContinuousMap.const _ x)
  have hpq : TopCat.Homotopy (p ≫ q) (𝟙 X) := H.symm
  have hqp : TopCat.Homotopy (q ≫ p) (𝟙 _) :=
    ContinuousMap.Homotopy.refl _
  have := (homologyIso R M p q hpq hqp n).2
  exact (asIso ((reducedHomologyFunctor R M n).map p)).isZero_iff.mpr
    (P202.SingularDegreeZero.pointReduced R M n)

end P202.PrismHomotopy
