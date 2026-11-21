import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GrothendieckSpectralSequence
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.HypercohomologyDerivedNaturality
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.RightDerivedComposition

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.checkUnivs false
universe u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AdvancedHomologicalAlgebra.GrothendieckSpectralSequence
open HypercohomologyDerivedNaturality CartanEilenbergData
open FiniteFiltrationConvergence
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Abelian A] [Category.{v₂} B] [Abelian B]
  [Category.{v₃} C] [Abelian C]
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B] [HasDerivedCategory.{w₃} C]
  [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]

/-- The row construction inverts quasi-isomorphisms as complete diagrams. -/
lemma complexInverts (S : System G) :
    (CochainComplex.Plus.quasiIso B).IsInvertedBy (rowFunctor G S) :=
  fun _ _ f hf => rowFunctor_isIso G S f hf

/-- Localize the whole row diagram, including its filtration steps. -/
def descendedRow (S : System G) : DerivedRow G where
  system := S
  resolution := chosenResolution G S
  complexes := rowFunctor G S
  derived := Localization.lift (rowFunctor G S)
    (complexInverts G S) DerivedCategory.Plus.Q
  obj_eq _ := rfl
  map_eq f := ⟨chosenLift G S f, chosenLift_isLift G S f, HEq.rfl⟩
  factors := Localization.fac (rowFunctor G S)
    (complexInverts G S) DerivedCategory.Plus.Q

/-- Derived homology of QK is ordinary homology of K. -/
def homologyFactors (q : ℤ) :
    DerivedCategory.Plus.Q (C := B) ⋙ DerivedCategory.Plus.homologyFunctor B q ≅
      CochainComplex.Plus.ι B ⋙ HomologicalComplex.homologyFunctor B (.up ℤ) q :=
  isoWhiskerLeft (CochainComplex.Plus.ι B) (DerivedCategory.homologyFunctorFactors B q)

/-- The natural E₂ calculation before localization. -/
def complexSecondIso (S : System G) (p : ℕ) (q : ℤ) :
    rowFunctor G S ⋙ pageEval 0 (p : ℤ) ((p : ℤ)+q) ≅
      DerivedCategory.Plus.Q ⋙
        (DerivedCategory.Plus.homologyFunctor B q ⋙ rightValue G p) :=
  NatIso.ofComponents (fun K =>
    ((S.data K (chosenResolution G S K)).secondIso p q) ≪≫
      (rightValue G p).mapIso ((homologyFactors (B := B) q).app K).symm) (by
    intro K L f
    change (S.lift (chosenResolution G S K) (chosenResolution G S L)
        (chosenLift G S f)).maps.map 2 (p:ℤ) ((p:ℤ)+q) ≫
        (((S.data L (chosenResolution G S L)).secondIso p q).hom ≫
          (rightValue G p).map ((homologyFactors (B := B) q).app L).inv) =
      (((S.data K (chosenResolution G S K)).secondIso p q).hom ≫
          (rightValue G p).map ((homologyFactors (B := B) q).app K).inv) ≫
        (rightValue G p).map
          ((DerivedCategory.Plus.homologyFunctor B q).map (DerivedCategory.Plus.Q.map f))
    rw [← Category.assoc, S.second_naturality _ _ f _ (chosenLift_isLift G S f) p q]
    simp only [Category.assoc]
    congr 1
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (rightValue G p).map ((homologyFactors (B := B) q).inv.naturality f))

/-- The ambient target is already the fixed RG target before localization. -/
def complexTargetIso (S : System G) (n : ℤ) :
    rowFunctor G S ⋙ targetEval n ≅ DerivedCategory.Plus.Q ⋙
      (G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C n) :=
  Iso.refl _

/-- Localization transports the natural second-page calculation. -/
def derivedSecondIso (S : System G) (p : ℕ) (q : ℤ) :
    (descendedRow G S).derived ⋙ pageEval 0 (p : ℤ) ((p : ℤ)+q) ≅
      DerivedCategory.Plus.homologyFunctor B q ⋙ rightValue G p := by
  letI : Localization.Lifting (DerivedCategory.Plus.Q (C := B))
      (CochainComplex.Plus.quasiIso B) (rowFunctor G S) (descendedRow G S).derived :=
    ⟨(descendedRow G S).factors⟩
  exact Localization.liftNatIso DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso B)
    _ _ _ _ (complexSecondIso G S p q)

/-- Localization also transports the identification of the whole target. -/
def derivedTargetIso (S : System G) (n : ℤ) :
    (descendedRow G S).derived ⋙ targetEval n ≅
      G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C n := by
  letI : Localization.Lifting (DerivedCategory.Plus.Q (C := B))
      (CochainComplex.Plus.quasiIso B) (rowFunctor G S) (descendedRow G S).derived :=
    ⟨(descendedRow G S).factors⟩
  exact Localization.liftNatIso DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso B)
    _ _ _ _ (complexTargetIso G S n)

private lemma descendedRow_complexIso (S : System G) (K : CochainComplex.Plus B) :
    DerivedRow.complexIso G (descendedRow G S) K = (descendedRow G S).factors.app K :=
  Iso.trans_refl _

/-- The localization comparison retains the calculated coordinates on every
bounded-below complex. The row diagram already uses the augmented total
comparison in its filtration inclusions, so the complex-level target map is
the identity in those coordinates. -/
def rowCoordinates (S : System G) : RowCoordinates G (descendedRow G S) where
  second := derivedSecondIso G S
  second_eq K p q := by
    simp only [derivedSecondIso, Localization.liftNatIso_hom, Localization.liftNatTrans_app,
      Localization.Lifting.compRight_iso, Localization.Lifting.compLeft_iso,
      isoWhiskerRight_hom, whiskerRight_app, Iso.refl_inv, NatTrans.id_app, Category.comp_id]
    rw [descendedRow_complexIso]
    rfl
  target := derivedTargetIso G S
  target_eq K n := by
    simp only [derivedTargetIso, Localization.liftNatIso_hom, Localization.liftNatTrans_app,
      Localization.Lifting.compRight_iso, Localization.Lifting.compLeft_iso,
      isoWhiskerRight_hom, whiskerRight_app, complexTargetIso, Iso.refl_hom, Iso.refl_inv,
      NatTrans.id_app, Category.comp_id, descendedRow_complexIso]
    rfl

local instance : (DerivedCategory.Plus.Q (C := B)).EssSurj :=
  Localization.essSurj _ (CochainComplex.Plus.quasiIso B)

/-- Every derived object has a full convergent row realization. -/
def realization (R : DerivedRow G) (Y : DerivedCategory.Plus B) :
    R.derived.obj Y ≅ diagram G
      (R.system.data (DerivedCategory.Plus.Q.objPreimage Y)
        (R.resolution (DerivedCategory.Plus.Q.objPreimage Y))) := by
  letI := Localization.essSurj (DerivedCategory.Plus.Q (C := B))
    (CochainComplex.Plus.quasiIso B)
  exact R.derived.mapIso (DerivedCategory.Plus.Q.objObjPreimageIso Y).symm ≪≫
    DerivedRow.complexIso G R (DerivedCategory.Plus.Q.objPreimage Y)

lemma diagram_finite {K : CochainComplex.Plus B} {R : ResolutionData K.obj}
    (M : Data G K R) (n : ℤ) : ∃ a b : ℤ,
      (∀ p, p ≤ a → IsIso ((diagram G M).inclusion p n)) ∧
      (∀ p, b ≤ p → IsZero ((diagram G M).step p n)) := by
  obtain ⟨a,b,ha,hb⟩ := M.convergence.target.finite n
  refine ⟨a,b,?_,?_⟩
  · intro p hp
    haveI : IsIso (cohomologyPiece M.filtration p n).arrow :=
      (Subobject.isIso_arrow_iff_eq_top _).mpr (ha p hp)
    change IsIso ((cohomologyPiece M.filtration p n).arrow ≫ (M.targetIso n).hom)
    infer_instance
  · intro p hp
    change IsZero (cohomologyPiece M.filtration p n : C)
    rw [hb p hp]
    exact IsZero.of_iso (isZero_zero C) Subobject.botCoeIsoZero

/-- Finiteness is invariant under isomorphisms of the complete diagrams. -/
lemma finite_of_iso {X Y : RowDiagram C} (e : X ≅ Y)
    (h : ∀ n, ∃ a b : ℤ,
      (∀ p, p ≤ a → IsIso (Y.inclusion p n)) ∧
      (∀ p, b ≤ p → IsZero (Y.step p n))) :
    ∀ n, ∃ a b : ℤ,
      (∀ p, p ≤ a → IsIso (X.inclusion p n)) ∧
      (∀ p, b ≤ p → IsZero (X.step p n)) := by
  intro n
  obtain ⟨a,b,ha,hb⟩ := h n
  refine ⟨a,b,?_,?_⟩
  · intro p hp
    haveI := ha p hp
    haveI : IsIso (e.hom.step p n) := ((stepEval p n).mapIso e).isIso_hom
    haveI : IsIso (e.hom.target n) := ((targetEval n).mapIso e).isIso_hom
    apply (isIso_comp_right_iff (X.inclusion p n) (e.hom.target n)).mp
    rw [← e.hom.inclusion_comm]
    infer_instance
  · intro p hp
    exact IsZero.of_iso (hb p hp) ((stepEval p n).mapIso e)

lemma mono_of_iso {X Y : RowDiagram C} (e : X ≅ Y)
    (h : ∀ p n, Mono (Y.inclusion p n)) : ∀ p n, Mono (X.inclusion p n) := by
  intro p n
  haveI := h p n
  haveI : IsIso (e.hom.step p n) := ((stepEval p n).mapIso e).isIso_hom
  haveI : IsIso (e.hom.target n) := ((targetEval n).mapIso e).isIso_hom
  haveI : Mono (X.inclusion p n ≫ e.hom.target n) := by
    rw [← e.hom.inclusion_comm]
    infer_instance
  exact mono_of_mono (X.inclusion p n) (e.hom.target n)

/-- The late pages of each actual row model are its graded cohomology. -/
lemma diagram_converges {K : CochainComplex.Plus B} {R : ResolutionData K.obj}
    (M : Data G K R) : Converges (diagram G M) := by
  intro n
  obtain ⟨Rs,hs,hstab⟩ := M.convergence.stabilization n
  obtain ⟨Rd,hd,hdiff⟩ := M.convergence.differential M.pages n
  refine ⟨(max Rs Rd).toNat, ?_⟩
  intro r hr p
  have hs' : Rs ≤ (r : ℤ)+2 := by omega
  have hd' : Rd ≤ (r : ℤ)+2 := by omega
  refine ⟨hdiff _ (by omega) hd' p, ?_⟩
  obtain ⟨e⟩ := M.convergence.limit M.pages ((r:ℤ)+2) p n (by omega)
    (hstab _ hs' p)
  exact ⟨e.iso⟩

/-- Convergence transports along a simultaneous page and filtration isomorphism. -/
lemma converges_of_iso {X Y : RowDiagram C} (e : X ≅ Y) (h : Converges Y) :
    Converges X := by
  intro n
  obtain ⟨N,hN⟩ := h n
  refine ⟨N, ?_⟩
  intro r hr p
  obtain ⟨hd, ⟨el⟩⟩ := hN r hr p
  haveI : IsIso (e.hom.page r (p+((r:ℤ)+2)) (n+1)) :=
    ((pageEval r (p+((r:ℤ)+2)) (n+1)).mapIso e).isIso_hom
  refine ⟨?_, ⟨(pageEval r p n).mapIso e ≪≫ el ≪≫
    (cokernel.mapIso (X.down p n) (Y.down p n)
      ((stepEval (p+1) n).mapIso e) ((stepEval p n).mapIso e)
      (e.hom.down_comm p n).symm).symm⟩⟩
  apply (cancel_mono (e.hom.page r (p+((r:ℤ)+2)) (n+1))).1
  rw [← e.hom.differential_comm, hd, comp_zero, zero_comp]

/-- All filtration transition maps commute with their inclusions. -/
lemma derived_down_inclusion (R : DerivedRow G) (Y : DerivedCategory.Plus B) (p n : ℤ) :
    (R.derived.obj Y).down p n ≫ (R.derived.obj Y).inclusion p n =
      (R.derived.obj Y).inclusion (p+1) n := by
  let e := realization G R Y
  haveI : IsIso (e.hom.target n) := ((targetEval n).mapIso e).isIso_hom
  apply (cancel_mono (e.hom.target n)).1
  rw [Category.assoc, ← e.hom.inclusion_comm, ← Category.assoc,
    ← e.hom.down_comm, Category.assoc]
  change e.hom.step (p+1) n ≫
      ((diagram G (R.system.data _ _)).down p n ≫
        (diagram G (R.system.data _ _)).inclusion p n) = _
  simp only [diagram, Subobject.ofLE_arrow_assoc]
  exact e.hom.inclusion_comm (p+1) n

/-- Assemble G03 applied to RF and pull its filtration back along R12. -/
theorem grothendieck : Specs.FullStatement.{u₁,v₁,u₂,v₂,u₃,v₃,w₁,w₂,w₃} := by
  intro A B C _ _ _ _ _ _ _ _ _ _ _ F G _ _ _ _ hacyc
  obtain ⟨S, _⟩ := (HypercohomologyDerivedNaturality.hypercohomology).2 B C G
  let R := descendedRow G S
  have hc := (RightDerivedComposition.comparisonIsoIff A B C F G).mpr hacyc
  letI := hc
  letI : IsIso (_root_.Specs.AdvancedHomologicalAlgebra.RightDerivedComposition.comparisonValue F G) :=
    NatIso.isIso_of_isIso_app _
  let coords : RowCoordinates G R := rowCoordinates G S
  let ei : ∀ n, sequence F G R ⋙ targetEval n ≅ iteratedValue F G n :=
    fun n => associator _ _ _ ≪≫
      isoWhiskerLeft F.rightDerivedFunctorPlus (coords.target n) ≪≫ (associator _ _ _).symm
  refine ⟨{
    row := R
    secondIso := fun p q => associator _ _ _ ≪≫
      isoWhiskerLeft F.rightDerivedFunctorPlus (coords.second p q) ≪≫ (associator _ _ _).symm
    coordinates := coords
    second_eq := fun _ _ => rfl
    negative := ?_
    comparison_isIso := hc
    iteratedIso := ei
    iterated_eq := fun _ => rfl
    targetIso := fun n => ei n ≪≫ isoWhiskerRight
      (asIso (_root_.Specs.AdvancedHomologicalAlgebra.RightDerivedComposition.comparisonValue F G)).symm
      (DerivedCategory.Plus.homologyFunctor C n)
    canonical := fun _ => rfl
    convergence := ?_
    down_inclusion := fun X => derived_down_inclusion G R (F.rightDerivedFunctorPlus.obj X)
    inclusion_mono := ?_
    finite := ?_ }⟩
  · intro X p q hp
    let e := (pageEval 0 p (p+q)).mapIso (realization G R (F.rightDerivedFunctorPlus.obj X))
    exact IsZero.of_iso (S.data _ _ |>.negative p q hp) e
  · intro X
    apply converges_of_iso (realization G R (F.rightDerivedFunctorPlus.obj X))
    exact diagram_converges G _
  · intro X
    apply mono_of_iso (realization G R (F.rightDerivedFunctorPlus.obj X))
    intro p n
    apply diagram_inclusion_mono
  · intro X
    apply finite_of_iso (realization G R (F.rightDerivedFunctorPlus.obj X))
    exact fun n => diagram_finite G _ n

end AdvancedHomologicalAlgebra.GrothendieckSpectralSequence
