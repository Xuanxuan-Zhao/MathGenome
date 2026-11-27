import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.AmitsurTotalComplex
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.AmitsurTruncationTower
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! The good truncation tower and the limit of its Amitsur totalizations. -/

open CategoryTheory Limits Opposite

namespace DerivedFormalization.Descent.AmitsurTruncationTower

universe u v w s

variable {A : Type u} [CommRing A]

noncomputable section

abbrev stage := @AmitsurTruncationTowerSpec.stage.{u, w}
abbrev projection := @AmitsurTruncationTowerSpec.projection.{u, w}
abbrev transition := @AmitsurTruncationTowerSpec.transition.{u, w}
abbrev tower := @AmitsurTruncationTowerSpec.tower.{u, w}
abbrev towerMap := @AmitsurTruncationTowerSpec.towerMap.{u, w}
abbrev truncationCone := @AmitsurTruncationTowerSpec.truncationCone.{u, w}
abbrev truncationComparison := @AmitsurTruncationTowerSpec.truncationComparison.{u, w}
abbrev totalTower := @AmitsurTruncationTowerSpec.totalTower.{u, v, w}
abbrev augmentationOfTowers := @AmitsurTruncationTowerSpec.augmentationOfTowers.{u, v, w}
abbrev totalCone := @AmitsurTruncationTowerSpec.totalCone.{u, v, w}
abbrev totalComparison := @AmitsurTruncationTowerSpec.totalComparison.{u, v, w}

variable (X : CochainComplex (ModuleCat.{w} A) ℤ)

@[reassoc (attr := simp)]
theorem projection_transition {m n : ℕ} (h : m ≤ n) :
    projection X n ≫ transition X h = projection X m :=
  AmitsurTruncationTowerSpec.projection_transition X h

@[reassoc]
theorem projection_naturality {X Y : CochainComplex (ModuleCat.{w} A) ℤ} (f : X ⟶ Y) (j : ℕᵒᵖ) :
    (truncationCone X).π.app j ≫ (towerMap f).app j = f ≫ (truncationCone Y).π.app j :=
  CochainComplex.πTruncGE_naturality f (-(j.unop : ℤ))

theorem stage_below (n : ℕ) (q : ℤ) (h : q < -(n : ℤ)) : IsZero ((stage X n).X q) :=
  (stage X n).isZero_of_isStrictlyGE _ _ h

theorem projection_f_above (n : ℕ) (q : ℤ) (h : -(n : ℤ) < q) :
    (projection X n).f q = (X.truncGEXIso (-(n : ℤ)) q h).inv := by
  let e := ComplexShape.embeddingUpIntGE (-(n : ℤ))
  let i := (q - (-(n : ℤ))).natAbs
  have hi : e.f i = q := by
    change -(n : ℤ) + (i : ℤ) = q
    dsimp [i]
    rw [Int.natAbs_of_nonneg (by omega)]
    omega
  have hb : ¬ e.BoundaryGE i := by
    change ¬ (ComplexShape.embeddingUpIntGE (-(n : ℤ))).BoundaryGE i
    rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff]
    dsimp [i]
    rw [Int.natAbs_eq_zero]
    omega
  change (e.liftExtend _ (X.restrictionToTruncGE'_hasLift e)).f q = _
  rw [e.liftExtend_f _ _ hi, X.restrictionToTruncGE'_f_eq_iso_hom_iso_inv e hi hb]
  simp [CochainComplex.truncGEXIso, HomologicalComplex.truncGEXIso, e, i]
  rfl

theorem projection_above (n : ℕ) (q : ℤ) (h : -(n : ℤ) < q) :
    IsIso ((projection X n).f q) := by
  rw [projection_f_above X n q h]
  infer_instance

theorem transition_above {m n : ℕ} (h : m ≤ n) (q : ℤ) (hq : -(m : ℤ) < q) :
    (X.truncGEXIso (-(n : ℤ)) q (by omega)).hom ≫
      (X.truncGEXIso (-(m : ℤ)) q hq).inv = (transition X h).f q := by
  have hn : -(n : ℤ) < q := by omega
  let e := X.truncGEXIso (-(n : ℤ)) q hn
  apply (cancel_epi e.inv).mp
  have eq := congrArg (fun f : X ⟶ stage X m => f.f q) (projection_transition X h)
  simp only [HomologicalComplex.comp_f, projection_f_above X n q hn,
    projection_f_above X m q hq] at eq
  simpa [e] using eq.symm

private theorem projection_f_boundary (n : ℕ) :
    (projection X n).f (-(n : ℤ)) =
      X.pOpcycles (-(n : ℤ)) ≫ (X.truncGEXIsoOpcycles (-(n : ℤ))).inv := by
  let e := ComplexShape.embeddingUpIntGE (-(n : ℤ))
  have hi : e.f 0 = -(n : ℤ) := by simp [e]
  have hb : e.BoundaryGE 0 := by
    change (ComplexShape.embeddingUpIntGE (-(n : ℤ))).BoundaryGE 0
    rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff]
  change (e.liftExtend _ (X.restrictionToTruncGE'_hasLift e)).f (-(n : ℤ)) = _
  rw [e.liftExtend_f _ _ hi, X.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv e hi hb]
  simp [CochainComplex.truncGEXIsoOpcycles, HomologicalComplex.truncGEXIsoOpcycles, e]
  rfl

theorem boundary_condition (n : ℕ) :
    X.d (-(n : ℤ) - 1) (-(n : ℤ)) ≫ (projection X n).f (-(n : ℤ)) = 0 := by
  rw [projection_f_boundary, ← Category.assoc, X.d_pOpcycles, zero_comp]

/-- At the cutoff the projection is the cokernel of the incoming differential. -/
def stage_boundary (n : ℕ) :
    IsColimit (CokernelCofork.ofπ _ (boundary_condition X n)) := by
  let q : ℤ := -(n : ℤ)
  let e := X.truncGEXIsoOpcycles q
  apply IsColimit.ofIsoColimit (X.opcyclesIsCokernel (q - 1) q (by simp))
  exact Cofork.ext e.symm (projection_f_boundary X n).symm

theorem stage_boundary_isCokernel (n : ℕ) :
    ∃ h : X.d (-(n : ℤ) - 1) (-(n : ℤ)) ≫ (projection X n).f (-(n : ℤ)) = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ _ h)) :=
  ⟨boundary_condition X n, ⟨stage_boundary X n⟩⟩

theorem transition_surjective {m n : ℕ} (h : m ≤ n) (q : ℤ) :
    Function.Surjective ((transition X h).f q) := by
  have hproj (k : ℕ) : Epi ((projection X k).f q) :=
    inferInstanceAs (Epi ((HomologicalComplex.πTruncGE X
      (ComplexShape.embeddingUpIntGE (-(k : ℤ)))).f q))
  have hf : (projection X n).f q ≫ (transition X h).f q = (projection X m).f q :=
    congrArg (fun f : X ⟶ stage X m => f.f q) (projection_transition X h)
  have : Epi ((projection X n).f q ≫ (transition X h).f q) := hf.symm ▸ hproj m
  exact (ModuleCat.epi_iff_surjective _).mp (epi_of_epi ((projection X n).f q) _)

private abbrev evaluation (q : ℤ) :
    CochainComplex (ModuleCat.{w} A) ℤ ⥤ ModuleCat.{w} A :=
  HomologicalComplex.eval _ _ q

private theorem cutoff (q : ℤ) : -((q.natAbs + 1 : ℕ) : ℤ) < q := by
  have := @Int.le_natAbs (-q)
  simp only [Int.natAbs_neg] at this
  omega

private theorem evaluation_eventuallyConstant (q : ℤ) (m : ℕ) (hq : -(m : ℤ) < q) :
    (tower X ⋙ evaluation (A := A) q).IsEventuallyConstantTo (op m) := by
  intro i f
  change IsIso ((transition X f.unop.le).f q)
  rw [← transition_above X f.unop.le q hq]
  infer_instance

/-- The original complex, with its canonical projections, is the inverse limit. -/
def truncationConeIsLimit : IsLimit (truncationCone X) :=
  HomologicalComplex.isLimitOfEval _ _ fun q => by
    let m := q.natAbs + 1
    let c := (evaluation (A := A) q).mapCone (truncationCone X)
    have : IsIso (c.π.app (op m)) := projection_above X m q (cutoff q)
    exact (evaluation_eventuallyConstant X q m (cutoff q)).isLimitOfIsIso c

theorem truncationComparison_isIso : IsIso (truncationComparison X) :=
  inferInstanceAs (IsIso ((truncationConeIsLimit X).conePointUniqueUpToIso (limit.isLimit _)).hom)

section Totalization

variable (A) (B : Type v) [CommRing B] [Algebra A B]
variable (Y : AmitsurTotalComplex.Complex.{u, v, w} A)

private theorem degreeMap_surjective {M N : ModuleCat.{max u v w} A} (f : M ⟶ N) (p : ℕ)
    (hf : Function.Surjective f) :
    Function.Surjective (AmitsurComplexSpec.degreeMap A B f p) :=
  TensorProduct.map_surjective (g := LinearMap.id) (g' := f.hom) Function.surjective_id hf

theorem total_transition_surjective {m n : ℕ} (h : m ≤ n) (k : ℤ) :
    Function.Surjective (((totalTower A B Y).map ((homOfLE h).op)).f k) := by
  change Function.Surjective ((AmitsurTotalComplex.map A B (transition Y h)).f k)
  intro y
  choose x hx using fun p : ℕ =>
    degreeMap_surjective A B ((transition Y h).f (AmitsurTotalComplex.rowIndex k p)) p
      (transition_surjective Y h (AmitsurTotalComplex.rowIndex k p)) (y p)
  exact ⟨x, funext fun p => (AmitsurTotalComplex.map_apply A B (transition Y h) k x p).trans (hx p)⟩

end Totalization

section CoefficientLimits

variable {Z : CochainComplex (ModuleCat.{s} A) ℤ}
variable {D : Type*} [Category D]

/-- Any functor preserves the limit of the eventually constant tower in a fixed degree. -/
private def mappedDegreeConeIsLimit (F : ModuleCat.{s} A ⥤ D) (q : ℤ) :
    IsLimit ((evaluation (A := A) q ⋙ F).mapCone (truncationCone Z)) := by
  let m := q.natAbs + 1
  have h : ((tower Z ⋙ evaluation (A := A) q) ⋙ F).IsEventuallyConstantTo (op m) := by
    intro i f
    have := evaluation_eventuallyConstant Z q m (cutoff q) f
    exact F.map_isIso ((tower Z ⋙ evaluation (A := A) q).map f)
  have : IsIso (((evaluation (A := A) q ⋙ F).mapCone (truncationCone Z)).π.app (op m)) := by
    have := projection_above Z m q (cutoff q)
    exact F.map_isIso ((projection Z m).f q)
  exact h.isLimitOfIsIso ((evaluation (A := A) q ⋙ F).mapCone (truncationCone Z))

end CoefficientLimits

section TotalizationLimits

variable (A) (B : Type v) [CommRing B] [Algebra A B]
variable (Z : CochainComplex (ModuleCat.{s} A) ℤ)
variable (F : ModuleCat.{s} A ⥤ ModuleCat.{max u v w} A) [F.PreservesZeroMorphisms]

/-- Tensoring with the ordered tensor power in column p after applying the coefficient functor. -/
private abbrev coefficientFunctor (p : ℕ) : ModuleCat.{s} A ⥤ ModuleCat.{max u v w} A :=
  F ⋙ AmitsurComplexSpec.functor A B ⋙ evaluation (A := A) (p : ℤ)

private abbrev mappedTotalFunctor :=
  F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ AmitsurTotalComplex.functor.{u, v, w} A B

private abbrev cellDiagram (p : ℕ) (q : ℤ) : ℕᵒᵖ ⥤ ModuleCat.{max u v w} A :=
  tower Z ⋙ (evaluation (A := A) q ⋙ coefficientFunctor.{u, v, w, s} A B F p)

private abbrev cellCone (p : ℕ) (q : ℤ) : Cone (cellDiagram.{u, v, w, s} A B Z F p q) :=
  (evaluation (A := A) q ⋙ coefficientFunctor.{u, v, w, s} A B F p).mapCone (truncationCone Z)

private abbrev totalDiagram (k : ℤ) : ℕᵒᵖ ⥤ ModuleCat.{max u v w} A :=
  (tower Z ⋙ mappedTotalFunctor.{u, v, w, s} A B F) ⋙ evaluation (A := A) k

private abbrev totalDegreeCone (k : ℤ) : Cone (totalDiagram.{u, v, w, s} A B Z F k) :=
  (evaluation (A := A) k).mapCone ((mappedTotalFunctor.{u, v, w, s} A B F).mapCone (truncationCone Z))

private abbrev columnProjection (Y : AmitsurTotalComplex.Complex.{u, v, w} A) (k : ℤ) (p : ℕ) :
    (AmitsurTotalComplex.total A B Y).X k ⟶
      AmitsurTotalComplexSpec.cell A B Y p (AmitsurTotalComplex.rowIndex k p) :=
  ModuleCat.ofHom (LinearMap.proj p)

private def totalToCell (k : ℤ) (p : ℕ) :
    totalDiagram.{u, v, w, s} A B Z F k ⟶ cellDiagram.{u, v, w, s} A B Z F p (AmitsurTotalComplex.rowIndex k p) where
  app j := columnProjection.{u, v, w} A B ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj ((tower Z).obj j)) k p
  naturality i j f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact AmitsurTotalComplex.map_apply.{u, v, w} A B ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map ((tower Z).map f)) k x p

@[reassoc]
private theorem columnProjection_comm (k : ℤ) (p : ℕ) (j : ℕᵒᵖ) :
    (totalDegreeCone.{u, v, w, s} A B Z F k).π.app j ≫ (totalToCell.{u, v, w, s} A B Z F k p).app j =
      columnProjection.{u, v, w} A B ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z) k p ≫
        (cellCone.{u, v, w, s} A B Z F p (AmitsurTotalComplex.rowIndex k p)).π.app j := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact AmitsurTotalComplex.map_apply.{u, v, w} A B ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (projection Z j.unop)) k x p

set_option backward.isDefEq.respectTransparency false in
/-- A cone over a diagonal of products is determined by its projections
to the towers of the individual cells. -/
private def totalDegreeConeIsLimit (k : ℤ) : IsLimit (totalDegreeCone.{u, v, w, s} A B Z F k) := by
  let q (p : ℕ) := AmitsurTotalComplex.rowIndex k p
  let hc (p : ℕ) := mappedDegreeConeIsLimit (Z := Z) (coefficientFunctor.{u, v, w, s} A B F p) (q p)
  let sCell (c : Cone (totalDiagram.{u, v, w, s} A B Z F k)) (p : ℕ) :=
    (Cone.postcompose (totalToCell.{u, v, w, s} A B Z F k p)).obj c
  let lift (c : Cone (totalDiagram.{u, v, w, s} A B Z F k)) :
      c.pt ⟶ (totalDegreeCone.{u, v, w, s} A B Z F k).pt :=
    ModuleCat.ofHom (LinearMap.pi fun p => ((hc p).lift (sCell c p)).hom)
  have lift_proj (c : Cone (totalDiagram.{u, v, w, s} A B Z F k)) (p : ℕ) :
      lift c ≫ columnProjection.{u, v, w} A B ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z) k p =
        (hc p).lift (sCell c p) := rfl
  refine { lift := lift, fac := ?_, uniq := ?_ }
  · intro c j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext p
    have eq := (hc p).fac (sCell c p) j
    rw [← lift_proj, Category.assoc, ← columnProjection_comm] at eq
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom eq) x
  · intro c l hl
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext p
    have eq : l ≫ columnProjection.{u, v, w} A B ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z) k p =
        lift c ≫ columnProjection.{u, v, w} A B ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z) k p := by
      apply (hc p).hom_ext
      intro j
      rw [Category.assoc, ← columnProjection_comm, ← Category.assoc, hl, lift_proj]
      exact ((hc p).fac (sCell c p) j).symm
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom eq) x

private def mappedTotalConeIsLimit :
    IsLimit ((mappedTotalFunctor.{u, v, w, s} A B F).mapCone (truncationCone Z)) :=
  HomologicalComplex.isLimitOfEval _ _ (totalDegreeConeIsLimit.{u, v, w, s} A B Z F)

end TotalizationLimits

section Totalization

variable (A) (B : Type v) [CommRing B] [Algebra A B]
variable (Y : AmitsurTotalComplex.Complex.{u, v, w} A)

/-- The product totalization of the original complex is the limit of the
totalizations of its good truncations. -/
def totalConeIsLimit : IsLimit (totalCone A B Y) :=
  mappedTotalConeIsLimit.{u, v, w, max u v w} A B Y (𝟭 _)

theorem totalComparison_isIso : IsIso (totalComparison A B Y) :=
  inferInstanceAs (IsIso ((totalConeIsLimit A B Y).conePointUniqueUpToIso (limit.isLimit _)).hom)

theorem augmentation_on_cones (j : ℕᵒᵖ) :
    (truncationCone Y).π.app j ≫ (augmentationOfTowers A B Y).app j =
      AmitsurTotalComplex.augmentation A B Y ≫ (totalCone A B Y).π.app j :=
  AmitsurTotalComplex.augmentation_naturality A B (projection Y j.unop)

set_option backward.isDefEq.respectTransparency false in
/-- Under the two canonical limit identifications, the map on limits is the original augmentation. -/
theorem augmentation_on_limits :
    truncationComparison Y ≫ limMap (augmentationOfTowers A B Y) =
      AmitsurTotalComplex.augmentation A B Y ≫ totalComparison A B Y := by
  apply limit.hom_ext
  intro j
  simp only [AmitsurTruncationTowerSpec.truncationComparison,
    AmitsurTruncationTowerSpec.totalComparison, Category.assoc, limMap_π, limit.lift_π_assoc,
    limit.lift_π]
  exact augmentation_on_cones A B Y j

end Totalization

namespace Independent

open AmitsurTotalComplex.Independent (lift tensorMap)

abbrev liftedTower := @AmitsurTruncationTowerSpec.Independent.liftedTower.{u, v, w}
abbrev liftedCone := @AmitsurTruncationTowerSpec.Independent.liftedCone.{u, v, w}
abbrev liftedStageComparison :=
  @AmitsurTruncationTowerSpec.Independent.liftedStageComparison.{u, v, w}
abbrev sourceLimitComparison :=
  @AmitsurTruncationTowerSpec.Independent.sourceLimitComparison.{u, v, w}
abbrev liftedComparison := @AmitsurTruncationTowerSpec.Independent.liftedComparison.{u, v, w}
abbrev totalTower := @AmitsurTruncationTowerSpec.Independent.totalTower.{u, v, w}
abbrev augmentationOfTowers :=
  @AmitsurTruncationTowerSpec.Independent.augmentationOfTowers.{u, v, w}
abbrev totalTowerIso := @AmitsurTruncationTowerSpec.Independent.totalTowerIso.{u, v, w}
abbrev totalCone := @AmitsurTruncationTowerSpec.Independent.totalCone.{u, v, w}
abbrev totalComparison := @AmitsurTruncationTowerSpec.Independent.totalComparison.{u, v, w}

section Lift

variable (A) (B : Type v) (X : CochainComplex (ModuleCat.{w} A) ℤ)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem lifted_projection_comparison (n : ℕ) :
    projection ((lift.{u, v, w} A).obj X) n ≫ liftedStageComparison.{u, v, w} A B X n =
      (lift.{u, v, w} A).map (projection X n) := by
  let L := lift.{u, v, w} A
  have : (L.obj (stage X n)).IsStrictlyGE (-(n : ℤ)) :=
    (stage X n).isStrictlyGE_mapHomologicalComplex_obj_iff
      (ModuleCat.uliftFunctor.{max u v, w} A) (-(n : ℤ)) |>.2 inferInstance
  simp [AmitsurTruncationTowerSpec.Independent.liftedStageComparison,
    AmitsurTruncationTowerSpec.projection, CochainComplex.πTruncGE_naturality_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem liftedStageComparison_isIso (n : ℕ) :
    IsIso (liftedStageComparison.{u, v, w} A B X n) := by
  let L := lift.{u, v, w} A
  let F := ModuleCat.uliftFunctor.{max u v, w} A
  let e := liftedStageComparison.{u, v, w} A B X n
  change IsIso e
  have hcomponents (q : ℤ) : IsIso (e.f q) := by
    have eq : (projection (L.obj X) n).f q ≫ e.f q = F.map ((projection X n).f q) :=
      congrArg (fun f => f.f q) (lifted_projection_comparison.{u, v, w} A B X n)
    rcases lt_trichotomy q (-(n : ℤ)) with h | rfl | h
    · exact (stage_below (L.obj X) n q h).isIso (F.map_isZero (stage_below X n q h)) _
    · let c := stage_boundary (L.obj X) n
      let c' := isColimitCoforkMapOfIsColimit' F (boundary_condition X n) (stage_boundary X n)
      have he : e.f (-(n : ℤ)) = (c.coconePointUniqueUpToIso c').hom := by
        have : Epi ((projection (L.obj X) n).f (-(n : ℤ))) :=
          inferInstanceAs (Epi ((HomologicalComplex.πTruncGE (L.obj X)
            (ComplexShape.embeddingUpIntGE (-(n : ℤ)))).f (-(n : ℤ))))
        exact (cancel_epi ((projection (L.obj X) n).f (-(n : ℤ)))).mp
          (eq.trans (c.comp_coconePointUniqueUpToIso_hom c' WalkingParallelPair.one).symm)
      rw [he]
      infer_instance
    · have := projection_above (L.obj X) n q h
      have := projection_above X n q h
      have : IsIso ((projection (L.obj X) n).f q ≫ e.f q) :=
        eq.symm ▸ F.map_isIso ((projection X n).f q)
      exact IsIso.of_isIso_comp_left ((projection (L.obj X) n).f q) _
  exact HomologicalComplex.Hom.isIso_of_components e

set_option backward.isDefEq.respectTransparency false in
theorem lifted_transition_comparison {m n : ℕ} (h : m ≤ n) :
    transition ((lift.{u, v, w} A).obj X) h ≫ liftedStageComparison.{u, v, w} A B X m =
      liftedStageComparison.{u, v, w} A B X n ≫ (lift.{u, v, w} A).map (transition X h) := by
  let L := lift.{u, v, w} A
  apply (cancel_epi (projection (L.obj X) n)).mp
  rw [projection_transition_assoc, lifted_projection_comparison,
    lifted_projection_comparison_assoc, ← Functor.map_comp, projection_transition]

def liftedConeIsLimit : IsLimit (liftedCone.{u, v, w} A B X) :=
  HomologicalComplex.isLimitOfEval _ _ fun q =>
    mappedDegreeConeIsLimit (Z := X) (ModuleCat.uliftFunctor.{max u v, w} A) q

theorem liftedComparison_isIso : IsIso (liftedComparison.{u, v, w} A B X) :=
  inferInstanceAs (IsIso ((liftedConeIsLimit.{u, v, w} A B X).conePointUniqueUpToIso
    (limit.isLimit _)).hom)

theorem source_comparison :
    (lift.{u, v, w} A).map (truncationComparison X) ≫ sourceLimitComparison.{u, v, w} A B X =
      liftedComparison.{u, v, w} A B X :=
  limit.lift_post (tower X) (lift.{u, v, w} A) (truncationCone X)

theorem sourceLimitComparison_isIso : IsIso (sourceLimitComparison.{u, v, w} A B X) := by
  have := truncationComparison_isIso X
  have h : IsIso ((lift.{u, v, w} A).map (truncationComparison X) ≫
      sourceLimitComparison.{u, v, w} A B X) := (source_comparison A B X).symm ▸ liftedComparison_isIso.{u, v, w} A B X
  exact IsIso.of_isIso_comp_left ((lift.{u, v, w} A).map (truncationComparison X)) _

theorem lifted_transition_surjective {m n : ℕ} (h : m ≤ n) (q : ℤ) :
    Function.Surjective (((liftedTower.{u, v, w} A B X).map ((homOfLE h).op)).f q) := by
  intro y
  obtain ⟨x, hx⟩ := transition_surjective X h q y.down
  exact ⟨ULift.up x, ULift.ext hx⟩

end Lift

variable (A) (B : Type v) [CommRing B] [Algebra A B]
variable (X : CochainComplex (ModuleCat.{w} A) ℤ)

theorem total_transition_surjective {m n : ℕ} (h : m ≤ n) (k : ℤ) :
    Function.Surjective (((totalTower A B X).map ((homOfLE h).op)).f k) := by
  change Function.Surjective ((AmitsurTotalComplex.Independent.map A B (transition X h)).f k)
  have hs (p : ℕ) :
      Function.Surjective (tensorMap A B ((transition X h).f (AmitsurTotalComplex.rowIndex k p)) p) :=
    TensorProduct.map_surjective (g := LinearMap.id) (g' := ((transition X h).f _).hom)
      Function.surjective_id (transition_surjective X h _)
  intro y
  choose x hx using fun p => hs p (y p)
  exact ⟨x, funext fun p =>
    (AmitsurTotalComplex.Independent.map_apply A B (transition X h) k x p).trans (hx p)⟩

/-- The product totalization with the original coefficients is the limit of the
totalizations of their good truncations. -/
def totalConeIsLimit : IsLimit (totalCone A B X) := by
  let F := ModuleCat.uliftFunctor.{max u v, w} A
  let c : Cone (liftedTower.{u, v, w} A B X ⋙ AmitsurTotalComplex.functor A B) :=
    (mappedTotalFunctor.{u, v, w, w} A B F).mapCone (truncationCone X)
  refine (IsLimit.equivOfNatIsoOfIso (totalTowerIso A B X) c (totalCone A B X) ?_)
    (mappedTotalConeIsLimit.{u, v, w, w} A B X F)
  refine Cone.ext (AmitsurTotalComplex.Independent.totalIso A B X) fun j => ?_
  exact (AmitsurTotalComplex.Independent.totalNatIso A B).hom.naturality (projection X j.unop)

theorem totalComparison_isIso : IsIso (totalComparison A B X) :=
  inferInstanceAs (IsIso ((totalConeIsLimit A B X).conePointUniqueUpToIso (limit.isLimit _)).hom)

set_option backward.isDefEq.respectTransparency false in
theorem tower_augmentation_comparison (j : ℕᵒᵖ) :
    (augmentationOfTowers A B X).app j =
      AmitsurTotalComplexSpec.augmentation A B ((liftedTower A B X).obj j) ≫
        (totalTowerIso A B X).hom.app j := by
  change AmitsurTotalComplex.Independent.augmentation A B (stage X j.unop) =
    AmitsurTotalComplexSpec.augmentation A B ((lift.{u, v, w} A).obj (stage X j.unop)) ≫
      (𝟙 _ ≫ (AmitsurTotalComplex.Independent.totalIso A B (stage X j.unop)).hom)
  rw [Category.id_comp, AmitsurTotalComplex.Independent.augmentation_comparison]

theorem augmentation_on_cones (j : ℕᵒᵖ) :
    (liftedCone.{u, v, w} A B X).π.app j ≫ (augmentationOfTowers A B X).app j =
      AmitsurTotalComplex.Independent.augmentation A B X ≫ (totalCone A B X).π.app j :=
  (AmitsurTotalComplex.Independent.naturalAugmentation A B).naturality (projection X j.unop)

set_option backward.isDefEq.respectTransparency false in
/-- The limit of the stagewise augmentations is the augmentation of the original complex,
using the canonical comparison from the lifted limit of the original stages. -/
theorem augmentation_on_limits :
    (lift.{u, v, w} A).map (truncationComparison X) ≫
        sourceLimitComparison.{u, v, w} A B X ≫ limMap (augmentationOfTowers A B X) =
      AmitsurTotalComplex.Independent.augmentation A B X ≫ totalComparison A B X := by
  rw [← Category.assoc, source_comparison A B X]
  apply limit.hom_ext
  intro j
  simp only [AmitsurTruncationTowerSpec.Independent.liftedComparison,
    AmitsurTruncationTowerSpec.Independent.totalComparison, Category.assoc, limMap_π,
    limit.lift_π_assoc, limit.lift_π]
  exact augmentation_on_cones A B X j

end Independent

end

end DerivedFormalization.Descent.AmitsurTruncationTower
