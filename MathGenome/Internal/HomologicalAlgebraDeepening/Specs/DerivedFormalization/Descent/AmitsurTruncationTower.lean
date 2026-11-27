import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.AmitsurTotalComplex
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Category.Preorder

/-! Good truncations and the induced Amitsur tower. -/

open CategoryTheory Limits Opposite

namespace AmitsurTruncationTowerSpec

universe u v w

variable {A : Type u} [CommRing A]

noncomputable section

abbrev stage (X : CochainComplex (ModuleCat.{w} A) ℤ) (n : ℕ) :=
  X.truncGE (-(n : ℤ))

def projection (X : CochainComplex (ModuleCat.{w} A) ℤ) (n : ℕ) : X ⟶ stage X n :=
  X.πTruncGE (-(n : ℤ))

set_option backward.defeqAttrib.useBackward true in
/-- Factor the projection onto stage m through the projection onto stage n.
The target is already strictly supported above the cutoff used for stage n. -/
def transition (X : CochainComplex (ModuleCat.{w} A) ℤ) {m n : ℕ} (h : m ≤ n) :
    stage X n ⟶ stage X m :=
  haveI : (stage X m).IsStrictlyGE (-(n : ℤ)) :=
    (stage X m).isStrictlyGE_of_ge (-(n : ℤ)) (-(m : ℤ)) (by omega)
  CochainComplex.truncGEMap (projection X m) (-(n : ℤ)) ≫
    inv ((stage X m).πTruncGE (-(n : ℤ)))

@[reassoc (attr := simp)]
theorem projection_transition (X : CochainComplex (ModuleCat.{w} A) ℤ)
    {m n : ℕ} (h : m ≤ n) :
    projection X n ≫ transition X h = projection X m := by
  have : (stage X m).IsStrictlyGE (-(n : ℤ)) :=
    (stage X m).isStrictlyGE_of_ge (-(n : ℤ)) (-(m : ℤ)) (by omega)
  simp [transition, projection, CochainComplex.πTruncGE_naturality_assoc]

instance (X : CochainComplex (ModuleCat.{w} A) ℤ) (n : ℕ) : Epi (projection X n) :=
  inferInstanceAs (Epi (HomologicalComplex.πTruncGE X (ComplexShape.embeddingUpIntGE (-(n : ℤ)))))

/-- The inverse system indexed by the opposite of the usual order of the natural numbers. -/
def tower (X : CochainComplex (ModuleCat.{w} A) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{w} A) ℤ where
  obj n := stage X n.unop
  map f := transition X f.unop.le
  map_id n := by
    apply (cancel_epi (projection X n.unop)).mp
    simp
  map_comp {n m k} f g := by
    apply (cancel_epi (projection X n.unop)).mp
    simp

/-- The canonical projections from the original complex to the good truncations. -/
def truncationCone (X : CochainComplex (ModuleCat.{w} A) ℤ) : Cone (tower X) where
  pt := X
  π :=
    { app := fun n => projection X n.unop
      naturality := fun i j f => by
        change 𝟙 X ≫ projection X j.unop = projection X i.unop ≫ transition X f.unop.le
        rw [Category.id_comp]
        exact (projection_transition X f.unop.le).symm }

/-- The map of good truncation towers induced by a map of complexes. -/
def towerMap {X Y : CochainComplex (ModuleCat.{w} A) ℤ} (f : X ⟶ Y) :
    tower X ⟶ tower Y where
  app n := CochainComplex.truncGEMap f (-(n.unop : ℤ))
  naturality i j g := by
    change transition X g.unop.le ≫ CochainComplex.truncGEMap f (-(j.unop : ℤ)) =
      CochainComplex.truncGEMap f (-(i.unop : ℤ)) ≫ transition Y g.unop.le
    apply (cancel_epi (projection X i.unop)).mp
    have proj_nat (n : ℕ) :
        projection X n ≫ CochainComplex.truncGEMap f (-(n : ℤ)) = f ≫ projection Y n :=
      CochainComplex.πTruncGE_naturality f (-(n : ℤ))
    rw [projection_transition_assoc, proj_nat, ← Category.assoc, proj_nat, Category.assoc,
      projection_transition]

/-- The canonical comparison to the chosen categorical limit of the truncations. -/
def truncationComparison (X : CochainComplex (ModuleCat.{w} A) ℤ) : X ⟶ limit (tower X) :=
  limit.lift _ (truncationCone X)

variable (A) (B : Type v) [CommRing B] [Algebra A B]
variable (X : AmitsurTotalComplexSpec.Complex.{u, v, w} A)

/-- Apply the Amitsur totalization functor at each level. -/
def totalTower := tower X ⋙ AmitsurTotalComplexSpec.functor A B

/-- The stagewise Amitsur augmentation as a map of inverse systems. -/
def augmentationOfTowers : tower X ⟶ totalTower A B X where
  app n := AmitsurTotalComplexSpec.augmentation A B ((tower X).obj n)
  naturality _ _ f := (AmitsurTotalComplexSpec.naturalAugmentation A B).naturality
    ((tower X).map f)

/-- The projections obtained by applying the Amitsur functor to those of the original complex. -/
def totalCone : Cone (totalTower A B X) :=
  (AmitsurTotalComplexSpec.functor A B).mapCone (truncationCone X)

/-- The canonical comparison to the chosen limit of the Amitsur totalizations. -/
def totalComparison : AmitsurTotalComplexSpec.total A B X ⟶ limit (totalTower A B X) :=
  limit.lift _ (totalCone A B X)

end

section DeclarationTypes

set_option linter.checkUnivs false

private def declarationType {T : Sort*} (_ : T) := T

def StageType := declarationType (@stage.{u, w})
def ProjectionType := declarationType (@projection.{u, w})
def TransitionType := declarationType (@transition.{u, w})
def TowerType := declarationType (@tower.{u, w})
def TowerMapType := declarationType (@towerMap.{u, w})
def TruncationConeType := declarationType (@truncationCone.{u, w})
def TruncationComparisonType := declarationType (@truncationComparison.{u, w})
def TotalTowerType := declarationType (@totalTower.{u, v, w})
def AugmentationOfTowersType := declarationType (@augmentationOfTowers.{u, v, w})
def TotalConeType := declarationType (@totalCone.{u, v, w})
def TotalComparisonType := declarationType (@totalComparison.{u, v, w})

def ProjectionTransition : Prop :=
  ∀ {A : Type u} [CommRing A] (X : CochainComplex (ModuleCat.{w} A) ℤ) {m n : ℕ} (h : m ≤ n),
    projection X n ≫ transition X h = projection X m

def ProjectionNaturality : Prop :=
  ∀ {A : Type u} [CommRing A] {X Y : CochainComplex (ModuleCat.{w} A) ℤ}
    (f : X ⟶ Y) (j : ℕᵒᵖ),
    (truncationCone X).π.app j ≫ (towerMap f).app j = f ≫ (truncationCone Y).π.app j

def StageBelow : Prop :=
  ∀ {A : Type u} [CommRing A] (X : CochainComplex (ModuleCat.{w} A) ℤ) (n : ℕ) (q : ℤ),
    q < -(n : ℤ) → IsZero ((stage X n).X q)

def StageBoundary : Prop :=
  ∀ {A : Type u} [CommRing A] (X : CochainComplex (ModuleCat.{w} A) ℤ) (n : ℕ),
    ∃ h : X.d (-(n : ℤ) - 1) (-(n : ℤ)) ≫ (projection X n).f (-(n : ℤ)) = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ _ h))

def ProjectionAbove : Prop :=
  ∀ {A : Type u} [CommRing A] (X : CochainComplex (ModuleCat.{w} A) ℤ) (n : ℕ) (q : ℤ)
    (h : -(n : ℤ) < q), (projection X n).f q = (X.truncGEXIso (-(n : ℤ)) q h).inv

def TransitionAbove : Prop :=
  ∀ {A : Type u} [CommRing A] (X : CochainComplex (ModuleCat.{w} A) ℤ)
    {m n : ℕ} (h : m ≤ n) (q : ℤ) (hq : -(m : ℤ) < q),
    (X.truncGEXIso (-(n : ℤ)) q (by omega)).hom ≫
      (X.truncGEXIso (-(m : ℤ)) q hq).inv = (transition X h).f q

def TransitionSurjective : Prop :=
  ∀ {A : Type u} [CommRing A] (X : CochainComplex (ModuleCat.{w} A) ℤ)
    {m n : ℕ} (h : m ≤ n) (q : ℤ), Function.Surjective ((transition X h).f q)

def TotalTransitionSurjective : Prop :=
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B]
    (X : AmitsurTotalComplexSpec.Complex.{u, v, w} A) {m n : ℕ} (h : m ≤ n) (k : ℤ),
    Function.Surjective (((totalTower A B X).map ((homOfLE h).op)).f k)

def TruncationComparisonIsIso : Prop :=
  ∀ {A : Type u} [CommRing A] (X : CochainComplex (ModuleCat.{w} A) ℤ),
    IsIso (truncationComparison X)

def TotalComparisonIsIso : Prop :=
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B]
    (X : AmitsurTotalComplexSpec.Complex.{u, v, w} A), IsIso (totalComparison A B X)

def AugmentationOnCones : Prop :=
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B]
    (X : AmitsurTotalComplexSpec.Complex.{u, v, w} A) (j : ℕᵒᵖ),
    (truncationCone X).π.app j ≫ (augmentationOfTowers A B X).app j =
      AmitsurTotalComplexSpec.augmentation A B X ≫ (totalCone A B X).π.app j

def AugmentationOnLimits : Prop :=
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B]
    (X : AmitsurTotalComplexSpec.Complex.{u, v, w} A),
    truncationComparison X ≫ limMap (augmentationOfTowers A B X) =
      AmitsurTotalComplexSpec.augmentation A B X ≫ totalComparison A B X

end DeclarationTypes

namespace Independent

open AmitsurTotalComplexSpec.Independent (lift functor naturalAugmentation totalNatIso)

noncomputable section

section Lift

variable (A)

/-- Lift the original truncations and their transition maps to the category
that contains the tensor products. -/
def liftedTower (_B : Type v) (X : CochainComplex (ModuleCat.{w} A) ℤ) := tower X ⋙ lift.{u, v, w} A

def liftedCone (B : Type v) (X : CochainComplex (ModuleCat.{w} A) ℤ) :
    Cone (liftedTower.{u, v, w} A B X) :=
  (lift.{u, v, w} A).mapCone (truncationCone X)

/-- The lift of the original inverse limit maps to the inverse limit of the lifts. -/
def sourceLimitComparison (B : Type v) (X : CochainComplex (ModuleCat.{w} A) ℤ) :
    (lift.{u, v, w} A).obj (limit (tower X)) ⟶ limit (liftedTower.{u, v, w} A B X) :=
  limit.post (tower X) (lift.{u, v, w} A)

def liftedComparison (B : Type v) (X : CochainComplex (ModuleCat.{w} A) ℤ) :
    (lift.{u, v, w} A).obj X ⟶ limit (liftedTower.{u, v, w} A B X) :=
  limit.lift _ (liftedCone.{u, v, w} A B X)

/-- The projection onto the lift of a good truncation factors through the
good truncation of the lifted complex. -/
def liftedStageComparison (_B : Type v) (X : CochainComplex (ModuleCat.{w} A) ℤ) (n : ℕ) :
    stage ((lift.{u, v, w} A).obj X) n ⟶ (lift.{u, v, w} A).obj (stage X n) :=
  let L := lift.{u, v, w} A
  haveI : (L.obj (stage X n)).IsStrictlyGE (-(n : ℤ)) :=
    (stage X n).isStrictlyGE_mapHomologicalComplex_obj_iff
      (ModuleCat.uliftFunctor.{max u v, w} A) (-(n : ℤ)) |>.2 inferInstance
  CochainComplex.truncGEMap (L.map (projection X n)) (-(n : ℤ)) ≫
    inv ((L.obj (stage X n)).πTruncGE (-(n : ℤ)))

end Lift

variable (A) (B : Type v) [CommRing B] [Algebra A B]
variable (X : CochainComplex (ModuleCat.{w} A) ℤ)

/-- Totalize the original good truncations, with their original coefficient modules. -/
def totalTower := tower X ⋙ functor A B

def augmentationOfTowers : liftedTower.{u, v, w} A B X ⟶ totalTower A B X :=
  Functor.whiskerLeft (tower X) (naturalAugmentation A B)

/-- Identify the totalizations of the lifted stages with the totalizations
using the original coefficient modules, compatibly with all transitions. -/
def totalTowerIso :
    liftedTower.{u, v, w} A B X ⋙ AmitsurTotalComplexSpec.functor A B ≅ totalTower A B X :=
  Functor.associator (tower X) (lift.{u, v, w} A) (AmitsurTotalComplexSpec.functor A B) ≪≫
    Functor.isoWhiskerLeft (tower X) (totalNatIso A B)

def totalCone : Cone (totalTower A B X) :=
  (functor A B).mapCone (truncationCone X)

def totalComparison : AmitsurTotalComplexSpec.Independent.total A B X ⟶ limit (totalTower A B X) :=
  limit.lift _ (totalCone A B X)

end

section DeclarationTypes

set_option linter.checkUnivs false

def LiftedTowerType := declarationType (@liftedTower.{u, v, w})
def LiftedConeType := declarationType (@liftedCone.{u, v, w})
def SourceLimitComparisonType := declarationType (@sourceLimitComparison.{u, v, w})
def LiftedComparisonType := declarationType (@liftedComparison.{u, v, w})
def TotalTowerType := declarationType (@totalTower.{u, v, w})
def AugmentationOfTowersType := declarationType (@augmentationOfTowers.{u, v, w})
def TotalTowerIsoType := declarationType (@totalTowerIso.{u, v, w})
def TotalConeType := declarationType (@totalCone.{u, v, w})
def TotalComparisonType := declarationType (@totalComparison.{u, v, w})

def LiftedStageComparisonType := declarationType (@liftedStageComparison.{u, v, w})

def LiftedStageComparisonIsIso : Prop :=
  ∀ (A : Type u) [CommRing A] (B : Type v) (X : CochainComplex (ModuleCat.{w} A) ℤ) (n : ℕ),
    IsIso (liftedStageComparison.{u, v, w} A B X n)

def LiftedProjectionComparison : Prop :=
  ∀ (A : Type u) [CommRing A] (B : Type v) (X : CochainComplex (ModuleCat.{w} A) ℤ) (n : ℕ),
    projection ((lift.{u, v, w} A).obj X) n ≫ liftedStageComparison.{u, v, w} A B X n =
      (lift.{u, v, w} A).map (projection X n)

def LiftedTransitionComparison : Prop :=
  ∀ (A : Type u) [CommRing A] (B : Type v) (X : CochainComplex (ModuleCat.{w} A) ℤ)
    {m n : ℕ} (h : m ≤ n),
    transition ((lift.{u, v, w} A).obj X) h ≫ liftedStageComparison.{u, v, w} A B X m =
      liftedStageComparison.{u, v, w} A B X n ≫ (lift.{u, v, w} A).map (transition X h)

def SourceLimitComparisonIsIso : Prop :=
  ∀ (A : Type u) [CommRing A] (B : Type v) (X : CochainComplex (ModuleCat.{w} A) ℤ),
    IsIso (sourceLimitComparison.{u, v, w} A B X)

def LiftedComparisonIsIso : Prop :=
  ∀ (A : Type u) [CommRing A] (B : Type v) (X : CochainComplex (ModuleCat.{w} A) ℤ),
    IsIso (liftedComparison.{u, v, w} A B X)

def SourceComparison : Prop :=
  ∀ (A : Type u) [CommRing A] (B : Type v) (X : CochainComplex (ModuleCat.{w} A) ℤ),
    (lift.{u, v, w} A).map (truncationComparison X) ≫ sourceLimitComparison.{u, v, w} A B X =
      liftedComparison.{u, v, w} A B X

def LiftedTransitionSurjective : Prop :=
  ∀ (A : Type u) [CommRing A] (B : Type v) (X : CochainComplex (ModuleCat.{w} A) ℤ)
    {m n : ℕ} (h : m ≤ n) (q : ℤ),
    Function.Surjective (((liftedTower.{u, v, w} A B X).map ((homOfLE h).op)).f q)

def TotalTransitionSurjective : Prop :=
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B]
    (X : CochainComplex (ModuleCat.{w} A) ℤ) {m n : ℕ} (h : m ≤ n) (k : ℤ),
    Function.Surjective (((totalTower A B X).map ((homOfLE h).op)).f k)

def TotalComparisonIsIso : Prop :=
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B]
    (X : CochainComplex (ModuleCat.{w} A) ℤ),
    IsIso (totalComparison A B X)

def TowerAugmentationComparison : Prop :=
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B]
    (X : CochainComplex (ModuleCat.{w} A) ℤ) (j : ℕᵒᵖ),
    (augmentationOfTowers A B X).app j =
      AmitsurTotalComplexSpec.augmentation A B ((liftedTower.{u, v, w} A B X).obj j) ≫
        (totalTowerIso A B X).hom.app j

def AugmentationOnCones : Prop :=
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B]
    (X : CochainComplex (ModuleCat.{w} A) ℤ) (j : ℕᵒᵖ),
    (liftedCone.{u, v, w} A B X).π.app j ≫ (augmentationOfTowers A B X).app j =
      AmitsurTotalComplexSpec.Independent.augmentation A B X ≫ (totalCone A B X).π.app j

def AugmentationOnLimits : Prop :=
  ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B]
    (X : CochainComplex (ModuleCat.{w} A) ℤ),
    (lift.{u, v, w} A).map (truncationComparison X) ≫
        sourceLimitComparison.{u, v, w} A B X ≫ limMap (augmentationOfTowers A B X) =
      AmitsurTotalComplexSpec.Independent.augmentation A B X ≫ totalComparison A B X

end DeclarationTypes

end Independent

end AmitsurTruncationTowerSpec
