import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.AmitsurTotalComplex
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Complexes.SequentialHomotopyLimits

/-! The finite-column tower of the signed Amitsur totalization. -/

namespace Specs.DerivedFormalization.Descent.AmitsurHorizontalLimit

open CategoryTheory CategoryTheory.Limits Opposite
open AmitsurTotalComplexSpec (Complex rowIndex)
open AmitsurTotalComplexSpec.Independent
open Specs.DerivedFormalization.SequentialHomotopyLimits
  (Towers holimValue comparisonValue surjectiveTransitions)
open Specs.DerivedFormalization.Cochains (qValue)

universe u v w

noncomputable section

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
variable {X Y : Input.{u, w} A}

section StageMaps

variable (f : X ⟶ Y) (k : ℕ)

private def finiteComponent (i : ℤ) :
    (finiteTotal A B X k).X i ⟶ (finiteTotal A B Y k).X i :=
  ModuleCat.ofHom (LinearMap.pi fun p : Fin (k + 1) =>
    (tensorMap A B (f.f (rowIndex i p)) p).hom.comp (LinearMap.proj p))

@[reassoc]
private theorem finiteComponent_factor (i : ℤ) :
    (truncate A B X k).f i ≫ finiteComponent A B f k i =
      (map A B f).f i ≫ (truncate A B Y k).f i := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext p
  change tensorMap A B (f.f (rowIndex i p)) p ((truncate A B X k).f i x p) =
    (truncate A B Y k).f i ((map A B f).f i x) p
  rw [truncate_apply, truncate_apply, map_apply]

private theorem finiteComponent_comm (i : ℤ) :
    finiteComponent A B f k i ≫ (finiteTotal A B Y k).d i (i + 1) =
      (finiteTotal A B X k).d i (i + 1) ≫ finiteComponent A B f k (i + 1) := by
  let : Epi ((truncate A B X k).f i) :=
    (ModuleCat.epi_iff_surjective _).2 (truncate_surjective A B X k i)
  apply (cancel_epi ((truncate A B X k).f i)).1
  rw [finiteComponent_factor_assoc, (truncate A B Y k).comm,
    ← Category.assoc, (map A B f).comm, Category.assoc, ← finiteComponent_factor,
    (truncate A B X k).comm_assoc]

/-- Tensor the coefficient map on each retained column. -/
def stageMap (f : X ⟶ Y) (k : ℕ) : finiteTotal A B X k ⟶ finiteTotal A B Y k :=
  CochainComplex.ofHom (finiteComponent A B f k) (finiteComponent_comm A B f k)

theorem stageMap_apply (i : ℤ) (x : finiteTerm A B X k i) (p : Fin (k + 1)) :
    (stageMap A B f k).f i x p = tensorMap A B (f.f (rowIndex i p)) p (x p) := rfl

@[reassoc]
theorem truncate_stageMap :
    truncate A B X k ≫ stageMap A B f k = map A B f ≫ truncate A B Y k := by
  apply HomologicalComplex.hom_ext
  exact finiteComponent_factor A B f k

end StageMaps

/-- Stage k retains columns 0 through k. The structure maps restrict
a family to the smaller initial segment. -/
abbrev tower (X : Input.{u, w} A) : Towers (Complex.{u, v, w} A) where
  obj k := finiteTotal A B X k.unop
  map h := projection A B X (leOfHom h.unop)
  map_id k := projection_id A B X k.unop
  map_comp h g := (projection_comp A B X (leOfHom g.unop) (leOfHom h.unop)).symm

/-- The tower map induced by a cochain map of coefficients. -/
abbrev towerMap (f : X ⟶ Y) : tower A B X ⟶ tower A B Y where
  app k := stageMap A B f k.unop
  naturality k l h := by
    have hkl := leOfHom h.unop
    change projection A B X hkl ≫ stageMap A B f l.unop =
      stageMap A B f k.unop ≫ projection A B Y hkl
    apply HomologicalComplex.hom_ext
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext p
    change (stageMap A B f l.unop).f i ((projection A B X hkl).f i x) p =
      (projection A B Y hkl).f i ((stageMap A B f k.unop).f i x) p
    rw [stageMap_apply, projection_apply, projection_apply, stageMap_apply]
    rfl

private theorem stage_hom_ext (X : Input.{u, w} A) (k : ℕ)
    {Z : Complex.{u, v, w} A} {f g : finiteTotal A B X k ⟶ Z}
    (h : truncate A B X k ≫ f = truncate A B X k ≫ g) : f = g := by
  apply HomologicalComplex.hom_ext
  intro i
  let : Epi ((truncate A B X k).f i) :=
    (ModuleCat.epi_iff_surjective _).2 (truncate_surjective A B X k i)
  exact (cancel_epi ((truncate A B X k).f i)).1 (congrArg (fun t => t.f i) h)

/-- The tower of horizontal truncations, functorial in the coefficient complex. -/
def towerFunctor : Input.{u, w} A ⥤ Towers (Complex.{u, v, w} A) where
  obj := tower A B
  map := towerMap A B
  map_id X := by
    apply NatTrans.ext
    funext k
    change stageMap A B (𝟙 X) k.unop = 𝟙 _
    apply stage_hom_ext A B X
    rw [truncate_stageMap, show map A B (𝟙 X) = 𝟙 _ from (functor A B).map_id X,
      Category.id_comp, Category.comp_id]
  map_comp {X Y Z} f g := by
    apply NatTrans.ext
    funext k
    change stageMap A B (f ≫ g) k.unop = stageMap A B f k.unop ≫ stageMap A B g k.unop
    apply stage_hom_ext A B X
    have h : map A B (f ≫ g) = map A B f ≫ map A B g := (functor A B).map_comp f g
    simp only [Category.assoc, truncate_stageMap_assoc, truncate_stageMap, h]

/-- The compatible coordinate restrictions from the product total complex. -/
abbrev restrictionCone (X : Input.{u, w} A) : Cone (tower A B X) where
  pt := total A B X
  π :=
    { app := fun k => truncate A B X k.unop
      naturality := fun k l h => by
        change 𝟙 _ ≫ truncate A B X l.unop =
          truncate A B X k.unop ≫ projection A B X (leOfHom h.unop)
        rw [Category.id_comp, truncate_projection] }

/-- The map to the ordinary limit induced by all coordinate restrictions. -/
def toLimit (X : Input.{u, w} A) : total A B X ⟶ limit (tower A B X) :=
  limit.lift _ (restrictionCone A B X)

/-- The composite of the ordinary limit map and the canonical shifted-cone comparison. -/
def toHolim (X : Input.{u, w} A) : total A B X ⟶ holimValue.obj (tower A B X) :=
  toLimit A B X ≫ comparisonValue (tower A B X)

def SurjectiveTransitions : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (X : Input.{u, w} A), surjectiveTransitions (tower A B X)

def ToLimitIsIso : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (X : Input.{u, w} A), IsIso (toLimit A B X)

def LimitProjection : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (X : Input.{u, w} A) (k : ℕ),
    toLimit A B X ≫ limit.π (tower A B X) (op k) = truncate A B X k

def ToLimitNaturality : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Input.{u, w} A} (f : X ⟶ Y),
    map A B f ≫ toLimit A B Y = toLimit A B X ≫ limMap (towerMap A B f)

def ToHolimQuasiIso : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (X : Input.{u, w} A), QuasiIso (toHolim A B X)

def ToHolimNaturality : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Input.{u, w} A} (f : X ⟶ Y),
    map A B f ≫ toHolim A B Y = toHolim A B X ≫ holimValue.map (towerMap A B f)

def DerivedComparisonIsIso : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (X : Input.{u, w} A), IsIso ((qValue A).map (toHolim A B X))

def NaturalLimitIso : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
    ∃ e : functor.{u, v, w} A B ≅ towerFunctor A B ⋙ lim,
      ∀ X, e.hom.app X = toLimit A B X

def NaturalDerivedIso : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
    ∃ e : functor.{u, v, w} A B ⋙ qValue A ≅ (towerFunctor A B ⋙ holimValue) ⋙ qValue A,
      ∀ X, e.hom.app X = (qValue A).map (toHolim A B X)

-- These type codes retain the independent universes of the input data.
set_option linter.checkUnivs false

private def declarationType {T : Sort*} (_ : T) := T

def StageMapType := declarationType (@stageMap.{u, v, w})
def TowerType := declarationType (@tower.{u, v, w})
def TowerMapType := declarationType (@towerMap.{u, v, w})
def TowerFunctorType := declarationType (@towerFunctor.{u, v, w})
def RestrictionConeType := declarationType (@restrictionCone.{u, v, w})
def ToLimitType := declarationType (@toLimit.{u, v, w})
def ToHolimType := declarationType (@toHolim.{u, v, w})

end

end Specs.DerivedFormalization.Descent.AmitsurHorizontalLimit
