import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SheafModels
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.TorusStages
import Mathlib.Topology.Sheaves.Skyscraper

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace
open scoped Classical

namespace RepTheorySurvey.Geometric.TorusPerverseSpecs

open Analytic LatticeModelSpecs BoundedLatticeSpecs TorusStageSpecs

/-- The actual analytic space of torus lattices, with the topology of the bounded stages. -/
def torusSpace (r : ℕ) : TopCat.{0} :=
  @TopCat.of (TorusLattice r) (torusAnalyticTopology r)

/-- The image of the bounded lattice model in the union. -/
def stageSet (r N : ℕ) : Set (TorusLattice r) :=
  {L | ∀ i, (scalarLattice 1 (N : ℤ)).val ≤ (L i).val ∧
    (L i).val ≤ (scalarLattice 1 (-(N : ℤ))).val}

/-- Geometric properties used to form the closed exhaustion in the sheaf model. -/
structure StageGeometry (r : ℕ) : Prop where
  discrete : @DiscreteTopology (torusSpace r) (torusSpace r).str
  exhaustive : ∀ x : torusSpace r, ∃ n, x ∈ stageSet r n

private theorem stageSet_monotone (r : ℕ) : Monotone (stageSet r) := by
  intro n m h L hL i
  exact ⟨(diagonalLattice_le fun _ ↦ Int.ofNat_le.mpr h).trans (hL i).1,
    (hL i).2.trans (diagonalLattice_le fun _ ↦ neg_le_neg (Int.ofNat_le.mpr h))⟩

def stages (r : ℕ) (g : StageGeometry r) : ClosedStages (torusSpace r) where
  stage := stageSet r
  closed n := @isClosed_discrete (torusSpace r) (torusSpace r).str g.discrete (stageSet r n)
  monotone := stageSet_monotone r
  exhaustive := g.exhaustive

/-- Every point of a discrete space is a stratum of complex dimension zero. -/
def pointStratification (X : TopCat.{0}) [DiscreteTopology X] : Stratification X where
  Index := X
  stratum x :=
    { ambientOpen := ⊤
      subset := {y | y.val = x}
      closed := isClosed_singleton.preimage continuous_subtype_val
      complexDimension := 0 }
  partition x := by
    refine ⟨x, ⟨⟨⟨x, by simp⟩, rfl⟩, rfl⟩, ?_⟩
    rintro y ⟨z, rfl⟩
    exact z.property.symm

private def subtypePointStratification (X : TopCat.{0}) [DiscreteTopology X] (S : Set X) :
    Stratification (TopCat.of S) :=
  pointStratification _

def stageStratifications (r : ℕ) (g : StageGeometry r) (n : ℕ) :
    Stratification ((stages r g).space n) :=
  @subtypePointStratification (torusSpace r) g.discrete (stageSet r n)

/-- Index k means reduction modulo t^(k+1), so every level is positive. -/
abbrev PositiveJet (r k : ℕ) := TorusJets r (k + 1) (Nat.succ_pos k)

instance positiveJetTopology (r k : ℕ) : TopologicalSpace (PositiveJet r k) :=
  torusJetTopology r (k + 1) (Nat.succ_pos k)

def jetTruncation {r k l : ℕ} (h : k ≤ l) : PositiveJet r l →* PositiveJet r k where
  toFun a i := Units.map (truncateJet (Nat.succ_le_succ h)).toMonoidHom (a i)
  map_one' := funext fun _ ↦ (Units.map (truncateJet (Nat.succ_le_succ h)).toMonoidHom).map_one
  map_mul' a b := funext fun i ↦
    (Units.map (truncateJet (Nat.succ_le_succ h)).toMonoidHom).map_mul (a i) (b i)

private theorem truncateJet_id {k : ℕ} (x : JetRing k) :
    truncateJet (le_refl k) x = x :=
  congrArg (fun f : JetRing k →+* JetRing k ↦ f x) Ideal.Quotient.factor_eq

private theorem truncateJet_comp {k l m : ℕ} (h : k ≤ l) (j : l ≤ m) (x : JetRing m) :
    truncateJet h (truncateJet j x) = truncateJet (h.trans j) x :=
  Ideal.Quotient.factor_comp_apply _ _ x

structure ContinuousJets (r : ℕ) : Prop where
  topologicalGroup :
    ∀ k, @IsTopologicalGroup (PositiveJet r k) (positiveJetTopology r k) inferInstance
  truncation : ∀ {k l : ℕ} (h : k ≤ l),
    @Continuous (PositiveJet r l) (PositiveJet r k) (positiveJetTopology r l)
      (positiveJetTopology r k) (jetTruncation (r := r) h)

def jetSystem (r : ℕ) (c : ContinuousJets r) : JetSystem.{0} where
  group k :=
    { space := @TopCat.of (PositiveJet r k) (positiveJetTopology r k)
      group := inferInstance
      topologicalGroup := c.topologicalGroup k }
  truncate _ _ h := TopCat.ofHom ⟨jetTruncation h, c.truncation h⟩
  truncate_one h := (jetTruncation (r := r) h).map_one
  truncate_mul h a b := (jetTruncation (r := r) h).map_mul a b
  truncate_id _k := TopCat.ext fun a ↦ funext fun i ↦ Units.ext (truncateJet_id (a i).val)
  truncate_comp h j :=
    TopCat.ext fun a ↦ funext fun i ↦
      Units.ext (truncateJet_comp (Nat.succ_le_succ h) (Nat.succ_le_succ j) (a i).val)

abbrev JetCoordinates (r k : ℕ) :=
  (Fin r → {z : ℂ // z ≠ 0}) × (Fin r → Fin k → ℂ)

/-- A homeomorphism using the constant and higher coefficients of each jet. -/
def HasJetCoordinates (r k : ℕ) : Prop :=
  ∃ e : @Homeomorph (PositiveJet r k) (JetCoordinates r k) (positiveJetTopology r k) inferInstance,
    (∀ a i, ((e a).1 i).val = jetCoefficients (k + 1) (a i).val 0) ∧
    (∀ a i j, (e a).2 i j = jetCoefficients (k + 1) (a i).val j.succ)

def trivialAction (H : AnalyticGroup.{0}) (X : TopCat.{0}) : AnalyticAction H X where
  act := AnalyticAction.projection H X
  one_act _ := rfl
  mul_act _ _ _ := rfl

private def trivialJetAction (J : JetSystem.{0}) (X : TopCat.{0}) : JetAction J X where
  cutoff := 0
  action k _ := trivialAction (J.group k) X
  factors := by intros; exact TopCat.ext (fun _ ↦ rfl)

private def trivialStageActions (J : JetSystem.{0}) {X : TopCat.{0}} (A : ClosedStages X) :
    StageJetActions J A where
  stageAction n := trivialJetAction J (A.space n)
  compatible := by intros; exact TopCat.ext (fun _ ↦ rfl)

/-- At every positive level the action on torus points is the projection. -/
def stageActions (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) :
    StageJetActions (jetSystem r c) (stages r g) :=
  trivialStageActions (jetSystem r c) (stages r g)

/-- The stage action pulls back under positive-loop reduction to the canonical lattice action. -/
def IsPositiveLoopAction (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) : Prop :=
  ∀ (n k : ℕ) (u : Fin r → Oˣ) (x : (stages r g).space n),
    (stages r g).inclusion n
      ((((stageActions r g c).stageAction n).action k (Nat.zero_le k)).act
        (reduceTorus r (k + 1) (Nat.succ_pos k) u, x)) =
      @SMul.smul (Fin r → Kˣ) (TorusLattice r) (torusAction r).toSMul
        (positiveTorusMap r u) ((stages r g).inclusion n x)

abbrev Perverse (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) :=
  (stageActions r g c).FiniteSupportPerverse (stageStratifications r g)

def forgetPerverse (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) :
    Perverse r g c ⥤ Derived (torusSpace r) :=
  ObjectProperty.ι _ ⋙ StageJetActions.forget (stageActions r g c)

abbrev Families (r : ℕ) := Discrete (Coweight r) ⥤ Coeff.{0}

def familySupport {r : ℕ} (V : Families r) : Set (Coweight r) :=
  {w | ¬ IsZero (V.obj (Discrete.mk w))}

def IsFiniteFamily (r : ℕ) : ObjectProperty (Families r) :=
  fun V ↦ (∀ w, Module.Finite ℚ (V.obj (Discrete.mk w))) ∧ (familySupport V).Finite

abbrev Graded (r : ℕ) := (IsFiniteFamily r).FullSubcategory

def gradedInclusion (r : ℕ) : Graded r ⥤ Families r :=
  ObjectProperty.ι (IsFiniteFamily r)

/-- The point represented by the monomial loop of coweight w. -/
def monomialPoint (r : ℕ) (w : Coweight r) : torusSpace r :=
  torusLatticeAt r w

/-- Stalks of degree-zero cohomology, taken at the monomial coweight labels. -/
def degreeZeroStalks (r : ℕ) : Derived (torusSpace r) ⥤ Families r where
  obj F := Discrete.functor fun w ↦ (stalk (X := torusSpace r) (monomialPoint r w)).obj
    ((cohomology (torusSpace r) 0).obj F)
  map f := Discrete.natTrans fun w ↦ (stalk (X := torusSpace r) (monomialPoint r w.as)).map
    ((cohomology (torusSpace r) 0).map f)
  map_id F := by
    apply NatTrans.ext
    funext w
    simp
  map_comp f h := by
    apply NatTrans.ext
    funext w
    simp

/-- The sheaf obtained by extending the individual stalks by zero. -/
def skyscraperProduct (r : ℕ) : Families r ⥤ Sheaves (torusSpace r) where
  obj V := ∏ᶜ fun w : Coweight r ↦
    (skyscraperSheafFunctor (X := torusSpace r) (monomialPoint r w)).obj (V.obj (Discrete.mk w))
  map f := CategoryTheory.Limits.Pi.map fun w ↦ (skyscraperSheafFunctor (X := torusSpace r) (monomialPoint r w)).map
    (f.app (Discrete.mk w))
  map_id V := by
    apply Pi.hom_ext
    intro w
    simp only [Pi.map_π, NatTrans.id_app, Category.id_comp]
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  map_comp f h := by
    apply Pi.hom_ext
    intro w
    simp only [Pi.map_π, NatTrans.comp_app, CategoryTheory.Functor.map_comp, Category.assoc, Pi.map_π_assoc]

/-- Extension by zero followed by placing the sheaf in cohomological degree zero. -/
def extendByZero (r : ℕ) : Graded r ⥤ Derived (torusSpace r) :=
  gradedInclusion r ⋙ skyscraperProduct r ⋙ DerivedCategory.singleFunctor _ 0

/-- The inverse sheaf is carried by exactly the finite locus of nonzero stalks.
The isomorphism is the unit for restriction and closed direct image on
the sheaf with those stalks. -/
def SupportedExtension (r : ℕ) (V : Graded r) : Prop :=
  let Z : Set (torusSpace r) := (monomialPoint r) '' familySupport V.obj
  let F := (skyscraperProduct r).obj V.obj
  IsIso ((inverseDirectAdjunction (closedInclusion Z)).unit.app F)

/-- The equivariant middle-perverse heart on the torus is equivalent to the
finite-dimensional coweight-graded rational vector spaces. -/
def TorusPerverseEquivalence : Prop :=
  ∀ r : ℕ, ∃ (g : StageGeometry r) (c : ContinuousJets r),
    (∀ k, HasJetCoordinates r k ∧ @ConnectedSpace (PositiveJet r k) (positiveJetTopology r k)) ∧
    IsPositiveLoopAction r g c ∧
    (∀ (F : Derived (torusSpace r)),
      IsFiniteStagePerverse (stages r g) (stageStratifications r g) F →
        ∃! _ : (stageActions r g c).Equivariance F, True) ∧
    (∀ V : Graded r, SupportedExtension r V) ∧
    ∃ E : Perverse r g c ≌ Graded r,
      Nonempty (E.functor ⋙ gradedInclusion r ≅
        forgetPerverse r g c ⋙ degreeZeroStalks r) ∧
      Nonempty (E.inverse ⋙ forgetPerverse r g c ≅ extendByZero r)

end RepTheorySurvey.Geometric.TorusPerverseSpecs
