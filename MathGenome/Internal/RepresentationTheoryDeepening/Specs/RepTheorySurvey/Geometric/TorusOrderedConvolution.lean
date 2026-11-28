import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.TorusPerverse
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Batteries.Tactic.OpenPrivate

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
open scoped Classical MonoidalCategory ZeroObject

namespace RepTheorySurvey.Geometric.TorusOrderedConvolutionSpecs

open Analytic LatticeModelSpecs TorusStageSpecs TorusPerverseSpecs
open private trivialJetAction from MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.TorusPerverse

abbrev Loops (r : ℕ) := Fin r → Kˣ
abbrev TorusQuotient (r : ℕ) := Grassmannian (PositiveTorus r)
abbrev Labels (r : ℕ) := Coweight r

/-- Coordinates on the two incarnations of the reduced torus Grassmannian. -/
structure CoordinatesAtRank (r : ℕ) where
  quotient : Labels r ≃ TorusQuotient r
  lattice : Labels r ≃ TorusLattice r
  quotient_monomial : ∀ a, quotient a = coset (PositiveTorus r) (torusMonomial r a)
  lattice_monomial : ∀ a, lattice a = torusLatticeAt r a
  relate : ∀ g : Loops r,
    lattice (quotient.symm (coset (PositiveTorus r) g)) =
      g • (fun _ : Fin r ↦ standardLattice 1)
  fixes : ∀ (a : PositiveTorus r) (x : TorusLattice r), (a : Loops r) • x = x

variable {r : ℕ}

def firstSet (c : CoordinatesAtRank r) (A : Set (Labels r)) : Set (TorusQuotient r) :=
  c.quotient '' A

def secondSet (c : CoordinatesAtRank r) (B : Set (Labels r)) : Set (TorusLattice r) :=
  c.lattice '' B

theorem secondSet_stable (c : CoordinatesAtRank r) (B : Set (Labels r)) :
    StableStage (PositiveTorus r) (secondSet c B) := by
  intro a x hx
  simpa only [c.fixes] using hx

abbrev OrderedRepresentatives (c : CoordinatesAtRank r) (A B : Set (Labels r)) :=
  Representatives (PositiveTorus r) (firstSet c A) (secondSet c B)

abbrev OrderedStage (c : CoordinatesAtRank r) (A B : Set (Labels r)) :=
  TwistedProduct (PositiveTorus r) (firstSet c A) (secondSet c B) (secondSet_stable c B)

def orderedMk {c : CoordinatesAtRank r} {A B : Set (Labels r)}
    (x : OrderedRepresentatives c A B) : OrderedStage c A B :=
  Quotient.mk _ x

def monomialPair (c : CoordinatesAtRank r) {A B : Set (Labels r)} (a : A) (b : B) :
    OrderedRepresentatives c A B :=
  ⟨(torusMonomial r a, c.lattice b),
    ⟨a, a.property, c.quotient_monomial a⟩, ⟨b, b.property, rfl⟩⟩

def enlargeOrdered {c : CoordinatesAtRank r} {A B A' B' : Set (Labels r)}
    (hA : A ⊆ A') (hB : B ⊆ B') : OrderedStage c A B → OrderedStage c A' B' :=
  Quotient.map (fun p : OrderedRepresentatives c A B ↦
    (⟨p.val, Set.image_mono hA p.property.1, Set.image_mono hB p.property.2⟩ :
      OrderedRepresentatives c A' B')) (fun _ _ h ↦ h)

/-- The two intermediate changes of trivialization for three successive modifications. -/
def tripleRel (r : ℕ) : Setoid (Loops r × Loops r × TorusLattice r) where
  r p q := ∃ a b : PositiveTorus r,
    q.1 = p.1 * (a : Loops r) ∧
    q.2.1 = ((a⁻¹ : PositiveTorus r) : Loops r) * p.2.1 * (b : Loops r) ∧
    q.2.2 = ((b⁻¹ : PositiveTorus r) : Loops r) • p.2.2
  iseqv := by
    constructor
    · intro p
      exact ⟨1, 1, by simp, by simp, by simp⟩
    · rintro p q ⟨a, b, h₁, h₂, h₃⟩
      exact ⟨a⁻¹, b⁻¹, by simp [h₁, mul_assoc], by simp [h₂, mul_assoc],
        by simp [h₃, smul_smul]⟩
    · rintro p q z ⟨a, b, h₁, h₂, h₃⟩ ⟨a', b', k₁, k₂, k₃⟩
      exact ⟨a * a', b * b', by simp [h₁, k₁, mul_assoc],
        by simp [h₂, k₂, mul_assoc], by simp [h₃, k₃, smul_smul]⟩

abbrev TripleStage (r : ℕ) := Quotient (tripleRel r)

def tripleMk (g h : Loops r) (x : TorusLattice r) : TripleStage r :=
  Quotient.mk _ (g, h, x)

def tripleTerminal : TripleStage r → TorusLattice r :=
  Quotient.lift (fun p : Loops r × Loops r × TorusLattice r ↦ (p.1 * p.2.1) • p.2.2) (by
    rintro p q ⟨a, b, h₁, h₂, h₃⟩
    simp [h₁, h₂, h₃, smul_smul, mul_assoc])

/-- The topology of the reduced ordered stage is the quotient of discrete
labels. The equations specify the labels and structural maps on representatives. -/
structure OrderedGeometry (r : ℕ) where
  coordinates : CoordinatesAtRank r
  labels : ∀ (A B : Set (Labels r)), OrderedStage coordinates A B ≃ A × B
  label_mk : ∀ {A B} (p : OrderedRepresentatives coordinates A B),
    ((labels A B (orderedMk p)).1.val, (labels A B (orderedMk p)).2.val) =
      (coordinates.quotient.symm (coset (PositiveTorus r) p.val.1),
        coordinates.lattice.symm p.val.2)
  terminal_label : ∀ {A B} (z : OrderedStage coordinates A B),
    terminalMap (PositiveTorus r) (secondSet_stable coordinates B) z =
      monomialPoint r ((labels A B z).1.val + (labels A B z).2.val)
  bounded : ∀ N (a : Labels r),
    coordinates.lattice a ∈ stageSet r N ↔ ∀ i, -(N : ℤ) ≤ a i ∧ a i ≤ N
  triples : TripleStage r ≃ Labels r × Labels r × Labels r
  triple_mk : ∀ (g h : Loops r) (x : TorusLattice r),
    triples (tripleMk g h x) =
      (coordinates.quotient.symm (coset (PositiveTorus r) g),
        coordinates.quotient.symm (coset (PositiveTorus r) h), coordinates.lattice.symm x)
  triple_terminal : ∀ p,
    tripleTerminal p =
      monomialPoint r ((triples p).1 + (triples p).2.1 + (triples p).2.2)

namespace OrderedGeometry

variable (D : OrderedGeometry r)

def space (A B : Set (Labels r)) : TopCat.{0} :=
  @TopCat.of (OrderedStage D.coordinates A B) ⊥

def labelSpace (A B : Set (Labels r)) : TopCat.{0} :=
  @TopCat.of (A × B) ⊥

def labelMap (A B : Set (Labels r)) : D.space A B ⟶ labelSpace A B :=
  @TopCat.ofHom _ _ (D.space A B).str (labelSpace A B).str
    ⟨D.labels A B, continuous_bot⟩

def terminal (A B : Set (Labels r)) : D.space A B ⟶ torusSpace r :=
  @TopCat.ofHom _ _ (D.space A B).str (torusSpace r).str
    ⟨terminalMap (PositiveTorus r) (secondSet_stable D.coordinates B), continuous_bot⟩

abbrev Whole := D.space Set.univ Set.univ

def wholePair (a b : Labels r) : D.Whole :=
  orderedMk (monomialPair D.coordinates (⟨a, trivial⟩ : (Set.univ : Set (Labels r)))
    (⟨b, trivial⟩ : (Set.univ : Set (Labels r))))

theorem wholePair_labels (a b : Labels r) :
    ((D.labels Set.univ Set.univ (D.wholePair a b)).1.val,
      (D.labels Set.univ Set.univ (D.wholePair a b)).2.val) = (a, b) := by
  simp only [wholePair, D.label_mk, monomialPair, ← D.coordinates.quotient_monomial,
    Equiv.symm_apply_apply]

def wholeMk (g : Loops r) (x : TorusLattice r) : D.Whole :=
  orderedMk (A := Set.univ) (B := Set.univ)
    ⟨(g, x), ⟨_, trivial, D.coordinates.quotient.apply_symm_apply _⟩,
      ⟨_, trivial, D.coordinates.lattice.apply_symm_apply _⟩⟩

/-- The two maps from triples which combine adjacent modifications. -/
def combineFirst (p : TripleStage r) : D.Whole :=
  D.wholePair ((D.triples p).1 + (D.triples p).2.1) (D.triples p).2.2

def combineLast (p : TripleStage r) : D.Whole :=
  D.wholePair (D.triples p).1 ((D.triples p).2.1 + (D.triples p).2.2)

def TripleMaps : Prop :=
  ∀ (g h : Loops r) (x : TorusLattice r),
    D.combineFirst (tripleMk g h x) = D.wholeMk (g * h) x ∧
    D.combineLast (tripleMk g h x) = D.wholeMk g (h • x)

/-- The jet cover in the monomial trivialization. The underlying map of
representatives sends (a,z) to (t^λ a,t^μ), where z has labels (λ,μ). -/
def jetCover (c : ContinuousJets r) (A B : Set (Labels r)) (k : ℕ) :
    AnalyticAction.Parameters ((jetSystem r c).group k) (D.space A B) ⟶ D.space A B :=
  AnalyticAction.projection _ _

def representatives (A B : Set (Labels r)) : Prop :=
  ∃ e : (Fin r → Oˣ) × D.space A B ≃ OrderedRepresentatives D.coordinates A B,
    ∀ a z, (e (a, z)).val =
      (torusMonomial r (D.labels A B z).1.val * positiveTorusMap r a,
        D.coordinates.lattice (D.labels A B z).2.val) ∧ orderedMk (e (a, z)) = z

end OrderedGeometry

abbrev Heart (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) := Perverse r g c

def stalkFamily (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) :=
  forgetPerverse r g c ⋙ degreeZeroStalks r

abbrev fiber {r : ℕ} (V : Families r) (a : Labels r) : Coeff.{0} := V.obj (Discrete.mk a)

def familyAt {r : ℕ} (a : Labels r) : Families r ⥤ Coeff.{0} :=
  (evaluation _ _).obj (Discrete.mk a)

def exteriorAt {r : ℕ} (a b : Labels r) : Families r × Families r ⥤ Coeff.{0} :=
  (familyAt a).prod (familyAt b) ⋙ MonoidalCategory.tensor Coeff.{0}

def skyscrapers (X : TopCat.{0}) {C : Type*} [Category C] (F : X → C ⥤ Coeff.{0}) :
    C ⥤ Sheaves X where
  obj V := ∏ᶜ fun x : X ↦ (skyscraperSheafFunctor x).obj ((F x).obj V)
  map f := CategoryTheory.Limits.Pi.map fun x ↦ (skyscraperSheafFunctor x).map ((F x).map f)
  map_id V := by
    apply Pi.hom_ext
    intro x
    simp
  map_comp f g := by
    apply Pi.hom_ext
    intro x
    simp

def exteriorOnLabels (A B : Set (Labels r)) :
    Families r × Families r ⥤ Sheaves (@TopCat.of (A × B) ⊥) :=
  skyscrapers _ fun p ↦ exteriorAt p.1.val p.2.val

/-- The descent sheaf on the actual quotient, assembled from the tensor stalks. -/
def descendedExterior (D : OrderedGeometry r) (A B : Set (Labels r)) :
    Families r × Families r ⥤ Sheaves (D.space A B) :=
  skyscrapers _ fun z ↦ exteriorAt (D.labels A B z).1.val (D.labels A B z).2.val

def descendedExteriorAtJet (D : OrderedGeometry r) (c : ContinuousJets r)
    (A B : Set (Labels r)) (k : ℕ) :
    Families r × Families r ⥤ Sheaves
      (AnalyticAction.Parameters ((jetSystem r c).group k) (D.space A B)) :=
  exteriorOnLabels A B ⋙ inverseImage (D.jetCover c A B k ≫ D.labelMap A B)

abbrev SumFiber {r : ℕ} (n : Labels r) := {p : Labels r × Labels r // p.1 + p.2 = n}

def fiberSum {r : ℕ} (n : Labels r) : Families r × Families r ⥤ Coeff.{0} where
  obj VW := ∐ fun p : SumFiber n ↦ fiber VW.1 p.val.1 ⊗ fiber VW.2 p.val.2
  map f := CategoryTheory.Limits.Sigma.map fun p : SumFiber n ↦
    f.1.app (Discrete.mk p.val.1) ⊗ₘ f.2.app (Discrete.mk p.val.2)
  map_id _ := by
    apply Sigma.hom_ext
    intro p
    simp
  map_comp f g := by
    apply Sigma.hom_ext
    intro p
    simp

def summand {r : ℕ} (n : Labels r) (V W : Families r) (p : SumFiber n) :
    fiber V p.val.1 ⊗ fiber W p.val.2 ⟶ (fiberSum n).obj (V, W) :=
  Sigma.ι (fun q : SumFiber n ↦ fiber V q.val.1 ⊗ fiber W q.val.2) p

def geometricPushforward (D : OrderedGeometry r) :
    Families r × Families r ⥤ Sheaves (torusSpace r) :=
  descendedExterior D Set.univ Set.univ ⋙ directImage (D.terminal Set.univ Set.univ)

def geometricFiber (D : OrderedGeometry r) (n : Labels r) :
    Families r × Families r ⥤ Coeff.{0} :=
  geometricPushforward D ⋙ stalk (monomialPoint r n)

private def skyscrapersProjection (X : TopCat.{0}) {C : Type*} [Category C]
    (F : X → C ⥤ Coeff.{0}) (x : X) (V : C) :
    (stalk x).obj ((skyscrapers X F).obj V) ⟶ (F x).obj V := by
  change (stalk x).obj (∏ᶜ fun y : X ↦ (skyscraperSheafFunctor y).obj ((F y).obj V)) ⟶ _
  exact (stalk x).map (Pi.π _ x) ≫ (stalkSkyscraperSheafAdjunction x).counit.app ((F x).obj V)

private def directImageGerm {X Y : TopCat.{0}} (f : X ⟶ Y) (F : Sheaves X) (z : X) :
    (stalk (f z)).obj ((directImage f).obj F) ⟶ (stalk z).obj F :=
  TopCat.Presheaf.stalkPushforward Coeff.{0} f F.obj z

theorem wholePair_terminal (D : OrderedGeometry r) (n : Labels r) (p : SumFiber n) :
    D.terminal Set.univ Set.univ (D.wholePair p.val.1 p.val.2) = monomialPoint r n := by
  let z := D.wholePair p.val.1 p.val.2
  have h : D.terminal Set.univ Set.univ z =
      terminalMap (PositiveTorus r) (secondSet_stable D.coordinates Set.univ) z := rfl
  exact h.trans ((D.terminal_label z).trans
    ((congrArg (fun q : Labels r × Labels r ↦ monomialPoint r (q.1 + q.2))
      (D.wholePair_labels p.val.1 p.val.2)).trans (congrArg (monomialPoint r) p.property)))

/-- The projection from a geometric fibre to the tensor stalk of a labelled point. -/
def orderedFiberProjection (D : OrderedGeometry r) (A B : Set (Labels r))
    (V W : Families r) (n : Labels r) (p : SumFiber n) (z : D.space A B)
    (h : D.terminal A B z = monomialPoint r n)
    (hl : ((D.labels A B z).1.val, (D.labels A B z).2.val) = p.val) :
    (stalk (monomialPoint r n)).obj
      ((directImage (D.terminal A B)).obj ((descendedExterior D A B).obj (V, W))) ⟶
      fiber V p.val.1 ⊗ fiber W p.val.2 := by
  let f := D.terminal A B
  let F := (descendedExterior D A B).obj (V, W)
  let first : (stalk (monomialPoint r n)).obj ((directImage f).obj F) ⟶ (stalk z).obj F :=
    eqToHom (congrArg (fun x ↦ (stalk x).obj ((directImage f).obj F)) h.symm) ≫
      directImageGerm f F z
  let atPoint := skyscrapersProjection (D.space A B)
    (fun y ↦ exteriorAt (D.labels A B y).1.val (D.labels A B y).2.val) z (V, W)
  exact first ≫ atPoint ≫ eqToHom (congrArg
    (fun q : Labels r × Labels r ↦ fiber V q.1 ⊗ fiber W q.2) hl)

/-- The projection from the full geometric fibre at the monomial representative. -/
def pushforwardProjection (D : OrderedGeometry r) (V W : Families r) (n : Labels r)
    (p : SumFiber n) :
    (geometricFiber D n).obj (V, W) ⟶ fiber V p.val.1 ⊗ fiber W p.val.2 :=
  orderedFiberProjection D Set.univ Set.univ V W n p (D.wholePair p.val.1 p.val.2)
    (wholePair_terminal D n p) (D.wholePair_labels p.val.1 p.val.2)

def pointUnit (r : ℕ) : Families r :=
  Discrete.functor fun a ↦ if a = 0 then (𝟙_ Coeff.{0}) else (0 : Coeff.{0})

/-- The direct-sum comparison identifies the components with the germ maps
at the actual ordered points. -/
structure FiberComparison (D : OrderedGeometry r) (V W : Families r) (n : Labels r) where
  iso : (fiberSum n).obj (V, W) ≅ (geometricFiber D n).obj (V, W)
  sameSummand : ∀ p : SumFiber n,
    summand n V W p ≫ iso.hom ≫ pushforwardProjection D V W n p = 𝟙 _
  otherSummand : ∀ p q : SumFiber n, p ≠ q →
    summand n V W p ≫ iso.hom ≫ pushforwardProjection D V W n q = 0

/-- The change of representative at each jet level preserves the quotient point. -/
abbrev orderedJetAction (D : OrderedGeometry r) (c : ContinuousJets r)
    (A B : Set (Labels r)) : JetAction (jetSystem r c) (D.space A B) :=
  trivialJetAction (jetSystem r c) (D.space A B)

/-- On the reduced analytic stages the two maps in the descent diagram are
the projection to the quotient and that projection followed by the label map. -/
structure ExteriorDescent (D : OrderedGeometry r) (c : ContinuousJets r) where
  compare : ∀ (A B : Set (Labels r)) (k : ℕ),
    descendedExterior D A B ⋙ inverseImage (D.jetCover c A B k) ≅
      descendedExteriorAtJet D c A B k
  datum : ∀ (A B : Set (Labels r)) (V W : Families r),
    (orderedJetAction D c A B).Equivariance
      ((DerivedCategory.singleFunctor _ 0).obj ((descendedExterior D A B).obj (V, W)))
  trivial : ∀ A B V W k hk, ((datum A B V W).datum k hk).iso.hom = 𝟙 _
  unique : ∀ A B V W (v : (orderedJetAction D c A B).Equivariance
    ((DerivedCategory.singleFunctor _ 0).obj ((descendedExterior D A B).obj (V, W)))),
    v = datum A B V W
  stalk : ∀ A B (V W : Families r) (z : D.space A B),
    IsIso (skyscrapersProjection (D.space A B)
      (fun y ↦ exteriorAt (D.labels A B y).1.val (D.labels A B y).2.val) z (V, W))

/-- The actual derived direct image on any finite support is in degree zero. -/
def FiniteDirectImage (D : OrderedGeometry r) : Prop :=
  ∀ (A B : Set (Labels r)), A.Finite → B.Finite →
    Nonempty (DerivedCategory.Plus.singleFunctor (Sheaves (D.space A B)) 0 ⋙
        derivedDirectImage (D.terminal A B) ≅
      directImage (D.terminal A B) ⋙ DerivedCategory.Plus.singleFunctor (Sheaves (torusSpace r)) 0)

def supportedPairs (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r)
    (A B : Set (Labels r)) : ObjectProperty (Heart r g c × Heart r g c) :=
  fun VW ↦ familySupport ((stalkFamily r g c).obj VW.1) ⊆ A ∧
    familySupport ((stalkFamily r g c).obj VW.2) ⊆ B

/-- Product on the actual equivariant heart, with its finite and global
sheaf comparisons and its functorial direct-sum stalk description. -/
structure OrderedProduct (D : OrderedGeometry r) (g : StageGeometry r) (c : ContinuousJets r) where
  convolution : Heart r g c × Heart r g c ⥤ Heart r g c
  pushforward : convolution ⋙ forgetPerverse r g c ≅
    (stalkFamily r g c).prod (stalkFamily r g c) ⋙
      geometricPushforward D ⋙ DerivedCategory.singleFunctor _ 0
  finiteSupport : ∀ (A B : Set (Labels r)), A.Finite → B.Finite →
    Nonempty (ObjectProperty.ι (supportedPairs r g c A B) ⋙ convolution ⋙
        forgetPerverse r g c ≅
      ObjectProperty.ι (supportedPairs r g c A B) ⋙
        (stalkFamily r g c).prod (stalkFamily r g c) ⋙ descendedExterior D A B ⋙
        DerivedCategory.Plus.singleFunctor _ 0 ⋙ derivedDirectImage (D.terminal A B) ⋙
        DerivedCategory.Plus.ι)
  stalkIso : ∀ n : Labels r,
    (stalkFamily r g c).prod (stalkFamily r g c) ⋙ fiberSum n ≅
      convolution ⋙ stalkFamily r g c ⋙ familyAt n
  geometricStalkIso : ∀ (V W : Heart r g c) (n : Labels r),
    ∃ e : FiberComparison D ((stalkFamily r g c).obj V) ((stalkFamily r g c).obj W) n,
      (stalkIso n).app (V, W) ≪≫
        (stalk (monomialPoint r n)).mapIso
          ((cohomology (torusSpace r) 0).mapIso (pushforward.app (V, W)) ≪≫
            (DerivedCategory.singleFunctorCompHomologyFunctorIso (Sheaves (torusSpace r)) 0).app _)
        = e.iso

namespace OrderedProduct

variable {D : OrderedGeometry r} {g : StageGeometry r} {c : ContinuousJets r}
variable (P : OrderedProduct D g c)

abbrev Stalk (V : Heart r g c) (a : Labels r) :=
  fiber ((stalkFamily r g c).obj V) a

def includeSummand (V W : Heart r g c) (a b : Labels r) :
    Stalk V a ⊗ Stalk W b ⟶ Stalk (P.convolution.obj (V, W)) (a + b) :=
  summand (a + b) ((stalkFamily r g c).obj V) ((stalkFamily r g c).obj W) ⟨(a, b), rfl⟩ ≫
    (P.stalkIso (a + b)).hom.app (V, W)

def leftSummand (U V W : Heart r g c) (a b d : Labels r) :
    (Stalk U a ⊗ Stalk V b) ⊗ Stalk W d ⟶
      Stalk (P.convolution.obj (P.convolution.obj (U, V), W)) (a + b + d) :=
  (P.includeSummand U V a b ⊗ₘ 𝟙 (Stalk W d)) ≫
    P.includeSummand (P.convolution.obj (U, V)) W (a + b) d

def rightSummand (U V W : Heart r g c) (a b d : Labels r) :
    Stalk U a ⊗ (Stalk V b ⊗ Stalk W d) ⟶
      Stalk (P.convolution.obj (U, P.convolution.obj (V, W))) (a + b + d) :=
  (𝟙 (Stalk U a) ⊗ₘ P.includeSummand V W b d) ≫
    P.includeSummand U (P.convolution.obj (V, W)) a (b + d) ≫
    eqToHom (congrArg (Stalk (P.convolution.obj (U, P.convolution.obj (V, W))))
      (add_assoc a b d).symm)

def associateLeft : Heart r g c × (Heart r g c × Heart r g c) ⥤ Heart r g c :=
  (((CategoryTheory.Prod.fst _ _).prod'
      (CategoryTheory.Prod.snd _ _ ⋙ CategoryTheory.Prod.fst _ _)) ⋙ P.convolution).prod'
    (CategoryTheory.Prod.snd _ _ ⋙ CategoryTheory.Prod.snd _ _) ⋙ P.convolution

def associateRight : Heart r g c × (Heart r g c × Heart r g c) ⥤ Heart r g c :=
  (CategoryTheory.Prod.fst _ _).prod' (CategoryTheory.Prod.snd _ _ ⋙ P.convolution) ⋙ P.convolution

end OrderedProduct

/-- Unit and associativity on the ordered convolution functor. The
associativity comparison acts on the summands of the actual triple quotient. -/
structure OrderedConstraints {D : OrderedGeometry r} {g : StageGeometry r} {c : ContinuousJets r}
    (P : OrderedProduct D g c) where
  unit : Heart r g c
  unitSheaf : (forgetPerverse r g c).obj unit ≅ (DerivedCategory.singleFunctor _ 0).obj
    ((skyscraperSheafFunctor (monomialPoint r 0)).obj (𝟙_ Coeff.{0}))
  unitStalk : (stalkFamily r g c).obj unit ≅ pointUnit r
  leftUnitor : ((Functor.const (Heart r g c)).obj unit).prod' (𝟭 _) ⋙
    P.convolution ≅ 𝟭 _
  rightUnitor : (𝟭 (Heart r g c)).prod' ((Functor.const (Heart r g c)).obj unit) ⋙
    P.convolution ≅ 𝟭 _
  associator : P.associateLeft ≅ P.associateRight
  leftUnitor_stalk : ∀ (V : Heart r g c) (a : Labels r),
    let scalar : (𝟙_ Coeff.{0}) ⟶ OrderedProduct.Stalk unit 0 :=
      eqToHom (by simp [pointUnit]) ≫ unitStalk.inv.app (Discrete.mk 0)
    (scalar ⊗ₘ 𝟙 (OrderedProduct.Stalk V a)) ≫
        P.includeSummand unit V 0 a ≫
        eqToHom (congrArg (OrderedProduct.Stalk (P.convolution.obj (unit, V))) (zero_add a)) ≫
        ((stalkFamily r g c).map (leftUnitor.hom.app V)).app (Discrete.mk a) =
      (λ_ (OrderedProduct.Stalk V a)).hom
  rightUnitor_stalk : ∀ (V : Heart r g c) (a : Labels r),
    let scalar : (𝟙_ Coeff.{0}) ⟶ OrderedProduct.Stalk unit 0 :=
      eqToHom (by simp [pointUnit]) ≫ unitStalk.inv.app (Discrete.mk 0)
    (𝟙 (OrderedProduct.Stalk V a) ⊗ₘ scalar) ≫
        P.includeSummand V unit a 0 ≫
        eqToHom (congrArg (OrderedProduct.Stalk (P.convolution.obj (V, unit))) (add_zero a)) ≫
        ((stalkFamily r g c).map (rightUnitor.hom.app V)).app (Discrete.mk a) =
      (ρ_ (OrderedProduct.Stalk V a)).hom
  associator_stalk : ∀ (U V W : Heart r g c) (p : TripleStage r),
    let (a, b, d) := D.triples p
    P.leftSummand U V W a b d ≫
        ((stalkFamily r g c).map (associator.hom.app (U, V, W))).app
          (Discrete.mk (a + b + d)) =
      (α_ (OrderedProduct.Stalk U a) (OrderedProduct.Stalk V b)
        (OrderedProduct.Stalk W d)).hom ≫ P.rightSummand U V W a b d

/-- Ordered convolution for every complex split torus, including rank zero. -/
def TorusOrderedConvolution : Prop :=
  ∀ r : ℕ, ∃ (D : OrderedGeometry r) (g : StageGeometry r) (c : ContinuousJets r),
    (∀ A B, D.representatives A B) ∧
    D.TripleMaps ∧ FiniteDirectImage D ∧
    Nonempty (ExteriorDescent D c) ∧
    ∃ P : OrderedProduct D g c, Nonempty (OrderedConstraints P)

end RepTheorySurvey.Geometric.TorusOrderedConvolutionSpecs
