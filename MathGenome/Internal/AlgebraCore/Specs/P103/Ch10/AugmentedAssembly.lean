import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.TotalComplexConstruction
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.ShiftsAndCones
import Mathlib.Algebra.Homology.Embedding.StupidTrunc

/-!
Interfaces for paper.tex 2416–2431. An augmented bicomplex is represented by
the whole diagram K, including its column at p = -1. Deleting that column
means restriction to p ≥ 0 followed by extension by zero. This representation
retains arbitrary modules, arbitrary unital rings, and a translated vertical
lower bound. Right modules are obtained over the opposite ring.
-/
namespace P103.Specs.Ch10.AugmentedAssembly
open CategoryTheory CategoryTheory.Limits
open TotalComplexAssembly Complexes ShiftsAndCones
noncomputable section
universe u v

/-- The shape induced on the retained horizontal degrees. -/
def nonnegativeShape (c : ComplexShape ℤ) : ComplexShape {p : ℤ // 0 ≤ p} where
  Rel p q := c.Rel p.val q.val
  next_eq h h' := Subtype.ext (c.next_eq h h')
  prev_eq h h' := Subtype.ext (c.prev_eq h h')

def nonnegativeEmbedding (c : ComplexShape ℤ) : (nonnegativeShape c).Embedding c :=
  ComplexShape.Embedding.mk' _ _ Subtype.val Subtype.val_injective (fun _ _ => Iff.rfl)

instance (c : ComplexShape ℤ) : (nonnegativeEmbedding c).IsRelIff where
  rel' _ _ h := h

variable {R : Type u} [Ring R] {c : ComplexShape ℤ}

/-- The unaugmented bicomplex obtained by deleting the p = -1 column.
All negative columns are deleted, so this definition also makes sense before
the lower support hypothesis is imposed. -/
def unaugmented (K : Bicomplex.{u,v} R c) : Bicomplex.{u,v} R c :=
  K.stupidTrunc (nonnegativeEmbedding c)

def retainedColumnIso (K : Bicomplex.{u,v} R c) (p : ℤ) (hp : 0 ≤ p) :
    (unaugmented K).X p ≅ K.X p :=
  K.stupidTruncXIso (nonnegativeEmbedding c) (i := ⟨p, hp⟩) rfl

/-- These are maps of vertical complexes, not maps of horizontal complexes
across the augmentation boundary. -/
def columnToAugmented (K : Bicomplex.{u,v} R c) (p : ℤ) :
    (unaugmented K).X p ⟶ K.X p :=
  if hp : 0 ≤ p then (retainedColumnIso K p hp).hom else 0

def columnFromAugmented (K : Bicomplex.{u,v} R c) (p : ℤ) :
    K.X p ⟶ (unaugmented K).X p :=
  if hp : 0 ≤ p then (retainedColumnIso K p hp).inv else 0

variable [ComplexShape.TensorSigns c]

/-- Inclusion of the retained summands, in each total degree. -/
def totalToAugmented (K : Bicomplex.{u,v} R c) (n : ℤ) :
    (total (unaugmented K)).X n ⟶ (total K).X n :=
  (unaugmented K).totalDesc (fun p q h =>
    (columnToAugmented K p).f q ≫ totalInclusion K p q n h)

/-- Projection onto the retained summands, in each total degree. -/
def totalFromAugmented (K : Bicomplex.{u,v} R c) (n : ℤ) :
    (total K).X n ⟶ (total (unaugmented K)).X n :=
  K.totalDesc (fun p q h =>
    (columnFromAugmented K p).f q ≫ totalInclusion (unaugmented K) p q n h)

/-- The coordinates (augmentation column, unaugmented total). -/
def augmentedCoordinates (K : Bicomplex.{u,v} R c) (n : ℤ) :
    (total K).X n →ₗ[R] (K.X (-1)).X (n + 1) × (total (unaugmented K)).X n :=
  (totalProjection K (-1) (n + 1) n (by omega)).hom.prod
    (totalFromAugmented K n).hom

/-- The formula which will be proved inverse to the coordinates. -/
def assembleCoordinates (K : Bicomplex.{u,v} R c) (n : ℤ) :
    ((K.X (-1)).X (n + 1) × (total (unaugmented K)).X n) →ₗ[R] (total K).X n :=
  ((totalInclusion K (-1) (n + 1) n (by omega)).hom.comp (LinearMap.fst R _ _)) +
    ((totalToAugmented K n).hom.comp (LinearMap.snd R _ _))

/-- Degree components of the chain augmentation, with horizontal degree zero. -/
def chainAugmentationComponent (K : ChainBicomplex.{u,v} R) (n : ℤ) :
    (total (unaugmented K)).X n ⟶ (K.X (-1)).X n :=
  totalProjection (unaugmented K) 0 n n (by omega) ≫
    (columnToAugmented K 0).f n ≫ (K.d 0 (-1)).f n

/-- Degree components of the cochain augmentation. -/
def cochainAugmentationComponent (K : CochainBicomplex.{u,v} R) (n : ℤ) :
    (K.X (-1)).X n ⟶ (total (unaugmented K)).X n :=
  (K.d (-1) 0).f n ≫ (columnFromAugmented K 0).f n ≫
    totalInclusion (unaugmented K) 0 n n (by omega)

/-- Source coordinates A_(n-1) = Y_n ⊕ X_(n-1), with no index casts hidden
in the statement of the differential or the cone comparison. -/
def chainCoordinates (K : ChainBicomplex.{u,v} R) (n : ℤ) :
    (total K).X (n - 1) →ₗ[R]
      (K.X (-1)).X n × (total (unaugmented K)).X (n - 1) :=
  (totalProjection K (-1) n (n - 1) (by omega)).hom.prod
    (totalFromAugmented K (n - 1)).hom

/-- Complete chain conclusion, including the specific map and all signs.
The support and row exactness hypotheses belong to the theorem below. -/
def ChainRowResult (K : ChainBicomplex.{u,v} R)
    (f : total (unaugmented K) ⟶ K.X (-1)) : Prop :=
  (∀ n, f.f n = chainAugmentationComponent K n) ∧
  QuasiIsomorphism f ∧
  (∀ n (z : (total K).X (n - 1)),
    chainCoordinates K (n - 1) ((total K).d (n - 1) ((n - 1) - 1) z) =
      (-((K.X (-1)).d n (n - 1)) (chainCoordinates K n z).1 +
          (f.f (n - 1)) (chainCoordinates K n z).2,
        (total (unaugmented K)).d (n - 1) ((n - 1) - 1) (chainCoordinates K n z).2)) ∧
  ∃ e : chainShift (total K) ≅ cone f,
    ∀ n (z : (chainShift (total K)).X n),
      chainConeTermEquiv f n ((e.hom.f n) z) =
        ((chainCoordinates K n (chainShiftTermEquiv (total K) n z)).1,
          -(chainCoordinates K n (chainShiftTermEquiv (total K) n z)).2)

/-- Complete cochain conclusion, with the reordered augmented total as cone. -/
def CochainRowResult (K : CochainBicomplex.{u,v} R)
    (f : K.X (-1) ⟶ total (unaugmented K)) : Prop :=
  (∀ n, f.f n = cochainAugmentationComponent K n) ∧
  QuasiIsomorphism f ∧
  (∀ n (z : (total K).X n),
    augmentedCoordinates K (n + 1) ((total K).d n (n + 1) z) =
      (-((K.X (-1)).d (n + 1) ((n + 1) + 1)) (augmentedCoordinates K n z).1,
        (f.f (n + 1)) (augmentedCoordinates K n z).1 +
          (total (unaugmented K)).d n (n + 1) (augmentedCoordinates K n z).2)) ∧
  ∃ e : total K ≅ cone f,
    ∀ n (z : (total K).X n),
      cochainConeTermEquiv f n ((e.hom.f n) z) =
        ((augmentedCoordinates K n z).2, (augmentedCoordinates K n z).1)

set_option linter.unusedVariables false
set_option linter.checkUnivs false

def augmentedCoordinates_inverseType : Prop :=
  ∀ {R : Type u} [Ring R] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c]
    (K : Bicomplex.{u,v} R c)
    (hs : ∀ p q, p < -1 → Subsingleton ((K.X p).X q)) (n : ℤ),
    Function.LeftInverse (assembleCoordinates K n) (augmentedCoordinates K n) ∧
    Function.RightInverse (assembleCoordinates K n) (augmentedCoordinates K n)

def chainAugmentation_existsType : Prop :=
  ∀ {R : Type u} [Ring R] (K : ChainBicomplex.{u,v} R),
    ∃ f : total (unaugmented K) ⟶ K.X (-1),
      ∀ n, f.f n = chainAugmentationComponent K n

def cochainAugmentation_existsType : Prop :=
  ∀ {R : Type u} [Ring R] (K : CochainBicomplex.{u,v} R),
    ∃ f : K.X (-1) ⟶ total (unaugmented K),
      ∀ n, f.f n = cochainAugmentationComponent K n

def chain_rows_quasiIsomorphismType : Prop :=
  ∀ {R : Type u} [Ring R] (K : ChainBicomplex.{u,v} R) (b : ℤ),
    SupportedQuadrant K (-1) b → RowsAcyclic K →
      ∃ f : total (unaugmented K) ⟶ K.X (-1), ChainRowResult K f

def cochain_rows_quasiIsomorphismType : Prop :=
  ∀ {R : Type u} [Ring R] (K : CochainBicomplex.{u,v} R) (b : ℤ),
    SupportedQuadrant K (-1) b → RowsAcyclic K →
      ∃ f : K.X (-1) ⟶ total (unaugmented K), CochainRowResult K f

/-- Deleting the augmented row is deleting the augmented column of K.flip.
The signed interchange specifies the map on the original, unflipped total. -/
def chain_columns_quasiIsomorphismType : Prop :=
  ∀ {R : Type u} [Ring R] (K : ChainBicomplex.{u,v} R) (a : ℤ),
    SupportedQuadrant K a (-1) → ColumnsAcyclic K →
      ∃ g : total (unaugmented K.flip) ⟶ K.flip.X (-1),
        ChainRowResult K.flip g ∧
          QuasiIsomorphism ((signedInterchange (unaugmented K.flip)).hom ≫ g)

def cochain_columns_quasiIsomorphismType : Prop :=
  ∀ {R : Type u} [Ring R] (K : CochainBicomplex.{u,v} R) (a : ℤ),
    SupportedQuadrant K a (-1) → ColumnsAcyclic K →
      ∃ g : K.flip.X (-1) ⟶ total (unaugmented K.flip),
        CochainRowResult K.flip g ∧
          QuasiIsomorphism (g ≫ (signedInterchange (unaugmented K.flip)).inv)

end
end P103.Specs.Ch10.AugmentedAssembly
