import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.Pinning
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.EuclideanComparison
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.FiniteWordClosure
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Lie.CartanSubalgebra
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SerreFiniteType
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.HighestWeightClassification
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RootForm
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Module.Torsion.Free

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u v

namespace LinearAlgebraicGroups.Specs.RationalRealization

open LieAlgebrasAndRepresentations

noncomputable section

open Pinning (AttachedDatum BasedIso BasedRootDatum PinnedGroup SimpleRoot)
open RootGroups (AdditiveLine rootPoint)
open RootData (integralCartan rationalRootAnnihilator extendFunctional)
open CharacterDescent (Character Cocharacter)
open CharacterPairing (characterValue)

variable {ι : Type u} [DecidableEq ι]

/-- The symbols of the Serre presentation, viewed in its quotient. -/
def generator (K : Type*) [CommRing K] (A : Matrix ι ι ℤ)
    (s : CartanMatrix.Generators ι) : Matrix.ToLieAlgebra K A :=
  LieSubmodule.Quotient.mk (FreeLieAlgebra.of K s)

/-- The rational Serre presentation extends to the actual pinned complex
presentation, with the images of all three families of generators specified. -/
def SerreBaseChange : Prop :=
  ∀ {ι : Type u} [DecidableEq ι] (A : Matrix ι ι ℤ),
    ∃ e : (ℂ ⊗[ℚ] Matrix.ToLieAlgebra ℚ A) ≃ₗ⁅ℂ⁆ Serre.Algebra A,
      ∀ s, e (1 ⊗ₜ[ℚ] generator ℚ A s) = generator ℂ A s

/-- The ordinary simultaneous eigenspace of the simple rational Cartan generators. -/
def rationalWeightSpace (A : Matrix ι ι ℤ) (χ : ι → ℚ) :
    Submodule ℚ (Matrix.ToLieAlgebra ℚ A) where
  carrier := {x | ∀ i, ⁅generator ℚ A (.H i), x⁆ = χ i • x}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy i; simp [lie_add, hx i, hy i, smul_add]
  smul_mem' := by
    intro c x hx i
    rw [lie_smul, hx i, smul_comm]

/-- Each rational weight space extends to the corresponding complex weight
space under the same generator-preserving Serre isomorphism. -/
def RationalWeightBaseChange : Prop :=
  ∀ {ι : Type u} [DecidableEq ι] [Fintype ι] (A : Matrix ι ι ℤ),
    ∃ e : (ℂ ⊗[ℚ] Matrix.ToLieAlgebra ℚ A) ≃ₗ⁅ℂ⁆ Serre.Algebra A,
      (∀ s, e (1 ⊗ₜ[ℚ] generator ℚ A s) = generator ℂ A s) ∧
      ∀ χ : ι → ℚ, ((rationalWeightSpace A χ).baseChange ℂ).map e.toLinearEquiv.toLinearMap =
        Serre.weightSpace A (fun i => (χ i : ℂ))

/-- The rational zero and root spaces exhaust the Serre algebra. The zero
space is spanned by the labelled Cartan generators. -/
def RationalSerreDecomposition : Prop :=
  ∀ (D : BasedRootDatum.{u}) [DecidableEq D.base.support],
    let A := RootData.integralCartan D.datum D.base
    let w (j : D.I) : D.base.support → ℚ := fun i => D.datum.pairing j i
    ((rationalWeightSpace A 0) ⊔ (⨆ j, rationalWeightSpace A (w j))) = ⊤ ∧
    (∀ j, Module.finrank ℚ (rationalWeightSpace A (w j)) = 1) ∧
    rationalWeightSpace A 0 = Submodule.span ℚ (Set.range fun i => generator ℚ A (.H i))

/-- Nonzero rational vectors in opposite root lines bracket to a nonzero
element of the rational Cartan. -/
def OppositeRationalRootBracket : Prop :=
  ∀ (D : BasedRootDatum.{u}) [DecidableEq D.base.support] (i : D.I),
    let A := integralCartan D.datum D.base
    let W := rationalWeightSpace A (fun j => D.datum.pairing i j)
    let W' := rationalWeightSpace A (fun j => D.datum.pairing (D.datum.reflectionPerm i i) j)
    ∀ x ∈ W, ∀ y ∈ W', x ≠ 0 → y ≠ 0 →
      ⁅x, y⁆ ∈ rationalWeightSpace A 0 ∧ ⁅x, y⁆ ≠ 0

/-- A root's joint weight on the simple coroots of the Serre algebra. -/
def rootWeight (D : BasedRootDatum.{u}) (j : D.I) : D.base.support → ℂ :=
  fun i => (D.datum.pairing j i : ℂ)

/-- The finite-type complex Serre algebra of the given datum, together with
the rational dimension and the Cartan input for highest-weight theory. -/
def SerreStructure : Prop :=
  ∀ (D : BasedRootDatum.{u}) [DecidableEq D.base.support],
    let A := integralCartan D.datum D.base
    Serre.Triangular A ∧
    Module.Finite ℂ (Serre.Algebra A) ∧
    Module.Finite ℚ (Matrix.ToLieAlgebra ℚ A) ∧
    Module.finrank ℚ (Matrix.ToLieAlgebra ℚ A) = D.base.support.card + Nat.card D.I ∧
    LieAlgebra.radical ℂ (Serre.Algebra A) = ⊥ ∧
    (⨆ χ : D.base.support → ℂ, Serre.weightSpace A χ) = ⊤ ∧
    (∀ χ : D.base.support → ℂ, χ ≠ 0 →
      (Serre.weightSpace A χ ≠ ⊥ ↔ ∃ j, χ = rootWeight D j)) ∧
    (∀ j, Module.finrank ℂ (Serre.weightSpace A (rootWeight D j)) = 1) ∧
    ∃ H : LieSubalgebra ℂ (Serre.Algebra A),
      H.toSubmodule = Serre.cartan A ∧ Serre.weightSpace A 0 = H.toSubmodule ∧
      H.IsCartanSubalgebra

open _root_.Specs.LieAlgebrasAndRepresentations.VermaModules (Direction Regular)
open _root_.Specs.LieAlgebrasAndRepresentations.SerreRelations (simple)
open _root_.Specs.LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient (Normalized)
open _root_.Specs.LieAlgebrasAndRepresentations.RootDecomposition (rootSet_value)

/-- The Cartan and simple-root indexing of the complex Serre presentation. -/
structure CartanIdentification (D : BasedRootDatum.{u}) [DecidableEq D.base.support] where
  finite : Module.Finite ℂ (Serre.Algebra (RootData.integralCartan D.datum D.base))
  cartan : LieSubalgebra ℂ (Serre.Algebra (RootData.integralCartan D.datum D.base))
  isCartan : cartan.IsCartanSubalgebra
  cartanBasis : Module.Basis D.base.support ℂ cartan
  cartanBasis_eq : ∀ i, (cartanBasis i : Serre.Algebra _) =
    Serre.h (RootData.integralCartan D.datum D.base) i
  direction : Direction cartan
  regular : Regular cartan direction
  roots_eq : Set.range (fun j => cartanBasis.constr ℂ (rootWeight D j)) = rootSet_value cartan
  root_height : ∀ j, direction (cartanBasis.constr ℂ (rootWeight D j)) = (D.base.height j : ℝ)
  simpleIndex : D.base.support ≃ simple cartan direction
  simple_eq : ∀ i, (simpleIndex i).val = cartanBasis.constr ℂ (rootWeight D i)
  normalized :
    letI := finite
    Normalized cartan direction
      (fun a => Serre.e (RootData.integralCartan D.datum D.base) (simpleIndex.symm a))
      (fun a => Serre.f (RootData.integralCartan D.datum D.base) (simpleIndex.symm a))

def ComplexCartan : Prop :=
  ∀ (D : BasedRootDatum.{u}) [DecidableEq D.base.support], Nonempty (CartanIdentification D)


/-- Finitely many dominant characters generate the full character lattice as an
abelian group, including the central directions. -/
def DominantGenerators : Prop :=
  ∀ D : BasedRootDatum.{u},
    ∃ s : Finset D.X, (∀ x ∈ s, ∀ i : D.base.support, 0 ≤ D.datum.coroot' i x) ∧
      Submodule.span ℤ (s : Set D.X) = ⊤

section HighestWeightModules

attribute [local instance 100] LieRing.ofAssociativeRing

open UniversalEnvelopingAlgebra renaming ι → envelopingGenerator

variable {R S L L' : Type*} [Field R] [Field S] [Algebra R S]
  [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra S L']

/-- The cyclic left module of an enveloping algebra with the specified relators. -/
abbrev CyclicPresentation (s : Set (UniversalEnvelopingAlgebra R L)) :=
  UniversalEnvelopingAlgebra R L ⧸ Submodule.span (UniversalEnvelopingAlgebra R L) s

def cyclicVector (s : Set (UniversalEnvelopingAlgebra R L)) : CyclicPresentation s :=
  (Submodule.span (UniversalEnvelopingAlgebra R L) s).mkQ 1

def cyclicRepresentation (s : Set (UniversalEnvelopingAlgebra R L)) :
    L →ₗ⁅R⁆ Module.End R (CyclicPresentation s) :=
  ((Algebra.lsmul R R (CyclicPresentation s) :
    UniversalEnvelopingAlgebra R L →ₐ[R] Module.End R (CyclicPresentation s)) :
    UniversalEnvelopingAlgebra R L →ₗ⁅R⁆ Module.End R (CyclicPresentation s)).comp (envelopingGenerator R)

abbrev cyclicLieRingModule (s : Set (UniversalEnvelopingAlgebra R L)) :
    LieRingModule L (CyclicPresentation s) :=
  LieRingModule.compLieHom _ (cyclicRepresentation s)

abbrev cyclicLieModule (s : Set (UniversalEnvelopingAlgebra R L)) :
    @LieModule R L (CyclicPresentation s) _ _ _ _ _ (cyclicLieRingModule s) :=
  LieModule.compLieHom _ (cyclicRepresentation s)

attribute [local instance] cyclicLieRingModule cyclicLieModule

variable (e : (S ⊗[R] L) ≃ₗ⁅S⁆ L')

abbrev extendedCyclicLieRingModule (s : Set (UniversalEnvelopingAlgebra R L)) :
    LieRingModule L' (S ⊗[R] CyclicPresentation s) :=
  LieRingModule.compLieHom _ e.symm.toLieHom

abbrev extendedCyclicLieModule (s : Set (UniversalEnvelopingAlgebra R L)) :
    @LieModule S L' (S ⊗[R] CyclicPresentation s) _ _ _ _ _ (extendedCyclicLieRingModule e s) :=
  LieModule.compLieHom _ e.symm.toLieHom

open _root_.Specs.LieAlgebrasAndRepresentations.VermaModules
  (Direction U borel_value induced_value IsWeightCharacter)
open _root_.Specs.LieAlgebrasAndRepresentations.VermaWeightsUniversal
  (inducedLieRingModule inducedLieModule)
open _root_.Specs.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient
  (simpleQuotient_value quotientHighestVector)

local instance {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    {H : LieSubalgebra ℂ L} {φ : Direction H} {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieRingModule L (induced_value H φ χ) :=
  inducedLieRingModule H φ χ

local instance {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    {H : LieSubalgebra ℂ L} {φ : Direction H} {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieModule ℂ L (induced_value H φ χ) :=
  inducedLieModule H φ χ

def highestRelations {L J : Type*} [LieRing L] [LieAlgebra ℚ L]
    (E F H : J → L) (m : J → ℤ) : Set (UniversalEnvelopingAlgebra ℚ L) :=
  Set.range (fun i => envelopingGenerator ℚ (E i)) ∪
    (Set.range (fun i => envelopingGenerator ℚ (H i) - algebraMap ℚ _ (m i : ℚ)) ∪
      Set.range (fun i => envelopingGenerator ℚ (F i) ^ ((m i).toNat + 1)))

def serreHighestRelations (D : BasedRootDatum) [DecidableEq D.base.support] (weight : D.X) :=
  let A := RootData.integralCartan D.datum D.base
  highestRelations (fun i => generator ℚ A (.E i)) (fun i => generator ℚ A (.F i))
    (fun i => generator ℚ A (.H i)) (fun i => D.datum.coroot' i weight)

/-- The Lie module defined by the rational relations extends to the
canonical complex simple quotient, carrying its cyclic vector to the
complex highest-weight vector. -/
def RationalHighestWeight : Prop :=
  ∀ (D : BasedRootDatum.{u}) [DecidableEq D.base.support] (weight : D.X),
    (∀ i : D.base.support, 0 ≤ D.datum.coroot' i weight) →
    let A := RootData.integralCartan D.datum D.base
    let s := serreHighestRelations D weight
    let L := Matrix.ToLieAlgebra ℚ A
    ∃ e : (ℂ ⊗[ℚ] L) ≃ₗ⁅ℂ⁆ Serre.Algebra A,
      (∀ j, e (1 ⊗ₜ[ℚ] generator ℚ A j) = generator ℂ A j) ∧
      ∃ C : CartanIdentification D,
        let complexWeight := C.cartanBasis.constr ℂ (fun i => (D.datum.coroot' i weight : ℂ))
        letI := extendedCyclicLieRingModule e s
        letI := extendedCyclicLieModule e s
        ∃ χ : U (borel_value C.cartan C.direction) →ₐ[ℂ] ℂ,
          IsWeightCharacter C.cartan C.direction complexWeight χ ∧
          ∃ g : (ℂ ⊗[ℚ] CyclicPresentation s) ≃ₗ⁅ℂ, Serre.Algebra A⁆
              simpleQuotient_value C.cartan C.direction χ,
            g (1 ⊗ₜ[ℚ] cyclicVector s) = quotientHighestVector C.cartan C.direction χ ∧
            Module.Finite ℚ (CyclicPresentation s) ∧ cyclicVector s ≠ 0

def loweringWeight (D : BasedRootDatum.{u}) (weight : D.X) (w : List D.base.support) : D.X :=
  weight - (w.map fun i => D.datum.root i).sum

def loweringWord (D : BasedRootDatum.{u}) [DecidableEq D.base.support] (weight : D.X) :
    List D.base.support → CyclicPresentation (serreHighestRelations D weight)
  | [] => cyclicVector (serreHighestRelations D weight)
  | j :: w =>
    let A := RootData.integralCartan D.datum D.base
    cyclicRepresentation (serreHighestRelations D weight) (generator ℚ A (.F j))
      (loweringWord D weight w)

/-- The rational presentation is spanned by lowering words with their full
lattice labels, with a lowering by a simple root at each step. -/
def RationalWeightWords : Prop :=
  ∀ (D : BasedRootDatum.{u}) [DecidableEq D.base.support] (weight : D.X),
    let A := RootData.integralCartan D.datum D.base
    let s := serreHighestRelations D weight
    (∀ w i, cyclicRepresentation s (generator ℚ A (.H i)) (loweringWord D weight w) =
      (D.datum.coroot' i (loweringWeight D weight w) : ℚ) • loweringWord D weight w) ∧
    Submodule.span ℚ (Set.range (loweringWord D weight)) = ⊤

/-- A finite rational weight basis whose labels come from the original
character lattice and include the chosen dominant character. -/
def RationalWeightBasis : Prop :=
  ∀ (D : BasedRootDatum.{u}) [DecidableEq D.base.support] (weight : D.X),
    (∀ i : D.base.support, 0 ≤ D.datum.coroot' i weight) →
    let s := serreHighestRelations D weight
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℚ (CyclicPresentation s))
      (words : Fin n → List D.base.support),
      (∀ j, b j = loweringWord D weight (words j)) ∧ ∃ j, words j = []

/-- A family of rational lowering-word bases whose weight labels generate the full lattice. -/
def DominantWeightFamily : Prop :=
  ∀ (D : BasedRootDatum.{u}) [DecidableEq D.base.support],
    ∃ (s : Finset D.X) (n : s → ℕ)
      (basis : ∀ x : s, Module.Basis (Fin (n x)) ℚ (CyclicPresentation (serreHighestRelations D x)))
      (words : (Σ x : s, Fin (n x)) → List D.base.support),
        (∀ x : s, ∀ i : D.base.support, 0 ≤ D.datum.coroot' i x) ∧
        (∀ x : s, ∀ j, basis x j = loweringWord D x (words ⟨x, j⟩)) ∧
        Submodule.span ℤ (Set.range fun i : Σ x : s, Fin (n x) => loweringWeight D i.1 (words i)) = ⊤

def rationalCharacter (D : BasedRootDatum.{u}) (x : D.X) : (ℚ ⊗[ℤ] D.Y) →ₗ[ℚ] ℚ :=
  extendFunctional ℚ (D.datum.toLinearMap x)

/-- The action of the Serre algebra enlarged by the common root annihilator.
On a lowering word the central character is the restriction of its full weight. -/
def RationalCentralAction : Prop :=
  ∀ (D : BasedRootDatum.{u}) [DecidableEq D.base.support] (weight : D.X),
    let A := integralCartan D.datum D.base
    let L := Matrix.ToLieAlgebra ℚ A
    let Z := rationalRootAnnihilator D.datum
    let s := serreHighestRelations D weight
    ∃ ρ : (L × Z) →ₗ[ℚ] Module.End ℚ (CyclicPresentation s),
      (∀ x y, ρ (⁅x.1, y.1⁆, 0) = ⁅ρ x, ρ y⁆) ∧
      (∀ x, ρ (x, 0) = cyclicRepresentation s x) ∧
      (∀ z v, ρ (0, z) v = rationalCharacter D weight z • v) ∧
      (∀ (w : List D.base.support) (z : Z),
        ρ (0, z) (loweringWord D weight w) =
          rationalCharacter D (loweringWeight D weight w) z • loweringWord D weight w)

end HighestWeightModules

/-- The rational Cartan with its central summand is the full rational
cocharacter space, with the simple Cartan generators marked. -/
def RationalCartanLattice : Prop :=
  ∀ (D : BasedRootDatum.{u}) [DecidableEq D.base.support],
    let A := RootData.integralCartan D.datum D.base
    let Z := RootData.rationalRootAnnihilator D.datum
    ∃ e : (rationalWeightSpace A 0 × Z) ≃ₗ[ℚ] (ℚ ⊗[ℤ] D.Y),
      (∀ i : D.base.support, ∃ h : rationalWeightSpace A 0,
        h.val = generator ℚ A (.H i) ∧ e (h, 0) = 1 ⊗ₜ[ℤ] D.datum.coroot i) ∧
      ∀ z : Z, e (0, z) = z.val

/-- Characters generating the integral lattice separate rational cocharacters. -/
def RationalWeightsDetectCocharacters : Prop :=
  ∀ (D : BasedRootDatum.{u}) {J : Type u} (w : J → D.X),
    Submodule.span ℤ (Set.range w) = ⊤ →
    Function.Injective (fun (z : ℚ ⊗[ℤ] D.Y) (j : J) => rationalCharacter D (w j) z)

section CartanAction

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The eigenvalues of the full rational Cartan on the lowering words are
the original lattice characters, evaluated on the rational cocharacter space. -/
def RationalCartanAction : Prop :=
  ∀ (D : BasedRootDatum.{u}) [DecidableEq D.base.support],
    let A := integralCartan D.datum D.base
    let L := Matrix.ToLieAlgebra ℚ A
    let H := rationalWeightSpace A 0
    let Z := rationalRootAnnihilator D.datum
    ∃ e : (H × Z) ≃ₗ[ℚ] (ℚ ⊗[ℤ] D.Y),
      (∀ i : D.base.support, ∃ h : H,
        h.val = generator ℚ A (.H i) ∧ e (h, 0) = 1 ⊗ₜ[ℤ] D.datum.coroot i) ∧
      (∀ z : Z, e (0, z) = z.val) ∧
      ∀ weight : D.X, let s := serreHighestRelations D weight
        ∃ ρ : (L × Z) →ₗ[ℚ] Module.End ℚ (CyclicPresentation s),
          (∀ x y, ρ (⁅x.1, y.1⁆, 0) = ⁅ρ x, ρ y⁆) ∧
          (∀ x, ρ (x, 0) = cyclicRepresentation s x) ∧
          ∀ (h : H) (z : Z) (w : List D.base.support),
            ρ (h.val, z) (loweringWord D weight w) =
              rationalCharacter D (loweringWeight D weight w) (e (h, z)) • loweringWord D weight w

end CartanAction

/-- The generic point of a dominant word map lies in its smooth locus in
characteristic zero, for integral domain and image. -/
def DominantGenericSmoothness : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (_p : Y ⟶ Spec (.of k))
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] [IsDominant f],
    genericPoint X ∈ f.smoothLocus

section WordMaps

open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
open FiniteWordClosure (power wordDomain evaluate)

/-- A pointed affine family whose powers are integral generates an affine
closed subgroup by a schematically dominant finite word. -/
def WordGeneratedGroup : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (X : SchemeOver k)
    (f : X ⟶ G.val.X) (x₀ : 𝟙_ (SchemeOver k) ⟶ X),
    IsAffine X.left → x₀ ≫ f = 1 → (∀ n, IsIntegral (power X n).left) →
    ∃ (N : ClosedSubgroup G.val) (n : ℕ) (w : wordDomain X n ⟶ N.group.X),
      0 < n ∧ IsIntegral N.group.X.left ∧ IsSchemeTheoreticallyDominant w.left ∧
      (∀ (K : Type u) [Field K] [Algebra k K], IsSchemeTheoreticallyDominant ((baseChange k K).map w).left) ∧
      (∃ a : X ⟶ N.group.X, a ≫ N.inclusion.hom.hom = f) ∧
      (∀ M : ClosedSubgroup G.val, (∃ a : X ⟶ M.group.X, a ≫ M.inclusion.hom.hom = f) →
        ∃ j : N.group ⟶ M.group, j ≫ M.inclusion = N.inclusion) ∧
      ∀ (S : SchemeOver k) (p : S ⟶ wordDomain X n),
        p ≫ w ≫ N.inclusion.hom.hom = evaluate f n p

end WordMaps

/-- A dual-number point at the generic point of the image of a dominant
affine morphism lifts at the generic point of the source. -/
def DominantGenericLift : Prop :=
  ∀ {A B : Type u} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [CharZero A] [Algebra A B] [Algebra.FiniteType A B],
    Function.Injective (algebraMap A B) →
    ∀ q : A →+* DualNumber (FractionRing B),
      (∀ a, (q a).fst = algebraMap B (FractionRing B) (algebraMap A B a)) →
      ∃ p : B →+* DualNumber (FractionRing B),
        (∀ b, (p b).fst = algebraMap B (FractionRing B) b) ∧
        p.comp (algebraMap A B) = q

/-- A presentation whose positively indexed roots are those of the specified Borel. -/
structure Realization (D : BasedRootDatum.{u}) {k : Type u} [Field k]
    (A : AdditiveLine k) where
  pinned : PinnedGroup A
  attached : AttachedDatum pinned.pair
  datumIso : BasedIso D attached.toBased

/-- The indicated simple index of the input datum labels a root of the model. -/
def Realization.simpleRoot {D : BasedRootDatum.{u}} {k : Type u} [Field k]
    {A : AdditiveLine k} (R : Realization D A) (i : D.base.support) :
    SimpleRoot R.pinned.pair :=
  ⟨R.datumIso.val.indexEquiv i.val, R.attached.simple_iff _ |>.mp <| by
    let f := R.datumIso.val.indexEquiv
    have hf : f '' (D.base.support : Set D.I) = R.attached.toBased.base.support :=
      R.datumIso.property
    have hi : f i.val ∈ f '' (D.base.support : Set D.I) := ⟨i.val, i.property, rfl⟩
    exact Eq.mp (congrArg (fun S : Set R.attached.toBased.I => f i.val ∈ S) hf) hi⟩

/-- The ambient pinned root map labelled by a simple index of the input datum. -/
def Realization.rootMap {D : BasedRootDatum.{u}} {k : Type u} [Field k]
    {A : AdditiveLine k} (R : Realization D A) (i : D.base.support) :
    A.group ⟶ R.pinned.pair.G.val :=
  (R.pinned.pin (R.simpleRoot i)).val.hom ≫
    (R.pinned.roots (R.simpleRoot i).val).val.inclusion

/-- The split torus with character lattice the given full lattice X. -/
def diagonalTorus (k : Type u) [Field k] (D : BasedRootDatum.{u}) :
    AffineAlgebraicGroup k :=
  letI : Module.Finite ℤ D.X := D.finiteX
  letI : Group.FG (Multiplicative D.X) :=
    GroupFG.iff_add_fg.mpr (Module.Finite.iff_addGroup_fg.mp D.finiteX)
  DiagonalizableGroups.diagonalGroup k (Multiplicative D.X)

section MatrixGroups

open StandardGroups (generalLinearPoints)
open Pinning (SplitBorelPair)
open DiagonalizableGroups (groupAlgebra groupAlgebraMap characterValuedPoints)

variable {k J : Type u} [Field k] [CharZero k] [Fintype J] [DecidableEq J]

abbrev matrixAlgebra (R : TestAlgebra k) : Algebra ℚ R :=
  ((algebraMap k R).comp (algebraMap ℚ k)).toAlgebra

def exponentialMatrix (N : Matrix J J k) (R : TestAlgebra k) (t : R) : Matrix J J R :=
  letI := matrixAlgebra R
  IsNilpotent.exp (t • (algebraMap k R).mapMatrix N)

/-- The linear term is the differential on the dual-number parameter. -/
def MatrixExponentialSquareZero : Prop :=
  ∀ {k J : Type u} [Field k] [CharZero k] [Fintype J] [DecidableEq J]
    (N : Matrix J J k) (R : TestAlgebra k) {t : R},
      t ^ 2 = 0 → exponentialMatrix N R t = 1 + t • (algebraMap k R).mapMatrix N

/-- A nilpotent matrix exponentiates to a group-scheme map over the
characteristic-zero ground field, with its value specified on every test algebra. -/
def MatrixExponential : Prop :=
  ∀ (k J : Type u) [Field k] [CharZero k] [Fintype J] [DecidableEq J],
    ∃ (A : AdditiveLine k) (G : AffineAlgebraicGroup k)
      (g : (groupPointsFunctor k).obj G.val ≅ generalLinearPoints k J),
      ∀ N : Matrix J J k, IsNilpotent N →
        ∃ f : A.group ⟶ G.val,
          (∀ (R : TestAlgebra k) (t : R),
            ((g.hom.app R).hom (rootPoint f R t)).val = exponentialMatrix N R t) ∧
          (N ≠ 0 → IsClosedImmersion f.hom.hom.left)

/-- For nilpotent `n`, conjugation by its exponential is the exponential
of the nilpotent commutator operator. -/
def ExponentialAdjoint : Prop :=
  ∀ {A : Type u} [Ring A] [Algebra ℚ A] (n : A), IsNilpotent n →
    ∃ D : Module.End ℚ A, IsNilpotent D ∧ (∀ x, D x = n * x - x * n) ∧
      ∀ x, IsNilpotent.exp D x = IsNilpotent.exp n * x * IsNilpotent.exp (-n)

/-- A matrix that shifts lattice weights by a nonzero weight is nilpotent
and intertwines the diagonal matrices by the corresponding character. -/
def WeightShiftMatrix : Prop :=
  ∀ {J X : Type u} {k : Type v} [Fintype J] [DecidableEq J] [AddCommGroup X]
    [Module.IsTorsionFree ℤ X] [Field k] (w : J → X) (α : X) (N : Matrix J J k),
    α ≠ 0 → (∀ i j, N i j ≠ 0 → w i = w j + α) →
    IsNilpotent N ∧ ∀ (R : TestAlgebra k) (χ : Multiplicative X →* Rˣ),
      let D := Matrix.diagonal (fun j => (χ (Multiplicative.ofAdd (w j))).val)
      let N' := (algebraMap k R).mapMatrix N
      D * N' = (χ (Multiplicative.ofAdd α)).val • (N' * D)

/-- Conjugating the root exponential by the diagonal weight action scales
its additive parameter by the root character on each test algebra. -/
def WeightShiftExponential : Prop :=
  ∀ {J X k : Type u} [Fintype J] [DecidableEq J] [AddCommGroup X]
    [Module.IsTorsionFree ℤ X] [Field k] [CharZero k]
    (w : J → X) (α : X) (N : Matrix J J k),
    α ≠ 0 → (∀ i j, N i j ≠ 0 → w i = w j + α) →
    ∀ (R : TestAlgebra k) (χ : Multiplicative X →* Rˣ) (t : R),
      let D := Matrix.diagonal (fun j => (χ (Multiplicative.ofAdd (w j))).val)
      D * exponentialMatrix N R t = exponentialMatrix N R ((χ (Multiplicative.ofAdd α)).val * t) * D

section RationalMatrixAction

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The direct sum of the rational highest-weight modules in their weight
bases gives a faithful matrix representation with the prescribed root shifts. -/
def RationalMatrixAction : Prop :=
  ∀ (D : BasedRootDatum.{u}) [DecidableEq D.base.support],
    let A := integralCartan D.datum D.base
    let L := Matrix.ToLieAlgebra ℚ A
    let H := rationalWeightSpace A 0
    let Z := rationalRootAnnihilator D.datum
    ∃ (J : Type u) (_ : Fintype J) (_ : DecidableEq J) (w : J → D.X)
      (e : (H × Z) ≃ₗ[ℚ] (ℚ ⊗[ℤ] D.Y)) (ρ : (L × Z) →ₗ[ℚ] Matrix J J ℚ),
      (∀ x y, ρ (⁅x.1, y.1⁆, 0) = ⁅ρ x, ρ y⁆) ∧
      (∀ i : D.base.support, ∃ h : H,
        h.val = generator ℚ A (.H i) ∧ e (h, 0) = 1 ⊗ₜ[ℤ] D.datum.coroot i) ∧
      (∀ z : Z, e (0, z) = z.val) ∧
      Submodule.span ℤ (Set.range w) = ⊤ ∧
      (∀ h : H, ∀ z : Z, ρ (h.val, z) = Matrix.diagonal fun j => rationalCharacter D (w j) (e (h, z))) ∧
      Function.Injective ρ ∧
      ∀ (i : D.I) (x : L), x ∈ rationalWeightSpace A (fun j => D.datum.pairing i j) →
        (∀ a b, ρ (x, 0) a b ≠ 0 → w a = w b + D.datum.root i) ∧
        IsNilpotent (ρ (x, 0))

end RationalMatrixAction

/-- Weights that generate the integral character lattice give a closed
diagonal representation of its split torus in the chosen matrix group. -/
def FaithfulDiagonalAction : Prop :=
  ∀ (k : Type u) [Field k] (D : BasedRootDatum.{u}) (J : Type u) [Fintype J] [DecidableEq J]
    (w : J → D.X), Submodule.span ℤ (Set.range w) = ⊤ →
    ∀ (G : AffineAlgebraicGroup k)
      (g : (groupPointsFunctor k).obj G.val ≅ generalLinearPoints k J),
      ∃ θ : (groupPointsFunctor k).obj (diagonalTorus k D).val ≅
          characterValuedPoints k (Multiplicative D.X),
        (∀ (R : TestAlgebra k) (a : MonoidAlgebra k (Multiplicative D.X) →ₐ[k] R)
          (t : Points (diagonalTorus k D).val.X R),
          t.left = Spec.map (CommRingCat.ofHom a.toRingHom) → ∀ m : Multiplicative D.X,
            ((show Multiplicative D.X →* Rˣ from (θ.hom.app R).hom t) m).val = a (MonoidAlgebra.single m 1)) ∧
        ∃ f : (diagonalTorus k D).val ⟶ G.val,
          IsClosedImmersion f.hom.hom.left ∧ ∀ (R : TestAlgebra k)
            (t : Points (diagonalTorus k D).val.X R),
            ((g.hom.app R).hom (t ≫ f.hom.hom)).val =
              Matrix.diagonal (fun i => ((show Multiplicative D.X →* Rˣ from (θ.hom.app R).hom t)
                (Multiplicative.ofAdd (w i))).val)

/-- Field extension of a split diagonalizable group carries each exponent to
the same exponent and commutes with precomposition on the character group. -/
def DiagonalScalarExtension : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K],
    ∃ e : ∀ (M : Type u) [CommGroup M],
        (groupBaseChange k K).obj (specGroup (groupAlgebra k M)) ≅ specGroup (groupAlgebra K M),
      ∀ (M N : Type u) [CommGroup M] [CommGroup N] (f : M →* N),
        (groupBaseChange k K).map (specGroupMap (groupAlgebraMap k f)) ≫ (e M).hom =
          (e N).hom ≫ specGroupMap (groupAlgebraMap K f)

/-- The split diagonal torus is its own geometrically maximal torus
and Borel in the characteristic-zero construction. -/
def SplitDiagonalPair : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (D : BasedRootDatum.{u}),
    ∃ P : SplitBorelPair k, ∃ _h : P.G = diagonalTorus k D,
      IsIso P.T.inclusion ∧ IsIso P.B.inclusion

end MatrixGroups

/-- Extension of scalars of the standard additive line keeps its test-algebra parameter. -/
def AdditiveScalarExtension : Prop :=
  ∀ (k : Type u) [Field k], ∃ A : AdditiveLine k,
    ∀ (K : Type u) [Field K] [Algebra k K],
      ∃ (B : AdditiveLine K) (e : (groupBaseChange k K).obj A.group ≅ B.group),
        ∀ (R : TestAlgebra K) (t : R),
          baseChangePoint k K A.group.X R (rootPoint (A := B) e.inv R t) =
            rootPoint (𝟙 A.group) ((restrictTestAlgebra k K).obj R) t

/-- A universe-polymorphic copy of the rational ground field. -/
abbrev RationalField := ULift.{u} ℚ

def multiplicativeLine (k : Type u) [Field k] : GroupScheme k :=
  specGroup (DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters)

/-- Extension of scalars preserves the Laurent coordinate on the multiplicative line. -/
def MultiplicativeScalarExtension : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K],
    ∃ e : (groupBaseChange k K).obj (multiplicativeLine k) ≅ multiplicativeLine K,
      ∀ (R : TestAlgebra K) (t : Points (multiplicativeLine K).X R),
        characterValue (𝟙 (multiplicativeLine k)) ((restrictTestAlgebra k K).obj R)
          (baseChangePoint k K (multiplicativeLine k).X R (t ≫ e.inv.hom.hom)) =
          characterValue (𝟙 (multiplicativeLine K)) R t

/-- The rational model and its field extension have the same torus, Borel,
labelled root coordinates and full lattice markings after scalar extension. -/
structure ExtendsRational {D : BasedRootDatum.{u}} {A : AdditiveLine (RationalField.{u})}
    {k : Type u} [Field k] [Algebra (RationalField.{u}) k] {B : AdditiveLine k}
    (Q : Realization D A) (K : Realization D B) where
  group : (groupBaseChange RationalField k).obj Q.pinned.pair.G.val ≅ K.pinned.pair.G.val
  torus : (groupBaseChange RationalField k).obj Q.pinned.pair.T.group ≅ K.pinned.pair.T.group
  borel : (groupBaseChange RationalField k).obj Q.pinned.pair.B.group ≅ K.pinned.pair.B.group
  additive : (groupBaseChange RationalField k).obj A.group ≅ B.group
  multiplicative : (groupBaseChange RationalField k).obj (multiplicativeLine RationalField) ≅
    multiplicativeLine k
  additive_parameter : ∀ (R : TestAlgebra k) (t : R),
    baseChangePoint RationalField k A.group.X R (rootPoint (A := B) additive.inv R t) =
      rootPoint (𝟙 A.group) ((restrictTestAlgebra RationalField k).obj R) t
  multiplicative_parameter :
    ∀ (R : TestAlgebra k) (t : AdjointRepresentation.GroupPoints (multiplicativeLine k) R),
      characterValue (𝟙 (multiplicativeLine RationalField))
          ((restrictTestAlgebra RationalField k).obj R)
          (baseChangePoint RationalField k (multiplicativeLine RationalField).X R
            (t ≫ multiplicative.inv.hom.hom)) =
        characterValue (𝟙 (multiplicativeLine k)) R t
  torus_comm : (groupBaseChange RationalField k).map Q.pinned.pair.T.inclusion ≫ group.hom =
    torus.hom ≫ K.pinned.pair.T.inclusion
  borel_comm : (groupBaseChange RationalField k).map Q.pinned.pair.B.inclusion ≫ group.hom =
    borel.hom ≫ K.pinned.pair.B.inclusion
  pin_comm : ∀ i, (groupBaseChange RationalField k).map (Q.rootMap i) ≫ group.hom =
    additive.hom ≫ K.rootMap i
  character_comm : ∀ x : D.X,
    (groupBaseChange RationalField k).map
        (Additive.toMul (Q.datumIso.val.weightEquiv x) : Character Q.pinned.pair.T.group) ≫
      multiplicative.hom =
    torus.hom ≫ (Additive.toMul (K.datumIso.val.weightEquiv x) : Character K.pinned.pair.T.group)
  cocharacter_comm : ∀ y : D.Y,
    (groupBaseChange RationalField k).map
        (Additive.toMul (Q.datumIso.val.coweightEquiv.symm y) : Cocharacter Q.pinned.pair.T.group) ≫
      torus.hom =
    multiplicative.hom ≫
      (Additive.toMul (K.datumIso.val.coweightEquiv.symm y) : Cocharacter K.pinned.pair.T.group)

/-- The realization for a rootless datum, with its two full lattice markings
and extension to every characteristic-zero field. -/
def RootlessRealization : Prop :=
  ∀ (D : BasedRootDatum.{u}), IsEmpty D.I →
    ∃ (A : AdditiveLine (RationalField.{u})) (Q : Realization D A),
      Nonempty (Q.pinned.pair.G.val ≅ (diagonalTorus RationalField D).val) ∧
      ∀ (k : Type u) [Field k] [CharZero k],
        letI : Algebra (RationalField.{u}) k :=
          ((algebraMap ℚ k).comp ULift.ringEquiv.toRingHom).toAlgebra
        ∃ (B : AdditiveLine k) (K : Realization D B), Nonempty (ExtendsRational Q K)

/-- The complex Cartan coroots compare with the given coroots on all roots. -/
def ComplexCorootPairings : Prop :=
  ∀ (D : BasedRootDatum.{u}) [DecidableEq D.base.support] (C : CartanIdentification D),
    letI := C.finite
    ∀ i j : D.I, (C.cartanBasis.constr ℂ (rootWeight D j))
      (_root_.Specs.LieAlgebrasAndRepresentations.RootForm.coroot_value C.cartan
        (C.cartanBasis.constr ℂ (rootWeight D i))) = (D.datum.pairing j i : ℂ)

/-- Opposite roots bracket to the prescribed coroot line in the full
cocharacter space, with the identification marked on the simple generators. -/
def RationalCorootBracket : Prop :=
  ∀ (D : BasedRootDatum.{u}) [DecidableEq D.base.support],
    let A := integralCartan D.datum D.base
    let L := Matrix.ToLieAlgebra ℚ A
    let H := rationalWeightSpace A 0
    let Z := rationalRootAnnihilator D.datum
    ∀ e : (H × Z) ≃ₗ[ℚ] (ℚ ⊗[ℤ] D.Y),
      (∀ i : D.base.support, ∃ h : H,
        h.val = generator ℚ A (.H i) ∧ e (h, 0) = 1 ⊗ₜ[ℤ] D.datum.coroot i) →
      ∀ (i : D.I) (x y : L),
        x ∈ rationalWeightSpace A (fun s => D.datum.pairing i s) →
        y ∈ rationalWeightSpace A (fun s => D.datum.pairing (D.datum.reflectionPerm i i) s) →
        x ≠ 0 → y ≠ 0 →
        ∃ (h : H) (r : ℚ), r ≠ 0 ∧ h.val = ⁅x, y⁆ ∧
          e (h, 0) = r • (1 ⊗ₜ[ℤ] D.datum.coroot i)

/-- Every characteristic-zero scalar extension of the rational Serre algebra
has zero solvable radical. -/
def SerreSemisimpleOver : Prop :=
  ∀ (D : BasedRootDatum.{u}) [DecidableEq D.base.support] (K : Type u) [Field K] [CharZero K],
    LieAlgebra.radical K (K ⊗[ℚ] Matrix.ToLieAlgebra ℚ (integralCartan D.datum D.base)) = ⊥

section MatrixIdeals

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A faithful matrix Lie algebra with diagonal kernel in a semisimple
quotient has zero ideals of nilpotent matrices. -/
def NilpotentMatrixIdeal : Prop :=
  ∀ {K J L S : Type u} [Field K] [Fintype J] [DecidableEq J]
    [LieRing L] [LieAlgebra K L] [Module.Finite K L] [LieRing S] [LieAlgebra K S]
    [CharZero K] (π : L →ₗ⁅K⁆ S), Function.Surjective π →
    LieAlgebra.radical K S = ⊥ → ∀ (ρ : L →ₗ⁅K⁆ Matrix J J K), Function.Injective ρ →
    (∀ x, π x = 0 → ∃ d : J → K, ρ x = Matrix.diagonal d) →
    ∀ I : LieIdeal K L, (∀ x ∈ I, IsNilpotent (ρ x)) → I = ⊥

end MatrixIdeals

section ScalarExtensionOfMatrices

open StandardGroups (generalLinearPoints)
open AdjointRepresentation (GroupPoints)

variable {k K J : Type u} [Field k] [Field K] [Algebra k K] [Fintype J] [DecidableEq J]

/-- The point identification of general linear groups commutes with scalar extension. -/
def GeneralLinearScalarExtension : Prop :=
  ∀ {k K J : Type u} [Field k] [Field K] [Algebra k K] [Fintype J] [DecidableEq J]
    (G : AffineAlgebraicGroup k) (H : AffineAlgebraicGroup K)
    (g : (groupPointsFunctor k).obj G.val ≅ generalLinearPoints k J)
    (h : (groupPointsFunctor K).obj H.val ≅ generalLinearPoints K J),
    ∃ e : (groupBaseChange k K).obj G.val ≅ H.val,
      ∀ (R : TestAlgebra K) (p : GroupPoints ((groupBaseChange k K).obj G.val) R),
        h.hom.app R (p ≫ e.hom.hom.hom) =
          g.hom.app ((restrictTestAlgebra k K).obj R) (baseChangePoint k K G.val.X R p)

/-- Extending the coefficients of the exponential preserves its polynomial value. -/
def ExponentialScalarExtension : Prop :=
  ∀ {k K J : Type u} [Field k] [Field K] [Algebra k K] [Fintype J] [DecidableEq J]
    [CharZero k] [CharZero K] (N : Matrix J J k) (R : TestAlgebra K) (t : R),
    exponentialMatrix ((algebraMap k K).mapMatrix N) R t =
      exponentialMatrix N ((restrictTestAlgebra k K).obj R) t

end ScalarExtensionOfMatrices

/-- At a generic point of the source of a dominant affine morphism,
every dual-number point through its image has a lift. -/
def DominantAffinePointLift : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {X Y : SchemeOver k}
    [IsAffine X.left] [IsAffine Y.left] [IsIntegral X.left] [IsIntegral Y.left]
    (w : X ⟶ Y) [LocallyOfFiniteType w.left] [IsSchemeTheoreticallyDominant w.left],
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (x : Points X (CommAlgCat.of k K)),
      ∀ (q : Points Y (CommAlgCat.of k (DualNumber K))),
        mapPoints (AdjointRepresentation.reduction (CommAlgCat.of k K)) q = x ≫ w →
        ∃ p : Points X (CommAlgCat.of k (DualNumber K)),
          mapPoints (AdjointRepresentation.reduction (CommAlgCat.of k K)) p = x ∧ p ≫ w = q

section GeneratedWordLieBound

open StandardGroups (generalLinearPoints)
open AdjointRepresentation (GroupPoints reduction)
open FiniteWordClosure (wordDomain evaluate)
open InfinitesimalCommutator (matrixDifferential)

set_option backward.isDefEq.respectTransparency false in
/-- A matrix Lie bound for a dominant multiplication word. Each generator
preserves the extended subspace under constant conjugation, and its
translated differential lies in that subspace. -/
def WordMatrixLieBound : Prop :=
  ∀ {k J : Type u} [Field k] [Fintype J] [DecidableEq J] [CharZero k]
    {G H : GroupScheme k} {X : SchemeOver k}
    (g : (groupPointsFunctor k).obj G ≅ generalLinearPoints k J)
    (i : H ⟶ G) (f : X ⟶ G.X) (n : ℕ) (w : wordDomain X n ⟶ H.X)
    [IsAffine (wordDomain X n).left] [IsIntegral (wordDomain X n).left]
    [IsAffine H.X.left] [IsIntegral H.X.left]
    [LocallyOfFiniteType w.left] [IsSchemeTheoreticallyDominant w.left],
    (∀ (S : SchemeOver k) (p : S ⟶ wordDomain X n),
      p ≫ w ≫ i.hom.hom = evaluate f n p) →
    ∀ L : Submodule k (Matrix J J k),
      (∀ (K : Type u) [Field K] [Algebra k K],
        let R := CommAlgCat.of k (DualNumber K)
        let L' := Submodule.span K ((algebraMap k K).mapMatrix '' (L : Set (Matrix J J k)))
        ∀ x : Points X R,
          let z : Matrix.GeneralLinearGroup J (DualNumber K) := (g.hom.app R).hom (x ≫ f)
          let a := Matrix.GeneralLinearGroup.map (TrivSqZeroExt.fstHom K K K).toRingHom z
          (∀ v ∈ L', a.val * v * a⁻¹.val ∈ L') ∧
          (∀ v ∈ L', a⁻¹.val * v * a.val ∈ L') ∧
          (Matrix.of fun p q => (z.val p q).snd) * a⁻¹.val ∈ L') →
      ∀ p : Lie k H, matrixDifferential i g p ∈ L

end GeneratedWordLieBound

section MatrixRootOperators

/-- The rational matrix Lie subspace is spanned by the full marked Cartan
and one nilpotent operator in each root line. -/
def RationalRootOperators : Prop :=
    ∀ (D : BasedRootDatum.{u}) [DecidableEq D.base.support],
    ∃ (J : Type u) (_ : Fintype J) (_ : DecidableEq J) (w : J → D.X)
      (d : (ℚ ⊗[ℤ] D.Y) →ₗ[ℚ] Matrix J J ℚ)
      (N : D.I → Matrix J J ℚ) (L : Submodule ℚ (Matrix J J ℚ)),
      Submodule.span ℤ (Set.range w) = ⊤ ∧ Function.Injective d ∧
      (∀ y, d y = Matrix.diagonal fun a => rationalCharacter D (w a) y) ∧
      L = LinearMap.range d ⊔ ⨆ i, ℚ ∙ N i ∧
      (∀ x ∈ L, ∀ y ∈ L, x * y - y * x ∈ L) ∧
      (∀ i, N i ≠ 0 ∧ IsNilpotent (N i) ∧
        ∀ a b, N i a b ≠ 0 → w a = w b + D.datum.root i) ∧
      (∀ i, ∃ c : ℚ, c ≠ 0 ∧
        N i * N (D.datum.reflectionPerm i i) - N (D.datum.reflectionPerm i i) * N i =
          c • d (1 ⊗ₜ[ℤ] D.datum.coroot i))

end MatrixRootOperators

/-- An integral cocharacter with the signs prescribed by the input base. -/
def PositiveIntegralCocharacter : Prop :=
  ∀ D : BasedRootDatum.{u}, ∃ (y : D.Y) (m : ℤ), 0 < m ∧
    ∀ i : D.I, D.datum.root' i y = m * D.base.height i

section MatrixGroupConstruction

open StandardGroups (generalLinearPoints additivePoints)
open DiagonalizableGroups (characterValuedPoints)
open AdjointRepresentation (GroupPoints)
open InfinitesimalCommutator (matrixDifferential)

variable {k : Type v} {X J I : Type u} [Field k] [AddCommGroup X] [DecidableEq J]

/-- An integral functional on the character lattice acts diagonally according to the weights. -/
def integralWeightDiagonal (k : Type v) [Field k] (w : J → X) (φ : X →ₗ[ℤ] ℤ) :
    Matrix J J k :=
  Matrix.diagonal fun i => (φ (w i) : k)

/-- Matrices spanned by the lattice diagonal and the specified root operators. -/
def latticeMatrixSpan (w : J → X) (N : I → Matrix J J k) :
    Submodule k (Matrix J J k) :=
  Submodule.span k (Set.range (integralWeightDiagonal k w) ∪ Set.range N)

/-- A closed matrix group generated by the marked torus and root exponentials,
with its tangent image inside the fixed general linear group. -/
structure MatrixGroup (D : BasedRootDatum.{u}) (k : Type u) [Field k]
    [CharZero k] (J : Type u) [Fintype J] [DecidableEq J] (w : J → D.X)
    (N : D.I → Matrix J J k) where
  additive : AdditiveLine k
  additivePointsIso : (groupPointsFunctor k).obj additive.group ≅ additivePoints k
  additiveParameter : ∀ (R : TestAlgebra k) (t : R),
    additivePointsIso.hom.app R (rootPoint (𝟙 additive.group) R t) = Multiplicative.ofAdd t
  ambient : AffineAlgebraicGroup k
  matrixPoints : (groupPointsFunctor k).obj ambient.val ≅ generalLinearPoints k J
  torusPoints : (groupPointsFunctor k).obj (diagonalTorus k D).val ≅
    characterValuedPoints k (Multiplicative D.X)
  group : ClosedSubgroup ambient.val
  smooth : Smooth group.group.X.hom
  connected : GeometricallyConnected group.group.X.hom
  torus : (diagonalTorus k D).val ⟶ group.group
  torusClosed : IsClosedImmersion torus.hom.hom.left
  root : D.I → (additive.group ⟶ group.group)
  rootClosed : ∀ i, IsClosedImmersion (root i).hom.hom.left
  torusCoordinate : ∀ (R : TestAlgebra k) (f : MonoidAlgebra k (Multiplicative D.X) →ₐ[k] R)
    (t : Points (diagonalTorus k D).val.X R),
    t.left = Spec.map (CommRingCat.ofHom f.toRingHom) → ∀ m : Multiplicative D.X,
      ((show Multiplicative D.X →* Rˣ from (torusPoints.hom.app R).hom t) m).val =
        f (MonoidAlgebra.single m 1)
  torusMatrix : ∀ (R : TestAlgebra k) (t : GroupPoints (diagonalTorus k D).val R),
    ((matrixPoints.hom.app R).hom (t ≫ (torus ≫ group.inclusion).hom.hom)).val =
      Matrix.diagonal (fun j =>
        ((show Multiplicative D.X →* Rˣ from (torusPoints.hom.app R).hom t)
          (Multiplicative.ofAdd (w j))).val)
  rootMatrix : ∀ (i : D.I) (R : TestAlgebra k) (t : R),
    ((matrixPoints.hom.app R).hom (rootPoint (root i ≫ group.inclusion) R t)).val =
      exponentialMatrix (N i) R t
  generated : ∀ H : ClosedSubgroup ambient.val,
    (∃ t : (diagonalTorus k D).val ⟶ H.group, t ≫ H.inclusion = torus ≫ group.inclusion) →
    (∀ i, ∃ x : additive.group ⟶ H.group, x ≫ H.inclusion = root i ≫ group.inclusion) →
    ∃ j : group.group ⟶ H.group, j ≫ H.inclusion = group.inclusion
  lie : Set.range (matrixDifferential group.inclusion matrixPoints) =
    (latticeMatrixSpan w N : Set (Matrix J J k))

/-- The same rational root operators and lattice weights give a smooth,
geometrically connected generated matrix group over every characteristic-zero
field, with its exact Lie image. -/
def RationalMatrixGroups : Prop :=
  ∀ D : BasedRootDatum.{u},
    ∃ (J : Type u) (_ : Fintype J) (_ : DecidableEq J) (w : J → D.X)
      (N : D.I → Matrix J J ℚ),
      Submodule.span ℤ (Set.range w) = ⊤ ∧
      (∀ i, N i ≠ 0 ∧ IsNilpotent (N i) ∧
        ∀ a b, N i a b ≠ 0 → w a = w b + D.datum.root i) ∧
      ∀ (k : Type u) [Field k] [CharZero k],
        Nonempty (MatrixGroup D k J w (fun i => (algebraMap ℚ k).mapMatrix (N i)))


open GeometricRadicals (IsReductive IsSplitTorus)
open RankOneFlag (IsGeometricallyMaximal)
open Unipotent (closedSubgroupAlgebraicGroup)
open CharacterPairing (absoluteRoots)
open DiagonalizableGroups (groupAlgebraMap)

/-- The generated matrix models are reductive with a split geometrically maximal
torus, and the absolute roots are the prescribed monomial characters. -/
def RationalReductiveMatrixGroups : Prop :=
  ∀ D : BasedRootDatum.{u},
    ∃ (J : Type u) (_ : Fintype J) (_ : DecidableEq J) (w : J → D.X)
      (N : D.I → Matrix J J ℚ),
      Submodule.span ℤ (Set.range w) = ⊤ ∧
      ∀ (k : Type u) [Field k] [CharZero k],
        ∃ G : MatrixGroup D k J w (fun i => (algebraMap ℚ k).mapMatrix (N i)),
          let T : ClosedSubgroup G.group.group := ⟨(diagonalTorus k D).val, G.torus, G.torusClosed⟩
          IsReductive (closedSubgroupAlgebraicGroup G.group) ∧ IsSplitTorus T.group ∧
          IsGeometricallyMaximal T ∧
          ∃ e : D.I ≃ {χ : Character (diagonalTorus k D).val // χ ∈ absoluteRoots T},
          ∀ i, (e i).val = specGroupMap (groupAlgebraMap k
            ((zpowersHom (Multiplicative D.X) (Multiplicative.ofAdd (D.datum.root i))).comp
              MulEquiv.ulift.toMonoidHom))

end MatrixGroupConstruction

/-- Every finite based reduced datum is realized over the rationals, then over
every characteristic-zero field by extension of that same pinned model. -/
def Statement : Prop :=
  ∀ D : BasedRootDatum.{u},
    ∃ (A : AdditiveLine (RationalField.{u})) (Q : Realization D A),
      (IsEmpty D.I → Nonempty (Q.pinned.pair.G.val ≅ (diagonalTorus RationalField D).val)) ∧
      ∀ (k : Type u) [Field k] [CharZero k],
        letI : Algebra (RationalField.{u}) k :=
          ((algebraMap ℚ k).comp ULift.ringEquiv.toRingHom).toAlgebra
        ∃ (B : AdditiveLine k) (K : Realization D B), Nonempty (ExtendsRational Q K)

end

end LinearAlgebraicGroups.Specs.RationalRealization
