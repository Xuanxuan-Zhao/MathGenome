import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Rat.Floor
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Dimension.Constructions
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AffineArrangementAlcoves
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.EuclideanComparison

/-! Coordinates and affine walls for the exceptional based data. -/

open scoped Matrix TensorProduct BigOperators

namespace LinearAlgebraicGroups.Specs.ExceptionalAffineRootSystems

/-- The depth index, so that depth `n / d` is the first one for which
`a + n / d > 0`. Here `d = 1` for split or long roots, and `d = 2` for
short roots of the ramified datum. -/
def threshold {K : Type*} [Ring K] [LinearOrder K] [FloorRing K] (a : K) : ℤ :=
  ⌊-a⌋ + 1

/-- The separating levels counted with orientation from positive to negative.
The argument is the root value multiplied by its depth denominator. -/
noncomputable def separatingLevels {K : Type*} [Ring K] [LinearOrder K] [FloorRing K]
    (a b : K) : Finset ℤ :=
  Finset.Ico (threshold a) (threshold b)

/-- One direction of the wall count, for a pair of endpoints outside the walls. -/
def ThresholdCount : Prop :=
  ∀ {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]
    (a b : K), a ∉ Set.range (Int.cast : ℤ → K) → b ∉ Set.range (Int.cast : ℤ → K) →
    (∀ n : ℤ, threshold a ≤ n ↔ 0 < a + (n : K)) ∧
    (∀ n : ℤ, n ∈ separatingLevels a b ↔ 0 < a + (n : K) ∧ b + (n : K) < 0) ∧
    (separatingLevels a b).card = (threshold b - threshold a).toNat ∧
    threshold (-b) - threshold (-a) = -(threshold b - threshold a)

/-- Each geometric wall contributes in exactly one of the two root directions.
The integer level in the negative direction is the negative of the original level. -/
def OppositeWallCount : Prop :=
  ∀ {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]
    (a b : K), a ∉ Set.range (Int.cast : ℤ → K) → b ∉ Set.range (Int.cast : ℤ → K) →
    {n : ℤ | (0 < a + n ∧ b + n < 0) ∨ (a + n < 0 ∧ 0 < b + n)} =
      (↑(separatingLevels a b) : Set ℤ) ∪ (Neg.neg '' ↑(separatingLevels (-a) (-b))) ∧
    Disjoint (↑(separatingLevels a b) : Set ℤ) (Neg.neg '' ↑(separatingLevels (-a) (-b))) ∧
    (separatingLevels a b).card + (separatingLevels (-a) (-b)).card =
      (threshold b - threshold a).natAbs

/-- Sum over one representative per pair of opposite roots. The two
arguments are the normalized root values at the endpoints of the gallery. -/
def SeparatingWallSum : Prop :=
  ∀ {ι K : Type} [Fintype ι] [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]
    (x y : ι → K),
    (∀ i, x i ∉ Set.range (Int.cast : ℤ → K)) →
    (∀ i, y i ∉ Set.range (Int.cast : ℤ → K)) →
    (∑ i, (threshold (y i) - threshold (x i)).natAbs) =
      (∑ i, ((threshold (y i) - threshold (x i)).toNat +
        (threshold (-y i) - threshold (-x i)).toNat))

/-- Rescaling the affine root to integral levels preserves its sign at every point. -/
def NormalizeWall.{u} : Prop :=
  ∀ {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (a : K) (d : ℕ) (_hd : 0 < d) (n : ℤ),
    (a + (n : K) / d = 0 ↔ (d : K) * a + n = 0) ∧
    (0 < a + (n : K) / d ↔ 0 < (d : K) * a + n)

/-- The signed walls of an alcove and the reflection and positivity rules
for the action on them. The geometric rule here is that crossing a simple
wall reverses that wall and preserves the other positive half-spaces. -/
structure SignedWallAction {W S A : Type*} [Group W] [MulAction W A] (s : S → W) where
  positive : A → Prop
  opposite : A → A
  reflect : A → W
  simple : S → A
  opposite_positive (a : A) : positive (opposite a) ↔ ¬positive a
  smul_opposite (w : W) (a : A) : w • opposite a = opposite (w • a)
  simple_positive (i : S) : positive (simple i)
  simple_opposite (i : S) : s i • simple i = opposite (simple i)
  simple_preserves (i : S) {a : A} : positive a → a ≠ simple i → positive (s i • a)
  simple_reflect (i : S) : reflect (simple i) = s i
  conjugate_reflect (w : W) (a : A) : reflect (w • a) = w * reflect a * w⁻¹
  reflection_sq (a : A) : reflect a * reflect a = 1

/-- Each separating wall is represented by its positive orientation for the
base alcove. The inverse takes that wall back to the base alcove to test its
sign on the translated alcove. -/
def separatingWalls {W S A : Type*} [Group W] [MulAction W A] {s : S → W}
    (H : SignedWallAction (A := A) s) (w : W) : Set A :=
  {a | H.positive a ∧ ¬ H.positive (w⁻¹ • a)}

/-- Evaluating a word in a family of reflections. -/
def wallWord {W S : Type*} [Group W] (s : S → W) (l : List S) : W := (l.map s).prod

/-- The deletion condition for a generating family of involutions. -/
def WallDeletionCondition {W S : Type*} [Group W] (s : S → W) : Prop :=
  ∀ l : List S, (∃ k : List S, wallWord s k = wallWord s l ∧ k.length < l.length) →
    ∃ (p m q : List S) (i j : S),
      l = p ++ i :: (m ++ j :: q) ∧ wallWord s (p ++ m ++ q) = wallWord s l

/-- The signed geometric action implies deletion and detects the identity
before using a Coxeter presentation. -/
def SignedWallDeletion.{u,v,w} : Prop :=
  ∀ {W : Type u} {S : Type v} {A : Type w} [Group W] [MulAction W A] {s : S → W}
    (H : SignedWallAction (A := A) s),
    WallDeletionCondition s ∧
    (∀ w : W, (∃ l : List S, wallWord s l = w) → separatingWalls H w = ∅ → w = 1)

/-- Once the geometric simple-wall rules have been checked, the word length
counts the separating walls and right multiplication is decided by the
sign of the transported simple wall. -/
def WallSignsAndLength.{u,v,w} : Prop :=
  ∀ {W : Type u} {S : Type v} {A : Type w} [Group W] [MulAction W A] {M : CoxeterMatrix S}
    (cs : CoxeterSystem M W) (H : SignedWallAction (A := A) cs.simple),
    (∀ w, (separatingWalls H w).Finite ∧ (separatingWalls H w).ncard = cs.length w) ∧
    (∀ w i, (H.positive (w • H.simple i) → cs.length (w * cs.simple i) = cs.length w + 1) ∧
      (¬H.positive (w • H.simple i) → cs.length (w * cs.simple i) + 1 = cs.length w))

section AffineGroups

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The normalized roots on a cocharacter apartment and their matched
coroots. In the ramified case the short root is doubled and its coroot
is halved. -/
abbrev ApartmentRoots (K V ι : Type*) [Field K] [AddCommGroup V] [Module K V] :=
  Arithmetic.AffineArrangement.Datum K V ι

namespace ApartmentRoots

variable (D : ApartmentRoots K V ι)

/-- The split apartment of an integral datum after extension to K. -/
def split {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum (ι := ι) X Y) (K : Type*) [Field K] :
    ApartmentRoots K (K ⊗[ℤ] Y) ι where
  root i := RootData.extendFunctional K (P.root' i)
  coroot i := 1 ⊗ₜ[ℤ] P.coroot i
  diagonal i := by simp
  integral i j := ⟨P.pairing i j, by simp⟩

/-- Transport the matched functionals and vectors to the actual cocharacter space. -/
def transport {V' : Type*} [AddCommGroup V'] [Module K V'] (f : V ≃ₗ[K] V') : ApartmentRoots K V' ι where
  root i := (D.root i).comp f.symm.toLinearMap
  coroot i := f (D.coroot i)
  diagonal i := by simpa using D.diagonal i
  integral i j := by simpa using D.integral i j

/-- The linear part of the reflection in a wall of direction `i`. -/
abbrev linearReflection (i : ι) : V ≃ₗ[K] V := Arithmetic.AffineArrangement.Datum.linearReflection D i

/-- The simultaneous stability of the normalized roots and matched coroots
under the linear root reflections. -/
abbrev ReflectionClosed : Prop := Arithmetic.AffineArrangement.Datum.ReflectionClosed D

/-- The distinct signed root functions have no proportional pairs except
opposites. The diagonal pairing already ensures the functions are nonzero. -/
abbrev ReducedDirections : Prop := Arithmetic.AffineArrangement.Datum.ReducedDirections D

/-- Reflection in the wall `root i (x) + n = 0`. -/
abbrev wallReflection (i : ι) (n : ℤ) : V ≃ᵃ[K] V := D.reflection (i, n)

/-- The linear Weyl action generated by the root reflections. -/
def linearWeylGroup : Subgroup (V ≃ₗ[K] V) :=
  Subgroup.closure (Set.range D.linearReflection)

/-- The ordinary affine reflection subgroup. -/
abbrev affineWeylGroup : Subgroup (V ≃ᵃ[K] V) := D.ordinary

/-- The coroot lattice in the cocharacter apartment. -/
def corootLattice : AddSubgroup V :=
  AddSubgroup.closure (Set.range D.coroot)

/-- The coweight lattice consists of the cocharacters integral on all roots. -/
def coweightLattice : AddSubgroup V where
  carrier := {x | ∀ i, ∃ n : ℤ, D.root i x = (n : K)}
  zero_mem' := fun i => ⟨0, by simp⟩
  add_mem' := by
    intro x y hx hy i
    obtain ⟨m, hm⟩ := hx i
    obtain ⟨n, hn⟩ := hy i
    exact ⟨m + n, by simp [hm, hn]⟩
  neg_mem' := by
    intro x hx i
    obtain ⟨m, hm⟩ := hx i
    exact ⟨-m, by simp [hm]⟩

/-- The extended affine group generated by the linear Weyl group and by
translations by all coweights. -/
abbrev extendedAffineWeylGroup : Subgroup (V ≃ᵃ[K] V) := D.extended

/-- A point is regular for the arrangement when it lies on no integral wall. -/
def IsRegular (x : V) : Prop :=
  ∀ i, D.root i x ∉ Set.range (Int.cast : ℤ → K)

/-- The equation of a signed affine root at a point. -/
abbrev wallValue (a : ι × ℤ) (x : V) : K := D.value a x

/-- The affine roots pointing from the destination back to the starting
alcove. For a reduced arrangement, this orients each separating wall once. -/
abbrev orientedSeparators [LinearOrder K] (x y : V) : Set (ι × ℤ) := D.separators x y

end ApartmentRoots

/-- The equation and the two normal forms for the ordinary and extended
affine groups. Evaluating at zero reads off their translation lattices. -/
def AffineGroupNormalForms.{u,v,w} : Prop :=
  ∀ {K : Type u} {V : Type v} {ι : Type w} [Field K] [AddCommGroup V] [Module K V] (D : ApartmentRoots K V ι),
    (∀ i n x, D.wallReflection i n x = x - (D.root i x + (n : K)) • D.coroot i) ∧
    (∀ g : V ≃ᵃ[K] V, g ∈ D.affineWeylGroup ↔
      g 0 ∈ D.corootLattice ∧ g.linear ∈ D.linearWeylGroup) ∧
    (∀ g : V ≃ᵃ[K] V, g ∈ D.extendedAffineWeylGroup ↔
      g 0 ∈ D.coweightLattice ∧ g.linear ∈ D.linearWeylGroup)

/-- The extended group maps onto `P∨/Q∨` by the class of its
translation part, with kernel the ordinary affine Weyl group. -/
def ExtendedTranslationQuotient.{u,v,w} : Prop :=
  ∀ {K : Type u} {V : Type v} {ι : Type w} [Field K] [AddCommGroup V] [Module K V] (D : ApartmentRoots K V ι),
    let Q := D.corootLattice.comap D.coweightLattice.subtype
    ∃ f : D.extendedAffineWeylGroup →* Multiplicative (D.coweightLattice ⧸ Q),
      Function.Surjective f ∧
      (∀ g (t : D.coweightLattice), g.val 0 = t.val →
        f g = Multiplicative.ofAdd (QuotientAddGroup.mk' Q t)) ∧
      (∀ g, f g = 1 ↔ g.val ∈ D.affineWeylGroup)

/-- Setwise stabilizer of the base alcove in the extended affine group. -/
def alcoveStabilizer (D : ApartmentRoots K V ι) (C : Set V) :
    Subgroup D.extendedAffineWeylGroup where
  carrier := {g | g.val '' C = C}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change g.val '' C = C at hg
    change h.val '' C = C at hh
    change ((g.val * h.val) : V ≃ᵃ[K] V) '' C = C
    rw [AffineEquiv.coe_mul, Set.image_comp, hh, hg]
  inv_mem' := by
    intro g hg
    change g.val '' C = C at hg
    change (g.val⁻¹ : V ≃ᵃ[K] V) '' C = C
    nth_rw 1 [← hg]
    rw [Set.image_image]
    simp [AffineEquiv.inv_def]

/-- If the ordinary affine Weyl group transports the base alcove simply
transitively, its extended stabilizer is the translation quotient. -/
def AlcoveStabilizerQuotient.{u,v,w} : Prop :=
  ∀ {K : Type u} {V : Type v} {ι : Type w} [Field K] [AddCommGroup V] [Module K V]
    (D : ApartmentRoots K V ι) (C : Set V),
    (∀ g : D.extendedAffineWeylGroup,
      ∃! w : D.affineWeylGroup, w.val '' C = g.val '' C) →
    let Q := D.corootLattice.comap D.coweightLattice.subtype
    Nonempty (alcoveStabilizer D C ≃* Multiplicative (D.coweightLattice ⧸ Q))

end AffineGroups

/-- Counting the signed levels in all root directions of an apartment. -/
def AffineThresholdCount.{u,v,w} : Prop :=
  ∀ {K : Type u} {V : Type v} {ι : Type w} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [FloorRing K] [AddCommGroup V] [Module K V] [Fintype ι] (D : ApartmentRoots K V ι)
    (x y : V), D.IsRegular x → D.IsRegular y → (D.orientedSeparators x y).Finite ∧
      (D.orientedSeparators x y).ncard = ∑ i, (threshold (D.root i y) - threshold (D.root i x)).toNat

section AlcoveGeometry

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [LinearOrder K] [IsStrictOrderedRing K] (D : ApartmentRoots K V ι) (p : V)

namespace ApartmentRoots

/-- The signed simple roots are the positive equations of the bounding walls. -/
abbrev SimpleWall := {a : ι × ℤ // D.IsSimple p a}

/-- The actual affine reflection in a bounding wall of the base alcove. -/
def simpleAffineReflection (i : SimpleWall D p) : D.affineWeylGroup :=
  ⟨D.reflection i.val, Subgroup.subset_closure ⟨i.val, rfl⟩⟩

/-- The underlying hyperplane of a signed equation. -/
def wallHyperplane (a : ι × ℤ) : Set V := {x | D.wallValue a x = 0}

/-- The hyperplanes for which the two points lie in opposite open half-apartments. -/
def separatingHyperplanes (x y : V) : Set (Set V) :=
  wallHyperplane D '' {a | (0 < D.wallValue a x ∧ D.wallValue a y < 0) ∨
    (D.wallValue a x < 0 ∧ 0 < D.wallValue a y)}

end ApartmentRoots

/-- The Coxeter system of the actual wall reflections, with the signed equation
action and the length formulas for its base alcove. -/
structure AlcoveCoxeterData [FloorRing K] where
  matrix : CoxeterMatrix (D.SimpleWall p)
  coxeter : CoxeterSystem matrix D.affineWeylGroup
  simple_eq : coxeter.simple = D.simpleAffineReflection p
  matrix_eq (i j : D.SimpleWall p) : matrix i j = orderOf (coxeter.simple i * coxeter.simple j)
  action : MulAction D.affineWeylGroup (ι × ℤ)
  walls : letI := action; SignedWallAction (A := ι × ℤ) coxeter.simple
  positive_eq : walls.positive = D.positive p
  opposite_eq : walls.opposite = D.opposite
  reflection_eq (a : ι × ℤ) : (walls.reflect a).val = D.reflection a
  simple_wall (i : D.SimpleWall p) : walls.simple i = i.val
  equation (w : D.affineWeylGroup) (a : ι × ℤ) (x : V) :
    letI := action
    D.wallValue (w • a) x = D.wallValue a (w.val.symm x)
  right_ascent (w : D.affineWeylGroup) (i : D.SimpleWall p) :
    letI := action
    coxeter.length (w * coxeter.simple i) = coxeter.length w + 1 ↔ D.positive p (w • i.val)
  right_descent (w : D.affineWeylGroup) (i : D.SimpleWall p) :
    letI := action
    coxeter.IsRightDescent w i ↔ D.wallValue (w • i.val) p < 0
  length_walls (w : D.affineWeylGroup) :
    (D.separatingHyperplanes p (w.val p)).Finite ∧
      coxeter.length w = (D.separatingHyperplanes p (w.val p)).ncard
  length_thresholds (w : D.affineWeylGroup) :
    coxeter.length w = ∑ᶠ i, (threshold (D.root i (w.val p)) - threshold (D.root i p)).toNat

/-- Simple transitivity of the ordinary action and the full extended alcove stabilizer. -/
structure AlcoveGeometry [FloorRing K] : Prop where
  regular : D.IsRegular p
  ordinary_symmetries : D.affineWeylGroup ≤ D.symmetries
  extended_symmetries : D.extendedAffineWeylGroup ≤ D.symmetries
  coxeter : Nonempty (AlcoveCoxeterData D p)
  simply_transitive (q : V) (hq : D.IsRegular q) :
    ∃! w : D.affineWeylGroup, w.val '' D.alcove p = D.alcove q
  extended_action (g : D.extendedAffineWeylGroup) :
    D.IsRegular (g.val p) ∧ g.val '' D.alcove p = D.alcove (g.val p)
  stabilizer : Nonempty (alcoveStabilizer D (D.alcove p) ≃*
    Multiplicative (D.coweightLattice ⧸ D.corootLattice.comap D.coweightLattice.subtype))

end AlcoveGeometry

/-- Geometry of the normalized integral-level arrangement over the rational
and real apartments. The hypotheses are finite root and coroot conditions. -/
def AffineApartmentGeometry.{u,v,w} : Prop :=
  ∀ {K : Type u} {V : Type v} {ι : Type w} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Archimedean K] [FloorRing K] [AddCommGroup V] [Module K V] [Finite ι]
    (D : ApartmentRoots K V ι), D.ReflectionClosed → D.ReducedDirections →
    ∀ p, D.IsRegular p → AlcoveGeometry D p

/-- In real linear coordinates the sign alcoves are exactly the connected
components of the complement of the transported walls. -/
def RealAlcovesInCoordinates.{v,w} : Prop :=
  ∀ {V : Type v} {ι : Type w} [AddCommGroup V] [Module ℝ V] (D : ApartmentRoots ℝ V ι),
    D.ReflectionClosed → D.ReducedDirections →
    ∀ {n : ℕ} (f : V ≃ₗ[ℝ] (Fin n → ℝ)) (p : V), D.IsRegular p →
    f '' D.alcove p = connectedComponentIn {x | (D.transport f).IsRegular x} (f p)

/-- The signed affine roots and the depth indices of the pinned alcove. -/
structure PinnedWallSigns {K V ι : Type*} [Field K] [LinearOrder K] [FloorRing K]
    [AddCommGroup V] [Module K V] (D : ApartmentRoots K V ι) (p : V) (positive : ι → Prop) : Prop where
  positive_iff (i : ι) (n : ℤ) : D.positive p (i, n) ↔ 0 < n ∨ (n = 0 ∧ positive i)
  threshold_positive (i : ι) : positive i → threshold (D.root i p) = 0
  threshold_negative (i : ι) : ¬positive i → threshold (D.root i p) = 1
  simple_index (a : ι × ℤ) : D.IsSimple p a → a.2 = threshold (D.root a.1 p)

/-- The scalar-extended split roots and coroots are stable under the paired
reflections of the integral datum. -/
def SplitReflectionClosed.{u,v,w,z} : Prop :=
  ∀ {ι : Type u} {X : Type v} {Y : Type w} {K : Type z}
    [AddCommGroup X] [AddCommGroup Y] [Field K] (P : RootDatum (ι := ι) X Y),
    let D := ApartmentRoots.split P K
    ∀ i j, D.root (P.reflectionPerm i j) = (D.root j).comp (D.linearReflection i).toLinearMap ∧
      D.coroot (P.reflectionPerm i j) = D.linearReflection i (D.coroot j)

/-- Extending the scalar field preserves reducedness for the actual split
root functions on cocharacters. -/
def SplitReducedDirections.{u,v,w,z} : Prop :=
  ∀ {ι : Type u} {X : Type v} {Y : Type w} {K : Type z}
    [AddCommGroup X] [AddCommGroup Y] [Field K] [CharZero K]
    (P : RootDatum (ι := ι) X Y) [P.IsReduced], (ApartmentRoots.split P K).ReducedDirections

/-- In simple-root coordinates the (i)-th reflection subtracts the Cartan
pairing from the (i)-th coefficient. -/
def simpleReflection {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (i : Fin n)
    (r : Fin n → ℤ) : Fin n → ℤ :=
  r - (C.mulVec r i) • Pi.single i 1

/-- The roots generated by the specified simple reflections. -/
inductive IsRootCoordinate {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) : (Fin n → ℤ) → Prop
  | simple (i : Fin n) : IsRootCoordinate C (Pi.single i 1)
  | reflect {r : Fin n → ℤ} (h : IsRootCoordinate C r) (i : Fin n) :
      IsRootCoordinate C (simpleReflection C i r)

/-- A Cartan matrix with its base gives these coordinates on the actual roots of
any finite based integral root datum, regardless of the isogeny type. -/
def SimpleRootCoordinates.{u,v,w} : Prop :=
  ∀ {ι : Type u} {X : Type v} {Y : Type w} [Finite ι] [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum (ι := ι) X Y) [P.IsReduced] (B : P.Base) {n : ℕ}
    (e : Fin n ≃ B.support) (C : Matrix (Fin n) (Fin n) ℤ),
    (∀ i j, C i j = P.pairing (e j) (e i)) →
    ∀ r : Fin n → ℤ,
      IsRootCoordinate C r ↔ (∑ i, r i • P.root (e i)) ∈ Set.range P.root

/-- Simple-root values on the scalar-extended cocharacter lattice. -/
def simpleRootValues {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum (ι := ι) X Y) (B : P.Base) {n : ℕ}
    (e : Fin n ≃ B.support) (K : Type*) [Field K] : (K ⊗[ℤ] Y) →ₗ[K] (Fin n → K) :=
  LinearMap.pi fun i => RootData.extendFunctional K (P.root' (e i))

/-- In simple-root values, the coweight lattice is the preimage of the
integer vectors and the coroot lattice is generated by the columns of the
Cartan matrix in the convention row root, column coroot. -/
def CocharacterLatticeCoordinates.{u,v,w,z} : Prop :=
  ∀ {ι : Type u} {X : Type v} {Y : Type w} {K : Type z}
    [Finite ι] [AddCommGroup X] [AddCommGroup Y] [Field K]
    (P : RootDatum (ι := ι) X Y) [P.IsReduced] (B : P.Base)
    {n : ℕ} (e : Fin n ≃ B.support) (C : Matrix (Fin n) (Fin n) ℤ),
    (∀ i j, C i j = P.pairing (e i) (e j)) →
    let D := ApartmentRoots.split P K
    let φ := simpleRootValues P B e K
    (∀ x, x ∈ D.coweightLattice ↔ ∃ t : Fin n → ℤ, φ x = fun i => (t i : K)) ∧
    (∀ x, x ∈ D.corootLattice ↔
      ∃ t : Fin n → ℤ, x = ∑ j, t j • ((1 : K) ⊗ₜ[ℤ] P.coroot (e j))) ∧
    φ '' (D.corootLattice : Set (K ⊗[ℤ] Y)) =
      Set.range (fun t : Fin n → ℤ => fun i => (C.mulVec t i : K))

/-- The same simple-root coefficients give the attached coroot coefficients in
a simply laced datum. The isomorphism retains the actual two root embeddings. -/
def PairedRootCoordinates.{u,v,w} : Prop :=
  ∀ {ι : Type u} {X : Type v} {Y : Type w} [Finite ι] [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum (ι := ι) X Y) [P.IsReduced] (B : P.Base) {n : ℕ}
    (e : Fin n ≃ B.support) (C : Matrix (Fin n) (Fin n) ℤ),
    C.IsSymm → (∀ i j, C i j = P.pairing (e i) (e j)) →
    ∃ ρ : ι ≃ {r // IsRootCoordinate C r}, ∀ i,
      P.root i = ∑ j, (ρ i).val j • P.root (e j) ∧
      P.coroot i = ∑ j, (ρ i).val j • P.coroot (e j)

/-- In the semisimple ranks the simple-root values are coordinates on the
entire scalar-extended cocharacter apartment. -/
def CocharacterApartmentCoordinates.{u,v,w,z} : Prop :=
  ∀ {ι : Type u} {X : Type v} {Y : Type w} {K : Type z}
    [Finite ι] [AddCommGroup X] [AddCommGroup Y] [Field K] [CharZero K]
    [Module.Free ℤ X] [Module.Finite ℤ X] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (P : RootDatum (ι := ι) X Y) [P.IsReduced] (B : P.Base) {n : ℕ}
    (e : Fin n ≃ B.support), Module.finrank ℤ Y = n →
    ∃ φ : (K ⊗[ℤ] Y) ≃ₗ[K] (Fin n → K), φ.toLinearMap = simpleRootValues P B e K

/-- A point in the pinned alcove can be chosen with equal positive simple
values and with room to double the short restricted roots. -/
def PinnedAlcovePoint.{u,v,w,z} : Prop :=
  ∀ {ι : Type u} {X : Type v} {Y : Type w} {K : Type z}
    [Finite ι] [AddCommGroup X] [AddCommGroup Y] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [Module.Free ℤ X] [Module.Finite ℤ X] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (P : RootDatum (ι := ι) X Y) [P.IsReduced] (B : P.Base) {n : ℕ}
    (e : Fin n ≃ B.support), Module.finrank ℤ Y = n →
    let D := ApartmentRoots.split P K
    ∃ (x : K ⊗[ℤ] Y) (c : K), 0 < c ∧ (∀ j, simpleRootValues P B e K x j = c) ∧
      (∀ i, (0 < D.root i x ↔ B.IsPos i) ∧ 0 < |D.root i x| ∧ |D.root i x| < 1 / 2)

/-- The Coxeter and alcove geometry for the integral-level split arrangement
on all cocharacters, with the positivity fixed by the chosen base. -/
def SplitPinnedAlcoveGeometry.{u,v,w,z} : Prop :=
  ∀ {ι : Type u} {X : Type v} {Y : Type w} {K : Type z}
    [Finite ι] [AddCommGroup X] [AddCommGroup Y] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Archimedean K] [FloorRing K]
    [Module.Free ℤ X] [Module.Finite ℤ X] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (P : RootDatum (ι := ι) X Y) [P.IsReduced] (B : P.Base) {n : ℕ}
    (e : Fin n ≃ B.support), Module.finrank ℤ Y = n →
    let D := ApartmentRoots.split P K
    ∃ (p : K ⊗[ℤ] Y) (c : K), 0 < c ∧ (∀ j, simpleRootValues P B e K p j = c) ∧
      PinnedWallSigns D p B.IsPos ∧ AlcoveGeometry D p

/-- The value of a root with known simple-root coefficients on the full
cocharacter apartment. -/
def RootValuesFromCoordinates.{u,v,w,z} : Prop :=
  ∀ {ι : Type u} {X : Type v} {Y : Type w} {K : Type z}
    [AddCommGroup X] [AddCommGroup Y] [Field K]
    (P : RootDatum (ι := ι) X Y) (B : P.Base) {n : ℕ} (e : Fin n ≃ B.support)
    (i : ι) (r : Fin n → ℤ), P.root i = ∑ j, r j • P.root (e j) →
    ∀ x, (ApartmentRoots.split P K).root i x =
      ∑ j, (r j : K) * simpleRootValues P B e K x j

/-- The ordinary translation lattice is the image of the integral coroot
lattice. For an adjoint datum the image of the whole cocharacter lattice is
the extended translation lattice. -/
def SplitIntegralCocharacterImages.{u,v,w,z} : Prop :=
  ∀ {ι : Type u} {X : Type v} {Y : Type w} {K : Type z}
    [Finite ι] [AddCommGroup X] [AddCommGroup Y] [Field K] [CharZero K]
    [Module.Free ℤ X] [Module.Finite ℤ X] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (P : RootDatum (ι := ι) X Y) [P.IsReduced] (_B : P.Base),
    let D := ApartmentRoots.split P K
    let lift (y : Y) := (1 : K) ⊗ₜ[ℤ] y
    (D.corootLattice : Set (K ⊗[ℤ] Y)) =
      lift '' (Submodule.span ℤ (Set.range P.coroot) : Set Y) ∧
    (Submodule.span ℤ (Set.range P.root) = ⊤ →
      (D.coweightLattice : Set (K ⊗[ℤ] Y)) = Set.range lift)

/-- Specialization to the cocharacters of the actual torus in a split Borel.
The full integral cocharacter image gives the translations in the simply
connected and adjoint cases, in their respective affine groups. -/
def SplitBorelApartmentGeometry.{u,v} : Prop :=
  ∀ {F : Type u} [Field F] {K : Type v} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [Archimedean K] [FloorRing K] (P : Pinning.SplitBorelPair F) (A : Pinning.AttachedDatum P),
    GeometricRadicals.IsSemisimple P.G →
    letI := A.comm
    let D := ApartmentRoots.split A.datum.rootDatum K
    let lift (y : Additive (CharacterDescent.Cocharacter P.T.group)) := (1 : K) ⊗ₜ[ℤ] y
    (∀ i, A.base.IsPos i ↔ i ∈ BorelsAndChambers.subgroupRoots P.T P.B) ∧
    (∀ {n : ℕ} (e : Fin n ≃ A.base.support),
      ∃ p c, 0 < c ∧ (∀ i, simpleRootValues A.datum.rootDatum A.base e K p i = c) ∧
        PinnedWallSigns D p A.base.IsPos ∧ AlcoveGeometry D p) ∧
    (SimplyConnectedLattice.GeometricallySimplyConnected P.G →
      (D.corootLattice : Set _) = Set.range lift) ∧
    (SchemeCentre.rootLattice P.T = ⊤ → (D.coweightLattice : Set _) = Set.range lift)

/-- E₆ in the numbering with chain 1–3–4–5–6 and vertex 2 attached to 4.
Columns of this matrix are simple coroots in fundamental coweight coordinates. -/
def e6Cartan : Matrix (Fin 6) (Fin 6) ℤ :=
  !![2, 0, -1, 0, 0, 0;
     0, 2, 0, -1, 0, 0;
     -1, 0, 2, -1, 0, 0;
     0, -1, -1, 2, -1, 0;
     0, 0, 0, -1, 2, -1;
     0, 0, 0, 0, -1, 2]

/-- The pinned diagram action on fundamental coweight coordinates. -/
def e6Diagram : Matrix (Fin 6) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 1, 0, 0, 0;
     1, 0, 0, 0, 0, 0]

/-- The partner of a based root under the pinned E₆ involution. -/
def e6Partner : Fin 6 → Fin 6 := ![5, 1, 4, 3, 2, 0]

/-- The action on cocharacters is covariant. The `RootPairing.Equiv` field
`coweightEquiv` encodes its inverse, which is transpose to the root action. -/
noncomputable def diagramCocharacters {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]
    {P : RootDatum (ι := ι) X Y} (σ : P.Equiv P) : (K ⊗[ℤ] Y) ≃ₗ[K] (K ⊗[ℤ] Y) :=
  σ.coweightEquiv.symm.baseChange ℤ K Y Y

/-- Projection by averaging the identity and a diagram involution. -/
def diagramAverage {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (σ : V ≃ₗ[K] V) : V →ₗ[K] V :=
  (2 : K)⁻¹ • (LinearMap.id + σ.toLinearMap)

/-- The subspace of cocharacters fixed by the diagram action. -/
def diagramFixedSpace {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (σ : V ≃ₗ[K] V) : Submodule K V :=
  (σ.toLinearMap - LinearMap.id).ker

/-- The simple-root values and the actual root coefficients transform by
the two transpositions of the pinned diagram. -/
def E6DiagramCoordinates.{u,v,w,z} : Prop :=
  ∀ {ι : Type u} {X : Type v} {Y : Type w} {K : Type z}
    [Finite ι] [AddCommGroup X] [AddCommGroup Y] [Field K]
    (P : RootDatum (ι := ι) X Y) [P.IsReduced] (B : P.Base)
    (e : Fin 6 ≃ B.support) (σ : P.Equiv P),
    (∀ i, σ.indexEquiv (e i) = (e (e6Partner i) : ι)) →
    (∀ i j, e6Cartan i j = P.pairing (e i) (e j)) →
    let φ := simpleRootValues P B e K
    (∀ x i, φ (diagramCocharacters σ x) i = φ x (e6Partner i)) ∧
    ∃ ρ : ι ≃ {r // IsRootCoordinate e6Cartan r},
      (∀ i, P.root i = ∑ j, (ρ i).val j • P.root (e j) ∧
        P.coroot i = ∑ j, (ρ i).val j • P.coroot (e j) ∧
        (ρ (σ.indexEquiv i)).val = e6Diagram.mulVec (ρ i).val) ∧
      (∀ i j, (ρ (P.reflectionPerm (e j) i)).val = simpleReflection e6Cartan j (ρ i).val)

/-- Projection of an integral coweight in the invariant rational apartment. -/
def e6Projection (x : Fin 6 → ℤ) (i : Fin 6) : ℚ :=
  ((1 + e6Diagram).mulVec x i : ℚ) / 2

/-- The projected coroot lattice coincides with the projected coweight lattice. -/
def E6ProjectedLattices : Prop :=
  Set.range (fun x => e6Projection (e6Cartan.mulVec x)) = Set.range e6Projection

/-- The coweight class modulo the coroot lattice in type E₆. -/
def e6CoweightClass (x : Fin 6 → ℤ) : ZMod 3 :=
  ((x 0 - x 2 + x 4 - x 5 : ℤ) : ZMod 3)

/-- The coweight class realizes the cyclic quotient of order three, with
the diagram involution inducing inversion on it. -/
def E6CoweightClass : Prop :=
  Function.Surjective e6CoweightClass ∧
    (∀ x, x ∈ Set.range e6Cartan.mulVec ↔ e6CoweightClass x = 0) ∧
    (∀ x, e6CoweightClass (e6Diagram.mulVec x) = -e6CoweightClass x)

/-- The E₇ and E₈ diagrams extend the right arm of the E₆ diagram. -/
def exceptionalCartan (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j =>
  if i = j then 2
  else if ({i.val, j.val} : Finset ℕ) ∈
    ({ {0, 2}, {1, 3}, {2, 3}, {3, 4}, {4, 5}, {5, 6}, {6, 7} } : Finset (Finset ℕ))
  then -1 else 0

/-- On each split exceptional diagram, the coordinate roots give both
absolute embeddings and the integral-level pinned alcove on cocharacters. -/
def ExceptionalSplitGeometry.{u,v,w,z} : Prop :=
  ∀ {ι : Type u} {X : Type v} {Y : Type w} {K : Type z}
    [Finite ι] [AddCommGroup X] [AddCommGroup Y] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Archimedean K] [FloorRing K]
    [Module.Free ℤ X] [Module.Finite ℤ X] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (P : RootDatum (ι := ι) X Y) [P.IsReduced] (B : P.Base) {n : ℕ}
    (e : Fin n ≃ B.support), (n = 6 ∨ n = 7 ∨ n = 8) → Module.finrank ℤ Y = n →
    (∀ i j, exceptionalCartan n i j = P.pairing (e i) (e j)) →
    let D := ApartmentRoots.split P K
    (∃ ρ : ι ≃ {r // IsRootCoordinate (exceptionalCartan n) r}, ∀ i,
      P.root i = ∑ j, (ρ i).val j • P.root (e j) ∧
      P.coroot i = ∑ j, (ρ i).val j • P.coroot (e j)) ∧
    (∃ p c, 0 < c ∧ (∀ j, simpleRootValues P B e K p j = c) ∧
      PinnedWallSigns D p B.IsPos ∧ AlcoveGeometry D p)

/-- The order of folded simple roots is 2, 4, {3,5}, {1,6}. -/
def orbitFirst : Fin 4 → Fin 6 := ![1, 3, 2, 0]

/-- The second member is equal to the first on the singleton orbits. -/
def orbitSecond : Fin 4 → Fin 6 := ![1, 3, 4, 5]

/-- A reflection in a singleton or the two commuting reflections in a pair. -/
def orbitReflection (j : Fin 4) (r : Fin 6 → ℤ) : Fin 6 → ℤ :=
  if orbitFirst j = orbitSecond j then simpleReflection e6Cartan (orbitFirst j) r
  else simpleReflection e6Cartan (orbitFirst j) (simpleReflection e6Cartan (orbitSecond j) r)

/-- Evaluation of a word in the simple orbit reflections. -/
def orbitWord (word : List (Fin 4)) (r : Fin 6 → ℤ) : Fin 6 → ℤ :=
  word.foldr orbitReflection r

/-- The corresponding products of simple reflections on the actual absolute roots. -/
def basedOrbitReflection {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum (ι := ι) X Y) (B : P.Base) (e : Fin 6 ≃ B.support) (j : Fin 4) (i : ι) : ι :=
  if orbitFirst j = orbitSecond j then P.reflectionPerm (e (orbitFirst j)) i
  else P.reflectionPerm (e (orbitFirst j)) (P.reflectionPerm (e (orbitSecond j)) i)

/-- An orbit word in the actual based Weyl action relates every absolute root
to a simple root with the same diagram orbit size. -/
def E6BasedOrbitTransport.{u,v,w} : Prop :=
  ∀ {ι : Type u} {X : Type v} {Y : Type w} [Finite ι] [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum (ι := ι) X Y) [P.IsReduced] (B : P.Base) (e : Fin 6 ≃ B.support) (σ : P.Equiv P),
    (∀ i, σ.indexEquiv (e i) = (e (e6Partner i) : ι)) →
    (∀ i j, e6Cartan i j = P.pairing (e i) (e j)) →
    (∀ j, orbitFirst j ≠ orbitSecond j → P.pairing (e (orbitFirst j)) (e (orbitSecond j)) = 0) ∧
    (∀ i, ∃ (j : Fin 4) (word : List (Fin 4)),
      (i = word.foldr (basedOrbitReflection P B e) (e (orbitFirst j) : ι) ∨
       i = word.foldr (basedOrbitReflection P B e) (e (orbitSecond j) : ι)) ∧
      (σ.indexEquiv i = i ↔ orbitFirst j = orbitSecond j))

/-- Restriction to invariant cocharacters in the four simple-root coordinates.
The orbit coefficients add because invariant cocharacters give the same value
on the two absolute simple roots in a pair. -/
def restrictedRoot (r : Fin 6 → ℤ) : Fin 4 → ℤ :=
  ![r 1, r 3, r 2 + r 4, r 0 + r 5]

/-- Twice the simple roots of the standard (F_4) in orthonormal coordinates.
The first two are long. -/
def f4SimpleDoubled : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 2, -2, 0;
     0, 0, 2, -2;
     0, 0, 0, 2;
     1, -1, -1, -1]

/-- Twice the restricted root in these orthonormal coordinates. -/
def foldedRoot (r : Fin 6 → ℤ) : Fin 4 → ℤ :=
  Matrix.vecMul (restrictedRoot r) f4SimpleDoubled

/-- The two signs used in the coordinate description of (F_4). -/
def unitSign (b : Bool) : ℤ := if b then 1 else -1

/-- The long roots of the standard (F_4), doubled. -/
def IsLongF4Doubled (z : Fin 4 → ℤ) : Prop :=
  ∃ (i j : Fin 4) (s t : Bool), i ≠ j ∧
    z = Pi.single i (2 * unitSign s) + Pi.single j (2 * unitSign t)

/-- The short roots of the standard (F_4), doubled. -/
def IsShortF4Doubled (z : Fin 4 → ℤ) : Prop :=
  (∃ (i : Fin 4) (s : Bool), z = Pi.single i (2 * unitSign s)) ∨
    (∀ i, z i = 1 ∨ z i = -1)

instance (z : Fin 4 → ℤ) : Decidable (IsLongF4Doubled z) := by
  unfold IsLongF4Doubled
  infer_instance

instance (z : Fin 4 → ℤ) : Decidable (IsShortF4Doubled z) := by
  unfold IsShortF4Doubled
  infer_instance

/-- The signed direction in the folded finite root system. A pair of
absolute roots with the same restriction indexes just one direction. -/
abbrev FoldedRootDirection := {z // IsLongF4Doubled z ∨ IsShortF4Doubled z}

/-- Integral long-root levels and half-integral short-root levels. -/
def foldedDepthDenominator (i : FoldedRootDirection) : ℕ :=
  if IsLongF4Doubled i.val then 1 else 2

/-- Twice the normalized root vector, with the short root doubled. -/
def normalizedFoldedNumerator (z : Fin 4 → ℤ) : Fin 4 → ℤ :=
  if IsLongF4Doubled z then z else 2 • z

/-- The normalized affine root uses this functional and an integer level. -/
def normalizedFoldedRoot (K : Type*) [Field K] (i : FoldedRootDirection) :
    (Fin 4 → K) →ₗ[K] K :=
  ∑ j, ((normalizedFoldedNumerator i.val j : K) / 2) • LinearMap.proj j

/-- The normalized coroot in the Euclidean coordinates of the fold. -/
def normalizedFoldedCoroot (K : Type*) [Field K] (i : FoldedRootDirection) : Fin 4 → K :=
  fun j => (i.val j : K) / 2

/-- The normalized folded apartment is an integral matched system of roots
and coroots. Both are carried to the same index by each root reflection. -/
def FoldedApartmentRootSystem.{u} : Prop :=
  ∀ {K : Type u} [Field K] [CharZero K],
    ∃ D : ApartmentRoots K (Fin 4 → K) FoldedRootDirection,
      D.root = normalizedFoldedRoot K ∧ D.coroot = normalizedFoldedCoroot K ∧
      D.ReflectionClosed

/-- Doubling the short roots preserves reducedness of the folded wall
directions, with no repetition of normalized functionals. -/
def FoldedReducedDirections.{u} : Prop :=
  ∀ {K : Type u} [Field K] [CharZero K]
    (D : ApartmentRoots K (Fin 4 → K) FoldedRootDirection),
    D.root = normalizedFoldedRoot K → D.ReducedDirections

/-- The folded, normalized system has trivial translation quotient. -/
def FoldedTranslationLattice.{u} : Prop :=
  ∀ {K : Type u} [Field K] [CharZero K]
    (D : ApartmentRoots K (Fin 4 → K) FoldedRootDirection),
    D.root = normalizedFoldedRoot K → D.coroot = normalizedFoldedCoroot K →
    D.corootLattice = D.coweightLattice

/-- Proportional roots in the standard folded system differ only by sign,
including after scalar extension to the real apartment. -/
def F4Reduced.{u} : Prop :=
  ∀ {K : Type u} [Field K] [CharZero K] (z w : Fin 4 → ℤ),
    (IsLongF4Doubled z ∨ IsShortF4Doubled z) →
    (IsLongF4Doubled w ∨ IsShortF4Doubled w) →
    (∃ a : K, ∀ i, (w i : K) = a * (z i : K)) →
    w = z ∨ w = -z

/-- Exact folding: the fibres in (F_4) are the singleton and orthogonal
two-element diagram orbits, and the simple orbit reflections transport the
absolute roots to their corresponding simple orbits. -/
def E6Folding : Prop :=
  (∀ j, orbitFirst j ≠ orbitSecond j → e6Cartan (orbitFirst j) (orbitSecond j) = 0) ∧
  (∀ r, IsRootCoordinate e6Cartan r →
    (r ≠ e6Diagram.mulVec r → dotProduct r (e6Cartan.mulVec (e6Diagram.mulVec r)) = 0) ∧
    (IsLongF4Doubled (foldedRoot r) ↔ r = e6Diagram.mulVec r) ∧
    (IsShortF4Doubled (foldedRoot r) ↔ r ≠ e6Diagram.mulVec r) ∧
    ∃ (j : Fin 4) (w : List (Fin 4)),
      (r = orbitWord w (Pi.single (orbitFirst j) 1) ∨
       r = orbitWord w (Pi.single (orbitSecond j) 1)) ∧
      (r = e6Diagram.mulVec r ↔ orbitFirst j = orbitSecond j)) ∧
  (∀ r s, IsRootCoordinate e6Cartan r → IsRootCoordinate e6Cartan s →
    (foldedRoot r = foldedRoot s ↔ s = r ∨ s = e6Diagram.mulVec r)) ∧
  (∀ z, (IsLongF4Doubled z ∨ IsShortF4Doubled z) ↔
    ∃ r, IsRootCoordinate e6Cartan r ∧ foldedRoot r = z)

/-- The coordinate map from the orthonormal realization of the folded
apartment into the actual E₆ fundamental coweight coordinates. -/
def foldedApartment {K : Type*} [Field K] (v : Fin 4 → K) : Fin 6 → K :=
  let u j := (∑ i, (f4SimpleDoubled j i : K) * v i) / 2
  ![u 3, u 0, u 2, u 1, u 2, u 3]

/-- Inverse on the invariant apartment. -/
def unfoldApartment {K : Type*} [Field K] (x : Fin 6 → K) : Fin 4 → K :=
  ![2 * x 0 + x 1 + 2 * x 3 + 3 * x 2, x 1 + x 3 + x 2, x 3 + x 2, x 2]

/-- The folded identification matches restriction of roots and projection
of coroots, over both the rational and real apartment. -/
def FoldedApartmentCoordinates.{u} : Prop :=
  ∀ {K : Type u} [Field K] [CharZero K],
    (∀ v : Fin 4 → K, unfoldApartment (foldedApartment v) = v) ∧
    (∀ x : Fin 6 → K, x 0 = x 5 → x 2 = x 4 → foldedApartment (unfoldApartment x) = x) ∧
    (∀ (r : Fin 6 → ℤ) (v : Fin 4 → K),
      (∑ i, (r i : K) * foldedApartment v i) = (∑ j, (foldedRoot r j : K) * v j) / 2) ∧
    (∀ (r : Fin 6 → ℤ) (i : Fin 6),
      foldedApartment (fun j => (foldedRoot r j : K) / 2) i =
      (((1 + e6Diagram).mulVec (e6Cartan.mulVec r) i : ℤ) : K) / 2)

/-- Each projected absolute coroot is the coroot for the arrangement with
short root functionals doubled. The latter coroot is the Euclidean vector
(2gamma/(gammacdotgamma)), for the normalized root (gamma). -/
def FoldedNormalizedCoroots : Prop :=
  ∀ (r : Fin 6 → ℤ), IsRootCoordinate e6Cartan r →
    let β : Fin 4 → ℚ := fun j => (foldedRoot r j : ℚ) / 2
    let d : ℚ := if r = e6Diagram.mulVec r then 1 else 2
    let γ := d • β
    (γ ⬝ᵥ γ ≠ 0) ∧
    foldedApartment (fun j => 2 * γ j / (γ ⬝ᵥ γ)) =
      e6Projection (e6Cartan.mulVec r)

/-- The coroot lattice of the normalized folded arrangement in orthonormal
coordinates. Each vector is a coroot by `FoldedNormalizedCoroots`. -/
def foldedCorootLattice : AddSubgroup (Fin 4 → ℚ) :=
  AddSubgroup.closure (Set.range fun r : {r // IsRootCoordinate e6Cartan r} =>
    fun j => (foldedRoot r.val j : ℚ) / 2)

/-- The translation lattice of the normalized folded arrangement agrees with
both projected split lattices in invariant coweight coordinates. -/
def FoldedLatticeComparison : Prop :=
  foldedApartment '' (foldedCorootLattice : Set (Fin 4 → ℚ)) =
    Set.range (fun t => e6Projection (e6Cartan.mulVec t)) ∧
  foldedApartment '' (foldedCorootLattice : Set (Fin 4 → ℚ)) = Set.range e6Projection

/-- The folded arrangement in the fixed space of the actual cocharacter
lattice. Its normalized root functions are the restrictions of the absolute
roots multiplied by their depth denominators. -/
def E6FoldedDatumInCocharacters.{u,v,w,z} : Prop :=
  ∀ {ι : Type u} {X : Type v} {Y : Type w} {K : Type z}
    [Finite ι] [AddCommGroup X] [AddCommGroup Y] [Field K] [CharZero K]
    [Module.Free ℤ X] [Module.Finite ℤ X] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (P : RootDatum (ι := ι) X Y) [P.IsReduced] (B : P.Base) (e : Fin 6 ≃ B.support)
    (σ : P.Equiv P), Module.finrank ℤ Y = 6 →
    (∀ i, σ.indexEquiv (e i) = (e (e6Partner i) : ι)) →
    (∀ i j, e6Cartan i j = P.pairing (e i) (e j)) →
    let E := ApartmentRoots.split P K
    let τ : (K ⊗[ℤ] Y) ≃ₗ[K] (K ⊗[ℤ] Y) := diagramCocharacters σ
    ∃ (f : (Fin 4 → K) ≃ₗ[K] diagramFixedSpace τ) (d : ι → FoldedRootDirection)
      (D : ApartmentRoots K (Fin 4 → K) FoldedRootDirection),
      (∀ x, simpleRootValues P B e K (f x).val = foldedApartment x) ∧
      Function.Surjective d ∧
      (∀ i j, d i = d j ↔ j = i ∨ j = σ.indexEquiv i) ∧
      (∀ i, IsLongF4Doubled (d i).val ↔ σ.indexEquiv i = i) ∧
      (∀ i, σ.indexEquiv i ≠ i → P.pairing i (σ.indexEquiv i) = 0) ∧
      D.root = normalizedFoldedRoot K ∧ D.coroot = normalizedFoldedCoroot K ∧ D.ReflectionClosed ∧
      (∀ i x, D.root (d i) x = (foldedDepthDenominator (d i) : K) * E.root i (f x).val) ∧
      (∀ i, (f (D.coroot (d i))).val = diagramAverage τ (E.coroot i)) ∧
      (fun x => (f x).val) '' (D.corootLattice : Set (Fin 4 → K)) =
        diagramAverage τ '' (E.corootLattice : Set (K ⊗[ℤ] Y))

/-- Both isogeny types give the same translation lattice projected into
the actual fixed space. The equality holds after real extension as well. -/
def E6ProjectedCocharacters.{u,v,w,z} : Prop :=
  ∀ {ι : Type u} {X : Type v} {Y : Type w} {K : Type z}
    [Finite ι] [AddCommGroup X] [AddCommGroup Y] [Field K] [CharZero K]
    [Module.Free ℤ X] [Module.Finite ℤ X] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (P : RootDatum (ι := ι) X Y) [P.IsReduced] (B : P.Base) (e : Fin 6 ≃ B.support)
    (σ : P.Equiv P), Module.finrank ℤ Y = 6 →
    (∀ i, σ.indexEquiv (e i) = (e (e6Partner i) : ι)) →
    (∀ i j, e6Cartan i j = P.pairing (e i) (e j)) →
    let E := ApartmentRoots.split P K
    let p := diagramAverage (diagramCocharacters (K := K) σ)
    p '' (E.corootLattice : Set (K ⊗[ℤ] Y)) = p '' (E.coweightLattice : Set (K ⊗[ℤ] Y))

/-- The ramified alcove in the diagram-fixed cocharacter space. The original
relative wall equations, their normalized signs and both translation lattices
refer to the same reflections. -/
def FoldedPinnedAlcoveGeometry.{u,v,w,z} : Prop :=
  ∀ {ι : Type u} {X : Type v} {Y : Type w} {K : Type z}
    [Finite ι] [AddCommGroup X] [AddCommGroup Y] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Archimedean K] [FloorRing K]
    [Module.Free ℤ X] [Module.Finite ℤ X] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (P : RootDatum (ι := ι) X Y) [P.IsReduced] (B : P.Base) (e : Fin 6 ≃ B.support)
    (σ : P.Equiv P), Module.finrank ℤ Y = 6 →
    (∀ i, σ.indexEquiv (e i) = (e (e6Partner i) : ι)) →
    (∀ i j, e6Cartan i j = P.pairing (e i) (e j)) →
    let E := ApartmentRoots.split P K
    let τ : (K ⊗[ℤ] Y) ≃ₗ[K] (K ⊗[ℤ] Y) := diagramCocharacters σ
    let A := diagramFixedSpace τ
    ∃ (d : ι → FoldedRootDirection) (D : ApartmentRoots K A FoldedRootDirection) (p : A),
      Function.Surjective d ∧ (∀ i j, d i = d j ↔ j = i ∨ j = σ.indexEquiv i) ∧
      (∀ i, IsLongF4Doubled (d i).val ↔ σ.indexEquiv i = i) ∧
      (∀ i, σ.indexEquiv i ≠ i → P.pairing i (σ.indexEquiv i) = 0) ∧
      (∀ i x, D.root (d i) x = (foldedDepthDenominator (d i) : K) * E.root i x.val) ∧
      (∀ i, (D.coroot (d i)).val = diagramAverage τ (E.coroot i)) ∧
      (∀ i x,
        (σ.indexEquiv i = i → (D.linearReflection (d i) x).val = E.linearReflection i x.val) ∧
        (σ.indexEquiv i ≠ i → (D.linearReflection (d i) x).val =
          E.linearReflection i (E.linearReflection (σ.indexEquiv i) x.val))) ∧
      (∀ i (n : ℤ) (x : A),
        let a := E.root i x.val + (n : K) / (foldedDepthDenominator (d i) : K)
        (a = 0 ↔ D.wallValue (d i, n) x = 0) ∧ (0 < a ↔ D.positive x (d i, n))) ∧
      (∀ i, 0 < D.root (d i) p ↔ B.IsPos i) ∧
      PinnedWallSigns D p (fun j => ∃ i, d i = j ∧ B.IsPos i) ∧
      AlcoveGeometry D p ∧
      A.subtype '' (D.corootLattice : Set A) = diagramAverage τ '' (E.corootLattice : Set (K ⊗[ℤ] Y)) ∧
      A.subtype '' (D.coweightLattice : Set A) = diagramAverage τ '' (E.coweightLattice : Set (K ⊗[ℤ] Y)) ∧
      D.affineWeylGroup = D.extendedAffineWeylGroup ∧
      Subsingleton (alcoveStabilizer D (D.alcove p))

end LinearAlgebraicGroups.Specs.ExceptionalAffineRootSystems
