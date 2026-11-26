import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.Pinning

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.RankTwoRelations

open AdjointRepresentation (GroupPoints)
open CharacterDescent (Character)
open CharacterPairing (absoluteRoots)
open Pinning (PinnedGroup RootCoordinate)
open RootGroups (AdditiveLine CorootReflection Proportional rankOneWord rootPoint)

noncomputable section

/-- The four possibilities for a reduced root system of semisimple rank two. -/
inductive TypeOfRoots where
  | orthogonal | a2 | b2 | g2
  deriving DecidableEq

/-- Coordinates in the ordered basis of simple roots. The first root is short
when the lengths differ. The torus can have additional central directions. -/
abbrev RootIndex := ℤ × ℤ

def a : RootIndex := (1, 0)
def b : RootIndex := (0, 1)
def c : RootIndex := (1, 1)
def d : RootIndex := (2, 1)
def e : RootIndex := (3, 1)
def f : RootIndex := (3, 2)

def positiveList : TypeOfRoots → List RootIndex
  | .orthogonal => [a, b]
  | .a2 => [a, b, c]
  | .b2 => [a, b, c, d]
  | .g2 => [a, b, c, d, e, f]

def IsIndex (τ : TypeOfRoots) (r : RootIndex) : Prop :=
  r ∈ positiveList τ ∨ -r ∈ positiveList τ

abbrev Index (τ : TypeOfRoots) := {r : RootIndex // IsIndex τ r}

/-- An ordered simple basis of the actual group, with its full signed root list. -/
structure Frame {k : Type u} [Field k] {A : AdditiveLine k}
    (P : PinnedGroup A) (τ : TypeOfRoots) where
  first : Pinning.SimpleRoot P.pair
  second : Pinning.SimpleRoot P.pair
  independent : Function.Injective (fun r : RootIndex =>
    first.val.val ^ r.1 * second.val.val ^ r.2)
  root_iff : ∀ χ : Character P.pair.T.group, χ ∈ absoluteRoots P.pair.T ↔
    ∃ r : Index τ, χ = first.val.val ^ r.val.1 * second.val.val ^ r.val.2

variable {k : Type u} [Field k] {A : AdditiveLine k} {P : PinnedGroup A}
  {τ : TypeOfRoots}

def Frame.character (F : Frame P τ) (r : RootIndex) : Character P.pair.T.group :=
  F.first.val.val ^ r.1 * F.second.val.val ^ r.2

def Frame.root (F : Frame P τ) (r : Index τ) : AbstractPairing.Root P.pair.T :=
  ⟨F.character r, (F.root_iff _).2 ⟨r, rfl⟩⟩

/-- Explicit integer reflections on the two simple-root coordinates. -/
def reflection (τ : TypeOfRoots) (i : Bool) (r : RootIndex) : RootIndex :=
  if i then (r.1, -r.2 + (if τ = .orthogonal then 0 else 1) * r.1)
  else (-r.1 + (match τ with | .orthogonal => 0 | .a2 => 1 | .b2 => 2 | .g2 => 3) * r.2, r.2)

/-- The signs on the positive coordinates, also used on their linked opposites. -/
def actionSign (τ : TypeOfRoots) (i : Bool) (r : RootIndex) : ℤ :=
  let has (s : RootIndex) : Bool := r == s || r == -s
  if i then
    if has b || (match τ with
      | .orthogonal => false
      | .a2 => has a
      | .b2 => has c
      | .g2 => has c || has f) then -1 else 1
  else
    if has a || (match τ with
      | .orthogonal => false
      | .a2 | .b2 => has c
      | .g2 => has d || has e) then -1 else 1

/-- One monomial in the ordered list of root correction factors. -/
structure Correction where
  root : RootIndex
  leftDegree : ℕ
  rightDegree : ℕ
  coefficient : ℤ

/-- The root and two exponents encode the strictly positive cone. The
integer coefficient is computed in the coordinates specified below. -/
def correctionTable (τ : TypeOfRoots) (r s : RootIndex) : List Correction :=
  if r = a ∧ s = b then
    match τ with
    | .orthogonal => []
    | .a2 => [⟨c, 1, 1, 1⟩]
    | .b2 => [⟨c, 1, 1, -1⟩, ⟨d, 2, 1, 1⟩]
    | .g2 => [⟨c, 1, 1, -1⟩, ⟨d, 2, 1, 1⟩, ⟨e, 3, 1, 1⟩, ⟨f, 3, 2, 1⟩]
  else if r = a ∧ s = c then
    match τ with
    | .b2 => [⟨d, 1, 1, -2⟩]
    | .g2 => [⟨d, 1, 1, -2⟩, ⟨e, 2, 1, -3⟩, ⟨f, 1, 2, 3⟩]
    | _ => []
  else if τ = .g2 then
    if r = a ∧ s = d then [⟨e, 1, 1, 3⟩]
    else if r = b ∧ s = e then [⟨f, 1, 1, 1⟩]
    else if r = c ∧ s = d then [⟨f, 1, 1, 3⟩]
    else []
  else []

/-- In each positive commutation, these factors follow the unmodified
second coordinate in the conjugation product. -/
def correctionFactors {R : Type*} [CommRing R] (τ : TypeOfRoots)
    (r s : RootIndex) (x y : R) : List (RootIndex × R) :=
  (correctionTable τ r s).map fun t =>
    (t.root, (t.coefficient : R) * x ^ t.leftDegree * y ^ t.rightDegree)

/-- Coordinates on the actual root groups. Link each positive coordinate with its
opposite by the rank-one word and its reflection on the character lattice. -/
structure Coordinates where
  coordinate : ∀ α : AbstractPairing.Root P.pair.T,
    RootCoordinate A P.pair.T (P.roots α).val α.val
  pin : ∀ α, coordinate α.val = P.pin α
  linked : ∀ α β : AbstractPairing.Root P.pair.T,
    α ∈ BorelsAndChambers.subgroupRoots P.pair.T P.pair.B → β.val = α.val⁻¹ →
    Nonempty (CorootReflection P.pair.T α.val
      ((coordinate α).val.hom ≫ (P.roots α).val.inclusion)
      ((coordinate β).val.hom ≫ (P.roots β).val.inclusion))

variable (F : Frame P τ) (X : Coordinates (P := P))

def rootMap (α : AbstractPairing.Root P.pair.T) : A.group ⟶ P.pair.G.val :=
  (X.coordinate α).val.hom ≫ (P.roots α).val.inclusion

/-- Evaluation on a label. The neutral value off the root list makes the
finite tables total. All labels used in the relations are root labels. -/
def point (R : TestAlgebra k) (r : RootIndex) (x : R) : GroupPoints P.pair.G.val R := by
  classical
  exact if h : F.character r ∈ absoluteRoots P.pair.T then
    rootPoint (rootMap X ⟨_, h⟩) R x else 1

def representative (R : TestAlgebra k) (i : Bool) : GroupPoints P.pair.G.val R :=
  let r := if i then b else a
  point F X R r 1 * point F X R (-r) (-1) * point F X R r 1

def ActsOn (i : Bool) (r s : RootIndex) (ε : ℤ) : Prop :=
  ∀ (R : TestAlgebra k) (x : R),
    let n := representative F X R i
    n * point F X R r x * n⁻¹ = point F X R s ((ε : R) * x)

/-- The positive coordinate choices made by the manuscript. -/
def WeylNormalization : Prop :=
  match τ with
  | .orthogonal => True
  | .a2 => ActsOn F X false b c 1
  | .b2 => ActsOn F X true a c 1 ∧ ActsOn F X false b d 1
  | .g2 => ActsOn F X true a c 1 ∧ ActsOn F X false c d 1 ∧
    ActsOn F X false b e 1 ∧ ActsOn F X true e f 1

def SimpleActions : Prop :=
  ∀ (i : Bool) (r : Index τ), ActsOn F X i r (reflection τ i r) (actionSign τ i r)

def positiveCorrection (R : TestAlgebra k) (r s : RootIndex) (x y : R) :
    GroupPoints P.pair.G.val R :=
  ((correctionFactors τ r s x y).map fun q => point F X R q.1 q.2).prod

def PositiveRelations : Prop :=
  ∀ (r s : RootIndex), r ∈ positiveList τ → s ∈ positiveList τ →
    (positiveList τ).idxOf r < (positiveList τ).idxOf s →
    ∀ (R : TestAlgebra k) (x y : R),
      point F X R r x * point F X R s y * point F X R r (-x) =
        point F X R s y * positiveCorrection F X R r s x y

def wordAction (τ : TypeOfRoots) (word : List Bool) (r : RootIndex) (ε : ℤ) :
    RootIndex × ℤ :=
  word.foldr (fun i q => (reflection τ i q.1, actionSign τ i q.1 * q.2)) (r, ε)

def positiveCommutator (R : TestAlgebra k) (r s : RootIndex) (x y : R) :
    GroupPoints P.pair.G.val R :=
  if (positiveList τ).idxOf r < (positiveList τ).idxOf s then
    point F X R s y * positiveCorrection F X R r s x y * (point F X R s y)⁻¹
  else
    (point F X R r x * positiveCorrection F X R s r y x * (point F X R r x)⁻¹)⁻¹

/-- Any independent signed pair can be transported into the chosen positive
system. Conjugation by the same word gives exactly the indicated commutator. -/
def SignedRelations : Prop :=
  ∀ (r s : Index τ), ¬ Proportional (F.character r) (F.character s) →
    ∃ word : List Bool,
      let p := wordAction τ word r 1
      let q := wordAction τ word s 1
      p.1 ∈ positiveList τ ∧ q.1 ∈ positiveList τ ∧
      ∀ (R : TestAlgebra k) (x y : R),
        let n := (word.map (representative F X R)).prod
        n * (point F X R r x * point F X R s y *
            (point F X R r x)⁻¹ * (point F X R s y)⁻¹) * n⁻¹ =
          positiveCommutator F X R p.1 q.1 ((p.2 : R) * x) ((q.2 : R) * y)

/-- Every system of linked coordinates with the prescribed Weyl
normalization satisfies the same table. -/
def DeterminedRelations : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k} (P : PinnedGroup A)
    (τ : TypeOfRoots) (F : Frame P τ) (X : Coordinates (P := P)),
    WeylNormalization F X → SimpleActions F X ∧ PositiveRelations F X ∧ SignedRelations F X

/-- The rank-two relations in existing split pinned groups over every field,
in the ordered coordinates of the manuscript. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k} (P : PinnedGroup A)
    (τ : TypeOfRoots) (F : Frame P τ),
    ∃ X : Coordinates (P := P), WeylNormalization F X ∧
      SimpleActions F X ∧ PositiveRelations F X ∧ SignedRelations F X

/-- In the orthogonal system all signed root groups from distinct factors
commute, on every test algebra. -/
def OrthogonalCommutation : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k} (P : PinnedGroup A)
    (F : Frame P .orthogonal)
    (r s : Index .orthogonal), ¬ Proportional (F.character r) (F.character s) →
    ∀ (R : TestAlgebra k) (x : GroupPoints (P.roots (F.root r)).val.group R)
      (y : GroupPoints (P.roots (F.root s)).val.group R),
      Commute
        (x ≫ (P.roots (F.root r)).val.inclusion.hom.hom : GroupPoints P.pair.G.val R)
        (y ≫ (P.roots (F.root s)).val.inclusion.hom.hom : GroupPoints P.pair.G.val R)

end

end LinearAlgebraicGroups.Specs.RankTwoRelations
