import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.VoganEquivalence
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.Lie.Prod

/-! The inner rows of LA-J08. Vertex (i+1) of the source is indexed by (i). -/

namespace Specs.LieAlgebrasAndRepresentations.ExceptionalInnerInvolutions

open VoganEquivalence (reflectedColors)

inductive Diagram where
  | G2 | F4 | E6 | E7 | E8
  deriving DecidableEq, Repr

abbrev Diagram.rank : Diagram → ℕ
  | .G2 => 2
  | .F4 => 4
  | .E6 => 6
  | .E7 => 7
  | .E8 => 8

abbrev Vertex (D : Diagram) := Fin D.rank
abbrev Root (D : Diagram) := Vertex D → ℤ
abbrev Color (D : Diagram) := Vertex D → ZMod 2

def adjacent (i j : ℕ) : Prop := i + 1 = j ∨ j + 1 = i

instance (i j : ℕ) : Decidable (adjacent i j) := inferInstanceAs (Decidable (_ ∨ _))

def chain (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j =>
  if i = j then 2 else if adjacent i j then -1 else 0

def eDiagram (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j =>
  if i = j then 2 else
  if (adjacent i j ∧ (i : ℕ) + 1 < n ∧ (j : ℕ) + 1 < n) ∨
      ((i : ℕ) = 2 ∧ (j : ℕ) + 1 = n) ∨ ((j : ℕ) = 2 ∧ (i : ℕ) + 1 = n)
    then -1 else 0

def cartan (D : Diagram) : Matrix (Vertex D) (Vertex D) ℤ := fun i j =>
  match D with
  | .G2 => if i = j then 2 else if (i : ℕ) = 0 then -3 else -1
  | .F4 => if i = j then 2 else if (i : ℕ) = 1 ∧ (j : ℕ) = 2 then -2
      else if adjacent i j then -1 else 0
  | .E6 => eDiagram 6 i j
  | .E7 => eDiagram 7 i j
  | .E8 => eDiagram 8 i j

def lengthFactor (D : Diagram) (i : Vertex D) : ℤ :=
  match D with
  | .G2 => if (i : ℕ) = 0 then 1 else 3
  | .F4 => if (i : ℕ) < 2 then 1 else 2
  | _ => 1

def unit (D : Diagram) (i : Vertex D) : Root D := fun j => if i = j then 1 else 0

def reflect (D : Diagram) (i : Vertex D) (c : Root D) : Root D := fun j =>
  if i = j then c j - ∑ k, cartan D i k * c k else c j

def colorAt (D : Diagram) (mask : ℕ) : Color D := fun i =>
  if mask.testBit i then 1 else 0

def parity (D : Diagram) (b : Color D) (c : Root D) : ZMod 2 :=
  ∑ i, (c i : ZMod 2) * b i

def gram (D : Diagram) (c d : Root D) : ℤ :=
  ∑ i, ∑ j, (c i * lengthFactor D i * cartan D i j) * d j

/-- Forward generation by the stated reflections, independent of termination bounds. -/
inductive Generated {α ι : Type*} (s : ι → α → α) (start : Set α) : α → Prop
  | initial {x : α} : x ∈ start → Generated s start x
  | next {x : α} (i : ι) : Generated s start x → Generated s start (s i x)

def IsDiagramPerm {D : Diagram} (p : Equiv.Perm (Vertex D)) : Prop :=
  ∀ i j, cartan D (p i) (p j) = cartan D i j

/-- The orbit relation allows all simple reflections and every directed
Cartan-matrix automorphism. -/
inductive ColorOrbit (D : Diagram) (b : Color D) : Color D → Prop
  | initial : ColorOrbit D b b
  | reflection {c : Color D} (i : Vertex D) : ColorOrbit D b c →
      ColorOrbit D b (reflectedColors (cartan D) i c)
  | diagram {c : Color D} (p : Equiv.Perm (Vertex D)) : IsDiagramPerm p →
      ColorOrbit D b c → ColorOrbit D b (c ∘ p)

def dDiagram (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j =>
  if i = j then 2 else
  if (adjacent i j ∧ (i : ℕ) + 1 < n ∧ (j : ℕ) + 1 < n) ∨
      ((i : ℕ) + 3 = n ∧ (j : ℕ) + 1 = n) ∨ ((j : ℕ) + 3 = n ∧ (i : ℕ) + 1 = n)
    then -1 else 0

/-- Block sum indexed by the first block followed by the second block. -/
def block {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℤ) (B : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin (m+n)) (Fin (m+n)) ℤ := fun i j =>
  (finSumFinEquiv.symm i).elim
    (fun x => (finSumFinEquiv.symm j).elim (A x) (fun _ => 0))
    (fun x => (finSumFinEquiv.symm j).elim (fun _ => 0) (B x))

/-- B₄ has its short root last. C₃ has its long root last. -/
def b4 : Matrix (Fin 4) (Fin 4) ℤ := fun i j =>
  if i = 3 ∧ j = 2 then -2 else chain 4 i j

def c3 : Matrix (Fin 3) (Fin 3) ℤ := fun i j =>
  if i = 1 ∧ j = 2 then -2 else chain 3 i j

structure Row where
  mask : ℕ
  size : ℕ
  fixedRank : ℕ
  matrix : Matrix (Fin fixedRank) (Fin fixedRank) ℤ
  center : ℕ
  dimension : ℕ
  signature : ℤ

def rows : Diagram → List Row
  | .G2 => [⟨0,1,2,cartan .G2,0,14,-14⟩, ⟨1,3,2,block (chain 1) (chain 1),0,6,2⟩]
  | .F4 => [⟨0,1,4,cartan .F4,0,52,-52⟩, ⟨1,3,4,b4,0,36,-20⟩,
      ⟨4,12,4,block c3 (chain 1),0,24,4⟩]
  | .E6 => [⟨0,1,6,cartan .E6,0,78,-78⟩, ⟨1,27,5,dDiagram 5,1,46,-14⟩,
      ⟨2,36,6,block (chain 5) (chain 1),0,38,2⟩]
  | .E7 => [⟨0,1,7,cartan .E7,0,133,-133⟩, ⟨1,63,7,block (dDiagram 6) (chain 1),0,69,-5⟩,
      ⟨8,36,7,chain 7,0,63,7⟩, ⟨10,28,6,eDiagram 6,1,79,-25⟩]
  | .E8 => [⟨0,1,8,cartan .E8,0,248,-248⟩, ⟨1,135,8,dDiagram 8,0,120,8⟩,
      ⟨2,120,8,block (eDiagram 7) (chain 1),0,136,-24⟩]

/-- Positive even roots and their indecomposable elements. -/
def positiveEven (D : Diagram) (b : Color D) (R : Finset (Root D)) : Finset (Root D) :=
  R.filter fun c => parity D b c = 0 ∧ ∀ i, 0 ≤ c i

def simpleEven (D : Diagram) (b : Color D) (R : Finset (Root D)) : Finset (Root D) :=
  let P := positiveEven D b R
  P.filter fun c => ∀ x ∈ P, c - x ∉ P

def rowRootCheck (D : Diagram) (r : Row) (R : Finset (Root D)) : Prop :=
  let b := colorAt D r.mask
  r.dimension = D.rank + (R.filter (fun c => parity D b c = 0)).card ∧
  r.signature = (D.rank + R.card : ℤ) - 2 * r.dimension ∧
  D.rank = r.fixedRank + r.center ∧
  ∃ base : Fin r.fixedRank → Root D, Function.Injective base ∧
    Finset.univ.image base = simpleEven D b R ∧
    (∀ i, gram D (base i) (base i) ≠ 0) ∧
    ∀ i j, 2 * gram D (base i) (base j) = gram D (base i) (base i) * r.matrix i j

/-- The exact finite computation, including the full orbit relation and the
Cartan matrices of the even-root subsystems. -/
def finiteTablesType : Prop :=
  ∀ D : Diagram, ∃ R : Finset (Root D),
    (∀ c, c ∈ R ↔ Generated (reflect D) (Set.range (unit D)) c) ∧
    (∀ b : Color D, ∃ r ∈ rows D, ColorOrbit D (colorAt D r.mask) b) ∧
    (∀ r ∈ rows D, ∃ O : Finset (Color D),
      (∀ b, b ∈ O ↔ ColorOrbit D (colorAt D r.mask) b) ∧ O.card = r.size ∧
      rowRootCheck D r R) ∧
    ∀ r ∈ rows D, ∀ s ∈ rows D, r.mask ≠ s.mask →
      ¬ ColorOrbit D (colorAt D r.mask) (colorAt D s.mask)


open _root_.LieAlgebrasAndRepresentations.RealForms (Conjugation Intertwines)
open _root_.LieAlgebrasAndRepresentations.Serre (Algebra)
open VoganEquivalence (colorSign)
open SerreRelations (simple)
open VermaModules (Direction Regular)
open RootDecomposition (rootSpace_value)
open IntegrableHighestWeightQuotient (Normalized)
open RootForm (coroot_value)
open CartanDecompositionSignature (complexFixed killingSignature)
open PolarRealStructures (IsCompact involutionConjugation)

universe u

/-- In a normalized inner datum, each root space carries the character of its
integral root coordinates. The simple roots are numbered in source order. -/
def innerRootActionType : Prop :=
  ∀ (D : Diagram) {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (ω : Conjugation L) (H : LieSubalgebra ℂ L),
    MaximalTori.IsMaximalToral_value H → (∀ h ∈ H, ω.map h ∈ H) →
    ∀ (φ : Direction H), Regular H φ →
    ∀ (e f : simple H φ → L), Normalized H φ e f →
    (∀ i, ω.map (e i) = -f i) →
    ∀ (a : L ≃ₗ⁅ℂ⁆ L), (∀ h : H, a (h : L) = (h : L)) →
    ∀ (s : Vertex D ≃ simple H φ) (b : Color D),
    (∀ i, a (e (s i)) = colorSign (b i) • e (s i) ∧
      a (f (s i)) = colorSign (b i) • f (s i)) →
    ∀ (c : Root D) (x : L), x ∈ rootSpace_value H (∑ i, c i • (s i).val) →
      a x = colorSign (parity D b c) • x

/-- The source numbering on a simple system of the ambient complex algebra. -/
structure NumberedCartan (D : Diagram) (L : Type u)
    [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] where
  subalgebra : LieSubalgebra ℂ L
  maximalToral : MaximalTori.IsMaximalToral_value subalgebra
  direction : Direction subalgebra
  regular : Regular subalgebra direction
  number : Vertex D ≃ simple subalgebra direction
  entries : ∀ i j, (number j).val (coroot_value subalgebra (number i).val) = (cartan D i j : ℂ)

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

/-- A complex-linear extension of an inner involution of the compact form. -/
structure CompactInnerInvolution [FiniteDimensional ℂ L] (ω : Conjugation L)
    (a : L ≃ₗ⁅ℂ⁆ L) : Prop where
  inner : a.toLinearEquiv ∈ CartanConjugacy.innerAutomorphisms_value L
  commutes : Intertwines ω ω a
  involutive : Function.Involutive a

def CompactConjugate (ω : Conjugation L) (a b : L ≃ₗ⁅ℂ⁆ L) : Prop :=
  ∃ g : L ≃ₗ⁅ℂ⁆ L, Intertwines ω ω g ∧ ∀ x, b (g x) = g (a x)

attribute [local instance 100] LieRing.ofAssociativeRing in
/-- The fixed complex Lie algebra is the indicated Serre algebra with an
abelian central factor, given by the commutative algebra `ℂ^r.center`. -/
def FixedRow (r : Row) (ω : Conjugation L) (a : L ≃ₗ⁅ℂ⁆ L)
    (hcomm : Intertwines ω ω a) (hinv : Function.Involutive a) : Prop :=
  Nonempty ((Algebra r.matrix × (Fin r.center → ℂ)) ≃ₗ⁅ℂ⁆ complexFixed a) ∧
    Module.finrank ℂ (complexFixed a) = r.dimension ∧
    killingSignature (involutionConjugation ω a hcomm hinv).fixed = r.signature

/-- Evaluation of a row on its actual Cartan and normalized root generators. -/
def fixedRowType : Prop :=
  ∀ (D : Diagram) (r : Row), r ∈ rows D →
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H →
    ∀ (φ : Direction H), Regular H φ → ∀ (s : Vertex D ≃ simple H φ),
    (∀ i j, (s j).val (coroot_value H (s i).val) = (cartan D i j : ℂ)) →
    ∀ (ω : Conjugation L), IsCompact ω → (∀ h ∈ H, ω.map h ∈ H) →
    ∀ (e f : simple H φ → L), Normalized H φ e f → (∀ i, ω.map (e i) = -f i) →
    ∀ (a : L ≃ₗ⁅ℂ⁆ L) (hcomm : Intertwines ω ω a) (hinv : Function.Involutive a),
    (∀ h : H, a (h : L) = (h : L)) →
    (∀ i, a (e (s i)) = colorSign (colorAt D r.mask i) • e (s i) ∧
      a (f (s i)) = colorSign (colorAt D r.mask i) • f (s i)) →
    FixedRow r ω a hcomm hinv

abbrev TableRow (D : Diagram) := { r : Row // r ∈ rows D }

/-- Every inner class is represented exactly once, for any compact form of
an ambient algebra of the specified type. The row also describes the fixed
algebra and intrinsic Killing signature of any involution in its class. -/
def innerInvolutionClassesType : Prop :=
  ∀ (D : Diagram) {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L → NumberedCartan D L →
    ∀ (ω : Conjugation L), IsCompact ω →
    ∃ (t : NumberedCartan D L) (a : TableRow D → L ≃ₗ⁅ℂ⁆ L)
      (ha : ∀ r, CompactInnerInvolution ω (a r)),
      (∀ x ∈ t.subalgebra, ω.map x ∈ t.subalgebra) ∧
      (∀ r (h : t.subalgebra), a r (h : L) = (h : L)) ∧
      (∀ r (c : Root D) (x : L), x ∈ rootSpace_value t.subalgebra (∑ i, c i • (t.number i).val) →
        a r x = colorSign (parity D (colorAt D r.val.mask) c) • x) ∧
      (∀ r, FixedRow r.val ω (a r) (ha r).commutes (ha r).involutive) ∧
      (∀ (b : L ≃ₗ⁅ℂ⁆ L), CompactInnerInvolution ω b →
        ∃! r : TableRow D, CompactConjugate ω (a r) b) ∧
      ∀ (b : L ≃ₗ⁅ℂ⁆ L) (hb : CompactInnerInvolution ω b) (r : TableRow D),
        CompactConjugate ω (a r) b → FixedRow r.val ω b hb.commutes hb.involutive

/-- The model for each block row is the indicated product of simple-type
Serre algebras with the ordered Cartan matrices of the two factors. -/
def serreBlockAlgebrasType : Prop :=
  ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℤ) (B : Matrix (Fin n) (Fin n) ℤ),
    (∀ i j, i ≠ j → A i j ≤ 0) → (∀ i j, i ≠ j → B i j ≤ 0) →
    Nonempty (Algebra (block A B) ≃ₗ⁅ℂ⁆ Algebra A × Algebra B)

end Specs.LieAlgebrasAndRepresentations.ExceptionalInnerInvolutions
