import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Action.CycleIndex
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Algebra.MvPolynomial.Rename

/-! Independent specification of the reflection part of paper.tex W34.
The abstract group has 2n elements; it is never replaced by its action image.
`false` denotes the sign +1 and `true` the sign -1. -/
namespace FiniteCombinatorics.ReflectionSpec

open scoped BigOperators

def pair {n : ℕ} (a : ZMod n) (e : Bool) : DihedralGroup n :=
  if e then DihedralGroup.sr (-a) else DihedralGroup.r a

def pairEquiv (n : ℕ) : ZMod n × Bool ≃ DihedralGroup n where
  toFun p := pair p.1 p.2
  invFun g := match g with
    | .r a => (a, false)
    | .sr b => (-b, true)
  left_inv := by rintro ⟨a, e⟩; cases e <;> simp [pair]
  right_inv := by rintro (a | b) <;> simp [pair]

/-- The source action, with the Mathlib parameter `sr b` corresponding to (-b,-1). -/
def act {n : ℕ} (g : DihedralGroup n) (x : ZMod n) : ZMod n :=
  match g with
  | .r a => a + x
  | .sr b => -b - x

instance dihedralAction (n : ℕ) : MulAction (DihedralGroup n) (ZMod n) where
  smul := act
  one_smul x := by change (0 : ZMod n) + x = x; exact zero_add x
  mul_smul g h x := by
    change act (g * h) x = act g (act h x)
    cases g <;> cases h <;> simp [act, DihedralGroup.r_mul_r,
      DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr] <;> abel

def reflection {n : ℕ} (a : ZMod n) : Equiv.Perm (ZMod n) where
  toFun x := a - x
  invFun x := a - x
  left_inv x := sub_sub_cancel a x
  right_inv x := sub_sub_cancel a x

noncomputable def fixedResidues {n : ℕ} [NeZero n] (a : ZMod n) : Finset (ZMod n) := by
  classical
  exact Finset.univ.filter (fun x => 2 * x = a)

noncomputable def reflectionCount {n : ℕ} [NeZero n] (a : ZMod n) (k : ℕ) : ℕ :=
  PermutationCyclesSpec.countCyclesOfLength (reflection a) k

noncomputable def solvableOffsets (n : ℕ) [NeZero n] : Finset (ZMod n) := by
  classical
  exact Finset.univ.filter (fun a => ∃ x : ZMod n, 2 * x = a)

noncomputable def reflectionMonomial {R : Type*} [CommMonoid R] {n : ℕ} [NeZero n]
    (a : ZMod n) (s : ℕ → R) : R :=
  ∏ k ∈ Finset.Icc 1 n, s k ^ reflectionCount a k

-- Expected definition types and canonical values.
def dihedralActionType := (n : ℕ) → MulAction (DihedralGroup n) (ZMod n)
def pairType := {n : ℕ} → ZMod n → Bool → DihedralGroup n
def pairEquivType := (n : ℕ) → ZMod n × Bool ≃ DihedralGroup n
def reflectionType := {n : ℕ} → ZMod n → Equiv.Perm (ZMod n)
def fixedResiduesType := {n : ℕ} → [NeZero n] → ZMod n → Finset (ZMod n)
def reflectionCountType := {n : ℕ} → [NeZero n] → ZMod n → ℕ → ℕ
def solvableOffsetsType := (n : ℕ) → [NeZero n] → Finset (ZMod n)
def reflectionMonomialType := {R : Type*} → [CommMonoid R] → {n : ℕ} → [NeZero n] →
  ZMod n → (ℕ → R) → R

def PairMul : Prop := ∀ {n : ℕ} (a b : ZMod n) (e f : Bool),
  pair a e * pair b f = pair (a + if e then -b else b) (Bool.xor e f)
def PairAction : Prop := ∀ {n : ℕ} (a x : ZMod n) (e : Bool),
  pair a e • x = a + if e then -x else x
def GroupCard : Prop := ∀ (n : ℕ) [NeZero n], Fintype.card (DihedralGroup n) = 2 * n
def ReflectionAction : Prop := ∀ {n : ℕ} (a : ZMod n),
  CycleIndexSpec.actionPermutation (DihedralGroup n) (ZMod n) (pair a true) = reflection a
def ReflectionSquare : Prop := ∀ {n : ℕ} (a : ZMod n), (pair a true) ^ 2 = 1
def ReflectionInvolutive : Prop := ∀ {n : ℕ} (a : ZMod n), Function.Involutive (reflection a)
def FixedEquation : Prop := ∀ {n : ℕ} (a x : ZMod n), reflection a x = x ↔ 2 * x = a

def ReflectionNumber : Prop := ∀ (n : ℕ) [NeZero n],
  (Finset.univ.image (fun a : ZMod n => pair a true)).card = n

def CycleLengths : Prop := ∀ {n : ℕ} [NeZero n] (a : ZMod n) (k : ℕ),
  k ≠ 1 → k ≠ 2 → reflectionCount a k = 0

def OddClassification : Prop := ∀ {n : ℕ} [NeZero n] (_hn : Odd n) (a : ZMod n),
  (fixedResidues a).card = 1 ∧ reflectionCount a 1 = 1 ∧
    reflectionCount a 2 = (n - 1) / 2

def EvenClassification : Prop := ∀ {n : ℕ} [NeZero n] (_hn : Even n) (a : ZMod n),
  (a ∈ solvableOffsets n → (fixedResidues a).card = 2 ∧
    reflectionCount a 1 = 2 ∧ reflectionCount a 2 = (n - 2) / 2) ∧
  (a ∉ solvableOffsets n → (fixedResidues a).card = 0 ∧
    reflectionCount a 1 = 0 ∧ reflectionCount a 2 = n / 2)

def EvenDistribution : Prop := ∀ {n : ℕ} [NeZero n], Even n →
  (solvableOffsets n).card = n / 2 ∧
    ((Finset.univ : Finset (ZMod n)) \ solvableOffsets n).card = n / 2

def OddMonomial : Prop := ∀ {R : Type*} [CommMonoid R] {n : ℕ} [NeZero n],
  Odd n → ∀ (a : ZMod n) (s : ℕ → R), reflectionMonomial a s = s 1 * s 2 ^ ((n - 1) / 2)

def EvenMonomial : Prop := ∀ {R : Type*} [CommMonoid R] {n : ℕ} [NeZero n],
  Even n → ∀ (a : ZMod n) (s : ℕ → R),
    reflectionMonomial a s = if a ∈ solvableOffsets n then
      s 1 ^ 2 * s 2 ^ ((n - 2) / 2) else s 2 ^ (n / 2)

def ActionCount : Prop := ∀ {n : ℕ} [NeZero n] (a : ZMod n) (k : ℕ),
  CycleIndexSpec.countCycles (DihedralGroup n) (ZMod n) (pair a true) k = reflectionCount a k

def MonomialBridge : Prop := ∀ {n : ℕ} [NeZero n] (a : ZMod n),
  MvPolynomial.rename (fun i : Fin (Fintype.card (ZMod n)) => i.val + 1)
    (CycleIndexSpec.elementMonomial (DihedralGroup n) (ZMod n) (pair a true)) =
      reflectionMonomial a (MvPolynomial.X : ℕ → MvPolynomial ℕ ℚ)

def EvenCountDistribution : Prop := ∀ {n : ℕ} [NeZero n], Even n →
  (Finset.univ.filter (fun a : ZMod n => reflectionCount a 1 = 2)).card = n / 2 ∧
  (Finset.univ.filter (fun a : ZMod n => reflectionCount a 1 = 0)).card = n / 2

def OneMonomial : Prop := ∀ {R : Type*} [CommMonoid R]
  (a : ZMod 1) (s : ℕ → R), reflectionMonomial a s = s 1

end FiniteCombinatorics.ReflectionSpec
