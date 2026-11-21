import Mathlib.Data.PNat.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Compactness.Compact

/-!
The residue-family model in FT-E06 (advanced-field-theory.tex, 1189–1198),
with the projections used in FT-E08 (1255–1258). Positive integers, including
1, are the indices; the transition from n to m is reduction when m divides n.
These canonical definitions are shared interfaces, independent of the proofs.
-/

namespace AdvancedFieldTheory.ProfiniteIntegers.ResidueSystem

abbrev Residues := (n : ℕ+) → ZMod (n : ℕ)

/-- Reduction from the larger modulus to the divisor modulus. -/
def reduction (m n : ℕ+) (h : (m : ℕ) ∣ (n : ℕ)) :
    ZMod (n : ℕ) →+ ZMod (m : ℕ) :=
  (ZMod.castHom h (ZMod (m : ℕ))).toAddMonoidHom

/-- The compatibility condition in the positive-divisibility inverse system. -/
def Compatible (a : Residues) : Prop :=
  ∀ (m n : ℕ+) (h : (m : ℕ) ∣ (n : ℕ)), reduction m n h (a n) = a m

/-- Compatible families form a subgroup of the product, with pointwise addition. -/
def compatibleResidues : AddSubgroup Residues where
  carrier := {a | Compatible a}
  zero_mem' := by intro m n h; exact map_zero _
  add_mem' := by
    intro a b ha hb m n h
    change reduction m n h (a n + b n) = a m + b m
    rw [map_add, ha m n h, hb m n h]
  neg_mem' := by
    intro a ha m n h
    change reduction m n h (-a n) = -a m
    rw [map_neg, ha m n h]

/-- The literal compatible-family subtype; its topology is the subtype of the
product topology, and its additive group operations are pointwise. -/
abbrev ResidueFamily := ↥compatibleResidues

/-- Coordinate projection as an additive homomorphism. -/
def coordinate (n : ℕ+) : ResidueFamily →+ ZMod (n : ℕ) where
  toFun a := a.val n
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The canonical integer residue family. -/
def integerResidues : ℤ →+ ResidueFamily where
  toFun z := ⟨fun n => (z : ZMod (n : ℕ)), by
    intro m n h
    exact map_intCast (ZMod.castHom h (ZMod (m : ℕ))) z⟩
  map_zero' := by apply Subtype.ext; funext n; exact Int.cast_zero
  map_add' a b := by apply Subtype.ext; funext n; exact Int.cast_add a b

end AdvancedFieldTheory.ProfiniteIntegers.ResidueSystem

namespace AdvancedFieldTheory.ProfiniteIntegers.ResidueModelSpec

open ResidueSystem

-- Expected definition types and values.
def ZhatType : Type 1 := Type
def ZhatValue : ZhatType := ResidueFamily

def ReductionType : Type := ∀ (m n : ℕ+), (m : ℕ) ∣ (n : ℕ) →
  (ZMod (n : ℕ) →+ ZMod (m : ℕ))
def ReductionValue : ReductionType := reduction

def ProjectionType : Type := ∀ n : ℕ+, ResidueFamily →+ ZMod (n : ℕ)
def ProjectionValue : ProjectionType := coordinate

def IntegerMapType : Type := ℤ →+ ResidueFamily
def IntegerMapValue : IntegerMapType := integerResidues

-- Full expected propositions; none assumes the result it specifies.
def TransitionLaws : Prop :=
  (∀ (n : ℕ+) (a : ZMod (n : ℕ)), reduction n n (dvd_refl _) a = a) ∧
  (∀ (l m n : ℕ+) (hlm : (l : ℕ) ∣ (m : ℕ)) (hmn : (m : ℕ) ∣ (n : ℕ))
    (a : ZMod (n : ℕ)),
    reduction l m hlm (reduction m n hmn a) = reduction l n (dvd_trans hlm hmn) a)

def CoordinateCompatibility : Prop :=
  ∀ (a : ResidueFamily) (m n : ℕ+) (h : (m : ℕ) ∣ (n : ℕ)),
    reduction m n h (coordinate n a) = coordinate m a

def IntegerCoordinates : Prop :=
  ∀ (z : ℤ) (n : ℕ+), coordinate n (integerResidues z) = (z : ZMod (n : ℕ))

def SubspaceTopology : Prop :=
  (inferInstance : TopologicalSpace ResidueFamily) =
    TopologicalSpace.induced (fun a : ResidueFamily => a.val)
      (inferInstance : TopologicalSpace Residues)

def FiniteDiscreteCoordinates : Prop :=
  ∀ n : ℕ+, Finite (ZMod (n : ℕ)) ∧ DiscreteTopology (ZMod (n : ℕ))

def ClosedFamilies : Prop := IsClosed (compatibleResidues : Set Residues)
def Compact : Prop := CompactSpace ResidueFamily
def Hausdorff : Prop := T2Space ResidueFamily
def TopologicalAddGroup : Prop := IsTopologicalAddGroup ResidueFamily

def ContinuousProjections : Prop :=
  ∀ n : ℕ+, Continuous (coordinate n)

universe u

/-- The subspace topology detects continuity by all actual residue coordinates. -/
def CoordinateContinuity : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (f : X → ResidueFamily),
    Continuous f ↔ ∀ n : ℕ+, Continuous (fun x => coordinate n (f x))

/-- The universal property of the inverse limit in topological additive groups.
It is stated for arbitrary topological additive groups, not just compact ones.
No separation condition is needed on the test group. -/
def InverseLimit : Prop :=
  ∀ (A : Type u) [AddGroup A] [TopologicalSpace A]
    (f : (n : ℕ+) → ContinuousAddMonoidHom A (ZMod (n : ℕ))),
    (∀ (m n : ℕ+) (h : (m : ℕ) ∣ (n : ℕ)) (x : A),
      reduction m n h (f n x) = f m x) →
    ∃! F : ContinuousAddMonoidHom A ResidueFamily,
      ∀ (n : ℕ+) (x : A), coordinate n (F x) = f n x

end AdvancedFieldTheory.ProfiniteIntegers.ResidueModelSpec
