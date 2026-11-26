import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.DatumAndWeyl
import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Lattice.Nat

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.SimpleRoots

open AbstractPairing (Datum Root)
open CharacterDescent (Character Cocharacter)
open CharacterPairing (pairing)
open GeometricRadicals (IsReductive IsSplitTorus)
open RankOneFlag (IsGeometricallyMaximal)

section RootPairing

variable {Idx X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing Idx ℤ X Y)

/-- The actual root indices on the positive side of the chosen functional. -/
def positive (f : X →ₗ[ℤ] ℤ) : Set Idx := {i | 0 < f (P.root i)}

/-- A word in the reflections of the specified base, evaluated in the Weyl group. -/
noncomputable def wordProduct (b : P.Base) (l : List b.support) : P.weylGroup :=
  (l.map fun i ↦ RootPairing.weylGroup.ofIdx P i.val).prod

/-- Minimal length of a word in the specified simple reflections. -/
noncomputable def wordLength (b : P.Base) (w : P.weylGroup) : ℕ :=
  sInf {n | ∃ l : List b.support, l.length = n ∧ wordProduct P b l = w}

/-- The roots in `Φ⁺ ∩ wΦ⁻`, using the action on the actual root indices. -/
def inversions (f : X →ₗ[ℤ] ℤ) (w : P.weylGroup) : Set Idx :=
  {i | 0 < f (P.root i) ∧ f (P.root (P.weylGroupToPerm w⁻¹ i)) < 0}

/-- A root hyperplane in the real cocharacter space, viewed by evaluation
on the character lattice. -/
def hyperplane (i : Idx) : Set (X →ₗ[ℤ] ℝ) := {x | x (P.root i) = 0}

/-- Hyperplanes on whose opposite open sides the two regular points lie. -/
def separatingHyperplanes (x y : X →ₗ[ℤ] ℝ) : Set (Set (X →ₗ[ℤ] ℝ)) :=
  {H | ∃ i, H = hyperplane P i ∧ x (P.root i) * y (P.root i) < 0}

/-- The open chamber given by the positive roots of the fixed regular functional. -/
def chamber (f : X →ₗ[ℤ] ℤ) : Set (X →ₗ[ℤ] ℝ) :=
  {x | ∀ i ∈ positive P f, 0 < x (P.root i)}

/-- The closed chamber, described by weak root inequalities. -/
def closedChamber (f : X →ₗ[ℤ] ℤ) : Set (X →ₗ[ℤ] ℝ) :=
  {x | ∀ i ∈ positive P f, 0 ≤ x (P.root i)}

/-- For a positive root, the part of its hyperplane in the chamber boundary
that lies on no distinct root hyperplane. -/
def wallInterior (f : X →ₗ[ℤ] ℤ) (i : Idx) : Set (X →ₗ[ℤ] ℝ) :=
  {x | x (P.root i) = 0 ∧ ∀ j ∈ positive P f, j ≠ i → 0 < x (P.root j)}

/-- Extension of an integral character-lattice functional to real values. -/
def realFunctional (f : X →ₗ[ℤ] ℤ) : X →ₗ[ℤ] ℝ :=
  (Int.castRingHom ℝ).toAddMonoidHom.toIntLinearMap.comp f

/-- The given positive system determines the base, its faces and its
simple-reflection length function. -/
structure IsBaseFor (f : X →ₗ[ℤ] ℤ) (b : P.Base) : Prop where
  simple_iff (i : Idx) : i ∈ b.support ↔
    i ∈ positive P f ∧ ∀ j ∈ positive P f, ∀ l ∈ positive P f,
      P.root i ≠ P.root j + P.root l
  positive_iff (i : Idx) : b.IsPos i ↔ i ∈ positive P f
  independent :
    LinearIndependent ℚ (fun i : b.support ↦ (1 : ℚ) ⊗ₜ[ℤ] P.root i.val)
  integral_coordinates (i : Idx) : ∃ c : Idx → ℤ,
    Function.support c ⊆ b.support ∧
    ((∀ j, 0 ≤ c j) ∨ (∀ j, c j ≤ 0)) ∧
    P.root i = ∑ j ∈ b.support, c j • P.root j
  span_iff (I : Set Idx) (_hI : I ⊆ b.support) (i : Idx) :
    (1 : ℚ) ⊗ₜ[ℤ] P.root i ∈
      Submodule.span ℚ ((fun j ↦ (1 : ℚ) ⊗ₜ[ℤ] P.root j) '' I) ↔
    P.root i ∈ Submodule.span ℤ (P.root '' I)
  chamber_eq : chamber P f = {x | ∀ i ∈ b.support, 0 < x (P.root i)}
  closedChamber_eq : closedChamber P f = {x | ∀ i ∈ b.support, 0 ≤ x (P.root i)}
  wall_iff (i : Idx) (_hi : i ∈ positive P f) :
    i ∈ b.support ↔ (wallInterior P f i).Nonempty
  integralWall (i : Idx) (_hi : i ∈ b.support) :
    ∃ g : X →ₗ[ℤ] ℤ, realFunctional g ∈ wallInterior P f i
  orbit (i : Idx) : ∃ (w : P.weylGroup) (j : b.support), P.weylGroupToPerm w j.val = i
  generates : Subgroup.closure (Set.range (fun i : b.support ↦
    RootPairing.weylGroup.ofIdx P i.val)) = ⊤
  inversions_eq (w : P.weylGroup) :
    inversions P f w = positive P f ∩
      (P.weylGroupToPerm w '' {i | f (P.root i) < 0})
  length_eq (w : P.weylGroup) :
    wordLength P b w = (inversions P f w).ncard
  separating_eq (w : P.weylGroup) :
    (separatingHyperplanes P (realFunctional f)
      ((realFunctional f).comp (w⁻¹).val.weightEquiv.toLinearMap)).ncard =
      (inversions P f w).ncard

end RootPairing

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

/-- Evaluation at an actual cocharacter of the split torus. -/
noncomputable def evaluate {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X] (D : Datum T)
    (cochar : Cocharacter T.group) : Additive (Character T.group) →ₗ[ℤ] ℤ :=
  D.rootDatum.toLinearMap.flip (Additive.ofMul cochar)

/-- Simple roots and word length for every regular positive system of a split
connected reductive pair, using the Weyl group identified with the scheme quotient. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ T : ClosedSubgroup G.val, IsSplitTorus T.group → IsGeometricallyMaximal T →
      ∃ h : IsCommMonObj T.group.X, letI := h
        ∃ (D : Datum T) (e : DatumAndWeyl.Identification D),
          ∀ cochar : Cocharacter T.group, (∀ i : Root T, pairing T.group i.val cochar ≠ 0) →
            ∃ b : D.rootDatum.Base, IsBaseFor D.rootDatum (evaluate D cochar) b ∧
              (∀ i ∈ b.support, ∃ wallCochar : Cocharacter T.group,
                realFunctional (evaluate D wallCochar) ∈
                  wallInterior D.rootDatum (evaluate D cochar) i) ∧
              ∀ w : D.rootDatum.weylGroup,
                wordLength D.rootDatum b w =
                  (separatingHyperplanes D.rootDatum (realFunctional (evaluate D cochar))
                    (realFunctional (evaluate D
                      (cochar ≫ (e.image.conjugation (e.labelEquiv w)).hom)))).ncard

end LinearAlgebraicGroups.Specs.SimpleRoots
