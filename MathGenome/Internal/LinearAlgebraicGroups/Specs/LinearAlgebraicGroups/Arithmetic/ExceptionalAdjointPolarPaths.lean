import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.PolarRealStructures
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SolvableRadical
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.UnitInterval

namespace Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAdjointPolarPaths

open LieAlgebrasAndRepresentations.RealForms
open Specs.LieAlgebrasAndRepresentations.PolarRealStructures

universe u v

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

/-- Complex linear bracket automorphisms, with composition as multiplication. -/
def bracketAutomorphisms (L : Type u) [LieRing L] [LieAlgebra ℂ L] :
    Subgroup (L ≃ₗ[ℂ] L) where
  carrier := {g | ∀ x y, g ⁅x, y⁆ = ⁅g x, g y⁆}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro g h hg hh x y
    change g (h ⁅x, y⁆) = ⁅g (h x), g (h y)⁆
    rw [hh, hg]
  inv_mem' := by
    intro g hg x y
    change g.symm ⁅x, y⁆ = ⁅g.symm x, g.symm y⁆
    apply g.injective
    rw [hg, g.apply_symm_apply, g.apply_symm_apply, g.apply_symm_apply]

abbrev LieAut (L : Type u) [LieRing L] [LieAlgebra ℂ L] := bracketAutomorphisms L

def toLieEquiv (g : LieAut L) : L ≃ₗ⁅ℂ⁆ L :=
  { g.val with map_lie' := g.property _ _ }

def ofLieEquiv (g : L ≃ₗ⁅ℂ⁆ L) : LieAut L :=
  ⟨g.toLinearEquiv, g.map_lie⟩

@[simp] theorem toLieEquiv_apply (g : LieAut L) (x : L) : toLieEquiv g x = g.val x := rfl
@[simp] theorem ofLieEquiv_apply (g : L ≃ₗ⁅ℂ⁆ L) (x : L) :
    (ofLieEquiv g).val x = g x := rfl

def compactAction (ω : Conjugation L) (g : LieAut L) : LieAut L :=
  ⟨{
    toFun := fun x => ω.map (g.val (ω.map x))
    invFun := fun x => ω.map (g.val.symm (ω.map x))
    map_add' := by simp
    map_smul' := by simp [ω.antilinear, map_smul]
    left_inv := fun x => by
      change ω.map (g.val.symm (ω.map (ω.map (g.val (ω.map x))))) = x
      rw [ω.involutive, LinearEquiv.symm_apply_apply, ω.involutive]
    right_inv := fun x => by
      change ω.map (g.val (ω.map (ω.map (g.val.symm (ω.map x))))) = x
      rw [ω.involutive, LinearEquiv.apply_symm_apply, ω.involutive]
  }, fun x y => by
    change ω.map (g.val (ω.map ⁅x, y⁆)) = ⁅ω.map (g.val (ω.map x)), ω.map (g.val (ω.map y))⁆
    rw [ω.map.map_lie, g.property, ω.map.map_lie]⟩

def holomorphicAction (θ g : LieAut L) : LieAut L := θ * g * θ⁻¹

/-- The Killing-form adjoint of a bracket automorphism. -/
def adjoint (ω : Conjugation L) (g : LieAut L) : LieAut L := compactAction ω g⁻¹

/-- Unitarity for the positive Hermitian form defined by compact conjugation. -/
def IsUnitary (ω : Conjugation L) (g : LieAut L) : Prop :=
  ∀ x y, hermitian ω (g.val x) (g.val y) = hermitian ω x y

noncomputable def matrixOf {ι : Type v} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ L) (g : LieAut L) : Matrix ι ι ℂ :=
  LinearMap.toMatrix b b g.val.toLinearMap

/-- The subspace topology of the finite matrix entries in the supplied basis. -/
@[instance_reducible] noncomputable def matrixTopology {ι : Type v} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ L) : TopologicalSpace (LieAut L) :=
  TopologicalSpace.induced (matrixOf b) inferInstance

theorem compactAction_mul (ω : Conjugation L) (g h : LieAut L) :
    compactAction ω (g * h) = compactAction ω g * compactAction ω h := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change ω.map (g.val (h.val (ω.map x))) = ω.map (g.val (ω.map (ω.map (h.val (ω.map x)))))
  rw [ω.involutive]

theorem compactAction_inv (ω : Conjugation L) (g : LieAut L) :
    compactAction ω g⁻¹ = (compactAction ω g)⁻¹ := rfl

/-- The compact fixed subgroup of the given group of bracket automorphisms. -/
def compactFixed (ω : Conjugation L) (A : Subgroup (LieAut L)) : Subgroup A where
  carrier := {g | compactAction ω g.val = g.val}
  one_mem' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    exact ω.involutive
  mul_mem' := by
    intro g h hg hh
    change compactAction ω (g.val * h.val) = g.val * h.val
    rw [compactAction_mul, hg, hh]
  inv_mem' := by
    intro g hg
    change compactAction ω g.val⁻¹ = g.val⁻¹
    rw [compactAction_inv, hg]

/-- Spectral characterization of the positive real power of the adjoint product. -/
def IsAdjointPower (ω : Conjugation L) (g : LieAut L) (t : ℝ) (p : LieAut L) : Prop :=
  ∀ (r : ℝ) (x : L), (adjoint ω g * g).val x = (r : ℂ) • x →
    p.val x = ((r ^ t : ℝ) : ℂ) • x

def polarDeformationStatement : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    {ι : Type v} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ L),
    Specs.LieAlgebrasAndRepresentations.SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (ω : Conjugation L), IsCompact ω →
    ∀ (θ : LieAut L), Function.Involutive θ.val →
      (∀ x, θ.val (ω.map x) = ω.map (θ.val x)) →
    letI : TopologicalSpace (LieAut L) := matrixTopology b
    ∀ (A : Subgroup (LieAut L)), IsClosed (A : Set (LieAut L)) →
      connectedComponent (1 : LieAut L) ⊆ (A : Set (LieAut L)) →
      (∀ g ∈ A, compactAction ω g ∈ A) →
      (∀ g ∈ A, holomorphicAction θ g ∈ A) →
      ∃ H : C(unitInterval × A, A),
        (∀ x y : L, star (hermitian ω y x) = hermitian ω x y) ∧
        (∀ x : L, x ≠ 0 → 0 < (hermitian ω x x).re) ∧
        (∀ g : LieAut L, ∀ x y,
          hermitian ω (g.val x) y = hermitian ω x ((adjoint ω g).val y)) ∧
        (∀ (s : unitInterval) (g : A), ∃! p : LieAut L,
          IsAdjointPower ω g.val (-(s : ℝ) / 2) p ∧ (H (s, g)).val = g.val * p) ∧
        (∀ g, H (0, g) = g) ∧
        (∀ g, H (1, g) ∈ compactFixed ω A) ∧
        (∀ s g, g ∈ compactFixed ω A → H (s, g) = g) ∧
        (∀ s (g k : A), k.val = compactAction ω g.val →
          (H (s, k)).val = compactAction ω (H (s, g)).val) ∧
        (∀ s (g k : A), k.val = holomorphicAction θ g.val →
          (H (s, k)).val = holomorphicAction θ (H (s, g)).val) ∧
        Set.range (fun g => H (1, g)) = (compactFixed ω A : Set A) ∧
        (∀ g : A, g ∈ compactFixed ω A ↔ IsUnitary ω g.val) ∧
        IsCompact (compactFixed ω A : Set A)

end Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAdjointPolarPaths
