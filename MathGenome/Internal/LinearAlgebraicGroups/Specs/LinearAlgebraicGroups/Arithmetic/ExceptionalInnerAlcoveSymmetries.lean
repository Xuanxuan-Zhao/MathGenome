import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBuilding

namespace LinearAlgebraicGroups.Specs.ExceptionalInnerAlcoveSymmetries

open ExceptionalAffineBruhat
open ExceptionalAffineBuilding
open ExceptionalAffineRootSystems
open ExceptionalIwahoriImageComparison (MarkedCentralCover)
open IntegralSemisimpleModel (Model integerAlgebra)
open Pinning (BasedRootDatum)
open ValuativeRel
open scoped TensorProduct CategoryTheory.MonObj
attribute [local instance] integerAlgebra

universe u

def e6Highest : Fin 6 → ℤ := ![1, 2, 2, 3, 2, 1]
def e7Highest : Fin 7 → ℤ := ![2, 2, 3, 4, 3, 2, 1]

def e6Rotate : Equiv.Perm (Fin 7) :=
  { toFun := ![1, 6, 3, 5, 4, 2, 0]
    invFun := ![6, 0, 5, 2, 4, 3, 1]
    left_inv := by decide
    right_inv := by decide }

def e7Reverse : Equiv.Perm (Fin 8) :=
  { toFun := ![7, 6, 2, 5, 4, 3, 1, 0]
    invFun := ![7, 6, 2, 5, 4, 3, 1, 0]
    left_inv := by decide
    right_inv := by decide }

/-- The linear parts of the normalized affine wall values in Bourbaki coordinates. -/
def directionalValues {n : ℕ} (highest : Fin n → ℤ) (r : Fin n → ℚ) : Fin (n + 1) → ℚ :=
  Fin.cases (-∑ i, (highest i : ℚ) * r i) r

def invariantDirections {n : ℕ} (highest : Fin n → ℤ) (σ : Equiv.Perm (Fin (n + 1))) :
    Submodule ℚ (Fin n → ℚ) where
  carrier := {r | ∀ i, directionalValues highest r (σ i) = directionalValues highest r i}
  zero_mem' := by
    have h (i : Fin (n + 1)) : directionalValues highest 0 i = 0 :=
      Fin.cases (by simp [directionalValues]) (fun _ => rfl) i
    intro i
    rw [h, h]
  add_mem' := by
    intro x y hx hy i
    have h (j : Fin (n + 1)) :
        directionalValues highest (x + y) j =
          directionalValues highest x j + directionalValues highest y j := by
      refine Fin.cases ?_ (fun _ => rfl) j
      simp [directionalValues, mul_add, Finset.sum_add_distrib, add_comm]
    rw [h, h, hx i, hy i]
  smul_mem' := by
    intro c x hx i
    have h (j : Fin (n + 1)) :
        directionalValues highest (c • x) j = c * directionalValues highest x j := by
      refine Fin.cases ?_ (fun _ => rfl) j
      simp only [directionalValues, Fin.cases_zero, Pi.smul_apply, smul_eq_mul, mul_neg]
      rw [Finset.mul_sum]
      simp only [mul_left_comm]
    rw [h, h, hx i]

def fixedDirections {V : Type*} [AddCommGroup V] [Module ℚ V]
    (g : V ≃ₗ[ℚ] V) : Submodule ℚ V :=
  LinearMap.ker (g.toLinearMap - LinearMap.id)

def MarkedAlcoveSymmetriesFor (n rank : ℕ) (highest : Fin n → ℤ)
    (perms : Set (Equiv.Perm (Fin (n + 1)))) : Prop :=
  ∀ (F K : Type u) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension F K],
    IsUnramifiedLocalExtension F K →
    ∀ {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
      (c : MarkedCentralCover M M')
      (b : Fin n ≃ D.base.support) (b' : Fin n ≃ E.base.support),
      ExceptionalNumbering D n b → ExceptionalNumbering E n b' →
      D.datum.corootSpan ℤ = ⊤ → E.datum.rootSpan ℤ = ⊤ →
      ∀ {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
        {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
        (Y : SplitLevel K c p p' e) (_B : SplitBuildingLevel Y),
        let A := ApartmentRoots.split E.datum ℚ
        (∀ i, E.base.IsPos i → 0 < A.root i p' ∧ A.root i p' < 1) →
        ∃ (l : Fin (n + 1) ≃ A.SimpleWall p')
          (coordinates : (ℚ ⊗[ℤ] E.Y) ≃ₗ[ℚ] (Fin n → ℚ)),
          coordinates.toLinearMap = simpleRootValues E.datum E.base b' ℚ ∧
          (∀ x, x ∈ A.coweightLattice ↔
            ∃ m : Fin n → ℤ, coordinates x = fun j => (m j : ℚ)) ∧
          coordinates '' (A.corootLattice : Set _) =
            Set.range (fun m : Fin n → ℤ => fun j => ((exceptionalCartan n).mulVec m j : ℚ)) ∧
          (∀ i x, A.wallValue (l i).val x =
            Fin.cases (1 - ∑ j, (highest j : ℚ) * coordinates x j) (coordinates x) i) ∧
          ∀ t : Y.ad.N, (t : FieldPoints M' K) ∈ lengthZeroNormalizer Y.ad →
            typeChange Y.typeQuotient t ≠ 1 →
            let g := Y.ad.affine t
            let ω := typeChange Y.typeQuotient t
            let w := Y.ad.localIwahori.normalizer.label t
            g = ω.val.val ∧
            g.linear = w.val.coweightEquiv.symm.baseChange ℤ ℚ E.Y E.Y ∧
            ∃ σ ∈ perms,
              (∀ i, Y.typeQuotient.wallPerm ω (l i) = l (σ i)) ∧
              (∀ i x, A.wallValue (l (σ i)).val (g x) = A.wallValue (l i).val x) ∧
              (fixedDirections g.linear).map coordinates.toLinearMap =
                invariantDirections highest σ ∧
              Module.finrank ℚ (fixedDirections g.linear) = rank

/-- The two nontrivial inner actions on the marked split exceptional apartments. -/
def MarkedAlcoveSymmetries : Prop :=
  MarkedAlcoveSymmetriesFor.{u} 6 2 e6Highest {e6Rotate, e6Rotate.symm} ∧
  MarkedAlcoveSymmetriesFor.{u} 7 4 e7Highest {e7Reverse}

end LinearAlgebraicGroups.Specs.ExceptionalInnerAlcoveSymmetries
