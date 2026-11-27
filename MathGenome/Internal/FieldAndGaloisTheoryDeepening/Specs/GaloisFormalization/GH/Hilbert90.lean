import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.Cochains
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.KrullLayers
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.NonabelianH1
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

namespace GaloisFormalization.GH.Hilbert90

open Matrix

/-- The Galois action on invertible matrices applies each automorphism entrywise. -/
scoped instance matrixAction {k L : Type*} [Field k] [Field L] [Algebra k L]
    (n : ℕ) : MulDistribMulAction Gal(L/k) (GeneralLinearGroup (Fin n) L) where
  smul g := GeneralLinearGroup.map g.toRingEquiv.toRingHom
  one_smul A := by
    apply GeneralLinearGroup.ext
    intro i j
    rfl
  mul_smul g h A := by
    apply GeneralLinearGroup.ext
    intro i j
    rfl
  smul_mul g := map_mul (GeneralLinearGroup.map g.toRingEquiv.toRingHom)
  smul_one g := map_one (GeneralLinearGroup.map g.toRingEquiv.toRingHom)

end GaloisFormalization.GH.Hilbert90

namespace Specs.GaloisFormalization.GH.Hilbert90

open Matrix
open _root_.GaloisFormalization.GH
open scoped _root_.GaloisFormalization.GH.Hilbert90

universe u v

/-- Every continuous matrix cocycle is the change of the identity by an invertible matrix. -/
def MatrixCoboundary : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L] [IsGalois k L]
    (n : ℕ), 1 ≤ n →
    ∀ [TopologicalSpace (GeneralLinearGroup (Fin n) L)]
      [DiscreteTopology (GeneralLinearGroup (Fin n) L)]
      (c : NonabelianH1.Spec.Cocycle Gal(L/k) (GeneralLinearGroup (Fin n) L)),
      ∃ b : GeneralLinearGroup (Fin n) L, ∀ g : Gal(L/k),
        c g = b⁻¹ * GeneralLinearGroup.map g.toRingEquiv.toRingHom b

/-- Matrix Hilbert 90 for the pointed continuous cohomology set. -/
def MatrixVanishing : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L] [IsGalois k L]
    (n : ℕ), 1 ≤ n →
    ∀ [TopologicalSpace (GeneralLinearGroup (Fin n) L)]
      [DiscreteTopology (GeneralLinearGroup (Fin n) L)],
      Subsingleton (NonabelianH1.Spec.H1 Gal(L/k) (GeneralLinearGroup (Fin n) L))

/-- A continuous unit-valued cocycle has a witness in the units of the extension. -/
def UnitsCoboundary : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L] [IsGalois k L]
    [TopologicalSpace Lˣ] [DiscreteTopology Lˣ]
    (c : NonabelianH1.Spec.Cocycle Gal(L/k) Lˣ),
    ∃ b : Lˣ, ∀ g : Gal(L/k), c g = b⁻¹ * (g • b)

/-- Multiplicative Hilbert 90 in the abelian continuous cohomology group. -/
def UnitsVanishing : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L] [IsGalois k L]
    [TopologicalSpace Lˣ] [DiscreteTopology Lˣ],
    letI : ContinuousSMul Gal(L/k) Lˣ :=
      continuousSMul_iff_stabilizer_isOpen.mpr fun a => by
        convert stabilizer_isOpen_of_isIntegral (K := k) (a : L) using 1
        ext g
        change g • a = a ↔ g (a : L) = (a : L)
        exact ⟨congrArg Units.val, fun h => by
          apply Units.ext
          exact h⟩
    Subsingleton (Model.ContinuousMulH Gal(L/k) Lˣ 1)

end Specs.GaloisFormalization.GH.Hilbert90
