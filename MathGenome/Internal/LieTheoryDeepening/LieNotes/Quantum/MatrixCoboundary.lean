import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.MatrixCoboundary
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.Cobracket
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Coboundary.Cocycle
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases

noncomputable section

open private matrixBasis matrixBasis_apply from MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.MatrixSpecialization

namespace LieNotes.Quantum.MatrixCoboundary

open Specs.LieNotes.Quantum.MatrixCoboundary (RestrictionCoboundaryProp MatrixCoboundaryProp)
open Specs.LieNotes.Quantum.MatrixSpecialization
  (Sl3 matrixE matrixF matrixH matrixUnit)
open Specs.LieNotes.Quantum.Presentation (Root)
open LieNotes.Coboundary

universe u

/-- The standard bivector for the skew sign of UQ08. -/
def standardTensor (k : Type u) [Field k] : ⋀[k]^2 (Sl3 k) :=
  Specs.LieNotes.Quantum.MatrixCoboundary.standardTensor k

section Matrices

variable {k : Type u} [Field k]

local notation "E" => matrixE k
local notation "F" => matrixF k
local notation "H" => matrixH k
local notation "P" => matrixUnit k 0 2 (by decide)
local notation "N" => matrixUnit k 2 0 (by decide)

-- Reduce products of elementary matrices using their middle indices.
local macro "matrix_bracket" : tactic =>
  `(tactic| (
    apply Subtype.ext
    simp (disch := decide) only [LieAlgebra.SpecialLinear.sl_bracket,
      matrixE, matrixF, matrixH, matrixUnit, LieAlgebra.SpecialLinear.val_single,
      LieAlgebra.SpecialLinear.val_singleSubSingle, Fin.castSucc_zero, Fin.castSucc_one,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.single_mul_single_same,
      Matrix.single_mul_single_of_ne, sub_mul, mul_sub, one_mul, zero_sub, sub_zero,
      sub_self, neg_neg, NegMemClass.coe_neg, ZeroMemClass.coe_zero]))

private theorem longRootBrackets :
    (⁅E 0, P⁆ = 0 ∧ ⁅E 0, N⁆ = -F 1) ∧
    (⁅E 1, P⁆ = 0 ∧ ⁅E 1, N⁆ = F 0) ∧
    (⁅F 0, P⁆ = E 1 ∧ ⁅F 0, N⁆ = 0) ∧
    (⁅F 1, P⁆ = -E 0 ∧ ⁅F 1, N⁆ = 0) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> matrix_bracket

private theorem cartanLongBrackets (i : Root) : ⁅H i, P⁆ = P ∧ ⁅H i, N⁆ = -N := by
  revert i
  rw [Fin.forall_fin_two]
  exact ⟨⟨by matrix_bracket, by matrix_bracket⟩, ⟨by matrix_bracket, by matrix_bracket⟩⟩

private theorem standardTensor_action (x : Sl3 k) :
    coboundary (standardTensor k) x =
      -(wedge₂ ⁅x, E 0⁆ (F 0) + wedge₂ (E 0) ⁅x, F 0⁆) -
      (wedge₂ ⁅x, E 1⁆ (F 1) + wedge₂ (E 1) ⁅x, F 1⁆) -
      (wedge₂ ⁅x, P⁆ N + wedge₂ P ⁅x, N⁆) := by
  change exteriorAdjoint 2 x
    (-wedge₂ (E 0) (F 0) - wedge₂ (E 1) (F 1) - wedge₂ P N) = _
  simp only [map_sub, map_neg, exteriorAdjoint_wedge₂]

private theorem cartan_action [CharZero k] (i : Root) :
    coboundary (standardTensor k) (H i) = 0 := by
  obtain ⟨h, _, _⟩ := MatrixSpecialization.matrix_relations k
  obtain ⟨hp, hn⟩ := cartanLongBrackets (k := k) i
  simp only [standardTensor_action, h.cartanE, h.cartanF, hp, hn,
    map_smul, LinearMap.smul_apply, neg_smul, map_neg]
  abel

private theorem positive_action [CharZero k] (i : Root) :
    coboundary (standardTensor k) (E i) = wedge₂ (H i) (E i) := by
  obtain ⟨h, he, _⟩ := MatrixSpecialization.matrix_relations k
  have he' : ⁅E 1, E 0⁆ = -P := by rw [← lie_skew (E 1) (E 0), he]
  obtain ⟨⟨h₀p, h₀n⟩, ⟨h₁p, h₁n⟩, _, _⟩ := longRootBrackets (k := k)
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · rw [standardTensor_action]
    simp [h.mixed, he, h₀p, h₀n, wedge₂_swap (H 0) (E 0)]
  · rw [standardTensor_action]
    simp [h.mixed, he', h₁p, h₁n, wedge₂_swap (H 1) (E 1)]

private theorem negative_action [CharZero k] (i : Root) :
    coboundary (standardTensor k) (F i) = wedge₂ (H i) (F i) := by
  obtain ⟨h, _, hf⟩ := MatrixSpecialization.matrix_relations k
  have hf' : ⁅F 1, F 0⁆ = N := by rw [← lie_skew (F 1) (F 0), hf, neg_neg]
  have hm (i j : Root) : ⁅F i, E j⁆ = -(if j = i then H j else 0) := by
    rw [← lie_skew (F i) (E j), h.mixed]
  obtain ⟨_, _, ⟨h₀p, h₀n⟩, ⟨h₁p, h₁n⟩⟩ := longRootBrackets (k := k)
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · rw [standardTensor_action]
    simp [hm, hf, h₀p, h₀n]
  · rw [standardTensor_action]
    simp [hm, hf', h₁p, h₁n]

end Matrices

/-- The actual first-order restriction agrees with the coboundary on all of `sl₃`. -/
theorem restriction_eq_coboundary : RestrictionCoboundaryProp.{u} := by
  intro k _ _ D r b q
  let δr := coboundary (standardTensor k)
  change q.delta = δr
  have hH (i : Root) : q.delta (matrixH k i) = δr (matrixH k i) :=
    (q.values.cartan i).trans (cartan_action i).symm
  have hE (i : Root) : q.delta (matrixE k i) = δr (matrixE k i) :=
    (q.values.simplePositive i).trans (positive_action i).symm
  have hF (i : Root) : q.delta (matrixF k i) = δr (matrixF k i) :=
    (q.values.simpleNegative i).trans (negative_action i).symm
  have hc : isCobracketCocycle δr := coboundary_isCocycle (standardTensor k)
  have hδ : isCobracketCocycle q.delta := q.cocycle
  have agree_bracket (x y : Sl3 k) (hx : q.delta x = δr x) (hy : q.delta y = δr y) :
      q.delta ⁅x, y⁆ = δr ⁅x, y⁆ :=
    (hδ x y).trans (by rw [hx, hy, ← hc x y])
  obtain ⟨_, he, hf⟩ := MatrixSpecialization.matrix_relations k
  have hP : q.delta (matrixUnit k 0 2 (by decide)) = δr (matrixUnit k 0 2 (by decide)) := by
    simpa only [he] using agree_bracket (matrixE k 0) (matrixE k 1) (hE 0) (hE 1)
  have hN : q.delta (-matrixUnit k 2 0 (by decide)) = δr (-matrixUnit k 2 0 (by decide)) := by
    simpa only [hf] using agree_bracket (matrixF k 0) (matrixF k 1) (hF 0) (hF 1)
  apply (matrixBasis (k := k)).ext
  intro j
  rw [matrixBasis_apply]
  fin_cases j
  exacts [hF 0, hN, hF 1, hH 0, hH 1, hE 0, hP, hE 1]

/-- UQ09 for the constructed Lie bialgebra cobracket and its divided-skew values. -/
theorem cobracket_is_coboundary : MatrixCoboundaryProp.{u} := by
  intro k _ _
  obtain ⟨d, s, D, hp, hh, ht, r, b, q, hLie, _, hLift⟩ := Cobracket.cobracket k
  have hq := restriction_eq_coboundary k q
  refine ⟨d, s, D, hp, hh, ht, r, b, q, hq, hLie, ?_⟩
  intro x X hX
  simpa only [← hq] using hLift x X hX

end LieNotes.Quantum.MatrixCoboundary
