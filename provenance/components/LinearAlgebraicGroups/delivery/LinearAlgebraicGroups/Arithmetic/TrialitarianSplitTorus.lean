import Specs.LinearAlgebraicGroups.Arithmetic.TrialitarianSplitTorus
import LinearAlgebraicGroups.Albert.AutomorphismType
import LinearAlgebraicGroups.Reductive.MaximalToriExist
import LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
import LinearAlgebraicGroups.Albert.ShortDirections
import LinearAlgebraicGroups.Affine.GroupSchemes
import LinearAlgebraicGroups.Affine.LieBracket
import LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
import LinearAlgebraicGroups.Reductive.CocharacterLieWeights
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.RingTheory.Smooth.Local
import Mathlib.Data.List.Sort
import Batteries.Tactic.OpenPrivate
import LinearAlgebraicGroups.Albert.FrameTangentRank
import LinearAlgebraicGroups.Albert.IntegralSmoothness
import LinearAlgebraicGroups.Affine.ClosedSubgroups
import LinearAlgebraicGroups.Affine.LieLeftExact
import LinearAlgebraicGroups.Flag.OpenCell
import LinearAlgebraicGroups.RootData.BorelsAndChambers
import LinearAlgebraicGroups.Reductive.WeylScheme
import LinearAlgebraicGroups.Classification.RationalRealization
import LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
import LinearAlgebraicGroups.Reductive.CocharacterOpenCell
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
import LinearAlgebraicGroups.Albert.SmoothIdentityCriterion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import LinearAlgebraicGroups.Reductive.CocharacterSmoothAndUnipotent

namespace LinearAlgebraicGroups.Arithmetic.TrialitarianSplitTorus

open scoped BigOperators
open Matrix

universe u

private abbrev Coord := Fin 27
private abbrev Slot := Fin 3

/-- Row-major coordinates on the three matrix blocks, in the order A, B, D. -/
private def coord (block i j : Slot) : Coord :=
  ⟨block.val * 9 + i.val * 3 + j.val, by omega⟩

private abbrev a := coord 0
private abbrev b := coord 1
private abbrev d := coord 2

/-- Coordinates of the action by the elementary matrix I + t Eᵢⱼ, i ≠ j. -/
private def elementaryAction {R : Type*} [CommRing R]
    (i j : Slot) (t : R) (v : Coord → R) : Coord → R := fun z =>
  let r : Slot := ⟨z.val / 3 % 3, by omega⟩
  let s : Slot := ⟨z.val % 3, by omega⟩
  match z.val / 9 with
  | 0 => v z + (if r = i then t * v (a j s) else 0)
      - (if s = j then t * v (a r i) else 0)
      - (if r = i ∧ s = j then t ^ 2 * v (a j i) else 0)
  | 1 => v z + (if r = i then t * v (b j s) else 0)
  | _ => v z - (if s = j then t * v (d r i) else 0)

/-- The sign of eᵢ × eⱼ in coordinate k. -/
private def crossEntry {R : Type*} [CommRing R] (i j k : Slot) : R :=
  if i = j ∨ i = k ∨ j = k then 0 else if j = i + 1 then 1 else -1

/-- Simultaneous application of the Zorn transvection pᵢ(t) to all three
Peirce blocks, with the sign of D inherited from its lower coordinates. -/
private def zornAction {R : Type*} [CommRing R]
    (i : Slot) (t : R) (v : Coord → R) : Coord → R := fun z =>
  let r : Slot := ⟨z.val / 3 % 3, by omega⟩
  let s : Slot := ⟨z.val % 3, by omega⟩
  match z.val / 9 with
  | 0 => v z + if r = s then 0
      else if r = s + 1 then t * v (d i (r + 1)) else -(t * v (d i (s + 1)))
  | 1 => v z + if s = i then
      t * (v (a (r + 2) (r + 1)) - v (a (r + 1) (r + 2))) + t ^ 2 * v (d i r)
      else 0
  | _ => v z - t * (((crossEntry i 0 r * v (b s 0) +
      crossEntry i 1 r * v (b s 1)) + crossEntry i 2 r * v (b s 2)))

private inductive FrameMove where
  | elementary (i j : Slot) (distinct : i ≠ j) (parameter : ℤ)
  | zorn (i : Slot) (parameter : ℤ)

private def frameMoves : List FrameMove :=
  [.elementary 0 2 (by decide) 1, .elementary 1 0 (by decide) 1,
   .elementary 2 0 (by decide) (-1), .elementary 0 1 (by decide) (-1),
   .elementary 1 0 (by decide) 1, .zorn 0 1,
   .elementary 1 0 (by decide) (-1), .zorn 1 1, .zorn 2 (-1),
   .elementary 2 0 (by decide) 1]

private def FrameMove.apply {R : Type*} [CommRing R] (v : Coord → R) :
    FrameMove → Coord → R
  | .elementary i j _ t => elementaryAction i j (t : R) v
  | .zorn i t => zornAction i (t : R) v

private def movedFrame {R : Type*} [CommRing R] (l : Slot) : Coord → R :=
  frameMoves.foldl FrameMove.apply (fun z => if z = a l l then 1 else 0)

private abbrev Entries := List (Coord × Coord × ℤ)

/-- The positive-weight solutions in lexicographic weight order, then the
four diagonal solutions in free-column order. Each triple is (row, column,
entry) and zero entries are omitted. -/
private def tangentEntries : Array Entries := #[
  [(9, 10, -1), (12, 13, -1), (15, 16, -1), (21, 18, 1), (22, 19, 1), (23, 20, 1)],
  [(10, 11, -1), (13, 14, -1), (16, 17, -1), (24, 21, 1), (25, 22, 1), (26, 23, 1)],
  [(9, 11, -1), (12, 14, -1), (15, 17, -1), (24, 18, 1), (25, 19, 1), (26, 20, 1)],
  [(0, 25, -1), (3, 24, 1), (5, 26, -1), (8, 25, 1), (11, 1, -1), (14, 0, 1), (14, 8, -1), (17, 7, 1), (18, 16, -1), (20, 10, -1), (21, 15, 1), (23, 9, 1)],
  [(0, 22, 1), (3, 21, -1), (5, 23, 1), (8, 22, -1), (10, 1, 1), (13, 0, -1), (13, 8, 1), (16, 7, -1), (18, 17, -1), (20, 11, -1), (24, 15, 1), (26, 9, 1)],
  [(0, 19, -1), (3, 18, 1), (5, 20, -1), (8, 19, 1), (9, 1, -1), (12, 0, 1), (12, 8, -1), (15, 7, 1), (21, 17, -1), (23, 11, -1), (24, 16, 1), (26, 10, 1)],
  [(3, 15, -1), (5, 9, 1), (13, 25, 1), (14, 22, -1), (18, 7, -1), (20, 1, 1)],
  [(3, 16, -1), (5, 10, 1), (12, 25, -1), (14, 19, 1), (21, 7, -1), (23, 1, 1)],
  [(3, 17, -1), (5, 11, 1), (12, 22, 1), (13, 19, -1), (24, 7, -1), (26, 1, 1)],
  [(0, 3, -1), (1, 0, 1), (1, 4, -1), (2, 5, -1), (4, 3, 1), (7, 6, 1), (9, 12, -1), (10, 13, -1), (11, 14, -1), (19, 18, 1), (22, 21, 1), (25, 24, 1)],
  [(1, 25, -1), (2, 26, 1), (4, 24, 1), (8, 24, -1), (11, 4, -1), (11, 8, 1), (14, 3, 1), (17, 6, -1), (19, 16, -1), (20, 13, -1), (22, 15, 1), (23, 12, 1)],
  [(1, 22, 1), (2, 23, -1), (4, 21, -1), (8, 21, 1), (10, 4, 1), (10, 8, -1), (13, 3, -1), (16, 6, 1), (19, 17, -1), (20, 14, -1), (25, 15, 1), (26, 12, 1)],
  [(1, 19, -1), (2, 20, 1), (4, 18, 1), (8, 18, -1), (9, 4, -1), (9, 8, 1), (12, 3, 1), (15, 6, -1), (22, 17, -1), (23, 14, -1), (25, 16, 1), (26, 13, 1)],
  [(0, 15, 1), (2, 9, -1), (4, 15, -1), (5, 12, 1), (10, 25, -1), (11, 22, 1), (13, 24, -1), (14, 21, 1), (18, 6, 1), (19, 7, -1), (20, 0, -1), (20, 4, 1)],
  [(0, 16, 1), (2, 10, -1), (4, 16, -1), (5, 13, 1), (9, 25, 1), (11, 19, -1), (12, 24, 1), (14, 18, -1), (21, 6, 1), (22, 7, -1), (23, 0, -1), (23, 4, 1)],
  [(0, 17, 1), (2, 11, -1), (4, 17, -1), (5, 14, 1), (9, 22, -1), (10, 19, 1), (12, 21, -1), (13, 18, 1), (24, 6, 1), (25, 7, -1), (26, 0, -1), (26, 4, 1)],
  [(2, 1, 1), (3, 6, -1), (4, 7, -1), (5, 4, 1), (5, 8, -1), (8, 7, 1), (12, 15, -1), (13, 16, -1), (14, 17, -1), (20, 19, 1), (23, 22, 1), (26, 25, 1)],
  [(1, 15, -1), (2, 12, 1), (10, 24, -1), (11, 21, 1), (19, 6, -1), (20, 3, 1)],
  [(1, 16, -1), (2, 13, 1), (9, 24, 1), (11, 18, -1), (22, 6, -1), (23, 3, 1)],
  [(1, 17, -1), (2, 14, 1), (9, 21, -1), (10, 18, 1), (25, 6, -1), (26, 3, 1)],
  [(0, 6, -1), (1, 7, -1), (2, 0, 1), (2, 8, -1), (5, 3, 1), (8, 6, 1), (9, 15, -1), (10, 16, -1), (11, 17, -1), (20, 18, 1), (23, 21, 1), (26, 24, 1)],
  [(2, 25, -1), (5, 24, 1), (11, 7, -1), (14, 6, 1), (20, 16, -1), (23, 15, 1)],
  [(2, 22, 1), (5, 21, -1), (10, 7, 1), (13, 6, -1), (20, 17, -1), (26, 15, 1)],
  [(2, 19, -1), (5, 18, 1), (9, 7, -1), (12, 6, 1), (23, 17, -1), (26, 16, 1)],
  [(9, 9, 1), (10, 10, -1), (12, 12, 1), (13, 13, -1), (15, 15, 1), (16, 16, -1), (18, 18, -1), (19, 19, -1), (20, 20, -1), (21, 21, 1), (22, 22, 1), (23, 23, 1)],
  [(1, 1, -1), (2, 2, -1), (3, 3, 1), (6, 6, 1), (10, 10, -1), (11, 11, -1), (12, 12, 1), (15, 15, 1), (19, 19, -1), (20, 20, -1), (21, 21, 1), (24, 24, 1)],
  [(1, 1, 1), (3, 3, -1), (5, 5, -1), (7, 7, 1), (9, 9, 1), (13, 13, -1), (14, 14, -1), (15, 15, 1), (18, 18, -1), (20, 20, -1), (22, 22, 1), (25, 25, 1)],
  [(2, 2, 1), (5, 5, 1), (6, 6, -1), (7, 7, -1), (10, 10, 1), (13, 13, 1), (15, 15, -1), (17, 17, -1), (20, 20, 1), (21, 21, -1), (22, 22, -1), (26, 26, 1)],
]

private def generator (j : Fin 28) : Entries :=
  tangentEntries[j.val]?.getD []

private def evaluationEntry (v : Coord → ℤ) (r : Coord) (j : Fin 28) : ℤ :=
  ((generator j).map fun (row, col, c) => if row = r then c * v col else 0).sum

private def frameIndex (i : Fin 81) : Slot := ⟨i.val / 27, by omega⟩
private def coordinateIndex (i : Fin 81) : Coord := ⟨i.val % 27, by omega⟩

/-- Each column is the evaluation of an integral infinitesimal matrix on
the translated ordered frame. The first 24 columns have positive weight. -/
def integralEvaluation : Matrix (Fin 81) (Fin 28) ℤ :=
  of fun i j => evaluationEntry (movedFrame (frameIndex i)) (coordinateIndex i) j

private def positiveColumns : Fin 24 → Fin 28 := Fin.castLE (by decide)

private def integralPositiveEvaluation : Matrix (Fin 81) (Fin 24) ℤ :=
  integralEvaluation.submatrix id positiveColumns

private def positiveRows : Fin 21 → Fin 81 :=
  ![0, 1, 2, 3, 4, 5, 32, 9, 10, 11, 12, 13, 14, 16, 19, 27, 28, 29, 30, 37, 43]

private def positiveMinorColumns : Fin 21 → Fin 24 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 22]

private def positiveInverseData : Array (Array ℤ) := #[
  #[11, -9, 9, -5, 7, -5, 5, -1, 2, 0, 0, 2, 2, 0, -2, -2, -8, 9, 0, -2, 2],
  #[4, -4, 3, -1, 2, -1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, -5, 2, 0, 1, 0],
  #[6, -5, 5, -3, 4, -3, 1, 0, 1, 0, 1, 1, 1, 0, -1, -1, -5, 4, -1, -1, 1],
  #[13, -10, 10, -3, 6, -3, 3, 0, 2, 2, 0, 3, 3, 1, 0, 0, -12, 6, 0, 0, 3],
  #[12, -12, 9, -3, 6, -3, 3, 0, 3, 3, 0, 3, 3, 1, 0, 0, -15, 6, 0, 3, 3],
  #[5, -4, 4, -2, 3, -2, 1, 0, 1, 0, 0, 1, 1, 0, -1, -1, -4, 3, 0, -1, 1],
  #[24, -16, 19, -3, 9, -3, 3, 0, 2, 5, 0, 6, 7, 3, 3, 3, -21, 9, 0, 0, 6],
  #[32, -35, 23, -20, 27, -19, 20, 0, 11, -3, 0, 5, 4, -3, -14, -14, -32, 27, 0, -2, 5],
  #[7, -12, 4, -10, 11, -9, 11, 0, 5, -4, 0, 0, -1, -3, -9, -9, -8, 11, -1, -1, 0],
  #[-1, 1, -1, 1, -1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, -1, 0, 0, 0],
  #[4, -3, 3, -1, 2, -1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, -4, 2, 0, 0, 1],
  #[4, -4, 3, -1, 2, -1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, -5, 2, 0, 1, 1],
  #[5, -4, 4, -2, 3, -2, 2, 0, 1, 0, 0, 1, 1, 0, -1, -1, -4, 4, 0, -1, 1],
  #[3, -2, 2, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, -3, 1, 0, 0, 1],
  #[12, -12, 9, -6, 8, -6, 6, 0, 3, 0, 0, 2, 2, 0, -4, -4, -12, 8, 0, 0, 2],
  #[8, -9, 6, -5, 6, -5, 5, 0, 2, 0, 0, 1, 1, 0, -3, -3, -9, 6, 0, 1, 1],
  #[20, -19, 15, -8, 13, -8, 8, 0, 5, 1, 0, 4, 4, 0, -4, -4, -20, 13, 0, 0, 4],
  #[-4, 3, -3, 1, -2, 1, -1, 0, -1, 0, 0, -1, -1, 0, 1, 0, 4, -2, 0, 0, -1],
  #[-5, 4, -4, 2, -3, 2, -2, 0, -1, 0, 0, -1, -1, 0, 1, 1, 4, -3, 0, 0, -1],
  #[-5, 4, -4, 2, -3, 2, -2, 0, -1, 0, 0, -1, -1, 0, 1, 1, 4, -3, 0, 1, -1],
  #[5, -2, 4, -2, 3, -2, 2, 0, 0, -1, 0, 1, 1, 0, -1, -1, -1, 3, 0, -3, 1],
]

private def borelRows : Fin 23 → Fin 81 :=
  ![0, 1, 2, 3, 4, 5, 33, 7, 9, 10, 11, 12, 13, 14, 16, 19, 27, 28, 29, 30, 32, 37, 43]

private def borelMinorColumns : Fin 23 → Fin 28 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 22, 25, 26]

private def borelInverseData : Array (Array ℤ) := #[
  #[8, -6, 6, -2, 4, -2, 8, 1, -1, 2, 0, 0, 2, 2, 0, -2, 1, -5, 6, 0, 2, -2, 2],
  #[1, -1, 0, 2, -1, 2, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 3, -2, -1, 0, -2, 1, 0],
  #[6, -5, 5, -3, 4, -3, 6, 0, 0, 1, 0, 1, 1, 1, 0, -1, -1, -5, 4, -1, 1, -1, 1],
  #[4, -1, 1, 6, -3, 6, 3, 3, 0, 2, 2, 0, 3, 3, 1, 0, 9, -3, -3, 0, -6, 0, 3],
  #[3, -3, 0, 6, -3, 6, 3, 3, 0, 3, 3, 0, 3, 3, 1, 0, 9, -6, -3, 0, -6, 3, 3],
  #[2, -1, 1, 1, 0, 1, 2, 1, 0, 1, 0, 0, 1, 1, 0, -1, 2, -1, 0, 0, -2, -1, 1],
  #[3, 5, -2, 18, -12, 18, 0, 7, 0, 2, 5, 0, 6, 7, 3, 3, 24, 0, -12, 0, -18, 0, 6],
  #[20, -23, 11, -8, 15, -7, 22, 4, 0, 11, -3, 0, 5, 4, -3, -14, -2, -20, 15, 0, 8, -2, 5],
  #[13, -18, 10, -16, 17, -15, 14, -2, 0, 5, -4, 0, 0, -1, -3, -9, -15, -14, 17, -1, 17, -1, 0],
  #[-1, 1, -1, 1, -1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, -1, 0, -1, 0, 0],
  #[1, 0, 0, 2, -1, 2, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 3, -1, -1, 0, -2, 0, 1],
  #[1, -1, 0, 2, -1, 2, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 3, -2, -1, 0, -2, 1, 1],
  #[2, -1, 1, 1, 0, 1, 2, 1, 0, 1, 0, 0, 1, 1, 0, -1, 2, -1, 1, 0, -1, -1, 1],
  #[0, 1, -1, 3, -2, 3, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 4, 0, -2, 0, -3, 0, 1],
  #[6, -6, 3, 0, 2, 0, 6, 2, 0, 3, 0, 0, 2, 2, 0, -4, 2, -6, 2, 0, 0, 0, 2],
  #[5, -6, 3, -2, 3, -2, 5, 1, 0, 2, 0, 0, 1, 1, 0, -3, 0, -6, 3, 0, 2, 1, 1],
  #[8, -7, 3, 4, 1, 4, 8, 4, 0, 5, 1, 0, 4, 4, 0, -4, 8, -8, 1, 0, -4, 0, 4],
  #[-1, 0, 0, -2, 1, -2, -1, -1, 0, -1, 0, 0, -1, -1, 0, 1, -3, 1, 1, 0, 2, 0, -1],
  #[-2, 1, -1, -1, 0, -1, -2, -1, 0, -1, 0, 0, -1, -1, 0, 1, -2, 1, 0, 0, 1, 0, -1],
  #[-2, 1, -1, -1, 0, -1, -2, -1, 0, -1, 0, 0, -1, -1, 0, 1, -2, 1, 0, 0, 1, 1, -1],
  #[2, 1, 1, 1, 0, 1, 1, 1, 0, 0, -1, 0, 1, 1, 0, -1, 2, 2, 0, 0, -1, -3, 1],
  #[0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[3, -3, 3, -3, 3, -3, 3, -1, 0, 0, 0, 0, 0, 0, 0, 0, -3, -3, 3, 0, 3, 0, 0],
]

private def inverseEntry (data : Array (Array ℤ)) (i j : Fin n) : ℤ :=
  ((data[i.val]?.getD #[])[j.val]?).getD 0

private def matrixProductCheck {n : ℕ} (inverse minor : Matrix (Fin n) (Fin n) ℤ) : Bool :=
  (List.finRange n).all fun i =>
    (List.finRange n).all fun j =>
      (((List.finRange n).map fun k => inverse i k * minor k j).sum ==
        (if i = j then 1 else 0 : ℤ))

private theorem sum_finRange_eq_sum {n : ℕ} (f : Fin n → ℤ) :
    ((List.finRange n).map f).sum = ∑ i, f i := by
  rfl

private theorem mul_eq_one_of_check {n : ℕ} {inverse minor : Matrix (Fin n) (Fin n) ℤ}
    (h : matrixProductCheck inverse minor = true) : inverse * minor = 1 := by
  apply Matrix.ext
  intro i j
  have h' := List.all_eq_true.mp (List.all_eq_true.mp h i (List.mem_finRange i))
    j (List.mem_finRange j)
  simpa only [beq_iff_eq, sum_finRange_eq_sum, Matrix.mul_apply, Matrix.one_apply] using h'

private def positiveMinor : Matrix (Fin 21) (Fin 21) ℤ :=
  integralPositiveEvaluation.submatrix positiveRows positiveMinorColumns

private def borelMinor : Matrix (Fin 23) (Fin 23) ℤ :=
  integralEvaluation.submatrix borelRows borelMinorColumns

private def positiveInverse : Matrix (Fin 21) (Fin 21) ℤ := of (inverseEntry positiveInverseData)
private def borelInverse : Matrix (Fin 23) (Fin 23) ℤ := of (inverseEntry borelInverseData)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem positiveInverse_mul : positiveInverse * positiveMinor = 1 :=
  mul_eq_one_of_check (by rfl)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem borelInverse_mul : borelInverse * borelMinor = 1 :=
  mul_eq_one_of_check (by rfl)

private theorem rank_ge_of_integer_minor {k : Type*} [Field k] {n m l : ℕ}
    {A : Matrix (Fin m) (Fin l) ℤ} {r : Fin n → Fin m} {c : Fin n → Fin l}
    {B : Matrix (Fin n) (Fin n) ℤ} (h : B * A.submatrix r c = 1) :
    n ≤ (A.map (Int.castRingHom k)).rank := by
  let f := Int.castRingHom k
  let C := (A.map f).submatrix r c
  have hinv : B.map f * C = 1 := by
    have h' := congrArg (fun X : Matrix (Fin n) (Fin n) ℤ => X.map f) h
    rw [Matrix.map_mul (f := f), Matrix.map_one f (map_zero f) (map_one f),
      ← Matrix.submatrix_map] at h'
    exact h'
  have hrank := Matrix.rank_mul_le_right (B.map f) C
  rw [hinv, Matrix.rank_one, Fintype.card_fin] at hrank
  exact hrank.trans (Matrix.rank_submatrix_le (A.map f) r c)

/-- The selected submatrix of the positive-weight evaluation is
unimodular, giving the rank bound over every field. -/
theorem positiveEvaluation_rank (k : Type*) [Field k] :
    21 ≤ (integralPositiveEvaluation.map (Int.castRingHom k)).rank :=
  rank_ge_of_integer_minor positiveInverse_mul

/-- The submatrix using both positive and zero weights is likewise
unimodular. No restriction on the ground characteristic is used. -/
theorem fullEvaluation_rank (k : Type*) [Field k] :
    23 ≤ (integralEvaluation.map (Int.castRingHom k)).rank :=
  rank_ge_of_integer_minor borelInverse_mul

/-- The three coordinates in each norm monomial are stored with its integral coefficient. -/
private abbrev CubicTerms := List (List Coord × ℤ)

private def evaluateTerms {R : Type*} [CommRing R] (terms : CubicTerms) (v : Coord → R) : R :=
  (terms.map fun (indices, coefficient) => (coefficient : R) * (indices.map v).prod).sum

private def insertTerm (indices : List Coord) (coefficient : ℤ) : CubicTerms → CubicTerms
  | [] => [(indices, coefficient)]
  | (w, c) :: rest =>
    if indices = w then (w, coefficient + c) :: rest
    else (w, c) :: insertTerm indices coefficient rest

private def collectTerms : CubicTerms → CubicTerms
  | [] => []
  | (w, c) :: rest => insertTerm (w.insertionSort (· ≤ ·)) c (collectTerms rest)

private theorem evaluateTerms_insert {R : Type*} [CommRing R] (v : Coord → R)
    (w : List Coord) (c : ℤ) (p : CubicTerms) :
    evaluateTerms (insertTerm w c p) v =
      (c : R) * (w.map v).prod + evaluateTerms p v := by
  induction p with
  | nil => simp [insertTerm, evaluateTerms]
  | cons t rest ih =>
    rcases t with ⟨u, a⟩
    by_cases h : w = u
    · subst w
      simp only [insertTerm, ite_true, evaluateTerms, List.map_cons, List.sum_cons, Int.cast_add,
        add_mul, add_assoc]
    · simp only [insertTerm, ite_eq_right h]
      change (a : R) * (u.map v).prod + evaluateTerms (insertTerm w c rest) v =
        _ + ((a : R) * (u.map v).prod + evaluateTerms rest v)
      rw [ih]
      abel

private theorem evaluateTerms_collect {R : Type*} [CommRing R] (v : Coord → R) (p : CubicTerms) :
    evaluateTerms (collectTerms p) v = evaluateTerms p v := by
  induction p with
  | nil => rfl
  | cons t rest ih =>
    rcases t with ⟨w, c⟩
    rw [collectTerms, evaluateTerms_insert, ih]
    have h : ((w.insertionSort (· ≤ ·)).map v).prod = (w.map v).prod :=
      ((List.perm_insertionSort (· ≤ ·) w).map v).prod_eq
    rw [h]
    rfl

private theorem evaluateTerms_of_zero_check {R : Type*} [CommRing R]
    (v : Coord → R) (p : CubicTerms) (h : (collectTerms p).all (fun t => t.2 == 0) = true) :
    evaluateTerms p v = 0 := by
  rw [← evaluateTerms_collect v p]
  unfold evaluateTerms
  apply List.sum_eq_zero
  intro t ht
  obtain ⟨⟨w, c⟩, hw, rfl⟩ := List.mem_map.mp ht
  have hc : c = 0 := beq_iff_eq.mp (List.all_eq_true.mp h _ hw)
  simp [hc]

private def determinantTerms (block : Slot) : CubicTerms :=
  [([coord block 0 0, coord block 1 1, coord block 2 2], 1),
    ([coord block 0 1, coord block 1 2, coord block 2 0], 1),
    ([coord block 0 2, coord block 1 0, coord block 2 1], 1),
    ([coord block 0 0, coord block 1 2, coord block 2 1], -1),
    ([coord block 0 1, coord block 1 0, coord block 2 2], -1),
    ([coord block 0 2, coord block 1 1, coord block 2 0], -1)]

private def traceTerms : CubicTerms :=
  (List.finRange 3).flatMap fun i =>
    (List.finRange 3).flatMap fun j =>
      (List.finRange 3).map fun k => ([a i j, b j k, d k i], -1)

private def normTerms : CubicTerms :=
  determinantTerms 0 ++ determinantTerms 1 ++ determinantTerms 2 ++ traceTerms

private def unflatten {R : Type*} (v : Coord → R) : Matrix Slot Slot R ×
    Matrix Slot Slot R × Matrix Slot Slot R :=
  (of fun i j => v (a i j), of fun i j => v (b i j), of fun i j => v (d i j))

private theorem evaluateTerms_norm {R : Type*} [CommRing R] (v : Coord → R) :
    evaluateTerms normTerms v = Albert.ShortDirectionSpecification.matrixNorm (unflatten v) := by
  simp only [evaluateTerms, normTerms, List.map_append, List.sum_append]
  rw [Albert.ShortDirectionSpecification.matrixNorm]
  simp only [unflatten, det_fin_three, of_apply, trace, diag_apply, Matrix.mul_apply, Fin.sum_univ_three]
  simp [determinantTerms, traceTerms, List.finRange_succ, List.finRange_zero, a, b, d, coord]
  ring

private def rowTerms (entries : Entries) (row : Coord) : List (Coord × ℤ) :=
  (entries.filter fun e => e.1 == row).map fun e => e.2

private def evaluateRow {R : Type*} [CommRing R] (entries : Entries) (v : Coord → R)
    (row : Coord) : R := ((rowTerms entries row).map fun (s, c) => (c : R) * v s).sum

private theorem evaluateRow_eq {R : Type*} [CommRing R] (entries : Entries) (v : Coord → R)
    (row : Coord) :
    evaluateRow entries v row =
      (entries.map fun (r, s, c) => if r = row then (c : R) * v s else 0).sum := by
  induction entries with
  | nil => rfl
  | cons e es ih =>
    rcases e with ⟨r, s, c⟩
    by_cases h : r = row
    · have hb : (r == row) = true := beq_iff_eq.mpr h
      simp only [evaluateRow, rowTerms, List.filter_cons, hb, ite_true,
        List.map_cons, List.sum_cons, ite_eq_left h] at ih ⊢
      rw [ih]
    · have hb : (r == row) = false := beq_eq_false_iff_ne.mpr h
      simp only [evaluateRow, rowTerms, List.filter_cons, hb, Bool.false_eq_true, ite_false,
        List.map_cons, List.sum_cons, ite_eq_right h, zero_add] at ih ⊢
      exact ih


private def derivativeTerms (entries : Entries) : CubicTerms :=
  normTerms.flatMap fun (w, c) =>
    match w with
    | [i, j, k] =>
      ((rowTerms entries i).map fun (l, x) => ([l, j, k], c * x)) ++
      ((rowTerms entries j).map fun (l, x) => ([i, l, k], c * x)) ++
      ((rowTerms entries k).map fun (l, x) => ([i, j, l], c * x))
    | _ => []

private def normDifferential {R : Type*} [CommRing R] (v dv : Coord → R) : R :=
  (normTerms.map fun (w, c) =>
    match w with
    | [i, j, k] => (c : R) * (dv i * v j * v k + v i * dv j * v k + v i * v j * dv k)
    | _ => 0).sum

private theorem evaluateTerms_append {R : Type*} [CommRing R] (v : Coord → R)
    (p q : CubicTerms) : evaluateTerms (p ++ q) v = evaluateTerms p v + evaluateTerms q v := by
  simp [evaluateTerms]

private theorem evaluateTerms_row {R : Type*} [CommRing R] (v : Coord → R)
    (entries : List (Coord × ℤ)) (w : List Coord) (c : ℤ) :
    evaluateTerms (entries.map fun (l, x) => (l :: w, c * x)) v =
      (c : R) * ((entries.map fun (l, x) => (x : R) * v l).sum) * (w.map v).prod := by
  induction entries with
  | nil => simp [evaluateTerms]
  | cons t entries ih =>
    rcases t with ⟨l, x⟩
    change (((c * x : ℤ) : R) * (v l * (w.map v).prod)) +
      evaluateTerms (entries.map fun (l, x) => (l :: w, c * x)) v =
      (c : R) * ((x : R) * v l + (entries.map fun (l, x) => (x : R) * v l).sum) *
        (w.map v).prod
    rw [ih, Int.cast_mul]
    ring

private theorem evaluateTerms_reorder {R : Type*} [CommRing R] (v : Coord → R)
    (entries : List (Coord × ℤ)) (w₁ w₂ : Coord → List Coord) (c : ℤ)
    (h : ∀ l, (w₁ l).Perm (w₂ l)) :
    evaluateTerms (entries.map fun (l, x) => (w₁ l, c * x)) v =
      evaluateTerms (entries.map fun (l, x) => (w₂ l, c * x)) v := by
  unfold evaluateTerms
  simp only [List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  rintro ⟨l, x⟩ _
  rw [((h l).map v).prod_eq]

private theorem evaluateTerms_derivative {R : Type*} [CommRing R] (v : Coord → R)
    (entries : Entries) :
    evaluateTerms (derivativeTerms entries) v = normDifferential v (evaluateRow entries v) := by
  unfold derivativeTerms normDifferential
  generalize normTerms = terms
  induction terms with
  | nil => simp [evaluateTerms]
  | cons t ts ih =>
    rcases t with ⟨w, c⟩
    simp only [List.flatMap_cons, evaluateTerms_append, List.map_cons, List.sum_cons, ih]
    obtain _ | ⟨i, _ | ⟨j, _ | ⟨k, _ | ⟨l, rest⟩⟩⟩⟩ := w <;>
      try solve | simp [evaluateTerms]
    congr 1
    change evaluateTerms ((_ ++ _) ++ _) v = _
    rw [evaluateTerms_append, evaluateTerms_append,
      evaluateTerms_reorder v (rowTerms entries j) _ (fun l => [l, i, k]) c
        (fun l => List.Perm.swap l i [k]),
      evaluateTerms_reorder v (rowTerms entries k) _ (fun l => [l, i, j]) c
        (fun l => (List.Perm.swap l i [j]).symm.trans ((List.Perm.swap l j []).symm.cons i) |>.symm)]
    simp only [evaluateTerms_row, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      evaluateRow]
    ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem derivativeTerms_check (j : Fin 28) :
    (collectTerms (derivativeTerms (generator j))).all (fun t => t.2 == 0) = true := by
  fin_cases j <;> rfl

/-- Each column matrix annihilates the differential of the split cubic norm. -/
theorem normDifferential_generator {R : Type*} [CommRing R] (j : Fin 28) (v : Coord → R) :
    normDifferential v (evaluateRow (generator j) v) = 0 := by
  rw [← evaluateTerms_derivative]
  exact evaluateTerms_of_zero_check v _ (derivativeTerms_check j)

/-- The cocharacter evaluates the two coordinate pairs against (1000,100)
and (10,1), so the sign on weight differences agrees with lexicographic order. -/
private def coordinateWeight (z : Coord) : ℤ :=
  let first : Slot → ℤ := ![1000, 100, -1100]
  let second : Slot → ℤ := ![10, 1, -11]
  let i : Slot := ⟨z.val / 3 % 3, by omega⟩
  let j : Slot := ⟨z.val % 3, by omega⟩
  match z.val / 9 with
  | 0 => first i - first j
  | 1 => first i + second j
  | _ => -first j - second i

private def generatorWeight (j : Fin 28) : ℤ :=
  ((generator j).head?.map fun (r, s, _) => coordinateWeight r - coordinateWeight s).getD 0

private theorem generatorWeight_check (j : Fin 28) :
    (generator j).all (fun (r, s, _) =>
      coordinateWeight r - coordinateWeight s == generatorWeight j) = true := by
  fin_cases j <;> rfl

/-- The matrices of the first 24 columns are supported in a positive
cocharacter weight each. The final four are in weight zero. -/
theorem tangentEntry_weight {j : Fin 28} {r s : Coord} {c : ℤ}
    (h : (r, s, c) ∈ generator j) : coordinateWeight r - coordinateWeight s = generatorWeight j :=
  beq_iff_eq.mp (List.all_eq_true.mp (generatorWeight_check j) _ h)

theorem positiveGeneratorWeight (j : Fin 24) : 0 < generatorWeight (positiveColumns j) := by
  fin_cases j <;> decide

theorem zeroGeneratorWeight (j : Fin 4) : generatorWeight (Fin.natAdd 24 j) = 0 := by
  fin_cases j <;> rfl

theorem positiveGeneratorWeight_injective :
    Function.Injective (fun j : Fin 24 => generatorWeight (positiveColumns j)) := by
  decide

theorem coordinateWeight_minimal (z : Coord) (h : z ≠ a 2 0) :
    coordinateWeight (a 2 0) < coordinateWeight z := by
  revert h
  fin_cases z <;> decide

open scoped DualNumber

private theorem evaluateTerms_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p : CubicTerms) (v : Coord → R) :
    evaluateTerms p (f ∘ v) = f (evaluateTerms p v) := by
  unfold evaluateTerms
  rw [← List.sum_map_hom]
  apply congrArg List.sum
  apply List.map_congr_left
  rintro ⟨w, c⟩ _
  dsimp only [Function.comp_apply]
  rw [List.prod_map_hom, map_mul, map_intCast]

private theorem normTerms_length (term : List Coord × ℤ) (h : term ∈ normTerms) :
    term.1.length = 3 := by
  have hc : normTerms.all (fun term => term.1.length == 3) = true := rfl
  exact beq_iff_eq.mp (List.all_eq_true.mp hc _ h)

private def dualVector {R : Type*} (v dv : Coord → R) (i : Coord) : DualNumber R :=
  (v i, dv i)

private theorem dualVector_fst {R : Type*} (v dv : Coord → R) (i : Coord) :
    (dualVector v dv i).fst = v i := rfl

private theorem dualVector_snd {R : Type*} (v dv : Coord → R) (i : Coord) :
    (dualVector v dv i).snd = dv i := rfl

private theorem evaluateTerms_snd {R : Type*} [CommRing R] (v dv : Coord → R) :
    (evaluateTerms normTerms (dualVector v dv)).snd =
      normDifferential v dv := by
  unfold normDifferential
  have h₃ : ∀ t ∈ normTerms, (t : List Coord × ℤ).1.length = 3 := normTerms_length
  generalize normTerms = terms at h₃ ⊢
  induction terms with
  | nil => simp [evaluateTerms]
  | cons t ts ih =>
    have htail (u) (hu : u ∈ ts) := h₃ u (List.mem_cons_of_mem _ hu)
    have ht := h₃ t (List.mem_cons_self)
    obtain ⟨w, c⟩ := t
    obtain _ | ⟨i, _ | ⟨j, _ | ⟨k, _ | ⟨l, rest⟩⟩⟩⟩ := w <;>
      simp only [List.length_cons, List.length_nil] at ht <;> try omega
    change TrivSqZeroExt.snd ((c : DualNumber R) *
      ((dualVector v dv i) * ((dualVector v dv j) * ((dualVector v dv k) * 1))) +
        evaluateTerms ts (dualVector v dv)) = _ + (ts.map _).sum
    rw [TrivSqZeroExt.snd_add, ih htail]
    congr 1
    simp only [mul_one, DualNumber.snd_mul, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_intCast,
      TrivSqZeroExt.fst_intCast, dualVector_fst, dualVector_snd]
    ring

/-- Each column is an infinitesimal symmetry of the cubic norm in split matrix
coordinates. The two components of the equality are the constant and linear
terms in the dual numbers. -/
theorem generator_preserves_matrixNorm_dual {R : Type*} [CommRing R] (j : Fin 28)
    (v : Coord → R) :
    Albert.ShortDirectionSpecification.matrixNorm
        (unflatten (dualVector v (evaluateRow (generator j) v))) =
      Albert.ShortDirectionSpecification.matrixNorm
        (unflatten (dualVector v (fun _ => 0))) := by
  let x := dualVector v (evaluateRow (generator j) v)
  let y := dualVector v (fun _ => 0)
  have he : evaluateTerms normTerms x = evaluateTerms normTerms y := by
    refine @TrivSqZeroExt.ext R R (evaluateTerms normTerms x) (evaluateTerms normTerms y) ?_ ?_
    · let f := (TrivSqZeroExt.fstHom R R R).toRingHom
      have hx := evaluateTerms_map f normTerms x
      have hy := evaluateTerms_map f normTerms y
      exact hx.symm.trans hy
    · let f := TrivSqZeroExt.inlHom R R
      have hz : evaluateTerms normTerms y = f (evaluateTerms normTerms v) :=
        evaluateTerms_map f normTerms v
      have hx := (evaluateTerms_snd v (evaluateRow (generator j) v)).trans
        (normDifferential_generator j v)
      exact hx.trans ((congrArg TrivSqZeroExt.snd hz).trans (TrivSqZeroExt.snd_inl R _)).symm
  exact (evaluateTerms_norm x).symm.trans (he.trans (evaluateTerms_norm y))

private def unitVector {R : Type*} [CommRing R] : Coord → R :=
  fun i => if i = a 0 0 ∨ i = a 1 1 ∨ i = a 2 2 then 1 else 0

private theorem evaluateRow_intCast {R : Type*} [CommRing R] (entries : Entries)
    (v : Coord → ℤ) (r : Coord) :
    evaluateRow entries (fun i => (v i : R)) r = ((evaluateRow (R := ℤ) entries v r : ℤ) : R) := by
  unfold evaluateRow
  change ((rowTerms entries r).map fun (s, c) => (c : R) * (v s : R)).sum =
    Int.castRingHom R (((rowTerms entries r).map fun (s, c) => c * v s).sum)
  rw [← List.sum_map_hom]
  congr 1
  apply List.map_congr_left
  rintro ⟨s, c⟩ _
  exact (Int.cast_mul c (v s)).symm

private theorem generator_fixesUnit_int (j : Fin 28) : ∀ r : Coord,
    evaluateRow (generator j) (unitVector (R := ℤ)) r = 0 := by
  have h (i : Fin 28) : ((List.finRange 27).all
      (fun r => evaluateRow (generator i) (unitVector (R := ℤ)) r == 0)) = true := by
    fin_cases i <;> rfl
  intro r
  exact beq_iff_eq.mp (List.all_eq_true.mp (h j) r (List.mem_finRange r))

/-- The tangent matrices annihilate the distinguished unit (I,0,0). -/
theorem generator_annihilates_unit {R : Type*} [CommRing R] (j : Fin 28) :
    evaluateRow (generator j) (unitVector (R := R)) = 0 := by
  funext r
  have h (i : Coord) : unitVector i = (unitVector (R := ℤ) i : R) := by
    unfold unitVector
    split <;> simp
  change evaluateRow (generator j) unitVector r = (0 : R)
  rw [show unitVector (R := R) = (fun i => (unitVector (R := ℤ) i : R)) from funext h,
    evaluateRow_intCast, generator_fixesUnit_int, Int.cast_zero]

set_option maxHeartbeats 1200000 in
private theorem zornAction_norm {R : Type*} [CommRing R]
    (i : Slot) (t : R) (v : Coord → R) :
    evaluateTerms normTerms (zornAction i t v) = evaluateTerms normTerms v := by
  fin_cases i <;>
    simp [evaluateTerms, normTerms, determinantTerms, traceTerms, List.finRange_succ,
      List.finRange_zero, a, b, d, coord, zornAction, crossEntry] <;> ring

set_option maxHeartbeats 1200000 in
private theorem elementaryAction_norm {R : Type*} [CommRing R]
    (i j : Slot) (h : i ≠ j) (t : R) (v : Coord → R) :
    evaluateTerms normTerms (elementaryAction i j t v) = evaluateTerms normTerms v := by
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals
    simp [evaluateTerms, normTerms, determinantTerms, traceTerms, List.finRange_succ,
      List.finRange_zero, a, b, d, coord, elementaryAction]; ring

private theorem elementaryAction_unit {R : Type*} [CommRing R] (i j : Slot) (h : i ≠ j) (t : R) :
    elementaryAction i j t (unitVector (R := R)) = unitVector := by
  funext z
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals fin_cases z <;> simp [elementaryAction, unitVector, a, b, d, coord]

private theorem zornAction_unit {R : Type*} [CommRing R] (i : Slot) (t : R) :
    zornAction i t (unitVector (R := R)) = unitVector := by
  funext z
  fin_cases i <;> fin_cases z <;> simp [zornAction, unitVector, a, b, d, coord]

set_option maxHeartbeats 1400000 in
private theorem elementaryAction_inverse {R : Type*} [CommRing R]
    (i j : Slot) (h : i ≠ j) (t : R) (v : Coord → R) :
    elementaryAction i j (-t) (elementaryAction i j t v) = v := by
  funext z
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals fin_cases z <;> simp [elementaryAction, a, b, d, coord]; ring

set_option maxHeartbeats 1400000 in
private theorem zornAction_inverse {R : Type*} [CommRing R]
    (i : Slot) (t : R) (v : Coord → R) :
    zornAction i (-t) (zornAction i t v) = v := by
  funext z
  fin_cases i <;> fin_cases z <;>
    simp [zornAction, crossEntry, a, b, d, coord] <;> ring

private def elementaryLinearEquiv {R : Type*} [CommRing R]
    (i j : Slot) (h : i ≠ j) (t : R) : (Coord → R) ≃ₗ[R] (Coord → R) where
  toFun := elementaryAction i j t
  invFun := elementaryAction i j (-t)
  left_inv := elementaryAction_inverse i j h t
  right_inv v := by simpa only [neg_neg] using elementaryAction_inverse i j h (-t) v
  map_add' v w := by
    funext z
    unfold elementaryAction
    simp only [Pi.add_apply]
    split <;> (try split_ifs) <;> ring
  map_smul' c v := by
    funext z
    change elementaryAction i j t (c • v) z = c * elementaryAction i j t v z
    unfold elementaryAction
    simp only [Pi.smul_apply, smul_eq_mul]
    split <;> (try split_ifs) <;> ring

private def zornLinearEquiv {R : Type*} [CommRing R]
    (i : Slot) (t : R) : (Coord → R) ≃ₗ[R] (Coord → R) where
  toFun := zornAction i t
  invFun := zornAction i (-t)
  left_inv := zornAction_inverse i t
  right_inv v := by simpa only [neg_neg] using zornAction_inverse i (-t) v
  map_add' v w := by
    funext z
    unfold zornAction
    simp only [Pi.add_apply]
    split <;> (try split_ifs) <;> ring
  map_smul' c v := by
    funext z
    change zornAction i t (c • v) z = c * zornAction i t v z
    unfold zornAction
    simp only [Pi.smul_apply, smul_eq_mul]
    split <;> (try split_ifs) <;> ring

private theorem elementaryAction_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (i j : Slot) (t : R) (v : Coord → R) :
    f ∘ elementaryAction i j t v = elementaryAction i j (f t) (f ∘ v) := by
  funext z
  unfold elementaryAction
  simp only [Function.comp_apply]
  split <;> (try split_ifs) <;> simp only [map_add, map_sub, map_mul, map_pow, map_zero]

private theorem zornAction_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (i : Slot) (t : R) (v : Coord → R) :
    f ∘ zornAction i t v = zornAction i (f t) (f ∘ v) := by
  funext z
  unfold zornAction
  simp only [Function.comp_apply]
  split <;> (try split_ifs) <;>
    simp only [map_add, map_sub, map_mul, map_pow, map_zero, map_neg]
  unfold crossEntry
  split_ifs <;> simp

private def FrameMove.equiv (R : Type*) [CommRing R] : FrameMove → (Coord → R) ≃ₗ[R] (Coord → R)
  | .elementary i j h t => elementaryLinearEquiv i j h (t : R)
  | .zorn i t => zornLinearEquiv i (t : R)

private def frameWord (R : Type*) [CommRing R] : List FrameMove → (Coord → R) ≃ₗ[R] (Coord → R)
  | [] => LinearEquiv.refl _ _
  | m :: l => (m.equiv R).trans (frameWord R l)

private theorem FrameMove.equiv_norm {R : Type*} [CommRing R] (m : FrameMove) (v : Coord → R) :
    evaluateTerms normTerms ((m.equiv R) v) = evaluateTerms normTerms v := by
  cases m with
  | elementary i j h t => exact elementaryAction_norm i j h (t : R) v
  | zorn i t => exact zornAction_norm i (t : R) v

private theorem FrameMove.equiv_preserves_unit {R : Type*} [CommRing R] (m : FrameMove) :
    (m.equiv R) unitVector = unitVector := by
  cases m with
  | elementary i j h t => exact elementaryAction_unit i j h (t : R)
  | zorn i t => exact zornAction_unit i (t : R)

private theorem FrameMove.equiv_natural {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (m : FrameMove) (v : Coord → R) :
    f ∘ (m.equiv R) v = (m.equiv S) (f ∘ v) := by
  cases m with
  | elementary i j h t =>
    change f ∘ elementaryAction i j (t : R) v = elementaryAction i j (t : S) (f ∘ v)
    simpa only [map_intCast] using elementaryAction_map f i j (t : R) v
  | zorn i t =>
    change f ∘ zornAction i (t : R) v = zornAction i (t : S) (f ∘ v)
    simpa only [map_intCast] using zornAction_map f i (t : R) v

private theorem frameWord_norm {R : Type*} [CommRing R] (moves : List FrameMove) (v : Coord → R) :
    evaluateTerms normTerms (frameWord R moves v) = evaluateTerms normTerms v := by
  induction moves generalizing v with
  | nil => rfl
  | cons m l ih =>
    change evaluateTerms normTerms (frameWord R l (m.equiv R v)) = _
    rw [ih, FrameMove.equiv_norm]

private theorem frameWord_unit (R : Type*) [CommRing R] (moves : List FrameMove) :
    frameWord R moves unitVector = unitVector := by
  induction moves with
  | nil => rfl
  | cons m l ih =>
    change frameWord R l (m.equiv R unitVector) = _
    rw [FrameMove.equiv_preserves_unit, ih]

private theorem frameWord_natural {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (moves : List FrameMove) (v : Coord → R) :
    f ∘ frameWord R moves v = frameWord S moves (f ∘ v) := by
  induction moves generalizing v with
  | nil => rfl
  | cons m l ih =>
    change f ∘ frameWord R l (m.equiv R v) = frameWord S l (m.equiv S (f ∘ v))
    rw [ih, FrameMove.equiv_natural]

private theorem FrameMove.equiv_apply {R : Type*} [CommRing R] (m : FrameMove)
    (v : Coord → R) : (m.equiv R) v = m.apply v := by
  cases m <;> rfl

private theorem frameWord_apply {R : Type*} [CommRing R] (moves : List FrameMove)
    (v : Coord → R) : frameWord R moves v = moves.foldl FrameMove.apply v := by
  induction moves generalizing v with
  | nil => rfl
  | cons m l ih =>
    change frameWord R l (m.equiv R v) = l.foldl FrameMove.apply (m.apply v)
    rw [FrameMove.equiv_apply, ih]

private theorem movedFrame_eq_frameWord (R : Type*) [CommRing R] (l : Slot) :
    movedFrame (R := R) l = frameWord R frameMoves (fun z => if z = a l l then 1 else 0) :=
  (frameWord_apply frameMoves _).symm

private theorem movedFrame_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (l : Slot) :
    f ∘ movedFrame l = movedFrame l := by
  rw [movedFrame_eq_frameWord, movedFrame_eq_frameWord, frameWord_natural]
  congr 1
  funext z
  change f (if z = a l l then 1 else 0) = _
  split <;> simp

private def firstInvariantWord : List FrameMove := [.elementary 2 0 (by decide) 1]

private def secondInvariantWord : List FrameMove :=
  [.elementary 0 1 (by decide) 1, .elementary 1 0 (by decide) (-1),
   .elementary 0 1 (by decide) 1] ++ firstInvariantWord

private theorem firstInvariantWord_values (R : Type*) [CommRing R] :
    let e := frameWord R firstInvariantWord
    e (fun z => if z = a 0 0 then 1 else 0) (a 2 0) = 1 ∧
    e (fun z => if z = a 1 1 then 1 else 0) (a 2 0) = 0 := by
  dsimp [firstInvariantWord, frameWord, FrameMove.equiv, elementaryLinearEquiv]
  simp [elementaryAction, a, coord]

private theorem secondInvariantWord_values (R : Type*) [CommRing R] :
    let e := frameWord R secondInvariantWord
    e (fun z => if z = a 0 0 then 1 else 0) (a 2 0) = 0 ∧
    e (fun z => if z = a 1 1 then 1 else 0) (a 2 0) = 1 := by
  dsimp [secondInvariantWord, firstInvariantWord, frameWord, FrameMove.equiv, elementaryLinearEquiv]
  simp [elementaryAction, a, coord]

open Albert.ShortDirectionSpecification (ThreeMatrices matrixCoordinates matrixNorm splitNorm)
open Albert.TrialitySpecification (Model mapModel modelBaseChange)
open Albert.CubicSpecification (cubicUnit)
open Albert.FrameSpecification (frameAxis)

private def flatten {R : Type*} (x : ThreeMatrices R) (z : Coord) : R :=
  let i : Slot := ⟨z.val / 3 % 3, by omega⟩
  let j : Slot := ⟨z.val % 3, by omega⟩
  match z.val / 9 with
  | 0 => x.1 i j
  | 1 => x.2.1 i j
  | _ => x.2.2 i j

private def matrixCoordinatesEquiv (R : Type*) [CommRing R] : ThreeMatrices R ≃ₗ[R] (Coord → R) where
  toFun := flatten
  invFun := unflatten
  left_inv x := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> ext i j <;> fin_cases i <;> fin_cases j <;> rfl
  right_inv v := by
    funext z
    fin_cases z <;> rfl
  map_add' x y := by
    funext z
    simp only [Pi.add_apply, flatten]
    split <;> rfl
  map_smul' r x := by
    funext z
    simp only [RingHom.id_apply, Pi.smul_apply, flatten]
    split <;> rfl

/-- The split model in the row-major coordinates used in the evaluation certificate. -/
def modelCoordinateEquiv (R : Type*) [CommRing R] : Model R ≃ₗ[R] (Coord → R) :=
  (Albert.ShortDirections.coordinateEquiv R).trans (matrixCoordinatesEquiv R)

private theorem modelCoordinateEquiv_natural {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (x : Model R) :
    modelCoordinateEquiv S (mapModel f x) = f ∘ modelCoordinateEquiv R x := by
  funext z
  change flatten (matrixCoordinates (mapModel f x)) z = f (flatten (matrixCoordinates x) z)
  fin_cases z <;>
    simp [flatten, matrixCoordinates, mapModel, Composition.ZornSpecification.mapCoordinates]

private theorem modelCoordinateEquiv_unit (R : Type*) [CommRing R] :
    modelCoordinateEquiv R cubicUnit = unitVector := by
  change flatten (matrixCoordinates cubicUnit) = _
  rw [(Albert.ShortDirections.matrixNormFormula R).1]
  funext z
  fin_cases z <;> simp [flatten, unitVector, coord, a, Matrix.one_apply]

private theorem modelCoordinateEquiv_axis (R : Type*) [CommRing R] (i : Slot) :
    modelCoordinateEquiv R (frameAxis i) = fun z => if z = a i i then 1 else 0 := by
  funext z
  change flatten (matrixCoordinates (frameAxis i)) z = _
  fin_cases i <;> fin_cases z <;>
    simp [flatten, matrixCoordinates, frameAxis, Albert.CubicSpecification.diagonalCoordinates,
      coord, a]

private theorem modelCoordinateEquiv_norm {R : Type*} [CommRing R] (x : Model R) :
    splitNorm x = matrixNorm (unflatten (modelCoordinateEquiv R x)) := by
  rw [(Albert.ShortDirections.matrixNormFormula R).2]
  change matrixNorm (matrixCoordinates x) =
    matrixNorm ((matrixCoordinatesEquiv R).symm ((matrixCoordinatesEquiv R)
      (matrixCoordinates x)))
  rw [LinearEquiv.symm_apply_apply]

private def rowOperator (R : Type*) [CommRing R] (entries : Entries) :
    Module.End R (Coord → R) where
  toFun := evaluateRow entries
  map_add' v w := by
    funext r
    unfold evaluateRow
    simp only [Pi.add_apply, mul_add, List.sum_map_add]
  map_smul' c v := by
    funext r
    change evaluateRow entries (c • v) r = c * evaluateRow entries v r
    unfold evaluateRow
    induction rowTerms entries r with
    | nil => simp
    | cons e es ih =>
      rcases e with ⟨j, a⟩
      simp only [List.map_cons, List.sum_cons] at *
      rw [ih]
      change (a : R) * (c * v j) + _ = _
      ring

private theorem evaluateRow_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (entries : Entries) (v : Coord → R) (r : Coord) :
    evaluateRow entries (f ∘ v) r = f (evaluateRow entries v r) := by
  unfold evaluateRow
  rw [← List.sum_map_hom]
  apply congrArg List.sum
  apply List.map_congr_left
  rintro ⟨j, c⟩ _
  simp [Function.comp_apply]

/-- The integral matrix of a column, acting on the split Albert model. -/
def tangentOperator (R : Type*) [CommRing R] (j : Fin 28) : Module.End R (Model R) :=
  (modelCoordinateEquiv R).symm.toLinearMap.comp
    ((rowOperator R (generator j)).comp (modelCoordinateEquiv R).toLinearMap)

private theorem tangentOperator_coordinates (R : Type*) [CommRing R] (j : Fin 28) (x : Model R) :
    modelCoordinateEquiv R (tangentOperator R j x) =
      evaluateRow (generator j) (modelCoordinateEquiv R x) := by
  change modelCoordinateEquiv R ((modelCoordinateEquiv R).symm _) = _
  exact (modelCoordinateEquiv R).apply_symm_apply _

theorem tangentOperator_natural {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (j : Fin 28) (x : Model R) :
    mapModel f (tangentOperator R j x) = tangentOperator S j (mapModel f x) := by
  apply (modelCoordinateEquiv S).injective
  rw [modelCoordinateEquiv_natural, tangentOperator_coordinates, tangentOperator_coordinates,
    modelCoordinateEquiv_natural]
  funext r
  exact (evaluateRow_map f _ _ _).symm

theorem tangentOperator_unit (R : Type*) [CommRing R] (j : Fin 28) :
    tangentOperator R j cubicUnit = 0 := by
  apply (modelCoordinateEquiv R).injective
  rw [tangentOperator_coordinates, modelCoordinateEquiv_unit, generator_annihilates_unit, map_zero]

open scoped TensorProduct
open _root_.Specs.LinearAlgebraicGroups.Albert (QuadraticJordan)
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms (IsQuadraticDerivation)
open Albert.TrialitySpecification (modelOp)
open Albert.SplitSpecification (ParaQuadratic)
open Albert.IntrinsicCubicSpecification (PreservesNorm)
open private splitChart_ground splitChart_over from LinearAlgebraicGroups.Albert.ShortDirections
open private transported_norm_iff norm_infinitesimal_iff from LinearAlgebraicGroups.Albert.IntrinsicCubic

private theorem norm_add_squareZero {R : Type*} [CommRing R] (j : Fin 28) (v : Coord → R)
    (t : R) (ht : t * t = 0) :
    matrixNorm (unflatten (v + t • evaluateRow (generator j) v)) =
      matrixNorm (unflatten v) := by
  let f : DualNumber R →ₐ[R] R :=
    DualNumber.lift ⟨(Algebra.ofId R R, t), ht, fun _ => Commute.all _ _⟩
  have h := congrArg f (generator_preserves_matrixNorm_dual j v)
  change f.toRingHom _ = f.toRingHom _ at h
  simp only [← evaluateTerms_norm, ← evaluateTerms_map] at h ⊢
  have h₁ : (f.toRingHom ∘ dualVector v (evaluateRow (generator j) v)) =
      v + t • evaluateRow (generator j) v := by
    funext i
    change f (dualVector v (evaluateRow (generator j) v) i) = _
    rw [show f (dualVector v (evaluateRow (generator j) v) i) =
      v i + evaluateRow (generator j) v i * t from rfl]
    change _ = v i + t * evaluateRow (generator j) v i
    rw [mul_comm t]
  have h₂ : (f.toRingHom ∘ dualVector v (fun _ => 0)) = v := by
    funext i
    change v i + 0 * t = v i
    simp
  rwa [h₁, h₂] at h

theorem tangentOperator_preserves_norm {R : Type*} [CommRing R] (j : Fin 28) (x : Model R)
    (t : R) (ht : t * t = 0) :
    splitNorm (x + t • tangentOperator R j x) = splitNorm x := by
  rw [modelCoordinateEquiv_norm, modelCoordinateEquiv_norm (x := x),
    map_add, map_smul, tangentOperator_coordinates]
  exact norm_add_squareZero j _ t ht

/-- The matrices used in the rank computation are quadratic derivations
for the split algebra, in every characteristic. -/
theorem tangentOperator_isQuadraticDerivation (R : Type) [CommRing R] :
    ∃ J : QuadraticJordan R (Model R), J.unit = cubicUnit ∧
      (∀ x y, J.groundOp x y = modelOp x y) ∧
      ∀ j, IsQuadraticDerivation J (tangentOperator R j) := by
  obtain ⟨J, F, hu, ho, hJ, hF, hchart, _⟩ := Albert.Triality.cubicFrameStabilizer R
  obtain ⟨c, hc⟩ := splitChart_ground J hu ho
  refine ⟨J, hu, ho, fun j => ?_⟩
  let D := tangentOperator R j
  apply (Albert.intrinsic_norm_tangent J F hJ hF D).2
  apply (norm_infinitesimal_iff hJ hF D).1
  apply (transported_norm_iff (J := J) (F := F) D).2
  refine ⟨hu ▸ tangentOperator_unit R j, ?_⟩
  intro S _ _ f x
  obtain ⟨d, hd⟩ := splitChart_over J hc S
  have hD (y : S ⊗[R] Model R) :
      d.coordinates (D.baseChange S y) = tangentOperator S j (d.coordinates y) := by
    induction y using TensorProduct.inductionOn with
    | tmul a y =>
      rw [LinearMap.baseChange_tmul, hd, hd, map_smul]
      exact congrArg (a • ·) (tangentOperator_natural (algebraMap R S) j y)
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [(hchart S d _).2.2, (hchart S d x).2.2]
  change splitNorm (d.coordinates _) = splitNorm (d.coordinates x)
  rw [map_add, map_smul, hD]
  exact tangentOperator_preserves_norm j _ (f ε) (by rw [← map_mul, DualNumber.eps_mul_eps, map_zero])

open Albert.IdempotentSpecification (IsSplitAutomorphism)

private def frameWordModel (R : Type*) [CommRing R] (moves : List FrameMove) : Model R ≃ₗ[R] Model R :=
  (modelCoordinateEquiv R).trans ((frameWord R moves).trans (modelCoordinateEquiv R).symm)

private theorem frameWordModel_coordinates (R : Type*) [CommRing R] (moves : List FrameMove)
    (x : Model R) :
    modelCoordinateEquiv R (frameWordModel R moves x) = frameWord R moves (modelCoordinateEquiv R x) :=
  (modelCoordinateEquiv R).apply_symm_apply _

private theorem frameWordModel_natural {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (moves : List FrameMove) (x : Model R) :
    mapModel f (frameWordModel R moves x) = frameWordModel S moves (mapModel f x) := by
  apply (modelCoordinateEquiv S).injective
  rw [modelCoordinateEquiv_natural, frameWordModel_coordinates, frameWordModel_coordinates,
    modelCoordinateEquiv_natural, frameWord_natural]

private theorem frameWordModel_norm {R : Type*} [CommRing R] (moves : List FrameMove)
    (x : Model R) : splitNorm (frameWordModel R moves x) = splitNorm x := by
  calc
    splitNorm (frameWordModel R moves x) =
        evaluateTerms normTerms (modelCoordinateEquiv R (frameWordModel R moves x)) :=
      (modelCoordinateEquiv_norm _).trans (evaluateTerms_norm _).symm
    _ = evaluateTerms normTerms (modelCoordinateEquiv R x) := by
      rw [frameWordModel_coordinates, frameWord_norm]
    _ = splitNorm x := (evaluateTerms_norm _).trans (modelCoordinateEquiv_norm x).symm

private theorem splitAutomorphism_of_natural_norm {R : Type} [CommRing R]
    (g : Model R ≃ₗ[R] Model R) (hu : g cubicUnit = cubicUnit)
    (h : ∀ (S : Type) [CommRing S] [Algebra R S], ∃ gS : Model S ≃ₗ[S] Model S,
      (∀ x, mapModel (algebraMap R S) (g x) = gS (mapModel (algebraMap R S) x)) ∧
      ∀ y, splitNorm (gS y) = splitNorm y) : IsSplitAutomorphism g := by
  obtain ⟨J, F, hunit, hground, hJ, hF, hagrees, -⟩ := Albert.Triality.cubicFrameStabilizer R
  let L := ParaQuadratic.ofJordan J
  obtain ⟨c, hc⟩ := splitChart_ground J hunit hground
  have hn : PreservesNorm L F g.toLinearMap := by
    refine ⟨?_, ?_⟩
    · change g J.unit = J.unit
      rwa [hunit]
    intro S _ _ x
    obtain ⟨d, hd⟩ := splitChart_over J hc S
    obtain ⟨gS, hgS, hnorm⟩ := h S
    have he (y : S ⊗[R] Model R) :
        d.coordinates (g.toLinearMap.baseChange S y) = gS (d.coordinates y) := by
      induction y using TensorProduct.inductionOn with
      | tmul a y =>
        rw [LinearMap.baseChange_tmul, hd, hd, map_smul]
        exact congrArg (a • ·) (hgS y)
      | add y z hy hz => simp only [map_add, hy, hz]
    rw [(hagrees S d _).2.2, (hagrees S d x).2.2, he]
    exact hnorm _
  have he := (L.isIso_iff_ground L g).mp ((Albert.intrinsic_norm_automorphisms L F hJ hF g).mpr hn)
  refine ⟨hu, fun x y => ?_⟩
  have hexy := he.2 x y
  change g (J.groundOp x y) = J.groundOp (g x) (g y) at hexy
  simpa only [hground] using hexy

private theorem frameWordModel_isSplitAutomorphism (R : Type) [CommRing R]
    (moves : List FrameMove) : IsSplitAutomorphism (frameWordModel R moves) := by
  apply splitAutomorphism_of_natural_norm
  · apply (modelCoordinateEquiv R).injective
    rw [frameWordModel_coordinates, modelCoordinateEquiv_unit, frameWord_unit]
  · intro S _ _
    exact ⟨frameWordModel S moves, frameWordModel_natural (algebraMap R S) moves,
      frameWordModel_norm moves⟩

section DiagonalAction

/-- Exponents in the four independent diagonal coordinates
`A₀₁`, `A₁₂`, `B₀₀`, and `B₀₁`. The determinant-one diagonal
parameters of the source act through these coordinates. -/
private def diagonalExponents (z : Coord) : Fin 4 → ℤ :=
  let first : Slot → Fin 4 → ℤ := ![![0, 0, 0, 0], ![-1, 0, 0, 0], ![-1, -1, 0, 0]]
  let second : Slot → Fin 4 → ℤ := ![![0, 0, 1, 0], ![0, 0, 0, 1], ![2, 1, -1, -1]]
  let i : Slot := ⟨z.val / 3 % 3, by omega⟩
  let j : Slot := ⟨z.val % 3, by omega⟩
  match z.val / 9 with
  | 0 => first i - first j
  | 1 => first i + second j
  | _ => -first j - second i

private def diagonalCoefficient {R : Type*} [CommRing R] (s : Fin 4 → Rˣ) (z : Coord) :
    Rˣ :=
  ∏ j, s j ^ diagonalExponents z j

private theorem diagonalCoefficient_one {R : Type*} [CommRing R] (z : Coord) :
    diagonalCoefficient (1 : Fin 4 → Rˣ) z = 1 := by
  simp [diagonalCoefficient]

private theorem diagonalCoefficient_mul {R : Type*} [CommRing R]
    (s t : Fin 4 → Rˣ) (z : Coord) :
    diagonalCoefficient (s * t) z = diagonalCoefficient s z * diagonalCoefficient t z := by
  simp only [diagonalCoefficient, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

private theorem diagonalCoefficient_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (s : Fin 4 → Rˣ) (z : Coord) :
    diagonalCoefficient (Units.map f.toMonoidHom ∘ s) z =
      Units.map f.toMonoidHom (diagonalCoefficient s z) := by
  simp [diagonalCoefficient]

private theorem diagonalCoefficient_axis {R : Type*} [CommRing R]
    (s : Fin 4 → Rˣ) (i : Slot) : diagonalCoefficient s (a i i) = 1 := by
  have h (j : Fin 4) : diagonalExponents (a i i) j = 0 := by
    fin_cases i <;> fin_cases j <;> rfl
  simp [diagonalCoefficient, h]

private def chamberExponents : Fin 4 → ℤ := ![900, 1200, 1010, 1001]

private def chamberParameter {R : Type*} [CommRing R] (t : Rˣ) : Fin 4 → Rˣ :=
  fun j => t ^ chamberExponents j

private theorem chamberExponents_weight (z : Coord) :
    (∑ j, chamberExponents j * diagonalExponents z j) = coordinateWeight z := by
  fin_cases z <;> rfl

private theorem diagonalCoefficient_chamber {R : Type*} [CommRing R] (t : Rˣ) (z : Coord) :
    diagonalCoefficient (chamberParameter t) z = t ^ coordinateWeight z := by
  simp only [diagonalCoefficient, chamberParameter, ← _root_.zpow_mul]
  rw [← chamberExponents_weight, Fin.sum_univ_four, Fin.prod_univ_four]
  simp only [_root_.zpow_add]

private theorem normTerms_weight (term : List Coord × ℤ) (ht : term ∈ normTerms)
    (j : Fin 4) : (term.1.map (fun z => diagonalExponents z j)).sum = 0 := by
  suffices hc : normTerms.all (fun t => (t.1.map (fun z => diagonalExponents z j)).sum == 0) = true
    from beq_iff_eq.mp (List.all_eq_true.mp hc _ ht)
  fin_cases j <;> rfl

private theorem prod_diagonalCoefficient {R : Type*} [CommRing R]
    (s : Fin 4 → Rˣ) (indices : List Coord) :
    (indices.map (diagonalCoefficient s)).prod =
      ∏ j, s j ^ (indices.map (fun z => diagonalExponents z j)).sum := by
  induction indices with
  | nil => simp
  | cons z indices ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, ih, diagonalCoefficient, _root_.zpow_add,
      Finset.prod_mul_distrib]

private theorem weightedMonomial_eq {R : Type*} [CommRing R]
    (s : Fin 4 → Rˣ) (x : Coord → R) (term : List Coord × ℤ) (ht : term ∈ normTerms) :
    (term.1.map (fun z => (diagonalCoefficient s z : R) * x z)).prod =
      (term.1.map x).prod := by
  rw [List.prod_map_mul]
  have h : (term.1.map (diagonalCoefficient s)).prod = 1 := by
    rw [prod_diagonalCoefficient]
    simp [normTerms_weight term ht]
  change (term.1.map (Units.coeHom R ∘ diagonalCoefficient s)).prod * _ = _
  rw [List.prod_map_hom, h, map_one, one_mul]

private theorem diagonal_norm {R : Type*} [CommRing R] (s : Fin 4 → Rˣ)
    (x : Coord → R) :
    matrixNorm (unflatten (fun z => (diagonalCoefficient s z : R) * x z)) =
      matrixNorm (unflatten x) := by
  rw [← evaluateTerms_norm, ← evaluateTerms_norm]
  unfold evaluateTerms
  apply congrArg List.sum
  exact List.map_congr_left (fun t ht => congrArg ((t.2 : R) * ·) (weightedMonomial_eq s x t ht))

private def diagonalEquiv {R : Type*} [CommRing R] (s : Fin 4 → Rˣ) :
    (Coord → R) ≃ₗ[R] (Coord → R) where
  toFun x z := (diagonalCoefficient s z : R) * x z
  invFun x z := ((diagonalCoefficient s z)⁻¹ : Rˣ).val * x z
  left_inv x := funext fun z => by simp [← mul_assoc]
  right_inv x := funext fun z => by simp [← mul_assoc]
  map_add' x y := funext fun z => mul_add _ _ _
  map_smul' r x := funext fun z => mul_left_comm _ _ _

private def diagonalModel {R : Type*} [CommRing R] (s : Fin 4 → Rˣ) :
    Model R ≃ₗ[R] Model R :=
  (modelCoordinateEquiv R).trans ((diagonalEquiv s).trans (modelCoordinateEquiv R).symm)

private theorem diagonalModel_coordinates {R : Type*} [CommRing R] (s : Fin 4 → Rˣ)
    (x : Model R) (z : Coord) :
    modelCoordinateEquiv R (diagonalModel s x) z =
      (diagonalCoefficient s z : R) * modelCoordinateEquiv R x z :=
  congrFun ((modelCoordinateEquiv R).apply_symm_apply _) z

private theorem diagonalModel_natural {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (s : Fin 4 → Rˣ) (x : Model R) :
    mapModel f (diagonalModel s x) =
      diagonalModel (Units.map f.toMonoidHom ∘ s) (mapModel f x) := by
  apply (modelCoordinateEquiv S).injective
  rw [modelCoordinateEquiv_natural]
  funext z
  rw [Function.comp_apply, diagonalModel_coordinates, diagonalModel_coordinates,
    modelCoordinateEquiv_natural, Function.comp_apply, map_mul, diagonalCoefficient_map f]
  rfl

private theorem diagonalModel_fixes_frame {R : Type*} [CommRing R]
    (s : Fin 4 → Rˣ) (i : Slot) :
    diagonalModel s (frameAxis i) = frameAxis i := by
  apply (modelCoordinateEquiv R).injective
  funext z
  rw [diagonalModel_coordinates, modelCoordinateEquiv_axis]
  by_cases hz : z = a i i
  · simp [hz, diagonalCoefficient_axis]
  · simp [hz]

private theorem diagonalModel_preserves_unit {R : Type*} [CommRing R] (s : Fin 4 → Rˣ) :
    diagonalModel s cubicUnit = cubicUnit := by
  apply (modelCoordinateEquiv R).injective
  funext z
  rw [diagonalModel_coordinates, modelCoordinateEquiv_unit]
  fin_cases z <;> simp [unitVector, a, coord, diagonalCoefficient, diagonalExponents,
    Fin.prod_univ_four]

private theorem diagonalModel_norm {R : Type*} [CommRing R] (s : Fin 4 → Rˣ)
    (x : Model R) : splitNorm (diagonalModel s x) = splitNorm x := by
  simp only [modelCoordinateEquiv_norm]
  exact (congrArg (fun v => matrixNorm (unflatten v))
    (funext fun z => diagonalModel_coordinates s x z)).trans (diagonal_norm s _)

set_option maxHeartbeats 400000 in
private theorem diagonalModel_isSplitAutomorphism {R : Type} [CommRing R]
    (s : Fin 4 → Rˣ) : IsSplitAutomorphism (diagonalModel s) := by
  apply splitAutomorphism_of_natural_norm _ (diagonalModel_preserves_unit s)
  intro S _ _
  let f := algebraMap R S
  let t : Fin 4 → Sˣ := Units.map f.toMonoidHom ∘ s
  exact ⟨diagonalModel t, diagonalModel_natural f s, diagonalModel_norm t⟩

/-- The diagonal action in split Albert coordinates. -/
def diagonalAction (R : Type*) [CommRing R] : (Fin 4 → Rˣ) →* (Model R ≃ₗ[R] Model R) where
  toFun := diagonalModel
  map_one' := by
    apply LinearEquiv.ext
    intro x
    apply (modelCoordinateEquiv R).injective
    funext z
    change modelCoordinateEquiv R (diagonalModel 1 x) z = modelCoordinateEquiv R x z
    simp [diagonalModel_coordinates, diagonalCoefficient_one]
  map_mul' s t := by
    apply LinearEquiv.ext
    intro x
    apply (modelCoordinateEquiv R).injective
    funext z
    change modelCoordinateEquiv R (diagonalModel (s * t) x) z =
      modelCoordinateEquiv R (diagonalModel s (diagonalModel t x)) z
    simp only [diagonalModel_coordinates, diagonalCoefficient_mul, Units.val_mul, mul_assoc]

private theorem weightedRow_chamber {R : Type*} [CommRing R] (t : Rˣ) (j : Fin 28)
    (x : Coord → R) (r : Coord) :
    evaluateRow (generator j) (fun z => (↑(t ^ coordinateWeight z) : R) * x z) r =
      (↑(t ^ (coordinateWeight r - generatorWeight j)) : R) * evaluateRow (generator j) x r := by
  unfold evaluateRow
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  rintro ⟨z, c⟩ hz
  have hmem : (r, z, c) ∈ generator j := by
    unfold rowTerms at hz
    obtain ⟨⟨r', z', c'⟩, hp, hp'⟩ := List.mem_map.mp hz
    obtain ⟨hm, hr⟩ := List.mem_filter.mp hp
    have he : r' = r := beq_iff_eq.mp hr
    subst r'
    cases hp'
    exact hm
  have hw := tangentEntry_weight hmem
  dsimp only
  rw [show coordinateWeight z = coordinateWeight r - generatorWeight j by omega]
  ring

/-- The tangent operators have the stated adjoint weights under the
diagonal action. -/
theorem tangentOperator_chamber {R : Type*} [CommRing R] (t : Rˣ) (j : Fin 28)
    (x : Model R) :
    diagonalAction R (chamberParameter t) (tangentOperator R j x) =
      (↑(t ^ generatorWeight j) : R) •
        tangentOperator R j (diagonalAction R (chamberParameter t) x) := by
  apply (modelCoordinateEquiv R).injective
  funext z
  change modelCoordinateEquiv R (diagonalModel (chamberParameter t) (tangentOperator R j x)) z =
    modelCoordinateEquiv R ((↑(t ^ generatorWeight j) : R) •
      tangentOperator R j (diagonalModel (chamberParameter t) x)) z
  rw [diagonalModel_coordinates, diagonalCoefficient_chamber, tangentOperator_coordinates,
    map_smul, Pi.smul_apply, tangentOperator_coordinates]
  have h : modelCoordinateEquiv R (diagonalModel (chamberParameter t) x) =
      fun r => (↑(t ^ coordinateWeight r) : R) * modelCoordinateEquiv R x r := by
    funext r
    rw [diagonalModel_coordinates, diagonalCoefficient_chamber]
  rw [h, weightedRow_chamber, smul_eq_mul, ← mul_assoc, ← Units.val_mul, ← _root_.zpow_add,
    add_sub_cancel]

end DiagonalAction

/-- The frame used in the minors is in the split Albert automorphism orbit. -/
theorem exists_movedFrame (R : Type) [CommRing R] :
    ∃ g : Model R ≃ₗ[R] Model R, IsSplitAutomorphism g ∧
      ∀ i, modelCoordinateEquiv R (g (frameAxis i)) = movedFrame i := by
  refine ⟨frameWordModel R frameMoves, frameWordModel_isSplitAutomorphism R _, fun i => ?_⟩
  rw [frameWordModel_coordinates, modelCoordinateEquiv_axis, movedFrame_eq_frameWord]

/-- On the frame orbit the two lowest-coordinate evaluations give the
distinct projective values [1:0] and [0:1]. -/
theorem exists_distinct_invariant_values (R : Type) [CommRing R] :
    ∃ (g₀ g₁ : Model R ≃ₗ[R] Model R), IsSplitAutomorphism g₀ ∧ IsSplitAutomorphism g₁ ∧
      modelCoordinateEquiv R (g₀ (frameAxis 0)) (a 2 0) = 1 ∧
      modelCoordinateEquiv R (g₀ (frameAxis 1)) (a 2 0) = 0 ∧
      modelCoordinateEquiv R (g₁ (frameAxis 0)) (a 2 0) = 0 ∧
      modelCoordinateEquiv R (g₁ (frameAxis 1)) (a 2 0) = 1 := by
  refine ⟨frameWordModel R firstInvariantWord, frameWordModel R secondInvariantWord,
    frameWordModel_isSplitAutomorphism R _, frameWordModel_isSplitAutomorphism R _, ?_⟩
  simp only [frameWordModel_coordinates, modelCoordinateEquiv_axis]
  exact ⟨(firstInvariantWord_values R).1, (firstInvariantWord_values R).2,
    (secondInvariantWord_values R).1, (secondInvariantWord_values R).2⟩

/-- Evaluation of an endomorphism on the translated frame, in the same
row order as the integral matrix. -/
def translatedFrameEvaluation (k : Type*) [Field k] :
    Module.End k (Model k) →ₗ[k] (Fin 81 → k) where
  toFun D i := modelCoordinateEquiv k
    (D ((modelCoordinateEquiv k).symm (movedFrame (frameIndex i)))) (coordinateIndex i)
  map_add' D E := by
    funext i
    simp only [LinearMap.add_apply, map_add, Pi.add_apply]
  map_smul' c D := by
    funext i
    simp only [LinearMap.smul_apply, map_smul, RingHom.id_apply, Pi.smul_apply]

private theorem translatedFrameEvaluation_column (k : Type*) [Field k] (j : Fin 28) :
    translatedFrameEvaluation k (tangentOperator k j) =
      (integralEvaluation.map (Int.castRingHom k)).col j := by
  funext i
  let f := Int.castRingHom k
  let l := frameIndex i
  let r := coordinateIndex i
  change modelCoordinateEquiv k (tangentOperator k j
      ((modelCoordinateEquiv k).symm (movedFrame l))) r =
    f (evaluationEntry (movedFrame l) r j)
  rw [tangentOperator_coordinates, LinearEquiv.apply_symm_apply, ← movedFrame_map f l,
    evaluateRow_map]
  exact congrArg f (evaluateRow_eq (generator j) (movedFrame l) r)

private theorem rank_le_of_evaluated_columns (k : Type*) [Field k] {n : ℕ}
    (A : Matrix (Fin 81) (Fin n) k) (U : Submodule k (Module.End k (Model k)))
    (columns : ∀ j, ∃ x : U, translatedFrameEvaluation k x.val = A.col j) :
    A.rank ≤ Module.finrank k ((translatedFrameEvaluation k).domRestrict U).range := by
  rw [Matrix.rank_eq_finrank_span_cols]
  apply Submodule.finrank_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact columns j

/-- For a 24-dimensional space containing the positive tangent operators, the
kernel of evaluation on the translated frame has dimension at most three. -/
theorem positive_evaluation_kernel_bound (k : Type*) [Field k]
    (U : Submodule k (Module.End k (Model k))) (hdim : Module.finrank k U ≤ 24)
    (hmem : ∀ j : Fin 24, tangentOperator k (positiveColumns j) ∈ U) :
    Module.finrank k ((translatedFrameEvaluation k).domRestrict U).ker ≤ 3 := by
  have h := rank_le_of_evaluated_columns k (integralPositiveEvaluation.map (Int.castRingHom k)) U
    (fun j => ⟨⟨tangentOperator k (positiveColumns j), hmem j⟩,
      translatedFrameEvaluation_column k (positiveColumns j)⟩)
  have h₁ := (positiveEvaluation_rank k).trans h
  have h₂ := LinearMap.finrank_range_add_finrank_ker (K := k) (V := U) (V₂ := Fin 81 → k)
    ((translatedFrameEvaluation k).domRestrict U)
  omega

/-- The positive and zero weight operators give the analogous bound five in
a 28-dimensional space. -/
theorem full_evaluation_kernel_bound (k : Type*) [Field k]
    (U : Submodule k (Module.End k (Model k))) (hdim : Module.finrank k U ≤ 28)
    (hmem : ∀ j, tangentOperator k j ∈ U) :
    Module.finrank k ((translatedFrameEvaluation k).domRestrict U).ker ≤ 5 := by
  have h := rank_le_of_evaluated_columns k (integralEvaluation.map (Int.castRingHom k)) U
    (fun j => ⟨⟨tangentOperator k j, hmem j⟩, translatedFrameEvaluation_column k j⟩)
  have h₁ := (fullEvaluation_rank k).trans h
  have h₂ := LinearMap.finrank_range_add_finrank_ker (K := k) (V := U) (V₂ := Fin 81 → k)
    ((translatedFrameEvaluation k).domRestrict U)
  omega

/-- Evaluation of the fixed tangent operators on a triple of coordinate vectors. -/
def evaluationMatrix {R : Type*} [CommRing R] (v : Slot → Coord → R) :
    Matrix (Fin 81) (Fin 28) R :=
  Matrix.of fun i j => evaluateRow (generator j) (v (frameIndex i)) (coordinateIndex i)

theorem evaluationMatrix_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (v : Slot → Coord → R) :
    evaluationMatrix (fun i => f ∘ v i) = (evaluationMatrix v).map f := by
  ext i j
  exact evaluateRow_map f _ _ _

/-- The product of the selected positive and full minors. This is functorial
in the scalar ring, so its nonvanishing defines an open condition. -/
def frameRankPolynomial {R : Type*} [CommRing R] (v : Slot → Coord → R) : R :=
  ((evaluationMatrix v).submatrix positiveRows (positiveColumns ∘ positiveMinorColumns)).det *
    ((evaluationMatrix v).submatrix borelRows borelMinorColumns).det

theorem frameRankPolynomial_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (v : Slot → Coord → R) :
    frameRankPolynomial (fun i => f ∘ v i) = f (frameRankPolynomial v) := by
  simp only [frameRankPolynomial, evaluationMatrix_map, map_mul, Matrix.submatrix_map,
    RingHom.map_det]
  rfl

private theorem evaluationMatrix_movedFrame (k : Type*) [CommRing k] :
    evaluationMatrix (movedFrame (R := k)) = integralEvaluation.map (Int.castRingHom k) := by
  let f := Int.castRingHom k
  rw [show movedFrame (R := k) = fun i => f ∘ movedFrame (R := ℤ) i from
    funext fun i => (movedFrame_map f i).symm, evaluationMatrix_map]
  congr 1
  ext i j
  exact evaluateRow_eq _ _ _

private theorem det_minor_ne_zero {k : Type*} [Field k] {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℤ} (h : B * A = 1) :
    (A.map (Int.castRingHom k)).det ≠ 0 := by
  have hd : (B.map (Int.castRingHom k)).det * (A.map (Int.castRingHom k)).det = 1 := by
    rw [← Matrix.det_mul, ← Matrix.map_mul,
      h, Matrix.map_one _ (map_zero _) (map_one _), Matrix.det_one]
  intro hc
  rw [hc, mul_zero] at hd
  exact zero_ne_one hd

/-- Both minors are nonzero for the translated frame in every characteristic. -/
theorem movedFrame_rankPolynomial_ne_zero (k : Type*) [Field k] :
    frameRankPolynomial (movedFrame (R := k)) ≠ 0 := by
  rw [frameRankPolynomial, evaluationMatrix_movedFrame]
  apply mul_ne_zero
  · rw [Matrix.submatrix_map]
    exact det_minor_ne_zero positiveInverse_mul
  · rw [Matrix.submatrix_map]
    exact det_minor_ne_zero borelInverse_mul

theorem evaluationMatrix_rank_of_rankPolynomial {k : Type*} [Field k]
    {v : Slot → Coord → k} (h : frameRankPolynomial v ≠ 0) :
    21 ≤ ((evaluationMatrix v).submatrix id positiveColumns).rank ∧
    23 ≤ (evaluationMatrix v).rank := by
  have h₂ := (mul_ne_zero_iff.mp h).2
  have h₁ := (mul_ne_zero_iff.mp h).1
  constructor
  · have hr := Matrix.rank_of_det_ne_zero h₁
    rw [Fintype.card_fin] at hr
    exact hr ▸ Matrix.rank_submatrix_le ((evaluationMatrix v).submatrix id positiveColumns)
      positiveRows positiveMinorColumns
  · have hr := Matrix.rank_of_det_ne_zero h₂
    rw [Fintype.card_fin] at hr
    exact hr ▸ Matrix.rank_submatrix_le (evaluationMatrix v) borelRows borelMinorColumns

/-- Rank conditions expressed by nonzero polynomials can be met with parameters
from an infinite ground field, even when the coefficients lie in an extension. -/
theorem polynomial_nonzero_at_ground_parameters {k K I : Type*} [Field k] [Field K]
    [Algebra k K] [Infinite k] (p : MvPolynomial I K) (hp : p ≠ 0) :
    ∃ x : I → k, (∀ i, x i ≠ 0) ∧ MvPolynomial.eval (algebraMap k K ∘ x) p ≠ 0 := by
  classical
  let boxes : I → Set K := fun _ => algebraMap k K '' ({0}ᶜ : Set k)
  have hb (i : I) : (boxes i).Infinite := by
    exact (Set.finite_singleton (0 : k)).infinite_compl.image
      (RingHom.injective (algebraMap k K)).injOn
  by_contra! h
  apply hp
  apply MvPolynomial.funext_set boxes hb
  intro y hy
  have h' (i : I) : ∃ x : k, x ≠ 0 ∧ algebraMap k K x = y i := hy i trivial
  choose x hx hxy using h'
  rw [show y = algebraMap k K ∘ x from funext fun i => (hxy i).symm]
  simpa only [map_zero] using h x hx

/-- Simultaneous evaluation on the three vectors of an ordered frame. -/
def frameTangentEvaluation (k : Type*) [Field k] (v : Slot → Model k) :
    Module.End k (Model k) →ₗ[k] (Fin 81 → k) where
  toFun D i := modelCoordinateEquiv k (D (v (frameIndex i))) (coordinateIndex i)
  map_add' D E := funext fun i => by simp only [LinearMap.add_apply, map_add, Pi.add_apply]
  map_smul' c D := funext fun i => by
    simp only [LinearMap.smul_apply, map_smul, RingHom.id_apply, Pi.smul_apply]

theorem mem_ker_frameTangentEvaluation (k : Type*) [Field k] (v : Slot → Model k)
    (D : Module.End k (Model k)) :
    D ∈ (frameTangentEvaluation k v).ker ↔ ∀ j, D (v j) = 0 := by
  constructor
  · intro h j
    apply (modelCoordinateEquiv k).injective
    funext q
    let i : Fin 81 := ⟨27 * j.val + q.val, by omega⟩
    have hj : frameIndex i = j := by
      apply Fin.ext
      change (27 * j.val + q.val) / 27 = j.val
      omega
    have hq : coordinateIndex i = q := by
      apply Fin.ext
      change (27 * j.val + q.val) % 27 = q.val
      omega
    have e := congrFun (LinearMap.mem_ker.mp h) i
    change modelCoordinateEquiv k (D (v (frameIndex i))) (coordinateIndex i) = 0 at e
    rw [hj, hq] at e
    simpa only [map_zero, Pi.zero_apply] using e
  · intro h
    apply LinearMap.mem_ker.mpr
    funext i
    change modelCoordinateEquiv k (D (v (frameIndex i))) (coordinateIndex i) = 0
    rw [h, map_zero, Pi.zero_apply]

private theorem frameTangentEvaluation_column (k : Type*) [Field k]
    (v : Slot → Model k) (j : Fin 28) :
    frameTangentEvaluation k v (tangentOperator k j) =
      (evaluationMatrix (modelCoordinateEquiv k ∘ v)).col j := by
  funext i
  exact congrFun (tangentOperator_coordinates k j (v (frameIndex i))) (coordinateIndex i)

private theorem frameEvaluation_span_cols {k : Type*} [Field k] {n : ℕ}
    (v : Slot → Model k) (E : Submodule k (Module.End k (Model k))) (j : Fin n → Fin 28)
    (hE : ∀ i, tangentOperator k (j i) ∈ E) :
    ((evaluationMatrix (modelCoordinateEquiv k ∘ v)).submatrix id j).rank ≤
      Module.finrank k (((frameTangentEvaluation k v).domRestrict E).range) := by
  rw [Matrix.rank_eq_finrank_span_cols]
  apply Submodule.finrank_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact ⟨⟨tangentOperator k (j i), hE i⟩, frameTangentEvaluation_column k v (j i)⟩

/-- The rank condition gives the Lie-kernel bounds for every translated frame
where the selected minors are nonzero. -/
theorem evaluationKernelBounds {k : Type*} [Field k] (v : Slot → Model k)
    (hv : frameRankPolynomial (modelCoordinateEquiv k ∘ v) ≠ 0)
    (U B : Submodule k (Module.End k (Model k)))
    (hUdim : Module.finrank k U ≤ 24) (hBdim : Module.finrank k B ≤ 28)
    (hU : ∀ j, tangentOperator k (positiveColumns j) ∈ U)
    (hB : ∀ j, tangentOperator k j ∈ B) :
    Module.finrank k ((frameTangentEvaluation k v).domRestrict U).ker ≤ 3 ∧
    Module.finrank k ((frameTangentEvaluation k v).domRestrict B).ker ≤ 5 := by
  obtain ⟨hp, hf⟩ := evaluationMatrix_rank_of_rankPolynomial hv
  have hUp := hp.trans (frameEvaluation_span_cols v U positiveColumns hU)
  have hBp := hf.trans (frameEvaluation_span_cols v B id hB)
  have hpdim := LinearMap.finrank_range_add_finrank_ker (K := k) (V := U) (V₂ := Fin 81 → k) ((frameTangentEvaluation k v).domRestrict U)
  have hfdim := LinearMap.finrank_range_add_finrank_ker (K := k) (V := B) (V₂ := Fin 81 → k) ((frameTangentEvaluation k v).domRestrict B)
  omega

private def generatorPivot (j : Fin 28) : Coord × Coord :=
  let e := (generator j).getLast?.getD (0, 0, 0)
  (e.1, e.2.1)

private def pivotCheck : Bool :=
  (List.finRange 28).all fun i =>
    (List.finRange 28).all fun j =>
      evaluationEntry (Pi.single (generatorPivot i).2 1) (generatorPivot i).1 j ==
        (if i = j then 1 else 0)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem pivotCheck_correct : pivotCheck = true := by
  decide

private theorem generatorPivot_int (i j : Fin 28) :
    evaluationEntry (Pi.single (generatorPivot i).2 1) (generatorPivot i).1 j =
      if i = j then 1 else 0 :=
  beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp pivotCheck_correct
    i (List.mem_finRange i)) j (List.mem_finRange j))

private def pivotEvaluation (R : Type*) [CommRing R] : Module.End R (Model R) →ₗ[R] (Fin 28 → R) where
  toFun T i := modelCoordinateEquiv R (T ((modelCoordinateEquiv R).symm
    (Pi.single (generatorPivot i).2 1))) (generatorPivot i).1
  map_add' T U := by funext i; simp only [LinearMap.add_apply, map_add, Pi.add_apply]
  map_smul' c T := by
    funext i
    simp only [LinearMap.smul_apply, map_smul, RingHom.id_apply, Pi.smul_apply]

private theorem pivotEvaluation_generator (R : Type*) [CommRing R] (j : Fin 28) :
    pivotEvaluation R (tangentOperator R j) = Pi.single j 1 := by
  funext i
  let f := Int.castRingHom R
  let z := generatorPivot i
  have hsingle : f ∘ Pi.single z.2 1 = Pi.single z.2 1 := by
    funext l
    by_cases h : l = z.2 <;> simp [h, f]
  have e : evaluateRow (generator j) (Pi.single z.2 1) z.1 =
      f (evaluationEntry (Pi.single z.2 1) z.1 j) := by
    rw [← hsingle, evaluateRow_map]
    exact congrArg f (evaluateRow_eq _ _ _)
  change modelCoordinateEquiv R
    (tangentOperator R j ((modelCoordinateEquiv R).symm (Pi.single z.2 1))) z.1 = _
  rw [tangentOperator_coordinates, LinearEquiv.apply_symm_apply, e, generatorPivot_int]
  by_cases h : i = j <;> simp [h, f]

/-- The positive and zero weight directions are independent after any scalar
extension. Each direction has an entry equal to one used by no other column. -/
theorem tangentOperator_linearIndependent (R : Type*) [CommRing R] :
    LinearIndependent R (tangentOperator R) := by
  apply LinearIndependent.of_comp (pivotEvaluation R)
  have h : (pivotEvaluation R) ∘ tangentOperator R = Pi.basisFun R (Fin 28) := by
    funext j
    rw [Function.comp_apply, Pi.basisFun_apply]
    exact pivotEvaluation_generator R j
  rw [h]
  exact (Pi.basisFun R (Fin 28)).linearIndependent

private def elementaryModelEquiv {R : Type*} [CommRing R] (i j : Slot) (h : i ≠ j)
    (t : R) : Model R ≃ₗ[R] Model R :=
  (modelCoordinateEquiv R).trans ((elementaryLinearEquiv i j h t).trans (modelCoordinateEquiv R).symm)

private theorem elementaryModelEquiv_coordinates {R : Type*} [CommRing R] (i j : Slot)
    (h : i ≠ j) (t : R) (x : Model R) :
    modelCoordinateEquiv R (elementaryModelEquiv i j h t x) =
      elementaryAction i j t (modelCoordinateEquiv R x) :=
  (modelCoordinateEquiv R).apply_symm_apply _

private theorem elementaryModelEquiv_isSplitAutomorphism {R : Type} [CommRing R]
    (i j : Slot) (h : i ≠ j) (t : R) :
    IsSplitAutomorphism (elementaryModelEquiv i j h t) := by
  apply splitAutomorphism_of_natural_norm
  · apply (modelCoordinateEquiv R).injective
    rw [elementaryModelEquiv_coordinates, modelCoordinateEquiv_unit]
    exact elementaryAction_unit i j h t
  · intro S _ _
    let f := algebraMap R S
    refine ⟨elementaryModelEquiv i j h (f t), ?_, ?_⟩
    · intro x
      apply (modelCoordinateEquiv S).injective
      rw [modelCoordinateEquiv_natural, elementaryModelEquiv_coordinates,
        elementaryModelEquiv_coordinates, modelCoordinateEquiv_natural, elementaryAction_map]
    · intro x
      rw [modelCoordinateEquiv_norm, modelCoordinateEquiv_norm (x := x),
        elementaryModelEquiv_coordinates, ← evaluateTerms_norm, ← evaluateTerms_norm]
      exact elementaryAction_norm i j h (f t) (modelCoordinateEquiv S x)

/-- On this translated frame the lowest-coordinate ratio varies to first
order along the elementary `g₁₀(t)` curve. The two coordinates on the curve
are exactly `(1, -t)`, including in positive characteristic. -/
theorem exists_transverse_invariant_curve (R : Type) [CommRing R] :
    ∃ (g : Model R ≃ₗ[R] Model R),
      IsSplitAutomorphism g ∧
      ∀ t : R,
        let h := elementaryModelEquiv 1 0 (by decide) t
        IsSplitAutomorphism h ∧
          modelCoordinateEquiv R (h (g (frameAxis 0))) (a 2 0) = 1 ∧
          modelCoordinateEquiv R (h (g (frameAxis 1))) (a 2 0) = -t := by
  let g₀ := elementaryModelEquiv 2 0 (by decide) (1 : R)
  let g₁ := elementaryModelEquiv 2 1 (by decide) (1 : R)
  have h₀ : IsSplitAutomorphism g₀ := elementaryModelEquiv_isSplitAutomorphism _ _ _ _
  have h₁ : IsSplitAutomorphism g₁ := elementaryModelEquiv_isSplitAutomorphism _ _ _ _
  refine ⟨g₀.trans g₁, ?_, fun t => ?_⟩
  · constructor
    · exact (congrArg g₁ h₀.1).trans h₁.1
    · intro x y
      simp only [LinearEquiv.trans_apply, h₀.2, h₁.2]
  · dsimp only
    refine ⟨elementaryModelEquiv_isSplitAutomorphism 1 0 (by decide) t, ?_, ?_⟩ <;>
      simp only [g₀, g₁, LinearEquiv.trans_apply, elementaryModelEquiv_coordinates,
        modelCoordinateEquiv_axis] <;>
      simp [elementaryAction, a, coord]

section SchemeAction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs (GroupScheme AffineAlgebraicGroup ClosedSubgroup)
open Albert.ReductiveFiberSpecification (SplitAction)

noncomputable section

private def modelBasisVector (R : Type) [CommRing R] (j : Coord) : Model R :=
  (modelCoordinateEquiv R).symm (Pi.single j 1)

private theorem mapModel_basisVector {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (j : Coord) :
    mapModel f (modelBasisVector R j) = modelBasisVector S j := by
  apply (modelCoordinateEquiv S).injective
  rw [modelCoordinateEquiv_natural]
  simp only [modelBasisVector, LinearEquiv.apply_symm_apply]
  funext i
  by_cases h : i = j <;> simp [h]

private theorem linearEquiv_ext_of_mapModel {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (g h : Model S ≃ₗ[S] Model S)
    (e : ∀ x, g (mapModel f x) = h (mapModel f x)) : g = h := by
  apply LinearEquiv.toLinearMap_injective
  refine ((Pi.basisFun S Coord).map (modelCoordinateEquiv S).symm).ext fun j => ?_
  rw [Module.Basis.map_apply, Pi.basisFun_apply]
  change g (modelBasisVector S j) = h (modelBasisVector S j)
  rw [← mapModel_basisVector f j]
  exact e _

variable {k : Type} [Field k]

private def liftActionPoint {G : GroupScheme k} (a : SplitAction G) (R : TestAlgebra k)
    (g : Model R ≃ₗ[R] Model R) (hg : IsSplitAutomorphism g) : Points G.X R :=
  (show g ∈ Set.range (a.action R) from (a.image R).symm ▸ hg).choose

private theorem liftActionPoint_action {G : GroupScheme k} (a : SplitAction G)
    (R : TestAlgebra k) (g : Model R ≃ₗ[R] Model R) (hg : IsSplitAutomorphism g) :
    a.action R (liftActionPoint a R g hg) = g :=
  (show g ∈ Set.range (a.action R) from (a.image R).symm ▸ hg).choose_spec

private theorem splitAction_mem {G : GroupScheme k} (a : SplitAction G) (R : TestAlgebra k)
    (x : Points G.X R) : IsSplitAutomorphism (a.action R x) := by
  change a.action R x ∈ {g | IsSplitAutomorphism g}
  rw [← a.image R]
  exact ⟨x, rfl⟩

private def actionPointEquiv {G H : GroupScheme k} (a : SplitAction G) (b : SplitAction H)
    (R : TestAlgebra k) : Points G.X R ≃* Points H.X R where
  toFun x := liftActionPoint b R (a.action R x) (splitAction_mem a R x)
  invFun y := liftActionPoint a R (b.action R y) (splitAction_mem b R y)
  left_inv x := by
    apply a.injective R
    simp only [liftActionPoint_action]
  right_inv y := by
    apply b.injective R
    simp only [liftActionPoint_action]
  map_mul' x y := by
    apply b.injective R
    simp only [map_mul, liftActionPoint_action]

private theorem actionPointEquiv_action {G H : GroupScheme k} (a : SplitAction G)
    (b : SplitAction H) (R : TestAlgebra k) (x : Points G.X R) :
    b.action R (actionPointEquiv a b R x) = a.action R x :=
  liftActionPoint_action b R _ (splitAction_mem a R x)

private def actionPointIso {G H : GroupScheme k} (a : SplitAction G) (b : SplitAction H) :
    (groupPointsFunctor k).obj G ≅ (groupPointsFunctor k).obj H :=
  NatIso.ofComponents (fun R => (actionPointEquiv a b R).toGrpIso) fun {R S} f => by
    apply GrpCat.ext
    intro x
    change Points G.X R at x
    change actionPointEquiv a b S (mapPoints f x) = mapPoints f (actionPointEquiv a b R x)
    apply b.injective S
    rw [actionPointEquiv_action]
    apply linearEquiv_ext_of_mapModel f.hom.toRingHom
    intro y
    rw [← a.natural f x, ← b.natural f (actionPointEquiv a b R x), actionPointEquiv_action]

private def coordinateEnd {G : GroupScheme k} (a : SplitAction G) (R : TestAlgebra k) :
    Points G.X R →* Module.End R (Coord → R) where
  toFun g := (modelCoordinateEquiv R).toLinearMap.comp
    ((a.action R g).toLinearMap.comp (modelCoordinateEquiv R).symm.toLinearMap)
  map_one' := by
    apply LinearMap.ext
    intro x
    change modelCoordinateEquiv R (a.action R 1 ((modelCoordinateEquiv R).symm x)) = x
    rw [map_one]
    exact (modelCoordinateEquiv R).apply_symm_apply x
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    change modelCoordinateEquiv R (a.action R (g * h) ((modelCoordinateEquiv R).symm x)) =
      modelCoordinateEquiv R (a.action R g ((modelCoordinateEquiv R).symm
        (modelCoordinateEquiv R (a.action R h ((modelCoordinateEquiv R).symm x)))))
    rw [map_mul, (modelCoordinateEquiv R).symm_apply_apply]
    rfl

private def coordinateMatrixHom {G : GroupScheme k} (a : SplitAction G) (R : TestAlgebra k) :
    Points G.X R →* Matrix.GeneralLinearGroup Coord R :=
  Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom.comp (coordinateEnd a R).toHomUnits

private theorem coordinateMatrixHom_mulVec {G : GroupScheme k} (a : SplitAction G)
    (R : TestAlgebra k) (g : Points G.X R) (v : Coord → R) :
    (coordinateMatrixHom a R g).val *ᵥ v =
      modelCoordinateEquiv R (a.action R g ((modelCoordinateEquiv R).symm v)) := by
  change (coordinateMatrixHom a R g).val.mulVecLin v = _
  rw [← Matrix.GeneralLinearGroup.toLin_apply]
  change ((Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.toLin.symm
    ((coordinateEnd a R).toHomUnits g))).val : Module.End R _) v = _
  rw [MulEquiv.apply_symm_apply]
  rfl

private theorem coordinateMatrixHom_entry {G : GroupScheme k} (a : SplitAction G)
    (R : TestAlgebra k) (g : Points G.X R) (i j : Coord) :
    (coordinateMatrixHom a R g).val i j =
      modelCoordinateEquiv R (a.action R g (modelBasisVector R j)) i := by
  have h := congrFun (coordinateMatrixHom_mulVec a R g (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at h
  exact h

private theorem coordinateMatrixHom_injective {G : GroupScheme k} (a : SplitAction G)
    (R : TestAlgebra k) : Function.Injective (coordinateMatrixHom a R) := by
  intro g h e
  apply a.injective R
  apply LinearEquiv.ext
  intro x
  apply (modelCoordinateEquiv R).injective
  simpa only [LinearEquiv.symm_apply_apply, coordinateMatrixHom_mulVec] using
    congrArg (fun m : Matrix.GeneralLinearGroup Coord R => m.val *ᵥ modelCoordinateEquiv R x) e

private def matrixPointRepresentation {G : GroupScheme k} (a : SplitAction G) :
    (groupPointsFunctor k).obj G ⟶ Specs.StandardGroups.generalLinearPoints k Coord where
  app R := GrpCat.ofHom (coordinateMatrixHom a R)
  naturality {R S} f := by
    apply GrpCat.ext
    intro g
    change Points G.X R at g
    apply Units.ext
    ext i j
    change (coordinateMatrixHom a S (mapPoints f g)).val i j =
      f.hom ((coordinateMatrixHom a R g).val i j)
    rw [coordinateMatrixHom_entry, coordinateMatrixHom_entry]
    have h := a.natural f g (modelBasisVector R j)
    rw [mapModel_basisVector] at h
    rw [← h, modelCoordinateEquiv_natural]
    rfl

/-- The scheme representation in the three-matrix coordinate basis. -/
def matrixRepresentation (G : AffineAlgebraicGroup k) (a : SplitAction G.val) :
    G.val ⟶ (StandardGroups.generalLinearGroup k Coord).val :=
  (groupHomEquiv _ _ G.property.1).symm
    (matrixPointRepresentation a ≫ (StandardGroups.generalLinearGroupPointsIso k Coord).inv)

theorem matrixRepresentation_apply (G : AffineAlgebraicGroup k) (a : SplitAction G.val)
    (R : TestAlgebra k) (g : Points G.val.X R) :
    (StandardGroups.generalLinearGroupPointsIso k Coord).hom.app R
      (g ≫ (matrixRepresentation G a).hom.hom) = coordinateMatrixHom a R g := by
  have h := (groupHomEquiv G.val _ G.property.1).apply_symm_apply
    (matrixPointRepresentation a ≫ (StandardGroups.generalLinearGroupPointsIso k Coord).inv)
  change (groupPointsFunctor k).map (matrixRepresentation G a) = _ at h
  have he : (groupPointsFunctor k).map (matrixRepresentation G a) ≫
      (StandardGroups.generalLinearGroupPointsIso k Coord).hom = matrixPointRepresentation a := by
    rw [h, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact DFunLike.congr_fun (congrArg (fun τ => (τ.app R).hom) he) g

end

section Chamber

open Specs.CharacterDescent (Cocharacter)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open DiagonalizableGroups (groupAlgebraPointsIso)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint unitPoint)
open private integerPointsIso from LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
open private unitEquiv unitEquiv_unitPoint from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

noncomputable section

variable {k : Type} [Field k]

private abbrev gm := specGroup (groupAlgebra k IntegerCharacters)

private theorem unitEquiv_natural {R S : TestAlgebra k} (f : R ⟶ S)
    (x : Points (gm (k := k)).X R) :
    unitEquiv S (mapPoints f x) = Units.map f.hom.toMonoidHom (unitEquiv R x) := by
  let e := groupAlgebraPointsIso k IntegerCharacters ≪≫ integerPointsIso (k := k)
  have h := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (e.hom.naturality f)) x
  exact h

private theorem chamberParameter_map {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (t : Rˣ) :
    Units.map f.toMonoidHom ∘ chamberParameter t =
      chamberParameter (Units.map f.toMonoidHom t) := by
  funext i
  exact map_zpow (Units.map f.toMonoidHom) t (chamberExponents i)

private def diagonalPoints {G : GroupScheme k} (a : SplitAction G) (R : TestAlgebra k) :
    (Fin 4 → Rˣ) →* Points G.X R where
  toFun s := liftActionPoint a R (diagonalModel s) (diagonalModel_isSplitAutomorphism s)
  map_one' := by
    apply a.injective R
    rw [liftActionPoint_action, map_one]
    exact (diagonalAction R).map_one
  map_mul' s t := by
    apply a.injective R
    simp only [map_mul, liftActionPoint_action]
    exact (diagonalAction R).map_mul s t

private theorem diagonalPoints_action {G : GroupScheme k} (a : SplitAction G)
    (R : TestAlgebra k) (s : Fin 4 → Rˣ) :
    a.action R (diagonalPoints a R s) = diagonalAction R s :=
  liftActionPoint_action a R _ (diagonalModel_isSplitAutomorphism s)

private theorem diagonalPoints_natural {G : GroupScheme k} (a : SplitAction G)
    {R S : TestAlgebra k} (f : R ⟶ S) (s : Fin 4 → Rˣ) :
    mapPoints f (diagonalPoints a R s) = diagonalPoints a S (Units.map f.hom.toMonoidHom ∘ s) := by
  apply a.injective S
  apply linearEquiv_ext_of_mapModel f.hom.toRingHom
  intro x
  rw [← a.natural, diagonalPoints_action, diagonalPoints_action]
  exact diagonalModel_natural f.hom.toRingHom s x

private def chamberPoints {G : GroupScheme k} (a : SplitAction G) (R : TestAlgebra k) :
    Rˣ →* Points G.X R :=
  (diagonalPoints a R).comp {
    toFun := chamberParameter
    map_one' := by
      funext i
      simp [chamberParameter]
    map_mul' s t := by
      funext i
      exact mul_zpow s t _ }

private theorem chamberPoints_action {G : GroupScheme k} (a : SplitAction G)
    (R : TestAlgebra k) (t : Rˣ) :
    a.action R (chamberPoints a R t) = diagonalAction R (chamberParameter t) :=
  diagonalPoints_action a R _

private theorem chamberPoints_natural {G : GroupScheme k} (a : SplitAction G)
    {R S : TestAlgebra k} (f : R ⟶ S) (t : Rˣ) :
    mapPoints f (chamberPoints a R t) = chamberPoints a S (Units.map f.hom.toMonoidHom t) := by
  change mapPoints f (diagonalPoints a R (chamberParameter t)) =
    diagonalPoints a S (chamberParameter (Units.map f.hom.toMonoidHom t))
  rw [diagonalPoints_natural, chamberParameter_map]

private def chamberPointMap {G : GroupScheme k} (a : SplitAction G) :
    (groupPointsFunctor k).obj (gm (k := k)) ⟶ (groupPointsFunctor k).obj G where
  app R := GrpCat.ofHom ((chamberPoints a R).comp (unitEquiv R).toMonoidHom)
  naturality {R S} f := by
    apply GrpCat.ext
    intro x
    change Points (gm (k := k)).X R at x
    change chamberPoints a S (unitEquiv S (mapPoints f x)) =
      mapPoints f (chamberPoints a R (unitEquiv R x))
    rw [unitEquiv_natural, chamberPoints_natural]

/-- The cocharacter whose order on the weights is used in the two rank
calculations. -/
def chamberCocharacter {G : GroupScheme k} (a : SplitAction G) : Cocharacter G :=
  (groupHomEquiv _ _ (inferInstanceAs
    (IsAffine (Spec (CommRingCat.of (MonoidAlgebra k IntegerCharacters)))))).symm (chamberPointMap a)

theorem chamberCocharacter_action {G : GroupScheme k} (a : SplitAction G)
    (R : TestAlgebra k) (t : Rˣ) :
    a.action R (cocharacterPoint (chamberCocharacter a) R t) =
      diagonalAction R (chamberParameter t) := by
  let e := groupHomEquiv (gm (k := k)) G
    (inferInstanceAs (IsAffine (Spec (CommRingCat.of (MonoidAlgebra k IntegerCharacters)))))
  have h := e.apply_symm_apply (chamberPointMap a)
  change (groupPointsFunctor k).map (chamberCocharacter a) = _ at h
  unfold cocharacterPoint
  rw [h]
  change a.action R (chamberPoints a R (unitEquiv R (unitPoint R t))) = _
  rw [unitEquiv_unitPoint, chamberPoints_action]

end
end Chamber

section Infinitesimal

private def infinitesimalAction {R : Type*} [CommRing R] (j : Fin 28)
    (t : R) (ht : t * t = 0) : Model R ≃ₗ[R] Model R where
  toFun x := x + t • tangentOperator R j x
  invFun x := x - t • tangentOperator R j x
  left_inv x := by
    simp only [map_add, map_smul, smul_add, smul_smul, ht, zero_smul, add_zero, add_sub_cancel_right]
  right_inv x := by
    simp only [map_sub, map_smul, smul_sub, smul_smul, ht, zero_smul, sub_zero, sub_add_cancel]
  map_add' x y := by
    simp only [map_add, smul_add]
    abel
  map_smul' r x := by
    simp only [RingHom.id_apply, map_smul, smul_add, smul_smul, mul_comm]

private theorem infinitesimalAction_apply {R : Type*} [CommRing R] (j : Fin 28)
    (t : R) (ht : t * t = 0) (x : Model R) :
    infinitesimalAction j t ht x = x + t • tangentOperator R j x := rfl

private theorem infinitesimalAction_natural {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (j : Fin 28) (t : R) (ht : t * t = 0) (hS : f t * f t = 0) (x : Model R) :
    mapModel f (infinitesimalAction j t ht x) =
      infinitesimalAction j (f t) hS (mapModel f x) := by
  rw [infinitesimalAction_apply, infinitesimalAction_apply]
  have h (y : Model R) :
      mapModel f (x + t • y) = mapModel f x + f t • mapModel f y := by
    apply (modelCoordinateEquiv S).injective
    rw [modelCoordinateEquiv_natural]
    funext i
    simp only [Function.comp_apply, map_add, map_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, modelCoordinateEquiv_natural, map_mul]
  rw [h, tangentOperator_natural]

private theorem infinitesimalAction_isSplitAutomorphism {R : Type} [CommRing R]
    (j : Fin 28) (t : R) (ht : t * t = 0) : IsSplitAutomorphism (infinitesimalAction j t ht) := by
  apply splitAutomorphism_of_natural_norm
  · rw [infinitesimalAction_apply, tangentOperator_unit, smul_zero, add_zero]
  intro S _ _
  let f := algebraMap R S
  have hS : f t * f t = 0 := by rw [← map_mul, ht, map_zero]
  refine ⟨infinitesimalAction j (f t) hS, infinitesimalAction_natural f j t ht hS, ?_⟩
  intro x
  exact tangentOperator_preserves_norm j x (f t) hS

private theorem infinitesimalAction_chamber {R : Type*} [CommRing R] (j : Fin 28)
    (s : Rˣ) (t : R) (ht : t * t = 0)
    (h : (t * ↑(s ^ generatorWeight j)) * (t * ↑(s ^ generatorWeight j)) = 0) :
    diagonalAction R (chamberParameter s) * infinitesimalAction j t ht =
      infinitesimalAction j (t * ↑(s ^ generatorWeight j)) h *
        diagonalAction R (chamberParameter s) := by
  apply LinearEquiv.ext
  intro x
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, infinitesimalAction_apply,
    infinitesimalAction_apply, map_add, map_smul, tangentOperator_chamber, smul_smul]

variable {k : Type} [Field k] {G : GroupScheme k} (a : SplitAction G)

private noncomputable def infinitesimalPoint (R : TestAlgebra k) (j : Fin 28) (t : R) (ht : t * t = 0) :
    Points G.X R :=
  liftActionPoint a R (infinitesimalAction j t ht) (infinitesimalAction_isSplitAutomorphism j t ht)

private theorem infinitesimalPoint_action (R : TestAlgebra k) (j : Fin 28) (t : R)
    (ht : t * t = 0) : a.action R (infinitesimalPoint a R j t ht) =
      infinitesimalAction j t ht :=
  liftActionPoint_action a R _ (infinitesimalAction_isSplitAutomorphism j t ht)

private theorem infinitesimalPoint_natural {R S : TestAlgebra k} (f : R ⟶ S)
    (j : Fin 28) (t : R) (ht : t * t = 0) (hS : f.hom t * f.hom t = 0) :
    mapPoints f (infinitesimalPoint a R j t ht) = infinitesimalPoint a S j (f.hom t) hS := by
  apply a.injective S
  rw [infinitesimalPoint_action]
  apply linearEquiv_ext_of_mapModel f.hom.toRingHom
  intro x
  rw [← a.natural, infinitesimalPoint_action]
  exact infinitesimalAction_natural f.hom.toRingHom j t ht hS x

private theorem infinitesimalPoint_zero (R : TestAlgebra k) (j : Fin 28) (h : (0 : R) * 0 = 0) :
    infinitesimalPoint a R j 0 h = 1 := by
  apply a.injective R
  rw [infinitesimalPoint_action, map_one]
  apply LinearEquiv.ext
  intro x
  simp [infinitesimalAction_apply]

end Infinitesimal

section ChamberLimits

open scoped DualNumber
open LinearAlgebraicGroups.CocharacterDynamics
open LinearAlgebraicGroups.Specs (Lie)
open private pointHom_injective from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups


variable {k : Type} [Field k] {G : GroupScheme k} (a : SplitAction G)

private theorem laurentParameter_pow_nonneg (R : TestAlgebra k) (n : ℤ) (hn : 0 ≤ n) :
    (↑(laurentParameter R ^ n) : LaurentPolynomial R) = LaurentPolynomial.T n := by
  obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  rw [_root_.zpow_natCast, Units.val_pow_eq_pow_val]
  change (LaurentPolynomial.T 1 : LaurentPolynomial R) ^ b = _
  rw [LaurentPolynomial.T_pow, mul_one]

private theorem infinitesimalParameter_congr (R : TestAlgebra k) (j : Fin 28)
    {r s : R} {hr : r * r = 0} {hs : s * s = 0} (e : r = s) :
    infinitesimalPoint a R j r hr = infinitesimalPoint a R j s hs := by
  subst s
  rfl

private theorem chamberPoint_conjugates_infinitesimal (R : TestAlgebra k)
    (j : Fin 28) (s : Rˣ) (t : R) (ht : t * t = 0)
    (h : (t * ↑(s ^ generatorWeight j)) * (t * ↑(s ^ generatorWeight j)) = 0) :
    let c : Points G.X R := cocharacterPoint (chamberCocharacter a) R s
    c * infinitesimalPoint a R j t ht * c⁻¹ =
      infinitesimalPoint a R j (t * ↑(s ^ generatorWeight j)) h := by
  dsimp only
  let c : Points G.X R := cocharacterPoint (chamberCocharacter a) R s
  change c * infinitesimalPoint a R j t ht * c⁻¹ = _
  apply mul_inv_eq_iff_eq_mul.mpr
  apply a.injective R
  have hc : a.action R c = diagonalAction R (chamberParameter s) :=
    chamberCocharacter_action a R s
  simp only [map_mul, hc, infinitesimalPoint_action]
  exact infinitesimalAction_chamber j s t ht h

set_option maxHeartbeats 700000 in
/-- The square-zero tangent family for a nonnegative weight extends along the
cocharacter orbit, with the prescribed limit in weight zero or positive weight. -/
theorem tangent_has_chamber_limit (R : TestAlgebra k) (j : Fin 28) (t : R) (ht : t * t = 0)
    (hweight : 0 ≤ generatorWeight j) :
    HasLimit (chamberCocharacter a)
      (infinitesimalPoint a R j t ht)
      (show Points G.X R from
        if generatorWeight j = 0 then infinitesimalPoint a R j t ht else 1) := by
  let n := (generatorWeight j).toNat
  let p : Polynomial R := Polynomial.C t * Polynomial.X ^ n
  have hp : p * p = 0 := by
    change (Polynomial.C t * Polynomial.X ^ n) * (Polynomial.C t * Polynomial.X ^ n) = 0
    rw [mul_mul_mul_comm, ← map_mul, ht, map_zero, zero_mul]
  refine ⟨infinitesimalPoint a (polynomialAlgebra R) j p hp, ?_, ?_⟩
  · let L := laurentAlgebra R
    let s := laurentParameter R
    let c : Points G.X L := cocharacterPoint (chamberCocharacter a) L s
    let f := polynomialToLaurent R
    let u := laurentConstants R
    have hq : f.hom p * f.hom p = 0 := by rw [← map_mul, hp, map_zero]
    have hqt : u.hom t * u.hom t = 0 := by rw [← map_mul, ht, map_zero]
    have ht' : (u.hom t * ↑(s ^ generatorWeight j)) * (u.hom t * ↑(s ^ generatorWeight j)) = 0 :=
      (mul_mul_mul_comm _ _ _ _).trans (by rw [hqt, zero_mul])
    have hpoly : f.hom p = u.hom t * ↑(s ^ generatorWeight j) := by
      change p.toLaurent = LaurentPolynomial.C t * ↑(s ^ generatorWeight j)
      rw [laurentParameter_pow_nonneg R _ hweight]
      exact (Polynomial.toLaurent_C_mul_X_pow n t).trans
        (congrArg (LaurentPolynomial.C t * LaurentPolynomial.T ·) (Int.toNat_of_nonneg hweight))
    change mapPoints f (infinitesimalPoint a (polynomialAlgebra R) j p hp) =
      c * mapPoints u (infinitesimalPoint a R j t ht) * c⁻¹
    have e₁ : mapPoints f (infinitesimalPoint a (polynomialAlgebra R) j p hp) =
        infinitesimalPoint a L j (f.hom p) hq := infinitesimalPoint_natural a f j p hp hq
    have e₂ : mapPoints u (infinitesimalPoint a R j t ht) =
        infinitesimalPoint a L j (u.hom t) hqt := infinitesimalPoint_natural a u j t ht hqt
    rw [e₁, e₂]
    let x := fun v : {w : L // w * w = 0} => infinitesimalPoint a L j v.val v.property
    have e₃ : (⟨f.hom p, hq⟩ : {w : L // w * w = 0}) =
        ⟨u.hom t * (↑(s ^ generatorWeight j) : L), ht'⟩ := Subtype.ext hpoly
    exact (congrArg x e₃).trans (chamberPoint_conjugates_infinitesimal a L j s (u.hom t) hqt ht').symm
  · let f := polynomialEvaluate R 0
    have hs : f.hom p * f.hom p = 0 := by rw [← map_mul, hp, map_zero]
    change mapPoints f (infinitesimalPoint a (polynomialAlgebra R) j p hp) =
      (if generatorWeight j = 0 then infinitesimalPoint a R j t ht else (1 : Points G.X R))
    refine (infinitesimalPoint_natural a f j p hp hs).trans ?_
    by_cases h : generatorWeight j = 0
    · rw [ite_eq_left h]
      have e : f.hom p = t := by
        change p.eval₂ (RingHom.id R) 0 = t
        simp [p, n, h]
      exact infinitesimalParameter_congr a R j (hr := hs) (hs := ht) e
    · rw [ite_eq_right h]
      have hn : n ≠ 0 := by
        intro hn
        apply h
        have he : (n : ℤ) = generatorWeight j := Int.toNat_of_nonneg hweight
        exact he.symm.trans (by simp [hn])
      have e : f.hom p = 0 := by
        change p.eval₂ (RingHom.id R) 0 = 0
        simp [p, zero_pow hn]
      exact (infinitesimalParameter_congr a R j (hr := hs) (hs := mul_zero 0) e).trans
        (infinitesimalPoint_zero a R j (mul_zero 0))

/-- Positive-weight tangent points lie in the actual contracting subgroup on
every test algebra. -/
theorem positive_tangent_in_contracting
    (D : LimitDecomposition (chamberCocharacter a)) (R : TestAlgebra k) (j : Fin 24)
    (t : R) (ht : t * t = 0) :
    ∃ z : Points D.contracting.group.X R,
      z ≫ D.contracting.inclusion.hom.hom =
        infinitesimalPoint a R (positiveColumns j) t ht := by
  apply (D.contracting_points R _).mp
  have hw := positiveGeneratorWeight j
  have hl := tangent_has_chamber_limit a R (positiveColumns j) t ht hw.le
  rw [ite_eq_right (ne_of_gt hw)] at hl
  exact hl

private theorem generatorWeight_nonnegative (j : Fin 28) : 0 ≤ generatorWeight j := by
  fin_cases j <;> decide

/-- Every column direction lies in the identity tangent of the positive
limit subgroup, as expressed over arbitrary test algebras. -/
theorem tangent_in_parabolic
    (D : LimitDecomposition (chamberCocharacter a)) (R : TestAlgebra k) (j : Fin 28)
    (t : R) (ht : t * t = 0) :
    ∃ z : Points D.parabolic.group.X R,
      z ≫ D.parabolic.inclusion.hom.hom = infinitesimalPoint a R j t ht :=
  (D.parabolic_points R _).mp
    ⟨_, tangent_has_chamber_limit a R j t ht (generatorWeight_nonnegative j)⟩

/-- The tangent point over the dual numbers with the prescribed first-order
matrix. -/
noncomputable def chamberTangent (j : Fin 28) : Lie k G := by
  let R := CommAlgCat.of k (DualNumber k)
  let f := dualReduction k
  let h : (ε : DualNumber k) * ε = 0 := DualNumber.eps_mul_eps
  let p := infinitesimalPoint a R j ε h
  refine Additive.ofMul ⟨p, ?_⟩
  change mapPoints f p = (1 : Points G.X (CommAlgCat.of k k))
  have h0 : f.hom (ε : DualNumber k) * f.hom ε = 0 := by
    change (0 : k) * 0 = 0
    exact mul_zero _
  exact (infinitesimalPoint_natural a f j ε h h0).trans
    (infinitesimalPoint_zero a (CommAlgCat.of k k) j h0)

private theorem tangentMem_of_lift (S : Specs.ClosedSubgroup G) (x : Lie k G)
    (q : Points S.group.X (CommAlgCat.of k (DualNumber k)))
    (hq : q ≫ S.inclusion.hom.hom = x.toMul.val) :
    x ∈ lieImage S := by
  have hr : mapPoints (dualReduction k) q = (1 : Points S.group.X (CommAlgCat.of k k)) := by
    apply pointHom_injective S (CommAlgCat.of k k)
    change (mapPoints (dualReduction k) q) ≫ S.inclusion.hom.hom =
      (1 : Points S.group.X (CommAlgCat.of k k)) ≫ S.inclusion.hom.hom
    have h := congrArg (mapPoints (dualReduction k)) hq
    change (testSpec k).map (dualReduction k).op ≫ (q ≫ S.inclusion.hom.hom) = _ at h
    rw [← Category.assoc] at h
    refine h.trans ?_
    exact x.toMul.property.trans (map_one
      (((groupPointsFunctor k).map S.inclusion).app (CommAlgCat.of k k)).hom).symm
  exact ⟨Additive.ofMul ⟨q, hr⟩, Subtype.ext hq⟩

theorem chamberTangent_mem_contracting (D : LimitDecomposition (chamberCocharacter a))
    (j : Fin 24) : chamberTangent a (positiveColumns j) ∈ lieImage D.contracting := by
  obtain ⟨q, hq⟩ := positive_tangent_in_contracting a D
    (CommAlgCat.of k (DualNumber k)) j ε DualNumber.eps_mul_eps
  exact tangentMem_of_lift D.contracting (chamberTangent a (positiveColumns j)) q hq

theorem chamberTangent_mem_parabolic (D : LimitDecomposition (chamberCocharacter a))
    (j : Fin 28) : chamberTangent a j ∈ lieImage D.parabolic := by
  obtain ⟨q, hq⟩ := tangent_in_parabolic a D
    (CommAlgCat.of k (DualNumber k)) j ε DualNumber.eps_mul_eps
  exact tangentMem_of_lift D.parabolic (chamberTangent a j) q hq

end ChamberLimits

section ChamberInvariant

open LinearAlgebraicGroups.CocharacterDynamics
open private laurentParameter_zpow zero_of_negative from
  LinearAlgebraicGroups.Reductive.CocharacterLieWeights

variable {k : Type} [Field k] {G : GroupScheme k} (A : SplitAction G)

private theorem matrixEntry_natural {R S : TestAlgebra k} (f : R ⟶ S)
    (g : Points G.X R) (i j : Coord) :
    (coordinateMatrixHom A S (mapPoints f g)).val i j =
      f.hom ((coordinateMatrixHom A R g).val i j) := by
  have h := DFunLike.congr_fun
    (congrArg GrpCat.Hom.hom ((matrixPointRepresentation A).naturality f)) g
  exact congrArg (fun x : Matrix.GeneralLinearGroup Coord S => x.val i j) h

private theorem chamberMatrix (R : TestAlgebra k) (t : Rˣ) :
    (coordinateMatrixHom A R (cocharacterPoint (chamberCocharacter A) R t)).val =
      Matrix.diagonal (fun i => (↑(t ^ coordinateWeight i) : R)) := by
  let c : Points G.X R := cocharacterPoint (chamberCocharacter A) R t
  have hc : A.action R c = diagonalModel (chamberParameter t) := chamberCocharacter_action A R t
  change (coordinateMatrixHom A R c).val = _
  ext i j
  rw [coordinateMatrixHom_entry, hc]
  rw [diagonalModel_coordinates, diagonalCoefficient_chamber]
  simp only [modelBasisVector, LinearEquiv.apply_symm_apply, Matrix.diagonal_apply, Pi.single_apply]
  split <;> simp_all

private theorem chamberMatrix_inv (R : TestAlgebra k) (t : Rˣ) :
    (coordinateMatrixHom A R (cocharacterPoint (chamberCocharacter A) R t)⁻¹).val =
      Matrix.diagonal (fun i => (↑(t ^ (-coordinateWeight i)) : R)) := by
  let c : Points G.X R := cocharacterPoint (chamberCocharacter A) R t
  let D := coordinateMatrixHom A R c
  let Q := Matrix.diagonal (fun i => (↑(t ^ (-coordinateWeight i)) : R))
  have hc : D.val = Matrix.diagonal (fun i => (↑(t ^ coordinateWeight i) : R)) := chamberMatrix A R t
  have hQ : Q * D.val = 1 := by
    rw [hc, Matrix.diagonal_mul_diagonal]
    have hz (i : Coord) :
        (↑(t ^ (-coordinateWeight i)) : R) * (↑(t ^ coordinateWeight i) : R) = 1 := by
      rw [← Units.val_mul, ← _root_.zpow_add, neg_add_cancel, zpow_zero, Units.val_one]
    simp only [hz, Matrix.diagonal_one]
  change (coordinateMatrixHom A R c⁻¹).val = Q
  rw [map_inv]
  calc
    (D⁻¹).val = 1 * (D⁻¹).val := (one_mul _).symm
    _ = Q * (D.val * (D⁻¹).val) := by rw [← mul_assoc, hQ]
    _ = Q := by
      change Q * (D.val * D.inv) = Q
      rw [D.val_inv, mul_one]

private theorem matrixEntry_chamber_conjugation (R : TestAlgebra k) (t : Rˣ)
    (g : Points G.X R) (i j : Coord) :
    let c : Points G.X R := cocharacterPoint (chamberCocharacter A) R t
    (coordinateMatrixHom A R (c * g * c⁻¹)).val i j =
      (↑(t ^ (coordinateWeight i - coordinateWeight j)) : R) * (coordinateMatrixHom A R g).val i j := by
  let c : Points G.X R := cocharacterPoint (chamberCocharacter A) R t
  change (coordinateMatrixHom A R (c * g * c⁻¹)).val i j = _
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, chamberMatrix_inv, chamberMatrix,
    Matrix.mul_diagonal, Matrix.diagonal_mul, sub_eq_add_neg, _root_.zpow_add, Units.val_mul]
  ring

/-- The limit parabolic preserves the coordinate weight filtration in the
split Albert representation. -/
theorem chamber_hasExtension_entry_zero (R : TestAlgebra k) (g : Points G.X R)
    (hg : HasExtension (chamberCocharacter A) g) (i j : Coord)
    (hij : coordinateWeight i < coordinateWeight j) :
    (coordinateMatrixHom A R g).val i j = 0 := by
  obtain ⟨_, q, hq, _⟩ := hg
  change Points G.X (polynomialAlgebra R) at q
  let L := laurentAlgebra R
  let s := laurentParameter R
  let c : Points G.X L := cocharacterPoint (chamberCocharacter A) L s
  let f := polynomialToLaurent R
  let u := laurentConstants R
  have e : mapPoints f q = c * mapPoints u g * c⁻¹ := hq
  have h := congrArg (fun x : Points G.X L => (coordinateMatrixHom A L x).val i j) e
  have h' := matrixEntry_chamber_conjugation A L s (mapPoints u g) i j
  change (coordinateMatrixHom A L (c * mapPoints u g * c⁻¹)).val i j = _ at h'
  rw [h', matrixEntry_natural A f, matrixEntry_natural A u, laurentParameter_zpow] at h
  exact zero_of_negative h (sub_neg.mpr hij)

/-- The lowest coordinate of the 27-dimensional representation is a
semi-invariant of the positive limit parabolic. -/
theorem chamber_lowest_coordinate (R : TestAlgebra k) (g : Points G.X R)
    (hg : HasExtension (chamberCocharacter A) g) (v : Model R) :
    let i := a 2 0
    modelCoordinateEquiv R (A.action R g v) i =
      (coordinateMatrixHom A R g).val i i * modelCoordinateEquiv R v i := by
  let i := a 2 0
  let M := (coordinateMatrixHom A R g).val
  let x := modelCoordinateEquiv R v
  have hv := coordinateMatrixHom_mulVec A R g (modelCoordinateEquiv R v)
  rw [LinearEquiv.symm_apply_apply] at hv
  have h : (M *ᵥ x) i = modelCoordinateEquiv R (A.action R g v) i := congrFun hv i
  change _ = M i i * x i
  rw [← h, Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
  · intro j _ hj
    have he := chamber_hasExtension_entry_zero A R g hg i j
      (coordinateWeight_minimal j hj)
    change M i j * x j = 0
    exact mul_eq_zero_of_left he _
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

end ChamberInvariant

section ChamberDifferential

open scoped DualNumber
open LinearAlgebraicGroups.Specs (Lie)
open LinearAlgebraicGroups.InfinitesimalCommutator (matrixDifferential)
open private matrixDifferentialLinear matrixDifferential_eq matrixCoefficient_injective from
  LinearAlgebraicGroups.Affine.LieBracket

private def operatorMatrix (k : Type) [Field k] (T : Module.End k (Model k)) :
    Matrix Coord Coord k :=
  Matrix.of fun i j => modelCoordinateEquiv k (T (modelBasisVector k j)) i

private theorem tangentOperator_eval_dual (k : Type) [Field k] (j : Fin 28) (r s : Coord) :
    modelCoordinateEquiv (DualNumber k)
        (tangentOperator (DualNumber k) j (modelBasisVector (DualNumber k) s)) r =
      algebraMap k (DualNumber k) (operatorMatrix k (tangentOperator k j) r s) := by
  have h := tangentOperator_natural (algebraMap k (DualNumber k)) j (modelBasisVector k s)
  rw [mapModel_basisVector] at h
  rw [← h]
  exact congrFun (modelCoordinateEquiv_natural _ _) r

private theorem basisVector_eval_dual (k : Type) [Field k] (r s : Coord) :
    modelCoordinateEquiv (DualNumber k) (modelBasisVector (DualNumber k) s) r =
      algebraMap k (DualNumber k) (modelCoordinateEquiv k (modelBasisVector k s) r) :=
  congrFun ((congrArg (modelCoordinateEquiv (DualNumber k))
    (mapModel_basisVector (algebraMap k (DualNumber k)) s)).symm.trans
    (modelCoordinateEquiv_natural _ _)) r

/-- The tangent calculation is the differential of the actual matrix
representation in the frame coordinates. -/
theorem chamberTangent_matrixDifferential {k : Type} [Field k]
    (G : AffineAlgebraicGroup k) (a : SplitAction G.val) (j : Fin 28) :
    matrixDifferential (matrixRepresentation G a)
      (StandardGroups.generalLinearGroupPointsIso k Coord) (chamberTangent a j) =
        operatorMatrix k (tangentOperator k j) := by
  let R := CommAlgCat.of k (DualNumber k)
  let p := infinitesimalPoint a R j ε DualNumber.eps_mul_eps
  ext r s
  change (((StandardGroups.generalLinearGroupPointsIso k Coord).hom.app R
      (p ≫ (matrixRepresentation G a).hom.hom)).val r s).snd = _
  rw [matrixRepresentation_apply, coordinateMatrixHom_entry]
  have hp : a.action R p = _ := infinitesimalPoint_action a R j ε DualNumber.eps_mul_eps
  rw [hp, infinitesimalAction_apply, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change (modelCoordinateEquiv (DualNumber k) (modelBasisVector (DualNumber k) s) r +
    ε * modelCoordinateEquiv (DualNumber k)
        (tangentOperator (DualNumber k) j (modelBasisVector (DualNumber k) s)) r).snd = _
  rw [basisVector_eval_dual, tangentOperator_eval_dual]
  rw [TrivSqZeroExt.snd_add, DualNumber.snd_mul]
  change (0 : k) + (0 * 0 + 1 * operatorMatrix k (tangentOperator k j) r s) = _
  simp only [zero_mul, one_mul, zero_add]

private def matrixToOperator (k : Type) [Field k] :
    Matrix Coord Coord k ≃ₗ[k] Module.End k (Model k) :=
  Matrix.toLin'.trans (modelCoordinateEquiv k).symm.conj

private theorem matrixToOperator_apply_operatorMatrix (k : Type) [Field k]
    (T : Module.End k (Model k)) : matrixToOperator k (operatorMatrix k T) = T := by
  refine ((Pi.basisFun k Coord).map (modelCoordinateEquiv k).symm).ext fun j => ?_
  rw [Module.Basis.map_apply, Pi.basisFun_apply]
  change (modelCoordinateEquiv k).symm (Matrix.toLin' (operatorMatrix k T) _) =
    T (modelBasisVector k j)
  rw [LinearEquiv.symm_symm, LinearEquiv.coe_coe, (modelCoordinateEquiv k).apply_symm_apply,
    Matrix.toLin'_apply, Matrix.mulVec_single_one]
  apply (modelCoordinateEquiv k).injective
  rw [(modelCoordinateEquiv k).apply_symm_apply]
  rfl


end ChamberDifferential

end SchemeAction

section SplitSubgroups

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs (ClosedSubgroup)
open DiagonalizableGroups (groupAlgebraPointsIso diagonalClosedSubgroups diagonalIntegerPowers)
open Specs.DiagonalizableGroups (groupAlgebra groupAlgebraMap diagonalGroup)
open private groupAlgebraMap_surjective from LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups

/-- A closed subgroup of a split diagonalizable group with finitely generated
characters that has an infinite-order point over a test algebra contains a split copy
of the multiplicative group. -/
theorem splitTorus_of_diagonalizable_infiniteOrder {k M : Type} [Field k]
    [CommGroup M] [Group.FG M] (S : ClosedSubgroup (diagonalGroup k M).val)
    (R : TestAlgebra k) (x : Points S.group.X R) (hx : ¬ IsOfFinOrder x) :
    ∃ T : ClosedSubgroup S.group,
      Nonempty (T.group ≅ (StandardGroups.multiplicativePowerGroup k (ULift (Fin 1))).val) := by
  obtain ⟨N, ⟨e, _⟩, _⟩ :=
    (diagonalClosedSubgroups k M S.group S.inclusion).mp S.isClosedImmersion
  let E : Points S.group.X R ≃* (M ⧸ N →* Rˣ) :=
    (((groupPointsFunctor k).mapIso e).app R).groupIsoToMulEquiv.trans
      (((groupAlgebraPointsIso k (M ⧸ N)).app R).groupIsoToMulEquiv)
  obtain ⟨Idx, J, _, _, p, hp, n, ⟨d⟩⟩ :=
    CommGroup.equiv_free_prod_prod_multiplicative_zmod (M ⧸ N)
  have hJ : Nonempty J := by
    by_contra! h
    let : IsEmpty J := h
    let (i : Idx) : NeZero (p i ^ n i) := ⟨pow_ne_zero _ (hp i).ne_zero⟩
    let : Finite (J → Multiplicative ℤ) := Finite.of_subsingleton
    let : Finite (M ⧸ N) := Finite.of_injective d d.injective
    let : Fintype (M ⧸ N) := Fintype.ofFinite _
    let m := Fintype.card (M ⧸ N)
    apply hx
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨m, Fintype.card_pos, ?_⟩
    apply E.injective
    rw [map_pow, map_one]
    apply MonoidHom.ext
    intro y
    change (E x y) ^ m = 1
    rw [← map_pow, pow_card_eq_one, map_one]
  obtain ⟨j⟩ := hJ
  let I := ULift.{0} (Fin 1)
  let F := Multiplicative (I → ℤ)
  let q : M ⧸ N →* F := {
    toFun y := Multiplicative.ofAdd (fun _ => Multiplicative.toAdd ((d y).1 j))
    map_one' := by rw [map_one]; rfl
    map_mul' y z := by rw [map_mul]; rfl }
  have hq : Function.Surjective q := by
    intro f
    refine ⟨d.symm (fun _ => Multiplicative.ofAdd (f.toAdd (ULift.up 0)), 1), ?_⟩
    change Multiplicative.ofAdd
      (fun _ : I => Multiplicative.toAdd ((d (d.symm _)).1 j)) = f
    rw [d.apply_symm_apply]
    apply (Multiplicative.ofAdd : (I → ℤ) ≃ F).symm.injective
    funext i
    exact congrArg f.toAdd (Subsingleton.elim _ i)
  let A := groupAlgebra k F
  let f := specGroupMap (groupAlgebraMap k q)
  have hf : IsClosedImmersion f.hom.hom.left :=
    (hopfMapClosedImmersion k (groupAlgebraMap k q)).mpr (groupAlgebraMap_surjective q hq)
  have he' : IsIso e.inv.hom.hom.left :=
    ((Grp.forget (SchemeOver k)) ⋙ (Over.forget (Spec (CommRingCat.of k)))).map_isIso e.inv
  refine ⟨⟨specGroup A, f ≫ e.inv, ?_⟩, diagonalIntegerPowers k I⟩
  exact IsClosedImmersion.comp f.hom.hom.left e.inv.hom.hom.left

end SplitSubgroups

section FibreComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Albert.AutomorphismTypeSpecification (IntegralSplitIdentification groupChange chevalleyChange)
open Albert.IntegralSmoothnessSpecification (geometricFiber)
open CategoryTheory.MonoidalCategory

noncomputable section

/-- The integral comparison gives the same Chevalley fibre whether one
extends directly from the classification's integers or first uses `ℤ`. -/
theorem splitIdentification_fieldFibre (S : IntegralSplitIdentification)
    (k : Type) [Field k] :
    Nonempty (geometricFiber S.split k ≅ (chevalleyChange k).obj S.chevalley.group) := by
  let Z := Specs.IntegralSemisimpleModel.Integers.{0}
  let : Algebra Z ℤ := Specs.IntegralSemisimpleModel.integerAlgebra ℤ
  let : Algebra Z k := Specs.IntegralSemisimpleModel.integerAlgebra k
  let f := Spec.map (CommRingCat.ofHom (algebraMap ℤ k))
  let g := Spec.map (CommRingCat.ofHom (algebraMap Z ℤ))
  have h : Spec.map (CommRingCat.ofHom (algebraMap Z k)) = f ≫ g := by
    change Spec.map (CommRingCat.ofHom (algebraMap Z k)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ k)) ≫ Spec.map (CommRingCat.ofHom (algebraMap Z ℤ))
    rw [← Spec.map_comp]
    congr 1
  have e := ((Functor.mapGrpNatIso (Over.pullbackComp f g)) ≪≫
    Functor.mapGrpCompIso (F := Over.pullback g) (G := Over.pullback f)).app S.chevalley.group
  refine ⟨(groupChange ℤ k).mapIso S.comparison ≪≫ ?_⟩
  change ((Over.pullback g).mapGrp ⋙ (Over.pullback f).mapGrp).obj S.chevalley.group ≅
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Z k)))).mapGrp.obj S.chevalley.group
  rw [h]
  exact e.symm

end

end FibreComparison

section SmoothIntersection

open Algebra TensorProduct KaehlerDifferential

/-- The local submersion criterion used for a transverse intersection.
The differential is expressed on cotangent spaces, with the map induced
from the source base differentials. -/
theorem formallySmooth_of_injective_residueDifferentials (R A B : Type*)
    [CommRing R] [CommRing A] [CommRing B] [IsLocalRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.EssFiniteType R A] [Algebra.EssFiniteType R B] [FormallySmooth R B]
    (hf : Function.Injective ((mapBaseChange R A B).lTensor (IsLocalRing.ResidueField B))) :
    FormallySmooth A B := by
  let f := mapBaseChange R A B
  let g := KaehlerDifferential.map R A B B
  have hfg := exact_mapBaseChange_map R A B
  have hfree : Module.Free B Ω[B⁄R] := Module.free_of_flat_of_isLocalRing
  have he : Module.Free B Ω[B⁄A] :=
    Module.free_of_lTensor_residueField_injective f g (map_surjective R A B) hfg hf
  obtain ⟨r, hr⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective f).mpr hf
  have hinj : Function.Injective f := Function.HasLeftInverse.injective ⟨r, LinearMap.congr_fun hr⟩
  apply (Algebra.formallySmooth_iff A B).mpr
  refine ⟨inferInstance, ⟨fun x y => ?_⟩⟩
  have hz (v : Algebra.H1Cotangent A B) : v = 0 := by
    have hv := (Algebra.H1Cotangent.exact_δ_mapBaseChange R A B).apply_apply_eq_zero v
    have hδ : Algebra.H1Cotangent.δ R A B v = 0 := hinj (hv.trans (map_zero f).symm)
    obtain ⟨w, hw⟩ := (Algebra.H1Cotangent.exact_map_δ R A B _).mp hδ
    rw [Subsingleton.elim w 0, map_zero] at hw
    exact hw.symm
  exact (hz x).trans (hz y).symm

end SmoothIntersection

/-- Nontrivial valuation already supplies the infinite-order units needed
for the rational open-cell argument. -/
theorem localField_infiniteOrderUnit (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    ∃ t : kˣ, ¬ IsOfFinOrder t := by
  obtain ⟨x, hx, hv⟩ := Valuation.IsNontrivial.exists_lt_one (v := ValuativeRel.valuation k)
  let t := Units.mk0 x hx
  refine ⟨t, ?_⟩
  intro h
  obtain ⟨n, hn, ht⟩ := h.exists_pow_eq_one
  have hh := congrArg (fun u : kˣ => ValuativeRel.valuation k u.val) ht
  change ValuativeRel.valuation k (x ^ n) = ValuativeRel.valuation k 1 at hh
  rw [map_pow, map_one] at hh
  exact (ne_of_lt (pow_lt_one₀ zero_le hv hn.ne')) hh

/-- A nonarchimedean local field with its specified valuation is infinite. -/
theorem localField_infinite (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : Infinite k := by
  obtain ⟨t, ht⟩ := localField_infiniteOrderUnit k
  have : Infinite kˣ := Set.infinite_univ_iff.mp
    ((infinite_not_isOfFinOrder ht).mono (Set.subset_univ _))
  exact Infinite.of_injective Units.val Units.val_injective

section Fibre

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs
open Albert.IntegralSmoothnessSpecification (SplitGroup geometricFiber algebraicFiber)
open Albert.IntegralSmoothness (geometricFiberAction)
open Albert.ShortDirectionSpecification (IntegralPresentation)
open Albert.AutomorphismTypeSpecification (IntegralSplitIdentification chevalleyChange)
open Albert.ReductiveFiberSpecification (SplitAction)
open Albert.TrialitySpecification (Model mapModel frameStabilizer)
open Albert.FrameSpecification (frameAxis)
open Albert.CubicSpecification (cubicUnit)
open Albert.IdempotentSpecification (IsSplitAutomorphism)
open TrialitarianSplitTorusSpecification (integralPoint IsGeometricFrameConjugate)
open Bialgebra
open private groupIsoOfPointIso baseChangePointIso isAffine_baseChange from
  LinearAlgebraicGroups.Affine.IdentityTangent
open private geometricFiberPointEquiv geometricFiberPointEquiv_left from
  LinearAlgebraicGroups.Albert.IntegralSmoothness
open private frameRepresentation frameGroup frameGroup_finrank coordinates
  integralCoordinates_locallyStandardSmooth locallyStandardSmooth_intTensor cotangent_finrank from
  LinearAlgebraicGroups.Albert.FrameTangentRank

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k : Type} [Field k]

/-- Two integral presentations of the split Albert action yield isomorphic fibres. -/
def splitFibreIso {P Q : IntegralPresentation} (G : SplitGroup P) (H : SplitGroup Q) :
    geometricFiber G k ≅ geometricFiber H k := by
  letI : IsAffine (geometricFiber G k).X.left := (algebraicFiber G k).property.1
  letI : IsAffine (geometricFiber H k).X.left := (algebraicFiber H k).property.1
  exact groupIsoOfPointIso (actionPointIso (geometricFiberAction G k) (geometricFiberAction H k))

/-- Smooth relative dimension is invariant under isomorphisms of the acting groups. -/
theorem smoothDimension_of_groupIso {G H : GroupScheme k} (e : G ≅ H) (n : ℕ)
    (h : SmoothOfRelativeDimension n H.X.hom) : SmoothOfRelativeDimension n G.X.hom := by
  let i : G.X ≅ H.X := (Grp.forget (SchemeOver k)).mapIso e
  have : IsIso i.hom.left := (Over.forget _).map_isIso i.hom
  have hi := MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension.{0} n) i.hom.left H.X.hom
  exact i.hom.w ▸ hi.mpr h

theorem splitFibre_smoothDimension (S : IntegralSplitIdentification)
    {P : IntegralPresentation} (G : SplitGroup P) :
    SmoothOfRelativeDimension 52 (geometricFiber G k).X.hom := by
  apply smoothDimension_of_groupIso (splitFibreIso G S.split) 52
  letI := S.smooth
  exact inferInstanceAs (SmoothOfRelativeDimension 52
    (pullback.snd S.split.group.X.hom (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))))

theorem splitFibre_chevalleyIso (S : IntegralSplitIdentification)
    {P : IntegralPresentation} (G : SplitGroup P) :
    Nonempty (geometricFiber G k ≅ (chevalleyChange k).obj S.chevalley.group) := by
  obtain ⟨e⟩ := splitIdentification_fieldFibre S k
  exact ⟨splitFibreIso G S.split ≪≫ e⟩

/-- The tangent dimension at the identity of a smooth affine group of pure
relative dimension agrees with that relative dimension. -/
theorem lie_finrank_of_smoothDimension {G : GroupScheme k} [IsAffine G.X.left] (n : ℕ)
    (h : SmoothOfRelativeDimension n G.X.hom) : Module.finrank k (Lie k G) = n := by
  let C : AffineGroupCategory k := ⟨G, inferInstance⟩
  let A := coordinateHopf C
  let e : hopfSpectrum A ≅ G := (affineGroupInclusion k).mapIso (coordinateHopfSpecIso C)
  have hs := smoothDimension_of_groupIso e n h
  have hA : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap k A) :=
    (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)).mp hs
  obtain ⟨p, _, hp⟩ := liePresentation k A G e
  let d : PointTangent (counitAlgHom k A) ≃ₗ[k] Lie k G := { p with map_smul' := hp }
  rw [← d.finrank_eq, Subspace.dual_finrank_eq]
  exact cotangent_finrank (counitAlgHom k A) n hA

variable {K : Type} [Field K] [Algebra k K]

/-- Extend the action along the point equivalence for scalar extension. -/
def extendSplitAction {G : GroupScheme k} (A : SplitAction G) :
    SplitAction ((groupBaseChange k K).obj G) where
  action R := (A.action ((restrictTestAlgebra k K).obj R)).comp
    (baseChangePointGroupEquiv K G R).toMonoidHom
  injective R := (A.injective ((restrictTestAlgebra k K).obj R)).comp
    (baseChangePointGroupEquiv K G R).injective
  image R := by
    change Set.range (A.action _ ∘ baseChangePointGroupEquiv K G R) = _
    rw [Set.range_comp, (baseChangePointGroupEquiv K G R).surjective.range_eq,
      Set.image_univ, A.image]
  natural {R S} f g x := by
    change mapModel f.hom.toRingHom (A.action _ (baseChangePoint k K G.X R g) x) =
      A.action _ (baseChangePoint k K G.X S (mapPoints f g)) (mapModel f.hom.toRingHom x)
    rw [baseChangePointsNaturality k K G.X f (show Points ((baseChange k K).obj G.X) R from g)]
    exact A.natural ((restrictTestAlgebra k K).map f) _ x

theorem geometricFrameConjugacy_action {P : IntegralPresentation} {G : SplitGroup P}
    {H : ClosedSubgroup (geometricFiber G k)} (h : IsGeometricFrameConjugate H) :
    ∃ g : Points ((groupBaseChange k (AlgebraicClosure k)).obj (geometricFiber G k)).X
        (CommAlgCat.of (AlgebraicClosure k) (AlgebraicClosure k)),
      ∀ (R : TestAlgebra (AlgebraicClosure k))
        (x : Points ((groupBaseChange k (AlgebraicClosure k)).obj (geometricFiber G k)).X R),
        let F := groupBaseChange k (AlgebraicClosure k)
        let gR := mapPoints (CommAlgCat.ofHom (Algebra.ofId (AlgebraicClosure k) R)) g
        (∃ p : Points (F.obj H.group).X R, p ≫ (F.map H.inclusion).hom.hom = x) ↔
          ∀ i, (extendSplitAction (geometricFiberAction G k)).action R (gR * x * gR⁻¹)
            (frameAxis i) = frameAxis i := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun R x => ?_⟩
  dsimp only
  have hRx := hg R x
  dsimp only at hRx
  rw [hRx]
  let gR := mapPoints (CommAlgCat.ofHom (Algebra.ofId (AlgebraicClosure k) R)) g
  let R' := (restrictTestAlgebra k (AlgebraicClosure k)).obj R
  let y := baseChangePoint k (AlgebraicClosure k) (geometricFiber G k).X R (gR * x * gR⁻¹)
  have hy : geometricFiberPointEquiv G R' y = integralPoint (G := G) y := by
    apply Over.OverMorphism.ext
    exact geometricFiberPointEquiv_left G R' y
  change (∀ i, G.action _ (integralPoint (G := G) y) (frameAxis i) = frameAxis i) ↔
    ∀ i, G.action _ (geometricFiberPointEquiv G R' y) (frameAxis i) = frameAxis i
  rw [hy]

private theorem mapModel_frameAxis {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (i : Slot) : mapModel f (frameAxis i) = frameAxis i := by
  apply (modelCoordinateEquiv S).injective
  rw [modelCoordinateEquiv_natural, modelCoordinateEquiv_axis, modelCoordinateEquiv_axis]
  funext j
  split <;> simp_all

/-- The ordered frame obtained by acting on the diagonal axes. -/
def orbitFrame {G : GroupScheme k} (A : SplitAction G)
    (p : Points G.X (CommAlgCat.of k k)) (i : Slot) : Model k :=
  A.action _ p (frameAxis i)

theorem geometricFrameConjugacy_stabilizer {P : IntegralPresentation} {G : SplitGroup P}
    {H : ClosedSubgroup (geometricFiber G k)} (h : IsGeometricFrameConjugate H) :
    let K := AlgebraicClosure k
    let F := groupBaseChange k K
    let A := extendSplitAction (K := K) (geometricFiberAction G k)
    ∃ p : Points (F.obj (geometricFiber G k)).X (CommAlgCat.of K K),
      ∀ (R : TestAlgebra K) (x : Points (F.obj (geometricFiber G k)).X R),
        (∃ y : Points (F.obj H.group).X R, y ≫ (F.map H.inclusion).hom.hom = x) ↔
          ∀ i, A.action R x (mapModel (algebraMap K R) (orbitFrame A p i)) =
            mapModel (algebraMap K R) (orbitFrame A p i) := by
  obtain ⟨g, hg⟩ := geometricFrameConjugacy_action h
  dsimp only
  refine ⟨g⁻¹, fun R x => ?_⟩
  have hRx := hg R x
  dsimp only at hRx
  rw [hRx]
  let A := extendSplitAction (K := AlgebraicClosure k) (geometricFiberAction G k)
  let f := CommAlgCat.ofHom (Algebra.ofId (AlgebraicClosure k) R)
  let gR := mapPoints f g
  have hf (i : Slot) : mapModel (algebraMap (AlgebraicClosure k) R) (orbitFrame A g⁻¹ i) =
      A.action R gR⁻¹ (frameAxis i) := by
    change mapModel f.hom.toRingHom (A.action _ g⁻¹ (frameAxis i)) =
      A.action R gR⁻¹ (frameAxis i)
    rw [A.natural f, mapModel_frameAxis]
    let J := (groupBaseChange k (AlgebraicClosure k)).obj (geometricFiber G k)
    let m := (((groupPointsFunctor (AlgebraicClosure k)).obj J).map f).hom
    exact congrArg (fun z : Points J.X R => A.action R z (frameAxis i)) (m.map_inv g)
  change (∀ i, A.action R (gR * x * gR⁻¹) (frameAxis i) = frameAxis i) ↔
    ∀ i, A.action R x (mapModel (algebraMap (AlgebraicClosure k) R) (orbitFrame A g⁻¹ i)) =
      mapModel (algebraMap (AlgebraicClosure k) R) (orbitFrame A g⁻¹ i)
  simp only [hf]
  apply forall_congr'
  intro i
  rw [map_mul, map_mul]
  change A.action R gR (A.action R x (A.action R gR⁻¹ (frameAxis i))) = frameAxis i ↔ _
  rw [map_inv]
  exact (A.action R gR).toEquiv.eq_symm_apply.symm

private theorem splitFrame_unit (R : Type) [CommRing R] :
    (∑ i : Fin 3, (frameAxis i : Model R)) = cubicUnit := by
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp [Fin.sum_univ_three, frameAxis, Albert.CubicSpecification.diagonalCoordinates, cubicUnit]
  · simp [Fin.sum_univ_three, frameAxis, Albert.CubicSpecification.diagonalCoordinates, cubicUnit]

/-- An ordered frame-fixing automorphism of the quadratic operator fixes the unit. -/
private theorem splitFrame_isSplitAutomorphism {R : Type} [CommRing R]
    (e : frameStabilizer (R := R)) : IsSplitAutomorphism e.val := by
  refine ⟨?_, e.property.2⟩
  rw [← splitFrame_unit, map_sum]
  exact Finset.sum_congr rfl fun i _ => e.property.1 i

private def conjugatedFrameAction {G : GroupScheme k} (A : SplitAction G)
    {S : ClosedSubgroup G} (g : Points G.X (CommAlgCat.of k k))
    (R : TestAlgebra k) : Points S.group.X R →* (Model R ≃ₗ[R] Model R) :=
  let gR := mapPoints (CommAlgCat.ofHom (Algebra.ofId k R)) g
  ((A.action R).comp (MulAut.conj gR).toMonoidHom).comp
    (((groupPointsFunctor k).map S.inclusion).app R).hom

private theorem conjugatedFrameAction_natural {G : GroupScheme k} (A : SplitAction G)
    {S : ClosedSubgroup G} (g : Points G.X (CommAlgCat.of k k))
    {R T : TestAlgebra k} (f : R ⟶ T) (p : Points S.group.X R) (x : Model R) :
    mapModel f.hom.toRingHom (conjugatedFrameAction A g R p x) =
      conjugatedFrameAction A g T (mapPoints f p) (mapModel f.hom.toRingHom x) := by
  let gR := mapPoints (CommAlgCat.ofHom (Algebra.ofId k R)) g
  let gT := mapPoints (CommAlgCat.ofHom (Algebra.ofId k T)) g
  have hg : mapPoints f gR = gT := by
    change (testSpec k).map f.op ≫ (testSpec k).map (CommAlgCat.ofHom (Algebra.ofId k R)).op ≫ g =
      (testSpec k).map (CommAlgCat.ofHom (Algebra.ofId k T)).op ≫ g
    rw [← Category.assoc, ← Functor.map_comp, ← op_comp]
    congr 3
    apply CommAlgCat.hom_ext
    ext
  change mapModel f.hom.toRingHom (A.action R (gR * (p ≫ S.inclusion.hom.hom) * gR⁻¹) x) =
    A.action T (gT * (mapPoints f p ≫ S.inclusion.hom.hom) * gT⁻¹) (mapModel f.hom.toRingHom x)
  rw [A.natural f]
  congr 2
  let m := (((groupPointsFunctor k).obj G).map f).hom
  change m (gR * (p ≫ S.inclusion.hom.hom) * gR⁻¹) = _
  rw [map_mul, map_mul, map_inv]
  change (mapPoints f gR) * (mapPoints f (p ≫ S.inclusion.hom.hom)) * (mapPoints f gR)⁻¹ = _
  rw [hg]
  simp only [mapPoints, Category.assoc]

open private pointHom_injective from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

/-- A closed subgroup with the prescribed conjugated point functor is the
represented split ordered-frame stabilizer. -/
private def frameStabilizerIso {G : GroupScheme k} [IsAffine G.X.left] (A : SplitAction G)
    (S : ClosedSubgroup G) (g : Points G.X (CommAlgCat.of k k))
    (h : ∀ (R : TestAlgebra k) (x : Points G.X R),
      let gR := mapPoints (CommAlgCat.ofHom (Algebra.ofId k R)) g
      (∃ p : Points S.group.X R, p ≫ S.inclusion.hom.hom = x) ↔
        ∀ i, A.action R (gR * x * gR⁻¹) (frameAxis i) = frameAxis i) :
    S.group ≅ (frameRepresentation k).group := by
  letI := S.isClosedImmersion
  letI : IsAffine S.group.X.left := isAffine_of_isAffineHom S.inclusion.hom.hom.left
  let Q := frameRepresentation k
  letI : IsAffine Q.group.X.left := Q.affine
  let f (R : TestAlgebra k) : Points S.group.X R →* frameStabilizer (R := R) :=
    (conjugatedFrameAction A g R).codRestrict _ fun p =>
      ⟨(h R _).mp ⟨p, rfl⟩, (splitAction_mem A R _).2⟩
  have hf (R : TestAlgebra k) : Function.Bijective (f R) := by
    let gR := mapPoints (CommAlgCat.ofHom (Algebra.ofId k R)) g
    constructor
    · intro x y e
      apply pointHom_injective S R
      exact (MulAut.conj gR).injective (A.injective R (congrArg Subtype.val e))
    · intro e
      obtain ⟨z, hz⟩ := (A.image R).symm ▸
        (show e.val ∈ {a | IsSplitAutomorphism a} from splitFrame_isSplitAutomorphism e)
      let x := (MulAut.conj gR).symm z
      have hx : gR * x * gR⁻¹ = z := (MulAut.conj gR).apply_symm_apply z
      obtain ⟨p, hp⟩ := (h R x).mpr (fun i => by rw [hx, hz]; exact e.property.1 i)
      refine ⟨p, Subtype.ext ?_⟩
      change A.action R (gR * (p ≫ S.inclusion.hom.hom) * gR⁻¹) = e.val
      rw [hp, hx, hz]
  let j (R : TestAlgebra k) := (MulEquiv.ofBijective (f R) (hf R)).trans (Q.points R).symm
  refine groupIsoOfPointIso (NatIso.ofComponents (fun R => (j R).toGrpIso) ?_)
  intro R T m
  apply GrpCat.ext
  intro p
  change j T (mapPoints m p) = mapPoints m (j R p)
  apply (Q.points T).injective
  apply Subtype.ext
  apply linearEquiv_ext_of_mapModel m.hom.toRingHom
  intro x
  have he (R : TestAlgebra k) (p : Points S.group.X R) :
      Q.points R (j R p) = f R p := (Q.points R).apply_symm_apply _
  rw [he]
  have hn := Q.natural m (j R p) x
  change _ = (Q.points T (mapPoints m (j R p))).val (mapModel m.hom.toRingHom x) at hn
  rw [he] at hn
  exact (conjugatedFrameAction_natural A g m p x).symm.trans hn

/-- The actual geometric subgroup in the hypothesis is smooth of relative dimension 28. -/
theorem geometricFrameConjugate_smoothDimension {P : IntegralPresentation} {G : SplitGroup P}
    {H : ClosedSubgroup (geometricFiber G k)} (h : IsGeometricFrameConjugate H) :
    SmoothOfRelativeDimension 28 ((groupBaseChange k (AlgebraicClosure k)).obj H.group).X.hom := by
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  letI : IsAffine (geometricFiber G k).X.left := (algebraicFiber G k).property.1
  letI : IsAffine (F.obj (geometricFiber G k)).X.left := isAffine_baseChange (K := K) _
  let S := scalarExtendedSubgroup K H
    (baseChangeClosedSubgroup k K H.inclusion H.isClosedImmersion)
  obtain ⟨g, hg⟩ := geometricFrameConjugacy_action h
  let e := frameStabilizerIso (extendSplitAction (geometricFiberAction G k)) S g hg
  apply smoothDimension_of_groupIso e 28
  change SmoothOfRelativeDimension 28 (Spec.map (CommRingCat.ofHom (algebraMap K (coordinates K))))
  exact (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 28)).mpr
    (locallyStandardSmooth_intTensor K 28 integralCoordinates_locallyStandardSmooth)

end

end Fibre

section Reversal

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open LinearAlgebraicGroups.Specs
open Albert.TrialitySpecification (Model mapModel)
open Albert.CubicSpecification (cubicUnit)
open Albert.IdempotentSpecification (IsSplitAutomorphism)
open Albert.ReductiveFiberSpecification (SplitAction)
open scoped CategoryTheory.MonObj
/-- The involution (A,B,D) ↦ (Aᵀ,Dᵀ,Bᵀ) on individual coordinates. -/
private def reverseCoord (z : Coord) : Coord :=
  let p : Slot := ⟨z.val / 9, by omega⟩
  let i : Slot := ⟨z.val / 3 % 3, by omega⟩
  let j : Slot := ⟨z.val % 3, by omega⟩
  coord (![0, 2, 1] p) j i

private theorem reverseCoord_involutive (i : Coord) : reverseCoord (reverseCoord i) = i := by
  fin_cases i <;> rfl

private theorem reverseCoord_weight (i : Coord) :
    coordinateWeight (reverseCoord i) = -coordinateWeight i := by
  fin_cases i <;> rfl

private theorem reverseCoord_unit {R : Type*} [CommRing R] (i : Coord) :
    (unitVector (R := R)) (reverseCoord i) = unitVector i := by
  change (if _ then (1 : R) else 0) = (if _ then 1 else 0)
  congr 1
  decide +revert

private def reverseTerms : CubicTerms :=
  normTerms.map (fun (w, c) => (w.map reverseCoord, c)) ++
    normTerms.map (fun (w, c) => (w, -c))

set_option maxRecDepth 4096 in
private theorem reverseTerms_check :
    (collectTerms reverseTerms).all (fun t => t.2 == 0) = true := by
  decide

private theorem reverseCoord_norm {R : Type*} [CommRing R] (v : Coord → R) :
    evaluateTerms normTerms (v ∘ reverseCoord) = evaluateTerms normTerms v := by
  have hn (p : CubicTerms) :
      evaluateTerms (p.map (fun (w, c) => (w, -c))) v = -evaluateTerms p v := by
    induction p with
    | nil => simp [evaluateTerms]
    | cons t p ih =>
      rcases t with ⟨w, c⟩
      simp only [List.map_cons, evaluateTerms, List.sum_cons] at ih ⊢
      rw [ih, Int.cast_neg, neg_mul, neg_add]
  have hm (p : CubicTerms) :
      evaluateTerms (p.map (fun (w, c) => (w.map reverseCoord, c))) v =
        evaluateTerms p (v ∘ reverseCoord) := by
    simp only [evaluateTerms, List.map_map, Function.comp_def]
  have h := evaluateTerms_of_zero_check v reverseTerms reverseTerms_check
  rw [reverseTerms, evaluateTerms_append, hm, hn, ← sub_eq_add_neg] at h
  exact sub_eq_zero.mp h

private def reverseEquiv (R : Type*) [CommRing R] : (Coord → R) ≃ₗ[R] (Coord → R) where
  toFun v := v ∘ reverseCoord
  invFun v := v ∘ reverseCoord
  left_inv v := funext fun i => congrArg v (reverseCoord_involutive i)
  right_inv v := funext fun i => congrArg v (reverseCoord_involutive i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Transposition and block exchange on the split Albert model. -/
private def reverseModel (R : Type*) [CommRing R] : Model R ≃ₗ[R] Model R :=
  (modelCoordinateEquiv R).trans ((reverseEquiv R).trans (modelCoordinateEquiv R).symm)

private theorem reverseModel_coordinates (R : Type*) [CommRing R] (x : Model R) (i : Coord) :
    modelCoordinateEquiv R (reverseModel R x) i =
      modelCoordinateEquiv R x (reverseCoord i) := by
  simp only [reverseModel, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

private theorem reverseModel_involutive (R : Type*) [CommRing R] (x : Model R) :
    reverseModel R (reverseModel R x) = x := by
  apply (modelCoordinateEquiv R).injective
  funext i
  rw [reverseModel_coordinates, reverseModel_coordinates, reverseCoord_involutive]

private theorem reverseModel_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (x : Model R) : mapModel f (reverseModel R x) = reverseModel S (mapModel f x) := by
  apply (modelCoordinateEquiv S).injective
  rw [modelCoordinateEquiv_natural f]
  funext i
  rw [reverseModel_coordinates, Function.comp_apply, reverseModel_coordinates,
    modelCoordinateEquiv_natural f]
  rfl

private theorem reverseModel_isSplitAutomorphism (R : Type) [CommRing R] :
    IsSplitAutomorphism (reverseModel R) := by
  apply splitAutomorphism_of_natural_norm
  · apply (modelCoordinateEquiv R).injective
    funext i
    rw [reverseModel_coordinates, modelCoordinateEquiv_unit]
    exact reverseCoord_unit i
  · intro S _ _
    refine ⟨reverseModel S, reverseModel_map (algebraMap R S), fun x => ?_⟩
    calc
      Albert.ShortDirectionSpecification.splitNorm (reverseModel S x) =
          evaluateTerms normTerms (modelCoordinateEquiv S (reverseModel S x)) :=
        (modelCoordinateEquiv_norm _).trans (evaluateTerms_norm _).symm
      _ = evaluateTerms normTerms (modelCoordinateEquiv S x) := by
        have he : modelCoordinateEquiv S (reverseModel S x) =
            (modelCoordinateEquiv S x) ∘ reverseCoord :=
          funext (reverseModel_coordinates S x)
        rw [he]
        exact reverseCoord_norm _
      _ = Albert.ShortDirectionSpecification.splitNorm x :=
        (evaluateTerms_norm _).trans (modelCoordinateEquiv_norm x).symm

noncomputable section

open LinearAlgebraicGroups.CocharacterDynamics
open private opposite_point from
  LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

variable {k : Type} [Field k] {G : GroupScheme k} (A : SplitAction G)

private def reversePoint (R : TestAlgebra k) : Points G.X R :=
  liftActionPoint A R (reverseModel R) (reverseModel_isSplitAutomorphism R)

private theorem reversePoint_action (R : TestAlgebra k) :
    A.action R (reversePoint A R) = reverseModel R :=
  liftActionPoint_action A R _ _

private theorem reversePoint_natural {R S : TestAlgebra k} (f : R ⟶ S) :
    mapPoints f (reversePoint A R) = reversePoint A S := by
  apply A.injective S
  apply linearEquiv_ext_of_mapModel f.hom.toRingHom
  intro x
  rw [← A.natural f, reversePoint_action, reversePoint_action]
  exact reverseModel_map f.hom.toRingHom x

private theorem reversePoint_inv (R : TestAlgebra k) :
    (reversePoint A R)⁻¹ = reversePoint A R := by
  apply inv_eq_of_mul_eq_one_right
  apply A.injective R
  rw [map_mul, map_one, reversePoint_action]
  apply LinearEquiv.ext
  intro x
  exact reverseModel_involutive R x

/-- Conjugation by the transposition symmetry reverses the chamber cocharacter. -/
private theorem reversePoint_conjugates (R : TestAlgebra k) (s : Rˣ) :
    reversePoint A R * (show Points G.X R from cocharacterPoint (chamberCocharacter A) R s) *
      (reversePoint A R)⁻¹ =
        cocharacterPoint (oppositeCocharacter (chamberCocharacter A)) R s := by
  apply A.injective R
  rw [reversePoint_inv, map_mul, map_mul, reversePoint_action,
    opposite_point, chamberCocharacter_action, chamberCocharacter_action]
  apply LinearEquiv.ext
  intro x
  apply (modelCoordinateEquiv R).injective
  funext i
  change modelCoordinateEquiv R
    (reverseModel R (diagonalModel (chamberParameter s) (reverseModel R x))) i =
    modelCoordinateEquiv R (diagonalModel (chamberParameter s⁻¹) x) i
  rw [reverseModel_coordinates]
  rw [diagonalModel_coordinates, diagonalModel_coordinates, diagonalCoefficient_chamber,
    diagonalCoefficient_chamber, reverseModel_coordinates, reverseCoord_involutive,
    reverseCoord_weight, _root_.inv_zpow]
  simp

end

end Reversal

section TangentComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LinearAlgebraicGroups.Specs LinearAlgebraicGroups.CocharacterDynamics
open Albert.TrialitySpecification (Model mapModel)
open Albert.ReductiveFiberSpecification (SplitAction)
open Matrix
open InfinitesimalCommutator (matrixDifferential)
open scoped CategoryTheory.MonObj DualNumber Matrix
open private matrixDifferentialLinear matrixDifferential_eq matrixCoefficient_injective from LinearAlgebraicGroups.Affine.LieBracket
open private lieMap_closed_injective from LinearAlgebraicGroups.Affine.LieLeftExact

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k : Type} [Field k]

/-- The differential of the Albert action, with the endomorphism interpreted
in the triple-matrix coordinate basis. -/
def splitActionDifferential (G : AffineAlgebraicGroup k) (A : SplitAction G.val) :
    letI : IsAffine G.val.X.left := G.property.1
    Lie k G.val →ₗ[k] Module.End k (Model k) := by
  letI : IsAffine G.val.X.left := G.property.1
  exact (matrixToOperator k).toLinearMap.comp (matrixDifferentialLinear (matrixRepresentation G A)
    (StandardGroups.generalLinearGroupPointsIso k Coord))

theorem splitActionDifferential_injective (G : AffineAlgebraicGroup k) (A : SplitAction G.val) :
    Function.Injective (splitActionDifferential G A) := by
  letI : IsAffine G.val.X.left := G.property.1
  let f := matrixRepresentation G A
  let l := StandardGroups.generalLinearGroupPointsIso k Coord
  intro x y h
  change matrixToOperator k (matrixDifferential f l x) =
    matrixToOperator k (matrixDifferential f l y) at h
  have he := (matrixToOperator k).injective h
  rw [matrixDifferential_eq, matrixDifferential_eq] at he
  have he' := matrixCoefficient_injective he
  let R := CommAlgCat.of k (DualNumber k)
  let p : Points G.val.X R := x.toMul.val
  let q : Points G.val.X R := y.toMul.val
  have hs : l.hom.app R (p ≫ f.hom.hom) = l.hom.app R (q ≫ f.hom.hom) :=
    congrArg (fun z => z.toMul.val) he'
  have hmat := (matrixRepresentation_apply G A R p).symm.trans
    (hs.trans (matrixRepresentation_apply G A R q))
  exact Subtype.ext (coordinateMatrixHom_injective A R hmat)

theorem splitActionDifferential_chamberTangent (G : AffineAlgebraicGroup k) (A : SplitAction G.val)
    (j : Fin 28) : splitActionDifferential G A (chamberTangent A j) = tangentOperator k j := by
  change matrixToOperator k (matrixDifferential (matrixRepresentation G A)
    (StandardGroups.generalLinearGroupPointsIso k Coord) (chamberTangent A j)) = _
  rw [chamberTangent_matrixDifferential, matrixToOperator_apply_operatorMatrix]

theorem splitActionDifferential_coordinates (G : AffineAlgebraicGroup k) (A : SplitAction G.val)
    (p : Lie k G.val) (v : Model k) (i : Coord) :
    let R := CommAlgCat.of k (DualNumber k)
    (modelCoordinateEquiv R
      (A.action R p.toMul.val (mapModel (algebraMap k R) v)) i).snd =
      modelCoordinateEquiv k ((splitActionDifferential G A p) v) i := by
  classical
  let R := CommAlgCat.of k (DualNumber k)
  let x := mapModel (algebraMap k R) v
  let M := (coordinateMatrixHom A R p.toMul.val).val
  let L := matrixDifferential (matrixRepresentation G A)
    (StandardGroups.generalLinearGroupPointsIso k Coord) p
  have hM (j l : Coord) : (M j l).snd = L j l := by
    change (M j l).snd =
      (((StandardGroups.generalLinearGroupPointsIso k Coord).hom.app R
        (p.toMul.val ≫ (matrixRepresentation G A).hom.hom)).val j l).snd
    rw [matrixRepresentation_apply]
  have h := congrFun (coordinateMatrixHom_mulVec A R p.toMul.val
    (modelCoordinateEquiv R x)) i
  rw [LinearEquiv.symm_apply_apply] at h
  have hdx : modelCoordinateEquiv k ((splitActionDifferential G A p) v) =
      L *ᵥ modelCoordinateEquiv k v := by
    change modelCoordinateEquiv k ((matrixToOperator k L) v) = _
    change modelCoordinateEquiv k ((modelCoordinateEquiv k).symm
      (Matrix.toLin' L ((modelCoordinateEquiv k) v))) = _
    rw [LinearEquiv.apply_symm_apply, Matrix.toLin'_apply]
  change (modelCoordinateEquiv R (A.action R p.toMul.val x) i).snd =
    modelCoordinateEquiv k ((splitActionDifferential G A p) v) i
  rw [← h, hdx, modelCoordinateEquiv_natural, Matrix.mulVec, Matrix.mulVec,
    dotProduct, dotProduct, TrivSqZeroExt.snd_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (M i j * algebraMap k (DualNumber k) (modelCoordinateEquiv k v j)).snd =
    L i j * modelCoordinateEquiv k v j
  rw [DualNumber.snd_mul, hM]
  change (M i j).fst * 0 + L i j * modelCoordinateEquiv k v j =
    L i j * modelCoordinateEquiv k v j
  rw [mul_zero, zero_add]

/-- A tangent vector of a frame stabilizer annihilates the actual three
frame vectors under the differential. -/
theorem splitActionDifferential_frame_fixed (G : AffineAlgebraicGroup k) (A : SplitAction G.val)
    (v : Model k) (p : Lie k G.val)
    (h : let R := CommAlgCat.of k (DualNumber k)
        A.action R p.toMul.val (mapModel (algebraMap k R) v) =
          mapModel (algebraMap k R) v) :
    splitActionDifferential G A p v = 0 := by
  apply (modelCoordinateEquiv k).injective
  funext i
  rw [← splitActionDifferential_coordinates, h, modelCoordinateEquiv_natural, map_zero]
  rfl

/-- The differential of the represented Albert action is injective and sends
the constructed tangent directions to their certified endomorphisms. -/
theorem chamberDifferential {k : Type} [Field k]
    (G : AffineAlgebraicGroup k) (a : SplitAction G.val) :
    letI : IsAffine G.val.X.left := G.property.1
    ∃ d : Lie k G.val →ₗ[k] Module.End k (Model k),
      Function.Injective d ∧ ∀ j, d (chamberTangent a j) = tangentOperator k j := by
  let : IsAffine G.val.X.left := G.property.1
  exact ⟨splitActionDifferential G a, splitActionDifferential_injective G a,
    splitActionDifferential_chamberTangent G a⟩

end

end TangentComparison

section ChamberRanks

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LinearAlgebraicGroups.Specs
open LinearAlgebraicGroups.CocharacterDynamics
open Albert.ReductiveFiberSpecification (SplitAction)
open scoped CategoryTheory.MonObj
open private groupIsoOfPointIso dualKernelIso from LinearAlgebraicGroups.Affine.IdentityTangent
open private unitEquiv unitPointHom_apply from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private contractingIso from LinearAlgebraicGroups.Flag.OpenCell
open private lieMap_closed_injective from LinearAlgebraicGroups.Affine.LieLeftExact
noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k : Type} [Field k]

private theorem chamberOppositeConjugate (G : AffineAlgebraicGroup k)
    (A : SplitAction G.val) :
    ∃ e : G.val ≅ G.val, chamberCocharacter A ≫ e.hom =
      oppositeCocharacter (chamberCocharacter A) := by
  letI : IsAffine G.val.X.left := G.property.1
  let i : (groupPointsFunctor k).obj G.val ≅ (groupPointsFunctor k).obj G.val :=
    NatIso.ofComponents (fun R => (MulAut.conj (reversePoint A R)).toGrpIso) fun {R S} f => by
      apply GrpCat.ext
      intro p
      change Points G.val.X R at p
      let m : Points G.val.X R →* Points G.val.X S := (((groupPointsFunctor k).obj G.val).map f).hom
      symm
      change m (reversePoint A R * p * (reversePoint A R)⁻¹) =
        reversePoint A S * m p * (reversePoint A S)⁻¹
      rw [map_mul, map_mul, map_inv, show m (reversePoint A R) = reversePoint A S
        from reversePoint_natural A f]
  let e := groupIsoOfPointIso i
  have he : (groupPointsFunctor k).map e.hom = i.hom :=
    (groupHomEquiv G.val G.val G.property.1).apply_symm_apply _
  refine ⟨e, ?_⟩
  apply (groupHomEquiv _ _ (inferInstanceAs
    (IsAffine (Spec (CommRingCat.of (MonoidAlgebra k DiagonalizableGroups.IntegerCharacters)))))).injective
  change (groupPointsFunctor k).map (_ ≫ _) = _
  rw [Functor.map_comp, he]
  apply NatTrans.ext
  funext R
  apply GrpCat.ext
  intro p
  change Points (gm (k := k)).X R at p
  let t := unitEquiv R p
  have ht : unitPoint R t = p :=
    (unitPointHom_apply R t).symm.trans ((unitEquiv R).symm_apply_apply p)
  change (i.hom.app R) (p ≫ (chamberCocharacter A).hom.hom) =
    p ≫ (oppositeCocharacter (chamberCocharacter A)).hom.hom
  rw [← ht]
  exact reversePoint_conjugates A R t

private theorem lieRank_of_iso {G H : GroupScheme k} [IsAffine G.X.left] [IsAffine H.X.left]
    (e : G ≅ H) : Module.finrank k (Lie k G) = Module.finrank k (Lie k H) := by
  let F := groupPointsFunctor k
  let d := lieMap e.hom
  let ed := dualKernelIso (F.mapIso e)
  have hb : Function.Bijective d := ed.bijective
  exact (LinearEquiv.ofBijective d hb).finrank_eq

private theorem lieRank_of_basis_support {G : GroupScheme k} [IsAffine G.X.left]
    (S : ClosedSubgroup G) [IsAffine S.group.X.left]
    {I : Type} [Fintype I] (b : Module.Basis I k (Lie k G))
    (p : I → Prop) [DecidablePred p]
    (h : lieImage S = {v | ∀ j, ¬ p j → b.equivFun v j = 0}) :
    Module.finrank k (Lie k S.group) = Fintype.card {i // p i} := by
  let e := lieMap S.inclusion
  have he : Function.Injective e := lieMap_closed_injective S.inclusion S.isClosedImmersion
  let d : Lie k S.group →ₗ[k] ({i // p i} → k) := {
    toFun v i := b.equivFun (e v) i.val
    map_add' v w := by ext i; simp
    map_smul' c v := by ext i; simp }

  have hmem (v : Lie k S.group) : ∀ j, ¬ p j → b.equivFun (e v) j = 0 :=
    by
      have hv : e v ∈ lieImage S := ⟨v, rfl⟩
      rw [h] at hv
      exact hv
  have hd : Function.Bijective d := by
    constructor
    · intro v w hv
      apply he
      apply b.equivFun.injective
      funext j
      by_cases hj : p j
      · exact congrFun hv ⟨j, hj⟩
      · rw [hmem v j hj, hmem w j hj]
    · intro u
      let v : I → k := fun j => if hj : p j then u ⟨j, hj⟩ else 0
      have hu : b.equivFun.symm v ∈ lieImage S := by
        rw [h]
        change ∀ j, ¬ p j → b.equivFun (b.equivFun.symm v) j = 0
        rw [LinearEquiv.apply_symm_apply]
        intro j hj
        exact dite_eq_right hj
      obtain ⟨a, ha⟩ := hu
      have hda : e a = b.equivFun.symm v := ha
      refine ⟨a, funext fun i => ?_⟩
      change b.equivFun (e a) i.val = u i
      rw [hda, LinearEquiv.apply_symm_apply]
      exact dite_eq_left i.property
  exact (LinearEquiv.ofBijective d hd).finrank_eq.trans (Module.finrank_pi k)

private theorem lieRank_at_least {G : GroupScheme k} [IsAffine G.X.left] [Module.Finite k (Lie k G)]
    (S : ClosedSubgroup G) [IsAffine S.group.X.left]
    {I : Type} [Fintype I] (v : I → Lie k G) (hv : LinearIndependent k v)
    (h : ∀ j, v j ∈ lieImage S) :
    Fintype.card I ≤ Module.finrank k (Lie k S.group) := by
  let d := lieMap S.inclusion
  letI : Module.Finite k (Lie k S.group) :=
    Module.Finite.of_injective d (lieMap_closed_injective S.inclusion S.isClosedImmersion)
  choose w hw using h
  have he : d ∘ w = v := funext hw
  exact (LinearIndependent.of_comp d (he.symm ▸ hv)).fintype_card_le_finrank

/-- The positive and nonnegative limit subgroups have the ranks of the
certified tangent families, and the cocharacter centralizer has rank four. -/
theorem chamberLieRanks (G : AffineAlgebraicGroup k) (A : SplitAction G.val)
    (hG : letI : IsAffine G.val.X.left := G.property.1
          Module.finrank k (Lie k G.val) = 52)
    (D : LimitDecomposition (chamberCocharacter A))
    (E : LimitDecomposition (oppositeCocharacter (chamberCocharacter A))) :
    letI : IsAffine D.parabolic.group.X.left :=
      (affineAlgebraicSubgroup D.parabolic G.property.1 G.property.2.1 G.property.2.2).property.1
    letI : IsAffine D.contracting.group.X.left :=
      (affineAlgebraicSubgroup D.contracting G.property.1 G.property.2.1 G.property.2.2).property.1
    letI : IsAffine D.centralizer.group.X.left :=
      (affineAlgebraicSubgroup D.centralizer G.property.1 G.property.2.1 G.property.2.2).property.1
    Module.finrank k (Lie k D.parabolic.group) = 28 ∧
    Module.finrank k (Lie k D.contracting.group) = 24 ∧
    Module.finrank k (Lie k D.centralizer.group) = 4 := by
  classical
  letI : IsAffine G.val.X.left := G.property.1
  letI : IsAffine D.parabolic.group.X.left :=
    (affineAlgebraicSubgroup D.parabolic G.property.1 G.property.2.1 G.property.2.2).property.1
  letI : IsAffine D.contracting.group.X.left :=
    (affineAlgebraicSubgroup D.contracting G.property.1 G.property.2.1 G.property.2.2).property.1
  letI : IsAffine D.centralizer.group.X.left :=
    (affineAlgebraicSubgroup D.centralizer G.property.1 G.property.2.1 G.property.2.2).property.1
  letI : IsAffine E.contracting.group.X.left :=
    (affineAlgebraicSubgroup E.contracting G.property.1 G.property.2.1 G.property.2.2).property.1
  let s := identityLieStructure G
  obtain ⟨W, hP, hU, hC⟩ := lieWeights G (chamberCocharacter A) D s
  letI : Module.Finite k (Lie k G.val) := Module.Finite.of_basis W.basis
  have hw := Module.finrank_eq_card_basis W.basis
  rw [hG] at hw
  have hneg : lieImage E.contracting =
      {v | ∀ j, 0 ≤ W.weight j → W.basis.equivFun v j = 0} := by
    ext v
    have h := relativeOppositeContractingWeights G (chamberCocharacter A) E s W
      (CommAlgCat.of k k) (W.basis.equivFun v)
    have he : W.coordinates.equiv (CommAlgCat.of k k) (W.basis.equivFun v) = v :=
      Subtype.ext (W.coordinates.at_base v)
    rw [he] at h
    refine Iff.trans ?_ h
    exact ⟨fun ⟨q,hq⟩ => ⟨q, congrArg (fun p : Lie k G.val => p.toMul.val) hq⟩,
      fun ⟨q,hq⟩ => ⟨q, Subtype.ext hq⟩⟩
  have rp := lieRank_of_basis_support D.parabolic W.basis (fun j => 0 ≤ W.weight j) (by
    simpa only [not_le] using hP)
  have ru := lieRank_of_basis_support D.contracting W.basis (fun j => 0 < W.weight j) (by
    simpa only [not_lt] using hU)
  have rc := lieRank_of_basis_support D.centralizer W.basis (fun j => W.weight j = 0) hC
  have re := lieRank_of_basis_support E.contracting W.basis (fun j => W.weight j < 0) (by
    simpa only [not_lt] using hneg)
  have rs : Module.finrank k (Lie k D.parabolic.group) +
      Module.finrank k (Lie k E.contracting.group) = 52 := by
    rw [rp, re, Fintype.card_subtype, Fintype.card_subtype, hw]
    simpa only [not_le, Finset.card_univ] using Finset.card_filter_add_card_filter_not
      (s := Finset.univ) (fun j => 0 ≤ W.weight j)
  have rps : Module.finrank k (Lie k D.contracting.group) +
      Module.finrank k (Lie k D.centralizer.group) =
      Module.finrank k (Lie k D.parabolic.group) := by
    rw [ru, rc, rp, Fintype.card_subtype, Fintype.card_subtype, Fintype.card_subtype]
    convert Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter (fun j => 0 ≤ W.weight j)) (fun j => 0 < W.weight j) using 2
    · congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => ⟨h.le, h⟩, And.right⟩
    · congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
      omega
  obtain ⟨d, _, hd⟩ := chamberDifferential G A
  have hli : LinearIndependent k (chamberTangent A) := by
    apply LinearIndependent.of_comp d
    have he : d ∘ chamberTangent A = tangentOperator k := funext hd
    rw [he]
    exact tangentOperator_linearIndependent k
  have hp : 28 ≤ Module.finrank k (Lie k D.parabolic.group) := by
    simpa only [Fintype.card_fin] using lieRank_at_least D.parabolic
      (chamberTangent A) hli (chamberTangent_mem_parabolic A D)
  have hu : 24 ≤ Module.finrank k (Lie k D.contracting.group) := by
    simpa only [Fintype.card_fin] using lieRank_at_least D.contracting
      (chamberTangent A ∘ positiveColumns)
      (hli.comp positiveColumns (Fin.castLE_injective _))
      (chamberTangent_mem_contracting A D)
  obtain ⟨e, he⟩ := chamberOppositeConjugate G A
  obtain ⟨j, _⟩ := contractingIso e D E he
  have hsymm := lieRank_of_iso j
  exact ⟨by omega, by omega, by omega⟩

end

end ChamberRanks

section Centralizer

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LinearAlgebraicGroups.Specs
open LinearAlgebraicGroups.CocharacterDynamics
open Albert.ReductiveFiberSpecification (SplitAction)
open Albert.TrialitySpecification (Model)
open Specs.GeometricRadicals (IsSplitTorus)
open scoped CategoryTheory.MonObj DualNumber

open private mapDualKernel_scale dualKernelIso from LinearAlgebraicGroups.Affine.IdentityTangent
open private gmCoordinate gmCoordinate_bijective lieMap_closed_injective from
  LinearAlgebraicGroups.Affine.LieLeftExact
open private centralizes_onAlgebras liftPointGroupHom from
  LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private isIso_of_closedImmersion_of_differential from
  LinearAlgebraicGroups.RootData.BorelsAndChambers
open private closedImmersion_of_injective_test_points from
  LinearAlgebraicGroups.Classification.RationalRealization
open private splitTorusSmooth from LinearAlgebraicGroups.Reductive.WeylScheme

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k : Type} [Field k]

theorem multiplicativePower_lie_finrank (I : Type) [Fintype I] :
    let P := Specs.StandardGroups.multiplicativePowerGroup k I
    letI : IsAffine P.val.X.left := P.property.1
    Module.finrank k (Lie k P.val) = Fintype.card I := by
  classical
  let P := Specs.StandardGroups.multiplicativePowerGroup k I
  letI : IsAffine P.val.X.left := P.property.1
  let F := Specs.StandardGroups.multiplicativePowerPoints k I
  let j : (groupPointsFunctor k).obj P.val ≅ F :=
    StandardGroups.multiplicativePowerGroupPointsIso k I
  let c (v : DualKernel F) (i : I) : k := (v.toMul.val i : DualNumber k).snd
  have hc : Function.Bijective c := by
    constructor
    · intro v w h
      apply Subtype.ext
      funext i
      let v' : DualKernel (Specs.StandardGroups.multiplicativePoints k) :=
        ⟨v.toMul.val i, congrFun v.toMul.property i⟩
      let w' : DualKernel (Specs.StandardGroups.multiplicativePoints k) :=
        ⟨w.toMul.val i, congrFun w.toMul.property i⟩
      exact congrArg (fun v => v.toMul.val)
        (gmCoordinate_bijective.1 (show gmCoordinate v' = gmCoordinate w' from congrFun h i))
    · intro v
      choose w hw using fun i : I => gmCoordinate_bijective.2 (v i)
      let v' : DualKernel F := ⟨fun i => (w i).toMul.val, funext fun i => (w i).toMul.property⟩
      exact ⟨v', funext hw⟩
  let d : Lie k P.val →ₗ[k] (I → k) := {
    toFun p := c (mapDualKernel j.hom p)
    map_add' p q := by
      change c (mapDualKernel j.hom (p + q)) = _
      rw [map_add]
      funext i
      let x := mapDualKernel j.hom p
      let y := mapDualKernel j.hom q
      have hx : (x.toMul.val i : DualNumber k).fst = 1 :=
        congrArg Units.val (congrFun x.toMul.property i)
      have hy : (y.toMul.val i : DualNumber k).fst = 1 :=
        congrArg Units.val (congrFun y.toMul.property i)
      change ((x.toMul.val i : DualNumber k) * (y.toMul.val i : DualNumber k)).snd =
        c x i + c y i
      rw [DualNumber.snd_mul, hx, hy, one_mul, mul_one, add_comm]
    map_smul' s p := by
      change c (mapDualKernel j.hom (scaleDualKernel ((groupPointsFunctor k).obj P.val) s p)) = _
      rw [mapDualKernel_scale j.hom s p]
      funext i
      change (dualNumberScale s ((mapDualKernel j.hom p).toMul.val i).val).snd = _
      rw [dualNumberScale, TrivSqZeroExt.snd_map]
      rfl }
  have hd : Function.Bijective d := hc.comp (dualKernelIso j).bijective
  exact (LinearEquiv.ofBijective d hd).finrank_eq.trans (Module.finrank_pi k)

private def parameterCoordinate : Fin 4 → Coord :=
  ![a 0 1, a 1 2, b 0 0, b 0 1]

private theorem diagonalCoefficient_parameter {R : Type} [CommRing R]
    (s : Fin 4 → Rˣ) (i : Fin 4) : diagonalCoefficient s (parameterCoordinate i) = s i := by
  have h (j : Fin 4) : diagonalExponents (parameterCoordinate i) j =
      if j = i then 1 else 0 := by
    fin_cases i <;> fin_cases j <;> rfl
  rw [diagonalCoefficient, Finset.prod_eq_single i]
  · simp only [h, ite_true, zpow_one]
  · intro j _ hj
    rw [h, ite_eq_right hj, zpow_zero]
  · simp

private theorem diagonalPoints_injective {G : GroupScheme k} (A : SplitAction G)
    (R : TestAlgebra k) : Function.Injective (diagonalPoints A R) := by
  intro s t h
  have h' := congrArg (A.action R) h
  rw [diagonalPoints_action, diagonalPoints_action] at h'
  funext i
  let j := parameterCoordinate i
  have e := congrArg (fun g : Model R ≃ₗ[R] Model R =>
    modelCoordinateEquiv R (g (modelBasisVector R j)) j) h'
  change modelCoordinateEquiv R (diagonalModel s (modelBasisVector R j)) j =
    modelCoordinateEquiv R (diagonalModel t (modelBasisVector R j)) j at e
  rw [diagonalModel_coordinates, diagonalModel_coordinates] at e
  simp only [modelBasisVector, LinearEquiv.apply_symm_apply, Pi.single_eq_same, mul_one, j,
    diagonalCoefficient_parameter] at e
  exact Units.ext e

private abbrev chamberTorus (k : Type) [Field k] :=
  Specs.StandardGroups.multiplicativePowerGroup k (ULift.{0} (Fin 4))

private def diagonalPointMap {G : GroupScheme k} (A : SplitAction G) :
    (groupPointsFunctor k).obj (chamberTorus k).val ⟶ (groupPointsFunctor k).obj G :=
  (StandardGroups.multiplicativePowerGroupPointsIso k (ULift.{0} (Fin 4))).hom ≫ {
    app R := GrpCat.ofHom ((diagonalPoints A R).comp {
      toFun := fun s i => s ⟨i⟩
      map_one' := rfl
      map_mul' _ _ := rfl })
    naturality {R S} f := by
      apply GrpCat.ext
      intro t
      exact (diagonalPoints_natural A f (fun i => t ⟨i⟩)).symm }

private theorem diagonalPointMap_injective {G : GroupScheme k} (A : SplitAction G)
    (R : TestAlgebra k) : Function.Injective ((diagonalPointMap A).app R).hom := by
  let e := (StandardGroups.multiplicativePowerGroupPointsIso k (ULift.{0} (Fin 4))).app R
  change Function.Injective ((fun s : ULift.{0} (Fin 4) → Rˣ =>
    diagonalPoints A R (fun i => s ⟨i⟩)) ∘ e.groupIsoToMulEquiv)
  apply Function.Injective.comp _ e.groupIsoToMulEquiv.injective
  intro s t h
  funext i
  exact congrFun (diagonalPoints_injective A R h) i.down

/-- The centralizer of the chamber is the split four-dimensional diagonal torus. -/
theorem chamberCentralizer_split (G : AffineAlgebraicGroup k) (A : SplitAction G.val)
    (D : LimitDecomposition (chamberCocharacter A))
    (hs : Smooth D.centralizer.group.X.hom) (hc : ConnectedSpace D.centralizer.group.X.left)
    (hr : letI : IsAffine D.centralizer.group.X.left :=
      (affineAlgebraicSubgroup D.centralizer G.property.1 G.property.2.1 G.property.2.2).property.1
      Module.finrank k (Lie k D.centralizer.group) = 4) :
    Nonempty ((chamberTorus k).val ≅ D.centralizer.group) := by
  let T := chamberTorus k
  let Z := affineAlgebraicSubgroup D.centralizer G.property.1 G.property.2.1 G.property.2.2
  letI : IsAffine T.val.X.left := T.property.1
  letI : IsAffine D.centralizer.group.X.left := Z.property.1
  obtain ⟨f, hf⟩ := liftPointGroupHom T.property.1 D.centralizer (diagonalPointMap A)
    (fun R t => (D.centralizer_points _ _).mp (by
      let u := (StandardGroups.multiplicativePowerGroupPointsIso k (ULift.{0} (Fin 4))).hom.app R t
      change Centralizes (chamberCocharacter A) (diagonalPoints A R fun i => u ⟨i⟩)
      apply (centralizes_onAlgebras _ _).mpr
      intro S m s
      change Commute (mapPoints m (diagonalPoints A R fun i => u ⟨i⟩))
        (show Points G.val.X S from cocharacterPoint (chamberCocharacter A) S s)
      rw [diagonalPoints_natural]
      apply A.injective S
      rw [map_mul, map_mul, diagonalPoints_action, chamberCocharacter_action]
      rw [← map_mul, ← map_mul, mul_comm]))
  have hfInj (R : TestAlgebra k) : Function.Injective
      (fun x : Points T.val.X R => x ≫ f.hom.hom) := by
    intro x y h
    apply diagonalPointMap_injective A R
    have ht := congrArg (fun q : Points Z.val.X R => q ≫ D.centralizer.inclusion.hom.hom) h
    change (((groupPointsFunctor k).map (f ≫ D.centralizer.inclusion)).app R).hom x =
      (((groupPointsFunctor k).map (f ≫ D.centralizer.inclusion)).app R).hom y at ht
    rwa [hf] at ht
  have hclosed := closedImmersion_of_injective_test_points (G := T) (H := Z) f hfInj
  have hTs : IsSplitTorus T.val := ⟨4, ⟨Iso.refl _⟩⟩
  have hTc : ConnectedSpace T.val.X.left := by
    let B := Specs.StandardGroups.LaurentPowerCoordinates k (ULift.{0} (Fin 4))
    let : IsDomain B := inferInstanceAs (IsDomain (AddMonoidAlgebra k (ULift.{0} (Fin 4) → ℤ)))
    exact inferInstanceAs (ConnectedSpace (PrimeSpectrum B))
  have hrT : Module.finrank k (Lie k T.val) = 4 := by
    simpa only [Fintype.card_ulift, Fintype.card_fin] using
      (multiplicativePower_lie_finrank (k := k) (ULift.{0} (Fin 4)))
  haveI : Module.Finite k (Lie k T.val) := Module.finite_of_finrank_pos (by rw [hrT]; decide)
  haveI : Module.Finite k (Lie k D.centralizer.group) := Module.finite_of_finrank_pos (by
    change 0 < Module.finrank k (Lie k D.centralizer.group)
    rw [hr]
    decide)
  have hdim : Module.finrank k (Lie k T.val) = Module.finrank k (Lie k D.centralizer.group) :=
    hrT.trans hr.symm
  have hdf : Function.Surjective (lieMap f) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
      (lieMap_closed_injective f hclosed)
  letI : IsIso f := isIso_of_closedImmersion_of_differential (A := T) (B := Z)
    f hclosed (splitTorusSmooth hTs) hTc hs hc hdf
  exact ⟨asIso f⟩

end

end Centralizer

section ChamberAndOpenCell

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open LinearAlgebraicGroups.Specs LinearAlgebraicGroups.CocharacterDynamics
open Albert.IntegralSmoothness (geometricFiberAction)
open Albert.IntegralSmoothnessSpecification (SplitGroup geometricFiber algebraicFiber)
open Albert.ShortDirectionSpecification (IntegralPresentation)
open Albert.AutomorphismTypeSpecification (IntegralSplitIdentification chevalleyChange)
open Albert.ReductiveFiberSpecification (SplitAction)
open Specs.GeometricRadicals (IsSplitTorus)
open Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel
open OrderedRootProducts (Enumerates)

open private IntegralMarkedCellCoordinates affineObject integralCellCoordinateMap
  integralCellCoordinateMap_isIso from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

noncomputable section

variable {k : Type} [Field k]

theorem splitFibre_geometricallyConnected (S : IntegralSplitIdentification)
    {P : IntegralPresentation} (G : SplitGroup P) :
    GeometricallyConnected (geometricFiber G k).X.hom := by
  let e := splitFibreIso (k := k) G S.split
  let i : (geometricFiber G k).X ≅ (geometricFiber S.split k).X :=
    (Grp.forget (SchemeOver k)).mapIso e
  have : IsIso i.hom.left := (Over.forget _).map_isIso i.hom
  have h : GeometricallyConnected (geometricFiber S.split k).X.hom := by
    letI := S.connected
    exact inferInstanceAs (GeometricallyConnected
      (pullback.snd S.split.group.X.hom (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))))
  letI : MorphismProperty.RespectsIso (@GeometricallyConnected.{0}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact i.hom.w ▸ (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected.{0}
    i.hom.left (geometricFiber S.split k).X.hom).mpr h

/-- The chamber in any presented split Albert fibre has smooth limit
subgroups and its centralizer is a split torus. -/
theorem splitFibre_chamberCentralizer (S : IntegralSplitIdentification)
    {P : IntegralPresentation} (G : SplitGroup P)
    (D : LimitDecomposition (chamberCocharacter (geometricFiberAction G k))) :
    IsSplitTorus D.centralizer.group ∧ Smooth D.parabolic.group.X.hom ∧
      Smooth D.contracting.group.X.hom := by
  let A := algebraicFiber G k
  let a := geometricFiberAction G k
  letI : IsAffine A.val.X.left := A.property.1
  letI hd : SmoothOfRelativeDimension 52 A.val.X.hom := splitFibre_smoothDimension S G
  letI : Smooth A.val.X.hom := SmoothOfRelativeDimension.smooth 52 A.val.X.hom
  letI : GeometricallyConnected A.val.X.hom := splitFibre_geometricallyConnected S G
  letI : ConnectedSpace A.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton A.val.X.hom
  obtain ⟨E⟩ := existsLimitDecomposition A (oppositeCocharacter (chamberCocharacter a))
  have hr := chamberLieRanks A a (lie_finrank_of_smoothDimension 52 hd) D E
  obtain ⟨hsp, hsu, hsc⟩ := limitSubgroupsSmooth A (chamberCocharacter a) D
  letI : GeometricallyConnected D.centralizer.group.X.hom :=
    (geometricallyConnectedLimitSubgroups A (chamberCocharacter a) D).2.2
  have hc := GeometricallyConnected.connectedSpace_of_subsingleton D.centralizer.group.X.hom
  obtain ⟨e⟩ := chamberCentralizer_split A a D hsc hc hr.2.2
  exact ⟨⟨4, ⟨e.symm⟩⟩, hsp, hsu⟩

/-- The ordered marked open cell has the Laurent polynomial coordinate ring
of the character lattice and the affine coordinates of all root groups. -/
theorem integralChevalley_openChart {D : BasedRootDatum.{0}} (C : Model D) :
    ∃ c : affineObject (k := Integers.{0}) (IntegralMarkedCellCoordinates D) ⟶ C.group.X,
      IsOpenImmersion c.left := by
  classical
  letI := D.finiteRoots
  letI := Fintype.ofFinite D.I
  let n := Finset.univ.filter (fun i : D.I => ¬ D.base.IsPos i)
  let p := Finset.univ.filter (fun i : D.I => D.base.IsPos i)
  have hn : Enumerates n.toList {i | ¬ D.base.IsPos i} := by
    refine ⟨Finset.nodup_toList _, fun i => ?_⟩
    simp [n]
  have hp : Enumerates p.toList {i | D.base.IsPos i} := by
    refine ⟨Finset.nodup_toList _, fun i => ?_⟩
    simp [p]
  let x := integralCellCoordinateMap C.line n.toList p.toList
  let y := cellMap C.line C.torus C.root n.toList p.toList
  haveI : IsIso x := integralCellCoordinateMap_isIso C.line n.toList p.toList hn hp
  haveI : IsOpenImmersion y.left := C.openCell n.toList p.toList hn hp
  haveI : IsIso x.left := (Over.forget _).map_isIso x
  exact ⟨x ≫ y, inferInstanceAs (IsOpenImmersion (x.left ≫ y.left))⟩

end

end ChamberAndOpenCell

section ChartBaseChange

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Algebra.TensorProduct
open scoped TensorProduct
open LinearAlgebraicGroups.Specs
open Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel
open Albert.AutomorphismTypeSpecification (IntegralSplitIdentification chevalleyChange)
open private IntegralMarkedCellCoordinates affineObject overPullback_map_isPullback
  from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

noncomputable section

/-- The spectrum of the tensor product realizes the scalar extension of an
affine scheme, with the indicated order of the tensor factors. -/
private def affineBaseChangeIso (R A B : Type) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    affineObject (k := B) (B ⊗[R] A) ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).obj
        (affineObject (k := R) A) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let g := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let e := (pullbackSpecIso R B A).symm ≪≫ pullbackSymmetry f g
  refine Over.isoMk e ?_
  change ((pullbackSpecIso R B A).inv ≫ (pullbackSymmetry f g).hom) ≫
      pullback.snd g f = Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[R] A)))
  rw [Category.assoc, pullbackSymmetry_hom_comp_snd]
  exact pullbackSpecIso_inv_fst' R B A

/-- The coordinate algebra of a Chevalley open cell over a coefficient ring. -/
abbrev chevalleyCellCoordinates (D : BasedRootDatum.{0}) (R : Type) [CommRing R] :=
  MvPolynomial D.I (MonoidAlgebra R (Multiplicative D.X))

/-- Polynomial coordinates and character monomials commute with scalar extension. -/
def chevalleyCellCoordinates_baseChange (D : BasedRootDatum.{0}) (R S : Type)
    [CommRing R] [CommRing S] [Algebra R S] :
    S ⊗[R] chevalleyCellCoordinates D R ≃ₐ[S] chevalleyCellCoordinates D S :=
  MvPolynomial.rTensorAlgEquiv.trans <|
    MvPolynomial.mapAlgEquiv D.I
      ((MonoidAlgebra.rTensorEquivAlgEquiv R S S R).trans
        (MonoidAlgebra.mapAlgEquiv S (Multiplicative D.X) (Algebra.TensorProduct.rid R S S)))

/-- The open cell in the Chevalley fibre is parametrized by one variable for
each root and by the split torus of the original character lattice. -/
theorem chevalleyFibre_openChart {D : BasedRootDatum.{0}} (C : Model D) (k : Type) [Field k] :
    ∃ c : affineObject (k := k) (chevalleyCellCoordinates D k) ⟶
      ((chevalleyChange k).obj C.group).X, IsOpenImmersion c.left := by
  let R := Integers.{0}
  letI : Algebra R k := integerAlgebra k
  let f := Spec.map (CommRingCat.ofHom (algebraMap R k))
  let F := Over.pullback f
  let A := IntegralMarkedCellCoordinates D
  obtain ⟨c, hc⟩ := integralChevalley_openChart C
  let e := chevalleyCellCoordinates_baseChange D R k
  let i := (testSpec k).mapIso (CommAlgCat.isoMk e).op
  let j := affineBaseChangeIso R A k
  let g := F.map c
  letI : IsOpenImmersion g.left := MorphismProperty.of_isPullback
    (overPullback_map_isPullback f c).flip hc
  letI : IsIso i.hom.left := (Over.forget _).map_isIso i.hom
  letI : IsIso j.hom.left := (Over.forget _).map_isIso j.hom
  exact ⟨i.hom ≫ j.hom ≫ g, inferInstanceAs (IsOpenImmersion (i.hom.left ≫ j.hom.left ≫ g.left))⟩

end

end ChartBaseChange

section Invariant

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LinearAlgebraicGroups.Specs
open LinearAlgebraicGroups.CocharacterDynamics
open Albert.ReductiveFiberSpecification (SplitAction)
open Albert.TrialitySpecification (Model mapModel)
open Albert.FrameSpecification (frameAxis)
open scoped CategoryTheory.MonObj
section

variable {R : Type*} [CommRing R]

/-- The wedge of the two lowest-coordinate values detects the projective
invariant of the positive limit subgroup. -/
def lowestCoordinateWedge (v w : Slot → Coord → R) : R :=
  w 0 (a 2 0) * v 1 (a 2 0) - w 1 (a 2 0) * v 0 (a 2 0)

/-- Coefficient of the transverse elementary action on the lowest-coordinate wedge. -/
def transverseCoefficient (v : Slot → Coord → R) : R :=
  v 1 (a 2 1) * v 0 (a 2 0) - v 0 (a 2 1) * v 1 (a 2 0)

theorem transverseCoefficient_map {S : Type*} [CommRing S] (f : R →+* S)
    (v : Slot → Coord → R) : transverseCoefficient (fun i j => f (v i j)) =
      f (transverseCoefficient v) := by
  simp only [transverseCoefficient, map_sub, map_mul]

/-- The same integral frame works for the two rank inequalities and for the
transverse elementary direction. -/
theorem transverseCoefficient_movedFrame (R : Type*) [CommRing R] :
    transverseCoefficient (movedFrame (R := R)) = 1 := by
  have h : transverseCoefficient (movedFrame (R := ℤ)) = 1 := by decide
  let f := Int.castRingHom R
  have e : movedFrame (R := R) = fun i j => f (movedFrame (R := ℤ) i j) :=
    funext fun i => (movedFrame_map f i).symm
  rw [e, transverseCoefficient_map, h, map_one]

theorem lowestCoordinateWedge_elementary (v : Slot → Coord → R) (t : R) :
    lowestCoordinateWedge v (fun i => elementaryAction 1 0 t (v i)) =
      t * transverseCoefficient v := by
  have h (i : Slot) : elementaryAction 1 0 t (v i) (a 2 0) =
      v i (a 2 0) - t * v i (a 2 1) := by
    change v i (a 2 0) + (if (2 : Slot) = 1 then t * v i (a 0 0) else 0) -
      (if (0 : Slot) = 0 then t * v i (a 2 1) else 0) -
      (if (2 : Slot) = 1 ∧ (0 : Slot) = 0 then t ^ 2 * v i (a 0 1) else 0) = _
    simp
  simp only [lowestCoordinateWedge, transverseCoefficient, h]
  ring

end

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k : Type} [Field k] {G : GroupScheme k} (A : SplitAction G)

/-- A geometric frame at which both rank bounds and the transverse coefficient hold. -/
theorem exists_frame_with_transverse_ranks :
    ∃ p : Points G.X (CommAlgCat.of k k),
      let v := fun i => modelCoordinateEquiv k (A.action _ p (frameAxis i))
      frameRankPolynomial v ≠ 0 ∧ transverseCoefficient v = 1 := by
  obtain ⟨e, he, hframe⟩ := exists_movedFrame k
  let p := liftActionPoint A (CommAlgCat.of k k) e he
  refine ⟨p, ?_⟩
  have h : (fun i => modelCoordinateEquiv k (A.action _ p (frameAxis i))) = movedFrame :=
    funext fun i => by rw [liftActionPoint_action, hframe]
  dsimp only
  rw [h]
  exact ⟨movedFrame_rankPolynomial_ne_zero k, transverseCoefficient_movedFrame k⟩

/-- The elementary one-parameter action used for the transverse slice. -/
def transversePoint (R : TestAlgebra k) (t : R) : Points G.X R :=
  liftActionPoint A R (elementaryModelEquiv 1 0 (by decide) t)
    (elementaryModelEquiv_isSplitAutomorphism 1 0 (by decide) t)

theorem transversePoint_value (R : TestAlgebra k) (v : Slot → Model R) (t : R) :
    lowestCoordinateWedge (fun i => modelCoordinateEquiv R (v i))
      (fun i => modelCoordinateEquiv R (A.action R (transversePoint A R t) (v i))) =
      t * transverseCoefficient (fun i => modelCoordinateEquiv R (v i)) := by
  have h (i : Slot) : modelCoordinateEquiv R (A.action R (transversePoint A R t) (v i)) =
      elementaryAction 1 0 t (modelCoordinateEquiv R (v i)) := by
    rw [transversePoint, liftActionPoint_action, elementaryModelEquiv_coordinates]
  simp only [h, lowestCoordinateWedge_elementary]

/-- Multiplication of a limit-parabolic point and a frame stabilizer point
preserves the projective lowest-coordinate invariant over every test algebra. -/
theorem lowestCoordinateWedge_mul_eq_zero (R : TestAlgebra k) (v : Slot → Model R)
    (p q : Points G.X R) (hp : HasExtension (chamberCocharacter A) p)
    (hq : ∀ i, A.action R q (v i) = v i) :
    lowestCoordinateWedge (fun i => modelCoordinateEquiv R (v i))
      (fun i => modelCoordinateEquiv R (A.action R (p * q) (v i))) = 0 := by
  have h (i : Slot) : modelCoordinateEquiv R (A.action R (p * q) (v i)) (a 2 0) =
      (coordinateMatrixHom A R p).val (a 2 0) (a 2 0) *
        modelCoordinateEquiv R (v i) (a 2 0) := by
    rw [map_mul]
    change modelCoordinateEquiv R (A.action R p (A.action R q (v i))) _ = _
    rw [hq]
    exact chamber_lowest_coordinate A R p hp (v i)
  simp only [lowestCoordinateWedge, h]
  ring

/-- In the product map with an added transverse factor, the identity fibre
forces the parameter of that factor to vanish. -/
theorem transversePoint_factor_parameter_zero (R : TestAlgebra k) (v : Slot → Model R)
    (hv : IsUnit (transverseCoefficient (fun i => modelCoordinateEquiv R (v i))))
    (t : R) (p q : Points G.X R) (hp : HasExtension (chamberCocharacter A) p)
    (hq : ∀ i, A.action R q (v i) = v i)
    (he : transversePoint A R t = p * q) : t = 0 := by
  have h := transversePoint_value A R v t
  rw [he, lowestCoordinateWedge_mul_eq_zero A R v p q hp hq] at h
  exact hv.mul_right_cancel (h.symm.trans (zero_mul _).symm)

end

end Invariant

section TransverseLine

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs
open Albert.TrialitySpecification (Model)
open Albert.ReductiveFiberSpecification (SplitAction)
noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k : Type} [Field k]

private theorem elementaryAction_transverse_zero {R : Type} [CommRing R] (v : Coord → R) :
    elementaryAction 1 0 0 v = v := by
  funext i
  fin_cases i <;> simp [elementaryAction, coord, a, b, d]

private theorem elementaryAction_transverse_add {R : Type} [CommRing R] (t s : R)
    (v : Coord → R) :
    elementaryAction 1 0 (t + s) v = elementaryAction 1 0 t (elementaryAction 1 0 s v) := by
  funext i
  fin_cases i <;>
    simp [elementaryAction, coord, a, b, d] <;> ring

private theorem transversePoint_action {G : GroupScheme k} (A : SplitAction G)
    (R : TestAlgebra k) (t : R) :
    A.action R (transversePoint A R t) = elementaryModelEquiv 1 0 (by decide) t :=
  liftActionPoint_action A R _ _

private def transversePointsHom {G : GroupScheme k} (A : SplitAction G)
    (R : TestAlgebra k) : Multiplicative R →* Points G.X R where
  toFun t := transversePoint A R t.toAdd
  map_one' := by
    change transversePoint A R (0 : R) = (1 : Points G.X R)
    apply A.injective R
    rw [(A.action R).map_one, transversePoint_action]
    apply LinearEquiv.ext
    intro x
    apply (modelCoordinateEquiv R).injective
    rw [elementaryModelEquiv_coordinates]
    exact elementaryAction_transverse_zero _
  map_mul' t s := by
    change transversePoint A R (t.toAdd + s.toAdd) =
      transversePoint A R t.toAdd * transversePoint A R s.toAdd
    apply A.injective R
    rw [(A.action R).map_mul, transversePoint_action, transversePoint_action,
      transversePoint_action]
    apply LinearEquiv.ext
    intro x
    apply (modelCoordinateEquiv R).injective
    change (modelCoordinateEquiv R) (elementaryModelEquiv 1 0 (by decide) (t.toAdd + s.toAdd) x) =
      (modelCoordinateEquiv R) (elementaryModelEquiv 1 0 (by decide) t.toAdd
        (elementaryModelEquiv 1 0 (by decide) s.toAdd x))
    simp only [elementaryModelEquiv_coordinates, elementaryAction_transverse_add]

private def transversePointTransformation {G : GroupScheme k} (A : SplitAction G) :
    Specs.StandardGroups.additivePoints k ⟶ (groupPointsFunctor k).obj G where
  app R := GrpCat.ofHom (transversePointsHom A R)
  naturality {R S} f := by
    apply GrpCat.ext
    intro t
    change Multiplicative R at t
    change transversePoint A S (f.hom t.toAdd) = mapPoints f (transversePoint A R t.toAdd)
    apply A.injective S
    apply linearEquiv_ext_of_mapModel f.hom.toRingHom
    intro x
    rw [← A.natural f, transversePoint_action, transversePoint_action]
    apply (modelCoordinateEquiv S).injective
    rw [modelCoordinateEquiv_natural, elementaryModelEquiv_coordinates,
      elementaryModelEquiv_coordinates, modelCoordinateEquiv_natural]
    exact elementaryAction_map f.hom.toRingHom 1 0 t.toAdd _ |>.symm

/-- The transverse elementary line is a group scheme homomorphism. -/
def transverseLine {G : GroupScheme k} (A : SplitAction G) :
    (StandardGroups.additiveGroup k).val ⟶ G :=
  (groupHomEquiv _ _ (StandardGroups.additiveGroup k).property.1).symm
    ((StandardGroups.additiveGroupPointsIso k).hom ≫ transversePointTransformation A)

theorem transverseLine_apply {G : GroupScheme k} (A : SplitAction G)
    (R : TestAlgebra k) (p : Points (StandardGroups.additiveGroup k).val.X R) :
    p ≫ (transverseLine A).hom.hom = transversePoint A R
      (((StandardGroups.additiveGroupPointsIso k).hom.app R).hom p : Multiplicative R).toAdd := by
  have h := (groupHomEquiv (StandardGroups.additiveGroup k).val G
    (StandardGroups.additiveGroup k).property.1).apply_symm_apply
    ((StandardGroups.additiveGroupPointsIso k).hom ≫ transversePointTransformation A)
  change (groupPointsFunctor k).map (transverseLine A) = _ at h
  exact DFunLike.congr_fun (congrArg (fun a => (a.app R).hom) h) p

end

end TransverseLine

section Submersion

open Algebra TensorProduct KaehlerDifferential
open _root_.Specs.LinearAlgebraicGroups.Albert.SmoothIdentityCriterion
open LinearAlgebraicGroups.Albert.SmoothIdentityCriterion
open _root_.Specs.AdvCommAlg.Differentials.Tangent (PointLifts)

noncomputable section

/-- If a map of finite type algebras has injective cotangent map at a point
with smooth source over the ground field, it is smooth at that point. -/
theorem smoothAt_of_injective_cotangentFiber
    (k A B K : Type*) [Field k] [Field K] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    [Algebra A K] [Algebra B K] [IsScalarTower A B K]
    [Algebra.FiniteType k A] [Algebra.FiniteType k B] [Algebra.Smooth k B]
    (hf : Function.Injective (cotangentFiberMap k A B K)) :
    letI : (RingHom.ker (algebraMap B K)).IsPrime := RingHom.ker_isPrime _
    Algebra.IsSmoothAt A (RingHom.ker (algebraMap B K)) := by
  let q := RingHom.ker (algebraMap B K)
  letI : q.IsPrime := RingHom.ker_isPrime _
  let L := Localization.AtPrime q
  let y : L →+* K := IsLocalization.lift (M := q.primeCompl) (fun a =>
    isUnit_iff_ne_zero.mpr a.property)
  letI : Algebra L K := y.toAlgebra
  letI : IsScalarTower B L K := .of_algebraMap_eq' (IsLocalization.lift_comp _).symm
  letI : IsScalarTower A L K := .to₁₃₄ _ B _ _
  letI : FormallyEtale B L := FormallyEtale.of_isLocalization q.primeCompl
  letI : FormallySmooth k L := FormallySmooth.comp _ B _
  letI : EssFiniteType k L := .comp _ B _
  have hi : Function.Injective (cotangentFiberMap k A L K) := by
    rw [cotangentFiberMap_comp (B := B)]
    exact (cotangentFiberMap_bijective_of_formallyEtale (R := k) (B := B) (C := L)
      (K := K)).injective.comp hf
  let f := mapBaseChange k A L
  have hK : Function.Injective (f.baseChange K) := by
    change Function.Injective (f.baseChange K ∘ₗ
      (AlgebraTensorModule.cancelBaseChange A L K K Ω[A⁄k]).symm.toLinearMap) at hi
    exact ((AlgebraTensorModule.cancelBaseChange A L K K Ω[A⁄k]).symm.injective_comp _).mp hi
  have hker : IsLocalRing.maximalIdeal L ≤ RingHom.ker (algebraMap L K) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q]
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change algebraMap L K (algebraMap B L a) = 0
    rw [← IsScalarTower.algebraMap_apply B L K]
    exact ha
  let E := IsLocalRing.ResidueField L
  let g : E →ₐ[L] K := Ideal.Quotient.liftₐ _ (Algebra.ofId L K) hker
  letI : Algebra E K := g.toAlgebra
  letI : IsScalarTower L E K := .of_algebraMap_eq' g.comp_algebraMap.symm
  have he : (AlgebraTensorModule.cancelBaseChange L E K K Ω[L⁄k]).toLinearMap ∘ₗ
      (f.baseChange E).baseChange K =
      f.baseChange K ∘ₗ
        (AlgebraTensorModule.cancelBaseChange L E K K (L ⊗[A] Ω[A⁄k])).toLinearMap := by
    apply AlgebraTensorModule.ext
    intro a v
    induction v using TensorProduct.inductionOn with
    | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
    | tmul b x => simp [LinearMap.baseChange_tmul]
  have hE : Function.Injective (f.baseChange E) := by
    apply (Module.FaithfullyFlat.lTensor_injective_iff_injective E K _).mp
    apply ((AlgebraTensorModule.cancelBaseChange L E K K Ω[L⁄k]).comp_injective _).mp
    change Function.Injective (⇑((AlgebraTensorModule.cancelBaseChange L E K K Ω[L⁄k]).toLinearMap ∘ₗ
      (f.baseChange E).baseChange K))
    rw [he, LinearMap.coe_comp]
    exact hK.comp (AlgebraTensorModule.cancelBaseChange L E K K (L ⊗[A] Ω[A⁄k])).injective
  exact formallySmooth_of_injective_residueDifferentials k A L hE

/-- Dual-number lifting at compatible rational points implies smoothness
of a morphism at its source point when the source is smooth over the field. -/
theorem smoothAt_of_surjective_pointLifts
    {k A B : Type*} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra.FiniteType k A] [Algebra.FiniteType k B]
    [Algebra.Smooth k B]
    (f : A →ₐ[k] B) (y : B →ₐ[k] k)
    (h : ∀ a : PointLifts k A k (y.comp f),
      ∃ b : PointLifts k B k y, b.val.comp f = a.val) :
    letI : Algebra A B := f.toAlgebra
    letI : (RingHom.ker y.toRingHom).IsPrime := RingHom.ker_isPrime _
    Algebra.IsSmoothAt A (RingHom.ker y.toRingHom) := by
  let x := y.comp f
  letI : Algebra A B := f.toAlgebra
  letI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  letI : Algebra A k := x.toAlgebra
  letI : Algebra B k := y.toAlgebra
  letI : IsScalarTower A B k := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower k A k := IsScalarTower.of_algebraMap_eq' x.comp_algebraMap.symm
  letI : IsScalarTower k B k := IsScalarTower.of_algebraMap_eq' y.comp_algebraMap.symm
  apply smoothAt_of_injective_cotangentFiber k A B k
  rw [← LinearMap.dualMap_surjective_iff]
  intro l
  let d := tangentEquivDerivation k A k
  let e := tangentEquivDerivation k B k
  obtain ⟨L, hL, -⟩ := AdvCommAlg.Differentials.point_tangent_lifts k A k x
  obtain ⟨M, hM, -⟩ := AdvCommAlg.Differentials.point_tangent_lifts k B k y
  obtain ⟨b, hb⟩ := h (L (d l))
  refine ⟨e.symm (M.symm b), d.injective ?_⟩
  ext a
  have ha := congrArg (fun p : A →ₐ[k] DualNumber k => (p a).snd) hb
  change (b.val (f a)).snd = ((L (d l)).val a).snd at ha
  rw [hL] at ha
  have hm := hM (M.symm b) (f a)
  rw [Equiv.apply_symm_apply] at hm
  have hm' : (b.val (f a)).snd = (M.symm b) (f a) :=
    congrArg TrivSqZeroExt.snd hm
  change d ((cotangentFiberMap k A B k).dualMap (e.symm (M.symm b))) a = d l a
  calc
    _ = e (e.symm (M.symm b)) (f a) := by
      change tangentEquivDerivation k A k _ a = tangentEquivDerivation k B k _ (f a)
      rw [tangentEquivDerivation_apply, tangentEquivDerivation_apply,
        LinearMap.dualMap_apply, cotangentFiberMap_tmul, KaehlerDifferential.map_D]
      rfl
    _ = (M.symm b) (f a) := by rw [Equiv.apply_symm_apply]
    _ = (b.val (f a)).snd := hm'.symm
    _ = d l a := ha

end

end Submersion

section SchemeSubmersion

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open LinearAlgebraicGroups.Specs
open Algebra
open _root_.Specs.AdvCommAlg.Differentials.Tangent (PointLifts)
open private affineSpectrum specFF affinePointEquiv affinePointEquiv_natural smooth_affine_iff from
  LinearAlgebraicGroups.Reductive.CocharacterSmoothAndUnipotent

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k : Type} [Field k]

private theorem finiteType_affine {A : TestAlgebra k}
    {X : SchemeOver k} (e : affineSpectrum A ≅ X) (h : LocallyOfFiniteType X.hom) :
    Algebra.FiniteType k A := by
  letI := h
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have hf : LocallyOfFiniteType (e.hom.left ≫ X.hom) := inferInstance
  have hs : LocallyOfFiniteType (affineSpectrum A).hom := e.hom.w ▸ hf
  exact (RingHom.finiteType_algebraMap.mp ((HasRingHomProperty.Spec_iff
    (P := @LocallyOfFiniteType)).mp hs))

set_option maxHeartbeats 900000 in
/-- A dual-number lifting criterion for a smooth neighbourhood of a rational
point of a morphism between affine schemes. -/
theorem smoothNeighbourhood_of_dualPointLifting {X Y : SchemeOver k}
    (f : X ⟶ Y) [IsAffine X.left] [IsAffine Y.left]
    [Smooth X.hom] [LocallyOfFiniteType Y.hom]
    (x : Points X (CommAlgCat.of k k))
    (h : ∀ p : Points Y (CommAlgCat.of k (DualNumber k)),
      mapPoints (dualReduction k) p = x ≫ f →
        ∃ q : Points X (CommAlgCat.of k (DualNumber k)),
          mapPoints (dualReduction k) q = x ∧ q ≫ f = p) :
    ∃ (W : SchemeOver k) (j : W ⟶ X),
      IsOpenImmersion j.left ∧ Smooth (j.left ≫ f.left) ∧
        ∃ x' : Points W (CommAlgCat.of k k), x' ≫ j = x := by
  obtain ⟨A', ⟨eY⟩⟩ := essImage_algSpec.mpr (inferInstance : IsAffine Y.left)
  obtain ⟨B', ⟨eX⟩⟩ := essImage_algSpec.mpr (inferInstance : IsAffine X.left)
  let A := A'.unop
  let B := B'.unop
  let s := eX.hom ≫ f ≫ eY.inv
  let F := (specFF k).preimage s
  let f₀ : A →ₐ[k] B := F.unop.hom
  have hf : (testSpec k).map (CommAlgCat.ofHom f₀).op = s :=
    (specFF k).map_preimage s
  let y : B →ₐ[k] k := (affinePointEquiv eX (CommAlgCat.of k k)).symm x
  have hy : affinePointEquiv eX (CommAlgCat.of k k) y = x :=
    (affinePointEquiv eX _).apply_symm_apply x
  have hcomp {R : TestAlgebra k} (a : B →ₐ[k] R) :
      affinePointEquiv eX R a ≫ f = affinePointEquiv eY R (a.comp f₀) := by
    change ((testSpec k).map (CommAlgCat.ofHom a).op ≫ eX.hom) ≫ f =
      (testSpec k).map ((CommAlgCat.ofHom f₀) ≫ CommAlgCat.ofHom a).op ≫ eY.hom
    rw [op_comp, Functor.map_comp, hf]
    simp only [s, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  letI : FiniteType k A := finiteType_affine eY inferInstance
  letI : FiniteType k B := finiteType_affine eX inferInstance
  letI : Smooth k B := (smooth_affine_iff eX).mp inferInstance
  have hl : ∀ a : PointLifts k A k (y.comp f₀),
      ∃ b : PointLifts k B k y, b.val.comp f₀ = a.val := by
    intro a
    let R := CommAlgCat.of k (DualNumber k)
    let p : Points Y R := affinePointEquiv eY R a.val
    have ha : (dualReduction k).hom.comp a.val = y.comp f₀ := a.property
    have hp : mapPoints (dualReduction k) p = x ≫ f := by
      rw [← affinePointEquiv_natural eY, ha, ← hcomp, hy]
    obtain ⟨q, hq, hqf⟩ := h p hp
    let b : B →ₐ[k] R := (affinePointEquiv eX R).symm q
    have hb : affinePointEquiv eX R b = q := (affinePointEquiv eX R).apply_symm_apply q
    have hby : (dualReduction k).hom.comp b = y := by
      apply (affinePointEquiv eX _).injective
      rw [affinePointEquiv_natural, hb, hq, hy]
    refine ⟨⟨b, hby⟩, (affinePointEquiv eY R).injective ?_⟩
    rw [← hcomp, hb, hqf]
  letI : Algebra A B := f₀.toAlgebra
  letI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' f₀.comp_algebraMap.symm
  let q := RingHom.ker y.toRingHom
  letI : q.IsPrime := RingHom.ker_isPrime _
  letI : IsSmoothAt A q := smoothAt_of_surjective_pointLifts f₀ y hl
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  letI : FiniteType A B := FiniteType.of_restrictScalars_finiteType k A B
  letI : FinitePresentation A B := FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨b, hby, hstd⟩ := IsSmoothAt.exists_notMem_isStandardSmooth A q
  let L := Localization.Away b
  let i : B →ₐ[k] L := IsScalarTower.toAlgHom k B L
  let j₀ := (testSpec k).map (CommAlgCat.ofHom i).op
  let j := j₀ ≫ eX.hom
  letI : IsStandardSmooth A L := hstd
  have hs : Smooth (Spec.map (CommRingCat.ofHom (algebraMap A L))) :=
    (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Smooth)).mpr (RingHom.smooth_algebraMap.mpr inferInstance)
  have hmap : j₀ ≫ s = (testSpec k).map
      (CommAlgCat.ofHom (IsScalarTower.toAlgHom k A L)).op := by
    rw [← hf, ← Functor.map_comp, ← op_comp]
    congr 2
  have hsm : Smooth (j.left ≫ f.left) := by
    have hi : IsIso eY.hom.left := (Over.forget _).map_isIso eY.hom
    have he := congrArg Over.Hom.left hmap
    change j₀.left ≫ eX.hom.left ≫ f.left ≫ eY.inv.left =
      Spec.map (CommRingCat.ofHom (algebraMap A L)) at he
    have hh : eY.inv.left ≫ eY.hom.left = 𝟙 _ :=
      ((Over.forget _).mapIso eY).inv_hom_id
    have hEq := congrArg (fun m : _ ⟶ _ => m ≫ eY.hom.left) he
    simp only [Category.assoc, hh, Category.comp_id] at hEq
    rw [show j.left = j₀.left ≫ eX.hom.left from rfl, Category.assoc, hEq]
    infer_instance
  have hj : IsOpenImmersion j.left := by
    have hi : IsIso eX.hom.left := (Over.forget _).map_isIso eX.hom
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫ eX.hom.left)
    infer_instance
  change y b ≠ 0 at hby
  let yL : L →ₐ[k] k := IsLocalization.Away.liftAlgHom b (isUnit_iff_ne_zero.mpr hby)
  refine ⟨_, j, hj, hsm, (testSpec k).map (CommAlgCat.ofHom yL).op, ?_⟩
  have hL : yL.comp i = y := by
    ext a
    exact IsLocalization.Away.lift_eq (S := L) (g := y.toRingHom) b
      (isUnit_iff_ne_zero.mpr hby) a
  change (testSpec k).map (CommAlgCat.ofHom yL).op ≫
    (testSpec k).map (CommAlgCat.ofHom i).op ≫ eX.hom = x
  rw [← Functor.map_comp_assoc, ← op_comp]
  change affinePointEquiv eX _ (yL.comp i) = x
  rw [hL, hy]

end

end SchemeSubmersion

section LaurentDensity

open scoped BigOperators

noncomputable section

variable {k K X J : Type*} [Field k] [Field K] [Algebra k K] [Infinite k]
variable [AddCommGroup X] [Module ℤ X] [Fintype J]

/-- Evaluation of a lattice monomial at units indexed by a basis of the lattice. -/
private def latticeCharacter (e : X ≃ₗ[ℤ] (J → ℤ)) (t : J → Kˣ) :
    Multiplicative X →* Kˣ where
  toFun m := ∏ i, t i ^ e m.toAdd i
  map_one' := by
    change (∏ i, t i ^ e 0 i) = 1
    simp
  map_mul' a b := by
    change (∏ i, t i ^ e (a.toAdd + b.toAdd) i) = _
    simp only [map_add, Pi.add_apply, _root_.zpow_add, Finset.prod_mul_distrib]

private def latticeEvaluation (e : X ≃ₗ[ℤ] (J → ℤ)) (t : J → Kˣ) :
    MonoidAlgebra K (Multiplicative X) →ₐ[K] K :=
  MonoidAlgebra.lift K K (Multiplicative X) ((Units.coeHom K).comp (latticeCharacter e t))

/-- A nonzero Laurent polynomial with extension-field coefficients is
nonzero at a tuple of units of the infinite ground field. -/
theorem laurent_nonzero_at_ground_parameters (e : X ≃ₗ[ℤ] (J → ℤ))
    (c : MonoidAlgebra K (Multiplicative X)) (hc : c ≠ 0) :
    ∃ t : J → kˣ, latticeEvaluation e (Units.map (algebraMap k K).toMonoidHom ∘ t) c ≠ 0 := by
  classical
  let s := c.coeff.support
  let shift (j : J) : ℤ := ∑ m ∈ s, |e m.toAdd j|
  have hshift (j : J) : 0 ≤ shift j := Finset.sum_nonneg fun m _ => abs_nonneg _
  have hs (m : Multiplicative X) (hm : m ∈ s) (j : J) :
      0 ≤ e m.toAdd j + shift j := by
    have hb : |e m.toAdd j| ≤ shift j := by
      dsimp only [shift]
      exact Finset.single_le_sum (f := fun a : Multiplicative X => |e a.toAdd j|)
        (fun a _ => abs_nonneg _) hm
    have hl := neg_le_abs (e m.toAdd j)
    omega
  let μ (m : Multiplicative X) : J →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm fun j => (e m.toAdd j + shift j).toNat
  have hμ (m n : Multiplicative X) (hm : m ∈ s) (hn : n ∈ s) (h : μ m = μ n) : m = n := by
    apply Multiplicative.toAdd.injective
    apply e.injective
    funext j
    have h' := congrArg (fun a : J →₀ ℕ => (a j : ℤ)) h
    change ((e m.toAdd j + shift j).toNat : ℤ) = ((e n.toAdd j + shift j).toNat : ℤ) at h'
    rw [Int.toNat_of_nonneg (hs m hm j), Int.toNat_of_nonneg (hs n hn j)] at h'
    exact add_right_cancel h'
  let p : MvPolynomial J K := ∑ m ∈ s, MvPolynomial.monomial (μ m) (c.coeff m)
  obtain ⟨m, hm⟩ := Finsupp.support_nonempty_iff.mpr (show c.coeff ≠ 0 from
    fun h => hc (MonoidAlgebra.ext (by simpa using h)))
  have hp : p ≠ 0 := by
    intro h
    have hd : p.coeff (μ m) = c.coeff m := by
      dsimp only [p]
      rw [MvPolynomial.coeff_sum, Finset.sum_eq_single m, MvPolynomial.coeff_monomial, ite_eq_left rfl]
      · intro n hn hnm
        rw [MvPolynomial.coeff_monomial, if_neg (fun hmn => hnm (hμ n m hn hm hmn))]
      · exact fun h => (h hm).elim
    rw [h, AddMonoidAlgebra.coeff_zero] at hd
    exact (Finsupp.mem_support_iff.mp hm) hd.symm
  obtain ⟨x, hx, hpx⟩ := polynomial_nonzero_at_ground_parameters (k := k) p hp
  let t : J → kˣ := fun j => Units.mk0 (x j) (hx j)
  let u : J → Kˣ := Units.map (algebraMap k K).toMonoidHom ∘ t
  refine ⟨t, ?_⟩
  let z : Kˣ := ∏ j, u j ^ shift j
  have he (n : Multiplicative X) (hn : n ∈ s) :
      (∏ j, (algebraMap k K (x j)) ^ (μ n j)) =
        (z : K) * (latticeCharacter e u n : K) := by
    have hj (j : J) : (algebraMap k K (x j)) ^ (μ n j) =
        (↑(u j ^ (e n.toAdd j + shift j)) : K) := by
      change (u j : K) ^ (e n.toAdd j + shift j).toNat = _
      rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, Int.toNat_of_nonneg (hs n hn j)]
    simp_rw [hj, _root_.zpow_add, Units.val_mul, Finset.prod_mul_distrib]
    have hz : (z : K) = ∏ j, (u j ^ shift j : Kˣ).val :=
      map_prod (Units.coeHom K) _ _
    have ht : (latticeCharacter e u n : K) =
        ∏ j, (u j ^ e n.toAdd j : Kˣ).val :=
      map_prod (Units.coeHom K) _ _
    rw [hz, ht, mul_comm]
  have hup : MvPolynomial.eval (algebraMap k K ∘ x) p =
      (z : K) * latticeEvaluation e u c := by
    dsimp only [p]
    rw [map_sum, latticeEvaluation, MonoidAlgebra.lift_apply']
    change (∑ m ∈ s, MvPolynomial.eval (algebraMap k K ∘ x)
      (MvPolynomial.monomial (μ m) (c.coeff m))) =
      (z : K) * ∑ m ∈ s, c.coeff m * (latticeCharacter e u m : K)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun j => pow_zero _)]
    simp only [Function.comp_apply]
    rw [he m hm]
    ring
  exact fun h => hpx (by rw [hup, h, mul_zero])

/-- Affine parameters and invertible lattice parameters can be specialized
together to the ground field while keeping a nonzero coefficient function. -/
theorem polynomial_laurent_nonzero_at_ground_parameters {I : Type*}
    (e : X ≃ₗ[ℤ] (J → ℤ)) (p : MvPolynomial I (MonoidAlgebra K (Multiplicative X))) (hp : p ≠ 0) :
    ∃ (t : J → kˣ) (x : I → k),
      MvPolynomial.eval (algebraMap k K ∘ x)
        (MvPolynomial.map (latticeEvaluation e (Units.map (algebraMap k K).toMonoidHom ∘ t)).toRingHom p) ≠ 0 := by
  have he : ∃ m, p.coeff m ≠ 0 := by
    by_contra! hn
    apply hp
    apply MvPolynomial.ext
    intro m
    simpa using hn m
  obtain ⟨m, hm⟩ := he
  obtain ⟨t, ht⟩ := laurent_nonzero_at_ground_parameters (k := k) e (p.coeff m) hm
  let q := MvPolynomial.map (latticeEvaluation e (Units.map (algebraMap k K).toMonoidHom ∘ t)).toRingHom p
  have hq : q ≠ 0 := by
    intro h
    apply ht
    have H := congrArg (fun r : MvPolynomial I K => r.coeff m) h
    dsimp only [q] at H
    rwa [MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero] at H
  obtain ⟨x, _, hx⟩ := polynomial_nonzero_at_ground_parameters (k := k) q hq
  exact ⟨t, x, hx⟩

end

end LaurentDensity

section IntersectionRanks

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LinearAlgebraicGroups.Specs LinearAlgebraicGroups.CocharacterDynamics
open Albert.TrialitySpecification (Model mapModel)
open Albert.ReductiveFiberSpecification (SplitAction)
open private lieMap_closed_injective from LinearAlgebraicGroups.Affine.LieLeftExact

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k : Type} [Field k]

private abbrev subgroupAlgebraicGroup {G : AffineAlgebraicGroup k} (S : ClosedSubgroup G.val) :=
  affineAlgebraicSubgroup S G.property.1 G.property.2.1 G.property.2.2

/-- The range of the differential of a subgroup acting in Albert coordinates. -/
private def representedLieImage (G : AffineAlgebraicGroup k) (A : SplitAction G.val)
    (S : ClosedSubgroup G.val) : Submodule k (Module.End k (Model k)) := by
  letI : IsAffine G.val.X.left := G.property.1
  letI : IsAffine S.group.X.left := (subgroupAlgebraicGroup S).property.1
  exact ((splitActionDifferential G A).comp (lieMap S.inclusion)).range

private theorem representedLieImage_finrank (G : AffineAlgebraicGroup k) (A : SplitAction G.val)
    (S : ClosedSubgroup G.val) :
    letI : IsAffine S.group.X.left := (subgroupAlgebraicGroup S).property.1
    Module.finrank k (representedLieImage G A S) = Module.finrank k (Lie k S.group) := by
  letI : IsAffine G.val.X.left := G.property.1
  letI : IsAffine S.group.X.left := (subgroupAlgebraicGroup S).property.1
  let f := (splitActionDifferential G A).comp (lieMap S.inclusion)
  have hf : Function.Injective f := (splitActionDifferential_injective G A).comp
    (lieMap_closed_injective S.inclusion S.isClosedImmersion)
  exact (LinearEquiv.ofInjective f hf).finrank_eq.symm

private theorem subgroups_fixing_frame_lie_bound
    (G : AffineAlgebraicGroup k) (A : SplitAction G.val)
    (S : ClosedSubgroup G.val) (L : ClosedSubgroup S.group) (v : Slot → Model k)
    (h : let R := CommAlgCat.of k (DualNumber k)
      ∀ (x : Points L.group.X R) (i : Slot),
        A.action R (x ≫ L.inclusion.hom.hom ≫ S.inclusion.hom.hom)
            (mapModel (algebraMap k R) (v i)) = mapModel (algebraMap k R) (v i)) :
    letI : IsAffine L.group.X.left :=
      (subgroupAlgebraicGroup (G := subgroupAlgebraicGroup S) L).property.1
    Module.finrank k (Lie k L.group) ≤
      Module.finrank k ((frameTangentEvaluation k v).domRestrict (representedLieImage G A S)).ker := by
  letI : IsAffine G.val.X.left := G.property.1
  letI : IsAffine S.group.X.left := (subgroupAlgebraicGroup S).property.1
  letI : IsAffine L.group.X.left :=
    (subgroupAlgebraicGroup (G := subgroupAlgebraicGroup S) L).property.1
  let B := representedLieImage G A S
  let f : Lie k S.group →ₗ[k] Module.End k (Model k) :=
    (splitActionDifferential G A).comp (lieMap S.inclusion)
  let g : Lie k L.group →ₗ[k] Lie k S.group := lieMap L.inclusion
  let Eval := (frameTangentEvaluation k v).domRestrict B
  have he (x : Lie k L.group) : (f.rangeRestrict (g x) : B) ∈ Eval.ker := by
    change frameTangentEvaluation k v ((splitActionDifferential G A)
      (mapPointKernel S.inclusion (mapPointKernel L.inclusion x))) = 0
    apply (mem_ker_frameTangentEvaluation k v _).mpr
    intro i
    apply splitActionDifferential_frame_fixed G A
    let R := CommAlgCat.of k (DualNumber k)
    change A.action R ((x.toMul.val ≫ L.inclusion.hom.hom) ≫ S.inclusion.hom.hom)
      (mapModel (algebraMap k R) (v i)) = mapModel (algebraMap k R) (v i)
    rw [Category.assoc]
    exact h x.toMul.val i
  let j : Lie k L.group →ₗ[k] Eval.ker :=
    (f.rangeRestrict.comp g).codRestrict Eval.ker he
  have hj : Function.Injective j := by
    intro p q h
    apply lieMap_closed_injective L.inclusion L.isClosedImmersion
    apply lieMap_closed_injective S.inclusion S.isClosedImmersion
    apply splitActionDifferential_injective G A
    exact congrArg (fun x : Eval.ker => x.val.val) h
  letI : Module.Finite k (Module.End k (Model k)) :=
    Module.Finite.of_injective (matrixToOperator k).symm.toLinearMap (matrixToOperator k).symm.injective
  exact LinearMap.finrank_le_finrank_of_injective hj

/-- For a frame satisfying the minors, closed subgroups in the parabolic and
contracting intersection have Lie dimension at most five and three, respectively. -/
theorem frameIntersection_lieRank_le
    (G : AffineAlgebraicGroup k) (A : SplitAction G.val)
    (D : LimitDecomposition (chamberCocharacter A)) (v : Slot → Model k)
    (hv : frameRankPolynomial (modelCoordinateEquiv k ∘ v) ≠ 0)
    (hP : letI : IsAffine D.parabolic.group.X.left :=
      (subgroupAlgebraicGroup D.parabolic).property.1
      Module.finrank k (Lie k D.parabolic.group) ≤ 28)
    (hU : letI : IsAffine D.contracting.group.X.left :=
      (subgroupAlgebraicGroup D.contracting).property.1
      Module.finrank k (Lie k D.contracting.group) ≤ 24) :
    ∀ (P : ClosedSubgroup D.parabolic.group) (U : ClosedSubgroup D.contracting.group),
      (let R := CommAlgCat.of k (DualNumber k)
        ∀ (x : Points P.group.X R) (i : Slot),
          A.action R (x ≫ P.inclusion.hom.hom ≫ D.parabolic.inclusion.hom.hom)
              (mapModel (algebraMap k R) (v i)) = mapModel (algebraMap k R) (v i)) →
      (let R := CommAlgCat.of k (DualNumber k)
        ∀ (x : Points U.group.X R) (i : Slot),
          A.action R (x ≫ U.inclusion.hom.hom ≫ D.contracting.inclusion.hom.hom)
              (mapModel (algebraMap k R) (v i)) = mapModel (algebraMap k R) (v i)) →
      letI : IsAffine P.group.X.left :=
        (subgroupAlgebraicGroup (G := subgroupAlgebraicGroup D.parabolic) P).property.1
      letI : IsAffine U.group.X.left :=
        (subgroupAlgebraicGroup (G := subgroupAlgebraicGroup D.contracting) U).property.1
      Module.finrank k (Lie k P.group) ≤ 5 ∧ Module.finrank k (Lie k U.group) ≤ 3 := by
  letI : IsAffine G.val.X.left := G.property.1
  letI : IsAffine D.parabolic.group.X.left := (subgroupAlgebraicGroup D.parabolic).property.1
  letI : IsAffine D.contracting.group.X.left := (subgroupAlgebraicGroup D.contracting).property.1
  have hmem (S : ClosedSubgroup G.val) (j : Fin 28) (h : chamberTangent A j ∈ lieImage S) :
      tangentOperator k j ∈ representedLieImage G A S := by
    letI : IsAffine S.group.X.left := (subgroupAlgebraicGroup S).property.1
    obtain ⟨x, hx⟩ := h
    refine ⟨x, ?_⟩
    change splitActionDifferential G A (mapPointKernel S.inclusion x) = tangentOperator k j
    rw [hx, splitActionDifferential_chamberTangent]
  obtain ⟨hkerU, hkerP⟩ := evaluationKernelBounds v hv
    (representedLieImage G A D.contracting) (representedLieImage G A D.parabolic)
    ((representedLieImage_finrank G A D.contracting).le.trans hU)
    ((representedLieImage_finrank G A D.parabolic).le.trans hP)
    (fun j => hmem _ _ (chamberTangent_mem_contracting A D j))
    (fun j => hmem _ _ (chamberTangent_mem_parabolic A D j))
  intro P U hp hu
  exact ⟨(subgroups_fixing_frame_lie_bound G A D.parabolic P v hp).trans hkerP,
    (subgroups_fixing_frame_lie_bound G A D.contracting U v hu).trans hkerU⟩

end

end IntersectionRanks

section RationalFrame

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open LinearAlgebraicGroups.Specs
open Algebra.TensorProduct
open scoped TensorProduct CategoryTheory.MonObj
open Pinning (BasedRootDatum)
open Albert.IntegralSmoothnessSpecification (SplitGroup geometricFiber algebraicFiber)
open Albert.IntegralSmoothness (geometricFiberAction)
open Albert.ShortDirectionSpecification (IntegralPresentation)
open Albert.AutomorphismTypeSpecification (IntegralSplitIdentification)
open Albert.ReductiveFiberSpecification (SplitAction)
open Albert.TrialitySpecification (Model mapModel)
open Albert.FrameSpecification (frameAxis)
open private affineSpectrum specFF affinePointEquiv from
  LinearAlgebraicGroups.Reductive.CocharacterSmoothAndUnipotent
open private geometry_of_smooth_geometricallyIrreducible geometricallyIrreducible_of_connected from
  LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private conjugate conjugate_inclusion conjugation_apply from
  LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private mapModel_comp mapModel_id from LinearAlgebraicGroups.Albert.ShortDirections

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 900000

variable {k K : Type} [Field k] [Field K] [Algebra k K]

private def algebraMorphism {A B : TestAlgebra k} (f : A →+* B)
    (h : ∀ x, f (algebraMap k A x) = algebraMap k B x) : A ⟶ B :=
  CommAlgCat.ofHom { toRingHom := f, commutes' := h }

private def underlyingRingMorphism {A B : TestAlgebra k} (f : A ⟶ B) : A →+* B :=
  f.hom.toRingHom

private theorem underlyingRingMorphism_commutes {A B : TestAlgebra k} (f : A ⟶ B)
    (x : k) : underlyingRingMorphism f (algebraMap k A x) = algebraMap k B x :=
  f.hom.commutes x

private theorem algebraMorphism_ext {A B : TestAlgebra k} {f g : A ⟶ B}
    (h : ∀ x : A, underlyingRingMorphism f x = underlyingRingMorphism g x) : f = g :=
  CommAlgCat.hom_ext (AlgHom.ext h)

private def scalarPointHom (k K : Type) [Field k] [Field K] [Algebra k K] :
    CommAlgCat.of k k ⟶ (restrictTestAlgebra k K).obj (CommAlgCat.of K K) :=
  algebraMorphism (algebraMap k K)
    (fun x => (Algebra.algebraMap_self_apply (algebraMap k K x)).symm)

private theorem injective_of_openCell {A B : TestAlgebra k}
    [IsDomain A] [Nontrivial B] (f : A →ₐ[k] B)
    (hf : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))) :
    Function.Injective f := by
  letI := hf
  have h : DenseRange (PrimeSpectrum.comap f.toRingHom) := by
    apply IsOpen.dense
    · exact IsOpenImmersion.isOpen_range (Spec.map (CommRingCat.ofHom f.toRingHom))
    · exact Set.range_nonempty _
  have hk := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f.toRingHom).mp h
  rw [nilradical_eq_zero] at hk
  exact (RingHom.injective_iff_ker_eq_bot _).mpr (le_bot_iff.mp hk)

private theorem chevalleyCellCoordinates_includeRight (D : BasedRootDatum.{0})
    (p : chevalleyCellCoordinates D k) :
    chevalleyCellCoordinates_baseChange D k K (1 ⊗ₜ[k] p) =
      MvPolynomial.map (MonoidAlgebra.mapAlgHom (Multiplicative D.X) (Algebra.ofId k K)).toRingHom p := by
  ext dg m
  simp only [chevalleyCellCoordinates_baseChange, AlgEquiv.trans_apply,
    MvPolynomial.mapAlgEquiv_apply, MvPolynomial.coeff_map, MvPolynomial.coeff_rTensorAlgEquiv_tmul,
    MvPolynomial.coeff_map]
  change (MonoidAlgebra.scalarTensorEquiv k K (1 ⊗ₜ[k] p.coeff dg)).coeff m = _
  simp

private def cellEvaluation {D : BasedRootDatum.{0}} {I : Type} [Fintype I]
    (e : D.X ≃ₗ[ℤ] (I → ℤ)) (t : I → kˣ) (x : D.I → k) :
    chevalleyCellCoordinates D k →ₐ[k] k :=
  MvPolynomial.aevalTower (latticeEvaluation e t) x

private theorem cellEvaluation_map {D : BasedRootDatum.{0}} {I : Type} [Fintype I]
    (e : D.X ≃ₗ[ℤ] (I → ℤ)) (t : I → kˣ) (x : D.I → k)
    (p : chevalleyCellCoordinates D k) :
    cellEvaluation e (Units.map (algebraMap k K).toMonoidHom ∘ t) (algebraMap k K ∘ x)
      (chevalleyCellCoordinates_baseChange D k K (1 ⊗ₜ[k] p)) =
        algebraMap k K (cellEvaluation e t x p) := by
  rw [chevalleyCellCoordinates_includeRight]
  let u := (latticeEvaluation e (Units.map (algebraMap k K).toMonoidHom ∘ t)).restrictScalars k
  have he : u.comp (MonoidAlgebra.mapAlgHom _ (Algebra.ofId k K)) =
      (Algebra.ofId k K).comp (latticeEvaluation e t) := by
    apply MonoidAlgebra.algHom_ext
    · intro m
      simp [u, latticeEvaluation, latticeCharacter, map_prod, map_zpow]
    · exact Subsingleton.elim _ _
  change MvPolynomial.eval₂ u.toRingHom (algebraMap k K ∘ x)
    (MvPolynomial.map (MonoidAlgebra.mapAlgHom _ (Algebra.ofId k K)).toRingHom p) =
      algebraMap k K (MvPolynomial.eval₂ (latticeEvaluation e t).toRingHom x p)
  rw [MvPolynomial.eval₂_map, MvPolynomial.eval₂_comp_left]
  exact congrArg (fun f : MonoidAlgebra k (Multiplicative D.X) →ₐ[k] K =>
    MvPolynomial.eval₂ f.toRingHom (algebraMap k K ∘ x) p) he

/-- A regular function on the scalar extension of an affine scheme with a
split Chevalley cell is nonzero at a point defined over the ground field. -/
private theorem rationalPoint_on_cell [Infinite k] {D : BasedRootDatum.{0}}
    {X : SchemeOver k} [IsAffine X.left] [IsIntegral X.left]
    (c : affineSpectrum (CommAlgCat.of k (chevalleyCellCoordinates D k)) ⟶ X)
    (hc : IsOpenImmersion c.left)
    (f : ∀ R : TestAlgebra K, Points X ((restrictTestAlgebra k K).obj R) → R)
    (hf : ∀ {R S : TestAlgebra K} (m : R ⟶ S) p,
      m.hom (f R p) = f S (mapPoints ((restrictTestAlgebra k K).map m) p))
    (hne : ∃ p, f (CommAlgCat.of K K) p ≠ 0) :
    ∃ p : Points X (CommAlgCat.of k k),
      f (CommAlgCat.of K K) (mapPoints (scalarPointHom k K) p) ≠ 0 := by
  let B := CommAlgCat.of k (chevalleyCellCoordinates D k)
  obtain ⟨A', ⟨a₀⟩⟩ := essImage_algSpec.mpr (inferInstance : IsAffine X.left)
  let A := A'.unop
  let a : affineSpectrum A ≅ X := a₀
  let g : A →ₐ[k] B := (affinePointEquiv a B).symm c
  have hga : affinePointEquiv a B g = c := (affinePointEquiv a B).apply_symm_apply c
  let a' : Spec (CommRingCat.of A) ≅ X.left := (Over.forget _).mapIso a
  letI : IsIntegral (Spec (CommRingCat.of A)) := IsIntegral.of_isIso a'.inv
  letI : IsDomain A := (affine_isIntegral_iff (CommRingCat.of A)).mp inferInstance
  have hg : Function.Injective g := by
    apply injective_of_openCell
    haveI : IsIso a.inv.left := (Over.forget _).map_isIso a.inv
    haveI := hc
    have hh := congrArg (fun z : Points X B => (z ≫ a.inv).left) hga
    change ((testSpec k).map (CommAlgCat.ofHom g).op ≫ a.hom ≫ a.inv).left = _ at hh
    have hmap : Spec.map (CommRingCat.ofHom g.toRingHom) = (c ≫ a.inv).left := by
      simp only [Iso.hom_inv_id, Category.comp_id] at hh
      exact hh
    rw [hmap]
    exact inferInstanceAs (IsOpenImmersion (c.left ≫ a.inv.left))
  let A_K := CommAlgCat.of K (K ⊗[k] A)
  let i : A ⟶ (restrictTestAlgebra k K).obj A_K :=
    algebraMorphism (includeRight : A →ₐ[k] K ⊗[k] A).toRingHom
      (fun x => (includeRight : A →ₐ[k] K ⊗[k] A).commutes x |>.trans
        (IsScalarTower.algebraMap_apply k K (K ⊗[k] A) x))
  let z := f A_K (mapPoints i a.hom)
  have hz : z ≠ 0 := by
    obtain ⟨p, hp⟩ := hne
    let s : A ⟶ (restrictTestAlgebra k K).obj (CommAlgCat.of K K) :=
      ((specFF k).preimage (p ≫ a.inv)).unop
    let s₀ : A →ₐ[k] K :=
      { toRingHom := underlyingRingMorphism s
        commutes' := fun x => (underlyingRingMorphism_commutes s x).trans
          (Algebra.algebraMap_self_apply (algebraMap k K x)) }
    let m : A_K ⟶ CommAlgCat.of K K := CommAlgCat.ofHom (AlgHom.liftEquiv k K A K s₀)
    have hm : i ≫ (restrictTestAlgebra k K).map m = s := by
      apply algebraMorphism_ext
      intro v
      change AlgHom.liftEquiv k K A K s₀ (1 ⊗ₜ[k] v) = s₀ v
      simp
    intro hzero
    apply hp
    have h := hf m (mapPoints i a.hom)
    change m.hom z = _ at h
    have hpt : mapPoints ((restrictTestAlgebra k K).map m) (mapPoints i a.hom) = p := by
      change (testSpec k).map ((restrictTestAlgebra k K).map m).op ≫
        (testSpec k).map i.op ≫ a.hom = p
      rw [← Functor.map_comp_assoc, ← op_comp, hm]
      change (testSpec k).map ((specFF k).preimage (p ≫ a.inv)) ≫ a.hom = _
      rw [(specFF k).map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    simpa only [hpt, hzero, map_zero] using h.symm
  let g_K : K ⊗[k] A →ₐ[K] K ⊗[k] B := Algebra.TensorProduct.map (AlgHom.id K K) g
  have hg_K : Function.Injective g_K :=
    Module.Flat.lTensor_preserves_injective_linearMap g.toLinearMap hg
  let e := chevalleyCellCoordinates_baseChange D k K
  let z' := e (g_K z)
  have hz' : z' ≠ 0 := fun h => hz (hg_K (e.injective (h.trans (by simp))))
  letI := D.freeX
  letI := D.finiteX
  let I := Module.Free.ChooseBasisIndex ℤ D.X
  letI : Fintype I := Fintype.ofFinite I
  let basis : D.X ≃ₗ[ℤ] (I → ℤ) :=
    (Module.Free.chooseBasis ℤ D.X).equivFun
  obtain ⟨t, x, hx⟩ := polynomial_laurent_nonzero_at_ground_parameters (k := k) basis z' hz'
  let b := cellEvaluation basis t x
  let b' := cellEvaluation basis (Units.map (algebraMap k K).toMonoidHom ∘ t)
    (algebraMap k K ∘ x)
  let m : A_K ⟶ CommAlgCat.of K K := CommAlgCat.ofHom
    (b'.comp (e.toAlgHom.comp g_K))
  let u : A ⟶ CommAlgCat.of k k := CommAlgCat.ofHom (b.comp g)
  refine ⟨mapPoints u a.hom, ?_⟩
  have hm : i ≫ (restrictTestAlgebra k K).map m = u ≫ scalarPointHom k K := by
    apply algebraMorphism_ext
    intro v
    change b' (e (g_K (1 ⊗ₜ[k] v))) = algebraMap k K (b (g v))
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    exact cellEvaluation_map basis t x (g v)
  have he := hf m (mapPoints i a.hom)
  have hh : mapPoints ((restrictTestAlgebra k K).map m) (mapPoints i a.hom) =
      mapPoints (scalarPointHom k K) (mapPoints u a.hom) := by
    simpa only [op_comp, Functor.map_comp, Category.assoc] using
      congrArg (fun q : A ⟶ (restrictTestAlgebra k K).obj (CommAlgCat.of K K) =>
        (testSpec k).map q.op ≫ a.hom) hm
  rw [← hh, ← he]
  change b' z' ≠ 0
  rw [MvPolynomial.eval_map] at hx
  exact hx

private def rationalSpecUnitIso (k : Type) [Field k] :
    (testSpec k).obj (op (CommAlgCat.of k k)) ≅ 𝟙_ (SchemeOver k) := by
  refine Over.isoMk (Iso.refl (Spec (CommRingCat.of k))) ?_
  change (𝟙 _) ≫ (𝟙 _) = Spec.map (CommRingCat.ofHom (algebraMap k k))
  have h : CommRingCat.ofHom (algebraMap k k) = 𝟙 (CommRingCat.of k) :=
    CommRingCat.hom_ext (RingHom.ext (Algebra.algebraMap_self_apply (R := k)))
  rw [h, Spec.map_id, Category.id_comp]

private def rationalSection {X : SchemeOver k} (p : Points X (CommAlgCat.of k k)) :
    𝟙_ (SchemeOver k) ⟶ X :=
  (rationalSpecUnitIso k).inv ≫ p

private theorem rationalSection_apply {X : SchemeOver k} (p : Points X (CommAlgCat.of k k))
    (R : TestAlgebra k) (f : CommAlgCat.of k k ⟶ R) :
    toUnit ((testSpec k).obj (op R)) ≫ rationalSection p = mapPoints f p := by
  let e := rationalSpecUnitIso k
  have h : (testSpec k).map f.op ≫ e.hom = toUnit _ :=
    (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _
  change toUnit _ ≫ e.inv ≫ p = (testSpec k).map f.op ≫ p
  rw [← h, Category.assoc, e.hom_inv_id_assoc]

private def translatedCoordinates {G : GroupScheme k} (A : SplitAction G)
    (v : Slot → Model K) (R : TestAlgebra K) (p : Points G.X ((restrictTestAlgebra k K).obj R)) :
    Slot → Fin 27 → R :=
  fun i => modelCoordinateEquiv R
    (A.action ((restrictTestAlgebra k K).obj R) p (mapModel (algebraMap K R) (v i)))

private theorem translatedCoordinates_natural {G : GroupScheme k} (A : SplitAction G)
    (v : Slot → Model K) {R S : TestAlgebra K} (f : R ⟶ S)
    (p : Points G.X ((restrictTestAlgebra k K).obj R)) :
    (fun i j => f.hom (translatedCoordinates A v R p i j)) =
      translatedCoordinates A v S (mapPoints ((restrictTestAlgebra k K).map f) p) := by
  funext i j
  have h := A.natural ((restrictTestAlgebra k K).map f) p (mapModel (algebraMap K R) (v i))
  change mapModel f.hom.toRingHom _ = _ at h
  have he : f.hom.toRingHom.comp (algebraMap K R) = algebraMap K S := f.hom.comp_algebraMap
  have hh : mapModel ((restrictTestAlgebra k K).map f).hom.toRingHom
      (mapModel (algebraMap K R) (v i)) = mapModel (algebraMap K S) (v i) := by
    change mapModel f.hom.toRingHom (mapModel (algebraMap K R) (v i)) = _
    rw [mapModel_comp, he]
  rw [hh] at h
  exact (congrFun (modelCoordinateEquiv_natural f.hom.toRingHom _) j).symm.trans
    (congrArg (fun z => modelCoordinateEquiv S z j) h)

private theorem mapModel_self (x : Model K) : mapModel (algebraMap K K) x = x := by
  rw [show algebraMap K K = RingHom.id K from RingHom.ext
    (Algebra.algebraMap_self_apply (R := K))]
  exact mapModel_id x

private theorem translatedCoordinates_self {G : GroupScheme k} (A : SplitAction G)
    (v : Slot → Model K) (p : Points ((groupBaseChange k K).obj G).X (CommAlgCat.of K K)) :
    translatedCoordinates A v (CommAlgCat.of K K) (baseChangePoint k K G.X _ p) =
      fun i => modelCoordinateEquiv K ((extendSplitAction A).action _ p (v i)) := by
  funext i j
  change modelCoordinateEquiv K (A.action _ (baseChangePoint k K G.X _ p)
    (mapModel (algebraMap K K) (v i))) j = _
  rw [mapModel_self]
  rfl

private theorem exists_rational_translated_frame [Infinite k]
    (S : IntegralSplitIdentification) {P : IntegralPresentation} (G : SplitGroup P)
    (p : Points ((groupBaseChange k K).obj (geometricFiber G k)).X (CommAlgCat.of K K)) :
    let A := extendSplitAction (K := K) (geometricFiberAction G k)
    ∃ g : Points (geometricFiber G k).X (CommAlgCat.of k k),
      let gK := (baseChangePointGroupEquiv K (geometricFiber G k) (CommAlgCat.of K K)).symm
        (mapPoints (scalarPointHom k K) g)
      let v := modelCoordinateEquiv K ∘ orbitFrame A (gK * p)
      frameRankPolynomial v ≠ 0 ∧ transverseCoefficient v ≠ 0 := by
  let G₀ := algebraicFiber G k
  let a : SplitAction G₀.val := geometricFiberAction G k
  let A := extendSplitAction (K := K) a
  change Points ((groupBaseChange k K).obj G₀.val).X (CommAlgCat.of K K) at p
  letI : IsAffine G₀.val.X.left := G₀.property.1
  letI : SmoothOfRelativeDimension 52 G₀.val.X.hom := splitFibre_smoothDimension S G
  letI : Smooth G₀.val.X.hom := SmoothOfRelativeDimension.smooth 52 _
  letI : GeometricallyConnected G₀.val.X.hom := splitFibre_geometricallyConnected S G
  letI : ConnectedSpace G₀.val.X.left := GeometricallyConnected.connectedSpace_of_subsingleton G₀.val.X.hom
  letI : GeometricallyIrreducible G₀.val.X.hom := geometricallyIrreducible_of_connected G₀
  letI : IsIntegral G₀.val.X.left := (geometry_of_smooth_geometricallyIrreducible G₀.val.X).2.2
  obtain ⟨e⟩ := splitFibre_chevalleyIso (k := k) S G
  obtain ⟨c, hc⟩ := chevalleyFibre_openChart S.chevalley k
  let j := (Grp.forget (SchemeOver k)).mapIso e
  let c' : affineSpectrum (CommAlgCat.of k (chevalleyCellCoordinates S.datum k)) ⟶ G₀.val.X := c ≫ j.inv
  haveI : IsIso j.inv.left := (Over.forget _).map_isIso j.inv
  haveI := hc
  have hc' : IsOpenImmersion c'.left := inferInstanceAs (IsOpenImmersion (c.left ≫ j.inv.left))
  let v := orbitFrame A p
  let f (R : TestAlgebra K) (x : Points G₀.val.X ((restrictTestAlgebra k K).obj R)) : R :=
    let w := translatedCoordinates a v R x
    frameRankPolynomial w * transverseCoefficient w
  have hf : ∀ {R T : TestAlgebra K} (b : R ⟶ T) (x : Points G₀.val.X ((restrictTestAlgebra k K).obj R)),
      b.hom (f R x) = f T (mapPoints ((restrictTestAlgebra k K).map b) x) := by
    intro R T b x
    let w := translatedCoordinates a v R x
    let w' := translatedCoordinates a v T (mapPoints ((restrictTestAlgebra k K).map b) x)
    have hw : (fun i j => b.hom (w i j)) = w' := translatedCoordinates_natural a v b x
    have hRank := (frameRankPolynomial_map b.hom.toRingHom w).symm.trans
      (congrArg frameRankPolynomial hw)
    have hTrans := (transverseCoefficient_map b.hom.toRingHom w).symm.trans
      (congrArg transverseCoefficient hw)
    change b.hom (frameRankPolynomial w * transverseCoefficient w) =
      frameRankPolynomial w' * transverseCoefficient w'
    exact (map_mul b.hom _ _).trans (congrArg₂ (· * ·) hRank hTrans)
  let L := CommAlgCat.of K K
  let E := baseChangePointGroupEquiv K G₀.val L
  have hE (q : Points ((groupBaseChange k K).obj G₀.val).X L) :
      f L (E q) = frameRankPolynomial (modelCoordinateEquiv K ∘ orbitFrame A (q * p)) *
        transverseCoefficient (modelCoordinateEquiv K ∘ orbitFrame A (q * p)) := by
    dsimp only [f]
    change frameRankPolynomial (translatedCoordinates a v L (baseChangePoint k K G₀.val.X L q)) *
      transverseCoefficient (translatedCoordinates a v L (baseChangePoint k K G₀.val.X L q)) = _
    rw [translatedCoordinates_self]
    have he : (fun i => modelCoordinateEquiv K (A.action L q (v i))) =
        modelCoordinateEquiv K ∘ orbitFrame A (q * p) := by
      funext i
      change modelCoordinateEquiv K (A.action L q (A.action L p (frameAxis i))) =
        modelCoordinateEquiv K (A.action L (q * p) (frameAxis i))
      rw [map_mul]
      rfl
    rw [he]
  have hn : ∃ x, f L x ≠ 0 := by
    obtain ⟨x, hx, ht⟩ := exists_frame_with_transverse_ranks A
    refine ⟨E (x * p⁻¹), ?_⟩
    rw [hE, inv_mul_cancel_right]
    exact mul_ne_zero hx (ht.trans_ne one_ne_zero)
  obtain ⟨g, hg⟩ := rationalPoint_on_cell c' hc' f hf hn
  let gK := E.symm (mapPoints (scalarPointHom k K) g)
  have hgg : E gK = mapPoints (scalarPointHom k K) g := E.apply_symm_apply _
  rw [← hgg, hE] at hg
  exact ⟨g, (mul_ne_zero_iff.mp hg)⟩

private theorem baseChange_conjugate_fixes_frame
    {G : GroupScheme k} (A : SplitAction G) (H : ClosedSubgroup G)
    (g : Points G.X (CommAlgCat.of k k))
    (p : Points ((groupBaseChange k K).obj G).X (CommAlgCat.of K K))
    (hfix : ∀ (R : TestAlgebra K) (x : Points ((groupBaseChange k K).obj H.group).X R)
      (i : Slot), (extendSplitAction A).action R (x ≫ ((groupBaseChange k K).map H.inclusion).hom.hom)
        (mapModel (algebraMap K R) (orbitFrame (extendSplitAction A) p i)) =
        mapModel (algebraMap K R) (orbitFrame (extendSplitAction A) p i)) :
    let H' := conjugate (rationalSection g) H
    let E := baseChangePointGroupEquiv K G (CommAlgCat.of K K)
    let gK := E.symm (mapPoints (scalarPointHom k K) g)
    let S := extendSplitAction A
    let v := orbitFrame S (gK * p)
    ∀ (R : TestAlgebra K) (x : Points ((groupBaseChange k K).obj H'.group).X R) (i : Slot),
      S.action R (x ≫ ((groupBaseChange k K).map H'.inclusion).hom.hom)
        (mapModel (algebraMap K R) (v i)) = mapModel (algebraMap K R) (v i) := by
  let F := groupBaseChange k K
  let S := extendSplitAction (K := K) A
  let E := baseChangePointGroupEquiv K G (CommAlgCat.of K K)
  let gK := E.symm (mapPoints (scalarPointHom k K) g)
  let H' := conjugate (rationalSection g) H
  dsimp only
  intro R x i
  let m : CommAlgCat.of K K ⟶ R := CommAlgCat.ofHom (Algebra.ofId K R)
  let R₀ := (restrictTestAlgebra k K).obj R
  let r : Points ((groupBaseChange k K).obj G).X R := mapPoints m gK
  let y : Points ((groupBaseChange k K).obj G).X R := x ≫ (F.map H.inclusion).hom.hom
  let B := baseChangePointGroupEquiv K G R
  have hr : toUnit ((testSpec k).obj (op R₀)) ≫ rationalSection g = B r := by
    change _ = baseChangePoint k K G.X R (mapPoints m gK)
    have hn := baseChangePointsNaturality k K G.X m gK
    have hgg : baseChangePoint k K G.X (CommAlgCat.of K K) gK = mapPoints (scalarPointHom k K) g :=
      E.apply_symm_apply _
    rw [hn, hgg, rationalSection_apply g R₀ (scalarPointHom k K ≫ (restrictTestAlgebra k K).map m)]
    change (testSpec k).map ((_ ≫ _).op) ≫ g =
      (testSpec k).map ((restrictTestAlgebra k K).map m).op ≫
        (testSpec k).map (scalarPointHom k K).op ≫ g
    rw [op_comp, Functor.map_comp, Category.assoc]
  have hy : x ≫ (F.map H'.inclusion).hom.hom = r * y * r⁻¹ := by
    let x₀ : Points ((baseChange k K).obj H.group.X) R := x
    let u := baseChangePoint k K H.group.X R x₀
    have hy' : B y = u ≫ H.inclusion.hom.hom :=
      baseChangePointsSchemeNaturality k K H.inclusion.hom.hom R x₀
    have hx' : B (x ≫ (F.map H'.inclusion).hom.hom) = u ≫ H'.inclusion.hom.hom :=
      baseChangePointsSchemeNaturality k K H'.inclusion.hom.hom R x₀
    apply B.injective
    rw [hx', map_mul, map_mul, map_inv, hy', ← hr]
    change u ≫ (conjugate (rationalSection g) H).inclusion.hom.hom = _
    rw [conjugate_inclusion]
    change u ≫ H.inclusion.hom.hom ≫ _ = _
    rw [← Category.assoc, conjugation_apply]
  have hv : mapModel (algebraMap K R) (orbitFrame S (gK * p) i) =
      S.action R r (mapModel (algebraMap K R) (orbitFrame S p i)) := by
    have hw : orbitFrame S (gK * p) i = S.action _ gK (orbitFrame S p i) := by
      change S.action _ (gK * p) (frameAxis i) = _
      rw [map_mul]
      rfl
    rw [hw]
    exact S.natural m gK _
  change S.action R (x ≫ (F.map H'.inclusion).hom.hom)
    (mapModel (algebraMap K R) (orbitFrame S (gK * p) i)) = _
  rw [hy, hv]
  let w := mapModel (algebraMap K R) (orbitFrame S p i)
  have hw : S.action R y w = w := hfix R x i
  change S.action R (r * y * r⁻¹) (S.action R r w) = S.action R r w
  calc
    _ = S.action R ((r * y * r⁻¹) * r) w := by rw [map_mul (S.action R) (r * y * r⁻¹) r]; rfl
    _ = S.action R (r * y) w := by rw [mul_assoc (r * y), inv_mul_cancel, mul_one]
    _ = S.action R r w := by
      rw [map_mul]
      change S.action R r (S.action R y w) = _
      rw [hw]

end

end RationalFrame

section TransverseTangent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory
open LinearAlgebraicGroups.Specs LinearAlgebraicGroups.CocharacterDynamics
open scoped CategoryTheory.MonObj
open Albert.TrialitySpecification (Model mapModel)
open Albert.ReductiveFiberSpecification (SplitAction)
open private lieMap_closed_injective from LinearAlgebraicGroups.Affine.LieLeftExact

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 750000
set_option linter.style.haveILetI false

variable {k : Type} [Field k]

private abbrev Ga (k : Type) [Field k] := StandardGroups.additiveGroup k
private abbrev LieDual (k : Type) [Field k] := CommAlgCat.of k (DualNumber k)
private abbrev Rational (k : Type) [Field k] := CommAlgCat.of k k

private def intersectionOverLeft {G : GroupScheme k} (S H : ClosedSubgroup G) :
    ClosedSubgroup S.group :=
  ⟨pullback S.inclusion H.inclusion, pullback.fst S.inclusion H.inclusion,
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (((Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))).map_isPullback
        (IsPullback.of_hasPullback S.inclusion H.inclusion)).flip) H.isClosedImmersion⟩

private theorem finrank_lieMap_closed_range {G H : GroupScheme k}
    [IsAffine G.X.left] [IsAffine H.X.left]
    (f : G ⟶ H) (hf : IsClosedImmersion f.hom.hom.left) :
    Module.finrank k (lieMap f).range = Module.finrank k (Lie k G) :=
  (LinearEquiv.ofInjective (lieMap f) (lieMap_closed_injective f hf)).finrank_eq.symm

private def additivePoint (R : TestAlgebra k) (t : R) : Points (Ga k).val.X R :=
  ((StandardGroups.additiveGroupPointsIso k).inv.app R).hom (Multiplicative.ofAdd t)

private theorem additivePoint_map {R S : TestAlgebra k} (f : R ⟶ S) (t : R) :
    mapPoints f (additivePoint R t) = additivePoint S (f.hom t) := by
  let e := StandardGroups.additiveGroupPointsIso k
  have h := e.inv.naturality f
  exact (DFunLike.congr_fun (congrArg GrpCat.Hom.hom h) (Multiplicative.ofAdd t)).symm

private theorem additivePoint_zero (R : TestAlgebra k) :
    additivePoint R 0 = 1 :=
  ((StandardGroups.additiveGroupPointsIso k).inv.app R).hom.map_one

private theorem additivePoint_coordinate (R : TestAlgebra k) (t : R) :
    (((StandardGroups.additiveGroupPointsIso k).hom.app R).hom
       (additivePoint R t) : Multiplicative R).toAdd = t := by
  let e := StandardGroups.additiveGroupPointsIso k
  have h := e.inv_hom_id_app R
  exact congrArg Multiplicative.toAdd
    (DFunLike.congr_fun (congrArg GrpCat.Hom.hom h) (Multiplicative.ofAdd t))

private def additiveTangent (c : k) : Lie k (Ga k).val := by
  refine ⟨additivePoint (LieDual k) (TrivSqZeroExt.inr c), ?_⟩
  change mapPoints (dualReduction k) (additivePoint (LieDual k) (TrivSqZeroExt.inr c)) = 1
  rw [additivePoint_map, show (dualReduction k).hom (TrivSqZeroExt.inr c) = 0 from rfl,
    additivePoint_zero]

private def transverseTangent {G : GroupScheme k} [IsAffine G.X.left] (A : SplitAction G) :
    Lie k G :=
  letI : IsAffine (Ga k).val.X.left := (Ga k).property.1
  lieMap (transverseLine A) (additiveTangent 1)

private theorem transverseTangent_point {G : GroupScheme k} [IsAffine G.X.left]
    (A : SplitAction G) :
    (transverseTangent A).toMul.val = transversePoint A (LieDual k) (TrivSqZeroExt.inr 1) := by
  change (additiveTangent 1).toMul.val ≫ (transverseLine A).hom.hom = _
  rw [transverseLine_apply]
  exact congrArg (transversePoint A (LieDual k)) (additivePoint_coordinate (LieDual k) _)

private theorem transverseTangent_not_mem_sum
    (G : AffineAlgebraicGroup k) (A : SplitAction G.val)
    (D : LimitDecomposition (chamberCocharacter A)) (H : ClosedSubgroup G.val)
    (v : Slot → Model k) (hv : transverseCoefficient (modelCoordinateEquiv k ∘ v) ≠ 0)
    (hfix : ∀ (R : TestAlgebra k) (h : Points H.group.X R) (i : Slot),
      A.action R (h ≫ H.inclusion.hom.hom) (mapModel (algebraMap k R) (v i)) =
        mapModel (algebraMap k R) (v i)) :
    letI : IsAffine G.val.X.left := G.property.1
    letI : IsAffine D.parabolic.group.X.left := (subgroupAlgebraicGroup D.parabolic).property.1
    letI : IsAffine H.group.X.left := (subgroupAlgebraicGroup H).property.1
    transverseTangent A ∉ (lieMap D.parabolic.inclusion).range ⊔ (lieMap H.inclusion).range := by
  letI : IsAffine G.val.X.left := G.property.1
  letI : IsAffine D.parabolic.group.X.left := (subgroupAlgebraicGroup D.parabolic).property.1
  letI : IsAffine H.group.X.left := (subgroupAlgebraicGroup H).property.1
  intro ht
  obtain ⟨_, ⟨b, rfl⟩, _, ⟨h, rfl⟩, hb⟩ := Submodule.mem_sup.mp ht
  have he := congrArg (fun z : Lie k G.val => z.toMul.val) hb
  rw [transverseTangent_point] at he
  let R := LieDual k
  change (b.toMul.val ≫ D.parabolic.inclusion.hom.hom) *
    (h.toMul.val ≫ H.inclusion.hom.hom) = transversePoint A R (TrivSqZeroExt.inr 1) at he
  have hw : IsUnit (transverseCoefficient (modelCoordinateEquiv R ∘
      (fun i => mapModel (algebraMap k R) (v i)))) := by
    have hh : (modelCoordinateEquiv R ∘ (fun i => mapModel (algebraMap k R) (v i))) =
        (fun i j => algebraMap k R ((modelCoordinateEquiv k ∘ v) i j)) := by
      funext i j
      rw [Function.comp_apply]
      exact congrFun (modelCoordinateEquiv_natural (algebraMap k R) (v i)) j
    rw [hh]
    have ht := transverseCoefficient_map (algebraMap k R) (modelCoordinateEquiv k ∘ v)
    exact ht ▸ (isUnit_iff_ne_zero.mpr hv).map (algebraMap k R)
  have ht0 := transversePoint_factor_parameter_zero A R
    (fun i => mapModel (algebraMap k R) (v i)) hw _ (b.toMul.val ≫ D.parabolic.inclusion.hom.hom)
    (h.toMul.val ≫ H.inclusion.hom.hom) ((D.parabolic_points _ _).mpr ⟨b.toMul.val, rfl⟩)
    (hfix R h.toMul.val) he.symm
  exact one_ne_zero (congrArg TrivSqZeroExt.snd ht0)

private theorem transverse_tangent_span
    (G : AffineAlgebraicGroup k) (A : SplitAction G.val)
    (D : LimitDecomposition (chamberCocharacter A)) (H : ClosedSubgroup G.val)
    (v : Slot → Model k) (hv : transverseCoefficient (modelCoordinateEquiv k ∘ v) ≠ 0)
    (hfix : ∀ (R : TestAlgebra k) (h : Points H.group.X R) (i : Slot),
      A.action R (h ≫ H.inclusion.hom.hom) (mapModel (algebraMap k R) (v i)) =
        mapModel (algebraMap k R) (v i)) :
    let V := intersectionOverLeft D.parabolic H
    letI : IsAffine G.val.X.left := G.property.1
    letI : IsAffine D.parabolic.group.X.left := (subgroupAlgebraicGroup D.parabolic).property.1
    letI : IsAffine H.group.X.left := (subgroupAlgebraicGroup H).property.1
    letI : IsAffine V.group.X.left :=
      (subgroupAlgebraicGroup (G := subgroupAlgebraicGroup D.parabolic) V).property.1
    Module.finrank k (Lie k G.val) = 52 →
    Module.finrank k (Lie k D.parabolic.group) = 28 →
    Module.finrank k (Lie k H.group) = 28 →
    Module.finrank k (Lie k V.group) ≤ 5 →
    Module.finrank k (Lie k V.group) = 5 ∧
      (lieMap D.parabolic.inclusion).range ⊔ (lieMap H.inclusion).range ⊔
        k ∙ transverseTangent A = ⊤ := by
  let V := intersectionOverLeft D.parabolic H
  letI : IsAffine G.val.X.left := G.property.1
  letI : IsAffine D.parabolic.group.X.left := (subgroupAlgebraicGroup D.parabolic).property.1
  letI : IsAffine H.group.X.left := (subgroupAlgebraicGroup H).property.1
  letI : IsAffine V.group.X.left :=
    (subgroupAlgebraicGroup (G := subgroupAlgebraicGroup D.parabolic) V).property.1
  dsimp only
  intro dG dB dH dV
  letI : Module.Finite k (Module.End k (Model k)) :=
    Module.Finite.of_injective (matrixToOperator k).symm.toLinearMap (matrixToOperator k).symm.injective
  letI : Module.Finite k (Lie k G.val) :=
    Module.Finite.of_injective (splitActionDifferential G A) (splitActionDifferential_injective G A)
  let B := (lieMap D.parabolic.inclusion).range
  let C := (lieMap H.inclusion).range
  have hrB : Module.finrank k B = 28 :=
    (finrank_lieMap_closed_range _ D.parabolic.isClosedImmersion).trans dB
  have hrC : Module.finrank k C = 28 :=
    (finrank_lieMap_closed_range _ H.isClosedImmersion).trans dH
  obtain ⟨hi, hR⟩ := lieClosedIntersection k D.parabolic.isClosedImmersion H.isClosedImmersion
    (IsPullback.of_hasPullback D.parabolic.inclusion H.inclusion)
  let f : Lie k V.group →ₗ[k] Lie k G.val := lieMap (V.inclusion ≫ D.parabolic.inclusion)
  have hf : f.range = B ⊓ C := SetLike.coe_injective hR
  have hdV : Module.finrank k (B ⊓ C : Submodule k (Lie k G.val)) =
      Module.finrank k (Lie k V.group) :=
    hf ▸ (LinearEquiv.ofInjective f hi).finrank_eq.symm
  have hs : Module.finrank k (B ⊔ C : Submodule k (Lie k G.val)) +
      Module.finrank k (Lie k V.group) = 56 := by
    rw [← hdV, Submodule.finrank_sup_add_finrank_inf_eq, hrB, hrC]
  have hnot : transverseTangent A ∉ B ⊔ C :=
    transverseTangent_not_mem_sum G A D H v hv hfix
  have ht : Module.finrank k (B ⊔ C ⊔ k ∙ transverseTangent A : Submodule k (Lie k G.val)) =
      Module.finrank k (B ⊔ C : Submodule k (Lie k G.val)) + 1 :=
    Submodule.finrank_sup_span_singleton hnot
  have hk : Module.finrank k (B ⊔ C ⊔ k ∙ transverseTangent A : Submodule k (Lie k G.val)) ≤ 52 :=
    dG ▸ Submodule.finrank_le _
  change Module.finrank k (Lie k V.group) ≤ 5 at dV
  change Module.finrank k (Lie k V.group) = 5 ∧ B ⊔ C ⊔ k ∙ transverseTangent A = ⊤
  refine ⟨by omega, ?_⟩
  apply Submodule.eq_top_of_finrank_eq
  rw [dG]
  omega

end

end TransverseTangent

section SmoothIntersectionFibre

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open LinearAlgebraicGroups.Specs LinearAlgebraicGroups.CocharacterDynamics
open scoped CategoryTheory.MonObj
open Albert.TrialitySpecification (Model mapModel)
open Albert.ReductiveFiberSpecification (SplitAction)
open private isPullback_tensor_structure from LinearAlgebraicGroups.Flag.SmoothOrbit
open private pointHom_injective from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private affineSpectrum from LinearAlgebraicGroups.Reductive.CocharacterSmoothAndUnipotent

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 900000

variable {k : Type} [Field k]

private theorem affine_tensor {X Y : SchemeOver k}
    [IsAffine X.left] [IsAffine Y.left] : IsAffine (X ⊗ Y).left :=
  IsAffine.of_isPullback (isPullback_tensor_structure X Y)

private theorem smooth_tensor {X Y : SchemeOver k}
    [Smooth X.hom] [Smooth Y.hom] : Smooth (X ⊗ Y).hom := by
  letI : Smooth (fst X Y).left :=
    MorphismProperty.of_isPullback (P := @Smooth) (isPullback_tensor_structure X Y).flip inferInstance
  rw [← Over.w (fst X Y)]
  infer_instance

private theorem affine_isIso_of_pointBijective {X Y : SchemeOver k}
    [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y)
    (h : ∀ R : TestAlgebra k, Function.Bijective (fun p : Points X R => p ≫ f)) :
    IsIso f := by
  obtain ⟨B, ⟨e⟩⟩ := essImage_algSpec.mpr (inferInstance : IsAffine Y.left)
  obtain ⟨p, hp⟩ := (h B.unop).2 e.hom
  let g := e.inv ≫ p
  have hg : g ≫ f = 𝟙 Y := by simp [g, hp]
  refine ⟨g, ?_, hg⟩
  obtain ⟨C, ⟨i⟩⟩ := essImage_algSpec.mpr (inferInstance : IsAffine X.left)
  apply (cancel_epi i.hom).mp
  apply (h C.unop).1
  simp only [Category.assoc, hg, Category.comp_id]

private abbrev TransverseProduct {G : GroupScheme k} (B H : ClosedSubgroup G) :=
  (Ga k).val.X ⊗ (B.group.X ⊗ H.group.X)

private def transverseProductMap {G : GroupScheme k} (A : SplitAction G)
    (B H : ClosedSubgroup G) : TransverseProduct B H ⟶ G.X :=
  (fst _ _ ≫ (transverseLine A).hom.hom) *
    (snd _ _ ≫ multiplyFactors B.inclusion H.inclusion)

private theorem transverseProductMap_apply {G : GroupScheme k} (A : SplitAction G)
    (B H : ClosedSubgroup G) {R : TestAlgebra k}
    (t : Points (Ga k).val.X R) (b : Points B.group.X R) (h : Points H.group.X R) :
    lift t (lift b h) ≫ transverseProductMap A B H =
      (t ≫ (transverseLine A).hom.hom) *
        ((b ≫ B.inclusion.hom.hom) * (h ≫ H.inclusion.hom.hom)) := by
  simp only [transverseProductMap, multiplyFactors, MonObj.comp_mul, ← Category.assoc,
    lift_fst, lift_snd]

private theorem transverseProductMap_one {G : GroupScheme k} (A : SplitAction G)
    (B H : ClosedSubgroup G) (R : TestAlgebra k) :
    lift (1 : Points (Ga k).val.X R) (lift (1 : Points B.group.X R) (1 : Points H.group.X R)) ≫
      transverseProductMap A B H = 1 := by
  rw [transverseProductMap_apply]
  simp only [MonObj.one_comp, one_mul]

private theorem transverse_product_lifts
    (G : AffineAlgebraicGroup k) (A : SplitAction G.val) (B H : ClosedSubgroup G.val) :
    letI : IsAffine G.val.X.left := G.property.1
    letI : IsAffine B.group.X.left := (subgroupAlgebraicGroup B).property.1
    letI : IsAffine H.group.X.left := (subgroupAlgebraicGroup H).property.1
    (lieMap B.inclusion).range ⊔ (lieMap H.inclusion).range ⊔ k ∙ transverseTangent A = ⊤ →
    let x : Points (TransverseProduct B H) (Rational k) :=
      lift 1 (lift 1 1)
    ∀ p : Points G.val.X (LieDual k),
      mapPoints (dualReduction k) p = x ≫ transverseProductMap A B H →
        ∃ q : Points (TransverseProduct B H) (LieDual k),
          mapPoints (dualReduction k) q = x ∧ q ≫ transverseProductMap A B H = p := by
  letI : IsAffine G.val.X.left := G.property.1
  letI : IsAffine B.group.X.left := (subgroupAlgebraicGroup B).property.1
  letI : IsAffine H.group.X.left := (subgroupAlgebraicGroup H).property.1
  letI : IsAffine (Ga k).val.X.left := (Ga k).property.1
  dsimp only
  intro hspan p hp
  rw [transverseProductMap_one] at hp
  let z : Lie k G.val := ⟨p, hp⟩
  have hz : z ∈ (lieMap B.inclusion).range ⊔ (lieMap H.inclusion).range ⊔ k ∙ transverseTangent A :=
    hspan.symm ▸ Submodule.mem_top
  obtain ⟨_, hbc, u, hu, hz'⟩ := Submodule.mem_sup.mp hz
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
  obtain ⟨_, ⟨b, rfl⟩, _, ⟨h, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hbc
  let t : Lie k (Ga k).val := c • additiveTangent 1
  have hT : c • transverseTangent A = lieMap (transverseLine A) t := by
    change c • lieMap (transverseLine A) (additiveTangent 1) =
      lieMap (transverseLine A) (c • additiveTangent 1)
    rw [map_smul]
  rw [hT, add_comm] at hz'
  refine ⟨lift t.toMul.val (lift b.toMul.val h.toMul.val), ?_, ?_⟩
  · change (testSpec k).map (dualReduction k).op ≫ _ = _
    rw [comp_lift, comp_lift]
    change lift (mapPoints (dualReduction k) t.toMul.val)
      (lift (mapPoints (dualReduction k) b.toMul.val) (mapPoints (dualReduction k) h.toMul.val)) = _
    rw [show mapPoints (dualReduction k) t.toMul.val = 1 from t.toMul.property,
      show mapPoints (dualReduction k) b.toMul.val = 1 from b.toMul.property,
      show mapPoints (dualReduction k) h.toMul.val = 1 from h.toMul.property]
  · rw [transverseProductMap_apply]
    exact congrArg (fun y : Lie k G.val => y.toMul.val) hz'

private def intersectionToProduct {G : GroupScheme k} (B H : ClosedSubgroup G) :
    (intersectionOverLeft B H).group.X ⟶ TransverseProduct B H :=
  lift 1 (lift (pullback.fst B.inclusion H.inclusion).hom.hom
    ((pullback.snd B.inclusion H.inclusion).hom.hom)⁻¹)

private theorem intersectionToProduct_identity {G : GroupScheme k} (B H : ClosedSubgroup G)
    (R : TestAlgebra k) :
    (1 : Points (intersectionOverLeft B H).group.X R) ≫ intersectionToProduct B H =
      lift 1 (lift 1 1) := by
  simp only [intersectionToProduct, comp_lift, MonObj.comp_one, GrpObj.comp_inv,
    MonObj.one_comp, inv_one]

private theorem intersectionToProduct_comp {G : GroupScheme k} (A : SplitAction G)
    (B H : ClosedSubgroup G) :
    intersectionToProduct B H ≫ transverseProductMap A B H = 1 := by
  simp only [intersectionToProduct, transverseProductMap, multiplyFactors, MonObj.comp_mul,
    ← Category.assoc, lift_fst, lift_snd, MonObj.one_comp, one_mul, GrpObj.inv_comp]
  have h := congrArg (fun f : (intersectionOverLeft B H).group ⟶ G => f.hom.hom)
    (pullback.condition (f := B.inclusion) (g := H.inclusion))
  change (pullback.fst B.inclusion H.inclusion).hom.hom ≫ B.inclusion.hom.hom =
    (pullback.snd B.inclusion H.inclusion).hom.hom ≫ H.inclusion.hom.hom at h
  rw [h, mul_inv_cancel]

private theorem transverse_fibre_parameter
    {G : GroupScheme k} (A : SplitAction G)
    (D : LimitDecomposition (chamberCocharacter A)) (H : ClosedSubgroup G)
    (v : Slot → Model k) (hv : transverseCoefficient (modelCoordinateEquiv k ∘ v) ≠ 0)
    (hfix : ∀ (R : TestAlgebra k) (h : Points H.group.X R) (i : Slot),
      A.action R (h ≫ H.inclusion.hom.hom) (mapModel (algebraMap k R) (v i)) =
        mapModel (algebraMap k R) (v i))
    (R : TestAlgebra k) (t : Points (Ga k).val.X R) (b : Points D.parabolic.group.X R)
    (h : Points H.group.X R)
    (he : lift t (lift b h) ≫ transverseProductMap A D.parabolic H = 1) : t = 1 := by
  let f := ((StandardGroups.additiveGroupPointsIso k).hom.app R).hom
  let s : R := (f t : Multiplicative R).toAdd
  have heq : transversePoint A R (-s) =
      (b ≫ D.parabolic.inclusion.hom.hom) * (h ≫ H.inclusion.hom.hom) := by
    rw [transverseProductMap_apply, transverseLine_apply] at he
    change transversePoint A R s * _ = 1 at he
    have hh := inv_mul_eq_of_eq_mul (he.symm : 1 = transversePoint A R s * _)
    rw [mul_one] at hh
    exact (transversePointsHom A R).map_inv (Multiplicative.ofAdd s) |>.trans hh
  have hu : IsUnit (transverseCoefficient
      (fun i => modelCoordinateEquiv R (mapModel (algebraMap k R) (v i)))) := by
    have hEq : (fun i => modelCoordinateEquiv R (mapModel (algebraMap k R) (v i))) =
        fun i j => algebraMap k R (modelCoordinateEquiv k (v i) j) :=
      funext fun i => modelCoordinateEquiv_natural (algebraMap k R) (v i)
    rw [hEq]
    have hmap := transverseCoefficient_map (algebraMap k R) (modelCoordinateEquiv k ∘ v)
    exact (congrArg IsUnit hmap).mpr ((isUnit_iff_ne_zero.mpr hv).map (algebraMap k R))
  have hs := transversePoint_factor_parameter_zero A R _ hu (-s)
    (b ≫ D.parabolic.inclusion.hom.hom) (h ≫ H.inclusion.hom.hom)
    ((D.parabolic_points _ _).mpr ⟨b, rfl⟩) (hfix R h) heq
  apply (((StandardGroups.additiveGroupPointsIso k).app R).groupIsoToMulEquiv).injective
  change f t = f 1
  rw [map_one]
  exact congrArg Multiplicative.ofAdd (neg_eq_zero.mp hs)

private theorem transverse_product_fibre
    (G : AffineAlgebraicGroup k) (A : SplitAction G.val)
    (D : LimitDecomposition (chamberCocharacter A)) (H : ClosedSubgroup G.val)
    (v : Slot → Model k) (hv : transverseCoefficient (modelCoordinateEquiv k ∘ v) ≠ 0)
    (hfix : ∀ (R : TestAlgebra k) (h : Points H.group.X R) (i : Slot),
      A.action R (h ≫ H.inclusion.hom.hom) (mapModel (algebraMap k R) (v i)) =
        mapModel (algebraMap k R) (v i)) :
    let V := intersectionOverLeft D.parabolic H
    IsPullback (intersectionToProduct D.parabolic H).left V.group.X.hom
      (transverseProductMap A D.parabolic H).left η[G.val.X].left := by
  let B := D.parabolic
  let V := intersectionOverLeft B H
  let X := TransverseProduct B H
  let f := transverseProductMap A B H
  let Y := pullback f (η[G.val.X] : 𝟙_ (SchemeOver k) ⟶ G.val.X)
  let j : V.group.X ⟶ Y := pullback.lift (intersectionToProduct B H) (toUnit _) (by
    exact intersectionToProduct_comp A B H)
  letI : IsAffine V.group.X.left :=
    (subgroupAlgebraicGroup (G := subgroupAlgebraicGroup B) V).property.1
  letI : IsAffine B.group.X.left := (subgroupAlgebraicGroup B).property.1
  letI : IsAffine H.group.X.left := (subgroupAlgebraicGroup H).property.1
  letI : IsAffine (Ga k).val.X.left := (Ga k).property.1
  letI : IsAffine (B.group.X ⊗ H.group.X).left := affine_tensor
  letI : IsAffine X.left := affine_tensor
  have hY := (Over.forget (Spec (CommRingCat.of k))).map_isPullback
    (IsPullback.of_hasPullback f (η[G.val.X] : 𝟙_ (SchemeOver k) ⟶ G.val.X))
  letI : IsAffine ((Over.forget (Spec (CommRingCat.of k))).obj (TransverseProduct B H)) :=
    inferInstanceAs (IsAffine X.left)
  letI : IsAffine ((Over.forget (Spec (CommRingCat.of k))).obj (𝟙_ (SchemeOver k))) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of k)))
  letI : IsAffine ((Over.forget (Spec (CommRingCat.of k))).obj G.val.X) := G.property.1
  letI : IsAffineHom ((Over.forget (Spec (CommRingCat.of k))).map (η[G.val.X])) :=
    isAffineHom_of_isAffine _
  letI : IsAffine Y.left := IsAffine.of_isPullback hY
  haveI : IsIso j := affine_isIso_of_pointBijective j (by
    intro R
    constructor
    · intro p q hpq
      have hp : p ≫ intersectionToProduct B H = q ≫ intersectionToProduct B H := by
        simpa only [Category.assoc, pullback.lift_fst, j] using
          congrArg (fun u : Points Y R => u ≫ pullback.fst _ _) hpq
      let f₀ : X ⟶ B.group.X := snd _ _ ≫ fst _ _
      have hh : intersectionToProduct B H ≫ f₀ = V.inclusion.hom.hom := by
        change intersectionToProduct B H ≫ snd _ _ ≫ fst _ _ = _
        rw [← Category.assoc]
        simp only [intersectionToProduct, lift_snd, lift_fst]
        rfl
      have hpp := congrArg (fun u : Points X R => u ≫ f₀) hp
      simp only [Category.assoc, hh] at hpp
      exact (pointHom_injective V R) hpp
    · intro p
      let x : Points X R := p ≫ pullback.fst _ _
      let t : Points (Ga k).val.X R := x ≫ fst _ _
      let b : Points B.group.X R := x ≫ snd _ _ ≫ fst _ _
      let h : Points H.group.X R := x ≫ snd _ _ ≫ snd _ _
      have hx : lift t (lift b h) = x := by
        simp only [t, b, h, ← comp_lift, lift_fst_snd]
        simp only [Category.comp_id, lift_fst_snd]
        exact Category.comp_id _
      have hxf : x ≫ f = 1 := by
        change p ≫ pullback.fst _ _ ≫ f = _
        rw [pullback.condition]
        change (p ≫ pullback.snd _ _) ≫ η[G.val.X] = toUnit _ ≫ η[G.val.X]
        rw [(isTerminalTensorUnit (C := SchemeOver k)).hom_ext (p ≫ pullback.snd _ _) (toUnit _)]
      have ht : t = 1 := transverse_fibre_parameter A D H v hv hfix R t b h (by rw [hx]; exact hxf)
      have hbh : (b ≫ B.inclusion.hom.hom) * (h ≫ H.inclusion.hom.hom) = 1 := by
        rw [← hx, transverseProductMap_apply, ht, MonObj.one_comp, one_mul] at hxf
        exact hxf
      have hcomp : b ≫ B.inclusion.hom.hom = h⁻¹ ≫ H.inclusion.hom.hom := by
        rw [GrpObj.inv_comp]
        exact eq_inv_of_mul_eq_one_left hbh
      obtain ⟨y, hy⟩ := (groupPullbackPoints k B.inclusion H.inclusion R).surjective ⟨(b, h⁻¹), hcomp⟩
      have hy₁ : y ≫ (pullback.fst B.inclusion H.inclusion).hom.hom = b :=
        congrArg (fun q => q.val.1) hy
      have hy₂ : y ≫ (pullback.snd B.inclusion H.inclusion).hom.hom = h⁻¹ :=
        congrArg (fun q => q.val.2) hy
      refine ⟨y, ?_⟩
      apply pullback.hom_ext
      · change (y ≫ j) ≫ pullback.fst _ _ = x
        rw [Category.assoc, pullback.lift_fst]
        simp only [intersectionToProduct, comp_lift, MonObj.comp_one, GrpObj.comp_inv]
        change lift 1 (lift (y ≫ (pullback.fst B.inclusion H.inclusion).hom.hom)
          (y ≫ (pullback.snd B.inclusion H.inclusion).hom.hom)⁻¹) = x
        rw [hy₁, hy₂, inv_inv, ← ht, hx]
      · exact (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _)
  have hi : IsPullback (intersectionToProduct B H) (toUnit V.group.X) f η[G.val.X] :=
    IsPullback.of_iso_pullback ⟨intersectionToProduct_comp A B H⟩ (asIso j)
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  exact (Over.forget (Spec (CommRingCat.of k))).map_isPullback hi

private theorem smoothAtIdentity_of_smoothNeighborhood
    (V : AffineAlgebraicGroup k) {X Y : SchemeOver k} (t : V.val.X ⟶ X)
    (f : X ⟶ Y) (y : 𝟙_ (SchemeOver k) ⟶ Y)
    (ht : IsPullback t.left V.val.X.hom f.left y.left)
    {W : SchemeOver k} (j : W ⟶ X) (hj : IsOpenImmersion j.left)
    (hs : Smooth (j.left ≫ f.left))
    (w : Points W (Rational k)) (hw : w ≫ j = (1 : Points V.val.X (Rational k)) ≫ t) :
    Smooth V.val.X.hom := by
  letI := V.property.2.1
  letI := hj
  let Z := pullback t.left j.left
  let a : Z ⟶ V.val.X.left := pullback.fst _ _
  let b : Z ⟶ W.left := pullback.snd _ _
  have hZ : IsPullback b (a ≫ V.val.X.hom) (j.left ≫ f.left) y.left :=
    (IsPullback.of_hasPullback t.left j.left).flip.paste_vert ht
  letI : Smooth (a ≫ V.val.X.hom) := MorphismProperty.of_isPullback hZ hs
  letI : IsOpenImmersion a := inferInstanceAs (IsOpenImmersion (pullback.fst t.left j.left))
  have hId : (1 : Points V.val.X (Rational k)).left = η[V.val.X].left := by
    rw [CategoryTheory.Hom.one_def, Over.comp_left, Over.toUnit_left]
    change Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ η[V.val.X].left = _
    rw [show CommRingCat.ofHom (algebraMap k k) = 𝟙 (CommRingCat.of k) from
      CommRingCat.hom_ext (RingHom.ext (Algebra.algebraMap_self_apply (R := k))),
      Spec.map_id, Category.id_comp]
  have he : η[V.val.X].left ≫ t.left = w.left ≫ j.left := by
    have he' := congrArg Over.Hom.left hw.symm
    rwa [Over.comp_left, hId, Over.comp_left] at he' 
  let z : Spec (CommRingCat.of k) ⟶ Z := pullback.lift η[V.val.X].left w.left he
  have hz : z ≫ a = η[V.val.X].left := pullback.lift_fst _ _ _
  have hm : a (z (IsLocalRing.closedPoint k)) = groupIdentityPoint V.val :=
    congrArg (fun s : Spec (CommRingCat.of k) ⟶ V.val.X.left => s (IsLocalRing.closedPoint k)) hz
  apply ((groupSmoothnessCriteria k V.val).2).mpr
  change groupIdentityPoint V.val ∈ V.val.X.hom.smoothLocus
  rw [← hm, ← Scheme.Hom.mem_preimage, Scheme.Hom.preimage_smoothLocus_eq,
    Scheme.Hom.smoothLocus_eq_top]
  trivial

private theorem geometricIntersection_smooth
    (G : AffineAlgebraicGroup k) (A : SplitAction G.val)
    (D : LimitDecomposition (chamberCocharacter A)) (H : ClosedSubgroup G.val)
    (v : Slot → Model k) (hv : transverseCoefficient (modelCoordinateEquiv k ∘ v) ≠ 0)
    (hfix : ∀ (R : TestAlgebra k) (h : Points H.group.X R) (i : Slot),
      A.action R (h ≫ H.inclusion.hom.hom) (mapModel (algebraMap k R) (v i)) =
        mapModel (algebraMap k R) (v i))
    (hB : Smooth D.parabolic.group.X.hom) (hH : Smooth H.group.X.hom) :
    letI : IsAffine G.val.X.left := G.property.1
    letI : IsAffine D.parabolic.group.X.left := (subgroupAlgebraicGroup D.parabolic).property.1
    letI : IsAffine H.group.X.left := (subgroupAlgebraicGroup H).property.1
    (lieMap D.parabolic.inclusion).range ⊔ (lieMap H.inclusion).range ⊔ k ∙ transverseTangent A = ⊤ →
      Smooth (intersectionOverLeft D.parabolic H).group.X.hom := by
  let B := D.parabolic
  let V := intersectionOverLeft B H
  let VG := subgroupAlgebraicGroup (G := subgroupAlgebraicGroup B) V
  let f := transverseProductMap A B H
  let t := intersectionToProduct B H
  letI := hB
  letI := hH
  letI : IsAffine G.val.X.left := G.property.1
  letI : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  letI : IsAffine B.group.X.left := (subgroupAlgebraicGroup B).property.1
  letI : IsAffine H.group.X.left := (subgroupAlgebraicGroup H).property.1
  letI : IsAffine (Ga k).val.X.left := (Ga k).property.1
  letI : IsAffine (B.group.X ⊗ H.group.X).left := affine_tensor
  letI : IsAffine (TransverseProduct B H).left := affine_tensor
  letI : Smooth (Ga k).val.X.hom := by
    change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))))
    exact HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr
      (show Algebra.Smooth k (Polynomial k) from ⟨inferInstance, inferInstance⟩))
  letI : Smooth (B.group.X ⊗ H.group.X).hom := smooth_tensor
  letI : Smooth (TransverseProduct B H).hom := smooth_tensor
  intro h
  obtain ⟨W, j, hj, hs, w, hw⟩ :=
    smoothNeighbourhood_of_dualPointLifting f (lift 1 (lift 1 1))
      (transverse_product_lifts G A B H h)
  refine smoothAtIdentity_of_smoothNeighborhood VG t f η[G.val.X]
    (transverse_product_fibre G A D H v hv hfix) j hj hs w ?_
  exact hw.trans (intersectionToProduct_identity B H (Rational k)).symm

end

end SmoothIntersectionFibre

section IntersectionDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open LinearAlgebraicGroups.Specs LinearAlgebraicGroups.CocharacterDynamics
open Specs.Unipotent (baseChangedAlgebraicGroup)
open Specs.CharacterDescent (Cocharacter)
open Albert.TrialitySpecification (Model mapModel)
open Albert.ReductiveFiberSpecification (SplitAction)
open scoped CategoryTheory.MonObj TensorProduct
open private cocharacter_ext_units subgroupIso_of_same from LinearAlgebraicGroups.RootData.RankOneFlag
open private subgroupInclusionFactors from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private smooth_of_smooth_after_fieldExtension from LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private vectorStructure_unique from LinearAlgebraicGroups.Affine.LieBracket
open private LinearAlgebraicGroups.LieVectorStructure.ofAffine from LinearAlgebraicGroups.Affine.IdentityTangent

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 450000

variable {k K : Type} [Field k] [Field K] [Algebra k K]

private theorem representedSubgroup_iso {G : AffineAlgebraicGroup k}
    (S T : ClosedSubgroup G.val) {P : ∀ R : TestAlgebra k, Points G.val.X R → Prop}
    (hS : RepresentsOnAlgebras S P) (hT : RepresentsOnAlgebras T P) :
    ∃ i : S.group ≅ T.group, i.hom ≫ T.inclusion = S.inclusion := by
  obtain ⟨f, hf⟩ := subgroupInclusionFactors (subgroupAlgebraicGroup S).property.1
    T S.inclusion (fun R p => (hT R _).mp ((hS R _).mpr ⟨p, rfl⟩))
  obtain ⟨g, hg⟩ := subgroupInclusionFactors (subgroupAlgebraicGroup T).property.1
    S T.inclusion (fun R p => (hS R _).mp ((hT R _).mpr ⟨p, rfl⟩))
  exact subgroupIso_of_same (A := S) (B := T) ⟨⟨f, hf⟩, ⟨g, hg⟩⟩

private theorem chamber_subgroups_baseChange (G : AffineAlgebraicGroup k) (A : SplitAction G.val)
    (D : LimitDecomposition (chamberCocharacter A))
    (E : LimitDecomposition (chamberCocharacter (extendSplitAction (K := K) A))) :
    let F := groupBaseChange k K
    ∃ (b : F.obj D.parabolic.group ≅ E.parabolic.group)
      (u : F.obj D.contracting.group ≅ E.contracting.group),
      b.hom ≫ E.parabolic.inclusion = F.map D.parabolic.inclusion ∧
      u.hom ≫ E.contracting.inclusion = F.map D.contracting.inclusion := by
  let F := groupBaseChange k K
  let A' := extendSplitAction (K := K) A
  obtain ⟨e, he, hb, hu, hz, hB, hU, _⟩ :=
    limitSubgroupsBaseChange (K := K) G (chamberCocharacter A) D
  have hc : e.hom ≫ F.map (chamberCocharacter A) = chamberCocharacter A' := by
    apply cocharacter_ext_units
    intro R s
    apply A'.injective R
    rw [chamberCocharacter_action]
    let C := specGroup (Specs.DiagonalizableGroups.groupAlgebra k
      Specs.DiagonalizableGroups.IntegerCharacters)
    let z : Points (F.obj C).X R := unitPoint R s ≫ e.hom.hom.hom
    have hn := baseChangePointsSchemeNaturality k K (chamberCocharacter A).hom.hom R z
    change A.action ((restrictTestAlgebra k K).obj R)
      (baseChangePoint k K G.val.X R (z ≫ (baseChange k K).map (chamberCocharacter A).hom.hom)) = _
    rw [hn, show baseChangePoint k K C.X R z = unitPoint ((restrictTestAlgebra k K).obj R) s from he R s]
    exact chamberCocharacter_action A ((restrictTestAlgebra k K).obj R) s
  change e.hom ≫ (groupBaseChange k K).map (chamberCocharacter A) = _ at hc
  rw [hc] at hB hU
  obtain ⟨b, h₁⟩ := representedSubgroup_iso (G := baseChangedAlgebraicGroup K G)
    (scalarExtendedSubgroup K D.parabolic hb) E.parabolic hB E.parabolic_points
  obtain ⟨u, h₂⟩ := representedSubgroup_iso (G := baseChangedAlgebraicGroup K G)
    (scalarExtendedSubgroup K D.contracting hu) E.contracting hU E.contracting_points
  exact ⟨b, u, h₁, h₂⟩

private theorem intersection_baseChange_iso {G : GroupScheme k}
    (S H : ClosedSubgroup G) (T : ClosedSubgroup ((groupBaseChange k K).obj G))
    (e : (groupBaseChange k K).obj S.group ≅ T.group)
    (he : e.hom ≫ T.inclusion = (groupBaseChange k K).map S.inclusion) :
    let HK := scalarExtendedSubgroup K H (baseChangeClosedSubgroup k K H.inclusion H.isClosedImmersion)
    Nonempty ((groupBaseChange k K).obj (intersectionOverLeft S H).group ≅
      (intersectionOverLeft T HK).group) := by
  let F := groupBaseChange k K
  let H' := scalarExtendedSubgroup K H (baseChangeClosedSubgroup k K H.inclusion H.isClosedImmersion)
  have p := baseChangeSubgroupPullback k K (IsPullback.of_hasPullback S.inclusion H.inclusion)
  have q : IsPullback (F.map (pullback.fst S.inclusion H.inclusion) ≫ e.hom)
      (F.map (pullback.snd S.inclusion H.inclusion)) T.inclusion H'.inclusion := by
    refine p.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp only [Iso.refl_hom, Category.id_comp]; rfl
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl
    · simpa only [Iso.refl_hom, Category.comp_id] using he.symm
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      rfl
  exact ⟨q.isoPullback⟩

private theorem lieRank_baseChange (G : AffineAlgebraicGroup k) :
    letI : IsAffine G.val.X.left := G.property.1
    letI : IsAffine ((groupBaseChange k K).obj G.val).X.left :=
      (baseChangedAlgebraicGroup K G).property.1
    Module.finrank K (Lie K ((groupBaseChange k K).obj G.val)) =
      Module.finrank k (Lie k G.val) := by
  let G' := baseChangedAlgebraicGroup K G
  letI : IsAffine G.val.X.left := G.property.1
  letI : IsAffine ((groupBaseChange k K).obj G.val).X.left := G'.property.1
  letI : IsAffine G'.val.X.left := G'.property.1
  obtain ⟨m, n, h⟩ := lieBaseChange k K G
  have hm := vectorStructure_unique m (LinearAlgebraicGroups.LieVectorStructure.ofAffine G.val)
  have hn := vectorStructure_unique n (LinearAlgebraicGroups.LieVectorStructure.ofAffine G'.val)
  subst m
  subst n
  obtain ⟨e, _⟩ := h
  exact e.finrank_eq.symm.trans (Module.finrank_baseChange (R := K) (S := k))

private theorem smooth_of_groupIso {G H : GroupScheme k} (e : G ≅ H)
    (h : Smooth H.X.hom) : Smooth G.X.hom := by
  let j := (Grp.forget (SchemeOver k)).mapIso e
  letI : IsIso j.hom.left := (Over.forget _).map_isIso j.hom
  letI := h
  have hj : j.hom.left ≫ H.X.hom = G.X.hom := Over.w j.hom
  rw [← hj]
  infer_instance

private theorem intersection_fixes_frame {G : GroupScheme k} (A : SplitAction G)
    (S H : ClosedSubgroup G) (v : Slot → Model k)
    (h : ∀ (R : TestAlgebra k) (x : Points H.group.X R) (i : Slot),
      A.action R (x ≫ H.inclusion.hom.hom) (mapModel (algebraMap k R) (v i)) =
        mapModel (algebraMap k R) (v i)) :
    ∀ (R : TestAlgebra k) (x : Points (intersectionOverLeft S H).group.X R) (i : Slot),
      A.action R (x ≫ (intersectionOverLeft S H).inclusion.hom.hom ≫ S.inclusion.hom.hom)
        (mapModel (algebraMap k R) (v i)) = mapModel (algebraMap k R) (v i) := by
  intro R x i
  have he := congrArg (fun f : (intersectionOverLeft S H).group ⟶ G => f.hom.hom)
    (pullback.condition (f := S.inclusion) (g := H.inclusion))
  change (intersectionOverLeft S H).inclusion.hom.hom ≫ S.inclusion.hom.hom =
    (pullback.snd S.inclusion H.inclusion).hom.hom ≫ H.inclusion.hom.hom at he
  rw [he, ← Category.assoc]
  exact h R _ i

private theorem good_frame_intersection
    (G : AffineAlgebraicGroup k) (A : SplitAction G.val) (D : LimitDecomposition (chamberCocharacter A))
    (H : ClosedSubgroup G.val)
    (hG : SmoothOfRelativeDimension 52 G.val.X.hom)
    (hH : SmoothOfRelativeDimension 28 ((groupBaseChange k K).obj H.group).X.hom)
    (v : Slot → Model K) (hv : frameRankPolynomial (modelCoordinateEquiv K ∘ v) ≠ 0)
    (ht : transverseCoefficient (modelCoordinateEquiv K ∘ v) ≠ 0)
    (hfix : ∀ (R : TestAlgebra K) (x : Points ((groupBaseChange k K).obj H.group).X R) (i : Slot),
      (extendSplitAction A).action R (x ≫ ((groupBaseChange k K).map H.inclusion).hom.hom)
        (mapModel (algebraMap K R) (v i)) = mapModel (algebraMap K R) (v i)) :
    let V := intersectionOverLeft D.parabolic H
    let W := intersectionOverLeft D.contracting H
    letI : IsAffine V.group.X.left :=
      (subgroupAlgebraicGroup (G := subgroupAlgebraicGroup D.parabolic) V).property.1
    letI : IsAffine W.group.X.left :=
      (subgroupAlgebraicGroup (G := subgroupAlgebraicGroup D.contracting) W).property.1
    Smooth V.group.X.hom ∧ Module.finrank k (Lie k V.group) = 5 ∧
      Module.finrank k (Lie k W.group) ≤ 3 := by
  let F := groupBaseChange k K
  let G' := baseChangedAlgebraicGroup K G
  let A' := extendSplitAction (K := K) A
  let H' := scalarExtendedSubgroup K H (baseChangeClosedSubgroup k K H.inclusion H.isClosedImmersion)
  let V := intersectionOverLeft D.parabolic H
  let W := intersectionOverLeft D.contracting H
  let VG := subgroupAlgebraicGroup (G := subgroupAlgebraicGroup D.parabolic) V
  let WG := subgroupAlgebraicGroup (G := subgroupAlgebraicGroup D.contracting) W
  letI : IsAffine G'.val.X.left := G'.property.1
  letI : IsAffine ((groupBaseChange k K).obj H.group).X.left :=
    (subgroupAlgebraicGroup (G := G') H').property.1
  letI : IsAffine VG.val.X.left := VG.property.1
  letI : IsAffine WG.val.X.left := WG.property.1
  letI : IsAffine ((groupBaseChange k K).obj VG.val).X.left := (baseChangedAlgebraicGroup K VG).property.1
  letI : IsAffine ((groupBaseChange k K).obj WG.val).X.left := (baseChangedAlgebraicGroup K WG).property.1
  letI : IsAffine ((groupBaseChange k K).obj (intersectionOverLeft D.parabolic H).group).X.left :=
    (baseChangedAlgebraicGroup K VG).property.1
  letI : IsAffine ((groupBaseChange k K).obj (intersectionOverLeft D.contracting H).group).X.left :=
    (baseChangedAlgebraicGroup K WG).property.1
  letI : SmoothOfRelativeDimension 52 G.val.X.hom := hG
  have hG' : SmoothOfRelativeDimension 52 G'.val.X.hom :=
    inferInstanceAs (SmoothOfRelativeDimension 52 (pullback.snd G.val.X.hom (fieldSpecMap k K)))
  letI := hG'
  letI : Smooth G'.val.X.hom := SmoothOfRelativeDimension.smooth 52 _
  obtain ⟨D'⟩ := existsLimitDecomposition G' (chamberCocharacter A')
  obtain ⟨E'⟩ := existsLimitDecomposition G' (oppositeCocharacter (chamberCocharacter A'))
  obtain ⟨b, u, hb, hu⟩ := chamber_subgroups_baseChange G A D D'
  obtain ⟨eV⟩ := intersection_baseChange_iso D.parabolic H D'.parabolic b hb
  obtain ⟨eW⟩ := intersection_baseChange_iso D.contracting H D'.contracting u hu
  let V' := intersectionOverLeft D'.parabolic H'
  let W' := intersectionOverLeft D'.contracting H'
  letI : IsAffine (intersectionOverLeft D'.parabolic H').group.X.left :=
    (subgroupAlgebraicGroup (G := subgroupAlgebraicGroup (G := G') D'.parabolic) V').property.1
  letI : IsAffine (intersectionOverLeft D'.contracting H').group.X.left :=
    (subgroupAlgebraicGroup (G := subgroupAlgebraicGroup (G := G') D'.contracting) W').property.1
  have dG := lie_finrank_of_smoothDimension 52 hG'
  obtain ⟨dB, dU, _⟩ := chamberLieRanks G' A' dG D' E'
  have dH := lie_finrank_of_smoothDimension 28 hH
  obtain ⟨dV, dW⟩ := frameIntersection_lieRank_le G' A' D' v hv dB.le dU.le V' W'
    (intersection_fixes_frame A' D'.parabolic H' v hfix _) 
    (intersection_fixes_frame A' D'.contracting H' v hfix _)
  obtain ⟨dV', hspan⟩ := transverse_tangent_span G' A' D' H' v ht hfix dG dB dH dV
  have hB := (limitSubgroupsSmooth G' (chamberCocharacter A') D').1
  letI : SmoothOfRelativeDimension 28 H'.group.X.hom := hH
  have hsmooth := geometricIntersection_smooth G' A' D' H' v ht hfix hB
    (SmoothOfRelativeDimension.smooth 28 H'.group.X.hom) hspan
  have hV := smooth_of_smooth_after_fieldExtension (K := K) V.group.X.hom
    (smooth_of_groupIso eV hsmooth)
  exact ⟨hV, (lieRank_baseChange (K := K) VG).symm.trans
    ((lieRank_of_iso eV).trans dV'),
    ((lieRank_baseChange (K := K) WG).symm.trans (lieRank_of_iso eW)).le.trans dW⟩

end

end IntersectionDescent

section SplitTorusProjection

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open LinearAlgebraicGroups.Specs LinearAlgebraicGroups.CocharacterDynamics
open scoped CategoryTheory.MonObj
open Specs.GeometricRadicals (IsTorus IsSplitTorus IsTrivialSubgroup)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.CharacterDescent (Cocharacter)
open Specs.DiagonalizableGroups (diagonalGroup)
open DiagonalizableGroups (diagonalIntegerPowers)
open private isTorus_iff_coordinates from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private lattice_torus_of_split from LinearAlgebraicGroups.RootData.RankOneFlag
open private torus_multiplicativeType from LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private trivial_baseChange_iff from LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private closedImmersion_of_injective_test_points from
  LinearAlgebraicGroups.Classification.RationalRealization
open private subgroupInclusionFactors from
  LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 950000

variable {k : Type} [Field k]

private def subgroupComposite {G : GroupScheme k} (S : ClosedSubgroup G)
    (H : ClosedSubgroup S.group) : ClosedSubgroup G := by
  letI := S.isClosedImmersion
  letI := H.isClosedImmersion
  exact ⟨H.group, H.inclusion ≫ S.inclusion,
    IsClosedImmersion.comp H.inclusion.hom.hom.left S.inclusion.hom.hom.left⟩

private def contractingInParabolic {G : GroupScheme k}
    {c : Cocharacter G} (D : LimitDecomposition c) : ClosedSubgroup D.parabolic.group := by
  let f := D.contractingToParabolic
  letI := D.parabolic.isClosedImmersion
  haveI : IsClosedImmersion (f.hom.hom.left ≫ D.parabolic.inclusion.hom.hom.left) := by
    change IsClosedImmersion (f ≫ D.parabolic.inclusion).hom.hom.left
    rw [D.contracting_in_G]
    exact D.contracting.isClosedImmersion
  exact ⟨_, f, IsClosedImmersion.of_comp_isClosedImmersion f.hom.hom.left D.parabolic.inclusion.hom.hom.left⟩

private theorem limit_kernel_lift {G : GroupScheme k} {c : Cocharacter G}
    (D : LimitDecomposition c) (R : TestAlgebra k) (x : Points D.parabolic.group.X R)
    (h : x ≫ D.limit.hom.hom = 1) :
    ∃ u : Points D.contracting.group.X R, u ≫ D.contractingToParabolic.hom.hom = x := by
  have hx : x ≫ D.limit.hom.hom = toUnit _ ≫ η[D.centralizer.group.X] := h
  let u := D.isKernel.lift x (toUnit _) hx
  exact ⟨u, D.isKernel.lift_fst _ _ _⟩

private theorem factor_through_contracting {G J : GroupScheme k} {c : Cocharacter G}
    (D : LimitDecomposition c) (j : J ⟶ D.parabolic.group) [IsAffine J.X.left]
    (h : j ≫ D.limit = 0) :
    ∃ f : J ⟶ D.contracting.group, f ≫ D.contractingToParabolic = j := by
  apply subgroupInclusionFactors (C := contractingInParabolic D) inferInstance j
  intro R p
  apply limit_kernel_lift
  change (p ≫ j.hom.hom) ≫ D.limit.hom.hom = 1
  rw [Category.assoc, ← show (j ≫ D.limit).hom.hom = j.hom.hom ≫ D.limit.hom.hom from rfl, h]
  exact MonObj.comp_one p

private theorem splitPower_zero_isZero (k : Type) [Field k] :
    IsZero (StandardGroups.multiplicativePowerGroup k (ULift (Fin 0))).val := by
  let T := StandardGroups.multiplicativePowerGroup k (ULift (Fin 0))
  rw [IsZero.iff_id_eq_zero]
  apply (groupHomComparison k T.val T.val T.property.1).1
  ext R p
  apply (((StandardGroups.multiplicativePowerGroupPointsIso k (ULift (Fin 0))).app R).groupIsoToMulEquiv).injective
  apply funext
  intro i
  exact Fin.elim0 i.down

private theorem torus_has_infiniteOrder_point {G : GroupScheme k} (T : ClosedSubgroup G)
    (hT : IsTorus T.group) (hN : ¬ IsTrivialSubgroup T)
    (a : kˣ) (ha : ¬ IsOfFinOrder a) :
    ∃ (R : TestAlgebra k) (x : Points T.group.X R), ¬ IsOfFinOrder x := by
  obtain ⟨E, iE, iA, _, r, ⟨e⟩⟩ := hT
  have hpos : 0 < r := by
    by_contra! h
    have hr : r = 0 := Nat.eq_zero_of_le_zero h
    subst r
    apply hN
    exact (trivial_baseChange_iff (K := E) T.group).mp
      ⟨e ≪≫ (splitPower_zero_isZero E).iso (Grp.isZero_trivial _)⟩
  let t := Units.map (algebraMap k E).toMonoidHom
  have ht : ¬ IsOfFinOrder (t a) := fun h =>
    ha (((Units.map_injective (algebraMap k E).injective : Function.Injective t).isOfFinOrder_iff).mp h)
  let R := CommAlgCat.of E E
  let q := (((groupPointsFunctor E).mapIso e).app R).groupIsoToMulEquiv
  let s := ((StandardGroups.multiplicativePowerGroupPointsIso E (ULift (Fin r))).app R).groupIsoToMulEquiv
  let b : ULift (Fin r) → Eˣ := fun _ => t a
  let x := (baseChangePointGroupEquiv E T.group R) ((q.trans s).symm b)
  refine ⟨_, x, ?_⟩
  intro hx
  have hy := MonoidHom.isOfFinOrder
    ((baseChangePointGroupEquiv E T.group R).symm.trans (q.trans s)).toMonoidHom hx
  have hb : ((baseChangePointGroupEquiv E T.group R).symm.trans (q.trans s)) x = b := by
    change (q.trans s) ((baseChangePointGroupEquiv E T.group R).symm
      ((baseChangePointGroupEquiv E T.group R) ((q.trans s).symm b))) = b
    rw [MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]
  change IsOfFinOrder (((baseChangePointGroupEquiv E T.group R).symm.trans (q.trans s)) x) at hy
  rw [hb] at hy
  change IsOfFinOrder (b : ULift (Fin r) → Eˣ) at hy
  exact ht (hy.apply (ULift.up ⟨0, hpos⟩))

private theorem projection_closed_on_torus (G : AffineAlgebraicGroup k) [Smooth G.val.X.hom]
    (c : Cocharacter G.val) (D : LimitDecomposition c) (T : ClosedSubgroup D.parabolic.group)
    (hT : IsTorus T.group) :
    IsClosedImmersion (T.inclusion ≫ D.limit).hom.hom.left := by
  let B := subgroupAlgebraicGroup D.parabolic
  let U := contractingInParabolic D
  let TA := subgroupAlgebraicGroup (G := B) T
  let C := subgroupAlgebraicGroup D.centralizer
  have hU : Specs.Unipotent.IsUnipotent (closedSubgroupAlgebraicGroup (G := B) U) :=
    contractingSubgroupUnipotent G c D
  have hM := torus_multiplicativeType ((isTorus_iff_coordinates TA).mp hT)
  have hzero := Unipotent.unipotentMultiplicativeTypeIntersection B U T _ _
    (IsPullback.of_hasPullback U.inclusion T.inclusion) hU hM
  let i : T.group ⟶ C.val := T.inclusion ≫ D.limit
  apply closedImmersion_of_injective_test_points (G := TA) (H := C) i
  intro R x y he
  change x ≫ i.hom.hom = y ≫ i.hom.hom at he
  let z := x * y⁻¹
  have hz : z ≫ i.hom.hom = 1 := by
    change (x * y⁻¹) ≫ i.hom.hom = _
    rw [MonObj.mul_comp, GrpObj.inv_comp, he, mul_inv_cancel]
  have hZ : (z ≫ T.inclusion.hom.hom) ≫ D.limit.hom.hom = 1 := hz
  obtain ⟨u, hu⟩ := limit_kernel_lift D R (z ≫ T.inclusion.hom.hom) hZ
  obtain ⟨p, hp⟩ := (groupPullbackPoints k U.inclusion T.inclusion R).surjective
    ⟨(u, z), hu⟩
  have hpz : p ≫ (pullback.snd U.inclusion T.inclusion).hom.hom = z :=
    congrArg (fun q => q.val.2) hp
  let Z := pullback U.inclusion T.inclusion
  have hP : IsTerminal Z.X :=
    IsTerminal.isTerminalObj (Grp.forget (SchemeOver k)) Z hzero.isTerminal
  have hp1 : p = 1 := hP.hom_ext _ _
  rw [hp1, MonObj.one_comp] at hpz
  exact eq_of_mul_inv_eq_one hpz.symm

private theorem splitTorus_of_positive_projection
    [Infinite k] (G : AffineAlgebraicGroup k) [Smooth G.val.X.hom]
    (c : Cocharacter G.val) (D : LimitDecomposition c) (S : ClosedSubgroup D.parabolic.group)
    (hs : Smooth S.group.X.hom) (hc : ConnectedSpace S.group.X.left)
    (hZ : IsSplitTorus D.centralizer.group) (hp : S.inclusion ≫ D.limit ≠ 0)
    (a : kˣ) (ha : ¬ IsOfFinOrder a) :
    ∃ T : ClosedSubgroup S.group,
      Nonempty (T.group ≅ (StandardGroups.multiplicativePowerGroup k (ULift (Fin 1))).val) := by
  let A := subgroupAlgebraicGroup (G := subgroupAlgebraicGroup D.parabolic) S
  let C := subgroupAlgebraicGroup D.centralizer
  have hM := torus_multiplicativeType ((isTorus_iff_coordinates C).mp (lattice_torus_of_split hZ))
  have hu : ¬ Specs.Unipotent.IsUnipotent A := fun h =>
    hp (Unipotent.homFromUnipotentToMultiplicativeType A C _ h hM)
  have hgeo : ∃ T : ClosedSubgroup (Specs.GeometricRadicals.GeometricGroup A).val,
      IsTorus T.group ∧ ¬ IsTrivialSubgroup T := by
    by_contra! h
    exact hu (TorusFreeUnipotent.torusFreeUnipotent A hs hc h)
  obtain ⟨T, hT, hN⟩ := NontrivialRationalTorus.existsNontrivialTorus k A hs hc hgeo
  obtain ⟨R, x, hx⟩ := torus_has_infiniteOrder_point T hT hN a ha
  let T_B := subgroupComposite S T
  have hi := projection_closed_on_torus G c D T_B hT
  obtain ⟨r, ⟨e⟩⟩ := hZ
  let I := ULift (Fin r)
  let M := Multiplicative (I → ℤ)
  letI : Group.FG M := inferInstance
  obtain ⟨d⟩ := diagonalIntegerPowers k I
  let j := e ≪≫ d.symm
  haveI : IsIso j.hom.hom.hom.left :=
    ((Grp.forget (SchemeOver k)) ⋙ (Over.forget (Spec (CommRingCat.of k)))).map_isIso j.hom
  letI : IsClosedImmersion (T_B.inclusion ≫ D.limit).hom.hom.left := hi
  let T' : ClosedSubgroup (diagonalGroup k M).val :=
    ⟨T.group, (T_B.inclusion ≫ D.limit) ≫ j.hom,
      inferInstanceAs (IsClosedImmersion ((T_B.inclusion ≫ D.limit).hom.hom.left ≫ j.hom.hom.hom.left))⟩
  obtain ⟨Q, hQ⟩ := splitTorus_of_diagonalizable_infiniteOrder T' R x hx
  exact ⟨subgroupComposite T Q, hQ⟩

end

end SplitTorusProjection

section SmoothNeutralIntersection

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open LinearAlgebraicGroups.Specs LinearAlgebraicGroups.CocharacterDynamics
open Specs.GeometricRadicals (IsSplitTorus)
open Albert.ReductiveFiberSpecification (SplitAction)
open Albert.TrialitySpecification (Model)
open scoped CategoryTheory.MonObj
open private lieMap_closed_injective from LinearAlgebraicGroups.Affine.LieLeftExact
open private reduction_surjective_on_spectra from LinearAlgebraicGroups.Classification.IntegralFibreDatum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 475000

variable {k : Type} [Field k]

private theorem lieMap_open_surjective {H G : GroupScheme k} (i : H ⟶ G)
    (hi : IsOpenImmersion i.hom.hom.left) : Function.Surjective (mapPointKernel i) := by
  letI := hi
  intro v
  let f := i.hom.hom
  let p := v.toMul.val
  let q₀ : Points H.X (CommAlgCat.of k k) := 1
  have h₀ : q₀ ≫ f = 1 := MonObj.one_comp f
  have hsub : Set.range p.left ⊆ Set.range f.left := by
    rintro _ ⟨j, rfl⟩
    obtain ⟨s, rfl⟩ := reduction_surjective_on_spectra k j
    have h₁ := congrArg Over.Hom.left v.toMul.property
    have h₂ := congrArg Over.Hom.left h₀
    refine ⟨q₀.left s, ?_⟩
    exact (congrArg (fun a : _ ⟶ G.X.left => a s) (h₁.trans h₂.symm)).symm
  let q : Points H.X (CommAlgCat.of k (DualNumber k)) :=
    Over.homMk (IsOpenImmersion.lift f.left p.left hsub) (by
      rw [← Over.w f, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w p]
      rfl)
  have hq : q ≫ f = p := Over.OverMorphism.ext (IsOpenImmersion.lift_fac ..)
  have hreduce : mapPoints (dualReduction k) q = 1 := by
    apply Over.OverMorphism.ext
    apply (cancel_mono f.left).mp
    change (mapPoints (dualReduction k) q ≫ f).left = ((1 : Points H.X (CommAlgCat.of k k)) ≫ f).left
    rw [h₀]
    change (mapPoints (dualReduction k) (q ≫ f)).left = _
    rw [hq]
    exact congrArg Over.Hom.left v.toMul.property
  exact ⟨⟨q, hreduce⟩, Subtype.ext hq⟩

private theorem intersectionComponent_limit_nonzero
    (G : AffineAlgebraicGroup k) (A : SplitAction G.val)
    (D : LimitDecomposition (chamberCocharacter A)) (H : ClosedSubgroup G.val)
    (N : ClosedSubgroup (intersectionOverLeft D.parabolic H).group)
    (ho : IsOpenImmersion N.inclusion.hom.hom.left) :
    let V := intersectionOverLeft D.parabolic H
    let W := intersectionOverLeft D.contracting H
    letI : IsAffine V.group.X.left :=
      (subgroupAlgebraicGroup (G := subgroupAlgebraicGroup D.parabolic) V).property.1
    letI : IsAffine W.group.X.left :=
      (subgroupAlgebraicGroup (G := subgroupAlgebraicGroup D.contracting) W).property.1
    Module.finrank k (Lie k V.group) = 5 →
    Module.finrank k (Lie k W.group) ≤ 3 →
      (N.inclusion ≫ V.inclusion) ≫ D.limit ≠ 0 := by
  let V := intersectionOverLeft D.parabolic H
  let W := intersectionOverLeft D.contracting H
  let VA := subgroupAlgebraicGroup (G := subgroupAlgebraicGroup D.parabolic) V
  let WA := subgroupAlgebraicGroup (G := subgroupAlgebraicGroup D.contracting) W
  let NA := subgroupAlgebraicGroup (G := VA) N
  letI : IsAffine G.val.X.left := G.property.1
  letI : IsAffine (intersectionOverLeft D.parabolic H).group.X.left := VA.property.1
  letI : IsAffine (intersectionOverLeft D.contracting H).group.X.left := WA.property.1
  letI : IsAffine V.group.X.left := VA.property.1
  letI : IsAffine W.group.X.left := WA.property.1
  letI : IsAffine N.group.X.left := NA.property.1
  dsimp only
  intro dV dW hzero
  let j := N.inclusion ≫ V.inclusion
  obtain ⟨u, hu⟩ := factor_through_contracting D j hzero
  let t := N.inclusion ≫ pullback.snd D.parabolic.inclusion H.inclusion
  have hcomp : u ≫ D.contracting.inclusion = t ≫ H.inclusion := by
    rw [← D.contracting_in_G, ← Category.assoc, hu, Category.assoc, ← Category.assoc]
    change N.inclusion ≫ (pullback.fst D.parabolic.inclusion H.inclusion ≫
      D.parabolic.inclusion) = _
    rw [pullback.condition, ← Category.assoc]
  let r : N.group ⟶ W.group := pullback.lift u t hcomp
  letI := D.contracting.isClosedImmersion
  letI := W.isClosedImmersion
  letI := V.isClosedImmersion
  letI := N.isClosedImmersion
  letI := D.parabolic.isClosedImmersion
  let q := W.inclusion ≫ D.contracting.inclusion
  letI : IsClosedImmersion q.hom.hom.left :=
    inferInstanceAs (IsClosedImmersion (W.inclusion.hom.hom.left ≫ D.contracting.inclusion.hom.hom.left))
  have he : r ≫ q = j ≫ D.parabolic.inclusion := by
    change r ≫ pullback.fst D.contracting.inclusion H.inclusion ≫ D.contracting.inclusion = _
    rw [← Category.assoc, pullback.lift_fst, ← D.contracting_in_G, ← Category.assoc, hu]
  haveI : IsClosedImmersion (r.hom.hom.left ≫ q.hom.hom.left) := by
    change IsClosedImmersion (r ≫ q).hom.hom.left
    rw [he]
    exact inferInstanceAs (IsClosedImmersion
      ((N.inclusion.hom.hom.left ≫ V.inclusion.hom.hom.left) ≫ D.parabolic.inclusion.hom.hom.left))
  have hr : IsClosedImmersion r.hom.hom.left :=
    IsClosedImmersion.of_comp_isClosedImmersion r.hom.hom.left q.hom.hom.left
  letI : Module.Finite k (Module.End k (Model k)) :=
    Module.Finite.of_injective (matrixToOperator k).symm.toLinearMap (matrixToOperator k).symm.injective
  letI : Module.Finite k (Lie k G.val) :=
    Module.Finite.of_injective (splitActionDifferential G A) (splitActionDifferential_injective G A)
  letI : Module.Finite k (Lie k W.group) :=
    Module.Finite.of_injective (lieMap q) (lieMap_closed_injective q inferInstance)
  let d : Lie k N.group ≃ₗ[k] Lie k V.group := LinearEquiv.ofBijective (lieMap N.inclusion)
    ⟨lieMap_closed_injective N.inclusion N.isClosedImmersion, lieMap_open_surjective N.inclusion ho⟩
  have hd : Module.finrank k (Lie k N.group) ≤ Module.finrank k (Lie k W.group) :=
    LinearMap.finrank_le_finrank_of_injective (f := lieMap r) (lieMap_closed_injective r hr)
  change Module.finrank k (Lie k V.group) = 5 at dV
  change Module.finrank k (Lie k W.group) ≤ 3 at dW
  rw [d.finrank_eq, dV] at hd
  omega

private theorem intersection_contains_splitTorus
    [Infinite k] (G : AffineAlgebraicGroup k) [Smooth G.val.X.hom] (A : SplitAction G.val)
    (D : LimitDecomposition (chamberCocharacter A)) (H : ClosedSubgroup G.val) :
    let V := intersectionOverLeft D.parabolic H
    let W := intersectionOverLeft D.contracting H
    letI : IsAffine V.group.X.left :=
      (subgroupAlgebraicGroup (G := subgroupAlgebraicGroup D.parabolic) V).property.1
    letI : IsAffine W.group.X.left :=
      (subgroupAlgebraicGroup (G := subgroupAlgebraicGroup D.contracting) W).property.1
    Smooth V.group.X.hom → Module.finrank k (Lie k V.group) = 5 →
    Module.finrank k (Lie k W.group) ≤ 3 → IsSplitTorus D.centralizer.group →
    ∀ (a : kˣ), (¬ IsOfFinOrder a) →
    ∃ T : ClosedSubgroup H.group,
      Nonempty (T.group ≅ (StandardGroups.multiplicativePowerGroup k (ULift (Fin 1))).val) := by
  let V := intersectionOverLeft D.parabolic H
  let VA := subgroupAlgebraicGroup (G := subgroupAlgebraicGroup D.parabolic) V
  dsimp only
  intro hs dV dW hZ a ha
  obtain ⟨Q, N, q, i, hN, _, _, _⟩ := identityComponentAndQuotient k VA
  let N' : ClosedSubgroup V.group := ⟨N, i, hN.closedImmersion⟩
  let NC := subgroupComposite V N'
  have hp : NC.inclusion ≫ D.limit ≠ 0 :=
    intersectionComponent_limit_nonzero G A D H N' hN.openImmersion dV dW
  have hc : ConnectedSpace NC.group.X.left := by
    letI := hN.geometricallyConnected
    exact GeometricallyConnected.connectedSpace_of_subsingleton N.X.hom
  have hm : Smooth NC.group.X.hom := by
    letI : IsOpenImmersion i.hom.hom.left := hN.openImmersion
    letI : Smooth VA.val.X.hom := hs
    change Smooth N.X.hom
    rw [← Over.w i.hom.hom]
    infer_instance
  obtain ⟨T, hT⟩ := splitTorus_of_positive_projection G (chamberCocharacter A) D NC hm hc hZ hp a ha
  let VH : ClosedSubgroup H.group := ⟨V.group, pullback.snd D.parabolic.inclusion H.inclusion,
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (((Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))).map_isPullback
        (IsPullback.of_hasPullback D.parabolic.inclusion H.inclusion))) D.parabolic.isClosedImmersion⟩
  exact ⟨subgroupComposite VH (subgroupComposite N' T), hT⟩

end

end SmoothNeutralIntersection

section Isotropy

open AlgebraicGeometry CategoryTheory
open LinearAlgebraicGroups.Specs LinearAlgebraicGroups.CocharacterDynamics
open Albert.ReductiveFiberSpecification (SplitAction)
open scoped CategoryTheory.MonObj
open Albert.IntegralSmoothnessSpecification (algebraicFiber)
open Albert.IntegralSmoothness (geometricFiberAction)
open private conjugate from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 700000

/-- A geometric ordered-frame stabilizer in the split Albert group over a
nonarchimedean local field contains a split torus of rank one. -/
theorem trialitarianIsotropy : TrialitarianSplitTorusSpecification.Statement := by
  intro k _ _ _ _ P G H h
  let K := AlgebraicClosure k
  letI : Infinite k := localField_infinite k
  obtain ⟨S, _⟩ := Albert.AutomorphismType.automorphismType
  let G₀ := algebraicFiber G k
  let A : SplitAction G₀.val := geometricFiberAction G k
  have hG : SmoothOfRelativeDimension 52 G₀.val.X.hom := splitFibre_smoothDimension S G
  letI := hG
  letI : Smooth G₀.val.X.hom := SmoothOfRelativeDimension.smooth 52 _
  obtain ⟨D⟩ := existsLimitDecomposition G₀ (chamberCocharacter A)
  have hZ := (splitFibre_chamberCentralizer S G D).1
  obtain ⟨p, hp⟩ := geometricFrameConjugacy_stabilizer h
  change Points ((groupBaseChange k K).obj G₀.val).X (CommAlgCat.of K K) at p
  obtain ⟨g, hrank, htrans⟩ := exists_rational_translated_frame (K := K) S G p
  let H' := conjugate (rationalSection g) H
  let A' := extendSplitAction (K := K) A
  let E := baseChangePointGroupEquiv K G₀.val (CommAlgCat.of K K)
  let gK := E.symm (mapPoints (scalarPointHom k K) g)
  let v := orbitFrame A' (gK * p)
  have hfix := baseChange_conjugate_fixes_frame (K := K) A H g p
    (fun R x i => ((hp R _).mp ⟨x, rfl⟩) i)
  have hH := geometricFrameConjugate_smoothDimension h
  obtain ⟨hs, dV, dW⟩ := good_frame_intersection G₀ A D H' hG hH v hrank htrans hfix
  obtain ⟨a, ha⟩ := localField_infiniteOrderUnit k
  obtain ⟨T, hT⟩ := intersection_contains_splitTorus G₀ A D H' hs dV dW hZ a ha
  exact ⟨T, 1, Nat.zero_lt_one, hT⟩

end

end Isotropy

end LinearAlgebraicGroups.Arithmetic.TrialitarianSplitTorus
