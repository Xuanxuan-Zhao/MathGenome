import Specs.LinearAlgebraicGroups.Arithmetic.LocalMixingExceptionalRootData
import LinearAlgebraicGroups.Arithmetic.ExceptionalAffineRootSystems
import LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility
import LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitLevis
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.GCDMonoid.Finset

open AlgebraicGeometry CategoryTheory Opposite

universe u
open scoped BigOperators CategoryTheory.MonObj InnerProductSpace Matrix

namespace LinearAlgebraicGroups.Arithmetic.LocalMixingExceptionalRootData

set_option linter.style.haveILetI false

open Specs.Arithmetic.LocalMixingExceptionalRootData
open Specs.ExceptionalAffineRootSystems
  (IsRootCoordinate e6Cartan exceptionalCartan simpleReflection)
open private e6RootTable e6Table_iff from
  LinearAlgebraicGroups.Arithmetic.ExceptionalAffineRootSystems

/-! Finite reflection calculations for the three projections in F12. -/

private theorem exceptionalCartan_six : exceptionalCartan 6 = e6Cartan := by
  decide +kernel

private def reflectionWord {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (word : List (Fin n)) (x : Fin n → ℤ) : Fin n → ℤ :=
  word.foldr (simpleReflection A) x

private theorem reflectionWord_root {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    (word : List (Fin n)) {x : Fin n → ℤ} (h : IsRootCoordinate A x) :
    IsRootCoordinate A (reflectionWord A word x) := by
  induction word with
  | nil => exact h
  | cons i word ih => exact ih.reflect i

/-- The E₇ root table is ordered by closure under the simple reflections,
starting with the seven simple roots. -/
private def e7RootTable : Fin 126 → Fin 7 → ℤ :=
  ![![1, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 1],
    ![-1, 0, 0, 0, 0, 0, 0],
    ![1, 0, 1, 0, 0, 0, 0],
    ![0, -1, 0, 0, 0, 0, 0],
    ![0, 1, 0, 1, 0, 0, 0],
    ![0, 0, -1, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0],
    ![0, 0, 0, -1, 0, 0, 0],
    ![0, 0, 0, 1, 1, 0, 0],
    ![0, 0, 0, 0, -1, 0, 0],
    ![0, 0, 0, 0, 1, 1, 0],
    ![0, 0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, -1],
    ![-1, 0, -1, 0, 0, 0, 0],
    ![1, 0, 1, 1, 0, 0, 0],
    ![0, -1, 0, -1, 0, 0, 0],
    ![0, 1, 1, 1, 0, 0, 0],
    ![0, 1, 0, 1, 1, 0, 0],
    ![0, 0, -1, -1, 0, 0, 0],
    ![0, 0, 1, 1, 1, 0, 0],
    ![0, 0, 0, -1, -1, 0, 0],
    ![0, 0, 0, 1, 1, 1, 0],
    ![0, 0, 0, 0, -1, -1, 0],
    ![0, 0, 0, 0, 1, 1, 1],
    ![0, 0, 0, 0, 0, -1, -1],
    ![-1, 0, -1, -1, 0, 0, 0],
    ![1, 1, 1, 1, 0, 0, 0],
    ![1, 0, 1, 1, 1, 0, 0],
    ![0, -1, -1, -1, 0, 0, 0],
    ![0, -1, 0, -1, -1, 0, 0],
    ![0, 1, 1, 1, 1, 0, 0],
    ![0, 1, 0, 1, 1, 1, 0],
    ![0, 0, -1, -1, -1, 0, 0],
    ![0, 0, 1, 1, 1, 1, 0],
    ![0, 0, 0, -1, -1, -1, 0],
    ![0, 0, 0, 1, 1, 1, 1],
    ![0, 0, 0, 0, -1, -1, -1],
    ![-1, -1, -1, -1, 0, 0, 0],
    ![-1, 0, -1, -1, -1, 0, 0],
    ![1, 1, 1, 1, 1, 0, 0],
    ![1, 0, 1, 1, 1, 1, 0],
    ![0, -1, -1, -1, -1, 0, 0],
    ![0, -1, 0, -1, -1, -1, 0],
    ![0, 1, 1, 2, 1, 0, 0],
    ![0, 1, 1, 1, 1, 1, 0],
    ![0, 1, 0, 1, 1, 1, 1],
    ![0, 0, -1, -1, -1, -1, 0],
    ![0, 0, 1, 1, 1, 1, 1],
    ![0, 0, 0, -1, -1, -1, -1],
    ![-1, -1, -1, -1, -1, 0, 0],
    ![-1, 0, -1, -1, -1, -1, 0],
    ![1, 1, 1, 2, 1, 0, 0],
    ![1, 1, 1, 1, 1, 1, 0],
    ![1, 0, 1, 1, 1, 1, 1],
    ![0, -1, -1, -2, -1, 0, 0],
    ![0, -1, -1, -1, -1, -1, 0],
    ![0, -1, 0, -1, -1, -1, -1],
    ![0, 1, 1, 2, 1, 1, 0],
    ![0, 1, 1, 1, 1, 1, 1],
    ![0, 0, -1, -1, -1, -1, -1],
    ![-1, -1, -1, -2, -1, 0, 0],
    ![-1, -1, -1, -1, -1, -1, 0],
    ![-1, 0, -1, -1, -1, -1, -1],
    ![1, 1, 2, 2, 1, 0, 0],
    ![1, 1, 1, 2, 1, 1, 0],
    ![1, 1, 1, 1, 1, 1, 1],
    ![0, -1, -1, -2, -1, -1, 0],
    ![0, -1, -1, -1, -1, -1, -1],
    ![0, 1, 1, 2, 2, 1, 0],
    ![0, 1, 1, 2, 1, 1, 1],
    ![-1, -1, -2, -2, -1, 0, 0],
    ![-1, -1, -1, -2, -1, -1, 0],
    ![-1, -1, -1, -1, -1, -1, -1],
    ![1, 1, 2, 2, 1, 1, 0],
    ![1, 1, 1, 2, 2, 1, 0],
    ![1, 1, 1, 2, 1, 1, 1],
    ![0, -1, -1, -2, -2, -1, 0],
    ![0, -1, -1, -2, -1, -1, -1],
    ![0, 1, 1, 2, 2, 1, 1],
    ![-1, -1, -2, -2, -1, -1, 0],
    ![-1, -1, -1, -2, -2, -1, 0],
    ![-1, -1, -1, -2, -1, -1, -1],
    ![1, 1, 2, 2, 2, 1, 0],
    ![1, 1, 2, 2, 1, 1, 1],
    ![1, 1, 1, 2, 2, 1, 1],
    ![0, -1, -1, -2, -2, -1, -1],
    ![0, 1, 1, 2, 2, 2, 1],
    ![-1, -1, -2, -2, -2, -1, 0],
    ![-1, -1, -2, -2, -1, -1, -1],
    ![-1, -1, -1, -2, -2, -1, -1],
    ![1, 1, 2, 3, 2, 1, 0],
    ![1, 1, 2, 2, 2, 1, 1],
    ![1, 1, 1, 2, 2, 2, 1],
    ![0, -1, -1, -2, -2, -2, -1],
    ![-1, -1, -2, -3, -2, -1, 0],
    ![-1, -1, -2, -2, -2, -1, -1],
    ![-1, -1, -1, -2, -2, -2, -1],
    ![1, 2, 2, 3, 2, 1, 0],
    ![1, 1, 2, 3, 2, 1, 1],
    ![1, 1, 2, 2, 2, 2, 1],
    ![-1, -2, -2, -3, -2, -1, 0],
    ![-1, -1, -2, -3, -2, -1, -1],
    ![-1, -1, -2, -2, -2, -2, -1],
    ![1, 2, 2, 3, 2, 1, 1],
    ![1, 1, 2, 3, 2, 2, 1],
    ![-1, -2, -2, -3, -2, -1, -1],
    ![-1, -1, -2, -3, -2, -2, -1],
    ![1, 2, 2, 3, 2, 2, 1],
    ![1, 1, 2, 3, 3, 2, 1],
    ![-1, -2, -2, -3, -2, -2, -1],
    ![-1, -1, -2, -3, -3, -2, -1],
    ![1, 2, 2, 3, 3, 2, 1],
    ![-1, -2, -2, -3, -3, -2, -1],
    ![1, 2, 2, 4, 3, 2, 1],
    ![-1, -2, -2, -4, -3, -2, -1],
    ![1, 2, 3, 4, 3, 2, 1],
    ![-1, -2, -3, -4, -3, -2, -1],
    ![2, 2, 3, 4, 3, 2, 1],
    ![-2, -2, -3, -4, -3, -2, -1]]

private def e7ReflectionIndex (i : Fin 7) : Fin 126 → Fin 126 :=
  (![![7, 1, 8, 3, 4, 5, 6, 0, 2, 9, 10, 20, 21, 13, 14, 15, 16, 17, 18, 19,
      11, 12, 22, 33, 24, 32, 34, 27, 28, 29, 30, 31, 25, 23, 26, 44, 36, 46, 38, 45,
      47, 41, 42, 43, 35, 39, 37, 40, 56, 49, 58, 59, 52, 57, 60, 55, 48, 53, 50, 51,
      54, 67, 68, 63, 71, 72, 69, 61, 62, 66, 70, 64, 65, 78, 79, 81, 82, 77, 73, 74,
      80, 75, 76, 87, 88, 91, 86, 83, 84, 89, 90, 85, 96, 99, 94, 95, 92, 97, 98, 93,
      103, 101, 102, 100, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119,
      120, 121, 124, 125, 122, 123],
    ![0, 9, 2, 10, 4, 5, 6, 7, 8, 1, 3, 11, 23, 22, 24, 15, 16, 17, 18, 19,
      20, 33, 13, 12, 14, 35, 37, 36, 38, 29, 30, 31, 44, 21, 46, 25, 27, 26, 28, 48,
      51, 49, 52, 43, 32, 56, 34, 59, 39, 41, 50, 40, 42, 62, 65, 63, 45, 68, 58, 47,
      72, 61, 53, 55, 64, 54, 74, 67, 57, 79, 70, 71, 60, 73, 66, 75, 76, 77, 78, 69,
      80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 104, 98, 99,
      100, 107, 102, 103, 97, 110, 106, 101, 112, 109, 105, 114, 108, 116, 111, 118, 113, 119, 115, 117,
      120, 121, 122, 123, 124, 125],
    ![8, 1, 11, 12, 4, 5, 6, 20, 0, 9, 23, 2, 3, 25, 26, 15, 16, 17, 18, 19,
      7, 21, 35, 10, 37, 13, 14, 39, 40, 29, 30, 31, 32, 33, 34, 22, 48, 24, 51, 27,
      28, 53, 54, 43, 44, 45, 46, 47, 36, 62, 50, 38, 65, 41, 42, 66, 56, 57, 70, 59,
      60, 61, 49, 74, 64, 52, 55, 77, 68, 69, 58, 80, 72, 73, 63, 75, 76, 67, 86, 79,
      71, 89, 90, 83, 84, 85, 78, 94, 95, 81, 82, 98, 92, 93, 87, 88, 102, 97, 91, 106,
      100, 101, 96, 109, 104, 105, 99, 107, 108, 103, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119,
      122, 123, 120, 121, 124, 125],
    ![0, 10, 12, 13, 14, 5, 6, 7, 21, 22, 1, 25, 2, 3, 4, 27, 28, 17, 18, 19,
      32, 8, 9, 23, 24, 11, 26, 15, 16, 41, 42, 31, 20, 33, 34, 35, 36, 50, 38, 39,
      40, 29, 30, 55, 44, 45, 58, 47, 61, 49, 37, 64, 52, 53, 54, 43, 67, 57, 46, 71,
      60, 48, 73, 63, 51, 76, 66, 56, 78, 69, 70, 59, 82, 62, 84, 75, 65, 77, 68, 88,
      80, 81, 72, 83, 74, 85, 86, 87, 79, 97, 90, 91, 92, 93, 101, 95, 96, 89, 105, 99,
      100, 94, 108, 103, 104, 98, 111, 107, 102, 113, 110, 106, 112, 109, 114, 115, 116, 117, 120, 121,
      118, 119, 122, 123, 124, 125],
    ![0, 1, 2, 14, 15, 16, 6, 7, 8, 9, 24, 11, 26, 27, 3, 4, 5, 29, 30, 19,
      20, 34, 36, 37, 10, 39, 12, 13, 28, 17, 18, 43, 45, 46, 21, 48, 22, 23, 38, 25,
      40, 41, 42, 31, 56, 32, 33, 47, 35, 49, 50, 51, 52, 53, 54, 55, 44, 57, 58, 59,
      60, 61, 62, 63, 75, 65, 66, 67, 68, 69, 70, 81, 72, 83, 74, 64, 85, 77, 87, 79,
      89, 71, 91, 73, 92, 76, 94, 78, 96, 80, 98, 82, 84, 93, 86, 102, 88, 97, 90, 99,
      100, 101, 95, 103, 104, 105, 106, 107, 108, 109, 110, 115, 112, 117, 118, 111, 119, 113, 114, 116,
      120, 121, 122, 123, 124, 125],
    ![0, 1, 2, 3, 16, 17, 18, 7, 8, 9, 10, 11, 12, 13, 28, 29, 4, 5, 6, 31,
      20, 21, 22, 23, 38, 25, 40, 41, 14, 15, 30, 19, 32, 33, 47, 35, 49, 51, 24, 53,
      26, 27, 42, 43, 44, 57, 59, 34, 62, 36, 64, 37, 52, 39, 54, 55, 68, 45, 71, 46,
      60, 73, 48, 63, 50, 65, 66, 78, 56, 69, 80, 58, 72, 61, 74, 75, 76, 86, 67, 79,
      70, 81, 82, 83, 84, 93, 77, 87, 88, 89, 90, 99, 100, 85, 94, 95, 103, 97, 106, 91,
      92, 101, 109, 96, 104, 111, 98, 107, 113, 102, 114, 105, 116, 108, 110, 115, 112, 117, 118, 119,
      120, 121, 122, 123, 124, 125],
    ![0, 1, 2, 3, 4, 18, 19, 7, 8, 9, 10, 11, 12, 13, 14, 15, 30, 31, 5, 6,
      20, 21, 22, 23, 24, 25, 26, 27, 42, 43, 16, 17, 32, 33, 34, 35, 36, 37, 52, 39,
      54, 55, 28, 29, 44, 45, 46, 60, 48, 63, 50, 65, 38, 66, 40, 41, 56, 69, 58, 72,
      47, 61, 74, 49, 76, 51, 53, 67, 79, 57, 70, 82, 59, 84, 62, 85, 64, 77, 88, 68,
      90, 91, 71, 92, 73, 75, 95, 96, 78, 98, 80, 81, 83, 93, 102, 86, 87, 105, 89, 99,
      100, 108, 94, 103, 110, 97, 106, 112, 101, 109, 104, 111, 107, 113, 114, 115, 116, 117, 118, 119,
      120, 121, 122, 123, 124, 125]]) i
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem e7RootTable_reflect : ∀ (i : Fin 7) (k : Fin 126),
    simpleReflection (exceptionalCartan 7) i (e7RootTable k) =
      e7RootTable (e7ReflectionIndex i k) := by
  decide +kernel

private def e7RootWord : Fin 126 → Fin 7 × List (Fin 7) :=
  ![(0, []),
    (1, []),
    (2, []),
    (3, []),
    (4, []),
    (5, []),
    (6, []),
    (0, [0]),
    (0, [2]),
    (1, [1]),
    (1, [3]),
    (2, [2]),
    (2, [3]),
    (3, [3]),
    (3, [4]),
    (4, [4]),
    (4, [5]),
    (5, [5]),
    (5, [6]),
    (6, [6]),
    (0, [2, 0]),
    (0, [3, 2]),
    (1, [3, 1]),
    (1, [2, 3]),
    (1, [4, 3]),
    (2, [3, 2]),
    (2, [4, 3]),
    (3, [4, 3]),
    (3, [5, 4]),
    (4, [5, 4]),
    (4, [6, 5]),
    (5, [6, 5]),
    (0, [3, 2, 0]),
    (0, [1, 3, 2]),
    (0, [4, 3, 2]),
    (1, [2, 3, 1]),
    (1, [4, 3, 1]),
    (1, [4, 2, 3]),
    (1, [5, 4, 3]),
    (2, [4, 3, 2]),
    (2, [5, 4, 3]),
    (3, [5, 4, 3]),
    (3, [6, 5, 4]),
    (4, [6, 5, 4]),
    (0, [1, 3, 2, 0]),
    (0, [4, 3, 2, 0]),
    (0, [4, 1, 3, 2]),
    (0, [5, 4, 3, 2]),
    (1, [4, 2, 3, 1]),
    (1, [5, 4, 3, 1]),
    (1, [3, 4, 2, 3]),
    (1, [5, 4, 2, 3]),
    (1, [6, 5, 4, 3]),
    (2, [5, 4, 3, 2]),
    (2, [6, 5, 4, 3]),
    (3, [6, 5, 4, 3]),
    (0, [4, 1, 3, 2, 0]),
    (0, [5, 4, 3, 2, 0]),
    (0, [3, 4, 1, 3, 2]),
    (0, [5, 4, 1, 3, 2]),
    (0, [6, 5, 4, 3, 2]),
    (1, [3, 4, 2, 3, 1]),
    (1, [5, 4, 2, 3, 1]),
    (1, [6, 5, 4, 3, 1]),
    (1, [5, 3, 4, 2, 3]),
    (1, [6, 5, 4, 2, 3]),
    (2, [6, 5, 4, 3, 2]),
    (0, [3, 4, 1, 3, 2, 0]),
    (0, [5, 4, 1, 3, 2, 0]),
    (0, [6, 5, 4, 3, 2, 0]),
    (0, [2, 3, 4, 1, 3, 2]),
    (0, [5, 3, 4, 1, 3, 2]),
    (0, [6, 5, 4, 1, 3, 2]),
    (1, [5, 3, 4, 2, 3, 1]),
    (1, [6, 5, 4, 2, 3, 1]),
    (1, [4, 5, 3, 4, 2, 3]),
    (1, [6, 5, 3, 4, 2, 3]),
    (0, [2, 3, 4, 1, 3, 2, 0]),
    (0, [5, 3, 4, 1, 3, 2, 0]),
    (0, [6, 5, 4, 1, 3, 2, 0]),
    (0, [5, 2, 3, 4, 1, 3, 2]),
    (0, [4, 5, 3, 4, 1, 3, 2]),
    (0, [6, 5, 3, 4, 1, 3, 2]),
    (1, [4, 5, 3, 4, 2, 3, 1]),
    (1, [6, 5, 3, 4, 2, 3, 1]),
    (1, [6, 4, 5, 3, 4, 2, 3]),
    (0, [5, 2, 3, 4, 1, 3, 2, 0]),
    (0, [4, 5, 3, 4, 1, 3, 2, 0]),
    (0, [6, 5, 3, 4, 1, 3, 2, 0]),
    (0, [4, 5, 2, 3, 4, 1, 3, 2]),
    (0, [6, 5, 2, 3, 4, 1, 3, 2]),
    (0, [6, 4, 5, 3, 4, 1, 3, 2]),
    (1, [6, 4, 5, 3, 4, 2, 3, 1]),
    (1, [5, 6, 4, 5, 3, 4, 2, 3]),
    (0, [4, 5, 2, 3, 4, 1, 3, 2, 0]),
    (0, [6, 5, 2, 3, 4, 1, 3, 2, 0]),
    (0, [6, 4, 5, 3, 4, 1, 3, 2, 0]),
    (0, [3, 4, 5, 2, 3, 4, 1, 3, 2]),
    (0, [6, 4, 5, 2, 3, 4, 1, 3, 2]),
    (0, [5, 6, 4, 5, 3, 4, 1, 3, 2]),
    (1, [5, 6, 4, 5, 3, 4, 2, 3, 1]),
    (0, [3, 4, 5, 2, 3, 4, 1, 3, 2, 0]),
    (0, [6, 4, 5, 2, 3, 4, 1, 3, 2, 0]),
    (0, [5, 6, 4, 5, 3, 4, 1, 3, 2, 0]),
    (0, [1, 3, 4, 5, 2, 3, 4, 1, 3, 2]),
    (0, [6, 3, 4, 5, 2, 3, 4, 1, 3, 2]),
    (0, [5, 6, 4, 5, 2, 3, 4, 1, 3, 2]),
    (0, [1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]),
    (0, [6, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]),
    (0, [5, 6, 4, 5, 2, 3, 4, 1, 3, 2, 0]),
    (0, [6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2]),
    (0, [5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2]),
    (0, [6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]),
    (0, [5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]),
    (0, [5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2]),
    (0, [4, 5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2]),
    (0, [5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]),
    (0, [4, 5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]),
    (0, [4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2]),
    (0, [4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]),
    (0, [3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2]),
    (0, [3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]),
    (0, [2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2]),
    (0, [2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]),
    (0, [0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2]),
    (0, [0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0])]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem e7RootTable_word : ∀ k : Fin 126,
    e7RootTable k = reflectionWord (exceptionalCartan 7) (e7RootWord k).2
      (Pi.single (e7RootWord k).1 1) := by
  decide +kernel

private theorem e7RootTable_iff (r : Fin 7 → ℤ) :
    IsRootCoordinate (exceptionalCartan 7) r ↔ r ∈ Set.range e7RootTable := by
  constructor
  · intro hr
    induction hr with
    | simple i =>
      refine ⟨i.castLE (by decide), ?_⟩
      fin_cases i <;> decide
    | reflect h i ih =>
      obtain ⟨k, rfl⟩ := ih
      exact ⟨e7ReflectionIndex i k, (e7RootTable_reflect i k).symm⟩
  · rintro ⟨k, rfl⟩
    rw [e7RootTable_word]
    exact reflectionWord_root _ (.simple _)

-- Rows record the pairing against each projected simple coroot.
private def g2Cartan : Matrix (Fin 2) (Fin 2) ℤ :=
  !![2, -1; -3, 2]

private def g2Roots : Fin 12 → Fin 2 → ℤ :=
  ![![1, 0],
    ![0, 1],
    ![-1, 0],
    ![1, 3],
    ![1, 1],
    ![0, -1],
    ![-1, -3],
    ![2, 3],
    ![1, 2],
    ![-1, -1],
    ![-2, -3],
    ![-1, -2]]

private def g2RootWord : Fin 12 → Fin 2 × List (Fin 2) :=
  ![(0, []),
    (1, []),
    (0, [0]),
    (0, [1]),
    (1, [0]),
    (1, [1]),
    (0, [1, 0]),
    (0, [0, 1]),
    (1, [1, 0]),
    (1, [0, 1]),
    (0, [0, 1, 0]),
    (1, [1, 0, 1])]

private def g2ReflectionIndex (i : Fin 2) : Fin 12 → Fin 12 :=
  (![![2, 4, 0, 7, 1, 9, 10, 3, 8, 5, 6, 11],
    ![3, 5, 6, 0, 8, 1, 2, 7, 4, 11, 10, 9]]) i

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem g2Roots_reflect : ∀ (i : Fin 2) (k : Fin 12),
    simpleReflection g2Cartan i (g2Roots k) =
      g2Roots (g2ReflectionIndex i k) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem g2Roots_word : ∀ k : Fin 12,
    g2Roots k = reflectionWord g2Cartan (g2RootWord k).2
      (Pi.single (g2RootWord k).1 1) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem g2Roots_gcd : ∀ k : Fin 12,
    Finset.univ.gcd (fun i ↦ (g2Roots k i).natAbs) = 1 := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem g2Roots_nonzero : ∀ k : Fin 12, g2Roots k ≠ 0 := by
  decide +kernel

-- The common simple Cartan matrix of the two rank-four projections.
private def f4Cartan : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, -1, 0, 0; -1, 2, -1, 0; 0, -2, 2, -1; 0, 0, -1, 2]

private def f4Roots : Fin 48 → Fin 4 → ℤ :=
  ![![1, 0, 0, 0],
    ![0, 1, 0, 0],
    ![0, 0, 1, 0],
    ![0, 0, 0, 1],
    ![-1, 0, 0, 0],
    ![1, 1, 0, 0],
    ![0, -1, 0, 0],
    ![0, 1, 2, 0],
    ![0, 1, 1, 0],
    ![0, 0, -1, 0],
    ![0, 0, 1, 1],
    ![0, 0, 0, -1],
    ![-1, -1, 0, 0],
    ![1, 1, 2, 0],
    ![0, -1, -2, 0],
    ![0, 1, 2, 2],
    ![1, 1, 1, 0],
    ![0, 1, 1, 1],
    ![0, -1, -1, 0],
    ![0, 0, -1, -1],
    ![-1, -1, -2, 0],
    ![1, 2, 2, 0],
    ![1, 1, 2, 2],
    ![0, -1, -2, -2],
    ![1, 1, 1, 1],
    ![0, 1, 2, 1],
    ![-1, -1, -1, 0],
    ![0, -1, -1, -1],
    ![-1, -2, -2, 0],
    ![-1, -1, -2, -2],
    ![1, 2, 2, 2],
    ![1, 1, 2, 1],
    ![-1, -1, -1, -1],
    ![0, -1, -2, -1],
    ![-1, -2, -2, -2],
    ![1, 2, 4, 2],
    ![1, 2, 2, 1],
    ![-1, -1, -2, -1],
    ![-1, -2, -4, -2],
    ![1, 3, 4, 2],
    ![1, 2, 3, 1],
    ![-1, -2, -2, -1],
    ![-1, -3, -4, -2],
    ![2, 3, 4, 2],
    ![1, 2, 3, 2],
    ![-1, -2, -3, -1],
    ![-2, -3, -4, -2],
    ![-1, -2, -3, -2]]

private def f4RootWord : Fin 48 → Fin 4 × List (Fin 4) :=
  ![(0, []),
    (1, []),
    (2, []),
    (3, []),
    (0, [0]),
    (0, [1]),
    (1, [1]),
    (1, [2]),
    (2, [1]),
    (2, [2]),
    (2, [3]),
    (3, [3]),
    (0, [1, 0]),
    (0, [2, 1]),
    (1, [2, 1]),
    (1, [3, 2]),
    (2, [0, 1]),
    (2, [3, 1]),
    (2, [1, 2]),
    (2, [3, 2]),
    (0, [2, 1, 0]),
    (0, [1, 2, 1]),
    (0, [3, 2, 1]),
    (1, [3, 2, 1]),
    (2, [3, 0, 1]),
    (2, [2, 3, 1]),
    (2, [0, 1, 2]),
    (2, [3, 1, 2]),
    (0, [1, 2, 1, 0]),
    (0, [3, 2, 1, 0]),
    (0, [3, 1, 2, 1]),
    (2, [2, 3, 0, 1]),
    (2, [3, 0, 1, 2]),
    (2, [2, 3, 1, 2]),
    (0, [3, 1, 2, 1, 0]),
    (0, [2, 3, 1, 2, 1]),
    (2, [1, 2, 3, 0, 1]),
    (2, [2, 3, 0, 1, 2]),
    (0, [2, 3, 1, 2, 1, 0]),
    (0, [1, 2, 3, 1, 2, 1]),
    (2, [2, 1, 2, 3, 0, 1]),
    (2, [1, 2, 3, 0, 1, 2]),
    (0, [1, 2, 3, 1, 2, 1, 0]),
    (0, [0, 1, 2, 3, 1, 2, 1]),
    (2, [3, 2, 1, 2, 3, 0, 1]),
    (2, [2, 1, 2, 3, 0, 1, 2]),
    (0, [0, 1, 2, 3, 1, 2, 1, 0]),
    (2, [3, 2, 1, 2, 3, 0, 1, 2])]

private def f4ReflectionIndex (i : Fin 4) : Fin 48 → Fin 48 :=
  (![![4, 5, 2, 3, 0, 1, 12, 13, 16, 9, 10, 11, 6, 7, 20, 22, 8, 24, 26, 19,
      14, 21, 15, 29, 17, 31, 18, 32, 28, 23, 30, 25, 27, 37, 34, 35, 36, 33, 38, 43,
      40, 41, 46, 39, 44, 45, 42, 47],
    ![5, 6, 8, 3, 12, 0, 1, 7, 2, 18, 17, 11, 4, 21, 14, 15, 16, 10, 9, 27,
      28, 13, 30, 23, 24, 25, 26, 19, 20, 34, 22, 36, 32, 33, 29, 39, 31, 41, 42, 35,
      40, 37, 38, 43, 44, 45, 46, 47],
    ![0, 7, 9, 10, 4, 13, 14, 1, 8, 2, 3, 19, 20, 5, 6, 15, 16, 25, 18, 11,
      12, 21, 22, 23, 31, 17, 26, 33, 28, 29, 35, 24, 37, 27, 38, 30, 40, 32, 34, 39,
      36, 45, 42, 43, 44, 41, 46, 47],
    ![0, 1, 10, 11, 4, 5, 6, 15, 17, 19, 2, 3, 12, 22, 23, 7, 24, 8, 27, 9,
      29, 30, 13, 14, 16, 25, 32, 18, 34, 20, 21, 31, 26, 33, 28, 35, 36, 37, 38, 39,
      44, 41, 42, 43, 40, 47, 46, 45]]) i

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem f4Roots_reflect : ∀ (i : Fin 4) (k : Fin 48),
    simpleReflection f4Cartan i (f4Roots k) =
      f4Roots (f4ReflectionIndex i k) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem f4Roots_word : ∀ k : Fin 48,
    f4Roots k = reflectionWord f4Cartan (f4RootWord k).2
      (Pi.single (f4RootWord k).1 1) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem f4Roots_gcd : ∀ k : Fin 48,
    Finset.univ.gcd (fun i ↦ (f4Roots k i).natAbs) = 1 := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem f4Roots_nonzero : ∀ k : Fin 48, f4Roots k ≠ 0 := by
  decide +kernel

private def innerE6ProjectionIndex : Fin 72 → Fin 13 :=
  ![1, 2, 0, 0, 0, 0, 3, 5, 6, 2, 2, 0, 0, 2, 0, 0, 0, 0, 10, 5,
      6, 2, 5, 2, 6, 0, 5, 2, 6, 0, 10, 9, 5, 6, 5, 2, 10, 6, 5, 2,
      10, 6, 12, 10, 9, 5, 10, 6, 5, 10, 6, 12, 9, 9, 10, 9, 10, 12, 4, 9,
      12, 9, 12, 7, 8, 9, 12, 9, 12, 11, 12, 12]

private def innerE6ProjectionLift : Fin 12 → Fin 72 :=
  ![0, 1, 6, 58, 7, 8, 63, 64, 31, 18, 69, 42]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem innerE6_projection : ∀ k : Fin 72,
    (Projection.innerE6).project (e6RootTable k) =
      Fin.cases 0 g2Roots (innerE6ProjectionIndex k) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem innerE6_projectionLift : ∀ k : Fin 12,
    (Projection.innerE6).project (e6RootTable (innerE6ProjectionLift k)) = g2Roots k := by
  decide +kernel

private def innerE7ProjectionIndex : Fin 126 → Fin 49 :=
  ![1, 0, 2, 3, 0, 4, 0, 5, 6, 0, 3, 7, 9, 10, 3, 0, 4, 12, 4, 0,
      13, 17, 10, 9, 3, 19, 9, 10, 11, 12, 4, 12, 27, 17, 17, 19, 10, 9, 11, 19,
      18, 20, 11, 12, 27, 27, 17, 25, 19, 20, 8, 18, 11, 28, 18, 20, 27, 33, 14, 25,
      25, 15, 28, 20, 26, 18, 28, 21, 33, 33, 22, 32, 25, 34, 28, 26, 26, 29, 38, 33,
      37, 32, 32, 34, 34, 26, 42, 38, 38, 37, 37, 32, 34, 16, 42, 42, 38, 41, 37, 23,
      24, 46, 42, 30, 41, 41, 31, 46, 46, 35, 41, 45, 46, 48, 45, 45, 48, 48, 45, 48,
      36, 39, 40, 43, 44, 47]

private def innerE7ProjectionLift : Fin 48 → Fin 126 :=
  ![0, 2, 3, 5, 7, 8, 11, 50, 12, 13, 28, 17, 20, 58, 61, 93, 21, 40, 25, 41,
      67, 70, 99, 100, 47, 64, 32, 53, 77, 103, 106, 71, 57, 73, 109, 120, 80, 78, 121, 122,
      97, 86, 123, 124, 111, 101, 125, 113]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem innerE7_projection : ∀ k : Fin 126,
    (Projection.innerE7).project (e7RootTable k) =
      Fin.cases 0 f4Roots (innerE7ProjectionIndex k) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem innerE7_projectionLift : ∀ k : Fin 48,
    (Projection.innerE7).project (e7RootTable (innerE7ProjectionLift k)) = f4Roots k := by
  decide +kernel

private def outerE6ProjectionIndex : Fin 72 → Fin 49 :=
  ![1, 2, 3, 3, 4, 4, 5, 6, 7, 8, 9, 10, 11, 9, 10, 11, 12, 12, 13, 14,
      15, 16, 17, 18, 19, 20, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 25, 26,
      27, 28, 29, 30, 31, 32, 33, 34, 32, 33, 34, 35, 36, 37, 38, 37, 38, 39, 40, 41,
      42, 41, 42, 43, 44, 45, 46, 45, 46, 47, 48, 48]

private def outerE6ProjectionLift : Fin 48 → Fin 72 :=
  ![0, 1, 2, 4, 6, 7, 8, 9, 10, 11, 12, 16, 18, 19, 20, 21, 22, 23, 24, 25,
      30, 31, 32, 33, 34, 35, 36, 37, 42, 43, 44, 45, 46, 47, 51, 52, 53, 54, 57, 58,
      59, 60, 63, 64, 65, 66, 69, 70]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem outerE6_projection : ∀ k : Fin 72,
    (Projection.outerE6).project (e6RootTable k) =
      Fin.cases 0 f4Roots (outerE6ProjectionIndex k) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem outerE6_projectionLift : ∀ k : Fin 48,
    (Projection.outerE6).project (e6RootTable (outerE6ProjectionLift k)) = f4Roots k := by
  decide +kernel


private def projectedRoots {n m : ℕ} (p : Projection n m) : Set (Fin m → ℤ) :=
  {v | v ≠ 0 ∧ ∃ r, IsRootCoordinate (exceptionalCartan n) r ∧ p.project r = v}

private theorem projectedRoots_eq_range {n m N L : ℕ} (p : Projection n m)
    (absolute : Fin N → Fin n → ℤ) (proj : Fin L → Fin m → ℤ)
    (ha : ∀ r, IsRootCoordinate (exceptionalCartan n) r ↔ r ∈ Set.range absolute)
    (idx : Fin N → Fin (L + 1)) (lift : Fin L → Fin N)
    (hidx : ∀ k, p.project (absolute k) = Fin.cases 0 proj (idx k))
    (hlift : ∀ l, p.project (absolute (lift l)) = proj l)
    (hnz : ∀ l, proj l ≠ 0) :
    projectedRoots p = Set.range proj := by
  ext v
  constructor
  · rintro ⟨hn, r, hr, rfl⟩
    obtain ⟨k, rfl⟩ := (ha r).mp hr
    rw [hidx k] at hn ⊢
    generalize idx k = j at hn ⊢
    cases j using Fin.cases with
    | zero => exact False.elim (hn rfl)
    | succ l => exact ⟨l, rfl⟩
  · rintro ⟨l, rfl⟩
    exact ⟨hnz l, absolute (lift l), (ha _).mpr ⟨lift l, rfl⟩, hlift l⟩

private theorem e6RootTable_iff (r : Fin 6 → ℤ) :
    IsRootCoordinate (exceptionalCartan 6) r ↔ r ∈ Set.range e6RootTable := by
  rw [exceptionalCartan_six]
  exact e6Table_iff r

private theorem projectedRoots_innerE6 : projectedRoots Projection.innerE6 = Set.range g2Roots :=
  projectedRoots_eq_range _ _ _ e6RootTable_iff _ _ innerE6_projection
    innerE6_projectionLift g2Roots_nonzero

private theorem projectedRoots_innerE7 : projectedRoots Projection.innerE7 = Set.range f4Roots :=
  projectedRoots_eq_range _ _ _ e7RootTable_iff _ _ innerE7_projection
    innerE7_projectionLift f4Roots_nonzero

private theorem projectedRoots_outerE6 : projectedRoots Projection.outerE6 = Set.range f4Roots :=
  projectedRoots_eq_range _ _ _ e6RootTable_iff _ _ outerE6_projection
    outerE6_projectionLift f4Roots_nonzero

private theorem primitive_projectedRoot {n m : ℕ} {p : Projection n m}
    {x : Fin m → ℤ} (hx : x ∈ projectedRoots p) :
    Finset.univ.gcd (fun i ↦ (x i).natAbs) = 1 := by
  cases p with
  | innerE6 =>
    rw [projectedRoots_innerE6] at hx
    obtain ⟨j, rfl⟩ := hx
    exact g2Roots_gcd j
  | innerE7 =>
    rw [projectedRoots_innerE7] at hx
    obtain ⟨j, rfl⟩ := hx
    exact f4Roots_gcd j
  | outerE6 =>
    rw [projectedRoots_outerE6] at hx
    obtain ⟨j, rfl⟩ := hx
    exact f4Roots_gcd j

private theorem eq_or_eq_neg_of_smul_eq {d : ℕ} {x y : Fin d → ℤ}
    (hx : Finset.univ.gcd (fun i ↦ (x i).natAbs) = 1)
    (hy : Finset.univ.gcd (fun i ↦ (y i).natAbs) = 1)
    {a b : ℤ} (ha : a ≠ 0) (hab : a • x = b • y) :
    y = x ∨ y = -x := by
  have hcoord : ∀ i, a * x i = b * y i := fun i ↦ congrFun hab i
  have hg : ∀ (c : ℤ) (z : Fin d → ℤ),
      Finset.univ.gcd (fun i ↦ (c * z i).natAbs) =
        c.natAbs * Finset.univ.gcd (fun i ↦ (z i).natAbs) := by
    intro c z
    simp only [Int.natAbs_mul, Finset.gcd_mul_left, normalize_eq]
  have h1 := congrArg (Finset.univ.gcd) (funext fun i ↦ congrArg Int.natAbs (hcoord i))
  rw [hg, hg, hx, hy, mul_one, mul_one] at h1
  rcases Int.natAbs_eq_natAbs_iff.mp h1 with h | h
  · left
    funext i
    have h' := hcoord i
    rw [← h] at h'
    exact (mul_left_cancel₀ ha h').symm
  · right
    funext i
    have h' := hcoord i
    rw [show b = -a by rw [h, neg_neg], neg_mul, ← mul_neg] at h'
    change y i = -x i
    have hh := mul_left_cancel₀ ha h'
    omega

open Specs.CharacterDescent (Character)
open Specs.Relative.RelativeChambers (relativeRoots)
open Specs.RootGroups (Proportional)

section Marked

variable {F : Type*} [Field F] {G : AffineAlgebraicGroup F} {S : ClosedSubgroup G.val}
  {n m : ℕ} {p : Projection n m} (M : MarkedTorus S p)

private def encode (v : Fin m → ℤ) : Character S.group :=
  M.encode (Multiplicative.ofAdd v)

private theorem encode_injective : Function.Injective (encode M) :=
  M.encode_injective.comp Multiplicative.ofAdd.injective

private theorem encode_sub_zsmul (x y : Fin m → ℤ) (k : ℤ) :
    encode M (x - k • y) = encode M x * encode M y ^ (-k) := by
  simp only [encode, ofAdd_sub, ofAdd_zsmul, map_mul, map_inv, map_zpow, div_eq_mul_inv, zpow_neg]

private theorem encode_mem_iff (x : Fin m → ℤ) :
    encode M x ∈ relativeRoots S ↔ x ∈ projectedRoots p := by
  rw [M.relativeRoots_eq]
  constructor
  · rintro ⟨⟨r, hr⟩, hn, he⟩
    have he' : p.project r = x := encode_injective M he
    exact ⟨he' ▸ hn, r, hr, he'⟩
  · rintro ⟨hn, r, hr, rfl⟩
    exact ⟨⟨r, hr⟩, hn, rfl⟩

private theorem relativeRoot_lift (a : relativeRoots S) :
    ∃ x ∈ projectedRoots p, encode M x = a.val := by
  let b : Character S.group := a.val
  have ha : b ∈ relativeRoots S := a.property
  rw [M.relativeRoots_eq] at ha
  obtain ⟨⟨r, hr⟩, hn, he⟩ := ha
  exact ⟨p.project r, ⟨hn, r, hr, rfl⟩, he⟩

include M in
private theorem markedRelativeRoots_reduced :
    ∀ a b : relativeRoots S, Proportional a.val b.val → b.val = a.val ∨ b.val = a.val⁻¹ := by
  intro a b ⟨ma, mb, hma, _, hab⟩
  obtain ⟨x, hx, ex⟩ := relativeRoot_lift M a
  obtain ⟨y, hy, ey⟩ := relativeRoot_lift M b
  rw [← ex, ← ey] at hab ⊢
  have hxy : ma • x = mb • y := by
    apply encode_injective M
    simpa only [encode, ofAdd_zsmul, map_zpow] using hab
  rcases eq_or_eq_neg_of_smul_eq (primitive_projectedRoot hx) (primitive_projectedRoot hy)
      hma hxy with h | h
  · exact Or.inl (congrArg (encode M) h)
  · right
    rw [h]
    exact map_inv M.encode (Multiplicative.ofAdd x)

end Marked


private theorem g2SimpleLengths (l : Fin 2 → ℝ) (hl : ∀ i, 0 ≤ l i)
    (h : ∀ i j, (g2Cartan i j : ℝ) * l i = (g2Cartan j i : ℝ) * l j) :
    ∀ i, l i ≤ l 0 := by
  have h01 := h 0 1
  norm_num [g2Cartan] at h01
  intro i
  fin_cases i
  · rfl
  · change l 1 ≤ l 0
    linarith [hl 1]

private theorem f4SimpleLengths (l : Fin 4 → ℝ) (hl : ∀ i, 0 ≤ l i)
    (h : ∀ i j, (f4Cartan i j : ℝ) * l i = (f4Cartan j i : ℝ) * l j) :
    (∀ i, l i ≤ l 0) ∧ ∀ i, l i ≤ l 1 := by
  have h01 := h 0 1
  have h12 := h 1 2
  have h23 := h 2 3
  norm_num [f4Cartan] at h01 h12 h23
  have hle : l 2 ≤ l 1 := by linarith [hl 2]
  have h₀ : ∀ i, l i ≤ l 0 := by
    intro i
    fin_cases i
    · exact le_rfl
    · change l 1 ≤ l 0
      linarith
    · change l 2 ≤ l 0
      linarith
    · change l 3 ≤ l 0
      linarith
  exact ⟨h₀, fun i ↦ h01 ▸ h₀ i⟩

/-- Simple reflections and length comparisons computed in projected coordinates. -/
private structure ProjectedSystem {n m : ℕ} (p : Projection n m) where
  cartan : Matrix (Fin m) (Fin m) ℤ
  diagonal : ∀ i, cartan i i = 2
  finite : (projectedRoots p).Finite
  simple : ∀ i : Fin m, Pi.single i 1 ∈ projectedRoots p
  reflect : ∀ (i : Fin m) x, x ∈ projectedRoots p →
    simpleReflection cartan i x ∈ projectedRoots p
  word : ∀ x ∈ projectedRoots p, ∃ (i : Fin m) (w : List (Fin m)),
    x = reflectionWord cartan w (Pi.single i 1)
  selected : Fin m
  selected_eq : p.project (Pi.single p.selectedIndex 1) = Pi.single selected 1
  longest : ∀ l : Fin m → ℝ, (∀ i, 0 ≤ l i) →
    (∀ i j, (cartan i j : ℝ) * l i = (cartan j i : ℝ) * l j) →
    ∀ i, l i ≤ l selected

private def projectedSystem {n m : ℕ} (p : Projection n m) : ProjectedSystem p := by
  cases p with
  | innerE6 =>
    refine ⟨g2Cartan, by decide, ?_, ?_, ?_, ?_, 0, by decide, g2SimpleLengths⟩
    · rw [projectedRoots_innerE6]
      exact Set.finite_range _
    · intro i
      rw [projectedRoots_innerE6]
      exact ⟨i.castLE (by decide), by fin_cases i <;> decide⟩
    · intro i x hx
      rw [projectedRoots_innerE6] at hx ⊢
      obtain ⟨k, rfl⟩ := hx
      exact ⟨g2ReflectionIndex i k, (g2Roots_reflect i k).symm⟩
    · intro x hx
      rw [projectedRoots_innerE6] at hx
      obtain ⟨k, rfl⟩ := hx
      exact ⟨(g2RootWord k).1, (g2RootWord k).2, g2Roots_word k⟩
  | innerE7 =>
    refine ⟨f4Cartan, by decide, ?_, ?_, ?_, ?_, 1, by decide,
      fun l hl h ↦ (f4SimpleLengths l hl h).2⟩
    · rw [projectedRoots_innerE7]
      exact Set.finite_range _
    · intro i
      rw [projectedRoots_innerE7]
      exact ⟨i.castLE (by decide), by fin_cases i <;> decide⟩
    · intro i x hx
      rw [projectedRoots_innerE7] at hx ⊢
      obtain ⟨k, rfl⟩ := hx
      exact ⟨f4ReflectionIndex i k, (f4Roots_reflect i k).symm⟩
    · intro x hx
      rw [projectedRoots_innerE7] at hx
      obtain ⟨k, rfl⟩ := hx
      exact ⟨(f4RootWord k).1, (f4RootWord k).2, f4Roots_word k⟩
  | outerE6 =>
    refine ⟨f4Cartan, by decide, ?_, ?_, ?_, ?_, 0, by decide,
      fun l hl h ↦ (f4SimpleLengths l hl h).1⟩
    · rw [projectedRoots_outerE6]
      exact Set.finite_range _
    · intro i
      rw [projectedRoots_outerE6]
      exact ⟨i.castLE (by decide), by fin_cases i <;> decide⟩
    · intro i x hx
      rw [projectedRoots_outerE6] at hx ⊢
      obtain ⟨k, rfl⟩ := hx
      exact ⟨f4ReflectionIndex i k, (f4Roots_reflect i k).symm⟩
    · intro x hx
      rw [projectedRoots_outerE6] at hx
      obtain ⟨k, rfl⟩ := hx
      exact ⟨(f4RootWord k).1, (f4RootWord k).2, f4Roots_word k⟩

private theorem cartan_mulVec_single {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ)
    (i j : Fin m) : A.mulVec (Pi.single j 1) i = A i j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- Two linear reflections along the same line preserving a finite set
agree on that set. Their composite translates along the line with a constant
step on each parallel line. -/
private theorem reflectionCoefficient_unique {m : ℕ} (R : Set (Fin m → ℤ))
    (hR : R.Finite) (i : Fin m) (a b : (Fin m → ℤ) →ₗ[ℤ] ℤ)
    (ha : a (Pi.single i 1) = 2) (hb : b (Pi.single i 1) = 2)
    (hA : ∀ x ∈ R, x - a x • Pi.single i 1 ∈ R)
    (hB : ∀ x ∈ R, x - b x • Pi.single i 1 ∈ R)
    {x : Fin m → ℤ} (hx : x ∈ R) : a x = b x := by
  let e : Fin m → ℤ := Pi.single i 1
  change a e = 2 at ha
  change b e = 2 at hb
  let d := a x - b x
  have shift (z : Fin m → ℤ) (hz : z ∈ R) :
      z + (a z - b z) • e ∈ R := by
    have hh := hB _ (hA z hz)
    change z - a z • e - b (z - a z • e) • e ∈ R at hh
    have hc : z - a z • e - b (z - a z • e) • e = z + (a z - b z) • e := by
      rw [map_sub, map_smul, hb]
      rw [← sub_add_eq_sub_sub, ← add_smul]
      rw [sub_eq_add_neg, ← neg_smul]
      congr 2
      ring
    rwa [hc] at hh
  have hiter (k : ℕ) : x + ((k : ℤ) * d) • e ∈ R := by
    induction k with
    | zero => simpa using hx
    | succ k hk =>
      have h := shift _ hk
      have hstep : a (x + ((k : ℤ) * d) • e) - b (x + ((k : ℤ) * d) • e) = d := by
        rw [map_add, map_add, map_smul, map_smul, ha, hb]
        dsimp [d]
        ring
      simpa only [hstep, add_assoc, ← add_smul, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using h
  by_contra h
  letI := hR.to_subtype
  let f : ℕ → R := fun k ↦ ⟨x + ((k : ℤ) * d) • e, hiter k⟩
  have hf : Function.Injective f := by
    intro s t hst
    have hi := congrArg (fun z : R ↦ z.val i) hst
    change x i + (((s : ℤ) * d) • e) i = x i + (((t : ℤ) * d) • e) i at hi
    simp only [e, Pi.smul_apply, Pi.single_eq_same, zsmul_eq_mul, mul_one] at hi
    exact_mod_cast mul_right_cancel₀ (sub_ne_zero.mpr h) (add_left_cancel hi)
  letI := Finite.of_injective f hf
  exact not_finite ℕ

open Specs.Arithmetic.RelativeRootIrreducibility (RealRootSpan realRoot)
open Specs.CharacterPairing (pairing)
open Specs.Relative.RelativeReflections (Datum)
open Specs.Relative.RelativeWeylScheme (QuotientData)
open private relativeForm relative_cartan relativeAction relativeAction_root
  relative_inner_invariant realRoot_ne_zero reductive_of_semisimple from
  LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility

noncomputable section

section Length

variable {F : Type u} [Field F] {G : AffineAlgebraicGroup F} {S : ClosedSubgroup G.val}
  {n m : ℕ} {p : Projection n m} (M : MarkedTorus S p)
  {D : QuotientData S} [IsCommMonObj S.group.X] (d : Datum D)

private def encodedRoot (x : Fin m → ℤ) (hx : x ∈ projectedRoots p) : relativeRoots S :=
  ⟨encode M x, (encode_mem_iff M x).mpr hx⟩

private def simpleRoot (Q : ProjectedSystem p) (i : Fin m) : relativeRoots S :=
  encodedRoot M (Pi.single i 1) (Q.simple i)

private def pairingFunctional (c : Specs.CharacterDescent.Cocharacter S.group) :
    (Fin m → ℤ) →ₗ[ℤ] ℤ :=
  (d.rootDatum.toLinearMap.flip (Additive.ofMul c)).comp
    M.encode.toAdditive.toIntLinearMap

private theorem pairingFunctional_apply (c : Specs.CharacterDescent.Cocharacter S.group)
    (x : Fin m → ℤ) :
    pairingFunctional M d c x = pairing S.group (encode M x) c :=
  d.pairing_eq _ _

private theorem model_pairing (Q : ProjectedSystem p) (i : Fin m)
    {x : Fin m → ℤ} (hx : x ∈ projectedRoots p) :
    Q.cartan.mulVec x i = pairing S.group (encode M x) (d.reflection (simpleRoot M Q i)).coroot := by
  let a : (Fin m → ℤ) →ₗ[ℤ] ℤ := (LinearMap.proj i).comp Q.cartan.mulVecLin
  let r := simpleRoot M Q i
  let c := (d.reflection r).coroot
  let b := pairingFunctional M d c
  change a x = pairing S.group (encode M x) c
  rw [← pairingFunctional_apply M d]
  change a x = b x
  apply reflectionCoefficient_unique _ Q.finite i a b _ _ _ _ hx
  · change Q.cartan.mulVec (Pi.single i 1) i = 2
    rw [cartan_mulVec_single, Q.diagonal]
  · rw [show b (Pi.single i 1) = pairing S.group r.val c from pairingFunctional_apply M d _ _]
    exact (d.reflection r).rootPairing
  · exact Q.reflect i
  · intro y hy
    apply (encode_mem_iff M _).mp
    rw [encode_sub_zsmul, show b y = pairing S.group (encode M y) c from
      pairingFunctional_apply M d _ _]
    have hroot := (d.normalizerPerm (d.reflection r).label (encodedRoot M y hy)).property
    have he := d.rootAction (d.reflection r).label (encodedRoot M y hy)
    rw [(d.reflection r).characterFormula] at he
    exact he ▸ hroot

attribute [local instance] InnerProductSpace.Core.toNormedAddCommGroup

private theorem model_reflection_root (Q : ProjectedSystem p) (i : Fin m)
    (x : Fin m → ℤ) (hx : x ∈ projectedRoots p) :
    encodedRoot M (simpleReflection Q.cartan i x) (Q.reflect i x hx) =
      d.normalizerPerm (d.reflection (simpleRoot M Q i)).label (encodedRoot M x hx) := by
  apply Subtype.ext
  rw [d.rootAction, (d.reflection (simpleRoot M Q i)).characterFormula]
  change encode M (x - (Q.cartan.mulVec x i) • Pi.single i 1) = _
  rw [encode_sub_zsmul, model_pairing M d Q i hx]
  rfl

private theorem inner_reflectionWord (Q : ProjectedSystem p) (w : List (Fin m))
    (x : Fin m → ℤ) (hx : x ∈ projectedRoots p) :
    letI := relativeForm d
    letI := InnerProductSpace.ofCore (relativeForm d).toCore
    ∃ hw : reflectionWord Q.cartan w x ∈ projectedRoots p,
      inner ℝ (realRoot (encodedRoot M (reflectionWord Q.cartan w x) hw))
        (realRoot (encodedRoot M (reflectionWord Q.cartan w x) hw)) =
      inner ℝ (realRoot (encodedRoot M x hx)) (realRoot (encodedRoot M x hx)) := by
  letI := relativeForm d
  letI := InnerProductSpace.ofCore (relativeForm d).toCore
  induction w with
  | nil => exact ⟨hx, rfl⟩
  | cons i w ih =>
    obtain ⟨hw, he⟩ := ih
    let y := reflectionWord Q.cartan w x
    refine ⟨Q.reflect i y hw, ?_⟩
    change inner ℝ (realRoot (encodedRoot M (simpleReflection Q.cartan i y) _))
      (realRoot (encodedRoot M (simpleReflection Q.cartan i y) _)) = _
    rw [model_reflection_root M d Q i y hw, ← relativeAction_root d, relative_inner_invariant d]
    exact he

omit [IsCommMonObj S.group.X] in
private theorem markedRoot_isLongest (hRed : Specs.GeometricRadicals.IsReductive G) :
    IsLongest S M.selected := by
  obtain ⟨D, _⟩ := Relative.RelativeWeylScheme.finiteConstantQuotient G hRed S M.maximalSplit
  obtain ⟨comm, ⟨d⟩⟩ :=
    Relative.RelativeReflections.relativeRootDatum G hRed S M.maximalSplit D
  letI := comm
  letI := relativeForm d
  letI := InnerProductSpace.ofCore (relativeForm d).toCore
  let Q := projectedSystem p
  refine ⟨D, comm, d, relativeForm d, fun b r ↦ relative_cartan d r b, ?_⟩
  let l (i : Fin m) : ℝ := inner ℝ (realRoot (simpleRoot M Q i)) (realRoot (simpleRoot M Q i))
  have hpos (i : Fin m) : 0 ≤ l i := real_inner_self_nonneg
  have hCartan (i j : Fin m) :
      (Q.cartan i j : ℝ) * l i = 2 * inner ℝ (realRoot (simpleRoot M Q j))
        (realRoot (simpleRoot M Q i)) := by
    have hh := relative_cartan d (simpleRoot M Q i) (simpleRoot M Q j)
    have hp := model_pairing M d Q i (Q.simple j)
    rw [cartan_mulVec_single] at hp
    change _ = pairing S.group (simpleRoot M Q j).val _ at hp
    rw [← hp] at hh
    change 2 * inner ℝ _ _ / l i = _ at hh
    haveI := d.freeCharacters
    have hne : l i ≠ 0 := inner_self_ne_zero.mpr (realRoot_ne_zero _)
    exact ((div_eq_iff hne).mp hh).symm
  have hsymm (i j : Fin m) : (Q.cartan i j : ℝ) * l i = (Q.cartan j i : ℝ) * l j := by
    rw [hCartan, hCartan, real_inner_comm]
  have hs : simpleRoot M Q Q.selected = M.selected := by
    apply Subtype.ext
    change encode M (Pi.single Q.selected 1) = M.selected.val
    rw [M.selected_eq, ← Q.selected_eq]
    rfl
  intro b
  obtain ⟨x, hx, he⟩ := relativeRoot_lift M b
  have hb : encodedRoot M x hx = b := Subtype.ext he
  obtain ⟨i, w, rfl⟩ := Q.word x hx
  obtain ⟨_, hw⟩ := inner_reflectionWord M d Q w _ (Q.simple i)
  rw [hb] at hw
  have hle := Q.longest l hpos hsymm i
  change inner ℝ (realRoot (simpleRoot M Q i)) (realRoot (simpleRoot M Q i)) ≤
    inner ℝ (realRoot (simpleRoot M Q Q.selected)) (realRoot (simpleRoot M Q Q.selected)) at hle
  change _ = l i at hw
  change l i ≤ inner ℝ (realRoot (simpleRoot M Q Q.selected)) _ at hle
  rw [hs, ← hw, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hle
  nlinarith [norm_nonneg (realRoot b), norm_nonneg (realRoot M.selected)]

end Length


section Transport

open Specs.CharacterPairing (absoluteRoots)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus)
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open private map_weightVector differential_injective from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private charactersOfIso from LinearAlgebraicGroups.RootData.CharacterPairing
open private innerIso innerMap comp_innerMap from LinearAlgebraicGroups.Reductive.BorelProper
open private transportSubgroup from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private geometricallyMaximalOfIso from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitLevis

variable {F : Type u} [Field F]

private theorem rootsAlongIso_forward {G H : GroupScheme F}
    {S : ClosedSubgroup G} {T : ClosedSubgroup H} (f : G ≅ H) (e : S.group ≅ T.group)
    (he : e.hom ≫ T.inclusion = S.inclusion ≫ f.hom)
    {χ : Character S.group} (hχ : χ ∈ absoluteRoots S) :
    charactersOfIso e χ ∈ absoluteRoots T := by
  obtain ⟨hne, v, hv, hvne⟩ := hχ
  haveI : IsIso f.hom.hom.hom := (Grp.forget (SchemeOver F)).map_isIso f.hom
  refine ⟨fun h ↦ hne ((charactersOfIso e).injective (h.trans (map_one _).symm)), ?_⟩
  have hpre : e.hom ≫ charactersOfIso e χ = χ := by
    change e.hom ≫ e.inv ≫ χ = χ
    simp
  have hv' : v ∈ Specs.CharacterPairing.adjointWeightVectors S (e.hom ≫ charactersOfIso e χ) := by
    rwa [hpre]
  refine ⟨mapPointKernel f.hom v, map_weightVector f.hom e he.symm hv', ?_⟩
  intro h
  apply hvne
  apply differential_injective f.hom
  change mapPointKernel f.hom v = mapPointKernel f.hom 0
  rw [h]
  apply Subtype.ext
  symm
  change (1 : _ ⟶ G.X) ≫ f.hom.hom.hom = (1 : _ ⟶ H.X)
  exact MonObj.one_comp _

private theorem rootsAlongIso {G H : GroupScheme F}
    {S : ClosedSubgroup G} {T : ClosedSubgroup H} (f : G ≅ H) (e : S.group ≅ T.group)
    (he : e.hom ≫ T.inclusion = S.inclusion ≫ f.hom) (χ : Character S.group) :
    charactersOfIso e χ ∈ absoluteRoots T ↔ χ ∈ absoluteRoots S := by
  constructor
  · intro hχ
    have hi : e.inv ≫ S.inclusion = T.inclusion ≫ f.inv := by
      rw [← cancel_mono f.hom, Category.assoc, Category.assoc, f.inv_hom_id, Category.comp_id,
        ← he, Iso.inv_hom_id_assoc]
    have h := rootsAlongIso_forward f.symm e.symm hi hχ
    change (e.hom ≫ (e.inv ≫ χ)) ∈ absoluteRoots S at h
    simpa using h
  · exact rootsAlongIso_forward f e he

private def transportMarked {G : AffineAlgebraicGroup F}
    {S₀ S : ClosedSubgroup G.val} {n m : ℕ} {p : Projection n m}
    (M : MarkedTorus S₀ p) (hS : IsMaximalSplitTorus S)
    (f : G.val ≅ G.val) (e : S₀.group ≅ S.group)
    (he : e.hom ≫ S.inclusion = S₀.inclusion ≫ f.hom) : MarkedTorus S p := by
  let E := groupBaseChange F (SeparableClosure F)
  let T := transportSubgroup f M.torus
  let i : S.group ⟶ T.group := e.inv ≫ M.inclusion
  let fe := charactersOfIso e
  have mem (a : Character S₀.group) : fe a ∈ relativeRoots S ↔ a ∈ relativeRoots S₀ :=
    rootsAlongIso f e he a
  refine {
    maximalSplit := hS
    torus := T
    isTorus := M.isTorus
    isMaximal := geometricallyMaximalOfIso f M.torus T (Iso.refl _) (Category.id_comp _) M.isMaximal
    inclusion := i
    inclusion_comp := ?_
    pair := M.pair
    datum := M.datum
    groupIso := M.groupIso ≪≫ E.mapIso f
    torusIso := M.torusIso
    inclusions_commute := ?_
    multiplicative := M.multiplicative
    preservesUnits := M.preservesUnits
    numbering := M.numbering
    cartan_eq := M.cartan_eq
    coordinates := M.coordinates
    coordinates_eq := M.coordinates_eq
    encode := fe.toMonoidHom.comp M.encode
    encode_injective := fe.injective.comp M.encode_injective
    restriction_eq := ?_
    relativeRoots_eq := ?_
    selected := ⟨fe M.selected.val, (mem _).mpr M.selected.property⟩
    selected_eq := congrArg fe M.selected_eq
    orthogonal := M.orthogonal
    singleton := ?_ }
  · change (e.inv ≫ M.inclusion) ≫ M.torus.inclusion ≫ f.hom = S.inclusion
    rw [Category.assoc, ← Category.assoc M.inclusion, M.inclusion_comp, ← he,
      Iso.inv_hom_id_assoc]
  · change M.pair.T.inclusion ≫ M.groupIso.hom ≫ E.map f.hom =
      M.torusIso.hom ≫ E.map (M.torus.inclusion ≫ f.hom)
    rw [← Category.assoc, M.inclusions_commute, Functor.map_comp, Category.assoc]
  · intro b
    change E.map (e.inv ≫ M.inclusion) ≫ M.torusIso.inv ≫ b.val =
      E.map (e.inv ≫ M.encode _) ≫ M.multiplicative.inv
    simp only [Functor.map_comp, Category.assoc]
    exact congrArg (E.map e.inv ≫ ·) (M.restriction_eq b)
  · ext b
    obtain ⟨a, rfl⟩ := fe.surjective b
    rw [mem, M.relativeRoots_eq]
    constructor
    · rintro ⟨v, hv, heq⟩
      exact ⟨v, hv, congrArg fe heq⟩
    · rintro ⟨v, hv, heq⟩
      exact ⟨v, hv, fe.injective heq⟩
  · have comp_iff (b : Specs.AbstractPairing.Root M.pair.T) :
        E.map (e.inv ≫ M.inclusion) ≫ M.torusIso.inv ≫ b.val =
          E.map (e.inv ≫ M.selected.val) ≫ M.multiplicative.inv ↔
        E.map M.inclusion ≫ M.torusIso.inv ≫ b.val =
          E.map M.selected.val ≫ M.multiplicative.inv := by
      simp only [Functor.map_comp, Category.assoc]
      exact cancel_epi (E.map e.inv)
    obtain ⟨b, hb, hu⟩ := M.singleton
    exact ⟨b, (comp_iff b).mpr hb, fun c hc ↦ hu c ((comp_iff c).mp hc)⟩

end Transport


section FiniteSplitting

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

open Specs.CharacterPairing (absoluteRoots)
open Specs.GeometricRadicals (IsReductive IsMaximalTorus IsTorus IsSplitTorus IsSplitReductive
  baseChangedSubgroup)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open Specs.QuasiSplitOrbitLevis (MultiplicativeComparison PreservesUnits)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CocharacterDynamics (cocharacterPoint unitPoint)
open private extendSubgroup subgroupOf_of_extend cocharacter_ext_units from
  LinearAlgebraicGroups.RootData.RankOneFlag
open private maximal_of_square isTorus_iff_coordinates transportSubgroup from
  LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private torus_after_algClosed_extension from LinearAlgebraicGroups.Reductive.MaximalToriExist
open private inverseBaseChangeIso splitTorus_baseChange from
  LinearAlgebraicGroups.RootData.BorelsAndChambers
open private groupBaseChangeTowerIso multiplicativeBaseChange multiplicativeBaseChange_tower
  multiplicativeBaseChange_unit from LinearAlgebraicGroups.Relative.RationalCocharacter
open private extendedGroupIso from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private finiteGaloisSplitsTorus from LinearAlgebraicGroups.Relative.RationalDensity
open private charactersOfIso from LinearAlgebraicGroups.RootData.CharacterPairing

private theorem maximalTorus_ringEquiv {L M : Type u} [Field L] [Field M] [Algebra L M]
    [IsAlgClosed L] [IsAlgClosed M] (e : L ≃+* M) (he : ∀ x, algebraMap L M x = e x)
    (H : AffineAlgebraicGroup L) (T : ClosedSubgroup H.val) (hT : IsMaximalTorus T) :
    IsMaximalTorus (extendSubgroup M T) := by
  letI : Algebra M L := e.symm.toRingHom.toAlgebra
  let B := groupBaseChange L M
  let R := groupBaseChange M L
  have hback (x : L) : algebraMap M L (algebraMap L M x) = x := by
    rw [he]
    exact e.symm_apply_apply x
  let q := inverseBaseChangeIso hback
  let qH := q.app H.val
  let qT := q.app T.group
  have hinc : R.map (B.map T.inclusion) ≫ qH.hom = qT.hom ≫ T.inclusion :=
    q.hom.naturality T.inclusion
  refine ⟨?_, ?_⟩
  · exact torus_after_algClosed_extension M (closedSubgroupAlgebraicGroup (G := H) T) hT.1
  · intro U hU hTU
    obtain ⟨j, hj⟩ := hTU
    change j ≫ U.inclusion = B.map T.inclusion at hj
    let U' := transportSubgroup qH (extendSubgroup L U)
    have hU' : IsTorus U'.group :=
      torus_after_algClosed_extension L
        (closedSubgroupAlgebraicGroup (G := baseChangedAlgebraicGroup M H) U) hU
    have hTU' : IsSubgroupOf T U' := ⟨qT.inv ≫ R.map j, by
      change (qT.inv ≫ R.map j) ≫ R.map U.inclusion ≫ qH.hom = T.inclusion
      rw [Category.assoc, ← Functor.map_comp_assoc, hj, hinc, Iso.inv_hom_id_assoc]⟩
    obtain ⟨g, hg⟩ := hT.2 U' hU' hTU'
    apply subgroupOf_of_extend (K := L)
    refine ⟨g ≫ qT.inv, ?_⟩
    apply (cancel_mono qH.hom).mp
    change ((g ≫ qT.inv) ≫ R.map (B.map T.inclusion)) ≫ qH.hom =
      R.map U.inclusion ≫ qH.hom
    simp only [Category.assoc]
    rw [hinc, Iso.inv_hom_id_assoc]
    exact hg

private theorem maximalTorus_finiteBaseChange {F K : Type u} [Field F] [Field K]
    [Algebra F K] [FiniteDimensional F K] {G : AffineAlgebraicGroup F}
    (T : ClosedSubgroup G.val) (h : IsGeometricallyMaximal T) :
    IsGeometricallyMaximal (extendSubgroup K T) := by
  let L := AlgebraicClosure F
  let M := AlgebraicClosure K
  let e : L ≃ₐ[F] M := IsAlgClosure.equiv F L M
  letI : Algebra L M := e.toAlgHom.toRingHom.toAlgebra
  letI : IsScalarTower F L M := IsScalarTower.of_algebraMap_eq' e.toAlgHom.comp_algebraMap.symm
  let t := groupBaseChangeTowerIso (k := F) (K := L) (L := M) ≪≫
    (groupBaseChangeTowerIso (k := F) (K := K) (L := M)).symm
  obtain ⟨hc, hm⟩ := h
  let U := baseChangedSubgroup L T hc
  let V := extendSubgroup M U
  let W := extendSubgroup M (extendSubgroup K T)
  have hV : IsMaximalTorus V := maximalTorus_ringEquiv e.toRingEquiv (fun _ ↦ rfl) (baseChangedAlgebraicGroup L G) U hm
  refine ⟨W.isClosedImmersion, maximal_of_square (t.app G.val) V W (t.app T.group) ?_ hV⟩
  exact (t.hom.naturality T.inclusion).symm

private theorem finiteSplitsTorus {F : Type u} [Field F] {G : AffineAlgebraicGroup F}
    (T : ClosedSubgroup G.val) (h : IsTorus T.group) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra F K) (_ : FiniteDimensional F K)
      (_ : IsGalois F K), IsSplitTorus ((groupBaseChange F K).obj T.group) := by
  obtain ⟨A, ⟨i⟩, hA⟩ := (isTorus_iff_coordinates (closedSubgroupAlgebraicGroup T)).mp h
  obtain ⟨K, _, _, _, _, r, ⟨j⟩⟩ := finiteGaloisSplitsTorus hA
  obtain ⟨s⟩ := CharacterDescent.standardSplitTorus (k := K) r
  let e := extendedGroupIso K A ≪≫ (groupBaseChange F K).mapIso i
  refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, r, ⟨?_⟩⟩
  exact e.symm ≪≫ (hopfSpec (CommRingCat.of K)).mapIso j.op ≪≫ s

private theorem canonicalMultiplicativeComparison {F K : Type u} [Field F] [Field K] [Algebra F K]
    (e : MultiplicativeComparison F K) (he : PreservesUnits e) :
    e = multiplicativeBaseChange F K := by
  apply Iso.ext
  apply cocharacter_ext_units
  intro R s
  apply (baseChangePoints F K _ R).1
  exact (he R s).trans (multiplicativeBaseChange_unit K R s).symm

set_option maxHeartbeats 1200000 in
private theorem markedRoot_hasFiniteFibre {F : Type u} [Field F] {G : AffineAlgebraicGroup F}
    {S : ClosedSubgroup G.val} {n m : ℕ} {p : Projection n m}
    (M : MarkedTorus S p) (hG : IsReductive G) : HasSingleAbsoluteRoot S M.selected.val := by
  let J := SeparableClosure F
  obtain ⟨K, _, _, _, _, hTK⟩ := finiteSplitsTorus M.torus M.isTorus
  let a : K →ₐ[F] J := IsSepClosed.lift
  letI : Algebra K J := a.toRingHom.toAlgebra
  letI : IsScalarTower F K J := IsScalarTower.of_algebraMap_eq' a.comp_algebraMap.symm
  let E := groupBaseChange F K
  let D := groupBaseChange K J
  let C := groupBaseChange F J
  let TK := extendSubgroup K M.torus
  let TJ := extendSubgroup J TK
  let X := extendSubgroup J M.torus
  let q := groupBaseChangeTowerIso (k := F) (K := K) (L := J)
  let t := q.app M.torus.group
  let s := q.app S.group
  let v := q.app (specGroup (groupAlgebra F IntegerCharacters))
  let e := multiplicativeBaseChange F K
  let f := multiplicativeBaseChange K J
  let w := multiplicativeBaseChange F J
  obtain ⟨eK, heK, _, hKroots⟩ :=
    Relative.RelativeChambers.relativeRootsByRestriction G S M.torus M.inclusion
      M.inclusion_comp M.maximalSplit.1 TK.isClosedImmersion hTK
  rw [canonicalMultiplicativeComparison eK heK] at hKroots
  change (fun a : Character S.group ↦ E.map a ≫ e.inv) '' relativeRoots S =
    ((fun b : Character TK.group ↦ E.map M.inclusion ≫ b) '' absoluteRoots TK) \ {1} at hKroots
  have aK_mem : E.map M.selected.val ≫ e.inv ∈
      ((fun b : Character TK.group ↦ E.map M.inclusion ≫ b) '' absoluteRoots TK) \ {1} := by
    rw [← hKroots]
    exact Set.mem_image_of_mem _ M.selected.property
  obtain ⟨⟨b, hb, hba⟩, _⟩ := aK_mem
  have hKred := (Reductive.RadicalBaseChange.reductiveFieldExtension (K := K) G hG.1 hG.2.1).mpr hG
  refine ⟨M.torus, M.inclusion, M.isTorus, M.isMaximal, M.inclusion_comp,
    K, inferInstance, inferInstance, inferInstance, inferInstance,
    TK.isClosedImmersion, e, ⟨hKred, TK, hTK, maximalTorus_finiteBaseChange M.torus M.isMaximal⟩,
    hTK, multiplicativeBaseChange_unit K, b, ⟨hb, hba⟩, ?_⟩
  obtain ⟨fJ, hfJ, hinj, hJroots⟩ :=
    Relative.RelativeChambers.relativeRootsByRestriction (baseChangedAlgebraicGroup K G)
      TK TK (𝟙 TK.group) (Category.id_comp _) hTK TJ.isClosedImmersion
      (splitTorus_baseChange hTK)
  rw [canonicalMultiplicativeComparison fJ hfJ] at hJroots hinj
  change (fun z : Character TK.group ↦ D.map z ≫ f.inv) '' absoluteRoots TK =
    ((fun z : Character TJ.group ↦ D.map (𝟙 TK.group) ≫ z) '' absoluteRoots TJ) \ {1} at hJroots
  have root_J (z : Character TK.group) (hz : z ∈ absoluteRoots TK) :
      D.map z ≫ f.inv ∈ absoluteRoots TJ := by
    have hz' : D.map z ≫ f.inv ∈
        (fun z : Character TK.group ↦ D.map z ≫ f.inv) '' absoluteRoots TK :=
      Set.mem_image_of_mem _ hz
    rw [hJroots] at hz'
    obtain ⟨⟨y, hy, heq⟩, _⟩ := hz'
    change D.map (𝟙 TK.group) ≫ y = D.map z ≫ f.inv at heq
    rw [D.map_id TK.group, Category.id_comp] at heq
    exact heq ▸ hy
  have positiveSquare : t.hom ≫ X.inclusion = TJ.inclusion ≫ (q.app G.val).hom :=
    (q.hom.naturality M.torus.inclusion).symm
  have inverseSquare : M.torusIso.hom ≫ X.inclusion = M.pair.T.inclusion ≫ M.groupIso.hom :=
    M.inclusions_commute.symm
  let iso := t ≪≫ M.torusIso.symm
  have hsquare : iso.hom ≫ M.pair.T.inclusion =
      TJ.inclusion ≫ ((q.app G.val) ≪≫ M.groupIso.symm).hom := by
    apply (cancel_mono M.groupIso.hom).mp
    simp only [iso, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    rw [← inverseSquare, Iso.inv_hom_id_assoc]
    exact positiveSquare
  have eComp : f.hom ≫ D.map e.hom ≫ v.hom = w.hom :=
    multiplicativeBaseChange_tower (k := F) (K := K) (L := J)
  have eInvComp : v.inv ≫ D.map e.inv ≫ f.inv = w.inv := by
    have h : f ≪≫ (D.mapIso e ≪≫ v) = w := Iso.ext eComp
    simpa only [Iso.trans_inv, Functor.mapIso_inv, Category.assoc] using congrArg Iso.inv h
  have lift_in_fibre (z : Character TK.group) (hz : z ∈ absoluteRoots TK)
      (hza : E.map M.inclusion ≫ z = E.map M.selected.val ≫ e.inv) :
      ∃ b' : Specs.AbstractPairing.Root M.pair.T,
        b'.val = iso.inv ≫ D.map z ≫ f.inv ∧
        C.map M.inclusion ≫ M.torusIso.inv ≫ b'.val =
          C.map M.selected.val ≫ M.multiplicative.inv := by
    have hz' := rootsAlongIso_forward ((q.app G.val) ≪≫ M.groupIso.symm) iso hsquare (root_J z hz)
    refine ⟨⟨charactersOfIso iso (D.map z ≫ f.inv), hz'⟩, rfl, ?_⟩
    rw [canonicalMultiplicativeComparison M.multiplicative M.preservesUnits]
    change C.map M.inclusion ≫ M.torusIso.inv ≫
        M.torusIso.hom ≫ t.inv ≫ D.map z ≫ f.inv = C.map M.selected.val ≫ w.inv
    rw [Iso.inv_hom_id_assoc]
    have hi : C.map M.inclusion ≫ t.inv = s.inv ≫ D.map (E.map M.inclusion) :=
      q.inv.naturality M.inclusion
    have ha : s.inv ≫ D.map (E.map M.selected.val) = C.map M.selected.val ≫ v.inv :=
      (q.inv.naturality M.selected.val).symm
    rw [← Category.assoc (C.map M.inclusion), hi, Category.assoc,
      ← Functor.map_comp_assoc, hza, D.map_comp]
    simp only [Category.assoc]
    rw [← Category.assoc s.inv, ha]
    simp only [Category.assoc, eInvComp]
  intro d hd
  obtain ⟨db, hdb, hdmem⟩ := lift_in_fibre d hd.1 hd.2
  obtain ⟨bb, hbb, hbmem⟩ := lift_in_fibre b hb hba
  obtain ⟨c, _, hc⟩ := M.singleton
  have h := congrArg Subtype.val ((hc db hdmem).trans (hc bb hbmem).symm)
  rw [hdb, hbb] at h
  exact hinj ((cancel_epi iso.inv).mp h)

end FiniteSplitting

open private innerIso innerMap comp_innerMap from LinearAlgebraicGroups.Reductive.BorelProper

theorem exceptionalRootData :
    Specs.Arithmetic.LocalMixingExceptionalRootData.ExceptionalRootData := by
  intro F _ _ _ _ G hG _ S hS S₀ n m p M₀
  have hRed := reductive_of_semisimple G hG.1
  obtain ⟨g, e, he⟩ :=
    Relative.MaximalSplitTori.maximalSplitToriConjugate G hRed S₀ S M₀.maximalSplit hS
  have hcommute : e.hom ≫ S.inclusion = S₀.inclusion ≫ (innerIso g).hom := by
    apply Grp.hom_ext
    change (e.hom ≫ S.inclusion).hom.hom =
      S₀.inclusion.hom.hom ≫ (innerMap g).hom.hom
    rw [comp_innerMap]
    exact he
  let M := transportMarked M₀ hS (innerIso g) e hcommute
  exact ⟨markedRelativeRoots_reduced M, M.selected, markedRoot_isLongest M hRed,
    markedRoot_hasFiniteFibre M hRed⟩

end

end LinearAlgebraicGroups.Arithmetic.LocalMixingExceptionalRootData
