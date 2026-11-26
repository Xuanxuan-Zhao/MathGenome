import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRadicalGeneration
import LinearAlgebraicGroups.Arithmetic.ExceptionalAffineRootSystems
import LinearAlgebraicGroups.Relative.RelativeChambers
import LinearAlgebraicGroups.Arithmetic.QuasiSplitLocalGeneration
import LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedPairModel
import LinearAlgebraicGroups.Descent.RelativeRank
import LinearAlgebraicGroups.Arithmetic.ExceptionalLocalFormClassification
import LinearAlgebraicGroups.Arithmetic.ExceptionalAdaptedRootCoordinates
import LinearAlgebraicGroups.Arithmetic.ExceptionalSingletonRootSL2
import LinearAlgebraicGroups.Arithmetic.ExceptionalOmittedNodeLevis
import LinearAlgebraicGroups.Arithmetic.ExceptionalLeviRadicalGeneration
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import Mathlib.Tactic.FinCases
import Batteries.Tactic.OpenPrivate

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRadicalGeneration

open LinearAlgebraicGroups.Specs.ExceptionalAffineRootSystems
open LinearAlgebraicGroups.Specs.ExceptionalLocalRadicalGeneration
open private e6RootTable e6Table_iff from
  LinearAlgebraicGroups.Arithmetic.ExceptionalAffineRootSystems

private theorem e6Cartan_eq : e6Cartan = exceptionalCartan 6 := by decide +kernel

private theorem e6Roots (v : Fin 6 → ℤ) :
    IsRootCoordinate (exceptionalCartan 6) v ↔ v ∈ Set.range e6RootTable := by
  rw [← e6Cartan_eq]
  exact e6Table_iff v

set_option maxHeartbeats 2000000 in
/-- E₇ coefficients in breadth-first order under simple reflections. -/
private def e7RootTable (k : Fin 126) : Fin 7 → ℤ :=
  (#[![1, 0, 0, 0, 0, 0, 0],
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
    ![-2, -2, -3, -4, -3, -2, -1]] : Array (Fin 7 → ℤ))[k.val]!

set_option maxHeartbeats 2000000 in
/-- The index of the reflected row in the E₇ table. -/
private def e7ReflectedIndex (i : Fin 7) (k : Fin 126) : Fin 126 :=
  (#[![7, 0, 8, 0, 0, 0, 0],
    ![1, 9, 1, 10, 1, 1, 1],
    ![8, 2, 11, 12, 2, 2, 2],
    ![3, 10, 12, 13, 14, 3, 3],
    ![4, 4, 4, 14, 15, 16, 4],
    ![5, 5, 5, 5, 16, 17, 18],
    ![6, 6, 6, 6, 6, 18, 19],
    ![0, 7, 20, 7, 7, 7, 7],
    ![2, 8, 0, 21, 8, 8, 8],
    ![9, 1, 9, 22, 9, 9, 9],
    ![10, 3, 23, 1, 24, 10, 10],
    ![20, 11, 2, 25, 11, 11, 11],
    ![21, 23, 3, 2, 26, 12, 12],
    ![13, 22, 25, 3, 27, 13, 13],
    ![14, 24, 26, 4, 3, 28, 14],
    ![15, 15, 15, 27, 4, 29, 15],
    ![16, 16, 16, 28, 5, 4, 30],
    ![17, 17, 17, 17, 29, 5, 31],
    ![18, 18, 18, 18, 30, 6, 5],
    ![19, 19, 19, 19, 19, 31, 6],
    ![11, 20, 7, 32, 20, 20, 20],
    ![12, 33, 21, 8, 34, 21, 21],
    ![22, 13, 35, 9, 36, 22, 22],
    ![33, 12, 10, 23, 37, 23, 23],
    ![24, 14, 37, 24, 10, 38, 24],
    ![32, 35, 13, 11, 39, 25, 25],
    ![34, 37, 14, 26, 12, 40, 26],
    ![27, 36, 39, 15, 13, 41, 27],
    ![28, 38, 40, 16, 28, 14, 42],
    ![29, 29, 29, 41, 17, 15, 43],
    ![30, 30, 30, 42, 18, 30, 16],
    ![31, 31, 31, 31, 43, 19, 17],
    ![25, 44, 32, 20, 45, 32, 32],
    ![23, 21, 33, 33, 46, 33, 33],
    ![26, 46, 34, 34, 21, 47, 34],
    ![44, 25, 22, 35, 48, 35, 35],
    ![36, 27, 48, 36, 22, 49, 36],
    ![46, 26, 24, 50, 23, 51, 37],
    ![38, 28, 51, 38, 38, 24, 52],
    ![45, 48, 27, 39, 25, 53, 39],
    ![47, 51, 28, 40, 40, 26, 54],
    ![41, 49, 53, 29, 41, 27, 55],
    ![42, 52, 54, 30, 42, 42, 28],
    ![43, 43, 43, 55, 31, 43, 29],
    ![35, 32, 44, 44, 56, 44, 44],
    ![39, 56, 45, 45, 32, 57, 45],
    ![37, 34, 46, 58, 33, 59, 46],
    ![40, 59, 47, 47, 47, 34, 60],
    ![56, 39, 36, 61, 35, 62, 48],
    ![49, 41, 62, 49, 49, 36, 63],
    ![58, 50, 50, 37, 50, 64, 50],
    ![59, 40, 38, 64, 51, 37, 65],
    ![52, 42, 65, 52, 52, 52, 38],
    ![57, 62, 41, 53, 53, 39, 66],
    ![60, 65, 42, 54, 54, 54, 40],
    ![55, 63, 66, 43, 55, 55, 41],
    ![48, 45, 56, 67, 44, 68, 56],
    ![53, 68, 57, 57, 57, 45, 69],
    ![50, 58, 70, 46, 58, 71, 58],
    ![51, 47, 59, 71, 59, 46, 72],
    ![54, 72, 60, 60, 60, 60, 47],
    ![67, 61, 61, 48, 61, 73, 61],
    ![68, 53, 49, 73, 62, 48, 74],
    ![63, 55, 74, 63, 63, 63, 49],
    ![71, 64, 64, 51, 75, 50, 76],
    ![72, 54, 52, 76, 65, 65, 51],
    ![69, 74, 55, 66, 66, 66, 53],
    ![61, 67, 77, 56, 67, 78, 67],
    ![62, 57, 68, 78, 68, 56, 79],
    ![66, 79, 69, 69, 69, 69, 57],
    ![70, 70, 58, 70, 70, 80, 70],
    ![64, 71, 80, 59, 81, 58, 82],
    ![65, 60, 72, 82, 72, 72, 59],
    ![78, 73, 73, 62, 83, 61, 84],
    ![79, 66, 63, 84, 74, 74, 62],
    ![81, 75, 75, 75, 64, 75, 85],
    ![82, 76, 76, 65, 85, 76, 64],
    ![77, 77, 67, 77, 77, 86, 77],
    ![73, 78, 86, 68, 87, 67, 88],
    ![74, 69, 79, 88, 79, 79, 68],
    ![80, 80, 71, 80, 89, 70, 90],
    ![75, 81, 89, 81, 71, 81, 91],
    ![76, 82, 90, 72, 91, 82, 71],
    ![87, 83, 83, 83, 73, 83, 92],
    ![88, 84, 84, 74, 92, 84, 73],
    ![91, 85, 85, 85, 76, 93, 75],
    ![86, 86, 78, 86, 94, 77, 95],
    ![83, 87, 94, 87, 78, 87, 96],
    ![84, 88, 95, 79, 96, 88, 78],
    ![89, 89, 81, 97, 80, 89, 98],
    ![90, 90, 82, 90, 98, 90, 80],
    ![85, 91, 98, 91, 82, 99, 81],
    ![96, 92, 92, 92, 84, 100, 83],
    ![99, 93, 93, 93, 93, 85, 93],
    ![94, 94, 87, 101, 86, 94, 102],
    ![95, 95, 88, 95, 102, 95, 86],
    ![92, 96, 102, 96, 88, 103, 87],
    ![97, 104, 97, 89, 97, 97, 105],
    ![98, 98, 91, 105, 90, 106, 89],
    ![93, 99, 106, 99, 99, 91, 99],
    ![103, 100, 100, 100, 100, 92, 100],
    ![101, 107, 101, 94, 101, 101, 108],
    ![102, 102, 96, 108, 95, 109, 94],
    ![100, 103, 109, 103, 103, 96, 103],
    ![104, 97, 104, 104, 104, 104, 110],
    ![105, 110, 105, 98, 105, 111, 97],
    ![106, 106, 99, 111, 106, 98, 106],
    ![107, 101, 107, 107, 107, 107, 112],
    ![108, 112, 108, 102, 108, 113, 101],
    ![109, 109, 103, 113, 109, 102, 109],
    ![110, 105, 110, 110, 110, 114, 104],
    ![111, 114, 111, 106, 115, 105, 111],
    ![112, 108, 112, 112, 112, 116, 107],
    ![113, 116, 113, 109, 117, 108, 113],
    ![114, 111, 114, 114, 118, 110, 114],
    ![115, 118, 115, 115, 111, 115, 115],
    ![116, 113, 116, 116, 119, 112, 116],
    ![117, 119, 117, 117, 113, 117, 117],
    ![118, 115, 118, 120, 114, 118, 118],
    ![119, 117, 119, 121, 116, 119, 119],
    ![120, 120, 122, 118, 120, 120, 120],
    ![121, 121, 123, 119, 121, 121, 121],
    ![124, 122, 120, 122, 122, 122, 122],
    ![125, 123, 121, 123, 123, 123, 123],
    ![122, 124, 124, 124, 124, 124, 124],
    ![123, 125, 125, 125, 125, 125, 125]] : Array (Fin 7 → Fin 126))[k.val]! i

/-- For each nonsimple row, an earlier row and the simple reflection yielding it. -/
private def e7Parent (k : Fin 126) : Fin 126 × Fin 7 :=
  (#[(0, 0),
    (0, 0),
    (0, 0),
    (0, 0),
    (0, 0),
    (0, 0),
    (0, 0),
    (0, 0),
    (0, 2),
    (1, 1),
    (1, 3),
    (2, 2),
    (2, 3),
    (3, 3),
    (3, 4),
    (4, 4),
    (4, 5),
    (5, 5),
    (5, 6),
    (6, 6),
    (7, 2),
    (8, 3),
    (9, 3),
    (10, 2),
    (10, 4),
    (11, 3),
    (12, 4),
    (13, 4),
    (14, 5),
    (15, 5),
    (16, 6),
    (17, 6),
    (20, 3),
    (21, 1),
    (21, 4),
    (22, 2),
    (22, 4),
    (23, 4),
    (24, 5),
    (25, 4),
    (26, 5),
    (27, 5),
    (28, 6),
    (29, 6),
    (32, 1),
    (32, 4),
    (33, 4),
    (34, 5),
    (35, 4),
    (36, 5),
    (37, 3),
    (37, 5),
    (38, 6),
    (39, 5),
    (40, 6),
    (41, 6),
    (44, 4),
    (45, 5),
    (46, 3),
    (46, 5),
    (47, 6),
    (48, 3),
    (48, 5),
    (49, 6),
    (50, 5),
    (51, 6),
    (53, 6),
    (56, 3),
    (56, 5),
    (57, 6),
    (58, 2),
    (58, 5),
    (59, 6),
    (61, 5),
    (62, 6),
    (64, 4),
    (64, 6),
    (67, 2),
    (67, 5),
    (68, 6),
    (70, 5),
    (71, 4),
    (71, 6),
    (73, 4),
    (73, 6),
    (75, 6),
    (77, 5),
    (78, 4),
    (78, 6),
    (80, 4),
    (80, 6),
    (81, 6),
    (83, 6),
    (85, 5),
    (86, 4),
    (86, 6),
    (87, 6),
    (89, 3),
    (89, 6),
    (91, 5),
    (92, 5),
    (94, 3),
    (94, 6),
    (96, 5),
    (97, 1),
    (97, 6),
    (98, 5),
    (101, 1),
    (101, 6),
    (102, 5),
    (104, 6),
    (105, 5),
    (107, 6),
    (108, 5),
    (110, 5),
    (111, 4),
    (112, 5),
    (113, 4),
    (114, 4),
    (116, 4),
    (118, 3),
    (119, 3),
    (120, 2),
    (121, 2),
    (122, 0),
    (123, 0)] : Array (Fin 126 × Fin 7))[k.val]!

private theorem e7Table_simple : ∀ i : Fin 7,
    e7RootTable (i.castLE (by decide)) = Pi.single i 1 := by decide +kernel

private theorem e7Table_contains_simple (i : Fin 7) :
    Pi.single i 1 ∈ Set.range e7RootTable :=
  ⟨i.castLE (by decide), e7Table_simple i⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
private theorem e7Table_reflection (i : Fin 7) :
    ∀ k : Fin 126,
      simpleReflection (exceptionalCartan 7) i (e7RootTable k) =
        e7RootTable (e7ReflectedIndex i k) := by
  fin_cases i <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
private theorem e7Table_step :
    ∀ k : Fin 126, ¬ k.val < 7 →
      (e7Parent k).1 < k ∧ e7ReflectedIndex (e7Parent k).2 (e7Parent k).1 = k := by
  decide +kernel

private theorem e7Table_isRoot (k : Fin 126) :
    IsRootCoordinate (exceptionalCartan 7) (e7RootTable k) := by
  induction k using (measure (fun x : Fin 126 => x.val)).wf.induction with
  | h k ih =>
    by_cases hk : k.val < 7
    · let i : Fin 7 := ⟨k.val, hk⟩
      have he : i.castLE (by decide : 7 ≤ 126) = k := Fin.ext rfl
      rw [← he, e7Table_simple]
      exact .simple _
    · obtain ⟨hp, he⟩ := e7Table_step k hk
      have prev := ih (e7Parent k).1 hp
      rw [← he, ← e7Table_reflection]
      exact prev.reflect _

private theorem e7Roots (v : Fin 7 → ℤ) :
    IsRootCoordinate (exceptionalCartan 7) v ↔ v ∈ Set.range e7RootTable := by
  constructor
  · intro hv
    induction hv with
    | simple i => exact e7Table_contains_simple i
    | reflect _ i ih =>
      obtain ⟨k, rfl⟩ := ih
      exact ⟨e7ReflectedIndex i k, (e7Table_reflection i k).symm⟩
  · rintro ⟨k, rfl⟩
    exact e7Table_isRoot k


section Projection

private def projectionFinset {m n r : ℕ} (table : Fin m → Fin n → ℤ)
    (project : (Fin n → ℤ) → Fin r → ℤ) : Finset (Fin r → ℤ) :=
  (Finset.univ.image fun k => project (table k)).erase 0

private theorem projectionFinset_eq {m n r : ℕ} {table : Fin m → Fin n → ℤ}
    (hTable : ∀ v, IsRootCoordinate (exceptionalCartan n) v ↔ v ∈ Set.range table)
    (project : (Fin n → ℤ) → Fin r → ℤ) :
    (projectionFinset table project : Set (Fin r → ℤ)) = projectedRoots project := by
  ext x
  simp only [projectionFinset, Finset.mem_coe, Finset.mem_erase, Finset.mem_image,
    Finset.mem_univ, true_and, projectedRoots, Set.mem_sdiff, Set.mem_singleton_iff,
    Set.mem_image, Set.mem_ofPred_eq, hTable, Set.mem_range]
  constructor
  · rintro ⟨hx, i, rfl⟩
    exact ⟨⟨table i, ⟨i, rfl⟩, rfl⟩, hx⟩
  · rintro ⟨⟨_, ⟨i, rfl⟩, rfl⟩, hx⟩
    exact ⟨hx, i, rfl⟩

/-- A coordinate or the difference of two coordinates detects a primitive
vector in these projected systems. -/
private def PrimitiveCoordinates {r : ℕ} (v : Fin r → ℤ) : Prop :=
  (∃ i, v i = 1 ∨ v i = -1) ∨ ∃ i j, v i - v j = 1

private instance {r : ℕ} (v : Fin r → ℤ) : Decidable (PrimitiveCoordinates v) := by
  unfold PrimitiveCoordinates
  infer_instance

private theorem integral_functional {r : ℕ} {v : Fin r → ℤ}
    (h : PrimitiveCoordinates v) : ∃ f : (Fin r → ℤ) →ₗ[ℤ] ℤ, f v = 1 := by
  rcases h with ⟨i, hi | hi⟩ | ⟨i, j, hij⟩
  · exact ⟨LinearMap.proj i, hi⟩
  · exact ⟨-LinearMap.proj i, by simpa using congrArg Neg.neg hi⟩
  · let evaluate (k : Fin r) : (Fin r → ℤ) →ₗ[ℤ] ℤ := LinearMap.proj k
    refine ⟨evaluate i - evaluate j, ?_⟩
    rw [LinearMap.sub_apply]
    exact hij

private theorem primitive_proportional {r : ℕ} {v w : Fin r → ℤ}
    (hv : PrimitiveCoordinates v) (hw : PrimitiveCoordinates w)
    {a b : ℤ} (ha : a ≠ 0) (h : a • v = b • w) : w = v ∨ w = -v := by
  obtain ⟨f, hf⟩ := integral_functional hv
  obtain ⟨g, hg⟩ := integral_functional hw
  have hab : a = b * f w := by
    have hf' : f (a • v) = f (b • w) := congrArg f h
    simpa only [map_smul, hf, smul_eq_mul, mul_one] using hf'
  have hba : a * g v = b := by
    have hg' : g (a • v) = g (b • w) := congrArg g h
    simpa only [map_smul, hg, smul_eq_mul, mul_one] using hg'
  have hprod : g v * f w = 1 := by
    apply mul_left_cancel₀ ha
    calc
      a * (g v * f w) = (a * g v) * f w := by ring
      _ = a * 1 := by rw [hba, ← hab, mul_one]
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hprod with hs | hs
  · left
    funext i
    have hi := congrFun h i
    rw [← hba, hs.1, mul_one] at hi
    exact (mul_left_cancel₀ ha hi).symm
  · right
    funext i
    have hi := congrFun h i
    rw [← hba, hs.1, mul_neg_one] at hi
    change a * v i = -a * w i at hi
    rw [neg_mul, ← mul_neg] at hi
    have hn := mul_left_cancel₀ ha hi
    exact eq_neg_of_add_eq_zero_left (by rw [hn, add_neg_cancel])

open LinearAlgebraicGroups.Specs.ExceptionalInnerAlcoveSymmetries (e6Highest e7Highest)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
private theorem projection_cardinalities :
    (projectionFinset e6RootTable e6InnerProjection).card = 12 ∧
    (projectionFinset e7RootTable e7InnerProjection).card = 48 ∧
    (projectionFinset e6RootTable restrictedRoot).card = 48 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
private theorem e6InnerTable_projection :
    ∀ k : Fin 72,
      let v := e6RootTable k
      let p := e6InnerProjection v
      (p = 0 ∨ PrimitiveCoordinates p) ∧
      (∀ j, p j ≤ e6InnerProjection e6Highest j) ∧
      (p = e6InnerProjection (Pi.single 1 1) → v = Pi.single 1 1) ∧
      (p = e6InnerProjection e6Highest → v = e6Highest) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
private theorem e7InnerTable_projection :
    ∀ k : Fin 126,
      let v := e7RootTable k
      let p := e7InnerProjection v
      (p = 0 ∨ PrimitiveCoordinates p) ∧
      (∀ j, p j ≤ e7InnerProjection e7Highest j) ∧
      (p = e7InnerProjection (Pi.single 2 1) → v = Pi.single 2 1) ∧
      (p = e7InnerProjection e7Highest → v = e7Highest) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
private theorem e6OuterTable_projection :
    ∀ k : Fin 72,
      let v := e6RootTable k
      let p := restrictedRoot v
      (p = 0 ∨ PrimitiveCoordinates p) ∧
      (∀ j, p j ≤ restrictedRoot e6Highest j) ∧
      (p = restrictedRoot (Pi.single 1 1) → v = Pi.single 1 1) ∧
      (p = restrictedRoot e6Highest → v = e6Highest) := by
  decide +kernel

private theorem e6_length {project : (Fin 6 → ℤ) → Fin r → ℤ}
    (hker : ∀ c, project c = 0 → c 1 = 0 ∧ c 3 = 0) :
    KeepsFullLength project (Pi.single 1 1) ∧ KeepsFullLength project e6Highest := by
  have hs : (exceptionalCartan 6).vecMul (Pi.single 1 1) = ![0, 2, 0, -1, 0, 0] := by
    decide +kernel
  have hh : (exceptionalCartan 6).vecMul e6Highest = ![0, 1, 0, 0, 0, 0] := by
    decide +kernel
  constructor <;> intro c hc <;> obtain ⟨h₁, h₃⟩ := hker c hc
  · rw [Matrix.dotProduct_mulVec, hs]
    simp [dotProduct, Fin.sum_univ_succ, h₁, h₃]
  · rw [Matrix.dotProduct_mulVec, hh]
    simp [dotProduct, Fin.sum_univ_succ, h₁]

private theorem e7_length :
    KeepsFullLength e7InnerProjection (Pi.single 2 1) ∧
      KeepsFullLength e7InnerProjection e7Highest := by
  have hs : (exceptionalCartan 7).vecMul (Pi.single 2 1) = ![-1, 0, 2, -1, 0, 0, 0] := by
    decide +kernel
  have hh : (exceptionalCartan 7).vecMul e7Highest = ![1, 0, 0, 0, 0, 0, 0] := by
    decide +kernel
  constructor <;> intro c hc
  · have h₀ : c 0 = 0 := congrFun hc 0
    have h₂ : c 2 = 0 := congrFun hc 1
    have h₃ : c 3 = 0 := congrFun hc 2
    rw [Matrix.dotProduct_mulVec, hs]
    simp [dotProduct, Fin.sum_univ_succ, h₀, h₂, h₃]
  · have h₀ : c 0 = 0 := congrFun hc 0
    rw [Matrix.dotProduct_mulVec, hh]
    simp [dotProduct, Fin.sum_univ_succ, h₀]

/-- The finite root calculation for a marked restriction map. -/
structure ProjectedRootCoordinates {n r : ℕ} (project : (Fin n → ℤ) → Fin r → ℤ)
    (count : ℕ) (node : Fin n) (highest : Fin n → ℤ) : Prop where
  cardinality : Nat.card (projectedRoots project) = count
  highestRoot : IsRootCoordinate (exceptionalCartan n) highest
  simpleMem : project (Pi.single node 1) ∈ projectedRoots project
  highestMem : project highest ∈ projectedRoots project
  greatest : ∀ v ∈ projectedRoots project, ∀ j, v j ≤ project highest j
  reduced : ∀ v ∈ projectedRoots project, ∀ w ∈ projectedRoots project,
    ∀ {a b : ℤ}, a ≠ 0 → a • v = b • w → w = v ∨ w = -v
  simpleFibre : ∀ v, IsRootCoordinate (exceptionalCartan n) v →
    project v = project (Pi.single node 1) → v = Pi.single node 1
  highestFibre : ∀ v, IsRootCoordinate (exceptionalCartan n) v →
    project v = project highest → v = highest
  simpleLength : KeepsFullLength project (Pi.single node 1)
  highestLength : KeepsFullLength project highest

private theorem projectedRootCoordinates_of_table {m n r count : ℕ}
    {table : Fin m → Fin n → ℤ} {project : (Fin n → ℤ) → Fin r → ℤ}
    {node : Fin n} {highest : Fin n → ℤ}
    (hTable : ∀ v, IsRootCoordinate (exceptionalCartan n) v ↔ v ∈ Set.range table)
    (hCount : (projectionFinset table project).card = count)
    (hHighest : highest ∈ Set.range table)
    (hSimpleNonzero : project (Pi.single node 1) ≠ 0)
    (hHighestNonzero : project highest ≠ 0)
    (hProject : ∀ k : Fin m,
      let v := table k
      let p := project v
      (p = 0 ∨ PrimitiveCoordinates p) ∧
      (∀ j, p j ≤ project highest j) ∧
      (p = project (Pi.single node 1) → v = Pi.single node 1) ∧
      (p = project highest → v = highest))
    (hLength : KeepsFullLength project (Pi.single node 1) ∧ KeepsFullLength project highest) :
    ProjectedRootCoordinates project count node highest := by
  have hr := (hTable highest).mpr hHighest
  have row {v : Fin r → ℤ} (hv : v ∈ projectedRoots project) :
      (∃ k, project (table k) = v) ∧ v ≠ 0 := by
    obtain ⟨⟨x, hx, rfl⟩, hzero⟩ := hv
    obtain ⟨k, rfl⟩ := (hTable x).mp hx
    exact ⟨⟨k, rfl⟩, hzero⟩
  have primitive {v : Fin r → ℤ} (hv : v ∈ projectedRoots project) :
      PrimitiveCoordinates v := by
    obtain ⟨⟨k, rfl⟩, hv₀⟩ := row hv
    exact (hProject k).1.resolve_left hv₀
  refine ⟨?_, hr, ⟨⟨_, .simple node, rfl⟩, hSimpleNonzero⟩,
    ⟨⟨_, hr, rfl⟩, hHighestNonzero⟩, ?_, ?_, ?_, ?_, hLength.1, hLength.2⟩
  · rw [← projectionFinset_eq hTable, Nat.card_coe_set_eq, Set.ncard_coe_finset, hCount]
  · intro v hv j
    obtain ⟨⟨k, rfl⟩, _⟩ := row hv
    exact (hProject k).2.1 j
  · exact fun _ hv _ hw _ _ ha he => primitive_proportional (primitive hv) (primitive hw) ha he
  · intro v hv he
    obtain ⟨k, rfl⟩ := (hTable v).mp hv
    exact (hProject k).2.2.1 he
  · intro v hv he
    obtain ⟨k, rfl⟩ := (hTable v).mp hv
    exact (hProject k).2.2.2 he

theorem e6InnerProjectedRoots : ProjectedRootCoordinates e6InnerProjection 12 1 e6Highest := by
  refine projectedRootCoordinates_of_table e6Roots projection_cardinalities.1
    ⟨64, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) e6InnerTable_projection ?_
  apply e6_length
  exact fun _ h => ⟨congrFun h 0, congrFun h 1⟩

theorem e7InnerProjectedRoots : ProjectedRootCoordinates e7InnerProjection 48 2 e7Highest :=
  projectedRootCoordinates_of_table e7Roots projection_cardinalities.2.1
    ⟨124, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) e7InnerTable_projection e7_length

theorem e6OuterProjectedRoots : ProjectedRootCoordinates restrictedRoot 48 1 e6Highest := by
  refine projectedRootCoordinates_of_table e6Roots projection_cardinalities.2.2
    ⟨64, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) e6OuterTable_projection ?_
  apply e6_length
  exact fun _ h => ⟨congrFun h 0, congrFun h 1⟩


/-- A sequence of reflections with a unique full-length absolute lift for
each reflecting root. The word acts on the absolute coefficient vectors. -/
def HasFullLengthReflectionWord {n r : ℕ} (project : (Fin n → ℤ) → Fin r → ℤ)
    (start finish : Fin n → ℤ) : Prop :=
  ∃ word : List (Fin n → ℤ),
    (∀ a ∈ word, IsRootCoordinate (exceptionalCartan n) a ∧
      project a ≠ 0 ∧ KeepsFullLength project a ∧
      ∀ v, IsRootCoordinate (exceptionalCartan n) v → project v = project a → v = a) ∧
    word.foldl (fun v a => v - dotProduct v ((exceptionalCartan n).mulVec a) • a) start = finish

private def e6Reflector : Fin 6 → ℤ := e6Highest - Pi.single 1 1

private def e7SecondReflector : Fin 7 → ℤ := e7Highest - (Pi.single 0 1 + Pi.single 2 1)

private theorem e6Reflector_isRoot : IsRootCoordinate (exceptionalCartan 6) e6Reflector :=
  (e6Roots _).mpr ⟨58, by decide +kernel⟩

private theorem e7SecondReflector_isRoot : IsRootCoordinate (exceptionalCartan 7) e7SecondReflector :=
  (e7Roots _).mpr ⟨120, by decide +kernel⟩

private theorem e6Reflector_length {project : (Fin 6 → ℤ) → Fin r → ℤ}
    (hker : ∀ c, project c = 0 → c 1 = 0 ∧ c 3 = 0) :
    KeepsFullLength project e6Reflector := by
  intro c hc
  obtain ⟨hs, hh⟩ := e6_length hker
  rw [e6Reflector, sub_dotProduct, hh c hc, hs c hc, sub_zero]

private theorem e7FirstReflector_length : KeepsFullLength e7InnerProjection (Pi.single 0 1) := by
  have hs : (exceptionalCartan 7).vecMul (Pi.single 0 1) = ![2, 0, -1, 0, 0, 0, 0] := by
    decide +kernel
  intro c hc
  have h₀ : c 0 = 0 := congrFun hc 0
  have h₂ : c 2 = 0 := congrFun hc 1
  rw [Matrix.dotProduct_mulVec, hs]
  simp [dotProduct, Fin.sum_univ_succ, h₀, h₂]

private theorem e7SecondReflector_length : KeepsFullLength e7InnerProjection e7SecondReflector := by
  intro c hc
  rw [e7SecondReflector, sub_dotProduct, add_dotProduct, e7_length.2 c hc,
    e7FirstReflector_length c hc, e7_length.1 c hc, add_zero, sub_zero]

private theorem uniqueLift_of_table {m n r : ℕ} {table : Fin m → Fin n → ℤ}
    {project : (Fin n → ℤ) → Fin r → ℤ} {root : Fin n → ℤ}
    (hTable : ∀ v, IsRootCoordinate (exceptionalCartan n) v ↔ v ∈ Set.range table)
    (hTest : ∀ k, project (table k) = project root → table k = root) :
    ∀ v, IsRootCoordinate (exceptionalCartan n) v → project v = project root → v = root := by
  intro v hv
  obtain ⟨k, rfl⟩ := (hTable v).mp hv
  exact hTest k

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem e6InnerHighestReflection :
    HasFullLengthReflectionWord e6InnerProjection (Pi.single 1 1) e6Highest := by
  refine ⟨[e6Reflector], ?_, by decide +kernel⟩
  intro a ha
  have h : a = e6Reflector := List.mem_singleton.mp ha
  subst a
  refine ⟨e6Reflector_isRoot, by decide +kernel,
    e6Reflector_length (fun _ h => ⟨congrFun h 0, congrFun h 1⟩), ?_⟩
  exact uniqueLift_of_table e6Roots (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem e6OuterHighestReflection :
    HasFullLengthReflectionWord restrictedRoot (Pi.single 1 1) e6Highest := by
  refine ⟨[e6Reflector], ?_, by decide +kernel⟩
  intro a ha
  have h : a = e6Reflector := List.mem_singleton.mp ha
  subst a
  refine ⟨e6Reflector_isRoot, by decide +kernel,
    e6Reflector_length (fun _ h => ⟨congrFun h 0, congrFun h 1⟩), ?_⟩
  exact uniqueLift_of_table e6Roots (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem e7InnerHighestReflections :
    HasFullLengthReflectionWord e7InnerProjection (Pi.single 2 1) e7Highest := by
  refine ⟨[Pi.single 0 1, e7SecondReflector], ?_, by decide +kernel⟩
  intro a ha
  rw [List.mem_cons] at ha
  rcases ha with rfl | ha
  · exact ⟨.simple 0, by decide +kernel, e7FirstReflector_length,
      uniqueLift_of_table e7Roots (by decide +kernel)⟩
  · have h : a = e7SecondReflector := List.mem_singleton.mp ha
    subst a
    exact ⟨e7SecondReflector_isRoot, by decide +kernel, e7SecondReflector_length,
      uniqueLift_of_table e7Roots (by decide +kernel)⟩

end Projection


section AdaptedRootSystem

open AlgebraicGeometry CategoryTheory Opposite
open _root_.LinearAlgebraicGroups.Specs.AbstractPairing (Root)
open _root_.LinearAlgebraicGroups.Specs.CharacterDescent (Character)
open _root_.LinearAlgebraicGroups.Specs.CharacterPairing (absoluteRoots)
open _root_.LinearAlgebraicGroups.Specs.Relative.RelativeChambers (relativeRoots)
open _root_.LinearAlgebraicGroups.Specs.GeometricBorelConjugacy (ConjugatesSubgroups)
open _root_.LinearAlgebraicGroups.Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open _root_.LinearAlgebraicGroups.CocharacterDynamics (unitPoint)
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

variable {F : Type u} [Field F] {G : _root_.LinearAlgebraicGroups.Specs.AffineAlgebraicGroup F}
variable {n : ℕ}

set_option backward.isDefEq.respectTransparency false in
theorem adaptedRootCoordinates (A : AdaptedBorel G n)
    (hCartan : (exceptionalCartan n).IsSymm) :
    ∃ coeff : Root A.P.T ≃ {v // IsRootCoordinate (exceptionalCartan n) v},
      (∀ a, A.D.toBased.datum.root a =
        ∑ j, (coeff a).val j • A.D.toBased.datum.root (A.numbering j)) ∧
      (∀ a, A.D.toBased.datum.coroot a =
        ∑ j, (coeff a).val j • A.D.toBased.datum.coroot (A.numbering j)) ∧
      (∀ i, (coeff (A.numbering i).val).val = Pi.single i 1) := by
  let := A.D.comm
  let := A.D.toBased.finiteRoots
  let := A.D.toBased.reduced
  let D := A.D.toBased.datum
  obtain ⟨coeff, h⟩ := ExceptionalAffineRootSystems.pairedRootCoordinates
    D A.D.toBased.base A.numbering (exceptionalCartan n) hCartan
    (fun i j => (A.cartan_eq i j).symm)
  refine ⟨coeff, fun a => (h a).1, fun a => (h a).2, ?_⟩
  have hinj : Function.Injective (fun v : Fin n → ℤ => ∑ j, v j • D.root (A.numbering j)) :=
    linearIndependent_iff_injective_fintypeLinearCombination.mp
      (A.D.toBased.base.linearIndepOn_root.comp A.numbering A.numbering.injective)
  intro i
  apply hinj
  change (∑ j, (coeff (A.numbering i).val).val j • D.root (A.numbering j)) = _
  rw [← (h (A.numbering i).val).1]
  simp

open private rootsOfIso from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private characterValue_extend from LinearAlgebraicGroups.Relative.RelativeChambers
open private unitEquiv unitEquiv_unitPoint from
  LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private characterValue_one from LinearAlgebraicGroups.RootData.CharacterPairing
open private splitTorus_baseChange from LinearAlgebraicGroups.RootData.BorelsAndChambers

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem adaptedRelativeRootRestrictions (A : AdaptedBorel G n) :
    Function.Injective A.extendRelative ∧
    A.extendRelative 1 = 1 ∧
    A.extendRelative '' relativeRoots A.S = (A.restrictAbsolute '' absoluteRoots A.P.T) \ {1} := by
  let K := SeparableClosure F
  let T' := _root_.LinearAlgebraicGroups.Specs.GeometricRadicals.baseChangedSubgroup K A.T
    (_root_.LinearAlgebraicGroups.baseChangeClosedSubgroup F K _ A.T.isClosedImmersion)
  have hsplit : _root_.LinearAlgebraicGroups.Specs.GeometricRadicals.IsSplitTorus T'.group := by
    obtain ⟨r, ⟨e⟩⟩ := A.P.split
    exact ⟨r, ⟨A.torus ≪≫ e⟩⟩
  obtain ⟨e, he, hInj, hRoots⟩ :=
    _root_.LinearAlgebraicGroups.Relative.RelativeChambers.relativeRootsByRestriction
      G A.S A.T A.intoTorus A.intoTorus_eq A.maximalSplit.1 T'.isClosedImmersion hsplit
  have heA : e = A.multiplicative := by
    apply Iso.ext
    apply (_root_.LinearAlgebraicGroups.groupHomComparison K _ _ (by
      change IsAffine (Spec (CommRingCat.of (MonoidAlgebra K IntegerCharacters)))
      infer_instance)).1
    apply NatTrans.ext
    funext R
    apply GrpCat.ext
    intro p
    change p ≫ e.hom.hom.hom = p ≫ A.multiplicative.hom.hom.hom
    obtain ⟨t, rfl⟩ := (Function.RightInverse.surjective
      (show Function.RightInverse (unitEquiv R) (unitPoint R) from by
        intro x
        apply (unitEquiv R).injective
        exact unitEquiv_unitPoint R _)) p
    apply (_root_.LinearAlgebraicGroups.baseChangePointsEquiv K _ R).injective
    exact (he R t).trans (A.multiplicative_eq R t).symm
  subst e
  refine ⟨hInj, ?_, hRoots.trans ?_⟩
  · apply _root_.LinearAlgebraicGroups.RootData.CharacterPairing.characterValuesDetectCharacters
      (splitTorus_baseChange A.maximalSplit.1)
    intro R t
    rw [characterValue_extend 1 A.multiplicative A.multiplicative_eq,
      characterValue_one, characterValue_one]
  · congr 1
    have hTorus : T'.inclusion ≫ A.ambient.inv = A.torus.hom ≫ A.P.T.inclusion := by
      change (groupBaseChange F (SeparableClosure F)).map A.T.inclusion ≫ A.ambient.inv =
        A.torus.hom ≫ A.P.T.inclusion
      rw [← A.torus_eq, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have hAbs (χ : Character A.P.T.group) :
        (A.torus.hom ≫ χ) ∈ absoluteRoots T' ↔ χ ∈ absoluteRoots A.P.T :=
      rootsOfIso (T := T') (S := A.P.T) A.ambient.symm A.torus hTorus χ
    ext x
    constructor
    · rintro ⟨χ, hχ, rfl⟩
      let χ' := A.torus.inv ≫ χ
      have hχ' : χ' ∈ absoluteRoots A.P.T := by
        apply (hAbs χ').mp
        rwa [show A.torus.hom ≫ χ' = χ from A.torus.hom_inv_id_assoc χ]
      refine ⟨χ', hχ', ?_⟩
      change ((groupBaseChange F K).map A.intoTorus ≫ A.torus.hom) ≫
        (A.torus.inv ≫ χ) = (groupBaseChange F K).map A.intoTorus ≫ χ
      rw [Category.assoc, Iso.hom_inv_id_assoc]
    · rintro ⟨χ, hχ, rfl⟩
      exact ⟨A.torus.hom ≫ χ, (hAbs χ).mpr hχ,
        Category.assoc _ _ _ |>.symm⟩

set_option backward.isDefEq.respectTransparency false in
/-- Identify the relative roots from their absolute restrictions and the
injective map on the chosen simple coordinates. -/
theorem relativeRootsOfProjection (A : AdaptedBorel G n) {r : ℕ}
    {project : (Fin n → ℤ) → Fin r → ℤ}
    (coeff : Root A.P.T ≃ {v // IsRootCoordinate (exceptionalCartan n) v})
    (encode : Multiplicative (Fin r → ℤ) →* Character A.S.group)
    (hEncode : Function.Injective encode)
    (hRestrict : ∀ a, A.restrictAbsolute a.val =
      A.extendRelative (encode (Multiplicative.ofAdd (project (coeff a).val)))) :
    relativeRoots A.S = (fun v => encode (Multiplicative.ofAdd v)) '' projectedRoots project := by
  obtain ⟨hInj, hOne, hRoots⟩ := adaptedRelativeRootRestrictions A
  let enc (v : Fin r → ℤ) := encode (Multiplicative.ofAdd v)
  have henc₀ (v : Fin r → ℤ) : enc v = 1 ↔ v = 0 := by
    change encode (Multiplicative.ofAdd v) = 1 ↔ _
    rw [← encode.map_one]
    exact ⟨fun h => congrArg Multiplicative.toAdd (hEncode h), fun h => congrArg enc h⟩
  ext a
  constructor
  · intro ha
    have h := Set.mem_image_of_mem A.extendRelative ha
    rw [hRoots] at h
    obtain ⟨⟨χ, hχ, he⟩, hne⟩ := h
    let α : Root A.P.T := ⟨χ, hχ⟩
    have hα : A.restrictAbsolute α.val = A.extendRelative a := he
    rw [hRestrict] at hα
    have hcod := hInj hα
    refine ⟨project (coeff α).val, ⟨⟨_, (coeff α).property, rfl⟩, ?_⟩, hcod⟩
    intro hzero
    exact hne ((congrArg A.extendRelative (hcod.symm.trans ((henc₀ _).mpr hzero))).trans hOne)
  · rintro ⟨v, ⟨⟨x, hx, rfl⟩, hn⟩, rfl⟩
    let α := coeff.symm ⟨x, hx⟩
    have he : (coeff α).val = x := congrArg Subtype.val (coeff.apply_symm_apply ⟨x, hx⟩)
    have hEq : A.restrictAbsolute α.val = A.extendRelative (enc (project x)) := by
      rw [hRestrict, he]
    have h : A.extendRelative (enc (project x)) ∈ A.extendRelative '' relativeRoots A.S := by
      rw [hRoots]
      refine ⟨⟨α.val, α.property, hEq⟩, ?_⟩
      exact fun h => hn ((henc₀ _).mp (hInj (h.trans hOne.symm)))
    obtain ⟨β, hβ, hEq'⟩ := h
    change enc (project x) ∈ relativeRoots A.S
    rw [← hInj hEq']
    exact hβ

set_option backward.isDefEq.respectTransparency false in
/-- Transfer the finite calculation to the actual root groups once the
restriction map and the rational normalizer conjugation have been constructed. -/
theorem hasProjectedRootSystem_of_coordinates (A : AdaptedBorel G n) {r count : ℕ}
    {project : (Fin n → ℤ) → Fin r → ℤ} {node : Fin n} {highest : Fin n → ℤ}
    (calculation : ProjectedRootCoordinates project count node highest)
    (selected : SplitRootSL2 A (A.numbering node).val)
    (coeff : Root A.P.T ≃ {v // IsRootCoordinate (exceptionalCartan n) v})
    (encode : Multiplicative (Fin r → ℤ) →* Character A.S.group)
    (hEncode : Function.Injective encode)
    (hCoeff : ∀ a, A.D.toBased.datum.root a =
      ∑ j, (coeff a).val j • A.D.toBased.datum.root (A.numbering j))
    (hSimple : ∀ i, (coeff (A.numbering i).val).val = Pi.single i 1)
    (hRestrict : ∀ a, A.restrictAbsolute a.val =
      A.extendRelative (encode (Multiplicative.ofAdd (project (coeff a).val))))
    (hConjugation :
      ∃ (highestSL2 : SplitRootSL2 A (coeff.symm ⟨highest, calculation.highestRoot⟩))
        (w : 𝟙_ (SchemeOver F) ⟶ G.val.X) (τ : A.S.group ≅ A.S.group),
        (τ.hom ≫ A.S.inclusion).hom.hom =
          (toUnit _ ≫ w) * A.S.inclusion.hom.hom * (toUnit _ ≫ w)⁻¹ ∧
        τ.hom ≫ encode (Multiplicative.ofAdd (project highest)) =
          encode (Multiplicative.ofAdd (project (Pi.single node 1))) ∧
        ConjugatesSubgroups w selected.subgroup highestSL2.subgroup) :
    HasProjectedRootSystem A project count node selected := by
  let enc (v : Fin r → ℤ) := encode (Multiplicative.ofAdd v)
  have hEnc : Function.Injective enc := fun _ _ h => congrArg Multiplicative.toAdd (hEncode h)
  have hExt := (adaptedRelativeRootRestrictions A).1
  have hActual := relativeRootsOfProjection A coeff encode hEncode hRestrict
  have enc_mem {v} (hv : v ∈ projectedRoots project) : enc v ∈ relativeRoots A.S := by
    rw [hActual]
    exact Set.mem_image_of_mem enc hv
  refine ⟨coeff, encode, hEncode, hCoeff, hSimple, hRestrict, hActual, ?_, ?_, ?_⟩
  · rw [hActual, Nat.card_coe_set_eq, Set.ncard_image_of_injective _ hEnc]
    exact calculation.cardinality
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨m, n, hm, _, h⟩
    rw [hActual] at ha hb
    obtain ⟨v, hv, rfl⟩ := ha
    obtain ⟨w, hw, rfl⟩ := hb
    change enc v ^ m = enc w ^ n at h
    have hEq : m • v = n • w := by
      apply hEnc
      simpa only [enc, ofAdd_zsmul, map_zpow] using h
    rcases calculation.reduced v hv w hw hm hEq with rfl | hwv
    · exact Or.inl rfl
    · right
      change enc w = (enc v)⁻¹
      rw [hwv]
      exact encode.map_inv (Multiplicative.ofAdd v)
  · let α := coeff.symm ⟨highest, calculation.highestRoot⟩
    have hα : (coeff α).val = highest := congrArg Subtype.val
      (coeff.apply_symm_apply ⟨highest, calculation.highestRoot⟩)
    refine ⟨⟨_, enc_mem calculation.simpleMem⟩, ⟨_, enc_mem calculation.highestMem⟩, α,
      rfl, congrArg (enc ∘ project) hα.symm, ?_, calculation.simpleLength, ?_, ?_, ?_⟩
    · exact fun v hv j => (calculation.greatest v hv j).trans_eq
        (congrArg (fun x => project x j) hα.symm)
    · simpa only [hα] using calculation.highestLength
    · intro a
      constructor
      · constructor
        · intro ha
          have hp : project (coeff a).val = project (Pi.single node 1) :=
            hEnc (hExt ((hRestrict a).symm.trans ha))
          apply coeff.injective
          exact Subtype.ext ((calculation.simpleFibre _ (coeff a).property hp).trans (hSimple node).symm)
        · rintro rfl
          rw [hRestrict, hSimple]
      · constructor
        · intro ha
          have hp : project (coeff a).val = project highest :=
            hEnc (hExt ((hRestrict a).symm.trans ha))
          apply coeff.injective
          exact Subtype.ext ((calculation.highestFibre _ (coeff a).property hp).trans hα.symm)
        · rintro rfl
          rw [hRestrict, hα]
    · exact hConjugation

end AdaptedRootSystem

section QuasiSplit

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open _root_.LinearAlgebraicGroups.Specs
open _root_.LinearAlgebraicGroups.Specs.ExceptionalLocalRadicalGeneration (localPointTopology)
open _root_.LinearAlgebraicGroups.Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open _root_.LinearAlgebraicGroups.Specs.Arithmetic.RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open _root_.LinearAlgebraicGroups.Specs.BorelProper (IsParabolic)
open _root_.LinearAlgebraicGroups.Specs.GeometricBorelConjugacy (IsKBorel subgroupOfSubgroup)
open _root_.LinearAlgebraicGroups.Specs.GeometricRadicals (IsSemisimple GeometricGroup
  IsSplitReductive baseChangedSubgroup geometricSolvableRadical IsSmoothConnectedNormal IsSolvableRadical)
open _root_.LinearAlgebraicGroups.Specs.QuasiSplitLocalGeneration (generatedByBorelRadicals)
open _root_.LinearAlgebraicGroups.Specs.QuasiSplitPinnedPairModel (BorelPair)
open _root_.LinearAlgebraicGroups.Specs.QuasiSplitOrbitAmbientWords (groundPointIso onRational)
open _root_.LinearAlgebraicGroups.Specs.RelativeRank (relativeRank)
open _root_.LinearAlgebraicGroups.Specs.SchemeDerivedGroup (IsSubgroupOf IsSolvable)
open _root_.LinearAlgebraicGroups.Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open _root_.LinearAlgebraicGroups.Specs.Unipotent (closedSubgroupAlgebraicGroup)
open private smooth_extend_iff from LinearAlgebraicGroups.RootData.BorelNormalizer
open private inclusion_mono from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private reductive_of_semisimple from LinearAlgebraicGroups.Classification.CentralIsogenies
open private terminalPointHom terminalSubgroup_mem from
  LinearAlgebraicGroups.Arithmetic.QuasiSplitLocalGeneration
open private splitBorelPair from LinearAlgebraicGroups.Classification.SimplyConnectedLattice

universe u

variable {F : Type u} [Field F] {G : AffineAlgebraicGroup F}

private theorem borelIsParabolic (hG : IsSemisimple G) (B : ClosedSubgroup G.val)
    (hB : IsKBorel B) : IsParabolic G B := by
  obtain ⟨h, hb⟩ := hB
  exact ⟨reductive_of_semisimple G hG,
    (smooth_extend_iff (AlgebraicClosure F) B.group.X).mp hb.1.1,
    h, _, hb, ⟨𝟙 _, Category.id_comp _⟩⟩

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem borelIsProper (hG : IsAbsolutelyAlmostSimple G) (B : ClosedSubgroup G.val)
    (hB : IsKBorel B) : ¬ IsIso B.inclusion := by
  intro hi
  let := hi
  obtain ⟨h, hB⟩ := hB
  let B' := baseChangedSubgroup (AlgebraicClosure F) B h
  have : IsIso B'.inclusion :=
    (groupBaseChange F (AlgebraicClosure F)).map_isIso B.inclusion
  have hBI : IsNormalSubgroup B'.inclusion := by
    refine ⟨subgroupConjugation B'.inclusion ≫ (inv B'.inclusion).hom.hom, ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, IsIso.inv_hom_id]
    exact Category.comp_id _
  let G' := GeometricGroup G
  let R : ClosedSubgroup G'.val := geometricSolvableRadical G
  have hR : IsSolvableRadical G' R :=
    _root_.LinearAlgebraicGroups.GeometricRadicals.geometricSolvableRadicalLargest G
  have hNorm : @IsSmoothConnectedNormal _ _ G' B' := ⟨hB.1.1, hB.1.2.1, hBI⟩
  have hSolv : IsSolvable (closedSubgroupAlgebraicGroup (G := G') B').val := hB.1.2.2
  have hSub : IsSubgroupOf B' R := hR.2.2 B' hNorm hSolv
  obtain ⟨f, hf⟩ := hSub
  let s : (GeometricGroup G).val ⟶ R.group := inv B'.inclusion ≫ f
  have hs : s ≫ R.inclusion = 𝟙 _ := by simp only [s, Category.assoc, hf, IsIso.inv_hom_id]
  let : Mono R.inclusion := inclusion_mono R
  have hs' : R.inclusion ≫ s = 𝟙 _ := by
    apply (cancel_mono R.inclusion).mp
    rw [Category.assoc, hs, Category.id_comp]
    exact Category.comp_id _
  obtain ⟨e⟩ := hG.1.2.2
  exact hG.2.1 ⟨(⟨s, R.inclusion, hs, hs'⟩ : (GeometricGroup G).val ≅ R.group) ≪≫ e⟩

set_option backward.isDefEq.respectTransparency false in
/-- The two rational Borel radicals give generation and positive rank in the
presence of an opposite rational Borel pair. -/
theorem radicalGenerationOfBorelPair [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (hG : IsAbsolutelyAlmostSimple G)
    (hsc : GeometricallySimplyConnected G) (M : BorelPair G) :
    letI := localPointTopology G
    0 < relativeRank G ∧ Dense (unipotentGenerated G : Set (𝟙_ (SchemeOver F) ⟶ G.val.X)) := by
  let := localPointTopology G
  have hpos := borelIsParabolic hG.1 M.positive M.positiveBorel
  have hneg := borelIsParabolic hG.1 M.negative M.negativeBorel
  have hrank := (_root_.LinearAlgebraicGroups.Descent.RelativeRank.semisimpleParabolicCriterion
    G hG.1).mp ⟨M.positive, hpos, borelIsProper hG M.positive M.positiveBorel⟩
  refine ⟨hrank, ?_⟩
  let p := terminalPointHom G.val
  have hp : Function.Injective p := fun _ _ h => (cancel_epi (groundPointIso F).inv).mp h
  have hasRadical (B : ClosedSubgroup G.val) (hB : IsParabolic G B)
      (U : ClosedSubgroup B.group)
      (hU : GeometricRadicals.IsUnipotentRadical (closedSubgroupAlgebraicGroup B) U) :
      (onRational (subgroupOfSubgroup B U).inclusion).range ≤ (unipotentGenerated G).map p := by
    intro y hy
    let x := (groundPointIso F).hom ≫ y
    have hxy : p x = y := (groundPointIso F).inv_hom_id_assoc y
    have hx : x ∈ SubgroupSections (subgroupOfSubgroup B U) (𝟙_ (SchemeOver F)) := by
      apply (terminalSubgroup_mem (subgroupOfSubgroup B U) x).mpr
      change p x ∈ _
      rw [hxy]
      exact hy
    have hle : SubgroupSections (subgroupOfSubgroup B U) (𝟙_ (SchemeOver F)) ≤
        unipotentGenerated G :=
      le_iSup_of_le B (le_iSup_of_le hB (le_iSup_of_le U (le_iSup_of_le hU le_rfl)))
    exact ⟨x, hle hx, hxy⟩
  have hgen : generatedByBorelRadicals M = ⊤ :=
    QuasiSplitLocalGeneration.quasiSplitLocalGeneration
      (Or.inl ⟨‹ValuativeRel F›, ‹TopologicalSpace F›, ‹IsNonarchimedeanLocalField F›⟩) G hG.1 hsc M
  have hle : generatedByBorelRadicals M ≤ (unipotentGenerated G).map p :=
    sup_le (hasRadical _ hpos _ M.positiveUnipotentRadical)
      (hasRadical _ hneg _ M.negativeUnipotentRadical)
  rw [hgen] at hle
  have he : unipotentGenerated G = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨y, hy, hyx⟩ := hle (show p x ∈ (⊤ : Subgroup _) from trivial)
    exact hp hyx ▸ hy
  rw [he, Subgroup.coe_top]
  exact dense_univ

/-- Split groups admit the rational Borel pair used for generation. -/
theorem radicalGenerationOfSplit [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (hG : IsAbsolutelyAlmostSimple G)
    (hsc : GeometricallySimplyConnected G) (hs : IsSplitReductive G) :
    letI := localPointTopology G
    0 < relativeRank G ∧ Dense (unipotentGenerated G : Set (𝟙_ (SchemeOver F) ⟶ G.val.X)) := by
  obtain ⟨T, hT, hmax⟩ := hs.2
  let P := splitBorelPair G hs.1 T hT hmax
  obtain ⟨A⟩ := _root_.LinearAlgebraicGroups.Classification.Pinning.additiveLineExists F
  obtain ⟨U, ⟨pin⟩⟩ := _root_.LinearAlgebraicGroups.Classification.Pinning.pinningsExist A P
  obtain ⟨M, _, _⟩ := QuasiSplitPinnedPairModel.splitOppositePair
    (⟨P, U, pin⟩ : _root_.LinearAlgebraicGroups.Specs.Pinning.PinnedGroup A)
  exact radicalGenerationOfBorelPair hG hsc M

end QuasiSplit

section InnerLevi

open AlgebraicGeometry CategoryTheory
open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open _root_.LinearAlgebraicGroups.Specs.Pinning (BasedRootDatum)
open _root_.LinearAlgebraicGroups.Specs.IntegralSemisimpleModel (Model)
open _root_.LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat (FieldPoints)
open _root_.LinearAlgebraicGroups.Specs.ExceptionalMarkedRootDescent (MarkedFibre)
open _root_.LinearAlgebraicGroups.Specs.ExceptionalInnerIndices (HasInnerIndex e6Black e7Black)
open _root_.LinearAlgebraicGroups.Specs.ExceptionalAffineRootSystems (exceptionalCartan)
open _root_.LinearAlgebraicGroups.Specs.RelativeRank (relativeRank)
open _root_.LinearAlgebraicGroups.Specs.GeometricRadicals (IsReductive)
open private dimension_of_iso standard_torus_dimension from
  LinearAlgebraicGroups.Descent.RelativeRank

universe u

/-- The maximal split torus supplied by the marked index has the stated rank
in the Krull dimension formulation. -/
theorem relativeRankOfMarkedIndex {F K : Type u} [Field F] [Field K] [Algebra F K]
    {H : AffineAlgebraicGroup F} {D : BasedRootDatum.{u}} {M : Model D} {n r : ℕ}
    {b : Fin n ≃ D.base.support} {black : Set (Fin n)}
    {C : MarkedFibre M K}
    {f : C.realization.pinned.pair.G.val ≅ (groupBaseChange F K).obj H.val}
    {normalizer : Set (FieldPoints M K)} (hG : IsReductive H)
    (h : HasInnerIndex b r black C f normalizer) :
    relativeRank H = (r : WithBot ℕ∞) := by
  obtain ⟨_, S, _, _, hS, ⟨e⟩, _, _, _⟩ := h.2
  exact ((Descent.RelativeRank.maximalSplitDimension H hG).2 S hS).symm.trans
    ((dimension_of_iso e).trans (standard_torus_dimension r))

/-- The A₅ chain left after omitting Bourbaki node 2. -/
def e6LeviChain : Fin 5 → Fin 6 := ![0, 2, 3, 4, 5]

/-- The A₅ component left after omitting Bourbaki node 3. -/
def e7LeviChain : Fin 5 → Fin 7 := ![1, 3, 4, 5, 6]

theorem e6LeviDiagram :
    Function.Injective e6LeviChain ∧
    (∀ i : Fin 6, i ∈ Set.range e6LeviChain ↔ i ≠ 1) ∧
    (∀ i j, exceptionalCartan 6 (e6LeviChain i) (e6LeviChain j) = CartanMatrix.A 5 i j) ∧
    (∀ i, e6LeviChain i ∈ e6Black ↔ i ≠ 2) := by
  unfold e6Black
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold Function.Injective
    decide +kernel
  · change ∀ i : Fin 6, (∃ j : Fin 5, e6LeviChain j = i) ↔ i ≠ 1
    decide +kernel
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · decide +kernel

theorem e7LeviDiagram :
    Function.Injective e7LeviChain ∧
    (∀ i : Fin 7, i ∈ Set.range e7LeviChain ↔ i ≠ 0 ∧ i ≠ 2) ∧
    (∀ i j, exceptionalCartan 7 (e7LeviChain i) (e7LeviChain j) = CartanMatrix.A 5 i j) ∧
    (∀ i, exceptionalCartan 7 0 (e7LeviChain i) = 0 ∧ exceptionalCartan 7 (e7LeviChain i) 0 = 0) ∧
    (∀ i, e7LeviChain i ∈ e7Black ↔ i ∈ ({0, 2, 4} : Set (Fin 5))) ∧
    (0 : Fin 7) ∉ e7Black := by
  unfold e7Black
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Function.Injective
    decide +kernel
  · change ∀ i : Fin 7, (∃ j : Fin 5, e7LeviChain j = i) ↔ i ≠ 0 ∧ i ≠ 2
    decide +kernel
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

end InnerLevi

universe u

section FormCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

open _root_.LinearAlgebraicGroups.Specs
open Specs.ExceptionalLocalRadicalGeneration
open Specs.ExceptionalAffineBruhat (ExceptionalNumbering RamifiedReference)
open Specs.ExceptionalAffineRootSystems (exceptionalCartan restrictedRoot)
open Specs.ExceptionalFormsOverUnramifiedFields (HasTypeE)
open Specs.ExceptionalInnerIndices (IsSplitOfRank e6Black e7Black)
open Specs.ExceptionalInnerStandardTorusDescent (markedCharacter)
open Specs.ExceptionalLocalFormClassification (SplitReference AgreesWithInnerForms HasMarkedInnerIndex HasOuterRepresentative)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre)
open Specs.GeometricRadicals (IsSplitReductive GeometricGroup IsSemisimple)
open Specs.IntegralSemisimpleModel (Model)
open Specs.Pinning (AttachedDatum BasedRootDatum SplitBorelPair)
open Specs.QuasiSplitPinnedPairModel (BorelPair)
open Specs.RelativeRank (relativeRank)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected corootLattice)
open Specs.CharacterDescent (Character)
open Specs.QuasiSplitInnerForms (basedAutTopology fieldGalTopology AreInnerForms)
open _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology (restriction)
open _root_.LinearAlgebraicGroups.Descent.PinnedPairDescent (pinnedPairDescent)

open private simpleVerticesOfBasedIso from
  LinearAlgebraicGroups.Arithmetic.QuasiSplitLocalGeneration
open private exceptionalCartan_eq from LinearAlgebraicGroups.Arithmetic.ExceptionalStableAlcoves
open private referenceType from LinearAlgebraicGroups.Arithmetic.ExceptionalLocalFormClassification
open private schemeIsoEquiv from LinearAlgebraicGroups.Descent.RelativeFormComparison
open private groupBaseChangeTower from LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private simplyConnected_of_geometricIso semisimple_of_geometricIso from
  LinearAlgebraicGroups.Arithmetic.MatrixFactorSplitRank
open private latticeCriterion_pair from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private compareMarkedRepresentative from LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalMarkedAdjoint

attribute [local instance] basedAutTopology fieldGalTopology

noncomputable section

variable {F : Type u} [Field F] {G : AffineAlgebraicGroup F} {n : ℕ}

local notation "Fsep" => SeparableClosure F

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The two descriptions of absolute almost simplicity use the same geometric
group and the same smooth connected normal subgroups. -/
theorem absoluteAlmostSimpleForClassification
    (h : Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple G) :
    Specs.AbsoluteDynkinTypes.IsAbsolutelyAlmostSimple G := by
  refine ⟨h.1, fun z => h.2.1 ⟨z.iso (Grp.isZero_trivial _)⟩, ?_⟩
  intro N hN
  rcases h.2.2 N hN with hN₀ | hi
  · obtain ⟨e⟩ := hN₀
    exact .inl ((Grp.isZero_trivial _).of_iso e)
  · exact .inr hi

set_option backward.isDefEq.respectTransparency false in
theorem innerTypeOfReference {P : SplitBorelPair Fsep} {D : AttachedDatum P}
    {b : Fin n ≃ D.toBased.base.support}
    {g : P.G.val ≅ (groupBaseChange F Fsep).obj G.val}
    (R : SplitReference G D b g) (hR : AgreesWithInnerForms R)
    (hn : n = 6 ∨ n = 7 ∨ n = 8)
    (hG : IsSemisimple G) (hsc : GeometricallySimplyConnected G) :
    Specs.ExceptionalLocalFormClassification.IsInner R ↔ IsInnerTypeE G n := by
  constructor
  · intro hi
    exact ⟨R.line, R.pinned, R.attached,
      referenceType R hn, hR.1.mp hi⟩
  · rintro ⟨A, Q, E, hE, hInner⟩
    have hForm := hInner
    obtain ⟨_, _, _, _, i, _⟩ := hForm
    let S := Fsep
    let L := AlgebraicClosure F
    let f := (schemeIsoEquiv S Q.pair.G.val G.val).symm i
    let e : (GeometricGroup G).val ≅ (GeometricGroup Q.pair.G).val :=
      (groupBaseChangeTower (K := S) L).app G.val ≪≫
        (groupBaseChange S L).mapIso f.symm ≪≫
          ((groupBaseChangeTower (K := S) L).app Q.pair.G.val).symm
    have hs := semisimple_of_geometricIso e hG Q.pair.reductive
    have hscQ := simplyConnected_of_geometricIso e hsc
    have hEfull : corootLattice E = ⊤ :=
      (latticeCriterion_pair Classification.IntegralRealization.integralRealization Q.pair E hs).mp hscQ
    obtain ⟨_, _, _, _, _, _, _, h⟩ := hR.2 A Q E hEfull hE
    exact h.mpr hInner

/-- A marked chart gives the adapted Borel used for the exceptional roots. -/
def adaptedBorelOfMarked {D : BasedRootDatum.{u}} {M : Model D}
    {C : MarkedFibre M Fsep} (A : Specs.ExceptionalAdaptedRootCoordinates.AdaptedBorel G C)
    (b : Fin n ≃ D.base.support) (hb : ExceptionalNumbering D n b) : AdaptedBorel G n where
  S := A.S
  maximalSplit := A.maximalSplit
  T := A.T
  maximalTorus := A.maximalTorus
  intoTorus := A.intoTorus
  intoTorus_eq := A.intoTorus_eq
  J := A.J
  minimalParabolic := A.minimalParabolic
  torusInParabolic := ⟨A.intoParabolic, A.intoParabolic_eq⟩
  P := C.realization.pinned.pair
  D := C.realization.attached
  numbering := b.trans (simpleVerticesOfBasedIso (asIso C.realization.datumIso))
  cartan_eq i j :=
    C.realization.datumIso.val.toHom.pairing.trans (hb.2 i j)
  ambient := A.ambient
  torus := A.torus
  torus_eq := A.torus_eq
  borel := A.borel
  borel_eq := A.borel_eq
  multiplicative := A.multiplicative
  multiplicative_eq := A.multiplicative_eq

@[simp] theorem adaptedBorelOfMarked_restriction {D : BasedRootDatum.{u}} {M : Model D}
    {C : MarkedFibre M Fsep} (A : Specs.ExceptionalAdaptedRootCoordinates.AdaptedBorel G C)
    (b : Fin n ≃ D.base.support) (hb : ExceptionalNumbering D n b) (i : Fin n) :
    (adaptedBorelOfMarked A b hb).restrictAbsolute ((adaptedBorelOfMarked A b hb).numbering i).val.val =
      A.restrictSimple (b i) := by
  exact Category.assoc _ _ _

/-- The simple-root restrictions in the actual adapted chart. -/
abbrev HasSimpleRestrictions (A : AdaptedBorel G n) {r : ℕ}
    (project : (Fin n → ℤ) → (Fin r → ℤ)) : Prop :=
  ∃ encode : Multiplicative (Fin r → ℤ) →* Character A.S.group,
    Function.Injective encode ∧ ∀ i,
      A.restrictAbsolute (A.numbering i).val.val =
        A.extendRelative (encode (Multiplicative.ofAdd (project (Pi.single i 1))))

theorem simpleRestrictionsOfMarked {D : BasedRootDatum.{u}} {M : Model D}
    {C : MarkedFibre M Fsep} (A : Specs.ExceptionalAdaptedRootCoordinates.AdaptedBorel G C)
    (b : Fin n ≃ D.base.support) (hb : ExceptionalNumbering D n b) {r : ℕ}
    {project : (Fin n → ℤ) → (Fin r → ℤ)}
    (hc : Specs.ExceptionalAdaptedRootCoordinates.HasRootCoordinates A b project) :
    HasSimpleRestrictions (adaptedBorelOfMarked A b hb) project :=
  let ⟨e, hinj, h⟩ := hc
  ⟨e, hinj, fun i => (adaptedBorelOfMarked_restriction A b hb i).trans (h i)⟩

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

set_option maxHeartbeats 1400000 in
set_option backward.isDefEq.respectTransparency false in
theorem adaptedBorelOfInnerIndex {P : SplitBorelPair Fsep} {D : AttachedDatum P}
    {b : Fin n ≃ D.toBased.base.support}
    {g : P.G.val ≅ (groupBaseChange F Fsep).obj G.val}
    (R : SplitReference G D b g) {r : ℕ} {black : Set (Fin n)}
    {project : (Fin n → ℤ) → (Fin r → ℤ)}
    (coords : Specs.ExceptionalAdaptedRootCoordinates.InnerCoordinates.{u} n r black project)
    (h : HasMarkedInnerIndex R r black) :
    ∃ A : AdaptedBorel G n, IsSplitOfRank A.S.group r ∧ relativeRank G = r ∧
      (∀ i, A.restrictAbsolute (A.numbering i).val.val = 1 ↔ i ∈ black) ∧
      HasSimpleRestrictions A project := by
  obtain ⟨K, _, _, _, _, _, M, _, _, _, Y, _, _, _, _, _, a₀, a, T, σ, jG,
    _, _, _, _, j, f, _, _, hindex⟩ := h
  have hb := M.scNumbering_eq
  obtain ⟨e, he⟩ := coords F K Y.sc_fibre M.scNumbering hb
      (f ≪≫ (groupBaseChange F K).mapIso jG) Y.sc.N (fun w hw => (Y.sc_points.1 w).mp hw) hindex
  let : Algebra K Fsep := e.toRingHom.toAlgebra
  obtain ⟨C, A, _, _, _, _, _, _, _, hs, hr, hbBlack, hroot⟩ := he
  refine ⟨adaptedBorelOfMarked A M.scNumbering hb, hs, hr, ?_, simpleRestrictionsOfMarked A _ _ hroot⟩
  intro i
  rw [adaptedBorelOfMarked_restriction]
  exact (hbBlack i).symm

set_option maxHeartbeats 1800000 in
set_option backward.isDefEq.respectTransparency false in
theorem adaptedBorelOfOuterRepresentative {P : SplitBorelPair Fsep} {D : AttachedDatum P}
    {b : Fin 6 ≃ D.toBased.base.support}
    {g : P.G.val ≅ (groupBaseChange F Fsep).obj G.val}
    (R : SplitReference G D b g) (h : HasOuterRepresentative R rfl) :
    ∃ A : AdaptedBorel G 6, Nonempty (BorelPair G) ∧ relativeRank G = 4 ∧
      HasSimpleRestrictions A restrictedRoot := by
  obtain ⟨L, _, _, _, _, ωL, h₂, hω, _, hAction, ω, V, jG, _, hdesc⟩ := h
  let B := R.attached.toBased
  obtain ⟨M⟩ := Classification.IntegralRealization.integralRealization B
  obtain ⟨C⟩ := RamifiedExceptionalMarkedAdjoint.markedFibreExists M F
  let d : B ≅ C.realization.attached.toBased :=
    (Groupoid.isoEquivHom B C.realization.attached.toBased).symm C.realization.datumIso
  obtain ⟨l, Q, ⟨E⟩⟩ := RamifiedExceptionalMarkedAdjoint.splitSequenceForAttachedDatum C.realization.attached
  let ω' := (Aut.autMulEquivOfIso d).toMonoidHom.comp ωL
  obtain ⟨W⟩ := pinnedPairDescent (K := (L : Type u)) E ω'
  let Mref : RamifiedReference F L M := ⟨C, l, Q, E, ω', W⟩
  obtain ⟨j⟩ := compareMarkedRepresentative L R.sequence E d ωL ω (fun σ => (hdesc σ).2) V W
  have hDiagram (σ : Gal(L/F)) : Mref.diagram σ = (ωL σ).asIso.hom := by
    change ((Aut.autMulEquivOfIso d.symm) ((Aut.autMulEquivOfIso d) (ωL σ))).asIso.hom = _
    rw [show Aut.autMulEquivOfIso d.symm = (Aut.autMulEquivOfIso d).symm from rfl,
      MulEquiv.symm_apply_apply]
  have hd :
      ∃ (σ : Gal(L/F)) (i : Fin 6), Specs.ExceptionalValuedTorusNormalizer.simplePermutationHom B
        (Specs.ExceptionalValuedTorusNormalizer.markedDiagramEquiv Mref.fibre.realization (Mref.outer σ))
        (R.numbering i) ≠ R.numbering i := by
    obtain ⟨σ, hσ⟩ : ∃ σ : Gal(L/F), σ ≠ 1 := by
      by_contra! hAll
      apply hω
      apply MonoidHom.ext
      intro t
      rw [hAll t]
      exact map_one ωL
    refine ⟨σ, 0, ?_⟩
    intro hfix
    have he : (Mref.diagram σ).val.indexEquiv (R.numbering 0).val = (R.numbering 0).val :=
      congrArg Subtype.val hfix
    rw [hDiagram, hAction σ hσ] at he
    have h0 : (Specs.SteinbergPinnedDescent.e6Involution (0 : Fin 6)) ≠ 0 := by decide
    exact h0 (R.numbering.injective (Subtype.ext he))
  obtain ⟨a, ha⟩ := ExceptionalAdaptedRootCoordinates.outerCoordinates F L Mref
    R.numbering R.numbered hd (j ≪≫ jG)
  let : Algebra L Fsep := a.toRingHom.toAlgebra
  obtain ⟨C', A, O, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hr, hc⟩ := ha
  exact ⟨adaptedBorelOfMarked A _ R.numbered, ⟨O⟩, hr,
    simpleRestrictionsOfMarked A _ R.numbered hc⟩

end
end FormCharts

section RootAssembly

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

open _root_.LinearAlgebraicGroups.Specs
open Specs.ExceptionalAffineRootSystems (exceptionalCartan IsRootCoordinate restrictedRoot)
open Specs.ExceptionalLocalRadicalGeneration
open Specs.ExceptionalSingletonRootSL2 (MarkedTori HasSingletonRootLine RationalReflection)
open Specs.AbstractPairing (Root)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CentralIsogenies (characterPullback)
open Specs.GeometricRadicals (IsSemisimple)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.RootGroups (Proportional)

open private extendCharacter from LinearAlgebraicGroups.Arithmetic.ExceptionalRootGroupDescent
open private oppositeRoot oppositeRoot_character from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitDerivedRoots
open private preservesUnits_unique from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitLevis

noncomputable section

variable {F : Type u} [Field F] {G : AffineAlgebraicGroup F} {n r : ℕ}

set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

private abbrev markedToriOf (A : AdaptedBorel G n) : MarkedTori G where
  S := A.S
  maximalSplit := A.maximalSplit
  T := A.T
  maximalTorus := A.maximalTorus
  intoTorus := A.intoTorus
  intoTorus_eq := A.intoTorus_eq
  P := A.P
  datum := A.D
  ambient := A.ambient
  torus := A.torus
  torus_eq := A.torus_eq

private def splitRootSL2OfMarked (A : AdaptedBorel G n) {a : Root A.P.T}
    (H : Specs.ExceptionalSingletonRootSL2.SplitRootSL2 (markedToriOf A) a) :
    SplitRootSL2 A a where
  subgroup := H.subgroup
  matrix := H.matrix
  positive := H.positive
  negative := H.negative
  positive_eq := H.positive_eq
  negative_eq := H.negative_eq
  positiveAbsolute := H.positiveAbsolute
  negativeAbsolute := H.negativeAbsolute
  positiveIso := H.positiveIso
  negativeIso := H.negativeIso
  positiveInclusion := H.positiveInclusion
  negativeInclusion := H.negativeInclusion
  positiveRoot := H.positiveRoot
  negativeRoot := H.negativeRoot
  diagonal := H.diagonal
  diagonal_eq := H.diagonal_eq
  coroot := H.coroot
  diagonalInAmbient := H.diagonalInAmbient
  coroot_eq := by
    have h := (preservesUnits_unique _ A.multiplicative_eq).trans
      (preservesUnits_unique _ H.multiplicative_eq).symm
    rw [h]
    exact H.coroot_eq

private def e6InnerRestriction : (Fin 6 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) where
  toFun := e6InnerProjection
  map_add' v w := by ext i; fin_cases i <;> rfl
  map_smul' a v := by ext i; fin_cases i <;> rfl

private def e7InnerRestriction : (Fin 7 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ) where
  toFun := e7InnerProjection
  map_add' v w := by ext i; fin_cases i <;> rfl
  map_smul' a v := by ext i; fin_cases i <;> rfl

private def e6OuterRestriction : (Fin 6 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ) where
  toFun := restrictedRoot
  map_add' v w := by ext i; fin_cases i <;> simp [restrictedRoot, add_add_add_comm]
  map_smul' a v := by ext i; fin_cases i <;> simp [restrictedRoot, mul_add]

private theorem exceptionalCartan_symmetric (n : ℕ) : (exceptionalCartan n).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, exceptionalCartan, eq_comm (a := j),
    Finset.pair_comm j.val i.val]

private theorem sum_single_coordinates (v : Fin n → ℤ) :
    (∑ i, v i • (Pi.single i 1 : Fin n → ℤ)) = v := by
  classical
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

/-- A character comparison on the simple roots determines the comparison
on every root by its integral simple-root expansion. -/
theorem rootRestrictionsOfSimpleRestrictions (A : AdaptedBorel G n)
    (project : (Fin n → ℤ) →ₗ[ℤ] (Fin r → ℤ))
    (coeff : Root A.P.T ≃ {v // IsRootCoordinate (exceptionalCartan n) v})
    (encode : Multiplicative (Fin r → ℤ) →* Character A.S.group)
    (hCoeff : ∀ a, A.D.toBased.datum.root a =
      ∑ j, (coeff a).val j • A.D.toBased.datum.root (A.numbering j))
    (hSimple : ∀ i, A.restrictAbsolute (A.numbering i).val.val =
      A.extendRelative (encode (Multiplicative.ofAdd (project (Pi.single i 1))))) :
    ∀ a, A.restrictAbsolute a.val =
      A.extendRelative (encode (Multiplicative.ofAdd (project (coeff a).val))) := by
  let := A.D.comm
  let R := (characterPullback A.splitInAbsolute).toAdditive.toIntLinearMap
  let E := ((extendCharacter A.multiplicative A.S.group).comp encode).toAdditive.toIntLinearMap
  have h (i : Fin n) :
      R (A.D.toBased.datum.root (A.numbering i)) = E (project (Pi.single i 1)) := by
    change R (A.D.datum.rootDatum.root _) = _
    rw [A.D.datum.root_eq]
    exact congrArg Additive.ofMul (hSimple i)
  intro a
  apply Additive.ofMul.injective
  change R (Additive.ofMul a.val) = E (project (coeff a).val)
  rw [← A.D.datum.root_eq a]
  change R (A.D.toBased.datum.root a) = _
  calc
    _ = ∑ i, (coeff a).val i • E (project (Pi.single i 1)) := by
      rw [hCoeff, map_sum]
      simp only [map_zsmul, h]
    _ = _ := by
      conv_rhs => rw [← sum_single_coordinates (coeff a).val]
      simp only [map_sum, map_zsmul]

private theorem singletonLineOfProjection (A : AdaptedBorel G n)
    (project : (Fin n → ℤ) →ₗ[ℤ] (Fin r → ℤ)) {count : ℕ} {node : Fin n} {highest : Fin n → ℤ}
    (calculation : ProjectedRootCoordinates project count node highest)
    (coeff : Root A.P.T ≃ {v // IsRootCoordinate (exceptionalCartan n) v})
    (encode : Multiplicative (Fin r → ℤ) →* Character A.S.group)
    (hEncode : Function.Injective encode)
    (hRestrict : ∀ a, A.restrictAbsolute a.val =
      A.extendRelative (encode (Multiplicative.ofAdd (project (coeff a).val))))
    (α : Root A.P.T) (hα : project (coeff α).val ≠ 0)
    (unique : ∀ v, IsRootCoordinate (exceptionalCartan n) v →
      project v = project (coeff α).val → v = (coeff α).val) :
    HasSingletonRootLine (markedToriOf A) α := by
  let E := (extendCharacter A.multiplicative A.S.group).comp encode
  have hE : Function.Injective E := (adaptedRelativeRootRestrictions A).1.comp hEncode
  have hR (a : Root A.P.T) :
      (markedToriOf A).restrict a.val = E (Multiplicative.ofAdd (project (coeff a).val)) :=
    hRestrict a
  have hnonzero (a : Root A.P.T) :
      (markedToriOf A).restrict a.val ≠ 1 ↔ project (coeff a).val ≠ 0 := by
    rw [hR, ← E.map_one]
    exact not_congr ⟨fun h => congrArg Multiplicative.toAdd (hE h), fun h =>
      congrArg (E ∘ Multiplicative.ofAdd) h⟩
  have hmem (a : Root A.P.T) (ha : project (coeff a).val ≠ 0) :
      project (coeff a).val ∈ projectedRoots project :=
    ⟨⟨(coeff a).val, (coeff a).property, rfl⟩, ha⟩
  have same (a : Root A.P.T) (he : project (coeff a).val = project (coeff α).val) :
      a = α := coeff.injective (Subtype.ext (unique _ (coeff a).property he))
  refine ⟨(hnonzero α).mpr hα, ?_⟩
  rintro β hβ ⟨m, q, hm, _, he⟩
  rw [hR, hR] at he
  have he' : E (Multiplicative.ofAdd (project (coeff α).val) ^ m) =
      E (Multiplicative.ofAdd (project (coeff β).val) ^ q) := by
    simpa only [map_zpow] using he
  have h := congrArg Multiplicative.toAdd (hE he')
  change m • project (coeff α).val = q • project (coeff β).val at h
  rcases calculation.reduced _ (hmem α hα) _ (hmem β ((hnonzero β).mp hβ)) hm h with hEq | hNeg
  · exact .inl (congrArg Subtype.val (same β hEq))
  · let a := oppositeRoot A.D β
    have ha : a.val = β.val⁻¹ := oppositeRoot_character A.D β
    have hsa : project (coeff a).val = project (coeff α).val := by
      apply (hE.comp Multiplicative.ofAdd.injective)
      rw [Function.comp_apply, Function.comp_apply, ← hR a, ha]
      let f := characterPullback A.splitInAbsolute
      change f (β.val⁻¹) = _
      rw [map_inv]
      change ((markedToriOf A).restrict β.val)⁻¹ = _
      rw [hR β, hNeg]
      change (E ((Multiplicative.ofAdd (project (coeff α).val))⁻¹))⁻¹ = _
      rw [map_inv, inv_inv]
    right
    have hf : α.val = β.val⁻¹ := congrArg Subtype.val (same a hsa).symm |>.trans ha
    rw [hf, inv_inv]

private theorem reflectionCoordinates (A : AdaptedBorel G n)
    (coeff : Root A.P.T ≃ {v // IsRootCoordinate (exceptionalCartan n) v})
    (hRoot : ∀ a, A.D.toBased.datum.root a =
      ∑ j, (coeff a).val j • A.D.toBased.datum.root (A.numbering j))
    (hCoroot : ∀ a, A.D.toBased.datum.coroot a =
      ∑ j, (coeff a).val j • A.D.toBased.datum.coroot (A.numbering j))
    (a b : Root A.P.T) :
    (coeff (A.D.toBased.datum.reflectionPerm a b)).val =
      (coeff b).val - dotProduct (coeff b).val ((exceptionalCartan n).mulVec (coeff a).val) •
        (coeff a).val := by
  let D := A.D.toBased.datum
  let e : (Fin n → ℤ) →ₗ[ℤ] A.D.toBased.X :=
    Fintype.linearCombination ℤ (fun j => D.root (A.numbering j))
  have hInj : Function.Injective e :=
    linearIndependent_iff_injective_fintypeLinearCombination.mp
      (A.D.toBased.base.linearIndepOn_root.comp A.numbering A.numbering.injective)
  have hE (i : Root A.P.T) : e (coeff i).val = D.root i := (hRoot i).symm
  have hpair : D.pairing b a =
      dotProduct (coeff b).val ((exceptionalCartan n).mulVec (coeff a).val) := by
    let v := (coeff b).val
    let w := (coeff a).val
    change D.toLinearMap (D.root b) (D.coroot a) = dotProduct v ((exceptionalCartan n).mulVec w)
    rw [hRoot b, hCoroot a]
    change D.toLinearMap (∑ i, v i • D.root (A.numbering i))
      (∑ j, w j • D.coroot (A.numbering j)) = _
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      RootPairing.root_coroot_eq_pairing, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    change w j * (v i * A.D.toBased.datum.pairing (A.numbering i) (A.numbering j)) = _
    rw [A.cartan_eq]
    ac_rfl
  apply hInj
  rw [hE, map_sub, map_smul, hE, hE, ← hpair, D.root_reflectionPerm, D.reflection_apply_root]

end
end RootAssembly

section RootConjugation

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

open _root_.LinearAlgebraicGroups.Specs
open Specs.ExceptionalAffineRootSystems (exceptionalCartan IsRootCoordinate)
open Specs.ExceptionalLocalRadicalGeneration
open Specs.ExceptionalSingletonRootSL2 (MarkedTori HasSingletonRootLine RationalReflection)
open Specs.AbstractPairing (Root)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CentralIsogenies (characterPullback)
open Specs.GeometricBorelConjugacy (ConjugatesSubgroups)
open Specs.GeometricRadicals (IsSemisimple)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.RootGroups (HasScalarAction IsRootSubgroup)
open Specs.Pinning (RootCoordinate)

open private conjugation conjugationIso comp_conjugation conjugates_iff_iso
  from LinearAlgebraicGroups.Descent.FiniteFieldFlags
open private conjugationIso_natural from LinearAlgebraicGroups.Arithmetic.ExceptionalInnerStandardTorusDescent
open private markedSplitIncl transportedRootCoordinate
  from LinearAlgebraicGroups.Arithmetic.ExceptionalSingletonRootSL2
open private subgroupOf_mutual_iso from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private transportSubgroup inclusion_mono from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private oppositeRoot oppositeRoot_character from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitDerivedRoots

noncomputable section

variable {F : Type u} [Field F] {G : AffineAlgebraicGroup F} {n r : ℕ}

local notation "Fsep" => SeparableClosure F

set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

private theorem conjugationIso_mul {H : GroupScheme F} (a b : 𝟙_ (SchemeOver F) ⟶ H.X) :
    (conjugationIso a).hom ≫ (conjugationIso b).hom = (conjugationIso (b * a)).hom := by
  apply Grp.hom_ext
  change conjugation a ≫ conjugation b = conjugation (b * a)
  rw [comp_conjugation]
  simp only [conjugation, MonObj.comp_mul, mul_inv_rev]
  group

private theorem conjugationIso_one (H : GroupScheme F) :
    (conjugationIso (1 : 𝟙_ (SchemeOver F) ⟶ H.X)).hom = 𝟙 _ := by
  apply Grp.hom_ext
  change conjugation (1 : 𝟙_ (SchemeOver F) ⟶ H.X) = 𝟙 _
  simp [conjugation]

private theorem scalarConjugation {K : Type u} [Field K] [Algebra F K]
    {H : GroupScheme F} (w : 𝟙_ (SchemeOver F) ⟶ H.X) :
    (groupBaseChange F K).map (conjugationIso w).hom =
      (conjugationIso (scalarExtendedRationalPoint K w)).hom := by
  apply Grp.hom_ext
  let E := baseChange F K
  have hw : E.map (toUnit H.X ≫ w) =
      toUnit (E.obj H.X) ≫ scalarExtendedRationalPoint K w := by
    rw [E.map_comp, scalarExtendedRationalPoint, ← Category.assoc, Functor.Monoidal.toUnit_ε]
  change E.map (conjugation (G := H) w) =
    conjugation (G := (groupBaseChange F K).obj H) (scalarExtendedRationalPoint K w)
  simp only [conjugation, E.map_mul, E.map_inv', E.map_id, hw]
  rfl

private theorem absolutePoint_mul (A : AdaptedBorel G n)
    (v w : 𝟙_ (SchemeOver F) ⟶ G.val.X) :
    (markedToriOf A).absolutePoint (v * w) =
      (markedToriOf A).absolutePoint v * (markedToriOf A).absolutePoint w := by
  simp only [Specs.ExceptionalSingletonRootSL2.MarkedTori.absolutePoint, scalarExtendedRationalPoint,
    Functor.map_mul, MonObj.comp_mul, MonObj.mul_comp]

private theorem absolutePoint_one (A : AdaptedBorel G n) :
    (markedToriOf A).absolutePoint 1 = 1 := by
  simp only [Specs.ExceptionalSingletonRootSL2.MarkedTori.absolutePoint, scalarExtendedRationalPoint,
    Functor.map_one, MonObj.comp_one, MonObj.one_comp]

/-- A rational normalizer point with its compatible actions on both tori. -/
private structure MarkedConjugation (A : AdaptedBorel G n) where
  point : 𝟙_ (SchemeOver F) ⟶ G.val.X
  split : A.S.group ≅ A.S.group
  absolute : A.P.T.group ≅ A.P.T.group
  split_eq : split.hom ≫ A.S.inclusion = A.S.inclusion ≫ (conjugationIso point).hom
  absolute_eq : absolute.hom ≫ A.P.T.inclusion =
    A.P.T.inclusion ≫ (conjugationIso ((markedToriOf A).absolutePoint point)).hom

private def MarkedConjugation.refl (A : AdaptedBorel G n) : MarkedConjugation A where
  point := 1
  split := Iso.refl _
  absolute := Iso.refl _
  split_eq := by simp [conjugationIso_one]
  absolute_eq := by simp [absolutePoint_one, conjugationIso_one]

private def MarkedConjugation.trans {A : AdaptedBorel G n} (a b : MarkedConjugation A) :
    MarkedConjugation A where
  point := b.point * a.point
  split := a.split ≪≫ b.split
  absolute := a.absolute ≪≫ b.absolute
  split_eq := by
    simp only [Iso.trans_hom, Category.assoc, b.split_eq, reassoc_of% a.split_eq, conjugationIso_mul]
  absolute_eq := by
    simp only [Iso.trans_hom, Category.assoc, b.absolute_eq, reassoc_of% a.absolute_eq,
      absolutePoint_mul, conjugationIso_mul]

private def markedConjugationOfReflection {A : AdaptedBorel G n} {α : Root A.P.T}
    {H : Specs.ExceptionalSingletonRootSL2.SplitRootSL2 (markedToriOf A) α}
    (w : RationalReflection H) : MarkedConjugation A where
  point := w.representative ≫ H.subgroup.inclusion.hom.hom
  split := w.splitConjugation
  absolute := w.absoluteConjugation
  split_eq := by
    apply Grp.hom_ext
    change (w.splitConjugation.hom ≫ A.S.inclusion).hom.hom =
      A.S.inclusion.hom.hom ≫ conjugation _
    rw [comp_conjugation]
    simpa only [Category.assoc] using w.splitConjugates
  absolute_eq := by
    apply Grp.hom_ext
    change (w.absoluteConjugation.hom ≫ A.P.T.inclusion).hom.hom =
      A.P.T.inclusion.hom.hom ≫ conjugation _
    rw [comp_conjugation]
    exact w.absoluteConjugates

private theorem MarkedConjugation.ambient_eq {A : AdaptedBorel G n} (w : MarkedConjugation A) :
    (conjugationIso ((markedToriOf A).absolutePoint w.point)).hom ≫ A.ambient.hom =
      A.ambient.hom ≫ (groupBaseChange F Fsep).map (conjugationIso w.point).hom := by
  rw [scalarConjugation]
  have h : (markedToriOf A).absolutePoint w.point ≫ A.ambient.hom.hom.hom =
      scalarExtendedRationalPoint Fsep w.point := by
    change (_ ≫ A.ambient.inv.hom.hom) ≫ A.ambient.hom.hom.hom = _
    rw [Category.assoc, ← Grp.comp_hom_hom, A.ambient.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  rw [conjugationIso_natural, h]

private theorem MarkedConjugation.onSplitInAbsolute {A : AdaptedBorel G n} (w : MarkedConjugation A) :
    (groupBaseChange F Fsep).map w.split.hom ≫ A.splitInAbsolute =
      A.splitInAbsolute ≫ w.absolute.hom := by
  let E := groupBaseChange F Fsep
  have hi : A.splitInAbsolute ≫ A.P.T.inclusion ≫ A.ambient.hom = E.map A.S.inclusion :=
    markedSplitIncl (markedToriOf A)
  letI := inclusion_mono A.P.T
  apply (cancel_mono (A.P.T.inclusion ≫ A.ambient.hom)).mp
  simp only [Category.assoc, reassoc_of% w.absolute_eq, w.ambient_eq, hi, reassoc_of% hi]
  rw [← E.map_comp, w.split_eq, E.map_comp]

/-- The character and coroot of the destination root are transported by the
same marked conjugation. -/
private structure MovesRoot {A : AdaptedBorel G n} (w : MarkedConjugation A)
    (a b : Root A.P.T) : Prop where
  character : w.absolute.inv ≫ a.val = b.val
  coroot : (A.D.toBased.datum.coroot a).toMul ≫ w.absolute.hom =
    (A.D.toBased.datum.coroot b).toMul

private theorem MovesRoot.trans {A : AdaptedBorel G n} {u v : MarkedConjugation A}
    {a b c : Root A.P.T} (h : MovesRoot u a b) (j : MovesRoot v b c) :
    MovesRoot (u.trans v) a c := by
  constructor
  · change (v.absolute.inv ≫ u.absolute.inv) ≫ a.val = c.val
    rw [Category.assoc, h.character, j.character]
  · change _ ≫ (u.absolute.hom ≫ v.absolute.hom) = _
    rw [← Category.assoc, h.coroot, j.coroot]

private theorem movesRootByReflection {A : AdaptedBorel G n} {α : Root A.P.T}
    {H : Specs.ExceptionalSingletonRootSL2.SplitRootSL2 (markedToriOf A) α}
    (w : RationalReflection H) (b : Root A.P.T) :
    MovesRoot (markedConjugationOfReflection w) b (A.D.toBased.datum.reflectionPerm α b) := by
  letI := A.D.comm
  let P := A.D.toBased.datum
  constructor
  · apply Additive.ofMul.injective
    change Additive.ofMul (w.absoluteConjugation.inv ≫ b.val) =
      Additive.ofMul (P.reflectionPerm α b).val
    rw [w.characterReflection]
    change P.reflection α (Additive.ofMul b.val) = Additive.ofMul (P.reflectionPerm α b).val
    calc
      _ = P.reflection α (P.root b) := congrArg (P.reflection α) (A.D.datum.root_eq b).symm
      _ = P.root (P.reflectionPerm α b) := (P.root_reflectionPerm α b).symm
      _ = _ := A.D.datum.root_eq _
  · apply Additive.ofMul.injective
    change Additive.ofMul ((P.coroot b).toMul ≫ w.absoluteConjugation.hom) =
      P.coroot (P.reflectionPerm α b)
    rw [w.cocharacterReflection, P.coroot_reflectionPerm]
    rfl

private theorem transportMarkedRoot (A : AdaptedBorel G n) (w : MarkedConjugation A)
    (U : ClosedSubgroup A.P.G.val) (a : Root A.P.T)
    (h : IsRootSubgroup A.P.T U a.val) :
    IsRootSubgroup A.P.T
      (transportSubgroup (conjugationIso ((markedToriOf A).absolutePoint w.point)) U)
      (w.absolute.inv ≫ a.val) := by
  obtain ⟨V, _, _, _, ⟨L, x, hx⟩, hu⟩ :=
    (RootData.RootGroups.rootSubgroups A.P.G A.P.reductive A.P.T A.P.split A.P.maximal).2
      a.val a.property |>.2.2
  obtain ⟨j, hj⟩ := subgroupOf_mutual_iso (hu U h).1 (hu U h).2
  have hj' : HasScalarAction A.P.T a.val ((x ≪≫ j).hom ≫ U.inclusion) := by
    simpa only [Iso.trans_hom, Category.assoc, hj] using hx
  exact (transportedRootCoordinate h (⟨x ≪≫ j, hj'⟩ : RootCoordinate L A.P.T U a.val)
    (conjugationIso ((markedToriOf A).absolutePoint w.point)) w.absolute w.absolute_eq.symm).1

private theorem movesRootRestriction {A : AdaptedBorel G n} {w : MarkedConjugation A}
    {a b : Root A.P.T} (h : MovesRoot w a b) :
    (groupBaseChange F Fsep).map w.split.hom ≫ A.restrictAbsolute b.val =
      A.restrictAbsolute a.val := by
  have he : w.absolute.hom ≫ b.val = a.val := by
    rw [← h.character, Iso.hom_inv_id_assoc]
  rw [AdaptedBorel.restrictAbsolute, ← Category.assoc, w.onSplitInAbsolute,
    Category.assoc, he]

/-- Transport the closed subgroup, its matrix charts, and its diagonal by one
rational normalizer element. -/
private def conjugateSplitRootSL2 {A : AdaptedBorel G n} {w : MarkedConjugation A}
    {a b : Root A.P.T} (h : MovesRoot w a b) (H : SplitRootSL2 A a) :
    SplitRootSL2 A b := by
  let e := conjugationIso w.point
  let e' := conjugationIso ((markedToriOf A).absolutePoint w.point)
  refine {
    subgroup := transportSubgroup e H.subgroup
    matrix := H.matrix
    positive := H.positive
    negative := H.negative
    positive_eq := H.positive_eq
    negative_eq := H.negative_eq
    positiveAbsolute := transportSubgroup e' H.positiveAbsolute
    negativeAbsolute := transportSubgroup e' H.negativeAbsolute
    positiveIso := H.positiveIso
    negativeIso := H.negativeIso
    positiveInclusion := ?_
    negativeInclusion := ?_
    positiveRoot := ?_
    negativeRoot := ?_
    diagonal := H.diagonal
    diagonal_eq := H.diagonal_eq
    coroot := H.coroot ≫ w.split.hom
    diagonalInAmbient := ?_
    coroot_eq := ?_ }
  · change H.positiveIso.hom ≫ (H.positiveAbsolute.inclusion ≫ e'.hom) ≫ A.ambient.hom =
      (groupBaseChange F Fsep).map (H.positive.inclusion ≫ H.subgroup.inclusion ≫ e.hom)
    have hi := H.positiveInclusion
    simp only [Category.assoc] at hi ⊢
    rw [w.ambient_eq, reassoc_of% hi, ← Functor.map_comp, Category.assoc]
  · change H.negativeIso.hom ≫ (H.negativeAbsolute.inclusion ≫ e'.hom) ≫ A.ambient.hom =
      (groupBaseChange F Fsep).map (H.negative.inclusion ≫ H.subgroup.inclusion ≫ e.hom)
    have hi := H.negativeInclusion
    simp only [Category.assoc] at hi ⊢
    rw [w.ambient_eq, reassoc_of% hi, ← Functor.map_comp, Category.assoc]
  · rw [← h.character]
    exact transportMarkedRoot A w _ a H.positiveRoot
  · let a' := oppositeRoot A.D a
    have ha' : a'.val = a.val⁻¹ := oppositeRoot_character A.D a
    have ht : w.absolute.inv ≫ a'.val = b.val⁻¹ := by
      rw [ha', ← h.character]
      exact (characterPullback w.absolute.inv).map_inv a.val
    rw [← ht]
    exact transportMarkedRoot A w _ a' (ha'.symm ▸ H.negativeRoot)
  · change H.diagonal ≫ H.subgroup.inclusion ≫ e.hom =
      (H.coroot ≫ w.split.hom) ≫ A.S.inclusion
    rw [Category.assoc, w.split_eq, ← Category.assoc H.diagonal, H.diagonalInAmbient, Category.assoc]
  · simp only [Functor.map_comp, Category.assoc]
    rw [w.onSplitInAbsolute]
    have hc := congrArg (fun f => f ≫ w.absolute.hom) H.coroot_eq
    calc
      _ = (A.D.toBased.datum.coroot a).toMul ≫ w.absolute.hom := by
        simpa only [Category.assoc] using hc
      _ = _ := h.coroot

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

private theorem realizesReflectionWord (A : AdaptedBorel G n)
    (hG : IsSemisimple G) (hsc : GeometricallySimplyConnected G)
    (project : (Fin n → ℤ) →ₗ[ℤ] (Fin r → ℤ)) {count : ℕ} {node : Fin n} {highest : Fin n → ℤ}
    (calculation : ProjectedRootCoordinates project count node highest)
    (coeff : Root A.P.T ≃ {v // IsRootCoordinate (exceptionalCartan n) v})
    (hRoot : ∀ a, A.D.toBased.datum.root a =
      ∑ j, (coeff a).val j • A.D.toBased.datum.root (A.numbering j))
    (hCoroot : ∀ a, A.D.toBased.datum.coroot a =
      ∑ j, (coeff a).val j • A.D.toBased.datum.coroot (A.numbering j))
    (encode : Multiplicative (Fin r → ℤ) →* Character A.S.group)
    (hEncode : Function.Injective encode)
    (hRestrict : ∀ a, A.restrictAbsolute a.val =
      A.extendRelative (encode (Multiplicative.ofAdd (project (coeff a).val))))
    (word : List (Fin n → ℤ))
    (hWord : ∀ a ∈ word, IsRootCoordinate (exceptionalCartan n) a ∧
      project a ≠ 0 ∧ KeepsFullLength project a ∧
      ∀ v, IsRootCoordinate (exceptionalCartan n) v → project v = project a → v = a)
    (start : Root A.P.T) :
    ∃ (finish : Root A.P.T) (w : MarkedConjugation A),
      MovesRoot w start finish ∧
      (coeff finish).val = word.foldl
        (fun v a => v - dotProduct v ((exceptionalCartan n).mulVec a) • a) (coeff start).val := by
  induction word generalizing start with
  | nil => exact ⟨start, MarkedConjugation.refl A, ⟨Category.id_comp _, Category.comp_id _⟩, rfl⟩
  | cons v word ih =>
      obtain ⟨hv, hnv, _, hu⟩ := hWord v (List.mem_cons_self ..)
      let α := coeff.symm ⟨v, hv⟩
      have hα : (coeff α).val = v := congrArg Subtype.val (coeff.apply_symm_apply ⟨v, hv⟩)
      have hs := singletonLineOfProjection A project calculation coeff encode hEncode hRestrict α
        (by simpa only [hα] using hnv) (by simpa only [hα] using hu)
      obtain ⟨H, ⟨ref⟩⟩ := ExceptionalSingletonRootSL2.singletonRootSL2 F G hG hsc
        (markedToriOf A) α hs
      let b := A.D.toBased.datum.reflectionPerm α start
      obtain ⟨finish, w, hw, he⟩ := ih (fun a ha => hWord a (List.mem_cons_of_mem _ ha)) b
      have hb : (coeff b).val = (coeff start).val -
          dotProduct (coeff start).val ((exceptionalCartan n).mulVec v) • v := by
        simpa only [b, hα] using reflectionCoordinates A coeff hRoot hCoroot α start
      exact ⟨finish, (markedConjugationOfReflection ref).trans w,
        (movesRootByReflection ref start).trans hw, by simpa only [List.foldl_cons, hb] using he⟩

/-- The finite root and reflection calculations give the rank-one
configuration on the actual adapted exceptional chart. -/
theorem projectedRootSubgroupsOfAdaptedChart (A : AdaptedBorel G n)
    (hG : IsSemisimple G) (hsc : GeometricallySimplyConnected G)
    (project : (Fin n → ℤ) →ₗ[ℤ] (Fin r → ℤ)) {count : ℕ} {node : Fin n} {highest : Fin n → ℤ}
    (hSimple : HasSimpleRestrictions A project)
    (calculation : ProjectedRootCoordinates project count node highest)
    (hw : HasFullLengthReflectionWord project (Pi.single node 1) highest) :
    ∃ selected : SplitRootSL2 A (A.numbering node).val,
      HasProjectedRootSystem A project count node selected := by
  obtain ⟨coeff, hRoot, hCoroot, hCoeff⟩ := adaptedRootCoordinates A (exceptionalCartan_symmetric n)
  obtain ⟨encode, hinj, hCoordinates⟩ := hSimple
  have hRestrict := rootRestrictionsOfSimpleRestrictions A project coeff encode hRoot hCoordinates
  let start := (A.numbering node).val
  have hstart : (coeff start).val = Pi.single node 1 := hCoeff node
  have hs := singletonLineOfProjection A project calculation coeff encode hinj hRestrict start
    (by rw [hstart]; exact calculation.simpleMem.2) (by simpa only [hstart] using calculation.simpleFibre)
  obtain ⟨H, _⟩ := ExceptionalSingletonRootSL2.singletonRootSL2 F G hG hsc (markedToriOf A) start hs
  let selected := splitRootSL2OfMarked A H
  obtain ⟨word, hWord, hw⟩ := hw
  obtain ⟨finish, w, hm, he⟩ :=
    realizesReflectionWord A hG hsc project calculation coeff hRoot hCoroot encode hinj hRestrict word hWord start
  have hCoordinate : (coeff finish).val = highest := by rw [he, hstart, hw]
  have hFinish : finish = coeff.symm ⟨highest, calculation.highestRoot⟩ := by
    apply coeff.injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext hCoordinate
  refine ⟨selected, hasProjectedRootSystem_of_coordinates A calculation selected coeff encode hinj
    hRoot hCoeff hRestrict ?_⟩
  rw [← hFinish]
  let highestSL2 := conjugateSplitRootSL2 hm selected
  refine ⟨highestSL2, w.point, w.split, ?_, ?_, ?_⟩
  · rw [w.split_eq, Grp.comp_hom_hom]
    exact comp_conjugation w.point A.S.inclusion.hom.hom
  · have hx := movesRootRestriction hm
    rw [hRestrict finish, hRestrict start, hCoordinate, hstart] at hx
    apply (adaptedRelativeRootRestrictions A).1
    rw [show A.extendRelative (w.split.hom ≫ encode (Multiplicative.ofAdd (project highest))) =
      (groupBaseChange F Fsep).map w.split.hom ≫
        A.extendRelative (encode (Multiplicative.ofAdd (project highest))) by
          simp only [AdaptedBorel.extendRelative, Functor.map_comp, Category.assoc]]
    exact hx
  · apply (conjugates_iff_iso w.point selected.subgroup highestSL2.subgroup).mpr
    exact ⟨Iso.refl _, by simp only [Iso.refl_hom, Category.id_comp]; rfl⟩

end
end RootConjugation

section LeviAssembly

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

open _root_.LinearAlgebraicGroups.Specs
open Specs.ExceptionalLocalRadicalGeneration
open Specs.ExceptionalOmittedNodeLevis (AdaptedPair HasWhiteRestrictions HasE6LeviModel HasE7LeviModel)
open Specs.GeometricRadicals (IsSemisimple IsSplitReductive)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.Arithmetic.RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open Specs.RelativeRank (relativeRank)
open Specs.OuterTypeAModels (RepresentsNormOne)
open Specs.InnerTypeARelativeContraction (NormOnePoints)
open _root_.Specs.RM03.CSA (isCentralSimple degree)
open private exceptionalCartan_eq from LinearAlgebraicGroups.Arithmetic.ExceptionalStableAlcoves

noncomputable section

variable {F : Type u} [Field F] {G : AffineAlgebraicGroup F} {n : ℕ}

set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false

private def leviAdaptedPair (A : AdaptedBorel G n) (hn : n = 6 ∨ n = 7 ∨ n = 8) :
    AdaptedPair G n where
  S := A.S
  maximalSplit := A.maximalSplit
  T := A.T
  maximalTorus := A.maximalTorus
  intoTorus := A.intoTorus
  intoTorus_eq := A.intoTorus_eq
  J := A.J
  minimalParabolic := A.minimalParabolic
  torusInParabolic := A.torusInParabolic
  pair := A.P
  datum := A.D
  numbering := A.numbering
  cartan_eq i j := (A.cartan_eq i j).trans (congrFun (congrFun (exceptionalCartan_eq n hn) i) j)
  ambient := A.ambient
  torus := A.torus
  torus_eq := A.torus_eq
  borel := A.borel
  borel_eq := A.borel_eq
  multiplicative := A.multiplicative
  multiplicative_eq := A.multiplicative_eq

private theorem innerForLevi (hi : IsInnerTypeE G n) : Specs.ExceptionalOmittedNodeLevis.IsInner G := by
  obtain ⟨_, P, _, _, h⟩ := hi
  exact ⟨P.pair.G, ⟨P.pair.reductive, P.pair.T, P.pair.split, P.pair.maximal⟩, h⟩

private theorem e6WhiteRestrictions {A : AdaptedBorel G 6} (h : HasSimpleRestrictions A e6InnerProjection) :
    HasWhiteRestrictions (leviAdaptedPair A (.inl rfl)) (![1, 3] : Fin 2 → Fin 6) := by
  obtain ⟨e, he, h⟩ := h
  refine ⟨e, he, fun i => ?_⟩
  have hh : e6InnerProjection (Pi.single i 1) =
      (fun j : Fin 2 => (Pi.single i 1 : Fin 6 → ℤ) ((![1, 3] : Fin 2 → Fin 6) j)) := by
    ext j
    fin_cases j <;> rfl
  simpa only [hh, leviAdaptedPair, AdaptedPair.splitInAbsolute,
    AdaptedBorel.restrictAbsolute, AdaptedBorel.extendRelative] using h i

private theorem e7WhiteRestrictions {A : AdaptedBorel G 7} (h : HasSimpleRestrictions A e7InnerProjection) :
    HasWhiteRestrictions (leviAdaptedPair A (.inr (.inl rfl))) (![0, 2, 3, 5] : Fin 4 → Fin 7) := by
  obtain ⟨e, he, h⟩ := h
  refine ⟨e, he, fun i => ?_⟩
  have hh : e7InnerProjection (Pi.single i 1) =
      (fun j : Fin 4 => (Pi.single i 1 : Fin 7 → ℤ) ((![0, 2, 3, 5] : Fin 4 → Fin 7) j)) := by
    ext j
    fin_cases j <;> rfl
  simpa only [hh, leviAdaptedPair, AdaptedPair.splitInAbsolute,
    AdaptedBorel.restrictAbsolute, AdaptedBorel.extendRelative] using h i

private theorem normOnePointsOfRepresentation {B : Type u} [Ring B] [Algebra F B] {m : ℕ}
    {a : isCentralSimple F (Matrix (Fin m) (Fin m) B)}
    {I : Type u} [Fintype I] {b : Module.Basis I F (Matrix (Fin m) (Fin m) B)}
    {H : AffineAlgebraicGroup F} (h : RepresentsNormOne a b H) :
    Nonempty (NormOnePoints a b H) := by
  obtain ⟨p, hm, hn⟩ := h
  refine ⟨⟨p, ?_, hm, hn⟩⟩
  intro R
  let e : {x : R ⊗[F] Matrix (Fin m) (Fin m) B // _root_.Specs.RM03.CSA.NormOneGroup.normAt a b x = 1} :=
    ⟨1, map_one (_root_.RM03.CSA.NormOneGroup.normHom a b)⟩
  let x := (p R).symm e
  have he : (p R x).val = 1 := congrArg Subtype.val ((p R).apply_symm_apply e)
  have h := hm R 1 x
  rw [one_mul, he, mul_one] at h
  exact h.symm

private theorem divisionMatrixModelOfRepresentation {H : AffineAlgebraicGroup F} {m d : ℕ}
    (h : IsDivisionMatrixGroup H m d) : Specs.ExceptionalLeviRadicalGeneration.IsDivisionMatrixGroup H m d := by
  obtain ⟨B, _, _, hB, hd, a, b, hr⟩ := h
  exact ⟨B, inferInstance, inferInstance, hB, hd, a, b, normOnePointsOfRepresentation hr⟩

private theorem parentOmittedNodeLevi {A : AdaptedBorel G n} {node : Fin n}
    (hn : n = 6 ∨ n = 7 ∨ n = 8)
    (selected : SplitRootSL2 A (A.numbering node).val)
    {p q : AffineAlgebraicGroup F → Prop}
    (h : Specs.ExceptionalOmittedNodeLevis.HasOmittedNodeLevi (leviAdaptedPair A hn) node selected.coroot p)
    (hq : ∀ H, p H → q H) :
    HasOmittedNodeLevi A node selected q := by
  obtain ⟨c, L, hc, hP, hProper, hJ, hMax, H, f, s, hDer, hSC, hKer, hQuot, hs, hδ, hm⟩ := h
  exact ⟨c, L, hc, hP, hProper, hJ, hMax, H, f, s, hDer, hSC, hKer, hQuot, hs, hδ, hq _ hm⟩

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem e6LeviFromAdaptedChart (A : AdaptedBorel G 6)
    (hG : IsSemisimple G) (hsc : GeometricallySimplyConnected G)
    (hi : IsInnerTypeE G 6) (hns : ¬ IsSplitReductive G)
    (hr : relativeRank G = 2) (h : HasSimpleRestrictions A e6InnerProjection)
    (selected : SplitRootSL2 A (A.numbering 1).val) :
    HasOmittedNodeLevi A 1 selected (fun H => IsDivisionMatrixGroup H 2 3) := by
  have hLev := ExceptionalOmittedNodeLevis.e6OmittedNodeLevi G (leviAdaptedPair A (.inl rfl))
    hG hsc (innerForLevi hi) hns hr (e6WhiteRestrictions h) selected.coroot
    selected.coroot_eq
  exact parentOmittedNodeLevi (.inl rfl) selected hLev fun _ h => h

private abbrev E7LeviModel (H : AffineAlgebraicGroup F) : Prop :=
  ∃ (H₁ H₂ : AffineAlgebraicGroup F) (_ : GeneralLinearStructure.SpecialMatrixPoints H₁ 2),
    IsDivisionMatrixGroup H₂ 3 2 ∧ Nonempty (H.val ≅ Limits.prod H₁.val H₂.val)

theorem e7LeviFromAdaptedChart (A : AdaptedBorel G 7)
    (hG : IsSemisimple G) (hsc : GeometricallySimplyConnected G)
    (hi : IsInnerTypeE G 7) (hns : ¬ IsSplitReductive G)
    (hr : relativeRank G = 4) (h : HasSimpleRestrictions A e7InnerProjection)
    (selected : SplitRootSL2 A (A.numbering 2).val) :
    HasOmittedNodeLevi A 2 selected E7LeviModel := by
  have hLev := ExceptionalOmittedNodeLevis.e7OmittedNodeLevi G (leviAdaptedPair A (.inr (.inl rfl)))
    hG hsc (innerForLevi hi) hns hr (e7WhiteRestrictions h) selected.coroot
    selected.coroot_eq
  refine parentOmittedNodeLevi (.inr (.inl rfl)) selected hLev fun _ hm => ?_
  obtain ⟨H₁, H₂, s, B, _, _, ⟨hA, _, hd, _, _⟩, hB, e⟩ := hm
  exact ⟨H₁, H₂, s, ⟨B, inferInstance, inferInstance, hA, hd, hB⟩, e⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem e7ModelForGeneration (H : AffineAlgebraicGroup F) (hm : E7LeviModel H) :
    Specs.ExceptionalLeviRadicalGeneration.HasDerivedLeviModel H := by
  obtain ⟨H₁, H₂, s, h, e⟩ := hm
  exact .inr ⟨H₁, H₂, ⟨s⟩, divisionMatrixModelOfRepresentation h, e⟩

theorem densityOfOmittedNodeLevi {A : AdaptedBorel G n} {node : Fin n}
    {selected : SplitRootSL2 A (A.numbering node).val}
    (hG : IsAbsolutelyAlmostSimple G) (hsc : GeometricallySimplyConnected G)
    {model : AffineAlgebraicGroup F → Prop}
    (h : HasOmittedNodeLevi A node selected model)
    (hm : ∀ H, model H → Specs.ExceptionalLeviRadicalGeneration.HasDerivedLeviModel H) :
    letI := localPointTopology G
    Dense (unipotentGenerated G : Set (𝟙_ (SchemeOver F) ⟶ G.val.X)) := by
  obtain ⟨c, L, _, _, _, _, _, H, q, s, hd, _, hk, hq, hs, hδ, hModel⟩ := h
  let D : Specs.ExceptionalLeviRadicalGeneration.SplitRankOneDiagonal G :=
    ⟨selected.subgroup, selected.matrix, selected.diagonal, selected.diagonal_eq⟩
  exact ExceptionalLeviRadicalGeneration.leviRadicalGeneration
    F G hG hsc (c ≫ A.S.inclusion) L H q s D hd hk hq hs
    (hδ.trans selected.diagonalInAmbient.symm) (hm _ hModel)

end
end LeviAssembly

section ExceptionalAssembly

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

open _root_.LinearAlgebraicGroups.Specs
open Specs.ExceptionalLocalRadicalGeneration
open Specs.ExceptionalInnerIndices (e6Black e7Black)
open Specs.ExceptionalAffineRootSystems (restrictedRoot)
open Specs.ExceptionalInnerAlcoveSymmetries (e6Highest e7Highest)
open Specs.RelativeRank (relativeRank)
open Specs.Arithmetic.RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open Specs.GeometricRadicals (IsSemisimple IsSplitReductive)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.QuasiSplitPinnedPairModel (BorelPair)
open Specs.ExceptionalLocalFormClassification (HasMarkedInnerIndex)

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {G : AffineAlgebraicGroup F}

set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

private abbrev InnerChart (G : AffineAlgebraicGroup F) {n r : ℕ} (black : Set (Fin n))
    (project : (Fin n → ℤ) → (Fin r → ℤ)) : Prop :=
  ∃ A : AdaptedBorel G n, relativeRank G = (r : WithBot ℕ∞) ∧
    (∀ i, A.restrictAbsolute (A.numbering i).val.val = 1 ↔ i ∈ black) ∧
    HasSimpleRestrictions A project

private theorem exceptionalFormCases (hG : IsAbsolutelyAlmostSimple G)
    (hsc : GeometricallySimplyConnected G) (n : ℕ) (hn : n = 6 ∨ n = 7 ∨ n = 8)
    (h : HasAbsoluteTypeE G n) :
    (IsInnerTypeE G n ∧ IsSplitReductive G) ∨
    (n = 6 ∧ IsInnerTypeE G 6 ∧ ¬ IsSplitReductive G ∧ InnerChart G e6Black e6InnerProjection) ∨
    (n = 7 ∧ IsInnerTypeE G 7 ∧ ¬ IsSplitReductive G ∧ InnerChart G e7Black e7InnerProjection) ∨
    (n = 6 ∧ ¬ IsInnerTypeE G 6 ∧ ∃ A : AdaptedBorel G 6, Nonempty (BorelPair G) ∧ relativeRank G = 4 ∧
      HasSimpleRestrictions A restrictedRoot) := by
  obtain ⟨P, D, b, ⟨g⟩, hb⟩ := h
  obtain ⟨_, R, hR, cases⟩ := ExceptionalLocalFormClassification.exceptionalLocalFormClassification
    F G (absoluteAlmostSimpleForClassification hG) hsc n hn P D b g hb
  have inner := innerTypeOfReference R hR hn hG.1 hsc
  rcases cases with ⟨hi, hs, _⟩ | ⟨hi, hns, h⟩ | ⟨h₆, hni, h⟩
  · exact .inl ⟨inner.mp hi, hs⟩
  · rcases h with ⟨h₆, hc⟩ | ⟨h₇, hc⟩
    · subst n
      have hIndex : HasMarkedInnerIndex R 2 e6Black := hc
      obtain ⟨A, _, hr, hb, hs⟩ := adaptedBorelOfInnerIndex R
        ExceptionalAdaptedRootCoordinates.innerCoordinates.1 hIndex
      exact .inr (.inl ⟨rfl, inner.mp hi, hns, A, hr, hb, hs⟩)
    · subst n
      have hIndex : HasMarkedInnerIndex R 4 e7Black := hc
      obtain ⟨A, _, hr, hb, hs⟩ := adaptedBorelOfInnerIndex R
        ExceptionalAdaptedRootCoordinates.innerCoordinates.2 hIndex
      exact .inr (.inr (.inl ⟨rfl, inner.mp hi, hns, A, hr, hb, hs⟩))
  · subst n
    exact .inr (.inr (.inr ⟨rfl, hni ∘ inner.mpr, adaptedBorelOfOuterRepresentative R h⟩))

private theorem e6InnerStructure (A : AdaptedBorel G 6)
    (hG : IsSemisimple G) (hsc : GeometricallySimplyConnected G)
    (hi : IsInnerTypeE G 6) (hns : ¬ IsSplitReductive G)
    (hr : relativeRank G = 2) (hs : HasSimpleRestrictions A e6InnerProjection) :
    ∃ selected : SplitRootSL2 A (A.numbering 1).val,
      HasProjectedRootSystem A e6InnerProjection 12 1 selected ∧
      HasOmittedNodeLevi A 1 selected (fun H => IsDivisionMatrixGroup H 2 3) := by
  obtain ⟨selected, h⟩ := projectedRootSubgroupsOfAdaptedChart A hG hsc e6InnerRestriction hs
    e6InnerProjectedRoots e6InnerHighestReflection
  exact ⟨selected, h, e6LeviFromAdaptedChart A hG hsc hi hns hr hs selected⟩

private theorem e7InnerStructure (A : AdaptedBorel G 7)
    (hG : IsSemisimple G) (hsc : GeometricallySimplyConnected G)
    (hi : IsInnerTypeE G 7) (hns : ¬ IsSplitReductive G)
    (hr : relativeRank G = 4) (hs : HasSimpleRestrictions A e7InnerProjection) :
    ∃ selected : SplitRootSL2 A (A.numbering 2).val,
      HasProjectedRootSystem A e7InnerProjection 48 2 selected ∧
      HasOmittedNodeLevi A 2 selected E7LeviModel := by
  obtain ⟨selected, h⟩ := projectedRootSubgroupsOfAdaptedChart A hG hsc e7InnerRestriction hs
    e7InnerProjectedRoots e7InnerHighestReflections
  exact ⟨selected, h, e7LeviFromAdaptedChart A hG hsc hi hns hr hs selected⟩

/-- The nonsplit inner Levis and the relative root systems with their
split rank-one subgroups on the given exceptional group schemes. -/
theorem exceptionalRootSystemsAndLevis : ExceptionalRootSystemsAndLevis.{u} := by
  intro F _ _ _ _ G hG hsc
  refine ⟨?_, ?_, ?_⟩
  · intro h₆ hi hn
    rcases exceptionalFormCases hG hsc 6 (.inl rfl) h₆ with
      ⟨_, h⟩ | ⟨_, _, _, A, hr, hb, hs⟩ | ⟨h, _, _, _⟩ | ⟨_, h, _⟩
    · exact (hn h).elim
    · obtain ⟨selected, hRoot, hLevi⟩ := e6InnerStructure A hG.1 hsc hi hn hr hs
      exact ⟨A, selected, hr, hb, hRoot, hLevi⟩
    · exact ((by decide : (6 : ℕ) ≠ 7) h).elim
    · exact (h hi).elim
  · intro h₇ hi hn
    rcases exceptionalFormCases hG hsc 7 (.inr (.inl rfl)) h₇ with
      ⟨_, h⟩ | ⟨h, _, _, _⟩ | ⟨_, _, _, A, hr, hb, hs⟩ | ⟨h, _, _⟩
    · exact (hn h).elim
    · exact ((by decide : (7 : ℕ) ≠ 6) h).elim
    · obtain ⟨selected, hRoot, hLevi⟩ := e7InnerStructure A hG.1 hsc hi hn hr hs
      exact ⟨A, selected, hr, hb, hRoot, hLevi⟩
    · exact ((by decide : (7 : ℕ) ≠ 6) h).elim
  · intro h₆ hi
    rcases exceptionalFormCases hG hsc 6 (.inl rfl) h₆ with
      ⟨h, _⟩ | ⟨_, h, _, _⟩ | ⟨h, _, _, _⟩ | ⟨_, _, A, _, _, h⟩
    · exact (hi h).elim
    · exact (hi h).elim
    · exact ((by decide : (6 : ℕ) ≠ 7) h).elim
    · obtain ⟨selected, hs⟩ := projectedRootSubgroupsOfAdaptedChart A hG.1 hsc
        e6OuterRestriction h e6OuterProjectedRoots e6OuterHighestReflection
      exact ⟨A, selected, hs⟩

private theorem generationOfExceptionalType (hG : IsAbsolutelyAlmostSimple G)
    (hsc : GeometricallySimplyConnected G) (n : ℕ) (hn : n = 6 ∨ n = 7 ∨ n = 8)
    (h : HasAbsoluteTypeE G n) :
    letI := localPointTopology G
    0 < relativeRank G ∧ Dense (unipotentGenerated G : Set (𝟙_ (SchemeOver F) ⟶ G.val.X)) := by
  rcases exceptionalFormCases hG hsc n hn h with
    ⟨_, hs⟩ | ⟨_, hi, hns, A, hr, _, hs⟩ | ⟨_, hi, hns, A, hr, _, hs⟩ | ⟨_, _, _, ⟨M⟩, _, _⟩
  · exact radicalGenerationOfSplit hG hsc hs
  · obtain ⟨_, _, hLevi⟩ := e6InnerStructure A hG.1 hsc hi hns hr hs
    exact ⟨by rw [hr]; norm_num,
      densityOfOmittedNodeLevi hG hsc hLevi fun _ hm => .inl (divisionMatrixModelOfRepresentation hm)⟩
  · obtain ⟨_, _, hLevi⟩ := e7InnerStructure A hG.1 hsc hi hns hr hs
    exact ⟨by rw [hr]; norm_num, densityOfOmittedNodeLevi hG hsc hLevi e7ModelForGeneration⟩
  · exact radicalGenerationOfBorelPair hG hsc M

/-- Exceptional groups of these absolute types over a nonarchimedean local
field have positive split rank and dense rational radical generation. -/
theorem localRadicalGeneration : LocalRadicalGeneration.{u} := by
  intro F _ _ _ _ G hG hsc h
  rcases h with h | h | h
  · exact generationOfExceptionalType hG hsc 6 (.inl rfl) h
  · exact generationOfExceptionalType hG hsc 7 (.inr (.inl rfl)) h
  · exact generationOfExceptionalType hG hsc 8 (.inr (.inr rfl)) h

end ExceptionalAssembly

end LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRadicalGeneration
