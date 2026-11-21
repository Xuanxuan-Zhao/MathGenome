import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ClassicalLowRank
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClassicalMatrixCartans
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.Reconstruction
import Mathlib.Tactic.FinCases
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.LinearCombination

/-! The low-rank coincidences of the classical root systems (LA-D08).
Finite coordinate calculations give the root bijections. The matrix root
decompositions and opposite-root brackets identify their ordered pairings
with the actual Killing coroot pairings used in reconstruction. -/

noncomputable section

namespace LieAlgebrasAndRepresentations.ClassicalLowRank

open Specs.LieAlgebrasAndRepresentations.ClassicalLowRank
open scoped BigOperators Matrix
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048

private theorem range_eq_of_finite_checks {ι κ V : Type*} (f : ι → V) (g : κ → V)
    (hf : ∀ i, ∃ j, f i = g j) (hg : ∀ j, ∃ i, g j = f i) :
    Set.range f = Set.range g := by
  ext a
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨j, h⟩ := hf i
    exact ⟨j, h.symm⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨i, h⟩ := hg j
    exact ⟨i, h.symm⟩

private theorem coordinate_identification {n m k : ℕ} {ι κ : Type*}
    (f : ι → Fin n → ℤ) (g : κ → Fin m → ℤ) (r s : ℕ)
    (x : Fin k → Fin n → ℤ) (y : Fin k → Fin m → ℤ)
    (hr : 0 < r) (hs : 0 < s)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hxf : ∀ i, ∃ j, x i = f j) (hfx : ∀ j, ∃ i, f j = x i)
    (hyg : ∀ i, ∃ j, y i = g j) (hgy : ∀ j, ∃ i, g j = y i)
    (hxy : ∀ i j, (r : ℤ) * dot (x i) (x j) = (s : ℤ) * dot (y i) (y j)) :
    CoordinateIdentification (Set.range f) (Set.range g) r s :=
  ⟨hr, hs, k, x, y, hx, hy, range_eq_of_finite_checks x f hxf hfx,
    range_eq_of_finite_checks y g hyg hgy, hxy⟩

private def a1 : Fin 2 → Fin 2 → ℤ := ![![1, -1], ![-1, 1]]
private def b1 : Fin 2 → Fin 1 → ℤ := ![![1], ![-1]]
private def c1 : Fin 2 → Fin 1 → ℤ := ![![2], ![-2]]

-- The correspondence in rank two is (x,y) ↦ (x+y,x-y).
private def b2 : Fin 8 → Fin 2 → ℤ :=
  ![![1,0], ![-1,0], ![0,1], ![0,-1], ![1,1], ![-1,-1], ![1,-1], ![-1,1]]
private def c2 : Fin 8 → Fin 2 → ℤ :=
  ![![1,1], ![-1,-1], ![1,-1], ![-1,1], ![2,0], ![-2,0], ![0,2], ![0,-2]]

private def d2 : Fin 4 → Fin 2 → ℤ := ![![1,-1], ![-1,1], ![1,1], ![-1,-1]]
private def a1Sum : Fin 4 → Fin 4 → ℤ :=
  ![![1,-1,0,0], ![-1,1,0,0], ![0,0,1,-1], ![0,0,-1,1]]

-- The rank-three map is half the matrix with rows (+++), (+--), (-+-), (--+).
private def d3 : Fin 12 → Fin 3 → ℤ :=
  ![![1,1,0], ![-1,-1,0], ![1,-1,0], ![-1,1,0],
    ![1,0,1], ![-1,0,-1], ![1,0,-1], ![-1,0,1],
    ![0,1,1], ![0,-1,-1], ![0,1,-1], ![0,-1,1]]
private def a3 : Fin 12 → Fin 4 → ℤ :=
  ![![1,0,0,-1], ![-1,0,0,1], ![0,1,-1,0], ![0,-1,1,0],
    ![1,0,-1,0], ![-1,0,1,0], ![0,1,0,-1], ![0,-1,0,1],
    ![1,-1,0,0], ![-1,1,0,0], ![0,0,1,-1], ![0,0,-1,1]]

theorem b1_a1_coordinates : b1_a1_coordinates_type := by
  exact coordinate_identification _ _ _ _ b1 a1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

theorem c1_a1_coordinates : c1_a1_coordinates_type := by
  exact coordinate_identification _ _ _ _ c1 a1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

theorem b2_c2_coordinates : b2_c2_coordinates_type := by
  exact coordinate_identification _ _ _ _ b2 c2
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

theorem d2_a1_sum_coordinates : d2_a1_sum_coordinates_type := by
  exact coordinate_identification _ _ _ _ d2 a1Sum
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

theorem d3_a3_coordinates : d3_a3_coordinates_type := by
  exact coordinate_identification _ _ _ _ d3 a3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

theorem d1_not_semisimple : d1_not_semisimple_type :=
  ClassicalRootsD.d1_not_semisimple


section Reconstruction

open Module
open private maximalToral_of_weightSpaces semisimple_of_weightSpaces
  coroot_eq_of_opposite_bracket from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClassicalMatrixCartans

variable {L : Type} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
variable {H : LieSubalgebra ℂ L}

private def coordinateFunctional {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (coord : V →ₗ[ℂ] (Fin n → ℂ)) (v : Fin n → ℤ) : Dual ℂ V :=
  ∑ i, (v i : ℂ) • (LinearMap.proj i).comp coord

private theorem coordinateFunctional_apply {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (coord : V →ₗ[ℂ] (Fin n → ℂ)) (v : Fin n → ℤ) (x : V) :
    coordinateFunctional coord v x = ∑ i, (v i : ℂ) * coord x i := by
  simp [coordinateFunctional, LinearMap.sum_apply, smul_eq_mul]

private def coordinateCoroot {n : ℕ} (v : Fin n → ℤ) : Fin n → ℂ :=
  fun i => (2 / (dot v v : ℂ)) * (v i : ℂ)

private theorem coordinate_pairing {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (coord : V →ₗ[ℂ] (Fin n → ℂ)) (u v : Fin n → ℤ) (h : V)
    (hh : coord h = coordinateCoroot u) :
    coordinateFunctional coord v h = 2 * (dot u v : ℂ) / (dot u u : ℂ) := by
  rw [coordinateFunctional_apply, hh]
  have hp : (dot u v : ℂ) = ∑ i, (u i : ℂ) * (v i : ℂ) := by
    simp [dot, Int.cast_sum]
  rw [hp, mul_comm (2 : ℂ), mul_div_assoc, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [coordinateCoroot]
  ring

private structure RealizedRoots (L : Type) [LieRing L] [LieAlgebra ℂ L]
    [FiniteDimensional ℂ L] {n k : ℕ} (v : Fin k → Fin n → ℤ) where
  cartan : LieSubalgebra ℂ L
  semisimple : IsSemisimple ℂ L
  maximalToral : IsMaximalToral cartan
  index : Fin k ≃ rootSet cartan
  pairing : ∀ i j, (index j).val (killingCoroot cartan (index i).val) =
    2 * (dot (v i) (v j) : ℂ) / (dot (v i) (v i) : ℂ)

/-- Index the actual roots by their coordinate vectors and record every
root-coroot pairing. -/
private def realizeRootsOfCoroots {n k : ℕ} (v : Fin k → Fin n → ℤ)
    (coord : H →ₗ[ℂ] (Fin n → ℂ))
    (h : Fin k → H)
    (hcoord : ∀ i, coord (h i) = coordinateCoroot (v i))
    (hlength : ∀ i, dot (v i) (v i) ≠ 0)
    (hdistinct : ∀ i j, i ≠ j → ∃ l, dot (v l) (v i) ≠ dot (v l) (v j))
    (hroots : rootSet H = Set.range (fun i => coordinateFunctional coord (v i)))
    (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (hc : ∀ i, killingCoroot H (coordinateFunctional coord (v i)) = h i) :
    RealizedRoots L v := by
  classical
  let a (i : Fin k) := coordinateFunctional coord (v i)
  have ha (i : Fin k) : a i ∈ rootSet H := hroots.symm ▸ Set.mem_range_self i
  let index : Fin k ≃ rootSet H := Equiv.ofBijective (fun i ↦ ⟨a i, ha i⟩) ⟨by
    intro i j hij
    by_contra hne
    obtain ⟨l, hl⟩ := hdistinct i j hne
    have hp : a i (h l) = a j (h l) :=
      congrArg (fun x : rootSet H => x.val (h l)) hij
    rw [coordinate_pairing coord _ _ _ (hcoord l),
      coordinate_pairing coord _ _ _ (hcoord l)] at hp
    exact hl (Int.cast_injective (mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)
      ((div_left_inj' (Int.cast_ne_zero.mpr (hlength l))).mp hp)))
    , by
      intro b
      obtain ⟨i, hi⟩ := (Set.ext_iff.mp hroots b.val).mp b.property
      exact ⟨i, Subtype.ext hi⟩⟩
  refine ⟨H, hss, hH, index, ?_⟩
  intro i j
  change a j (killingCoroot H (a i)) = _
  rw [hc i]
  exact coordinate_pairing coord _ _ _ (hcoord i)


/-- Use a product's weight decomposition and opposite-root brackets to
establish the hypotheses of reconstruction on its product Cartan. -/
private def realizeRoots {n k : ℕ} (v : Fin k → Fin n → ℤ)
    (coord : H →ₗ[ℂ] (Fin n → ℂ))
    (h : Fin k → H)
    (hcoord : ∀ i, coord (h i) = coordinateCoroot (v i))
    (hlength : ∀ i, dot (v i) (v i) ≠ 0)
    (hdistinct : ∀ i j, i ≠ j → ∃ l, dot (v l) (v i) ≠ dot (v l) (v j))
    (hroots : rootSet H = Set.range (fun i => coordinateFunctional coord (v i)))
    (hspan : (⨆ a : Dual ℂ H, rootSpace H a) = ⊤)
    (hzero : rootSpace H 0 = H.toSubmodule)
    (hsep : ∀ x, (∀ i, coordinateFunctional coord (v i) x = 0) → x = 0)
    (hdim : ∀ a : rootSet H, finrank ℂ (rootSpace H a.val) = 1)
    (htr : ∀ i, ∃ e f : L,
      e ∈ rootSpace H (coordinateFunctional coord (v i)) ∧
      f ∈ rootSpace H (-coordinateFunctional coord (v i)) ∧
      ⁅e, f⁆ = (h i : L)) : RealizedRoots L v := by
  classical
  let a (i : Fin k) := coordinateFunctional coord (v i)
  have ha (i : Fin k) : a i ∈ rootSet H := hroots.symm ▸ Set.mem_range_self i
  have hnorm (i : Fin k) : a i (h i) = 2 := by
    rw [coordinate_pairing coord _ _ _ (hcoord i)]
    exact (mul_div_cancel_right₀ _ (Int.cast_ne_zero.mpr (hlength i)))
  have hH := maximalToral_of_weightSpaces H hzero hspan
  have hss := semisimple_of_weightSpaces H hH.1 hzero (by
    intro x hx
    exact hsep x fun i => hx (a i) (ha i)) (fun b hb => hdim ⟨b, hb⟩) (by
      intro b hb
      obtain ⟨i, rfl⟩ := (Set.ext_iff.mp hroots b).mp hb
      obtain ⟨e, f, he, hf, hef⟩ := htr i
      exact ⟨h i, e, f, he, hf, hef, hnorm i⟩)
  refine realizeRootsOfCoroots v coord h hcoord hlength hdistinct hroots hss hH ?_
  intro i
  obtain ⟨e, f, he, hf, hef⟩ := htr i
  exact coroot_eq_of_opposite_bracket hss H hH (ha i) he hf hef (hnorm i)


private theorem reconstruct {M : Type} [LieRing M] [LieAlgebra ℂ M]
    [FiniteDimensional ℂ M] {n m k : ℕ} {v : Fin k → Fin n → ℤ} {w : Fin k → Fin m → ℤ}
    (X : RealizedRoots L v) (Y : RealizedRoots M w) {r s : ℕ}
    (hr : r ≠ 0) (hs : s ≠ 0)
    (hgram : ∀ i j, (r : ℤ) * dot (v i) (v j) = (s : ℤ) * dot (w i) (w j)) :
    Nonempty (L ≃ₗ⁅ℂ⁆ M) := by
  let σ := X.index.symm.trans Y.index
  have hp (i j : Fin k) :
      2 * (dot (v i) (v j) : ℂ) / (dot (v i) (v i) : ℂ) =
      2 * (dot (w i) (w j) : ℂ) / (dot (w i) (w i) : ℂ) := by
    have h₁ : (r : ℂ) * (dot (v i) (v j) : ℂ) = (s : ℂ) * (dot (w i) (w j) : ℂ) := by
      exact_mod_cast hgram i j
    have h₂ : (r : ℂ) * (dot (v i) (v i) : ℂ) = (s : ℂ) * (dot (w i) (w i) : ℂ) := by
      exact_mod_cast hgram i i
    rw [← mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr hr),
      mul_left_comm, h₁, h₂, ← mul_left_comm,
      mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr hs)]
  have hσ : ∀ a b : rootSet X.cartan,
      (σ b).val (killingCoroot Y.cartan (σ a).val) =
      b.val (killingCoroot X.cartan a.val) := by
    intro a b
    obtain ⟨i, rfl⟩ := X.index.surjective a
    obtain ⟨j, rfl⟩ := X.index.surjective b
    have hσi (l : Fin k) : σ (X.index l) = Y.index l := by simp [σ]
    rw [hσi, hσi, X.pairing, Y.pairing, hp]
  obtain ⟨_, _, _, _, _, _, _, _, g, _⟩ :=
    root_system_reconstruction X.semisimple Y.semisimple X.cartan Y.cartan
      X.maximalToral Y.maximalToral σ hσ
  exact ⟨g⟩

end Reconstruction


private abbrev A := Specs.LieAlgebrasAndRepresentations.ClassicalRootsA.sl

section CoordinateFunctionals

open Module

private theorem coordinateFunctional_eq_sum {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (coord : V →ₗ[ℂ] (Fin n → ℂ)) (i : Fin n) :
    coordinateFunctional coord (axis i) = (LinearMap.proj i).comp coord := by
  ext x
  simp [coordinateFunctional_apply, axis]

private theorem coordinateFunctional_add {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (coord : V →ₗ[ℂ] (Fin n → ℂ)) (a b : Fin n → ℤ) :
    coordinateFunctional coord (a + b) =
      coordinateFunctional coord a + coordinateFunctional coord b := by
  ext x
  simp [coordinateFunctional_apply, add_mul, Finset.sum_add_distrib]

private theorem coordinateFunctional_sub {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (coord : V →ₗ[ℂ] (Fin n → ℂ)) (a b : Fin n → ℤ) :
    coordinateFunctional coord (a - b) =
      coordinateFunctional coord a - coordinateFunctional coord b := by
  ext x
  simp [coordinateFunctional_apply, sub_mul, Finset.sum_sub_distrib]

private theorem coordinateFunctional_neg {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (coord : V →ₗ[ℂ] (Fin n → ℂ)) (a : Fin n → ℤ) :
    coordinateFunctional coord (-a) = -coordinateFunctional coord a := by
  ext x
  simp [coordinateFunctional_apply]

private theorem coordinateFunctional_two {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (coord : V →ₗ[ℂ] (Fin n → ℂ)) (a : Fin n → ℤ) :
    coordinateFunctional coord (2 • a) = (2 : ℂ) • coordinateFunctional coord a := by
  rw [two_nsmul, coordinateFunctional_add, two_smul]

end CoordinateFunctionals

section TypeA

open Specs.LieAlgebrasAndRepresentations.ClassicalRootsA (cartan epsilon root)
private abbrev aMatrixCoroot := Specs.LieAlgebrasAndRepresentations.ClassicalRootsA.coroot
open ClassicalRootsA (root_set killing_coroot)

private def aCoordinates (n : ℕ) : cartan n →ₗ[ℂ] (Fin (n + 1) → ℂ) :=
  LinearMap.pi (epsilon n)

private theorem aFunctional {n : ℕ} (ij : {p : Fin (n+1) × Fin (n+1) // p.1 ≠ p.2}) :
    coordinateFunctional (aCoordinates n) (aRoot ij) = root n ij.val.1 ij.val.2 := by
  rw [aRoot, coordinateFunctional_sub, coordinateFunctional_eq_sum, coordinateFunctional_eq_sum]
  rfl

private theorem aCoroot {n : ℕ} (ij : {p : Fin (n+1) × Fin (n+1) // p.1 ≠ p.2}) :
    aCoordinates n (aMatrixCoroot n ij.val.1 ij.val.2) = coordinateCoroot (aRoot ij) := by
  let i := ij.val.1
  let j := ij.val.2
  have hij : i ≠ j := ij.property
  have hc := ClassicalRootsA.coroot_coordinates n i j hij
  dsimp only at hc
  have hv (a : Fin (n+1)) :
      (aRoot ij a : ℝ) =
      Specs.LieAlgebrasAndRepresentations.ClassicalRootsA.euclideanRoot n i j a := by
    simp only [aRoot, axis, Pi.sub_apply, Int.cast_sub,
      Specs.LieAlgebrasAndRepresentations.ClassicalRootsA.euclideanRoot, Pi.single_apply]
    dsimp only [i, j]
    split_ifs <;> norm_num
  have hl : dot (aRoot ij) (aRoot ij) = 2 := by
    have he := hc.1
    simp_rw [← hv] at he
    exact_mod_cast he
  ext a
  change (aMatrixCoroot n i j).val.val a a = _
  rw [ClassicalRootsA.coroot_apply, coordinateCoroot, hl]
  simp only [aRoot, axis, Pi.sub_apply, Int.cast_sub, Matrix.single_apply]
  simp only [and_self, show ij.val.1 = i from rfl, show ij.val.2 = j from rfl]
  have ei : (i = a) ↔ (a = i) := eq_comm
  have ej : (j = a) ↔ (a = j) := eq_comm
  simp only [ei, ej]
  split_ifs <;> norm_num

private def typeA {n k : ℕ} (v : Fin k → Fin (n+1) → ℤ)
    (hv : Set.range v = Set.range (@aRoot (n+1)))
    (hlength : ∀ i, dot (v i) (v i) ≠ 0)
    (hdistinct : ∀ i j, i ≠ j → ∃ l, dot (v l) (v i) ≠ dot (v l) (v j)) :
    RealizedRoots (A n) v := by
  classical
  have hk (i : Fin k) : ∃ p, aRoot p = v i := by
    have hi : v i ∈ Set.range (@aRoot (n+1)) := hv ▸ Set.mem_range_self i
    exact hi
  choose ij hij using hk
  have ha (i : Fin k) : coordinateFunctional (aCoordinates n) (v i) =
      root n (ij i).val.1 (ij i).val.2 := by rw [← hij i, aFunctional]
  have hroots : rootSet (cartan n) = Set.range (fun i => coordinateFunctional (aCoordinates n) (v i)) := by
    ext a
    rw [root_set n]
    constructor
    · rintro ⟨i, j, hne, rfl⟩
      let p : {p : Fin (n+1) × Fin (n+1) // p.1 ≠ p.2} := ⟨(i,j), hne⟩
      obtain ⟨l, hl⟩ : aRoot p ∈ Set.range v := hv.symm ▸ Set.mem_range_self p
      exact ⟨l, by dsimp only; rw [hl, aFunctional]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨_, _, (ij i).property, ha i⟩
  let h (i : Fin k) := aMatrixCoroot n (ij i).val.1 (ij i).val.2
  have hA := ClassicalMatrixCartans.type_a n
  refine realizeRootsOfCoroots v (aCoordinates n) h
    (fun i => by rw [← hij i]; exact aCoroot (ij i))
    hlength hdistinct hroots hA.1 hA.2 ?_
  intro i
  rw [ha i]
  exact killing_coroot n (ij i).val.1 (ij i).val.2 (ij i).property

end TypeA


private abbrev Params (n : ℕ) := Fin n → ℂ

section ClassicalParameters

open Module

private abbrev parameterWeight {n : ℕ} (v : Fin n → ℤ) : Dual ℂ (Params n) :=
  coordinateFunctional (LinearMap.id : Params n →ₗ[ℂ] Params n) v
private abbrev difference (n : ℕ) (i j : Fin n) : Dual ℂ (Params n) :=
  (LinearMap.proj i : Dual ℂ (Params n)) - LinearMap.proj j
private abbrev positiveSum (n : ℕ) (i j : Fin n) : Dual ℂ (Params n) :=
  (LinearMap.proj i : Dual ℂ (Params n)) + LinearMap.proj j

private theorem parameterWeight_axis {n : ℕ} (i : Fin n) :
    parameterWeight (axis i) = LinearMap.proj i := by
  change coordinateFunctional LinearMap.id _ = _
  rw [coordinateFunctional_eq_sum, LinearMap.comp_id]

private theorem parameterWeight_coordinate {n : ℕ} (v : Fin n → ℤ) (i : Fin n) :
    parameterWeight v (Pi.single i 1) = (v i : ℂ) := by
  simp [coordinateFunctional_apply, Pi.single_apply, mul_ite]

private theorem dot_cast {n : ℕ} (v w : Fin n → ℤ) :
    (dot v w : ℂ) = ∑ i, (v i : ℂ) * (w i : ℂ) := by simp [dot, Int.cast_sum]

private theorem dWeight_range (n : ℕ) (a : Dual ℂ (Params n)) :
    a ∈ Set.range (parameterWeight ∘ @dRoot n) ↔
      ∃ i j : Fin n, i < j ∧
        (a = difference n i j ∨ a = -(difference n i j) ∨
         a = positiveSum n i j ∨ a = -(positiveSum n i j)) := by
  constructor
  · rintro ⟨⟨⟨⟨i,j⟩, hij⟩, u, v⟩, rfl⟩
    refine ⟨i, j, hij, ?_⟩
    cases u <;> cases v <;>
      simp only [Function.comp_apply, dRoot, signed, Bool.false_eq_true, ↓reduceIte,
        coordinateFunctional_add, coordinateFunctional_neg, parameterWeight_axis, difference, positiveSum] <;>
      abel_nf <;> tauto
  · rintro ⟨i, j, hij, (rfl | rfl | rfl | rfl)⟩
    · refine ⟨⟨⟨(i,j), hij⟩, false, true⟩, ?_⟩
      simp [dRoot, signed, coordinateFunctional_add, coordinateFunctional_neg,
        parameterWeight_axis, difference, sub_eq_add_neg]
    · refine ⟨⟨⟨(i,j), hij⟩, true, false⟩, ?_⟩
      simp [dRoot, signed, coordinateFunctional_add, coordinateFunctional_neg,
        parameterWeight_axis, difference]; abel
    · exact ⟨⟨⟨(i,j), hij⟩, false, false⟩, by
        simp [dRoot, signed, coordinateFunctional_add, parameterWeight_axis, positiveSum]⟩
    · exact ⟨⟨⟨(i,j), hij⟩, true, true⟩, by
        simp [dRoot, signed, coordinateFunctional_add, coordinateFunctional_neg, parameterWeight_axis, positiveSum, add_comm]⟩

private theorem roots_image {ι : Type} {n k : ℕ}
    (v : Fin k → Fin n → ℤ) (f : ι → Fin n → ℤ)
    (h : Set.range v = Set.range f) :
    Set.range (fun i => parameterWeight (v i)) = Set.range (parameterWeight ∘ f) := by
  change Set.range (parameterWeight ∘ v) = _
  rw [Set.range_comp, Set.range_comp, h]

private theorem signedWeight {n : ℕ} (i : Fin n) (s : Bool) :
    parameterWeight (signed i s) =
      if s then -(LinearMap.proj i : Dual ℂ (Params n)) else LinearMap.proj i := by
  cases s <;> simp [signed, coordinateFunctional_neg, parameterWeight_axis]

private theorem mem_range_elim {ι κ V : Type} (f : ι → V) (g : κ → V) (a : V) :
    a ∈ Set.range (Sum.elim f g) ↔ a ∈ Set.range f ∨ a ∈ Set.range g := by
  constructor
  · rintro ⟨(i | j), rfl⟩
    · exact Or.inl ⟨i,rfl⟩
    · exact Or.inr ⟨j,rfl⟩
  · rintro (⟨i,rfl⟩ | ⟨j,rfl⟩)
    · exact ⟨Sum.inl i,rfl⟩
    · exact ⟨Sum.inr j,rfl⟩

private theorem coordinateFunctional_comp {n : ℕ} {V : Type}
    [AddCommGroup V] [Module ℂ V] (g : V →ₗ[ℂ] Params n) (v : Fin n → ℤ) :
    coordinateFunctional g v = (parameterWeight v).comp g := by
  ext x
  simp only [LinearMap.comp_apply, coordinateFunctional_apply, LinearMap.id_apply]

private def realizeParameterizedRoots {L : Type} [LieRing L] [LieAlgebra ℂ L]
    [FiniteDimensional ℂ L] {H : LieSubalgebra ℂ L} {n k : ℕ}
    (v : Fin k → Fin n → ℤ) (e : Params n ≃ₗ[ℂ] H)
    (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (hlength : ∀ i, dot (v i) (v i) ≠ 0)
    (hdistinct : ∀ i j, i ≠ j → ∃ l, dot (v l) (v i) ≠ dot (v l) (v j))
    (hroots : ∀ a : Dual ℂ (Params n),
      a.comp e.symm.toLinearMap ∈ rootSet H ↔ a ∈ Set.range (parameterWeight ∘ v))
    (hc : ∀ i, e.symm (killingCoroot H ((parameterWeight (v i)).comp e.symm.toLinearMap)) =
      coordinateCoroot (v i)) : RealizedRoots L v := by
  let g := e.symm.toLinearMap
  let h i := killingCoroot H (coordinateFunctional g (v i))
  have hcoord (i : Fin k) : g (h i) = coordinateCoroot (v i) := by
    change g (killingCoroot H (coordinateFunctional g (v i))) = coordinateCoroot (v i)
    rw [coordinateFunctional_comp]
    exact hc i
  refine realizeRootsOfCoroots v g h hcoord hlength hdistinct ?_ hss hH (fun _ => rfl)
  ext a
  have ha : (a.comp e.toLinearMap).comp g = a := by ext x; simp [g]
  calc
    a ∈ rootSet H ↔ a.comp e.toLinearMap ∈ Set.range (parameterWeight ∘ v) :=
      by
        have ht := hroots (a.comp e.toLinearMap)
        change (a.comp e.toLinearMap).comp g ∈ rootSet H ↔ _ at ht
        rw [ha] at ht
        exact ht
    _ ↔ a ∈ Set.range (fun i => coordinateFunctional g (v i)) := by
      constructor
      · rintro ⟨i, hi⟩
        refine ⟨i, ?_⟩
        change coordinateFunctional g (v i) = a
        rw [coordinateFunctional_comp]
        exact (congrArg (fun b : Dual ℂ (Params n) => b.comp g) hi).trans ha
      · rintro ⟨i, rfl⟩
        refine ⟨i, ?_⟩
        change parameterWeight (v i) = (coordinateFunctional g (v i)).comp e.toLinearMap
        rw [coordinateFunctional_comp]
        ext t
        simp [g]

end ClassicalParameters


section TypeB

open Module
attribute [local instance 100] LieRing.ofAssociativeRing
open Specs.LieAlgebrasAndRepresentations.ClassicalRootsB
  (algebra diagonal weightSpace coordinateWeight listedRoots squaredLength epsilon)
private abbrev bMatrixCoroot := @Specs.LieAlgebrasAndRepresentations.ClassicalRootsB.coroot

private theorem bParameterRoots {n k : ℕ} (v : Fin k → Fin n → ℤ)
    (hv : Set.range v = Set.range (@bRoot n)) :
    Specs.LieAlgebrasAndRepresentations.ClassicalRootsB.roots n =
      Set.range (fun i => parameterWeight (v i)) := by
  rw [ClassicalRootsB.roots_eq n, roots_image v _ hv]
  ext a
  have hf : parameterWeight ∘ @bRoot n =
      Sum.elim (fun p : Fin n × Bool => parameterWeight (signed p.1 p.2))
        (parameterWeight ∘ @dRoot n) := by
    funext p
    cases p <;> rfl
  rw [hf]
  change a ∈ listedRoots n ↔
    a ∈ Set.range (Sum.elim (fun p : Fin n × Bool => parameterWeight (signed p.1 p.2))
      (parameterWeight ∘ @dRoot n))
  rw [mem_range_elim, dWeight_range]
  have h : a ∈ Set.range (fun p : Fin n × Bool => parameterWeight (signed p.1 p.2)) ↔
      ∃ i, a = epsilon i ∨ a = -epsilon i := by
    constructor
    · rintro ⟨⟨i,s⟩, rfl⟩
      exact ⟨i, by cases s <;> simp [signedWeight, epsilon]⟩
    · rintro ⟨i, (rfl | rfl)⟩
      · exact ⟨(i,false), by simp [signedWeight, epsilon]⟩
      · exact ⟨(i,true), by simp [signedWeight, epsilon]⟩
  rw [h]
  simp only [listedRoots, Set.mem_ofPred_eq, epsilon]
  apply or_congr_right
  apply exists_congr
  intro i
  apply exists_congr
  intro j
  dsimp only [difference, positiveSum]
  rw [neg_sub, sub_eq_add_neg (LinearMap.proj j), add_comm (LinearMap.proj j), neg_add,
    ← sub_eq_add_neg]
  rw [sub_eq_add_neg (-(LinearMap.proj i))]
  tauto

private def typeB {n k : ℕ} (v : Fin k → Fin n → ℤ)
    (hv : Set.range v = Set.range (@bRoot n))
    (hlength : ∀ i, dot (v i) (v i) ≠ 0)
    (hdistinct : ∀ i j, i ≠ j → ∃ l, dot (v l) (v i) ≠ dot (v l) (v j)) :
    RealizedRoots (algebra n) v := by
  obtain ⟨hss, hH, hmem, hcoroot⟩ := ClassicalMatrixCartans.type_b n
  let H := Specs.LieAlgebrasAndRepresentations.ClassicalRootsB.cartan n
  let coord := Specs.LieAlgebrasAndRepresentations.ClassicalRootsB.coordinates n
  let ch := @Specs.LieAlgebrasAndRepresentations.ClassicalRootsB.character n
  have hch : Function.Bijective ch := (ClassicalRootsB.cartan_identification n).2
  have hfun (z : Fin n → ℤ) : ch (parameterWeight z) = coordinateFunctional coord z := by
    ext x
    simp [coord, ch, Specs.LieAlgebrasAndRepresentations.ClassicalRootsB.character,
      coordinateFunctional_apply]
  have hr := bParameterRoots v hv
  have hroots : rootSet H = Set.range (fun i => coordinateFunctional coord (v i)) := by
    ext a
    obtain ⟨b, rfl⟩ := hch.2 a
    change ch b ∈ rootSet H ↔ _
    rw [hmem b, hr]
    simp only [Set.mem_range, ← hfun, hch.1.eq_iff]
  let h (i : Fin k) := killingCoroot H (coordinateFunctional coord (v i))
  have hcoord (i : Fin k) : coord (h i) = coordinateCoroot (v i) := by
    have ha : parameterWeight (v i) ∈ Specs.LieAlgebrasAndRepresentations.ClassicalRootsB.roots n :=
      hr.symm ▸ Set.mem_range_self i
    have he := hcoroot (parameterWeight (v i)) ha
    change ((killingCoroot H (ch (parameterWeight (v i))) : algebra n) : _) =
      bMatrixCoroot (parameterWeight (v i)) at he
    rw [hfun] at he
    funext j
    have hj := congrArg (fun X : Specs.LieAlgebrasAndRepresentations.ClassicalRootsB.Mat n =>
      X (some (Sum.inl j)) (some (Sum.inl j))) he
    change coord (h i) j = _ at hj
    rw [hj]
    simp [bMatrixCoroot, Specs.LieAlgebrasAndRepresentations.ClassicalRootsB.coroot,
      diagonal, coordinateWeight, epsilon, squaredLength, coordinateCoroot,
      parameterWeight_coordinate, dot_cast, pow_two]
  exact realizeRootsOfCoroots v coord h hcoord hlength hdistinct hroots hss hH (fun _ => rfl)

end TypeB


section TypeC

open Module
attribute [local instance 100] LieRing.ofAssociativeRing
open Specs.LieAlgebrasAndRepresentations.ClassicalRootsC (sp diagonal listedRoots eps)
private abbrev cMatrixCoroot := @Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.coroot

private theorem cParameterRoots {n k : ℕ} (v : Fin k → Fin n → ℤ)
    (hv : Set.range v = Set.range (@cRoot n)) :
    Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.rootSet n =
      Set.range (fun i => parameterWeight (v i)) := by
  rw [ClassicalRootsC.roots n, roots_image v _ hv]
  ext a
  have hf : parameterWeight ∘ @cRoot n =
      Sum.elim (fun p : Fin n × Bool => parameterWeight (2 • signed p.1 p.2))
        (parameterWeight ∘ @dRoot n) := by
    funext p
    cases p <;> rfl
  rw [hf, mem_range_elim, dWeight_range]
  apply or_congr_left
  change (∃ i : Fin n, a = (2 : ℂ) • eps i ∨ a = -((2 : ℂ) • eps i)) ↔ _
  have h (i : Fin n) (s : Bool) : parameterWeight (2 • signed i s) =
      (2 : ℂ) • (if s then -eps i else eps i) := by
    exact (coordinateFunctional_two _ _).trans
      (congrArg ((2 : ℂ) • ·) (signedWeight i s))
  constructor
  · rintro ⟨i, (rfl | rfl)⟩
    · exact ⟨(i,false), by dsimp only; rw [h]; rfl⟩
    · exact ⟨(i,true), by dsimp only; rw [h]; simp⟩
  · rintro ⟨⟨i,s⟩, rfl⟩
    exact ⟨i, by cases s <;> dsimp only <;> rw [h] <;> simp⟩

private def typeC {n k : ℕ} (v : Fin k → Fin n → ℤ)
    (hv : Set.range v = Set.range (@cRoot n))
    (hlength : ∀ i, dot (v i) (v i) ≠ 0)
    (hdistinct : ∀ i j, i ≠ j → ∃ l, dot (v l) (v i) ≠ dot (v l) (v j)) :
    RealizedRoots (sp n) v := by
  classical
  apply Classical.choice
  obtain ⟨hss, H, e, hH, he, hroots, hcoroot⟩ := ClassicalMatrixCartans.type_c n
  have hr := cParameterRoots v hv
  refine ⟨realizeParameterizedRoots v e hss hH hlength hdistinct
    (fun a => (hroots a).trans (by rw [hr]; rfl)) ?_⟩
  intro i
  let a := parameterWeight (v i)
  have ha : a ∈ Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.rootSet n := by
    rw [hr]
    exact Set.mem_range_self i
  let h := killingCoroot H (a.comp e.symm.toLinearMap)
  have hcoord : cMatrixCoroot a = diagonal (coordinateCoroot (v i)) := by
    change diagonal _ = _
    apply congrArg diagonal
    funext j
    simp [Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.euclidean,
      Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.coordinates, a,
      parameterWeight_coordinate, coordinateCoroot, dot_cast]
  have hm : ((h : sp n) : Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.Mat n) =
      diagonal (coordinateCoroot (v i)) := (hcoroot a ha).trans hcoord
  have hd := he (e.symm h)
  rw [LinearEquiv.apply_symm_apply, hm] at hd
  change e.symm h = _
  funext j
  simpa [diagonal] using congrArg
    (fun X : Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.Mat n =>
      X (Sum.inl j) (Sum.inl j)) hd.symm

end TypeC


section TypeD

open Module
attribute [local instance 100] LieRing.ofAssociativeRing
open Specs.LieAlgebrasAndRepresentations.ClassicalRootsD (algebra roots diagonal coordinate)
private abbrev dMatrixCoroot := Specs.LieAlgebrasAndRepresentations.ClassicalRootsD.coroot

private theorem dParameterRoots {n k : ℕ} (v : Fin k → Fin n → ℤ)
    (hv : Set.range v = Set.range (@dRoot n)) :
    roots n = Set.range (fun i => parameterWeight (v i)) := by
  rw [roots_image v _ hv]
  ext a
  rw [ClassicalRootsD.roots_ordered, dWeight_range]
  rfl

private def integralParameters {n : ℕ} (v : Fin n → ℤ) : Params n := fun i => (v i : ℂ)

private theorem dMatrixCoroot_coordinates {n : ℕ} (v : Fin n → ℤ) :
    dMatrixCoroot n (integralParameters v) = diagonal n (coordinateCoroot v) := by
  unfold dMatrixCoroot Specs.LieAlgebrasAndRepresentations.ClassicalRootsD.coroot
  apply congrArg (diagonal n)
  funext i
  simp [coordinateCoroot, Specs.LieAlgebrasAndRepresentations.ClassicalRootsD.dot,
    dot_cast, integralParameters, smul_eq_mul]

private def typeD {n k : ℕ} (hn : 2 ≤ n) (v : Fin k → Fin n → ℤ)
    (hv : Set.range v = Set.range (@dRoot n))
    (hlength : ∀ i, dot (v i) (v i) ≠ 0)
    (hdistinct : ∀ i j, i ≠ j → ∃ l, dot (v l) (v i) ≠ dot (v l) (v j)) :
    RealizedRoots (algebra n) v := by
  classical
  apply Classical.choice
  obtain ⟨hss, H, e, hH, he, hroots, hcoroot⟩ := ClassicalMatrixCartans.type_d n (by omega)
  have hr := dParameterRoots v hv
  refine ⟨realizeParameterizedRoots v e hss hH hlength hdistinct
    (fun a => (hroots a).trans (by rw [hr]; rfl)) ?_⟩
  intro i
  let a := parameterWeight (v i)
  have ha : a ∈ roots n := by
    rw [hr]
    exact Set.mem_range_self i
  let h := killingCoroot H (a.comp e.symm.toLinearMap)
  have hc : (fun j => a (coordinate n j)) = integralParameters (v i) :=
    funext (parameterWeight_coordinate (v i))
  have hm : ((h : algebra n) : Specs.LieAlgebrasAndRepresentations.ClassicalRootsD.Mat n) =
      diagonal n (coordinateCoroot (v i)) := by
    have hb := hcoroot a ha
    rw [hc] at hb
    exact hb.trans (dMatrixCoroot_coordinates (v i))
  apply ClassicalRootsD.diagonal_injective (n := n)
  have hd := he (e.symm h)
  rw [LinearEquiv.apply_symm_apply, hm] at hd
  exact hd.symm

end TypeD


private theorem range_b1 : Set.range b1 = Set.range (@bRoot 1) :=
  range_eq_of_finite_checks _ _ (by decide) (by decide)
private theorem range_c1 : Set.range c1 = Set.range (@cRoot 1) :=
  range_eq_of_finite_checks _ _ (by decide) (by decide)
private theorem range_a1 : Set.range a1 = Set.range (@aRoot 2) :=
  range_eq_of_finite_checks _ _ (by decide) (by decide)
private theorem range_b2 : Set.range b2 = Set.range (@bRoot 2) :=
  range_eq_of_finite_checks _ _ (by decide) (by decide)
private theorem range_c2 : Set.range c2 = Set.range (@cRoot 2) :=
  range_eq_of_finite_checks _ _ (by decide) (by decide)
private theorem range_d2 : Set.range d2 = Set.range (@dRoot 2) :=
  range_eq_of_finite_checks _ _ (by decide) (by decide)
private theorem range_d3 : Set.range d3 = Set.range (@dRoot 3) :=
  range_eq_of_finite_checks _ _ (by decide) (by decide)
private theorem range_a3 : Set.range a3 = Set.range (@aRoot 4) :=
  range_eq_of_finite_checks _ _ (by decide) (by decide)

private def realizedA1 : RealizedRoots (A 1) a1 :=
  typeA a1 range_a1 (by decide) (by decide)

theorem b1_a1 : b1_a1_type :=
  reconstruct (typeB b1 range_b1 (by decide) (by decide)) realizedA1
    (r := 2) (s := 1) (by decide) (by decide) (by decide)

theorem c1_a1 : c1_a1_type :=
  reconstruct (typeC c1 range_c1 (by decide) (by decide)) realizedA1
    (r := 1) (s := 2) (by decide) (by decide) (by decide)

theorem b2_c2 : b2_c2_type :=
  reconstruct (typeB b2 range_b2 (by decide) (by decide))
    (typeC c2 range_c2 (by decide) (by decide))
    (r := 2) (s := 1) (by decide) (by decide) (by decide)

theorem d3_a3 : d3_a3_type :=
  reconstruct (typeD (by decide) d3 range_d3 (by decide) (by decide))
    (typeA a3 range_a3 (by decide) (by decide))
    (r := 1) (s := 1) (by decide) (by decide) (by decide)


section TypeAOneSum

open Module
open private trace_zero all_weight_spaces_span from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClassicalRootsA
open ClassicalRootsA (root_set root_dimension)
open Specs.LieAlgebrasAndRepresentations.ClassicalRootsA (cartan root rootVector epsilon)

private abbrev H₁ := cartan 1
private abbrev L₁ := A 1

private def productCartan : LieSubalgebra ℂ (L₁ × L₁) where
  toSubmodule := H₁.toSubmodule.prod H₁.toSubmodule
  lie_mem' := fun hx hy => ⟨H₁.lie_mem hx.1 hy.1, H₁.lie_mem hx.2 hy.2⟩

private abbrev K := productCartan
private def leftCartan : K →ₗ[ℂ] H₁ where
  toFun x := ⟨x.val.1, x.property.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def rightCartan : K →ₗ[ℂ] H₁ where
  toFun x := ⟨x.val.2, x.property.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def leftDiagonal (h : H₁) : K := ⟨(h.val, 0), h.property, H₁.zero_mem⟩
private def rightDiagonal (h : H₁) : K := ⟨(0, h.val), H₁.zero_mem, h.property⟩

private def leftWeight (a : Dual ℂ H₁) := a.comp leftCartan
private def rightWeight (a : Dual ℂ H₁) := a.comp rightCartan

private theorem left_mem {a : Dual ℂ H₁} {x : L₁} (hx : x ∈ rootSpace H₁ a) :
    (x, 0) ∈ rootSpace K (leftWeight a) := by
  rw [mem_rootSpace] at hx ⊢
  intro h
  exact Prod.ext (hx (leftCartan h)) (by simp)

private theorem right_mem {a : Dual ℂ H₁} {x : L₁} (hx : x ∈ rootSpace H₁ a) :
    (0, x) ∈ rootSpace K (rightWeight a) := by
  rw [mem_rootSpace] at hx ⊢
  intro h
  exact Prod.ext (by simp) (hx (rightCartan h))

private theorem left_space (a : Dual ℂ H₁) (ha : a ≠ 0) :
    rootSpace K (leftWeight a) =
      (rootSpace H₁ a).map (LieHom.inl ℂ L₁ L₁).toLinearMap := by
  ext x
  constructor
  · intro hx
    rw [mem_rootSpace] at hx
    obtain ⟨h, hh⟩ := DFunLike.ne_iff.mp ha
    have hx₂ := congrArg Prod.snd (hx (leftDiagonal h))
    change ⁅0, x.2⁆ = a h • x.2 at hx₂
    rw [zero_lie] at hx₂
    have h₂ := (smul_eq_zero.mp hx₂.symm).resolve_left hh
    refine ⟨x.1, (mem_rootSpace _ _ _).mpr fun y => congrArg Prod.fst (hx (leftDiagonal y)), ?_⟩
    exact Prod.ext rfl h₂.symm
  · rintro ⟨y, hy, rfl⟩
    exact left_mem hy

private theorem right_space (a : Dual ℂ H₁) (ha : a ≠ 0) :
    rootSpace K (rightWeight a) =
      (rootSpace H₁ a).map (LieHom.inr ℂ L₁ L₁).toLinearMap := by
  ext x
  constructor
  · intro hx
    rw [mem_rootSpace] at hx
    obtain ⟨h, hh⟩ := DFunLike.ne_iff.mp ha
    have hx₁ := congrArg Prod.fst (hx (rightDiagonal h))
    change ⁅0, x.1⁆ = a h • x.1 at hx₁
    rw [zero_lie] at hx₁
    have h₁ := (smul_eq_zero.mp hx₁.symm).resolve_left hh
    refine ⟨x.2, (mem_rootSpace _ _ _).mpr fun y => congrArg Prod.snd (hx (rightDiagonal y)), ?_⟩
    exact Prod.ext h₁.symm rfl
  · rintro ⟨y, hy, rfl⟩
    exact right_mem hy

private theorem prod_root (a : Dual ℂ K) :
    a ∈ rootSet K ↔ ∃ b ∈ rootSet H₁, a = leftWeight b ∨ a = rightWeight b := by
  constructor
  · rintro ⟨ha, hw⟩
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hw
    rw [mem_rootSpace] at hx
    by_cases h₁ : x.1 = 0
    · have h₂ : x.2 ≠ 0 := fun hz => hx0 (Prod.ext h₁ hz)
      let b : Dual ℂ H₁ :=
        { toFun := fun h => a (rightDiagonal h)
          map_add' := fun y z => by rw [show rightDiagonal (y+z) = rightDiagonal y + rightDiagonal z
                            from Subtype.ext (Prod.ext (zero_add _).symm rfl), map_add]
          map_smul' := fun c y => by rw [show rightDiagonal (c • y) = c • rightDiagonal y
                            from Subtype.ext (Prod.ext (smul_zero _).symm rfl), map_smul, RingHom.id_apply] }
      have h : a = rightWeight b := by
        apply LinearMap.ext
        intro z
        have hz : z = leftDiagonal (leftCartan z) + rightDiagonal (rightCartan z) :=
          Subtype.ext (Prod.ext ((add_zero _).symm) ((zero_add _).symm))
        have hs := congrArg Prod.snd (hx (leftDiagonal (leftCartan z)))
        change ⁅0, x.2⁆ = a (leftDiagonal (leftCartan z)) • x.2 at hs
        rw [zero_lie] at hs
        have hh := (smul_eq_zero.mp hs.symm).resolve_right h₂
        conv_lhs => rw [hz]
        rw [map_add, hh, zero_add]
        rfl
      have hb : b ≠ 0 := fun he => ha (h.trans (by rw [he]; rfl))
      have hx' : x.2 ∈ rootSpace H₁ b :=
        (mem_rootSpace _ _ _).mpr fun y => congrArg Prod.snd (hx (rightDiagonal y))
      exact ⟨b, ⟨hb, (Submodule.ne_bot_iff _).mpr ⟨_, hx', h₂⟩⟩, Or.inr h⟩
    · let b : Dual ℂ H₁ :=
        { toFun := fun h => a (leftDiagonal h)
          map_add' := fun y z => by rw [show leftDiagonal (y+z) = leftDiagonal y + leftDiagonal z
                            from Subtype.ext (Prod.ext rfl (zero_add _).symm), map_add]
          map_smul' := fun c y => by rw [show leftDiagonal (c • y) = c • leftDiagonal y
                            from Subtype.ext (Prod.ext rfl (smul_zero _).symm), map_smul, RingHom.id_apply] }
      have h : a = leftWeight b := by
        apply LinearMap.ext
        intro z
        have hz : z = leftDiagonal (leftCartan z) + rightDiagonal (rightCartan z) :=
          Subtype.ext (Prod.ext ((add_zero _).symm) ((zero_add _).symm))
        have hs := congrArg Prod.fst (hx (rightDiagonal (rightCartan z)))
        change ⁅0, x.1⁆ = a (rightDiagonal (rightCartan z)) • x.1 at hs
        rw [zero_lie] at hs
        have hh := (smul_eq_zero.mp hs.symm).resolve_right h₁
        conv_lhs => rw [hz]
        rw [map_add, hh, add_zero]
        rfl
      have hb : b ≠ 0 := fun he => ha (h.trans (by rw [he]; rfl))
      have hx' : x.1 ∈ rootSpace H₁ b :=
        (mem_rootSpace _ _ _).mpr fun y => congrArg Prod.fst (hx (leftDiagonal y))
      exact ⟨b, ⟨hb, (Submodule.ne_bot_iff _).mpr ⟨_, hx', h₁⟩⟩, Or.inl h⟩
  · rintro ⟨b, ⟨hb, hw⟩, (rfl | rfl)⟩
    · refine ⟨fun he => hb (LinearMap.ext fun h => congrArg
        (fun c : Dual ℂ K => c (leftDiagonal h)) he), ?_⟩
      change rootSpace K (leftWeight b) ≠ ⊥
      rw [left_space b hb]
      exact fun he => hw (Submodule.map_injective_of_injective (LieHom.inl_injective (R := ℂ) (L₁ := L₁) (L₂ := L₁))
        (he.trans (Submodule.map_bot _).symm))
    · refine ⟨fun he => hb (LinearMap.ext fun h => congrArg
        (fun c : Dual ℂ K => c (rightDiagonal h)) he), ?_⟩
      change rootSpace K (rightWeight b) ≠ ⊥
      rw [right_space b hb]
      exact fun he => hw (Submodule.map_injective_of_injective (LieHom.inr_injective (R := ℂ) (L₁ := L₁) (L₂ := L₁))
        (he.trans (Submodule.map_bot _).symm))

private theorem product_span : (⨆ a : Dual ℂ K, rootSpace K a) = ⊤ := by
  let S := ⨆ a : Dual ℂ K, rootSpace K a
  have hs := all_weight_spaces_span 1
  have hL (x : L₁) : (x, 0) ∈ S := by
    suffices h : (⊤ : Submodule ℂ L₁) ≤ S.comap (LieHom.inl ℂ L₁ L₁).toLinearMap from
      h (Submodule.mem_top (R := ℂ))
    rw [← hs]
    exact iSup_le fun a x hx => le_iSup (rootSpace K) (leftWeight a) (left_mem hx)
  have hR (x : L₁) : (0, x) ∈ S := by
    suffices h : (⊤ : Submodule ℂ L₁) ≤ S.comap (LieHom.inr ℂ L₁ L₁).toLinearMap from
      h (Submodule.mem_top (R := ℂ))
    rw [← hs]
    exact iSup_le fun a x hx => le_iSup (rootSpace K) (rightWeight a) (right_mem hx)
  apply top_unique
  intro x _
  have hh := S.add_mem (hL x.1) (hR x.2)
  simpa using hh

private theorem product_zero : rootSpace K 0 = K.toSubmodule := by
  ext x
  have h₀ := ClassicalRootsA.zero_space 1
  rw [mem_rootSpace]
  simp only [LinearMap.zero_apply, zero_smul]
  constructor
  · intro hx
    have h₁ : x.1 ∈ rootSpace H₁ 0 := (mem_rootSpace _ _ _).mpr fun y => by
      rw [LinearMap.zero_apply, zero_smul]
      exact congrArg Prod.fst (hx (leftDiagonal y))
    have h₂ : x.2 ∈ rootSpace H₁ 0 := (mem_rootSpace _ _ _).mpr fun y => by
      rw [LinearMap.zero_apply, zero_smul]
      exact congrArg Prod.snd (hx (rightDiagonal y))
    rw [h₀] at h₁ h₂
    exact ⟨h₁, h₂⟩
  · rintro ⟨hl, hr⟩ h
    have h₁ : x.1 ∈ rootSpace H₁ 0 := h₀.symm ▸ hl
    have h₂ : x.2 ∈ rootSpace H₁ 0 := h₀.symm ▸ hr
    apply Prod.ext
    · change ⁅(leftCartan h : L₁), x.1⁆ = 0
      simpa only [LinearMap.zero_apply, zero_smul] using
        (mem_rootSpace H₁ 0 x.1).mp h₁ (leftCartan h)
    · change ⁅(rightCartan h : L₁), x.2⁆ = 0
      simpa only [LinearMap.zero_apply, zero_smul] using
        (mem_rootSpace H₁ 0 x.2).mp h₂ (rightCartan h)

private def productCoordinates : K →ₗ[ℂ] (Fin 4 → ℂ) :=
  LinearMap.pi ![(epsilon 1 0).comp leftCartan, (epsilon 1 1).comp leftCartan,
    (epsilon 1 0).comp rightCartan, (epsilon 1 1).comp rightCartan]

private def productCoroots : Fin 4 → K :=
  ![leftDiagonal (aMatrixCoroot 1 0 1), leftDiagonal (aMatrixCoroot 1 1 0),
    rightDiagonal (aMatrixCoroot 1 0 1), rightDiagonal (aMatrixCoroot 1 1 0)]

private def productWeights : Fin 4 → Dual ℂ K :=
  ![leftWeight (root 1 0 1), leftWeight (root 1 1 0),
    rightWeight (root 1 0 1), rightWeight (root 1 1 0)]

private theorem product_weight_formula (i : Fin 4) :
    coordinateFunctional productCoordinates (a1Sum i) = productWeights i := by
  apply LinearMap.ext
  intro x
  fin_cases i <;> simp [coordinateFunctional_apply, a1Sum, productCoordinates, productWeights,
    leftWeight, rightWeight, root, Fin.sum_univ_four] <;> ring

private theorem a1_roots (a : Dual ℂ H₁) :
    a ∈ rootSet H₁ ↔ a = root 1 0 1 ∨ a = root 1 1 0 := by
  rw [root_set 1]
  constructor
  · rintro ⟨i,j,h,rfl⟩
    fin_cases i <;> fin_cases j <;> simp_all
  · rintro (rfl | rfl)
    · exact ⟨0,1,by decide,rfl⟩
    · exact ⟨1,0,by decide,rfl⟩

private theorem product_root_range :
    rootSet K = Set.range (fun i => coordinateFunctional productCoordinates (a1Sum i)) := by
  simp_rw [product_weight_formula]
  ext a
  rw [prod_root]
  constructor
  · rintro ⟨b, hb, (rfl | rfl)⟩ <;> rw [a1_roots] at hb <;> rcases hb with rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩
  · rintro ⟨i,rfl⟩
    fin_cases i
    · exact ⟨_, (a1_roots _).mpr (Or.inl rfl), Or.inl rfl⟩
    · exact ⟨_, (a1_roots _).mpr (Or.inr rfl), Or.inl rfl⟩
    · exact ⟨_, (a1_roots _).mpr (Or.inl rfl), Or.inr rfl⟩
    · exact ⟨_, (a1_roots _).mpr (Or.inr rfl), Or.inr rfl⟩

private theorem product_coroot_formula (i : Fin 4) :
    productCoordinates (productCoroots i) = coordinateCoroot (a1Sum i) := by
  have evaluate (l : Fin 2) (h : H₁) : epsilon 1 l h = h.val.val l l := rfl
  funext j
  fin_cases i <;> fin_cases j <;>
    norm_num [productCoordinates, productCoroots, coordinateCoroot, a1Sum, dot,
      leftCartan, rightCartan, leftDiagonal, rightDiagonal, evaluate,
      ClassicalRootsA.coroot_apply, Matrix.single_apply, Fin.sum_univ_four, aMatrixCoroot]

private theorem a1_cartan_separates (h : H₁) (hh : root 1 0 1 h = 0) : h = 0 := by
  have hdiff : epsilon 1 0 h - epsilon 1 1 h = 0 := hh
  have hsum := trace_zero h
  rw [Fin.sum_univ_two] at hsum
  change epsilon 1 0 h + epsilon 1 1 h = 0 at hsum
  have h0 : epsilon 1 0 h = 0 := by linear_combination (hsum + hdiff) / 2
  have h1 : epsilon 1 1 h = 0 := by linear_combination (hsum - hdiff) / 2
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · exact h0
  · exact h.property (by decide)
  · exact h.property (by decide)
  · exact h1

private def realizedA1Sum : RealizedRoots (L₁ × L₁) a1Sum := by
  apply realizeRoots a1Sum productCoordinates productCoroots product_coroot_formula
    (by decide) (by decide) product_root_range product_span product_zero
  · intro x hx
    have hL : root 1 0 1 (leftCartan x) = 0 := by simpa [product_weight_formula, productWeights, leftWeight] using hx 0
    have hR : root 1 0 1 (rightCartan x) = 0 := by simpa [product_weight_formula, productWeights, rightWeight] using hx 2
    exact Subtype.ext (Prod.ext (congrArg Subtype.val (a1_cartan_separates _ hL))
      (congrArg Subtype.val (a1_cartan_separates _ hR)))
  · intro a
    obtain ⟨b,hb,he⟩ := (prod_root a.val).mp a.property
    have hd : finrank ℂ (rootSpace H₁ b) = 1 := by
      obtain ⟨i,j,hij,rfl⟩ := (root_set 1 b).mp hb
      exact root_dimension 1 i j hij
    rcases he with h | h
    · rw [h, left_space b hb.1]
      exact (Submodule.equivMapOfInjective _
        (LieHom.inl_injective (R := ℂ) (L₁ := L₁) (L₂ := L₁)) (rootSpace H₁ b)).finrank_eq.symm.trans hd
    · rw [h, right_space b hb.1]
      exact (Submodule.equivMapOfInjective _
        (LieHom.inr_injective (R := ℂ) (L₁ := L₁) (L₂ := L₁)) (rootSpace H₁ b)).finrank_eq.symm.trans hd
  · intro i
    have left (i j : Fin 2) (hij : i ≠ j) :
        ∃ E F : L₁ × L₁, E ∈ rootSpace K (leftWeight (root 1 i j)) ∧
          F ∈ rootSpace K (-leftWeight (root 1 i j)) ∧
          ⁅E,F⁆ = (leftDiagonal (aMatrixCoroot 1 i j) : L₁ × L₁) := by
      refine ⟨(rootVector 1 i j hij, 0), (rootVector 1 j i hij.symm, 0),
        left_mem (ClassicalRootsA.rootVector_mem _ _ _), ?_,
        Prod.ext (ClassicalRootsA.root_triple 1 i j hij).1
          (by change ⁅(0 : L₁), 0⁆ = 0; simp)⟩
      have he : -leftWeight (root 1 i j) = leftWeight (root 1 j i) := by
        ext x
        simp [leftWeight, root, neg_sub]
      rw [he]
      exact left_mem (ClassicalRootsA.rootVector_mem _ _ _)
    have right (i j : Fin 2) (hij : i ≠ j) :
        ∃ E F : L₁ × L₁, E ∈ rootSpace K (rightWeight (root 1 i j)) ∧
          F ∈ rootSpace K (-rightWeight (root 1 i j)) ∧
          ⁅E,F⁆ = (rightDiagonal (aMatrixCoroot 1 i j) : L₁ × L₁) := by
      refine ⟨(0, rootVector 1 i j hij), (0, rootVector 1 j i hij.symm),
        right_mem (ClassicalRootsA.rootVector_mem _ _ _), ?_,
        Prod.ext (by change ⁅(0 : L₁), 0⁆ = 0; simp)
          (ClassicalRootsA.root_triple 1 i j hij).1⟩
      have he : -rightWeight (root 1 i j) = rightWeight (root 1 j i) := by
        ext x
        simp [rightWeight, root, neg_sub]
      rw [he]
      exact right_mem (ClassicalRootsA.rootVector_mem _ _ _)
    rw [product_weight_formula]
    fin_cases i
    · exact left 0 1 (by decide)
    · exact left 1 0 (by decide)
    · exact right 0 1 (by decide)
    · exact right 1 0 (by decide)

theorem d2_a1_sum : d2_a1_sum_type :=
  reconstruct (typeD (by decide) d2 range_d2 (by decide) (by decide)) realizedA1Sum
    (r := 1) (s := 1) (by decide) (by decide) (by decide)

end TypeAOneSum


end LieAlgebrasAndRepresentations.ClassicalLowRank
