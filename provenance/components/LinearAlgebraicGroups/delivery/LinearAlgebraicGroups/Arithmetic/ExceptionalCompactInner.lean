import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalCompactInner
import LinearAlgebraicGroups.Arithmetic.ExceptionalAdjointPolarPaths
import LinearAlgebraicGroups.Arithmetic.ExceptionalLieAutomorphismTransport
import LinearAlgebraicGroups.Arithmetic.ExceptionalTorsionCentralizers
import LinearAlgebraicGroups.Arithmetic.ExceptionalComplexPointGeometry
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.Matrix.Reindex
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ExceptionalCoordinateE
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Maps.Proper.Basic

set_option maxRecDepth 4096

open scoped Matrix

open LinearAlgebraicGroups.Specs.AbsoluteDynkinTypes
  (CartanRoots reflectCoordinates simpleCharacter)
open LinearAlgebraicGroups.Specs.ExceptionalCompactInner
open LieAlgebrasAndRepresentations
open ExceptionalE (e8List e8Roots simpleQ)
open ExceptionalGF (QVec dot realize)

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalCompactInner

/-- The scaled columns of the inverse Cartan matrices for the
coefficient-one vertices, in the simple coroot basis. -/
theorem exceptionalCoweightColumns :
    CartanMatrix.E 6 *ᵥ (![4, 3, 5, 6, 4, 2] : Fin 6 → ℤ) = Pi.single 0 3 ∧
    CartanMatrix.E 6 *ᵥ (![2, 3, 4, 6, 5, 4] : Fin 6 → ℤ) = Pi.single 5 3 ∧
    CartanMatrix.E 7 *ᵥ (![2, 3, 4, 6, 5, 4, 3] : Fin 7 → ℤ) = Pi.single 6 2 := by
  refine ⟨funext ?_, funext ?_, funext ?_⟩ <;> decide

private theorem alcoveVertexIntegralEquation {n : ℕ} {m : Fin n → ℤ}
    {i : Fin n} {x : Fin n → ℤ}
    (h : IsNonzeroAlcoveVertex m i (fun j => (x j : ℝ))) :
    ∀ j, m i * (x ᵥ* CartanMatrix.E n) j = (Pi.single i 1 : Fin n → ℤ) j := by
  intro j
  specialize h j
  change (m i : ℝ) * (∑ k, (x k : ℝ) * (CartanMatrix.E n k j : ℝ)) = _ at h
  have hcast : (Pi.single i 1 : Fin n → ℝ) j =
      ((Pi.single i 1 : Fin n → ℤ) j : ℝ) := by
    by_cases hij : j = i <;> simp [hij]
  rw [hcast] at h
  exact_mod_cast h

private theorem alcoveVertex_coefficient_one {n : ℕ} {m : Fin n → ℤ}
    {i : Fin n} {x : Fin n → ℤ} (hm : 0 < m i)
    (h : IsNonzeroAlcoveVertex m i (fun j => (x j : ℝ))) : m i = 1 := by
  have hprod := alcoveVertexIntegralEquation h i
  rw [Pi.single_eq_same] at hprod
  have hdvd : m i ∣ (1 : ℤ) := ⟨_, hprod.symm⟩
  exact Int.eq_one_of_dvd_one hm.le hdvd

private theorem alcoveVertex_dvd_column {n : ℕ} {m : Fin n → ℤ}
    {i j : Fin n} {x v : Fin n → ℤ} {d : ℤ} (hm : m i = 1)
    (h : IsNonzeroAlcoveVertex m i (fun k => (x k : ℝ)))
    (hv : CartanMatrix.E n *ᵥ v = Pi.single j d) : d ∣ v i := by
  have hrow : x ᵥ* CartanMatrix.E n = Pi.single i 1 := by
    funext k
    simpa only [hm, one_mul] using alcoveVertexIntegralEquation h k
  refine ⟨x j, ?_⟩
  calc
    v i = (Pi.single i 1 : Fin n → ℤ) ⬝ᵥ v := by simp
    _ = x ⬝ᵥ (CartanMatrix.E n *ᵥ v) := by
      rw [Matrix.dotProduct_mulVec, hrow]
    _ = d * x j := by rw [hv]; simp [mul_comm]

private def corootPair {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (v : Fin n → ℤ) :=
  (A *ᵥ v, v)

private def reflectCoroot {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (i : Fin n) (v : Fin n → ℤ) :=
  v - (A *ᵥ v) i • Pi.single i 1

private theorem reflectCorootPair {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : A.transpose = A) (i : Fin n) (v : Fin n → ℤ) :
    reflectCoordinates A i (corootPair A v) = corootPair A (reflectCoroot A i v) := by
  have hrow : (v ᵥ* A) i = (A *ᵥ v) i := by
    rw [← hA, Matrix.vecMul_transpose, hA]
  change (_ - _ • _, v - (v ᵥ* A) i • _) = _
  rw [hrow]
  simp only [corootPair, reflectCoroot, Matrix.mulVec_sub, Matrix.mulVec_smul,
    Matrix.mulVec_single_one]
  rfl

/-- The simple-root basis of the Euclidean E₈ model, with columns restricted
to the first `n` simple roots for E₆ and E₇. -/
private def simpleColumns {n : ℕ} (hn : n ≤ 8) : Matrix (Fin 8) (Fin n) ℚ :=
  Matrix.of fun j i => simpleQ (i.castLE hn) j

/-- Inverse of the simple-root basis in the standard Euclidean coordinates. -/
private def coordinateRows : Matrix (Fin 8) (Fin 8) ℚ :=
  !![0, 0, 0, 0, 0, 0, 0, 2;
    1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 5/2;
    -1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 7/2;
    0, 0, 1, 1, 1, 1, 1, 5;
    0, 0, 0, 1, 1, 1, 1, 4;
    0, 0, 0, 0, 1, 1, 1, 3;
    0, 0, 0, 0, 0, 1, 1, 2;
    0, 0, 0, 0, 0, 0, 1, 1]

private theorem simpleColumns_gram {n : ℕ} {hn : n ≤ 8}
    (h : n = 6 ∨ n = 7 ∨ n = 8) :
    (simpleColumns hn).transpose * simpleColumns hn = (CartanMatrix.E n).map (Int.cast : ℤ → ℚ) := by
  rcases h with rfl | rfl | rfl
  · have hh : ∀ i j : Fin 6, ((simpleColumns (by decide : 6 ≤ 8)).transpose *
        simpleColumns (by decide : 6 ≤ 8)) i j = ((CartanMatrix.E 6 i j : ℤ) : ℚ) := by
      decide +kernel
    exact Matrix.ext hh
  · have hh : ∀ i j : Fin 7, ((simpleColumns (by decide : 7 ≤ 8)).transpose *
        simpleColumns (by decide : 7 ≤ 8)) i j = ((CartanMatrix.E 7 i j : ℤ) : ℚ) := by
      decide +kernel
    exact Matrix.ext hh
  · have hh : ∀ i j : Fin 8, ((simpleColumns (by decide : 8 ≤ 8)).transpose *
        simpleColumns (by decide : 8 ≤ 8)) i j = ((CartanMatrix.E 8 i j : ℤ) : ℚ) := by
      decide +kernel
    exact Matrix.ext hh

private theorem coordinateRows_mul_simpleColumns {n : ℕ} {hn : n ≤ 8}
    (h : n = 6 ∨ n = 7 ∨ n = 8) (i : Fin 8) (j : Fin n) :
    (coordinateRows * simpleColumns hn) i j = if i.val = j.val then 1 else 0 := by
  rcases h with rfl | rfl | rfl
  · exact (show ∀ a : Fin 8, ∀ b : Fin 6,
      (coordinateRows * simpleColumns (by decide : 6 ≤ 8)) a b =
        if a.val = b.val then 1 else 0 by decide +kernel) i j
  · exact (show ∀ a : Fin 8, ∀ b : Fin 7,
      (coordinateRows * simpleColumns (by decide : 7 ≤ 8)) a b =
        if a.val = b.val then 1 else 0 by decide +kernel) i j
  · exact (show ∀ a b : Fin 8,
      (coordinateRows * simpleColumns (by decide : 8 ≤ 8)) a b =
        if a.val = b.val then 1 else 0 by decide +kernel) i j

private theorem eCartan_transpose (n : ℕ) : (CartanMatrix.E n).transpose = CartanMatrix.E n := by
  apply Matrix.ext
  intro i j
  simp [CartanMatrix.E, eq_comm, or_comm, or_left_comm, or_assoc]

private theorem cartanRoots_mem_e8List {n : ℕ} (hn : n ≤ 8) (h : n = 6 ∨ n = 7 ∨ n = 8)
    {p : (Fin n → ℤ) × (Fin n → ℤ)} (hp : CartanRoots (CartanMatrix.E n) p) :
    simpleColumns hn *ᵥ (fun i => (p.2 i : ℚ)) ∈ e8List := by
  have hReflect {a b : QVec 8} (ha : a ∈ e8List) (hb : b ∈ e8List) :
      ExceptionalGF.reflect a b ∈ e8List := by
    have har : realize a ∈ e8Roots := ⟨a, ha, rfl⟩
    have hbr : realize b ∈ e8Roots := ⟨b, hb, rfl⟩
    obtain ⟨c, hc, he⟩ := ExceptionalE.e8_isRootSystem.reflection_mem _ har _ hbr
    rw [← ExceptionalGF.realize_reflect] at he
    exact ExceptionalGF.realize_injective he ▸ hc
  let S := simpleColumns hn
  induction hp with
  | simple i =>
    change S *ᵥ (fun j => (((Pi.single i 1 : Fin n → ℤ) j) : ℚ)) ∈ e8List
    have hs : (fun j => (((Pi.single i 1 : Fin n → ℤ) j) : ℚ)) =
        (Pi.single i 1 : Fin n → ℚ) := by
      funext j
      by_cases hij : j = i <;> simp [hij]
    rw [hs, Matrix.mulVec_single_one]
    exact ExceptionalE.simple_mem_q (i.castLE hn)
  | neg hp ih =>
    rename_i p
    let q := S *ᵥ (fun j => (p.2 j : ℚ))
    have he : ExceptionalGF.reflect q q = -q := by
      rw [ExceptionalGF.reflect, ExceptionalE.e8_list_norm _ ih]
      rw [show (2 : ℚ) * 2 / 2 = 2 by norm_num, two_smul]
      abel
    change S *ᵥ (fun j => ((-p.2 j : ℤ) : ℚ)) ∈ e8List
    simp only [Int.cast_neg]
    rw [show (fun j => -(p.2 j : ℚ)) = -(fun j => (p.2 j : ℚ)) from rfl, Matrix.mulVec_neg]
    exact he ▸ hReflect ih ih
  | reflect i hp ih =>
    rename_i p
    let v := p.2
    let q := S *ᵥ (fun j => (v j : ℚ))
    let a := simpleQ (i.castLE hn)
    have ha := ExceptionalE.simple_mem_q (i.castLE hn)
    have hA := eCartan_transpose n
    have hrow : (v ᵥ* CartanMatrix.E n) i = (CartanMatrix.E n *ᵥ v) i := by
      rw [← hA, Matrix.vecMul_transpose, hA]
    have hdot : dot q a = ((CartanMatrix.E n *ᵥ v) i : ℚ) := by
      calc
        dot q a = dotProduct a q := dotProduct_comm _ _
        _ = (S.transpose *ᵥ (S *ᵥ (fun j => (v j : ℚ)))) i := rfl
        _ = ((S.transpose * S) *ᵥ (fun j => (v j : ℚ))) i := by
          rw [Matrix.mulVec_mulVec]
        _ = _ := by
          rw [simpleColumns_gram h]
          exact (RingHom.map_mulVec (Int.castRingHom ℚ) _ _ _).symm
    let b := (CartanMatrix.E n *ᵥ v) i
    have hcast : (fun j => (((v - b • (Pi.single i 1 : Fin n → ℤ)) j : ℤ) : ℚ)) =
        (fun j => (v j : ℚ)) - (b : ℚ) • Pi.single i 1 := by
      funext j
      by_cases hij : j = i <;>
        simp [hij, Pi.smul_apply, zsmul_eq_mul]
    change S *ᵥ (fun j => (((v - (v ᵥ* CartanMatrix.E n) i • (Pi.single i 1 : Fin n → ℤ)) j : ℤ) : ℚ)) ∈ e8List
    rw [hrow, hcast, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_single_one]
    have hmem := hReflect ha ih
    rw [ExceptionalGF.reflect, ExceptionalE.e8_list_norm _ ha, hdot] at hmem
    have hscalar : (2 : ℚ) * (b : ℚ) / 2 = b := by ring
    rw [hscalar] at hmem
    exact hmem

private theorem cartanRoots_coordinates {n : ℕ} (hn : n ≤ 8) (h : n = 6 ∨ n = 7 ∨ n = 8)
    {p : (Fin n → ℤ) × (Fin n → ℤ)} (hp : CartanRoots (CartanMatrix.E n) p) :
    ∃ q ∈ e8List,
      (∀ i : Fin n, (coordinateRows *ᵥ q) (i.castLE hn) = (p.2 i : ℚ)) ∧
      (∀ i : Fin 8, n ≤ i.val → (coordinateRows *ᵥ q) i = 0) := by
  let q := simpleColumns hn *ᵥ (fun j => (p.2 j : ℚ))
  have he (i : Fin 8) : (coordinateRows *ᵥ q) i =
      ∑ j : Fin n, (if i.val = j.val then 1 else 0) * (p.2 j : ℚ) := by
    dsimp only [q]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec]
    simp only [dotProduct, coordinateRows_mul_simpleColumns h]
  refine ⟨q, cartanRoots_mem_e8List hn h hp, ?_, ?_⟩
  · intro i
    rw [he]
    simp [Fin.val_inj]
  · intro i hi
    rw [he]
    apply Finset.sum_eq_zero
    intro j _
    have hj : i.val ≠ j.val := by omega
    simp [hj]

private def rootWalk {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    (Fin n → ℤ) → List (Fin n) → Prop
  | _, [] => True
  | v, i :: is => (A *ᵥ v) i = -1 ∧ rootWalk A (v + Pi.single i 1) is

private instance rootWalkDecidable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (v : Fin n → ℤ) (is : List (Fin n)) : Decidable (rootWalk A v is) := by
  induction is generalizing v with
  | nil => exact isTrue trivial
  | cons i is ih =>
    letI := ih (v + Pi.single i 1)
    unfold rootWalk
    infer_instance

private theorem rootWalk_mem {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : A.transpose = A) (v : Fin n → ℤ) (is : List (Fin n))
    (hv : CartanRoots A (corootPair A v)) (hw : rootWalk A v is) :
    CartanRoots A (corootPair A (is.foldl (fun w i => w + Pi.single i 1) v)) := by
  induction is generalizing v with
  | nil => exact hv
  | cons i is ih =>
    change (A *ᵥ v) i = -1 ∧ rootWalk A (v + Pi.single i 1) is at hw
    have hnext := hv.reflect i
    rw [reflectCorootPair A hA, reflectCoroot, hw.1, neg_one_smul, sub_neg_eq_add] at hnext
    exact ih _ hnext hw.2

private theorem cartanRoots_walk {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : A.transpose = A) (start : Fin n) (is : List (Fin n))
    (hw : rootWalk A (Pi.single start 1) is) {m : Fin n → ℤ}
    (he : ∀ j, (is.foldl (fun w i => w + Pi.single i 1) (Pi.single start 1 : Fin n → ℤ)) j = m j) :
    CartanRoots A (corootPair A m) := by
  rw [← funext he]
  apply rootWalk_mem A hA _ _ _ hw
  unfold corootPair
  rw [Matrix.mulVec_single_one]
  exact CartanRoots.simple start

private theorem e6Highest_mem :
    CartanRoots (CartanMatrix.E 6) (CartanMatrix.E 6 *ᵥ e6Highest, e6Highest) := by
  apply cartanRoots_walk (CartanMatrix.E 6) (eCartan_transpose 6) 5
    [4, 3, 2, 1, 3, 4, 0, 2, 3, 1] <;> decide +kernel

private theorem e7Highest_mem :
    CartanRoots (CartanMatrix.E 7) (CartanMatrix.E 7 *ᵥ e7Highest, e7Highest) := by
  apply cartanRoots_walk (CartanMatrix.E 7) (eCartan_transpose 7) 6
    [5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0] <;> decide +kernel

private theorem e8Highest_mem :
    CartanRoots (CartanMatrix.E 8) (CartanMatrix.E 8 *ᵥ e8Highest, e8Highest) := by
  apply cartanRoots_walk (CartanMatrix.E 8) (eCartan_transpose 8) 7
    [6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7] <;> decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem e6_coordinate_bound : ∀ q ∈ e8List,
    (coordinateRows *ᵥ q) 6 = 0 → (coordinateRows *ᵥ q) 7 = 0 →
    ∀ i : Fin 6, (coordinateRows *ᵥ q) (i.castLE (by decide)) ≤ (e6Highest i : ℚ) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem e7_coordinate_bound : ∀ q ∈ e8List,
    (coordinateRows *ᵥ q) 7 = 0 →
    ∀ i : Fin 7, (coordinateRows *ᵥ q) i.castSucc ≤ (e7Highest i : ℚ) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem e8_coordinate_bound : ∀ q ∈ e8List,
    ∀ i : Fin 8, (coordinateRows *ᵥ q) i ≤ (e8Highest i : ℚ) := by
  decide +kernel

private theorem e6HighestRootAndVertices : HighestRootAndVertices e6Highest := by
  have hpos : ∀ i, 0 < e6Highest i := by decide
  refine ⟨hpos, e6Highest_mem, ?_, ?_⟩
  · intro p hp i
    obtain ⟨q, hq, he, hz⟩ := cartanRoots_coordinates (n := 6) (by decide) (Or.inl rfl) hp
    have hb := e6_coordinate_bound q hq (hz 6 (by decide)) (hz 7 (by decide)) i
    rw [he] at hb
    exact_mod_cast hb
  · intro i x hx
    have hone := alcoveVertex_coefficient_one (hpos i) hx
    have hi : i = 0 ∨ i = 5 := by
      fin_cases i <;> first | (exfalso; contradiction) | decide
    have hd := alcoveVertex_dvd_column hone hx exceptionalCoweightColumns.1
    rcases hi with rfl | rfl
    · exact (by decide : ¬ (3 : ℤ) ∣ 4) hd
    · exact (by decide : ¬ (3 : ℤ) ∣ 2) hd

private theorem e7HighestRootAndVertices : HighestRootAndVertices e7Highest := by
  have hpos : ∀ i, 0 < e7Highest i := by decide
  refine ⟨hpos, e7Highest_mem, ?_, ?_⟩
  · intro p hp i
    obtain ⟨q, hq, he, hz⟩ := cartanRoots_coordinates (n := 7) (by decide) (Or.inr (Or.inl rfl)) hp
    have hb := e7_coordinate_bound q hq (hz 7 (by decide)) i
    have hei : (coordinateRows *ᵥ q) i.castSucc = (p.2 i : ℚ) := he i
    rw [hei] at hb
    exact_mod_cast hb
  · intro i x hx
    have hone := alcoveVertex_coefficient_one (hpos i) hx
    have hi : i = 6 := by
      fin_cases i <;> first | (exfalso; contradiction) | decide
    have hd := alcoveVertex_dvd_column hone hx exceptionalCoweightColumns.2.2
    subst i
    exact (by decide : ¬ (2 : ℤ) ∣ 3) hd

private theorem e8HighestRootAndVertices : HighestRootAndVertices e8Highest := by
  have hpos : ∀ i, 0 < e8Highest i := by decide
  refine ⟨hpos, e8Highest_mem, ?_, ?_⟩
  · intro p hp i
    obtain ⟨q, hq, he, _⟩ := cartanRoots_coordinates (n := 8) (by decide) (Or.inr (Or.inr rfl)) hp
    have hb := e8_coordinate_bound q hq i
    have hei : (coordinateRows *ᵥ q) i = (p.2 i : ℚ) := he i
    rw [hei] at hb
    exact_mod_cast hb
  · intro i x hx
    have hgt : ∀ j, e8Highest j ≠ 1 := by decide
    exact hgt _ (alcoveVertex_coefficient_one (hpos i) hx)

/-- The highest-root and fundamental-alcove calculations for the three E-types. -/
theorem exceptionalAlcove : ExceptionalAlcoveStatement :=
  ⟨e6HighestRootAndVertices, e7HighestRootAndVertices, e8HighestRootAndVertices,
    exceptionalCoweightColumns⟩


noncomputable section

section AlgebraicPoints

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Topology
open Function
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Specs.IntegralModels (MatrixRealization)
open LinearAlgebraicGroups.Arithmetic.AdelicGroups (PointsIn asMatrix)

set_option backward.isDefEq.respectTransparency false

universe u

private theorem pointMatrix_injective {k R : Type u} [Field k]
    [CommRing R] [Algebra k R] {G : AffineAlgebraicGroup k} (i : MatrixRealization G) :
    Injective (asMatrix i R) := by
  intro x y h
  let T := CommAlgCat.of k R
  let m := ((groupPointsFunctor k).map i.embedding).app T
  have hm : m x = m y := by
    change (i.matrix.hom.app T) (m x) = (i.matrix.hom.app T) (m y) at h
    exact (GrpCat.mono_iff_injective (i.matrix.hom.app T)).mp inferInstance h
  have : IsClosedImmersion i.embedding.hom.hom.left := i.closed
  apply Over.OverMorphism.ext
  apply (cancel_mono i.embedding.hom.hom.left).mp
  exact congrArg (fun z : Points i.ambient.val.X T => z.left) hm

private theorem asMatrix_mapCoefficients {k R S : Type u} [Field k]
    [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] {G : AffineAlgebraicGroup k}
    (i : MatrixRealization G) (a : R →ₐ[k] S) (g : PointsIn i R) :
    asMatrix i S (((groupPointsFunctor k).obj G.val).map (CommAlgCat.ofHom a) g) =
      Matrix.GeneralLinearGroup.map a.toRingHom (asMatrix i R g) := by
  let α := ((groupPointsFunctor k).map i.embedding) ≫ i.matrix.hom
  exact congrArg (fun f => f g) (α.naturality (CommAlgCat.ofHom a))

/-- Extension of scalars embeds the actual real points in the complex points
for the ordinary matrix topology. -/
theorem isEmbedding_realToComplex (G : AffineAlgebraicGroup ℝ) (i : MatrixRealization G) :
    IsEmbedding (realToComplex G i) := by
  have hR : IsEmbedding (asMatrix i ℝ) := ⟨IsInducing.induced _, pointMatrix_injective (R := ℝ) i⟩
  have hC : IsEmbedding (asMatrix i ℂ) := ⟨IsInducing.induced _, pointMatrix_injective (R := ℂ) i⟩
  have hf :
      IsEmbedding (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) :
        Matrix.GeneralLinearGroup (Specs.Unipotent.Index i.size) ℝ →*
          Matrix.GeneralLinearGroup (Specs.Unipotent.Index i.size) ℂ) :=
    (Complex.isUniformEmbedding_ofReal.isEmbedding.matrix_map).units_map
  apply (IsEmbedding.of_comp_iff hC).mp
  have he : (asMatrix i ℂ) ∘ realToComplex G i =
      Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) ∘ asMatrix i ℝ :=
    funext (asMatrix_mapCoefficients i (Algebra.ofId ℝ ℂ))
  rw [he]
  exact hf.comp hR

private abbrev baseReal : CommAlgCat.of ℝ ℝ ⟶ CommAlgCat.of ℝ ℂ :=
  CommAlgCat.ofHom (Algebra.ofId ℝ ℂ)

private abbrev conjComplex : CommAlgCat.of ℝ ℂ ⟶ CommAlgCat.of ℝ ℂ :=
  CommAlgCat.ofHom Complex.conjAe.toAlgHom

private theorem baseReal_comp_conjComplex : baseReal ≫ conjComplex = baseReal := by
  apply CommAlgCat.hom_ext
  ext

/-- The fixed points of ground-field conjugation are exactly the actual real
points, by taking the real part in an affine coordinate algebra. -/
theorem range_realToComplex (G : AffineAlgebraicGroup ℝ) (i : MatrixRealization G) :
    Set.range (realToComplex G i) = {x | realConjugation G i x = x} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change
      (testSpec ℝ).map conjComplex.op ≫ (testSpec ℝ).map baseReal.op ≫ y =
        (testSpec ℝ).map baseReal.op ≫ y
    rw [← Category.assoc, ← Functor.map_comp, ← op_comp, baseReal_comp_conjComplex]
  · intro hx
    change (testSpec ℝ).map conjComplex.op ≫ x = x at hx
    obtain ⟨B, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr G.prop.1
    let ff := algSpec.fullyFaithful (R := CommRingCat.of ℝ)
    let f : B.unop ⟶ CommAlgCat.of ℝ ℂ := (ff.preimage (x ≫ e.inv)).unop
    have hf : (testSpec ℝ).map f.op = x ≫ e.inv := ff.map_preimage _
    have he : f ≫ conjComplex = f := by
      apply Quiver.Hom.op_inj
      apply ff.map_injective
      change (testSpec ℝ).map (f ≫ conjComplex).op = (testSpec ℝ).map f.op
      rw [op_comp, Functor.map_comp, hf, ← Category.assoc, hx]
    have him (a : B.unop) : (f.hom a).im = 0 := by
      refine Complex.conj_eq_iff_im.mp ?_
      exact congrArg (fun g : B.unop ⟶ CommAlgCat.of ℝ ℂ => g.hom a) he
    let g : B.unop →ₐ[ℝ] ℝ :=
      { toFun := fun a => (f.hom a).re
        map_zero' := by simp
        map_one' := by simp
        map_add' := fun a b => by rw [map_add, Complex.add_re]
        map_mul' := fun a b => by rw [map_mul, Complex.mul_re, him a, zero_mul, sub_zero]
        commutes' := fun a => by simp }
    have hg : CommAlgCat.ofHom g ≫ baseReal = f := by
      apply CommAlgCat.hom_ext
      ext a
      exact Complex.ext (Complex.ofReal_re _) ((Complex.ofReal_im _).trans (him a).symm)
    refine ⟨(testSpec ℝ).map (CommAlgCat.ofHom g).op ≫ e.hom, ?_⟩
    change
      (testSpec ℝ).map baseReal.op ≫ (testSpec ℝ).map (CommAlgCat.ofHom g).op ≫ e.hom = x
    rw [← Category.assoc, ← Functor.map_comp, ← op_comp, hg, hf, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]

/-- Conjugation of coefficients is continuous in the given matrix realization. -/
theorem continuous_realConjugation (G : AffineAlgebraicGroup ℝ) (i : MatrixRealization G) :
    Continuous (realConjugation G i) := by
  apply (IsInducing.induced (asMatrix i ℂ)).continuous_iff.mpr
  have he : (asMatrix i ℂ) ∘ realConjugation G i =
      Matrix.GeneralLinearGroup.map Complex.conjAe.toAlgHom.toRingHom ∘ asMatrix i ℂ :=
    funext (asMatrix_mapCoefficients i Complex.conjAe.toAlgHom)
  rw [he]
  exact (Complex.continuous_conj.generalLinearGroup_map).comp continuous_induced_dom

end AlgebraicPoints

section Coverings

open Function Topology
open scoped unitInterval

/-- A topological quotient homomorphism with finite kernel is proper.
The saturation of a closed set is a finite union of translates. -/
theorem proper_of_finiteKernel {H Q : Type*} [Group H] [Group Q]
    [TopologicalSpace H] [TopologicalSpace Q] [ContinuousMul H]
    (p : H →* Q) (hp : IsQuotientMap p) [Finite p.ker] :
    IsProperMap p := by
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  refine ⟨hp.continuous, ?_, ?_⟩
  · intro s hs
    apply hp.isCoinducing.isClosed_preimage.mp
    have he : p ⁻¹' (p '' s) = ⋃ z : p.ker, (fun y => y * z.val) ⁻¹' s := by
      ext x
      constructor
      · rintro ⟨y, hy, hxy⟩
        have hz : x⁻¹ * y ∈ p.ker := by
          change p (x⁻¹ * y) = 1
          rw [map_mul, map_inv, hxy, inv_mul_cancel]
        refine Set.mem_iUnion.mpr ⟨⟨x⁻¹ * y, hz⟩, ?_⟩
        change x * (x⁻¹ * y) ∈ s
        rwa [mul_inv_cancel_left]
      · intro hx
        obtain ⟨⟨z, hz⟩, hy⟩ := Set.mem_iUnion.mp hx
        exact ⟨x * z, hy, by rw [map_mul, show p z = 1 from hz, mul_one]⟩
    rw [he]
    exact isClosed_iUnion_of_finite fun z => hs.preimage (continuous_id.mul continuous_const)
  · intro y
    obtain ⟨x, rfl⟩ := hp.surjective y
    have he : p ⁻¹' {p x} = (fun z : p.ker => x * z.val) '' Set.univ := by
      ext v
      constructor
      · intro hv
        have he : p v = p x := hv
        have hz : x⁻¹ * v ∈ p.ker := by
          change p (x⁻¹ * v) = 1
          rw [map_mul, map_inv, he, inv_mul_cancel]
        exact ⟨⟨x⁻¹ * v, hz⟩, Set.mem_univ _, mul_inv_cancel_left x v⟩
      · rintro ⟨⟨z, hz⟩, _, rfl⟩
        change p (x * z) = p x
        rw [map_mul, show p z = 1 from hz, mul_one]
    rw [he]
    exact (Set.finite_univ.image _).isCompact

/-- Properness carries compactness back along the full preimage of the fixed subgroup. -/
theorem compactSpace_fixed_of_proper {H Q : Type*} [Group H] [Group Q]
    [TopologicalSpace H] [TopologicalSpace Q]
    (p : H →* Q) (hp : IsProperMap p) (ω : MulAut H) (ω' : MulAut Q)
    (hw : ∀ x, p x ∈ fixedSubgroup ω' ↔ x ∈ fixedSubgroup ω)
    (hK : CompactSpace (fixedSubgroup ω')) : CompactSpace (fixedSubgroup ω) := by
  change CompactSpace (fixedSubgroup ω : Set H)
  apply isCompact_iff_compactSpace.mp
  have he : (fixedSubgroup ω : Set H) = p ⁻¹' (fixedSubgroup ω' : Set Q) :=
    Set.ext fun x => (hw x).symm
  rw [he]
  exact hp.isCompact_preimage (isCompact_iff_compactSpace.mpr hK)

/-- Lift an adjoint deformation and identify the full preimage of its compact
fixed subgroup. This preimage is connected by the endpoint map. The lifted
involution agrees with the identity on it by uniqueness for covering maps. -/
theorem exists_liftCompactRetraction {H Q : Type*} [Group H] [Group Q]
    [TopologicalSpace H] [TopologicalSpace Q] [ConnectedSpace H]
    (p : H →* Q) (hp : IsCoveringMap p) (hsurj : Surjective p)
    (ω θ : MulAut H) (ω' θ' : MulAut Q)
    (hωc : Continuous ω) (hθc : Continuous θ)
    (hω : ∀ x, p (ω x) = ω' (p x)) (hθ : ∀ x, p (θ x) = θ' (p x))
    (r' : CompactRetraction ω' θ') :
    ∃ r : CompactRetraction ω θ,
      (∀ t x, p (r.homotopy (t, x)) = r'.homotopy (t, p x)) ∧
      (∀ x, p x ∈ fixedSubgroup ω' ↔ x ∈ fixedSubgroup ω) ∧
      ConnectedSpace (fixedSubgroup ω) ∧ ConnectedSpace (fixedSubgroup ω') := by
  let F : C(unitInterval × H, Q) :=
    r'.homotopy.comp ⟨fun tx => (tx.1, p tx.2),
      continuous_fst.prodMk (hp.continuous.comp continuous_snd)⟩
  have hF (x : H) : F (0, x) = p ((ContinuousMap.id H) x) := r'.start (p x)
  let L := hp.liftHomotopy F (ContinuousMap.id H) hF
  have hstart (x : H) : L (0, x) = x := hp.liftHomotopy_zero F (ContinuousMap.id H) hF x
  have hproject (t : unitInterval) (x : H) :
      p (L (t, x)) = r'.homotopy (t, p x) :=
    congr_fun (hp.liftHomotopy_lifts F (ContinuousMap.id H) hF) (t, x)
  have hstationary (x : H) (hx : p x ∈ fixedSubgroup ω') (t : unitInterval) : L (t, x) = x := by
    have he := hp.eq_of_comp_eq (g₁ := fun s : unitInterval => L (s, x))
      (g₂ := fun _ => x) (L.continuous.comp (continuous_id.prodMk continuous_const))
      continuous_const (funext fun s => (hproject s x).trans (r'.stationary s (p x) hx))
      0 (hstart x)
    exact congr_fun he t
  let P := p ⁻¹' (fixedSubgroup ω' : Set Q)
  let endpoint : H → P := fun x => ⟨L (1, x), by
    change p (L (1, x)) ∈ fixedSubgroup ω'
    rw [hproject]
    exact r'.endpoint (p x)⟩
  have hcont_end : Continuous endpoint :=
    (L.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _
  have hsurj_end : Surjective endpoint := fun x =>
    ⟨x.val, Subtype.ext (hstationary x.val x.property 1)⟩
  let : ConnectedSpace P := hsurj_end.connectedSpace hcont_end
  have hpreimage (x : H) : p x ∈ fixedSubgroup ω' ↔ x ∈ fixedSubgroup ω := by
    constructor
    · intro hx
      have he : (fun y : P => ω y.val) = Subtype.val :=
        hp.eq_of_comp_eq (hωc.comp continuous_subtype_val) continuous_subtype_val
          (funext fun y => (hω y.val).trans y.property)
          ⟨1, by change p 1 ∈ fixedSubgroup ω'; rw [map_one]; exact Subgroup.one_mem _⟩
          (map_one ω)
      exact congr_fun he ⟨x, hx⟩
    · intro hx
      change ω x = x at hx
      exact (hω x).symm.trans (congrArg p hx)
  let r : CompactRetraction ω θ :=
    { homotopy := L
      start := hstart
      endpoint := fun x => (hpreimage _).mp (endpoint x).property
      stationary := fun t x hx => hstationary x ((hpreimage x).mpr hx) t
      equivariant := by
        intro t x
        have he := hp.eq_of_comp_eq (g₁ := fun s : unitInterval => L (s, θ (ω x)))
          (g₂ := fun s => θ (ω (L (s, x))))
          (L.continuous.comp (continuous_id.prodMk continuous_const))
          (hθc.comp (hωc.comp (L.continuous.comp (continuous_id.prodMk continuous_const))))
          (by
            funext s
            change p (L (s, θ (ω x))) = p (θ (ω (L (s, x))))
            rw [hproject, hθ, hω, r'.equivariant, hθ, hω, hproject])
          0 (by rw [hstart, hstart])
        exact congr_fun he t }
  refine ⟨r, hproject, hpreimage, ?_, ?_⟩
  · let f : H → fixedSubgroup ω := fun x => ⟨r.homotopy (1, x), r.endpoint x⟩
    have hsurj_f : Surjective f := fun x =>
      ⟨x.val, Subtype.ext (r.stationary 1 x.val x.property)⟩
    exact hsurj_f.connectedSpace
      ((r.homotopy.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _)
  · let f : P → fixedSubgroup ω' := fun x => ⟨p x.val, x.prop⟩
    have hsurj_f : Surjective f := by
      intro y
      obtain ⟨x, hx⟩ := hsurj y.val
      exact ⟨⟨x, by change p x ∈ fixedSubgroup ω'; rw [hx]; exact y.prop⟩, Subtype.ext hx⟩
    exact hsurj_f.connectedSpace ((hp.continuous.comp continuous_subtype_val).subtype_mk _)

/-- The equivariant deformation joins every real fixed point to the
connected compact fixed subgroup. -/
theorem connectedSpace_fixed_of_compactRetraction {H : Type*} [Group H] [TopologicalSpace H]
    {ω θ : MulAut H} (r : CompactRetraction ω θ)
    (hK : ConnectedSpace ({x : fixedSubgroup ω | θ x.val = x.val} : Set (fixedSubgroup ω))) :
    ConnectedSpace {x : H | θ (ω x) = x} := by
  let S : Set H := {x | θ (ω x) = x}
  let T : Set (fixedSubgroup ω) := {x | θ x.val = x.val}
  change ConnectedSpace S
  let : ConnectedSpace T := hK
  let f : T → S := fun x => ⟨x.val.val, by
    change θ (ω x.val.val) = x.val.val
    rw [show ω x.val.val = x.val.val from x.val.prop]
    exact x.prop⟩
  have hf : Continuous f := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  obtain ⟨y : T⟩ := (inferInstance : Nonempty T)
  refine connectedSpace_iff_connectedComponent.mpr ⟨f y, Set.eq_univ_of_forall fun x => ?_⟩
  let γ : unitInterval → S := fun t => ⟨r.homotopy (t, x.val), by
    change θ (ω (r.homotopy (t, x.val))) = r.homotopy (t, x.val)
    rw [← r.equivariant, show θ (ω x.val) = x.val from x.prop]⟩
  have hγ : Continuous γ := (r.homotopy.continuous.comp
    (continuous_id.prodMk continuous_const)).subtype_mk _
  have h0 : γ 0 = x := Subtype.ext (r.start _)
  have h1 (t : unitInterval) (hz : (γ t).val ∈ fixedSubgroup ω) : θ (γ t).val = (γ t).val := by
    have he := (γ t).prop
    change θ (ω (γ t).val) = (γ t).val at he
    rwa [show ω (γ t).val = (γ t).val from hz] at he
  let z : T := ⟨⟨(γ 1).val, r.endpoint x.val⟩, h1 1 (r.endpoint x.val)⟩
  have hz : γ 1 ∈ connectedComponent (f y) :=
    (isConnected_range hf).subset_connectedComponent ⟨y, rfl⟩ ⟨z, rfl⟩
  rw [connectedComponent_eq hz, ← h0]
  exact (isConnected_range hγ).subset_connectedComponent ⟨1, rfl⟩ ⟨0, rfl⟩

/-- An inner factor commuting with compact conjugation has a compact
implementer if the full preimage of the compact subgroup is compact fixed
and the quotient has faithful conjugation. -/
theorem exists_fixedImplementer_of_inner {H Q : Type*} [Group H] [Group Q]
    (p : H →* Q) (hsurj : Surjective p) (hcenter : Injective (MulAut.conj : Q → MulAut Q))
    {ω θ : MulAut H} {ω' : MulAut Q} (hcomm : Function.Commute θ ω)
    (hω : ∀ x, p (ω x) = ω' (p x))
    (hpreimage : ∀ x, p x ∈ fixedSubgroup ω' ↔ x ∈ fixedSubgroup ω)
    (hinner : ∃ t : H, θ = MulAut.conj t) :
    ∃ t : fixedSubgroup ω, θ = MulAut.conj t.val := by
  obtain ⟨t, rfl⟩ := hinner
  have hp (s x : H) : p (MulAut.conj s x) = MulAut.conj (p s) (p x) := by
    simp [MulAut.conj_apply]
  have he : p (ω t) = p t := by
    apply hcenter
    ext y
    obtain ⟨x, rfl⟩ := hsurj y
    obtain ⟨z, rfl⟩ := ω.surjective x
    rw [← hp, ← hp]
    apply congrArg p
    have hz : MulAut.conj (ω t) (ω z) = ω (MulAut.conj t z) := by
      simp [MulAut.conj_apply]
    exact hz.trans (hcomm z).symm
  refine ⟨⟨t, (hpreimage t).mp ?_⟩, rfl⟩
  change ω' (p t) = p t
  exact (hω t).symm.trans he

/-- Transport connectedness of the real fixed points along an embedding
identifying them with a fixed subgroup and a continuous conjugacy. -/
theorem connectedSpace_of_realConjugacy {R H : Type*} [TopologicalSpace R]
    [Group H] [TopologicalSpace H] {ω θ c : MulAut H} (r : CompactRetraction ω θ)
    (hK : ConnectedSpace ({x : fixedSubgroup ω | θ x.val = x.val} : Set (fixedSubgroup ω)))
    (s : H → H) (j : R → H) (hj : IsEmbedding j)
    (hrange : Set.range j = {x | s x = x})
    (hc : Continuous c) (hc' : Continuous c.symm)
    (hs : ∀ x, c (s x) = θ (ω (c x))) : ConnectedSpace R := by
  let e : H ≃ₜ H := ⟨c.toEquiv, hc, hc'⟩
  have hr : Set.range (e ∘ j) = {x | θ (ω x) = x} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      have hy : s (j y) = j y := by
        have h : j y ∈ Set.range j := ⟨y, rfl⟩
        rw [hrange] at h
        exact h
      change θ (ω (c (j y))) = c (j y)
      rw [← hs, hy]
    · intro hx
      have hv : e.symm x ∈ Set.range j := by
        rw [hrange]
        change s (e.symm x) = e.symm x
        apply e.injective
        change c (s (e.symm x)) = e (e.symm x)
        rw [hs, show c (e.symm x) = x from e.apply_symm_apply x]
        exact hx.trans (e.apply_symm_apply x).symm
      obtain ⟨y, hy⟩ := hv
      exact ⟨y, (congrArg e hy).trans (e.apply_symm_apply x)⟩
  have hconnected : ConnectedSpace (Set.range (e ∘ j)) := by
    rw [hr]
    exact connectedSpace_fixed_of_compactRetraction r hK
  exact ((e.isEmbedding.comp hj).toHomeomorph.connectedSpace_iff).mpr hconnected

end Coverings

open scoped unitInterval

section AdjointPolar

open AlgebraicGeometry CategoryTheory Topology Function
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Specs.AdjointLieAutomorphisms (coordinateBracket PreservesBracket)
open _root_.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAdjointPolarPaths
open LieAlgebrasAndRepresentations.RealForms (Conjugation)

open private coordinateBracket_basis from LinearAlgebraicGroups.Arithmetic.AdjointLieAutomorphisms

variable {L ι : Type} [LieRing L] [LieAlgebra ℂ L] [Fintype ι] [DecidableEq ι]

/-- A basis identifies invertible matrices with linear automorphisms. -/
private def matrixLinearEquiv (b : Module.Basis ι ℂ L) :
    Matrix.GeneralLinearGroup ι ℂ ≃* (L ≃ₗ[ℂ] L) :=
  (Units.mapEquiv (Matrix.toLinAlgEquiv b).toMulEquiv).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv ℂ L)

private theorem matrixLinearEquiv_apply (b : Module.Basis ι ℂ L)
    (m : Matrix.GeneralLinearGroup ι ℂ) (x : L) :
    matrixLinearEquiv b m x = b.equivFun.symm (m.val *ᵥ b.equivFun x) := by
  change Matrix.toLin b b m.val x = _
  rw [Matrix.toLin_apply, b.equivFun_symm_apply]
  rfl

private theorem matrix_mem_bracketAutomorphisms (b : Module.Basis ι ℂ L)
    (m : Matrix.GeneralLinearGroup ι ℂ) :
    PreservesBracket (fun r t u => b.repr ⁅b r, b t⁆ u) (RingHom.id ℂ) m ↔
      matrixLinearEquiv b m ∈ bracketAutomorphisms L := by
  let e := matrixLinearEquiv b m
  have he (x : L) : m.val *ᵥ b.equivFun x = b.equivFun (e x) := by
    rw [show e x = _ from matrixLinearEquiv_apply b m x, LinearEquiv.apply_symm_apply]
  constructor
  · intro h x y
    apply b.equivFun.injective
    have hp := h (b.equivFun x) (b.equivFun y)
    rw [he, he, coordinateBracket_basis, coordinateBracket_basis, he] at hp
    exact hp.symm
  · intro h x y
    obtain ⟨x, rfl⟩ := b.equivFun.surjective x
    obtain ⟨y, rfl⟩ := b.equivFun.surjective y
    rw [he, he, coordinateBracket_basis, coordinateBracket_basis, he]
    exact congrArg b.equivFun (h x y).symm

private def bracketMatrixEquiv (b : Module.Basis ι ℂ L)
    (B : Subgroup (Matrix.GeneralLinearGroup ι ℂ))
    (hB : ∀ m, m ∈ B ↔
      PreservesBracket (fun r t u => b.repr ⁅b r, b t⁆ u) (RingHom.id ℂ) m) :
    B ≃* LieAut L where
  toFun m := ⟨matrixLinearEquiv b m.val,
    (matrix_mem_bracketAutomorphisms b _).mp ((hB _).mp m.prop)⟩
  invFun g := ⟨(matrixLinearEquiv b).symm g.val, (hB _).mpr
    ((matrix_mem_bracketAutomorphisms b _).mpr (by
      rw [MulEquiv.apply_symm_apply]
      exact g.prop))⟩
  left_inv m := Subtype.ext ((matrixLinearEquiv b).symm_apply_apply m.val)
  right_inv g := Subtype.ext ((matrixLinearEquiv b).apply_symm_apply g.val)
  map_mul' m n := Subtype.ext (map_mul (matrixLinearEquiv b) m.val n.val)

private theorem bracketMatrixEquiv_apply (b : Module.Basis ι ℂ L)
    (B : Subgroup (Matrix.GeneralLinearGroup ι ℂ)) (hB) (m : B) (x : L) :
    (bracketMatrixEquiv b B hB m).val x = b.equivFun.symm (m.val.val *ᵥ b.equivFun x) :=
  matrixLinearEquiv_apply b m.val x

private theorem bracketMatrixEquiv_isEmbedding (b : Module.Basis ι ℂ L)
    (B : Subgroup (Matrix.GeneralLinearGroup ι ℂ)) (hB) :
    letI := matrixTopology b
    letI : TopologicalSpace B := TopologicalSpace.induced
      (fun m : B => (m.val.val : Matrix ι ι ℂ)) inferInstance
    IsEmbedding (bracketMatrixEquiv b B hB) := by
  let := matrixTopology b
  let : TopologicalSpace B := TopologicalSpace.induced
    (fun m : B => (m.val.val : Matrix ι ι ℂ)) inferInstance
  have hM : IsEmbedding (matrixOf b) :=
    ⟨IsInducing.induced _, fun _ _ h => Subtype.ext (LinearEquiv.toLinearMap_injective
      ((LinearMap.toMatrix b b).injective h))⟩
  apply (IsEmbedding.of_comp_iff hM).mp
  have he (m : B) : matrixOf b (bracketMatrixEquiv b B hB m) = m.val.val :=
    (LinearMap.toMatrix b b).apply_symm_apply m.val.val
  rw [show matrixOf b ∘ bracketMatrixEquiv b B hB = fun m : B => m.val.val from funext he]
  exact ⟨IsInducing.induced _, fun _ _ h => Subtype.ext (Units.ext h)⟩

/-- Transport the analytic polar deformation through the closed adjoint
embedding, retaining equivariance under each action. -/
private theorem adjointCompactRetraction {Q : Type} [Group Q] [TopologicalSpace Q]
    [FiniteDimensional ℂ L] (b : Module.Basis ι ℂ L)
    (hs : _root_.Specs.LieAlgebrasAndRepresentations.SolvableRadical.IsSemisimple_value ℂ L)
    (ωL : Conjugation L)
    (hc : _root_.Specs.LieAlgebrasAndRepresentations.PolarRealStructures.IsCompact ωL)
    (θL : L ≃ₗ⁅ℂ⁆ L) (hθL : Involutive θL)
    (hcomm : Function.Commute (fun x : L => θL x) (fun x : L => ωL.map x))
    (ωQ θQ : MulAut Q) :
    letI := matrixTopology b
    ∀ (f : Q →* LieAut L), IsClosedEmbedding f →
      connectedComponent (1 : LieAut L) ⊆ Set.range f →
      (∀ x, f (ωQ x) = compactAction ωL (f x)) →
      (∀ x, f (θQ x) = holomorphicAction (ofLieEquiv θL) (f x)) →
      ∃ r : CompactRetraction ωQ θQ, CompactSpace (fixedSubgroup ωQ) ∧
        ∀ t x, r.homotopy (t, θQ x) = θQ (r.homotopy (t, x)) := by
  let := matrixTopology b
  intro f hf hComp hω hθ
  let A := f.range
  let E : Q ≃ₜ A := hf.isEmbedding.toHomeomorph
  have hωA (g : LieAut L) (hg : g ∈ A) : compactAction ωL g ∈ A := by
    obtain ⟨x, rfl⟩ := hg
    exact ⟨ωQ x, hω x⟩
  have hθA (g : LieAut L) (hg : g ∈ A) : holomorphicAction (ofLieEquiv θL) g ∈ A := by
    obtain ⟨x, rfl⟩ := hg
    exact ⟨θQ x, hθ x⟩
  obtain ⟨H, _, _, _, _, hstart, hend, hstat, heqω, heqθ, _, _, hcompact⟩ :=
    ExceptionalAdjointPolarPaths.polarDeformation b hs ωL hc (ofLieEquiv θL)
      hθL (fun x => hcomm x) A hf.isClosed_range hComp hωA hθA
  have hfix (x : Q) : E x ∈ compactFixed ωL A ↔ x ∈ fixedSubgroup ωQ := by
    change compactAction ωL (f x) = f x ↔ ωQ x = x
    rw [← hω x, hf.injective.eq_iff]
  let F : C(unitInterval × Q, Q) :=
    ⟨fun tx => E.symm (H (tx.1, E tx.2)),
      E.symm.continuous.comp (H.continuous.comp
        (continuous_fst.prodMk (E.continuous.comp continuous_snd)))⟩
  have hF (t : unitInterval) (x : Q) : f (F (t, x)) = (H (t, E x)).val :=
    congrArg Subtype.val (E.apply_symm_apply (H (t, E x)))
  have hFω (t : unitInterval) (x : Q) : F (t, ωQ x) = ωQ (F (t, x)) := by
    apply hf.injective
    rw [hF, hω, hF]
    exact heqω t (E x) (E (ωQ x)) (hω x)
  have hFθ (t : unitInterval) (x : Q) : F (t, θQ x) = θQ (F (t, x)) := by
    apply hf.injective
    rw [hF, hθ, hF]
    exact heqθ t (E x) (E (θQ x)) (hθ x)
  let r : CompactRetraction ωQ θQ := {
    homotopy := F
    start := fun x => by
      change E.symm (H (0, E x)) = x
      rw [hstart, E.symm_apply_apply]
    endpoint := fun x => (hfix _).mp (by
      change E (E.symm (H (1, E x))) ∈ compactFixed ωL A
      rw [E.apply_symm_apply]
      exact hend (E x))
    stationary := fun t x hx => by
      change E.symm (H (t, E x)) = x
      rw [hstat t (E x) ((hfix x).mpr hx), E.symm_apply_apply]
    equivariant := fun t x => (hFθ t (ωQ x)).trans (congrArg θQ (hFω t x)) }
  refine ⟨r, isCompact_iff_compactSpace.mp ?_, hFθ⟩
  have hpre : (fixedSubgroup ωQ : Set Q) = E ⁻¹' (compactFixed ωL A : Set A) :=
    Set.ext fun x => (hfix x).symm
  rw [hpre]
  exact E.isCompact_preimage.mpr hcompact


/-- The point action on the closed adjoint matrix group is the Lie action
in its specified basis. Its polar paths transport to the point group. -/
private theorem matrixAdjointCompactRetraction {Q : Type} [Group Q] [TopologicalSpace Q]
    [FiniteDimensional ℂ L] (b : Module.Basis ι ℂ L)
    (hs : _root_.Specs.LieAlgebrasAndRepresentations.SolvableRadical.IsSemisimple_value ℂ L)
    (ωL : Conjugation L)
    (hc : _root_.Specs.LieAlgebrasAndRepresentations.PolarRealStructures.IsCompact ωL)
    (θL : L ≃ₗ⁅ℂ⁆ L) (hθL : Involutive θL)
    (hcomm : Function.Commute (fun x : L => θL x) (fun x : L => ωL.map x))
    (B : Subgroup (Matrix.GeneralLinearGroup ι ℂ))
    (hB : ∀ m, m ∈ B ↔
      PreservesBracket (fun r t u => b.repr ⁅b r, b t⁆ u) (RingHom.id ℂ) m)
    (ωQ θQ : MulAut Q) (ρ : Q →* B) :
    letI : TopologicalSpace B := TopologicalSpace.induced
      (fun m : B => (m.val.val : Matrix ι ι ℂ)) inferInstance
    IsClosedEmbedding ρ →
      connectedComponent (1 : B) ⊆ Set.range ρ →
      (∀ y v, b.equivFun.symm ((ρ (ωQ y)).val.val *ᵥ b.equivFun v) =
        ωL.map (b.equivFun.symm ((ρ y).val.val *ᵥ b.equivFun (ωL.map v)))) →
      (∀ y v, b.equivFun.symm ((ρ (θQ y)).val.val *ᵥ b.equivFun v) =
        θL (b.equivFun.symm ((ρ y).val.val *ᵥ b.equivFun (θL.symm v)))) →
      ∃ r : CompactRetraction ωQ θQ, CompactSpace (fixedSubgroup ωQ) ∧
        ∀ t x, r.homotopy (t, θQ x) = θQ (r.homotopy (t, x)) := by
  let : TopologicalSpace B := TopologicalSpace.induced
    (fun m : B => (m.val.val : Matrix ι ι ℂ)) inferInstance
  let := matrixTopology b
  intro hρ hComp hω hθ
  let e := bracketMatrixEquiv b B hB
  let E : B ≃ₜ LieAut L :=
    (bracketMatrixEquiv_isEmbedding b B hB).toHomeomorphOfSurjective e.surjective
  let f := e.toMonoidHom.comp ρ
  have hf : IsClosedEmbedding f := E.isClosedEmbedding.comp hρ
  have hfComp : connectedComponent (1 : LieAut L) ⊆ Set.range f := by
    intro x hx
    have h1 : E.symm (1 : LieAut L) = 1 := by
      apply E.injective
      rw [E.apply_symm_apply]
      exact (map_one e).symm
    have hy := E.symm.continuous.mapsTo_connectedComponent (1 : LieAut L) hx
    rw [h1] at hy
    obtain ⟨y, hy⟩ := hComp hy
    refine ⟨y, ?_⟩
    change E (ρ y) = x
    rw [hy, E.apply_symm_apply]
  refine adjointCompactRetraction b hs ωL hc θL hθL hcomm ωQ θQ f hf hfComp ?_ ?_
  · intro y
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change (e (ρ (ωQ y))).val v = ωL.map ((e (ρ y)).val (ωL.map v))
    simpa only [e, bracketMatrixEquiv_apply] using hω y v
  · intro y
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change (e (ρ (θQ y))).val v = θL ((e (ρ y)).val (θL.symm v))
    simpa only [e, bracketMatrixEquiv_apply] using hθ y v

end AdjointPolar

open scoped CategoryTheory.MonObj CategoryTheory.GrpObj
section Centralizers

open AlgebraicGeometry CategoryTheory Topology Function
open LinearAlgebraicGroups.Specs
open Specs.ExceptionalCompactInner (HasExceptionalType fixedSubgroup CompactRetraction)
open Specs.ExceptionalTorsionCentralizers (ComplexPoints ExceptionalAlcoveInputs
  RootGenerators torusPoint)
open Specs.IntegralModels (MatrixRealization)
open Specs.AbsoluteDynkinTypes (IsAbsolutelyAlmostSimple)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open Specs.GeometricRadicals (IsSplitTorus)
open Specs.RankOneFlag (IsSplitAdditive)
open LinearAlgebraicGroups.Arithmetic.AdelicGroups (PointsIn)

private def transportComplexPoints {H J : AffineAlgebraicGroup ℂ} (h : H = J) :
    ComplexPoints H.val ≃* ComplexPoints J.val :=
  h ▸ MulEquiv.refl _

private theorem transportComplexPoints_apply {H J : AffineAlgebraicGroup ℂ} (h : H = J)
    (x : ComplexPoints H.val) :
    transportComplexPoints h x = (h ▸ x : ComplexPoints J.val) := by
  subst J
  rfl

private theorem transportComplexPoints_comp {H J : AffineAlgebraicGroup ℂ} (h : H = J)
    {S : GroupScheme ℂ} (f : S ⟶ H.val) (z : ComplexPoints S) :
    transportComplexPoints h (z ≫ f.hom.hom) =
      z ≫ (f ≫ eqToHom (congrArg (fun A : AffineAlgebraicGroup ℂ => A.val) h)).hom.hom := by
  subst J
  simp [transportComplexPoints]

/-- A path connected set containing the identity lies in the identity path
component of any subgroup containing the set. -/
private theorem subset_map_pathComponentOne {X : Type*}
    [Group X] [TopologicalSpace X] [IsTopologicalGroup X] {C : Subgroup X} {S : Set X}
    (hS : IsPathConnected S) (hone : 1 ∈ S) (hSC : S ⊆ (C : Set X)) :
    S ⊆ ((Subgroup.pathComponentOne C).map C.subtype : Set X) := by
  intro x hx
  refine ⟨⟨x, hSC hx⟩, ?_, rfl⟩
  exact ((hS.joinedIn 1 hone x hx).mono hSC).joined_subtype

/-- The complex point centralizer is path connected in the given closed
matrix realization, by the path connected images of the torus and root groups. -/
private theorem torsionCentralizer_pathConnected (inputs : ExceptionalAlcoveInputs)
    (G : AffineAlgebraicGroup ℝ) (i : MatrixRealization G)
    (hG : IsAbsolutelyAlmostSimple G) (hsc : GeometricallySimplyConnected G)
    (htype : HasExceptionalType G) (t : PointsIn i ℂ) (ht : IsOfFinOrder t) :
    PathConnectedSpace (Subgroup.centralizer ({t} : Set (PointsIn i ℂ))) := by
  let H := baseChangedAlgebraicGroup ℂ G
  let R := CommAlgCat.of ℂ ℂ
  let eC : ComplexPoints H.val ≃* PointsIn i ℂ := baseChangePointGroupEquiv ℂ G.val R
  obtain ⟨P, hP, s, _, U, hs, _, hgen⟩ :=
    ExceptionalTorsionCentralizers.torsionCentralizer inputs G hG hsc htype
      (eC.symm t) (eC.symm.toMonoidHom.isOfFinOrder ht)
  let e : ComplexPoints P.G.val ≃* PointsIn i ℂ :=
    (transportComplexPoints hP).trans eC
  have hta : e (torusPoint s) = t := by
    change eC (transportComplexPoints hP (torusPoint s)) = t
    rw [transportComplexPoints_apply, hs, MulEquiv.apply_symm_apply]
  let C := Subgroup.centralizer ({t} : Set (PointsIn i ℂ))
  let C₀ := (Subgroup.pathComponentOne C).map C.subtype
  let D := Subgroup.centralizer ({torusPoint s} : Set (ComplexPoints P.G.val))
  have he (x : ComplexPoints P.G.val) : e x ∈ C ↔ x ∈ D := by
    change e x ∈ Subgroup.centralizer {t} ↔ x ∈ Subgroup.centralizer {torusPoint s}
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
      ← hta, ← map_mul, ← map_mul, e.injective.eq_iff]
  have hline {S : GroupScheme ℂ} (f : S ⟶ P.G.val)
      (hf : IsSplitTorus S ∨ IsSplitAdditive S)
      (hfD : ∀ z : ComplexPoints S, z ≫ f.hom.hom ∈ D) :
      Set.range (fun z : ComplexPoints S => e (z ≫ f.hom.hom)) ⊆ (C₀ : Set (PointsIn i ℂ)) := by
    let f' : S ⟶ H.val := f ≫ eqToHom (congrArg (fun A : AffineAlgebraicGroup ℂ => A.val) hP)
    let fₚ : ComplexPoints S →* ComplexPoints P.G.val :=
      (((groupPointsFunctor ℂ).map f).app R).hom
    have hcmp (z : ComplexPoints S) :
        e (z ≫ f.hom.hom) =
          (show PointsIn i ℂ from baseChangePoint ℝ ℂ G.val.X R (z ≫ f'.hom.hom)) := by
      change eC (transportComplexPoints hP (z ≫ f.hom.hom)) = eC (z ≫ f'.hom.hom)
      rw [transportComplexPoints_comp]
    have hpath : IsPathConnected (Set.range (fun z : ComplexPoints S => e (z ≫ f.hom.hom))) := by
      simpa only [hcmp] using ExceptionalComplexPointGeometry.pathConnectedComplexifiedLineImages i f' hf
    apply subset_map_pathComponentOne hpath
    · exact ⟨1, (e.toMonoidHom.comp fₚ).map_one⟩
    · rintro x ⟨z, rfl⟩
      exact (he _).mpr (hfD z)
  have hle : D ≤ C₀.comap e.toMonoidHom := by
    change Subgroup.centralizer _ ≤ _
    rw [hgen]
    apply (Subgroup.closure_le _).mpr
    intro x hx
    change e x ∈ C₀
    have htorus (z : ComplexPoints P.T.group) : z ≫ P.T.inclusion.hom.hom ∈ D := by
      change torusPoint z ∈ Subgroup.centralizer _
      rw [hgen]
      exact Subgroup.subset_closure (Or.inl ⟨z, rfl⟩)
    rcases hx with ⟨z, rfl⟩ | ⟨α, hα, ⟨z, rfl⟩⟩
    · exact hline P.T.inclusion (Or.inl P.split) htorus ⟨z, rfl⟩
    · have hroot (v : ComplexPoints (U α).val.group) : v ≫ (U α).val.inclusion.hom.hom ∈ D := by
        change _ ∈ Subgroup.centralizer _
        rw [hgen]
        exact Subgroup.subset_closure (Or.inr ⟨α, hα, v, rfl⟩)
      exact hline (U α).val.inclusion (Or.inr (U α).prop.2.1) hroot ⟨z, rfl⟩
  apply pathConnectedSpace_iff_eq.mpr
  refine ⟨(1 : C), Set.eq_univ_of_forall fun x => ?_⟩
  have hxD : e.symm x.val ∈ D :=
    (he _).mp (by rw [e.apply_symm_apply]; exact x.prop)
  have hxC₀ : x.val ∈ C₀ := by
    have hx := hle hxD
    change e (e.symm x.val) ∈ C₀ at hx
    rwa [e.apply_symm_apply] at hx
  obtain ⟨y, hy, hyx⟩ := hxC₀
  have hyx' : y = x := Subtype.ext hyx
  exact hyx' ▸ hy

/-- A lift of an equivariant deformation is equivariant for the lifted
action, by uniqueness of paths with a specified starting point. -/
private theorem liftedRetraction_equivariant {X Y : Type*} [Group X] [Group Y]
    [TopologicalSpace X] [TopologicalSpace Y]
    {p : X →* Y} (hp : IsCoveringMap p)
    {ω θ : MulAut X} {ω' θ' : MulAut Y}
    (r : CompactRetraction ω θ) (r' : CompactRetraction ω' θ')
    (hproject : ∀ t x, p (r.homotopy (t, x)) = r'.homotopy (t, p x))
    (hθ : Continuous θ) (hθp : ∀ x, p (θ x) = θ' (p x))
    (hθr : ∀ t y, r'.homotopy (t, θ' y) = θ' (r'.homotopy (t, y))) :
    ∀ t x, r.homotopy (t, θ x) = θ (r.homotopy (t, x)) := by
  intro t x
  have he := hp.eq_of_comp_eq (g₁ := fun s : unitInterval => r.homotopy (s, θ x))
    (g₂ := fun s : unitInterval => θ (r.homotopy (s, x)))
    (r.homotopy.continuous.comp (continuous_id.prodMk continuous_const))
    (hθ.comp (r.homotopy.continuous.comp (continuous_id.prodMk continuous_const)))
    (by
      funext s
      change p (r.homotopy (s, θ x)) = p (θ (r.homotopy (s, x)))
      rw [hproject, hθp, hθr, hθp, hproject])
    0 (by rw [r.start, r.start])
  exact congr_fun he t

private theorem finiteOrder_of_involutive_conjugation {X Y : Type*} [Group X] [Group Y]
    (p : X →* Y) (hp : Surjective p) [Finite p.ker]
    (hf : Injective (MulAut.conj : Y → MulAut Y)) (t : X)
    (ht : Function.Involutive (MulAut.conj t)) : IsOfFinOrder t := by
  have hsq : MulAut.conj (t ^ 2) = 1 := by
    rw [map_pow, pow_two]
    ext x
    exact ht x
  have hk : t ^ 2 ∈ p.ker := by
    change p (t ^ 2) = 1
    apply hf
    ext y
    obtain ⟨x, rfl⟩ := hp y
    have he := congrArg (fun a : MulAut X => p (a x)) hsq
    simpa only [MulAut.conj_apply, map_mul, map_inv, MulAut.one_apply, one_mul, inv_one, mul_one]
      using he
  have hfin : IsOfFinOrder (t ^ 2) :=
    p.ker.subtype.isOfFinOrder (isOfFinOrder_of_finite (⟨t ^ 2, hk⟩ : p.ker))
  exact (isOfFinOrder_pow.mp hfin).resolve_right (by decide)

/-- The equivariant endpoint map restricts to a surjection from the
θ-fixed complex group to the θ-fixed points of the compact group. -/
private theorem connectedSpace_compactFixed {X : Type*} [Group X] [TopologicalSpace X]
    {ω θ : MulAut X} (r : CompactRetraction ω θ)
    (hθr : ∀ t x, r.homotopy (t, θ x) = θ (r.homotopy (t, x)))
    (hθ : ConnectedSpace (fixedSubgroup θ)) :
    ConnectedSpace ({x : fixedSubgroup ω | θ x.val = x.val} : Set (fixedSubgroup ω)) := by
  let := hθ
  let e : fixedSubgroup θ → {x : fixedSubgroup ω | θ x.val = x.val} :=
    fun x => ⟨⟨r.homotopy (1, x.val), r.endpoint x.val⟩, by
      change θ (r.homotopy (1, x.val)) = r.homotopy (1, x.val)
      rw [← hθr, show θ x.val = x.val from x.prop]⟩
  have he : Continuous e :=
    ((r.homotopy.continuous.comp
      (continuous_const.prodMk continuous_subtype_val)).subtype_mk _).subtype_mk _
  have hsurj : Surjective e := by
    intro x
    refine ⟨⟨x.val.val, x.prop⟩, Subtype.ext (Subtype.ext ?_)⟩
    exact r.stationary 1 x.val.val x.val.prop
  exact hsurj.connectedSpace he

end Centralizers
section Assembly

open AlgebraicGeometry CategoryTheory Function Topology
open LinearAlgebraicGroups.Specs
open Specs.ExceptionalCompactInner
open Specs.IntegralModels (MatrixRealization)
open Specs.AbsoluteDynkinTypes (IsAbsolutelyAlmostSimple)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open Specs.StandardGroups (generalLinearPoints)
open LinearAlgebraicGroups.Arithmetic.AdelicGroups (PointsIn asMatrix)

open private realConjugation_involutive from
  LinearAlgebraicGroups.Arithmetic.ExceptionalLieAutomorphismTransport
open private glVal_isEmbedding from LinearAlgebraicGroups.Arithmetic.AdelicGroups

private def generalLinearPointsReindex {idx idx' : Type} [Fintype idx] [DecidableEq idx]
    [Fintype idx'] [DecidableEq idx'] (e : idx ≃ idx') :
    generalLinearPoints ℝ idx ≅ generalLinearPoints ℝ idx' :=
  NatIso.ofComponents
    (fun R => (Units.mapEquiv (Matrix.reindexRingEquiv R e).toMulEquiv).toGrpIso) (by
      intro R S f
      apply GrpCat.hom_ext
      apply MonoidHom.ext
      intro x
      apply Units.ext
      rfl)

/-- The topology from invertible matrices is the topology of their entries. -/
private theorem pointTopology_eq_induced_entries {G : AffineAlgebraicGroup ℝ}
    (i : MatrixRealization G) :
    (inferInstance : TopologicalSpace (PointsIn i ℂ)) =
      TopologicalSpace.induced (fun x : PointsIn i ℂ => (asMatrix i ℂ x).val) inferInstance :=
  (glVal_isEmbedding.isInducing.comp (IsInducing.induced (asMatrix i ℂ))).eq_induced

private theorem continuous_of_algebraicAction {G : AffineAlgebraicGroup ℝ}
    {i : MatrixRealization G} {a : Aut ((groupBaseChange ℝ ℂ).obj G.val)}
    {f : PointsIn i ℂ → PointsIn i ℂ} (ha : ActsOnComplexPoints a f) : Continuous f := by
  obtain ⟨p, hp, hp'⟩ :=
    ExceptionalComplexPointGeometry.continuousComplexifiedPointMap i i a.asIso.hom
  let R := CommAlgCat.of ℂ ℂ
  let e := baseChangePointGroupEquiv ℂ G.val R
  have he : (p : PointsIn i ℂ → PointsIn i ℂ) = f := by
    funext x
    obtain ⟨z, rfl⟩ := e.surjective x
    exact (Over.OverMorphism.ext (hp' z)).trans (ha z).symm
  rwa [← he]

private theorem algebraicAction_inverse {G : AffineAlgebraicGroup ℝ}
    {i : MatrixRealization G} {a : Aut ((groupBaseChange ℝ ℂ).obj G.val)}
    {f : MulAut (PointsIn i ℂ)} (ha : ActsOnComplexPoints a f) :
    ActsOnComplexPoints a⁻¹ f.symm := by
  intro z
  let R := CommAlgCat.of ℂ ℂ
  let e : Points ((groupBaseChange ℝ ℂ).obj G.val).X R ≃* PointsIn i ℂ :=
    baseChangePointGroupEquiv ℂ G.val R
  let w : Points ((groupBaseChange ℝ ℂ).obj G.val).X R := z
  let z' := w ≫ a.asIso.inv.hom.hom
  change f.symm (e w) = e z'
  have hinv : a.asIso.inv.hom.hom ≫ a.asIso.hom.hom.hom = 𝟙 _ :=
    congrArg (fun g : (groupBaseChange ℝ ℂ).obj G.val ⟶ _ => g.hom.hom) a.asIso.inv_hom_id
  have he : z' ≫ a.asIso.hom.hom.hom = w :=
    (Category.assoc w _ _).trans ((congrArg (fun g => w ≫ g) hinv).trans (Category.comp_id w))
  apply f.injective
  exact (f.apply_symm_apply (e w)).trans ((congrArg e he.symm).trans (ha z').symm)

set_option maxHeartbeats 800000 in
/-- The real structure, compact deformation, and inner-case connectedness
for the given simply connected real exceptional group. -/
theorem compactInner : CompactInnerStatement := by
  intro G i hG hsc htype
  obtain ⟨s, hs⟩ := ExceptionalLieAutomorphismTransport.exceptionalLieAutomorphismTransport
    G i.size i.ambient i.embedding (i.matrix ≪≫ generalLinearPointsReindex Equiv.ulift)
    i.closed hG hsc htype
  let := s.lieRing
  let := s.lieAlgebra
  obtain ⟨σL, ωL, θL, _, ω₀, θ₀, c₀, aω, aθ, ac, hσL, hωL, hθL, hcommL, _,
    haω, haθ, hac, hdω, _, _, hω, hθ, hcomm, hconj, hAdj⟩ := hs
  obtain ⟨Z, Q, q, d, N, ιQ, l, b, B, hAdj, hcentral, _, hclosed, _, _, hB, hρ,
    hEmbed, hComp, hfaithful, ωQ, θQ, hωp, hθp, hωQ, hθQ⟩ := hAdj
  let j : MatrixRealization Q := ⟨d, N, l, ιQ, hclosed⟩
  let p : PointsIn i ℂ →* PointsIn j ℂ :=
    ExceptionalComplexPointGeometry.pointMap i j q
  obtain ⟨_, hp, hfin, hcover⟩ := ExceptionalComplexPointGeometry.centralIsogenyCovering i j q hcentral
  let : Finite p.ker := hfin
  have hproper : IsProperMap p := proper_of_finiteKernel p (hcover.isQuotientMap hp)
  have hred := (ComplexExceptionalDatum.complexExceptionalDatum G hG hsc htype).1
  let : PathConnectedSpace (PointsIn i ℂ) :=
    ExceptionalComplexPointGeometry.realGroupComplexPointsPathConnected G i hred
  have hsemisimple := (Reductive.RadicalBaseChange.semisimpleFieldExtension G hG.1.1 hG.1.2.1
    (K := ℂ)).mpr hG.1
  obtain ⟨hfiniteDim, hLie⟩ :=
    Representation.SemisimplyDifferentiated.lieSemisimple (baseChangedAlgebraicGroup ℂ G) hsemisimple s
  let : FiniteDimensional ℂ (Lie ℂ (Specs.ExceptionalLieAutomorphismTransport.complexGroup G)) :=
    hfiniteDim
  let : TopologicalSpace B := TopologicalSpace.induced
    (fun m : B => (m.val.val : Matrix (ULift.{0} (Fin d)) (ULift.{0} (Fin d)) ℂ)) inferInstance
  let ρ : PointsIn j ℂ →* B := (asMatrix j ℂ).codRestrict B hρ
  have hEmb : IsClosedEmbedding ρ := by
    let P (τ : TopologicalSpace (PointsIn j ℂ)) :=
      @IsClosedEmbedding (PointsIn j ℂ) B τ inferInstance (⇑ρ)
    exact Eq.mpr (congrArg P (pointTopology_eq_induced_entries j)) hEmbed
  obtain ⟨rQ, hKQ, hθrQ⟩ :=
    matrixAdjointCompactRetraction (Q := PointsIn j ℂ) b hLie ωL hωL θL hθL hcommL B hB ωQ θQ ρ
      hEmb hComp hωQ hθQ
  let ω : MulAut (PointsIn i ℂ) := ω₀
  let θ : MulAut (PointsIn i ℂ) := θ₀
  let c : MulAut (PointsIn i ℂ) := c₀
  have hθc : Continuous θ :=
    continuous_of_algebraicAction (i := i) haθ
  have hcc : Continuous c :=
    continuous_of_algebraicAction (i := i) hac
  have hccInv : Continuous c.symm :=
    continuous_of_algebraicAction (i := i) (algebraicAction_inverse (i := i) hac)
  have hωc : Continuous ω := by
    have hωσ : Continuous (fun x : PointsIn i ℂ => ω (realConjugation G i x)) :=
      continuous_of_algebraicAction (i := i) haω
    have he : (fun x : PointsIn i ℂ => ω (realConjugation G i x)) ∘ realConjugation G i = ω :=
      funext fun x => congrArg ω (realConjugation_involutive G x)
    rw [← he]
    exact hωσ.comp (continuous_realConjugation G i)
  obtain ⟨r, hproj, hpre, hK, hconnKQ⟩ :=
    exists_liftCompactRetraction p hcover hp ω θ ωQ θQ hωc hθc hωp hθp rQ
  have hθr := liftedRetraction_equivariant hcover r rQ hproj hθc hθp hθrQ
  have hcompactK := compactSpace_fixed_of_proper p hproper ω ωQ hpre hKQ
  have hd : HasCompactDifferential aω := by
    refine ⟨s, ωL, hωL, fun x => ⟨σL.map x, hσL x, hdω x⟩⟩
  have hrealEmb := isEmbedding_realToComplex G i
  have hrealRange := range_realToComplex G i
  refine ⟨ω, θ, c, hωc, hθc, hcc, hccInv, ⟨aω, haω, hd⟩, ⟨aθ, haθ⟩, ⟨ac, hac⟩,
    hω, hθ, hcomm, hconj, hrealEmb, hrealRange, hcompactK, hK,
    ⟨r, Q, j, Z, q, hAdj, hcentral, hcover, hp, ωQ, θQ, rQ, hωp, hθp, hpre, hconnKQ, hproj⟩,
    ?_⟩
  intro hinner
  obtain ⟨t, hinner⟩ := exists_fixedImplementer_of_inner p hp hfaithful
    (ω := ω) (θ := θ) hcomm hωp hpre hinner
  have ht : IsOfFinOrder t.val :=
    finiteOrder_of_involutive_conjugation p hp hfaithful t.val (hinner ▸ hθ)
  let := torsionCentralizer_pathConnected
    ⟨exceptionalAlcove.1, exceptionalAlcove.2.1, exceptionalAlcove.2.2.1⟩ G i hG hsc htype t.val ht
  have hC : (fixedSubgroup θ : Subgroup (PointsIn i ℂ)) = Subgroup.centralizer {t.val} := by
    ext x
    change θ x = x ↔ x ∈ Subgroup.centralizer {t.val}
    rw [hinner, Subgroup.mem_centralizer_singleton_iff]
    change t.val * x * t.val⁻¹ = x ↔ x * t.val = t.val * x
    rw [mul_inv_eq_iff_eq_mul]
    exact eq_comm
  have hfix : ConnectedSpace (fixedSubgroup θ) := by
    rw [hC]
    infer_instance
  have hconn := connectedSpace_compactFixed r hθr hfix
  exact ⟨⟨t, hinner⟩, hconn, connectedSpace_of_realConjugacy r hconn
    (realConjugation G i) (realToComplex G i) hrealEmb hrealRange hcc hccInv hconj⟩

end Assembly

end

end LinearAlgebraicGroups.Arithmetic.ExceptionalCompactInner
