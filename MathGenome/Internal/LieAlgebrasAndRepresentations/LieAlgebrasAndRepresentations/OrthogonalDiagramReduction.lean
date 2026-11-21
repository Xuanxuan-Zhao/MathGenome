import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.OrthogonalDiagramReduction
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PolarRealStructures
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClassicalCoordinateRoots
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClassicalRootsB
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClassicalRootsD
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.AutomorphismDecomposition
import Batteries.Tactic.OpenPrivate
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.LinearAlgebra.Determinant

noncomputable section

namespace LieAlgebrasAndRepresentations.OrthogonalDiagramReduction

open Specs.LieAlgebrasAndRepresentations.OrthogonalDiagramReduction
open Specs.LieAlgebrasAndRepresentations.AutomorphismDecomposition (Aut)
local notation "innerAut" => Specs.LieAlgebrasAndRepresentations.AutomorphismDecomposition.inner
open Specs.LieAlgebrasAndRepresentations.PolarRealStructures
open LieAlgebrasAndRepresentations.RealForms
open Complex
open scoped Classical

open private sandwich real_eigenbasis adjoint_product_symmetric positive_adjoint_product
  equiv_ext_basis inverse_on_eigenvector from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PolarRealStructures

universe u v

private theorem toAut_trans {L : Type u} [LieRing L] [LieAlgebra ℂ L]
    (a b : L ≃ₗ⁅ℂ⁆ L) : toAut (a.trans b) = toAut b * toAut a := rfl

private theorem pow_apply_of_eigenvalue {L : Type u} [LieRing L] [LieAlgebra ℂ L]
    (a : Aut L) (n : ℕ) (c : ℂ) (z : L) (h : a.val z = c • z) :
    (a ^ n).val z = c ^ n • z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ']
    change (a ^ n).val (a.val z) = (c * c ^ n) • z
    rw [h, map_smul, ih, smul_smul]

theorem compactRepresentatives : compactRepresentativesType.{u,v} := by
  intro L _ _ _ ω hc G _ _ q a
  let d := sandwich ω ω a.symm
  let p := a.trans d
  obtain ⟨basis, r, hr⟩ := real_eigenbasis ω hc p (adjoint_product_symmetric ω a)
  have hpos i : 0 < r i := positive_adjoint_product ω hc a (basis.ne_zero i) (hr i)
  have hpω (z : L) : p (ω.map z) = ω.map (p.symm z) := by
    change ω.map (a.symm (ω.map (a (ω.map z)))) =
      ω.map (a.symm (ω.map (a (ω.map z))))
    rfl
  obtain ⟨s, hs, _⟩ := PolarRealStructures.adjoint_product_power ω hc a (1/2)
  have hs' (i) : s (basis i) = ((r i ^ (1/2 : ℝ) : ℝ) : ℂ) • basis i :=
    hs _ _ (hr i)
  have hss : s.trans s = p := by
    apply equiv_ext_basis basis
    intro i
    change s (s (basis i)) = p (basis i)
    nth_rw 1 [hs']
    rw [map_smul, hs', smul_smul, ← ofReal_mul, ← Real.rpow_add (hpos i)]
    norm_num [Real.rpow_one, hr]
  have hsω (z : L) : ω.map (s z) = s.symm (ω.map z) := by
    have he : sandwich ω ω s = s.symm := by
      apply equiv_ext_basis basis
      intro i
      have hi : p (ω.map (basis i)) = (((r i)⁻¹ : ℝ) : ℂ) • ω.map (basis i) := by
        rw [hpω, inverse_on_eigenvector p (hpos i).ne' (hr i),
          ω.antilinear, star_def, conj_ofReal]
      change ω.map (s (ω.map (basis i))) = s.symm (basis i)
      rw [hs _ _ hi, ω.antilinear, star_def, conj_ofReal, ω.involutive,
        Real.inv_rpow (hpos i).le,
        inverse_on_eigenvector s (Real.rpow_pos_of_pos (hpos i) _).ne' (hs' i)]
    have hh := congrArg (fun k : L ≃ₗ⁅ℂ⁆ L => k (ω.map z)) he
    change ω.map (s (ω.map (ω.map z))) = s.symm (ω.map z) at hh
    rwa [ω.involutive] at hh
  let N := Nat.card G
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  obtain ⟨t, ht, _⟩ := PolarRealStructures.adjoint_product_power ω hc a ((1/2) / N)
  have hsN : toAut s = toAut t ^ N := by
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply basis.ext
    intro i
    change s (basis i) = (toAut t ^ N).val (basis i)
    rw [hs', pow_apply_of_eigenvalue (toAut t) N _ _ (ht _ _ (hr i)),
      ← ofReal_pow, ← Real.rpow_mul_natCast (hpos i).le, div_mul_cancel₀ _ hN]
  have hqs : q (toAut s) = 1 := by rw [hsN, map_pow, pow_card_eq_one']
  let b := s.symm.trans a
  refine ⟨b, ?_, ?_⟩
  · intro z
    change ω.map (a (s.symm z)) = a (s.symm (ω.map z))
    have hds (w : L) : d (a w) = s (s w) :=
      congrArg (fun k : L ≃ₗ⁅ℂ⁆ L => k w) hss.symm
    have hds' (w : L) : a (s.symm w) = d.symm (s w) := by
      apply d.injective
      change d (a (s.symm w)) = d (d.symm (s w))
      rw [d.apply_symm_apply, hds, s.apply_symm_apply]
    calc
      _ = ω.map (d.symm (s z)) := congrArg ω.map (hds' z)
      _ = a (ω.map (s z)) := ω.involutive _
      _ = _ := congrArg a (hsω z)
  · have hinv : toAut s.symm = (toAut s)⁻¹ := rfl
    rw [show b = s.symm.trans a by rfl, toAut_trans, hinv, map_mul, map_inv, hqs,
      inv_one, mul_one]

section Diagrams

open LieAlgebrasAndRepresentations.ClassicalCoordinates

theorem b_diagram_trivial : bDiagramTrivialType := by
  intro n p hEdge hArrow
  by_cases hn : n < 2
  · have hsub : Subsingleton (Fin n) := ⟨fun i j => Fin.ext (by
      have := i.isLt
      have := j.isLt
      omega)⟩
    exact Equiv.ext (fun _ => Subsingleton.elim _ _)
  have hAdj (i j : Fin n) : adjacent (p i) (p j) ↔ adjacent i j := by
    have zero_edge (i j : Fin n) :
        (dynkinDiagram (simpleB n)).edges i j ≠ 0 ↔ adjacent i j := by
      rw [simpleB_diagram_edges]
      by_cases ht : terminalEdge i j
      · simp only [ite_eq_left ht]
        unfold terminalEdge adjacent at *
        omega
      · simp [ht]
    rw [← zero_edge, ← zero_edge, hEdge]
  let a : Fin n := ⟨n - 2, by omega⟩
  let b : Fin n := ⟨n - 1, by omega⟩
  have hb := (hArrow a b).mpr ((simpleB_diagram_arrows a b).mpr (by
    dsimp [a, b]
    omega))
  have hFix := (simpleB_diagram_arrows (p a) (p b)).mp hb
  have hAll (d : ℕ) (i : Fin n) (hi : i.val + d + 1 = n) : p i = i := by
    induction d using Nat.strong_induction_on generalizing i with
    | h d ih =>
      by_cases hd : d < 2
      · by_cases he : d = 0
        · have h : i = b := Fin.ext (by dsimp [b]; omega)
          subst i
          exact Fin.ext (by dsimp [b] at *; omega)
        · have h : i = a := Fin.ext (by dsimp [a]; omega)
          subst i
          exact Fin.ext (by dsimp [a] at *; omega)
      let j : Fin n := ⟨i.val + 1, by omega⟩
      let k : Fin n := ⟨i.val + 2, by omega⟩
      have hj := ih (d - 1) (by omega) j (by dsimp [j]; omega)
      have hk := ih (d - 2) (by omega) k (by dsimp [k]; omega)
      have h := (hAdj i j).mpr (Or.inl rfl)
      rw [hj] at h
      have hne : (p i).val ≠ k.val := by
        intro he
        have := p.injective ((Fin.ext he).trans hk.symm)
        change i = k at this
        have := congrArg Fin.val this
        dsimp [k] at this
        omega
      unfold adjacent at h
      dsimp [j, k] at h hne
      exact Fin.ext (by omega)
  exact Equiv.ext fun i => hAll (n - 1 - i.val) i (by have := i.isLt; omega)

private def forkLeaf {n : ℕ} (i : Fin n) : Prop :=
  if n = 4 then i.val ≠ 1 else n ≤ i.val + 2

private theorem leaf_adjacent {n : ℕ} (_hn : 3 ≤ n) {i j : Fin n} (hi : forkLeaf i) :
    forkAdjacent i j ↔ j.val + 3 = n := by
  have hi' := i.isLt
  have hj' := j.isLt
  unfold forkAdjacent forkLeaf at *
  split at hi <;> omega

private theorem fork_fixed_center {n : ℕ} (hn : 3 ≤ n) (p : forkGroup n) :
    let c : Fin n := ⟨n - 3, by omega⟩
    p.val c = c := by
  let c : Fin n := ⟨n - 3, by omega⟩
  let a : Fin n := ⟨n - 2, by omega⟩
  let b : Fin n := ⟨n - 1, by omega⟩
  have ac : forkAdjacent a c := by
    unfold forkAdjacent
    dsimp [a, c]
    omega
  have bc : forkAdjacent b c := by
    unfold forkAdjacent
    dsimp [b, c]
    omega
  have h1 := (p.property a c).mpr ac
  have h2 := (p.property b c).mpr bc
  have hne : (p.val a).val ≠ (p.val b).val := by
    intro hab
    have := congrArg Fin.val (p.val.injective (Fin.ext hab))
    dsimp [a, b] at this
    omega
  have ha := (p.val a).isLt
  have hb := (p.val b).isLt
  have hc := (p.val c).isLt
  by_cases hn3 : n = 3
  · unfold forkAdjacent at h1 h2
    exact Fin.ext (by change (p.val c).val = n - 3; omega)
  have hc1 : 4 ≤ n := by omega
  let d : Fin n := ⟨n - 4, by omega⟩
  have h3 : forkAdjacent d c := by
    unfold forkAdjacent
    dsimp [d, c]
    omega
  have h3 := (p.property d c).mpr h3
  have hda : (p.val d).val ≠ (p.val a).val := by
    intro he
    have := congrArg Fin.val (p.val.injective (Fin.ext he))
    dsimp [d, a] at this
    omega
  have hdb : (p.val d).val ≠ (p.val b).val := by
    intro he
    have := congrArg Fin.val (p.val.injective (Fin.ext he))
    dsimp [d, b] at this
    omega
  have hd := (p.val d).isLt
  unfold forkAdjacent at h1 h2 h3
  exact Fin.ext (by change (p.val c).val = n - 3; omega)

private theorem fork_fixes_complement {n : ℕ} (hn : 3 ≤ n) (p : forkGroup n)
    (i : Fin n) (hi : ¬forkLeaf i) : p.val i = i := by
  let c : Fin n := ⟨n - 3, by omega⟩
  have hc : p.val c = c := fork_fixed_center hn p
  by_cases hsmall : n ≤ 4
  · have he : i = c := Fin.ext (by
      have := i.isLt
      unfold forkLeaf at hi
      split at hi <;> dsimp [c] <;> omega)
    rwa [he]
  have hge : 5 ≤ n := by omega
  let a : Fin n := ⟨n - 4, by omega⟩
  let b : Fin n := ⟨n - 5, by omega⟩
  have ha : p.val a = a := by
    have hab : forkAdjacent a b := by
      unfold forkAdjacent
      dsimp [a, b]
      omega
    have hac : forkAdjacent a c := by
      unfold forkAdjacent
      dsimp [a, c]
      omega
    have ec := (p.property a c).mpr hac
    rw [hc] at ec
    have hne : (p.val b).val ≠ c.val := by
      intro he
      have := congrArg Fin.val (p.val.injective ((Fin.ext he).trans hc.symm))
      dsimp [b, c] at this
      omega
    have hno : ¬forkLeaf (p.val a) := fun h =>
      hne (by have := (leaf_adjacent hn h).mp ((p.property a b).mpr hab); dsimp [c]; omega)
    unfold forkAdjacent at ec
    have := (p.val a).isLt
    unfold forkLeaf at hno
    rw [ite_eq_right (by omega)] at hno
    exact Fin.ext (by dsimp [c, a] at *; omega)
  have hAll (d : ℕ) (i : Fin n) (hi : i.val + d + 3 = n) : p.val i = i := by
    induction d using Nat.strong_induction_on generalizing i with
    | h d ih =>
      by_cases he : d < 2
      · by_cases hd : d = 0
        · have : i = c := Fin.ext (by dsimp [c]; omega)
          rwa [this]
        · have : i = a := Fin.ext (by dsimp [a]; omega)
          rwa [this]
      let j : Fin n := ⟨i.val+1, by omega⟩
      let k : Fin n := ⟨i.val+2, by omega⟩
      have hj := ih (d-1) (by omega) j (by dsimp [j]; omega)
      have hk := ih (d-2) (by omega) k (by dsimp [k]; omega)
      have e : forkAdjacent i j := by
        unfold forkAdjacent
        dsimp [j]
        omega
      have h := (p.property i j).mpr e
      rw [hj] at h
      have hne : (p.val i).val ≠ k.val := by
        intro hv
        have := congrArg Fin.val (p.val.injective ((Fin.ext hv).trans hk.symm))
        dsimp [k] at this
        omega
      unfold forkAdjacent at h
      have := (p.val i).isLt
      dsimp [j, k] at h hne
      exact Fin.ext (by omega)
  unfold forkLeaf at hi
  rw [ite_eq_right (by omega)] at hi
  exact hAll (n - 3 - i.val) i (by omega)

private def forkLeafIndex {n : ℕ} (hn : 3 ≤ n) :
    Subtype (forkLeaf (n := n)) ≃ Fin (if n = 4 then 3 else 2) := by
  by_cases h : n = 4
  · subst n
    change Subtype (forkLeaf (n := 4)) ≃ Fin 3
    refine ⟨fun i => ⟨if i.val.val = 0 then 0 else i.val.val - 1, by
      have := i.val.isLt
      split <;> omega⟩, fun k => ⟨⟨if k.val = 0 then 0 else k.val + 1, by
      have := k.isLt
      split <;> omega⟩, by
      change (if k.val = 0 then 0 else k.val + 1) ≠ 1
      split <;> omega⟩, ?_, ?_⟩
    · intro i
      apply Subtype.ext
      apply Fin.ext
      have hi : i.val.val ≠ 1 := i.property
      change (if (if i.val.val = 0 then 0 else i.val.val - 1) = 0 then 0
        else (if i.val.val = 0 then 0 else i.val.val - 1) + 1) = i.val.val
      split_ifs <;> omega
    · intro k
      apply Fin.ext
      have := k.isLt
      change (if (if k.val = 0 then 0 else k.val + 1) = 0 then 0
        else (if k.val = 0 then 0 else k.val + 1) - 1) = k.val
      by_cases hk : k.val = 0 <;> simp [hk]
  rw [ite_eq_right h]
  refine ⟨fun i => ⟨i.val.val - (n - 2), by have := i.val.isLt; omega⟩,
    fun k => ⟨⟨n - 2 + k.val, by have := k.isLt; omega⟩, by
      unfold forkLeaf
      rw [ite_eq_right h]
      change n ≤ n - 2 + k.val + 2
      omega⟩, ?_, ?_⟩
  · intro i
    apply Subtype.ext
    apply Fin.ext
    have hi := i.property
    unfold forkLeaf at hi
    rw [ite_eq_right h] at hi
    change n - 2 + (i.val.val - (n - 2)) = i.val.val
    omega
  · intro k
    apply Fin.ext
    change n - 2 + k.val - (n - 2) = k.val
    omega

private theorem leaf_center_iff {n : ℕ} (_hn : 3 ≤ n) (i : Fin n) :
    i.val + 3 = n → ¬forkLeaf i := by
  intro hi
  unfold forkLeaf
  split <;> omega

private theorem forkGroup_eq_range {n : ℕ} (hn : 3 ≤ n)
    [DecidablePred (forkLeaf (n := n))] :
    forkGroup n =
      (Equiv.Perm.ofSubtype : Equiv.Perm (Subtype (forkLeaf (n := n))) →*
        Equiv.Perm (Fin n)).range := by
  ext p
  rw [Equiv.Perm.mem_range_ofSubtype_iff]
  constructor
  · intro hp i hi
    by_contra hnmem
    exact Equiv.Perm.mem_support.mp hi (fork_fixes_complement hn ⟨p, hp⟩ i hnmem)
  · intro hs
    have hf (i : Fin n) (hi : ¬forkLeaf i) : p i = i := by
      by_contra h
      exact hi (hs (Equiv.Perm.mem_support.mpr h))
    have hp (i : Fin n) (hi : forkLeaf i) : forkLeaf (p i) := by
      by_contra h
      have he : i = p i := p.injective (hf (p i) h).symm
      exact h (he ▸ hi)
    have hf' (i : Fin n) : (p i).val + 3 = n ↔ i.val + 3 = n := by
      by_cases h : forkLeaf i
      · exact iff_of_false (fun he => leaf_center_iff hn (p i) he (hp i h))
          (fun he => leaf_center_iff hn i he h)
      · rw [hf i h]
    change ∀ i j, forkAdjacent (p i) (p j) ↔ forkAdjacent i j
    intro i j
    by_cases hi : forkLeaf i
    · rw [leaf_adjacent hn (hp i hi), leaf_adjacent hn hi, hf']
    by_cases hj : forkLeaf j
    · have symm (a b : Fin n) : forkAdjacent a b ↔ forkAdjacent b a := by
        unfold forkAdjacent
        omega
      rw [symm (p i) (p j), symm i j, leaf_adjacent hn (hp j hj), leaf_adjacent hn hj,
        hf']
    · rw [hf i hi, hf j hj]

theorem fork_group_iso : forkGroupIsoType := by
  classical
  intro n hn
  exact ⟨(MulEquiv.subgroupCongr (forkGroup_eq_range hn)).trans
    ((MonoidHom.ofInjective Equiv.Perm.ofSubtype_injective).symm.trans
      (forkLeafIndex hn).permCongrHom)⟩

end Diagrams

open Matrix LieAlgebra
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem sign_sq {R : Type*} [Ring R] {ι : Type*} [DecidableEq ι] (j i : ι) :
    (if i = j then (-1 : R) else 1) * (if i = j then -1 else 1) = 1 := by
  split <;> simp

theorem reflectionMatrix_properties : reflectionMatrixSpec.{u} := by
  intro ι _ _ j
  change (reflectionMatrix ι j)ᵀ * reflectionMatrix ι j = 1 ∧
    (reflectionMatrix ι j).det = -1
  constructor
  · unfold reflectionMatrix
    rw [diagonal_transpose, diagonal_mul_diagonal]
    simpa only [sign_sq] using (diagonal_one : Matrix.diagonal (1 : ι → ℝ) = 1)
  · unfold reflectionMatrix
    rw [det_diagonal, Finset.prod_eq_single j]
    · simp
    · intro i _ hi
      simp [hi]
    · simp

private theorem complex_reflection {ι : Type u} [Fintype ι] [DecidableEq ι] (j : ι) :
    Complex.ofRealHom.mapMatrix (reflectionMatrix ι j) =
      Matrix.diagonal (fun i => if i = j then (-1 : ℂ) else 1) := by
  ext i k
  change ((reflectionMatrix ι j i k : ℝ) : ℂ) = _
  by_cases h : i = k
  · subst k
    by_cases hj : i = j <;> simp [Specs.LieAlgebrasAndRepresentations.OrthogonalDiagramReduction.reflectionMatrix,
      hj]
  · simp [Specs.LieAlgebrasAndRepresentations.OrthogonalDiagramReduction.reflectionMatrix,
      h]

private theorem reflection_transpose_mul {ι : Type u} [Fintype ι] [DecidableEq ι] (j : ι) :
    let A := Complex.ofRealHom.mapMatrix (reflectionMatrix ι j)
    Aᵀ = A ∧ A * A = 1 := by
  dsimp
  rw [complex_reflection, diagonal_transpose, diagonal_mul_diagonal]
  refine ⟨rfl, ?_⟩
  simp only [sign_sq]
  exact diagonal_one

private def reflectionAction {ι : Type u} [Fintype ι] [DecidableEq ι] (j : ι) :
    so ι ≃ₗ⁅ℂ⁆ so ι := by
  let A := Complex.ofRealHom.mapMatrix (reflectionMatrix ι j)
  have ht : Aᵀ = A := (reflection_transpose_mul j).1
  have hs : A * A = 1 := (reflection_transpose_mul j).2
  have mem (X : so ι) : A * X.val * A ∈ so ι := by
    rw [Orthogonal.mem_so, transpose_mul, transpose_mul, ht,
      (Orthogonal.mem_so _ _ _).1 X.property]
    simp [mul_assoc]
  let f (X : so ι) : so ι := ⟨A * X.val * A, mem X⟩
  have hinv : Function.Involutive f := by
    intro X
    apply Subtype.ext
    change A * (A * X.val * A) * A = X.val
    calc
      _ = (A * A) * X.val * (A * A) := by noncomm_ring
      _ = _ := by rw [hs, one_mul, mul_one]
  refine
    { toFun := f
      invFun := f
      left_inv := hinv
      right_inv := hinv
      map_add' := ?_
      map_smul' := ?_
      map_lie' := ?_ }
  · intro X Y
    apply Subtype.ext
    change A * (X.val + Y.val) * A = A * X.val * A + A * Y.val * A
    rw [mul_add, add_mul]
  · intro k X
    apply Subtype.ext
    change A * (k • X.val) * A = k • (A * X.val * A)
    rw [mul_smul_comm, smul_mul_assoc]
  · intro X Y
    apply Subtype.ext
    change A * (X.val * Y.val - Y.val * X.val) * A =
      (A * X.val * A) * (A * Y.val * A) - (A * Y.val * A) * (A * X.val * A)
    calc
      _ = A * (X.val * (1 : Matrix ι ι ℂ) * Y.val -
          Y.val * (1 : Matrix ι ι ℂ) * X.val) * A := by simp
      _ = _ := by rw [← hs]; noncomm_ring

theorem reflectionExists : reflectionExistsType.{u} := by
  intro ι _ _ j
  refine ⟨reflectionAction j, fun X => ?_⟩
  change _ * X.val * Complex.ofRealHom.mapMatrix (reflectionMatrix ι j) = _
  rw [(reflection_transpose_mul j).1]

private def asLieEquiv {L : Type u} [LieRing L] [LieAlgebra ℂ L] (a : Aut L) :
    L ≃ₗ⁅ℂ⁆ L :=
  { a.val with map_lie' := fun {x y} => a.property x y }

private theorem toAut_involutive_sq {L : Type u} [LieRing L] [LieAlgebra ℂ L]
    (a : L ≃ₗ⁅ℂ⁆ L) (ha : Function.Involutive a) : toAut a ^ 2 = 1 := by
  rw [pow_two]
  apply Subtype.ext
  exact LinearEquiv.ext ha

private theorem cycleType_involution {k : ℕ} (hk : k ≤ 3) {a : Equiv.Perm (Fin k)}
    (ha : a ^ 2 = 1) (hne : a ≠ 1) : a.cycleType = {2} := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht := Equiv.Perm.cycleType_of_pow_prime_eq_one ha
  have hn := Equiv.Perm.card_cycleType_eq_zero.not.mpr hne
  apply Equiv.Perm.cycleType_of_card_le_mem_cycleType_add_two
  · simpa using Nat.lt_succ_of_le hk
  · rw [ht, Multiset.mem_replicate]
    exact ⟨hn, rfl⟩

private theorem compact_conjugates_of_quotient {L : Type u}
    [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (ω : Conjugation L) (hc : IsCompact ω)
    {G : Type v} [Group G] [Finite G] (q : Aut L →* G) (hq : Function.Surjective q)
    (a r : L ≃ₗ⁅ℂ⁆ L) (h : IsConj (q (toAut a)) (q (toAut r))) :
    ∃ b : L ≃ₗ⁅ℂ⁆ L, Intertwines ω ω b ∧
      q (toAut b * toAut a * (toAut b)⁻¹) = q (toAut r) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  obtain ⟨f, hf⟩ := hq g
  obtain ⟨b, hb, hbf⟩ := compactRepresentatives ω hc q (asLieEquiv f)
  exact ⟨b, hb, by rw [map_mul, map_mul, map_inv, hbf, show toAut (asLieEquiv f) = f from rfl, hf, hg]⟩

private theorem reduction_of_quotient (outer : outerQuotientType.{u}) :
    outerClassReductionType.{u} := by
  intro ι _ _ hss hN ω _ hc normal a ha j
  letI := normal
  have hparity : (∃ n : ℕ, 1 ≤ n ∧ Fintype.card ι = 2*n+1) ∨
      (∃ n : ℕ, 3 ≤ n ∧ Fintype.card ι = 2*n) := by
    let n := Fintype.card ι / 2
    have hn : Fintype.card ι = 2*n ∨ Fintype.card ι = 2*n+1 := by dsimp [n]; omega
    rcases hn with h | h
    · exact Or.inr ⟨n, by omega, h⟩
    · exact Or.inl ⟨n, by omega, h⟩
  obtain ⟨_, hB, hD, hD4, hrclass⟩ := outer ι hss hparity
  let q := QuotientGroup.mk' (innerAut (so ι))
  obtain ⟨r, hr⟩ := reflectionExists ι j
  have hid (hq : q (toAut a) = 1) :
      ∃ (b r : so ι ≃ₗ⁅ℂ⁆ so ι), Intertwines ω ω b ∧ ActsByReflection ι j r ∧
        let g := toAut b * toAut a * (toAut b)⁻¹
        g ∈ innerAut (so ι) ∨ g * (toAut r)⁻¹ ∈ innerAut (so ι) := by
    refine ⟨LieEquiv.refl, r, fun _ => rfl, hr, Or.inl ?_⟩
    simpa only [show toAut (LieEquiv.refl : so ι ≃ₗ⁅ℂ⁆ so ι) = 1 by rfl, one_mul,
      inv_one, mul_one] using (QuotientGroup.eq_one_iff _).mp hq
  by_cases hqa : q (toAut a) = 1
  · exact hid hqa
  rcases hparity with ⟨n, hn, hcard⟩ | ⟨n, hn, hcard⟩
  · letI := hB n hn hcard
    exact (hqa (Subsingleton.elim _ _)).elim
  have hr' := hrclass n hn hcard j r hr
  have outer_action {k : ℕ} (hk : k ≤ 3)
      (e : (Aut (so ι) ⧸ innerAut (so ι)) ≃* Equiv.Perm (Fin k)) :
      IsConj (q (toAut a)) (q (toAut r)) := by
    have hpa : e (q (toAut a)) ^ 2 = 1 := by
      rw [← map_pow, show q (toAut a) ^ 2 = 1 from ha, map_one]
    have hp : q (toAut r) ^ 2 = 1 := hr'.2
    have hpr : e (q (toAut r)) ^ 2 = 1 := by rw [← map_pow, hp, map_one]
    have hne (v : _) (hv : v ≠ 1) : e v ≠ 1 := by
      intro hz
      exact hv (e.injective (hz.trans (map_one e).symm))
    have hconj := Equiv.Perm.isConj_iff_cycleType_eq.mpr
      ((cycleType_involution hk hpa (hne _ hqa)).trans
        (cycleType_involution hk hpr (hne _ hr'.1)).symm)
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    refine isConj_iff.mpr ⟨e.symm g, e.injective ?_⟩
    simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using hg
  have hconj : IsConj (q (toAut a)) (q (toAut r)) := by
    by_cases h4 : n = 4
    · obtain ⟨e⟩ := hD4 (by omega)
      exact outer_action (by decide) e
    · obtain ⟨e⟩ := hD n hn h4 hcard
      exact outer_action (by decide) e
  haveI : Finite (Aut (so ι) ⧸ innerAut (so ι)) := by
    by_cases h4 : n = 4
    · obtain ⟨e⟩ := hD4 (by omega)
      exact Finite.of_injective e e.injective
    · obtain ⟨e⟩ := hD n hn h4 hcard
      exact Finite.of_injective e e.injective
  obtain ⟨b, hb, hbr⟩ := compact_conjugates_of_quotient ω hc q
    (QuotientGroup.mk'_surjective _) a r hconj
  refine ⟨b, r, hb, hr, Or.inr ((QuotientGroup.eq_one_iff _).mp ?_)⟩
  change q (_ * _) = 1
  rw [q.map_mul, hbr, q.map_inv, mul_inv_cancel]

section MatrixCartans

open Module Polynomial
open Specs.LieAlgebrasAndRepresentations.MaximalTori
open Specs.LieAlgebrasAndRepresentations.RootDecomposition

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]
variable {n : ℕ}

private abbrev Params (n : ℕ) := Fin n → ℂ
private abbrev Weight (n : ℕ) := Module.Dual ℂ (Params n)

private def matricesOfEquiv (S : LieSubalgebra ℂ (Matrix κ κ ℂ)) (e : L ≃ₗ⁅ℂ⁆ S) :
    L →ₗ⁅ℂ⁆ Matrix κ κ ℂ :=
  S.incl.comp e.toLieHom

private theorem matricesOfEquiv_injective
    (S : LieSubalgebra ℂ (Matrix κ κ ℂ)) (e : L ≃ₗ⁅ℂ⁆ S) :
    Function.Injective (matricesOfEquiv S e) :=
  Subtype.val_injective.comp e.injective

private def liftDiagonals (S : LieSubalgebra ℂ (Matrix κ κ ℂ))
    (e : L ≃ₗ⁅ℂ⁆ S) (D : Params n →ₗ[ℂ] Matrix κ κ ℂ) (hD : ∀ t, D t ∈ S) :
    Params n →ₗ[ℂ] L :=
  e.symm.toLinearEquiv.toLinearMap.comp (D.codRestrict S.toSubmodule hD)

private theorem matricesOfEquiv_liftDiagonals (S : LieSubalgebra ℂ (Matrix κ κ ℂ))
    (e : L ≃ₗ⁅ℂ⁆ S) (D : Params n →ₗ[ℂ] Matrix κ κ ℂ) (hD : ∀ t, D t ∈ S)
    (t : Params n) :
    matricesOfEquiv S e (liftDiagonals S e D hD t) = D t :=
  congrArg Subtype.val (e.apply_symm_apply ⟨D t, hD t⟩)

private theorem ad_diagonal_semisimple (z : κ → ℂ) :
    (LieAlgebra.ad ℂ (Matrix κ κ ℂ) (Matrix.diagonal z)).IsSemisimple := by
  classical
  let f := LieAlgebra.ad ℂ (Matrix κ κ ℂ) (Matrix.diagonal z)
  let val (i : κ × κ) := z i.1 - z i.2
  let T := Finset.univ.image val
  let P : ℂ[X] := ∏ a ∈ T, (Polynomial.X - Polynomial.C a)
  have hs : Squarefree P := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro a _ b _ hab
      exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hab).isUnit).isRelPrime
    · intro a _
      exact (Polynomial.irreducible_X_sub_C a).squarefree
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hs
  apply (Matrix.stdBasis ℂ κ κ).ext
  rintro ⟨i, j⟩
  rw [Matrix.stdBasis_eq_single]
  have heig : f (Matrix.single i j 1) = val (i,j) • Matrix.single i j 1 := by
    ext a b
    change (Matrix.diagonal z * (Matrix.single i j 1 : Matrix κ κ ℂ)) a b -
      ((Matrix.single i j 1 : Matrix κ κ ℂ) * Matrix.diagonal z) a b = _
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases ha : i = a <;> by_cases hb : j = b <;>
      simp [Matrix.single_apply, ha, hb, val]
  change Polynomial.aeval f P (Matrix.single i j 1) = 0
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul heig]
  have hv : val (i,j) ∈ T := Finset.mem_image.mpr ⟨(i,j), Finset.mem_univ _, rfl⟩
  have hzero : P.eval (val (i,j)) = 0 := by
    unfold P
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero hv (by simp)
  rw [hzero, zero_smul]

private def diagonalCartan (F : L →ₗ⁅ℂ⁆ Matrix κ κ ℂ) (hF : Function.Injective F)
    (D : Params n →ₗ[ℂ] L) (z : Params n → κ → ℂ)
    (hD : ∀ t, F (D t) = Matrix.diagonal (z t)) : LieSubalgebra ℂ L where
  toSubmodule := D.range
  lie_mem' {x y} hx hy := by
    obtain ⟨t, rfl⟩ := hx
    obtain ⟨s, rfl⟩ := hy
    refine ⟨0, hF ?_⟩
    rw [map_zero, map_zero, F.map_lie, hD, hD]
    change 0 = Matrix.diagonal (z t) * Matrix.diagonal (z s) -
      Matrix.diagonal (z s) * Matrix.diagonal (z t)
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    simp [mul_comm]

private theorem diagonalCartan_maximal
    (F : L →ₗ⁅ℂ⁆ Matrix κ κ ℂ) (hF : Function.Injective F)
    (D : Params n →ₗ[ℂ] L) (z : Params n → κ → ℂ)
    (hD : ∀ t, F (D t) = Matrix.diagonal (z t))
    (hcenter : ∀ x : L, (∀ t, ⁅D t, x⁆ = 0) → x ∈ D.range) :
    IsMaximalToral_value (diagonalCartan F hF D z hD) := by
  let H := diagonalCartan F hF D z hD
  have hab : IsLieAbelian H := by
    constructor
    rintro ⟨x, t, rfl⟩ ⟨y, s, rfl⟩
    apply Subtype.ext
    change ⁅D t, D s⁆ = 0
    apply hF
    rw [F.map_lie, map_zero, hD, hD]
    change Matrix.diagonal (z t) * Matrix.diagonal (z s) -
      Matrix.diagonal (z s) * Matrix.diagonal (z t) = 0
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    simp [mul_comm]
  refine ⟨⟨hab, ?_⟩, ?_⟩
  · rintro ⟨x, t, rfl⟩
    let f := LieAlgebra.ad ℂ (Matrix κ κ ℂ) (F (D t))
    have hf : f.IsSemisimple := by
      simpa only [f, hD] using ad_diagonal_semisimple (z t)
    let FL := F.toLinearMap
    have hinv : FL.range ∈ f.invtSubmodule := by
      rintro X ⟨x, rfl⟩
      exact ⟨⁅D t, x⁆, F.map_lie _ _⟩
    let E : L ≃ₗ[ℂ] LinearMap.range FL := LinearEquiv.ofInjective FL hF
    exact (E.isSemisimple_iff _ _ (by
      apply LinearMap.ext
      intro y
      apply Subtype.ext
      exact F.map_lie _ _)).mpr (hf.restrict hinv)
  · intro K hK hHK x hx
    apply hcenter
    intro t
    have hDt : D t ∈ K := hHK (show D t ∈ H from ⟨t, rfl⟩)
    letI := hK.1
    exact congrArg Subtype.val (trivial_lie_zero K K ⟨D t, hDt⟩ ⟨x, hx⟩)

private def diagonalCoords
    (F : L →ₗ⁅ℂ⁆ Matrix κ κ ℂ) (hF : Function.Injective F)
    (D : Params n →ₗ[ℂ] L) (z : Params n → κ → ℂ)
    (hD : ∀ t, F (D t) = Matrix.diagonal (z t)) (h : Function.Injective D) :
    Params n ≃ₗ[ℂ] diagonalCartan F hF D z hD :=
  LinearEquiv.ofInjective D h

private theorem diagonal_weightSpace
    (F : L →ₗ⁅ℂ⁆ Matrix κ κ ℂ) (hF : Function.Injective F)
    (D : Params n →ₗ[ℂ] L) (z : Params n → κ → ℂ)
    (hD : ∀ t, F (D t) = Matrix.diagonal (z t)) (h : Function.Injective D)
    (α : Weight n) (x : L) :
    let E := diagonalCoords F hF D z hD h
    x ∈ rootSpace_value (diagonalCartan F hF D z hD) (α.comp E.symm.toLinearMap) ↔
      ∀ t, ⁅F (D t), F x⁆ = α t • F x := by
  let E := diagonalCoords F hF D z hD h
  dsimp only
  rw [mem_rootSpace]
  constructor
  · intro hx t
    have hh := hx (E t)
    change ⁅D t, x⁆ = α (E.symm (E t)) • x at hh
    rw [E.symm_apply_apply] at hh
    exact (F.map_lie _ _).symm.trans (by rw [hh, map_smul])
  · intro hx a
    obtain ⟨t, rfl⟩ := E.surjective a
    apply hF
    change F ⁅D t, x⁆ = F (α (E.symm (E t)) • x)
    rw [F.map_lie, map_smul, E.symm_apply_apply]
    exact hx t

end MatrixCartans

section MatrixRootCharts

open Module
open Specs.LieAlgebrasAndRepresentations.MaximalTori
open Specs.LieAlgebrasAndRepresentations.RootDecomposition
open Specs.LieAlgebrasAndRepresentations.RootForm

open LieAlgebrasAndRepresentations.ClassicalCoordinates



variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]
variable {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- A coordinate description of the maximal torus and all its weight spaces.
The isomorphism to the hyperbolic matrix model is retained. -/
private structure MatrixRootChart
    (S : LieSubalgebra ℂ (Matrix κ κ ℂ)) (e : L ≃ₗ⁅ℂ⁆ S)
    (d : Params n →ₗ[ℂ] Matrix κ κ ℂ) (W : Weight n → Submodule ℂ (Matrix κ κ ℂ)) where
  H : LieSubalgebra ℂ L
  maximal : IsMaximalToral_value H
  coords : Params n ≃ₗ[ℂ] H
  diagonal (t : Params n) : (e (coords t : L) : Matrix κ κ ℂ) = d t
  weightSpace (a : Weight n) (x : L) :
    x ∈ rootSpace_value H (a.comp coords.symm.toLinearMap) ↔
      (e x : Matrix κ κ ℂ) ∈ W a

private def matrixRootChart
    (S : LieSubalgebra ℂ (Matrix κ κ ℂ)) (e : L ≃ₗ⁅ℂ⁆ S)
    (d : Params n →ₗ[ℂ] Matrix κ κ ℂ) (z : Params n → κ → ℂ)
    (W : Weight n → Submodule ℂ (Matrix κ κ ℂ))
    (hdiag : ∀ t, d t = Matrix.diagonal (z t))
    (hS : ∀ t, d t ∈ S)
    (hinj : Function.Injective d)
    (hzero : ∀ X ∈ W 0, ∃ t, X = d t)
    (hW : ∀ a X, X ∈ W a ↔ X ∈ S ∧ ∀ t, ⁅d t, X⁆ = a t • X) :
    MatrixRootChart S e d W := by
  let F := matricesOfEquiv S e
  let A := liftDiagonals S e d hS
  have hFA (t : Params n) : F (A t) = d t := matricesOfEquiv_liftDiagonals S e d hS t
  have hF := matricesOfEquiv_injective S e
  have hA : Function.Injective A := by
    intro t s he
    apply hinj
    rw [← hFA, ← hFA, he]
  let H := diagonalCartan F hF A z (fun t => (hFA t).trans (hdiag t))
  let E := diagonalCoords F hF A z (fun t => (hFA t).trans (hdiag t)) hA
  have hHA : ∀ x : L, (∀ t, ⁅A t, x⁆ = 0) → x ∈ A.range := by
    intro x hx
    have he : F x ∈ W 0 := (hW _ _).mpr ⟨(e x).property, fun t => by
      rw [← hFA, ← F.map_lie, hx, map_zero]
      simp⟩
    obtain ⟨t, ht⟩ := hzero _ he
    exact ⟨t, hF ((hFA t).trans ht.symm)⟩
  refine ⟨H, diagonalCartan_maximal _ _ _ _ _ hHA, E, hFA, ?_⟩
  intro a x
  change x ∈ rootSpace_value _ (a.comp E.symm.toLinearMap) ↔ F x ∈ W a
  have hweight := diagonal_weightSpace F hF A z (fun t => (hFA t).trans (hdiag t)) hA a x
  dsimp only at hweight
  rw [hweight, hW]
  simp only [hFA, and_iff_right (show F x ∈ S from (e x).property)]

private theorem chart_root_mem
    {S : LieSubalgebra ℂ (Matrix κ κ ℂ)} {e : L ≃ₗ⁅ℂ⁆ S}
    {d : Params n →ₗ[ℂ] Matrix κ κ ℂ} {W : Weight n → Submodule ℂ (Matrix κ κ ℂ)}
    (c : MatrixRootChart S e d W)
    (hW : ∀ a, W a ≤ S.toSubmodule) (a : Weight n) :
    a.comp c.coords.symm.toLinearMap ∈ rootSet_value c.H ↔ a ≠ 0 ∧ W a ≠ ⊥ := by
  have hn : a.comp c.coords.symm.toLinearMap ≠ 0 ↔ a ≠ 0 := by
    constructor
    · rintro ha rfl
      exact ha (LinearMap.zero_comp _)
    · intro ha he
      apply ha
      apply LinearMap.ext
      intro t
      have hh := LinearMap.congr_fun he (c.coords t)
      change a (c.coords.symm (c.coords t)) = 0 at hh
      simpa only [c.coords.symm_apply_apply, LinearMap.zero_apply] using hh
  change (_ ≠ 0 ∧ rootSpace_value c.H _ ≠ ⊥) ↔ _
  rw [hn, and_congr_right_iff]
  intro _
  simp only [Submodule.ne_bot_iff]
  constructor
  · rintro ⟨x, hx, hnx⟩
    refine ⟨(e x).val, (c.weightSpace a x).mp hx, ?_⟩
    intro hz
    exact hnx (e.injective (by
      apply Subtype.ext
      rw [map_zero]
      exact hz))
  · rintro ⟨X, hx, hnx⟩
    let x := e.symm ⟨X, hW a hx⟩
    have he : (e x : Matrix κ κ ℂ) = X :=
      congrArg Subtype.val (e.apply_symm_apply ⟨X, hW a hx⟩)
    refine ⟨x, (c.weightSpace a x).mpr (he.symm ▸ hx), ?_⟩
    intro hz
    exact hnx (by rw [← he, hz, map_zero]; rfl)

private def typeBDiagonalChart (e : L ≃ₗ⁅ℂ⁆ Specs.LieAlgebrasAndRepresentations.ClassicalRootsB.algebra n) :
    MatrixRootChart (Specs.LieAlgebrasAndRepresentations.ClassicalRootsB.algebra n) e (Specs.LieAlgebrasAndRepresentations.ClassicalRootsB.diagonal n) (@Specs.LieAlgebrasAndRepresentations.ClassicalRootsB.weightSpace n) :=
  matrixRootChart (Specs.LieAlgebrasAndRepresentations.ClassicalRootsB.algebra n) e (Specs.LieAlgebrasAndRepresentations.ClassicalRootsB.diagonal n) (fun t p => Specs.LieAlgebrasAndRepresentations.ClassicalRootsB.coordinateWeight p t)
    (@Specs.LieAlgebrasAndRepresentations.ClassicalRootsB.weightSpace n) (fun _ => rfl) (ClassicalRootsB.diagonal_mem n)
    (ClassicalRootsB.diagonal_injective n)
    (fun X hx => by
      rw [ClassicalRootsB.zero_space n] at hx
      obtain ⟨t, ht⟩ := hx
      exact ⟨t, ht.symm⟩)
    (ClassicalRootsB.mem_weightSpace)

private def typeDDiagonal (n : ℕ) : Params n →ₗ[ℂ] Specs.LieAlgebrasAndRepresentations.ClassicalRootsD.Mat n where
  toFun := Specs.LieAlgebrasAndRepresentations.ClassicalRootsD.diagonal n
  map_add' t s := by
    classical
    ext i j
    by_cases hij : i = j
    · subst j
      cases i <;> simp [Specs.LieAlgebrasAndRepresentations.ClassicalRootsD.diagonal, Pi.add_apply, Pi.neg_apply, add_comm]
    · simp [Specs.LieAlgebrasAndRepresentations.ClassicalRootsD.diagonal, Matrix.diagonal_apply_ne _ hij]
  map_smul' c t := by
    classical
    ext i j
    by_cases h : i = j
    · subst j
      cases i <;> simp [Specs.LieAlgebrasAndRepresentations.ClassicalRootsD.diagonal, smul_eq_mul, Pi.smul_apply, Pi.neg_apply]
    · simp [Specs.LieAlgebrasAndRepresentations.ClassicalRootsD.diagonal, Matrix.diagonal_apply_ne _ h]

private def typeDDiagonalChart (e : L ≃ₗ⁅ℂ⁆ Specs.LieAlgebrasAndRepresentations.ClassicalRootsD.algebra n) :
    MatrixRootChart (Specs.LieAlgebrasAndRepresentations.ClassicalRootsD.algebra n) e (typeDDiagonal n) (Specs.LieAlgebrasAndRepresentations.ClassicalRootsD.weightSpace n) :=
  matrixRootChart (Specs.LieAlgebrasAndRepresentations.ClassicalRootsD.algebra n) e (typeDDiagonal n) (fun t => Sum.elim t (-t))
    (Specs.LieAlgebrasAndRepresentations.ClassicalRootsD.weightSpace n) (fun _ => rfl) (fun _ => ClassicalRootsD.diagonal_mem _)
    ClassicalRootsD.diagonal_injective
    (fun X hx => (ClassicalRootsD.zero_space X).mp hx)
    (fun _ _ => Iff.rfl)

end MatrixRootCharts

section RootCoordinates

open Module
open LieAlgebrasAndRepresentations.ClassicalCoordinates
open Specs.LieAlgebrasAndRepresentations.RootDecomposition
open Specs.LieAlgebrasAndRepresentations.RootForm
open Specs.LieAlgebrasAndRepresentations.SerreRelations (positive simple)
open Specs.LieAlgebrasAndRepresentations.VermaModules (Direction Regular)
open Specs.LieAlgebrasAndRepresentations.AutomorphismDecomposition (diagramAutomorphisms)
open Specs.LieAlgebrasAndRepresentations.MaximalTori (IsMaximalToral_value)
open Specs.LieAlgebrasAndRepresentations.SolvableRadical (IsSemisimple_value)
open Specs.LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient (Normalized)

variable {n : ℕ}

private def coordinateWeight (n : ℕ) : Space n →ₗ[ℝ] Weight n where
  toFun v := ∑ i, (v i : ℂ) • (LinearMap.proj i : Weight n)
  map_add' u v := by
    apply LinearMap.ext
    intro t
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, PiLp.add_apply, ofReal_add, smul_eq_mul, add_mul,
      Finset.sum_add_distrib]
  map_smul' a v := by
    apply LinearMap.ext
    intro t
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
      PiLp.smul_apply, smul_eq_mul, ofReal_mul, RingHom.id_apply,
      Complex.real_smul, Finset.mul_sum, mul_assoc]

private theorem coordinateWeight_epsilon (i : Fin n) :
    coordinateWeight n (epsilon i) = LinearMap.proj i := by
  classical
  apply LinearMap.ext
  intro t
  change (∑ j, (epsilon i j : ℂ) • (LinearMap.proj j : Weight n)) t = t i
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.proj_apply]
  simp [epsilon_apply, apply_ite (fun z : ℝ => (z : ℂ)), ite_mul]

private theorem coordinateWeight_injective (n : ℕ) :
    Function.Injective (coordinateWeight n) := by
  classical
  intro x y h
  ext i
  have he := LinearMap.congr_fun h (Pi.single i 1)
  change (∑ j, (x j : ℂ) • (LinearMap.proj j : Weight n)) (Pi.single i 1) =
    (∑ j, (y j : ℂ) • (LinearMap.proj j : Weight n)) (Pi.single i 1) at he
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.proj_apply] at he
  exact ofReal_inj.mp (by simpa [Pi.single_apply, mul_ite] using he)

private theorem coordinateWeight_real_eval (u v : Space n) :
    (coordinateWeight n v (fun i => (u i : ℂ))).re = inner ℝ u v := by
  change ((∑ i, (v i : ℂ) • (LinearMap.proj i : Weight n)) (fun i => (u i : ℂ))).re = _
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.proj_apply]
  rw [show (∑ i, (v i : ℂ) * (u i : ℂ)) = ((∑ i, (v i * u i) : ℝ) : ℂ) by simp]
  rw [Complex.ofReal_re, PiLp.inner_apply]
  simp [RCLike.inner_apply, mul_comm]

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {S : LieSubalgebra ℂ (Matrix κ κ ℂ)} {e : L ≃ₗ⁅ℂ⁆ S}
variable {d : Params n →ₗ[ℂ] Matrix κ κ ℂ} {W : Weight n → Submodule ℂ (Matrix κ κ ℂ)}

private def rootChartMap (c : MatrixRootChart S e d W) : Space n →ₗ[ℝ] Dual ℂ c.H :=
  ((LinearMap.llcomp ℂ c.H (Params n) ℂ).flip c.coords.symm.toLinearMap).restrictScalars ℝ ∘ₗ
    coordinateWeight n

private theorem rootChartMap_apply (c : MatrixRootChart S e d W) (x : Space n) :
    rootChartMap c x = (coordinateWeight n x).comp c.coords.symm.toLinearMap := rfl

private theorem rootChartMap_injective (c : MatrixRootChart S e d W) :
    Function.Injective (rootChartMap c) := by
  intro x y h
  apply coordinateWeight_injective n
  apply LinearMap.ext
  intro t
  have ht := LinearMap.congr_fun h (c.coords t)
  rw [rootChartMap_apply, rootChartMap_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, c.coords.symm_apply_apply] at ht
  exact ht

private def chartDirection (c : MatrixRootChart S e d W) (v : Space n) : Direction c.H :=
  Complex.reLm.comp ((Module.Dual.eval ℂ c.H (c.coords (fun i => (v i : ℂ)))).restrictScalars ℝ)

private theorem chartDirection_apply (c : MatrixRootChart S e d W) (v x : Space n) :
    chartDirection c v (rootChartMap c x) = inner ℝ v x := by
  simpa [chartDirection, rootChartMap_apply] using coordinateWeight_real_eval v x

private theorem chart_regular (c : MatrixRootChart S e d W)
    (R : Set (Space n)) (hroot : rootChartMap c '' R = rootSet_value c.H)
    (v : Space n) (hv : RootRegular R v) : Regular c.H (chartDirection c v) := by
  intro a ha
  rw [← hroot] at ha
  obtain ⟨x, hx, rfl⟩ := ha
  simpa [chartDirection_apply] using hv x hx

private theorem chart_simple_image (c : MatrixRootChart S e d W)
    (R : Set (Space n)) (hroot : rootChartMap c '' R = rootSet_value c.H) (v : Space n) :
    rootChartMap c '' simpleRoots R v = simple c.H (chartDirection c v) := by
  let J := rootChartMap c
  have hJ := rootChartMap_injective c
  have hpos : J '' positiveRoots R v = positive c.H (chartDirection c v) := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hroot ▸ ⟨x, hx.1, rfl⟩, by simpa [J, chartDirection_apply] using hx.2⟩
    · intro ha
      have har := ha.1
      rw [← hroot] at har
      obtain ⟨x, hx, rfl⟩ := har
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      exact (chartDirection_apply c v x) ▸ ha.2
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨hpos ▸ ⟨x, hx.1, rfl⟩, ?_⟩
    intro b hb z hz he
    rw [← hpos] at hb hz
    obtain ⟨y, hy, rfl⟩ := hb
    obtain ⟨w, hw, rfl⟩ := hz
    exact hx.2 y hy w hw (hJ (he.trans (map_add J _ _).symm))
  · intro ha
    have hap := ha.1
    rw [← hpos] at hap
    obtain ⟨x, hx, rfl⟩ := hap
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro y hy z hz he
    exact ha.2 (J y) (hpos ▸ ⟨y, hy, rfl⟩) (J z) (hpos ▸ ⟨z, hz, rfl⟩)
      ((congrArg J he).trans (map_add J _ _))

private theorem simpleB_coordinate_basis (n : ℕ) :
    ∃ b : Basis (Fin n) ℝ (Space n), (∀ i, b i = simpleB n i) ∧
      IsSimpleBasis (rootsB n) (regularBCD n 0) b := by
  have hR : IsRootSystem (rootsB n) :=
    ⟨union_axis_pair_axioms n (Or.inl rfl), union_axis_pair_span n (by norm_num)⟩
  apply simple_basis_of_span _ hR _ (regularB_regular n)
  · intro i
    exact simple_of_height_one
      (fun _ ha => union_height_separated (Or.inl ⟨rfl, rfl⟩) ha)
      (simpleB_mem n i) (simpleB_height n i)
  · exact simpleB_span n

private theorem simpleD_coordinate_mem (hn : 3 ≤ n) (i : Fin n) :
    simpleD n i ∈ rootsD n := by
  unfold simpleD
  split_ifs with h
  · exact ⟨i, ⟨i.val+1,h⟩, by simp [Fin.ext_iff], false, true, by simp [sign, sub_eq_add_neg]⟩
  · exact ⟨⟨n-2,by have := i.isLt; omega⟩, i, by
      apply Fin.ne_of_val_ne
      change n-2 ≠ i.val
      have := i.isLt
      omega, false, false, by simp [sign]⟩

private theorem simpleD_coordinate_basis (n : ℕ) (hn : 3 ≤ n) :
    ∃ b : Basis (Fin n) ℝ (Space n), (∀ i, b i = simpleD n i) ∧
      IsSimpleBasis (rootsD n) (regularBCD n 1) b := by
  by_cases hn4 : 4 ≤ n
  · exact simpleD_basis n hn4
  have hn3 : n = 3 := by omega
  subst n
  have hR : IsRootSystem (rootsD 3) := ⟨pairRoots_axioms 3, pairRoots_span 3 (by decide)⟩
  apply simple_basis_of_span _ hR _ (regularD_regular 3)
  · intro i
    apply simple_of_height_one (fun _ ha => pair_height_separated (by norm_num) (by norm_num) ha)
      (simpleD_coordinate_mem (by decide) i)
    fin_cases i <;>
      norm_num [simpleD, inner_sub_right, inner_add_right, inner_epsilon_right,
        regularBCD, Fin.val_last]
  · let M := Submodule.span ℝ (Set.range (simpleD 3))
    have hm : epsilon (1 : Fin 3) - epsilon (2 : Fin 3) ∈ M := by
      simpa [M, simpleD] using
        Submodule.subset_span (R := ℝ) (Set.mem_range_self (f := simpleD 3) 1)
    have hp : epsilon (1 : Fin 3) + epsilon (2 : Fin 3) ∈ M := by
      simpa [M, simpleD] using
        Submodule.subset_span (R := ℝ) (Set.mem_range_self (f := simpleD 3) 2)
    have heq : (1/2 : ℝ) • ((epsilon (1 : Fin 3) + epsilon (2 : Fin 3)) -
        (epsilon (1 : Fin 3) - epsilon (2 : Fin 3))) = epsilon (2 : Fin 3) := by module
    have he : epsilon (2 : Fin 3) ∈ M := heq ▸ M.smul_mem _ (M.sub_mem hp hm)
    apply submodule_eq_top_of_adjacent
    · intro i hi
      have hib : i = 2 := Fin.ext (by have := i.isLt; omega)
      simpa [hib] using he
    · intro i hi
      simpa [simpleD, hi] using
        Submodule.subset_span (R := ℝ) (Set.mem_range_self (f := simpleD 3) i)

private def simpleChartEquiv (c : MatrixRootChart S e d W)
    (R : Set (Space n)) (hroot : rootChartMap c '' R = rootSet_value c.H)
    (v : Space n) (b : Basis (Fin n) ℝ (Space n)) (hb : IsSimpleBasis R v b) :
    Fin n ≃ simple c.H (chartDirection c v) := by
  let s := rootChartMap c ∘ b
  have hr : Set.range s = simple c.H (chartDirection c v) := by
    rw [Set.range_comp, hb, chart_simple_image c R hroot v]
  exact (Equiv.ofInjective s ((rootChartMap_injective c).comp b.injective)).trans
    (Set.equivOfEq hr)

private theorem diagram_quotient {L : Type u} [LieRing L] [LieAlgebra ℂ L]
    [FiniteDimensional ℂ L] (hss : IsSemisimple_value ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral_value H)
    (φ : Direction H) (hφ : Regular H φ) :
    ∃ h : (innerAut L).Normal,
      letI := h
      Nonempty ((Aut L ⧸ innerAut L) ≃* diagramAutomorphisms H φ) := by
  have ht (i : simple H φ) := exists_root_triple hss H hH i.val i.property.1.1
  choose e f he hf hne hnf hbr _ _ using ht
  have hn : Normalized H φ e f := fun i => ⟨he i, hf i, hne i, hnf i, hbr i⟩
  obtain ⟨h, s, _, hmem, hbij⟩ := AutomorphismDecomposition.decomposition hss H hH φ hφ e f hn
  letI := h
  let q := QuotientGroup.mk' (innerAut L)
  let m := q.comp s
  have hm : Function.Bijective m := by
    constructor
    · apply (injective_iff_map_eq_one m).mpr
      intro p hp
      exact (hmem p).mp ((QuotientGroup.eq_one_iff _).mp hp)
    · intro c
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ c
      obtain ⟨⟨x, p⟩, rfl⟩ := hbij.2 a
      refine ⟨p, ?_⟩
      change q (s p) = q (x.val * s p)
      have hx : q x.val = 1 := (QuotientGroup.eq_one_iff x.val).mpr x.property
      rw [q.map_mul, hx, one_mul]
  exact ⟨h, ⟨(MulEquiv.ofBijective m hm).symm⟩⟩

private theorem coordinate_pair_roots (a : Weight n) :
    a ∈ coordinateWeight n '' pairRoots n ↔
      ∃ i j : Fin n, i < j ∧
        (a = (LinearMap.proj i : Weight n) + LinearMap.proj j ∨
         a = (LinearMap.proj i : Weight n) - LinearMap.proj j ∨
         a = -(LinearMap.proj i : Weight n) + LinearMap.proj j ∨
         a = -(LinearMap.proj i : Weight n) - LinearMap.proj j) := by
  have aux (i j : Fin n) :
      (∃ s t : Bool, a = coordinateWeight n (sign s • epsilon i + sign t • epsilon j)) ↔
        (a = (LinearMap.proj i : Weight n) + LinearMap.proj j ∨
         a = (LinearMap.proj i : Weight n) - LinearMap.proj j ∨
         a = -(LinearMap.proj i : Weight n) + LinearMap.proj j ∨
         a = -(LinearMap.proj i : Weight n) - LinearMap.proj j) := by
    simp only [Bool.exists_bool, sign, Bool.false_eq_true, ↓reduceIte, one_smul,
      neg_smul, map_add, map_neg, coordinateWeight_epsilon, sub_eq_add_neg, or_assoc]
  constructor
  · rintro ⟨_, ⟨i, j, hij, s, t, rfl⟩, rfl⟩
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i, j, h, (aux i j).mp ⟨s, t, rfl⟩⟩
    · exact ⟨j, i, h, (aux j i).mp ⟨t, s, by rw [add_comm]⟩⟩
  · rintro ⟨i, j, lij, ha⟩
    obtain ⟨s,t,rfl⟩ := (aux i j).mpr ha
    exact ⟨_, ⟨i,j,ne_of_lt lij,s,t,rfl⟩, rfl⟩

private theorem coordinate_axis_roots (a : Weight n) :
    a ∈ coordinateWeight n '' axisRoots n 1 ↔
      ∃ i : Fin n, a = LinearMap.proj i ∨ a = -LinearMap.proj i := by
  constructor
  · rintro ⟨_, ⟨i, s, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    cases s <;> simp [sign, coordinateWeight_epsilon]
  · rintro ⟨i, rfl | rfl⟩
    · exact ⟨epsilon i, ⟨i, false, by simp [sign]⟩, coordinateWeight_epsilon i⟩
    · exact ⟨-epsilon i, ⟨i, true, by simp [sign]⟩, by simp [coordinateWeight_epsilon]⟩

private theorem chart_roots_eq_image (c : MatrixRootChart S e d W)
    (hW : ∀ a, W a ≤ S.toSubmodule) (R : Set (Space n))
    (hr : ∀ a : Weight n, a ∈ coordinateWeight n '' R ↔ a ≠ 0 ∧ W a ≠ ⊥) :
    rootChartMap c '' R = rootSet_value c.H := by
  ext α
  let a : Weight n := α.comp c.coords.toLinearMap
  have he : a.comp c.coords.symm.toLinearMap = α := by
    ext h
    change α (c.coords (c.coords.symm h)) = α h
    rw [c.coords.apply_symm_apply]
  rw [← he, chart_root_mem c hW a, ← hr]
  constructor
  · rintro ⟨x,hx,h⟩
    have hh : coordinateWeight n x = a := by
      apply LinearMap.ext
      intro t
      have hx := LinearMap.congr_fun h (c.coords t)
      change coordinateWeight n x (c.coords.symm (c.coords t)) =
        a (c.coords.symm (c.coords t)) at hx
      simpa only [c.coords.symm_apply_apply] using hx
    exact ⟨x,hx,hh⟩
  · rintro ⟨x, hx, hh⟩
    exact ⟨x, hx, by rw [rootChartMap_apply, hh]⟩

private theorem typeB_chart_roots (e : L ≃ₗ⁅ℂ⁆ Specs.LieAlgebrasAndRepresentations.ClassicalRootsB.algebra n) :
    rootChartMap (typeBDiagonalChart e) '' rootsB n = rootSet_value (typeBDiagonalChart e).H := by
  apply chart_roots_eq_image
  · intro a X hx
    exact ((ClassicalRootsB.mem_weightSpace a X).mp hx).1
  · intro a
    change (_ : Prop) ↔ a ∈ Specs.LieAlgebrasAndRepresentations.ClassicalRootsB.roots n
    rw [ClassicalRootsB.roots_eq n, rootsB, Set.image_union, Set.mem_union,
      coordinate_axis_roots, coordinate_pair_roots]
    rfl

private theorem typeD_chart_roots (e : L ≃ₗ⁅ℂ⁆ Specs.LieAlgebrasAndRepresentations.ClassicalRootsD.algebra n) :
    rootChartMap (typeDDiagonalChart e) '' rootsD n = rootSet_value (typeDDiagonalChart e).H := by
  apply chart_roots_eq_image
  · intro a X hx
    exact hx.1
  · intro a
    change (_ : Prop) ↔ a ∈ Specs.LieAlgebrasAndRepresentations.ClassicalRootsD.roots n
    rw [ClassicalRootsD.roots_ordered, rootsD, coordinate_pair_roots]
    simp only [Specs.LieAlgebrasAndRepresentations.ClassicalRootsD.epsilon, neg_sub, neg_add,
      sub_eq_add_neg, neg_neg, add_comm, or_comm, or_left_comm, or_assoc]

/-- Both reflections preserve the finite root set. On a line parallel to
the root their composite is a translation, so its displacement is zero. -/
private theorem chart_cartan [FiniteDimensional ℂ L] (hss : IsSemisimple_value ℂ L)
    (c : MatrixRootChart S e d W) {R : Set (Space n)} (hR : RootAxioms R)
    (hroot : rootChartMap c '' R = rootSet_value c.H)
    {a b : Space n} (ha : a ∈ R) (hb : b ∈ R) :
    rootChartMap c b (coroot_value c.H (rootChartMap c a)) =
      (rootCartan b a : ℂ) := by
  let J := rootChartMap c
  let h := coroot_value c.H (J a)
  have hj (x : Space n) (hx : x ∈ R) : J x ∈ rootSet_value c.H :=
    hroot ▸ Set.mem_image_of_mem J hx
  have hreal (x : Space n) (hx : x ∈ R) : ((J x h).re : ℂ) = J x h := by
    obtain ⟨z, hz, _⟩ := RootStrings.coroot_pairing_integral hss c.H c.maximal
      (J a) (J x) (hj a ha) (hj x hx)
    change J x h = _ at hz
    simp [hz]
  let f : Space n →ₗ[ℝ] ℝ := Complex.reLm.comp
    ((Module.Dual.eval ℂ c.H h).restrictScalars ℝ ∘ₗ J)
  let g : Space n →ₗ[ℝ] ℝ :=
    (2 / inner ℝ a a) • (innerSL ℝ a).toLinearMap
  have hf (x : Space n) : f x = (J x h).re := rfl
  have hg (x : Space n) : g x = rootCartan x a := by
    simp only [g, LinearMap.smul_apply, ContinuousLinearMap.coe_coe, innerSL_apply_apply, smul_eq_mul, rootCartan]
    rw [real_inner_comm a x]
    ring
  have hfa : f a = 2 := by
    obtain ⟨x, y, hx, _, hne, _, _, hbr, _⟩ :=
      exists_root_triple hss c.H c.maximal (J a) (hj a ha)
    have he := (mem_rootSpace c.H (J a) x).mp hx h
    change ⁅(h : L), x⁆ = J a h • x at he
    have hv := smul_left_injective ℂ hne (he.symm.trans hbr)
    simp [hf, hv]
  have hga : g a = 2 := by
    rw [hg, rootCartan, mul_div_cancel_right₀]
    exact (real_inner_self_pos.mpr (hR.nonzero a ha)).ne'
  have hF (x : Space n) (hx : x ∈ R) : x - f x • a ∈ R := by
    have hr := RootStrings.reflection_mem_rootSet hss c.H c.maximal (J a) (J x)
      (hj a ha) (hj x hx)
    change J x - J x h • J a ∈ rootSet_value c.H at hr
    rw [← hroot] at hr
    obtain ⟨y, hy, hey⟩ := hr
    have he : J y = J (x - f x • a) := by
      rw [hey, map_sub, map_smul, hf]
      change J x - J x h • J a = J x - (((J x h).re : ℝ) : ℂ) • J a
      rw [hreal x hx]
    rw [← rootChartMap_injective c he]
    exact hy
  have hG (x : Space n) (hx : x ∈ R) : x - g x • a ∈ R := by
    rw [hg]
    exact hR.reflection_mem a ha x hx
  let k := f b - g b
  have hstep (s : ℝ) (hs : b + s • a ∈ R) : b + (s + k) • a ∈ R := by
    have hc := hG _ (hF _ hs)
    have her (x : Space n) :
        (x - f x • a) - g (x - f x • a) • a = x + (f x - g x) • a := by
      rw [map_sub, map_smul, hga, smul_eq_mul]
      module
    rw [her, map_add, map_add, map_smul, map_smul, hfa, hga, smul_eq_mul] at hc
    have hk : f b + s * 2 - (g b + s * 2) = k := by dsimp [k]; ring
    simpa only [hk, add_assoc, ← add_smul] using hc
  have horbit (m : ℕ) : b + ((m : ℝ) * k) • a ∈ R := by
    induction m with
    | zero => simpa using hb
    | succ m ih =>
      simpa only [Nat.cast_succ, add_mul, one_mul] using hstep _ ih
  have hk : k = 0 := by
    by_contra hk
    let z (m : ℕ) : R := ⟨_, horbit m⟩
    have hz : Function.Injective z := by
      intro m l he
      have he' : b + ((m : ℝ) * k) • a = b + ((l : ℝ) * k) • a :=
        congrArg Subtype.val he
      exact_mod_cast mul_right_cancel₀ hk
        (smul_left_injective ℝ (hR.nonzero a ha) (add_left_cancel he'))
    letI := hR.finite.to_subtype
    haveI := Finite.of_injective z hz
    exact not_finite ℕ
  have heq : f b = g b := sub_eq_zero.mp hk
  change J b h = _
  rw [← hreal b hb, ← hf, heq, hg]

private theorem chart_diagram_values [FiniteDimensional ℂ L] (hss : IsSemisimple_value ℂ L)
    (c : MatrixRootChart S e d W) (R : Set (Space n)) (hR : IsRootSystem R)
    (hroot : rootChartMap c '' R = rootSet_value c.H)
    (v : Space n) (b : Basis (Fin n) ℝ (Space n)) (hb : IsSimpleBasis R v b)
    (i j : Fin n) :
    let k := simpleChartEquiv c R hroot v b hb
    (k j).val (coroot_value c.H (k i).val) = (cartanMatrix b i j : ℂ) := by
  dsimp only
  change rootChartMap c (b j) (coroot_value c.H (rootChartMap c (b i))) = _
  have hmem (k : Fin n) : b k ∈ R := by
    have ht : b k ∈ simpleRoots R v := hb ▸ Set.mem_range_self k
    exact ht.1.1
  exact chart_cartan hss c hR.toRootAxioms hroot (hmem i) (hmem j)

private theorem chart_diagram_transport [FiniteDimensional ℂ L] (hss : IsSemisimple_value ℂ L)
    (c : MatrixRootChart S e d W) (R : Set (Space n)) (hR : IsRootSystem R)
    (hroot : rootChartMap c '' R = rootSet_value c.H)
    (v : Space n) (b : Basis (Fin n) ℝ (Space n)) (hb : IsSimpleBasis R v b)
    (p : Equiv.Perm (Fin n)) :
    let k := simpleChartEquiv c R hroot v b hb
    k.permCongr p ∈ diagramAutomorphisms c.H (chartDirection c v) ↔
      ∀ i j, cartanMatrix b (p i) (p j) = cartanMatrix b i j := by
  intro k
  let hv := chart_diagram_values hss c R hR hroot v b hb
  change (∀ i j : simple c.H (chartDirection c v),
    ((k.permCongr p) j).val (coroot_value c.H ((k.permCongr p) i).val) =
       j.val (coroot_value c.H i.val)) ↔ _
  constructor
  · intro h i j
    have ht := h (k i) (k j)
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply] at ht
    exact Complex.ofReal_injective ((hv (p i) (p j)).symm.trans (ht.trans (hv i j)))
  · intro h i j
    obtain ⟨i, rfl⟩ := k.surjective i
    obtain ⟨j, rfl⟩ := k.surjective j
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    rw [hv, hv, h]

private theorem chart_B_quotient [FiniteDimensional ℂ L] (hss : IsSemisimple_value ℂ L)
    (e : L ≃ₗ⁅ℂ⁆ Specs.LieAlgebrasAndRepresentations.ClassicalRootsB.algebra n) :
    ∃ h : (innerAut L).Normal, letI := h; Subsingleton (Aut L ⧸ innerAut L) := by
  classical
  let c := typeBDiagonalChart e
  let v := regularBCD n 0
  have hR : IsRootSystem (rootsB n) :=
    ⟨union_axis_pair_axioms n (Or.inl rfl), union_axis_pair_span n (by norm_num)⟩
  have hr := regularB_regular n
  obtain ⟨b, hb, hsb⟩ := simpleB_coordinate_basis n
  have hroot := typeB_chart_roots e
  let k := simpleChartEquiv c (rootsB n) hroot v b hsb
  obtain ⟨h, ⟨q⟩⟩ := diagram_quotient hss c.H c.maximal (chartDirection c v)
    (chart_regular c _ hroot v hr)
  letI := h
  refine ⟨h, ⟨fun x y => ?_⟩⟩
  have htriv (p : diagramAutomorphisms c.H (chartDirection c v)) : p.val = 1 := by
    let t := k.symm.permCongr p.val
    have hp : k.permCongr t = p.val := by ext i; simp [t, Equiv.permCongr_apply]
    have ht := (chart_diagram_transport hss c _ hR hroot v b hsb t).mp (hp.symm ▸ p.property)
    have htb (i j : Fin n) : cartanMatrix (simpleB n) (t i) (t j) =
        cartanMatrix (simpleB n) i j := by simpa only [cartanMatrix, ← hb] using ht i j
    have ht1 : t = 1 := by
      apply b_diagram_trivial n t
      · intro i j
        simp [dynkinDiagram, t.injective.eq_iff, htb]
      · intro i j
        have hfun : (b : Fin n → Space n) = simpleB n := funext hb
        rw [← hfun]
        by_cases hij : i = j
        · simp [hij, dynkinDiagram]
        · rw [dynkin_arrow_iff_cartan_lt hR hr hsb (t.injective.ne hij),
            dynkin_arrow_iff_cartan_lt hR hr hsb hij, ht, ht]
    rw [← hp, ht1]
    ext i
    simp [Equiv.permCongr_apply]
  exact q.injective (Subtype.ext ((htriv (q x)).trans (htriv (q y)).symm))

private theorem simpleD_gram_all (hn : 3 ≤ n) (i j : Fin n) :
    inner ℝ (simpleD n i) (simpleD n j) =
      if i = j then 2 else if forkAdjacent i j then -1 else 0 := by
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    exact pairRoots_inner_self (simpleD_coordinate_mem hn i)
  · rw [ite_eq_right hij]
    have hv := Fin.val_ne_of_ne hij
    have hi := i.isLt
    have hj := j.isLt
    unfold simpleD forkAdjacent
    split_ifs <;>
      simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
        inner_epsilon_left, epsilon_apply, Fin.ext_iff] <;>
      split_ifs <;> norm_num <;> omega

private theorem simpleD_cartan (hn : 3 ≤ n) (i j : Fin n) :
    cartanMatrix (simpleD n) i j = if i = j then 2 else if forkAdjacent i j then -1 else 0 := by
  have hs : inner ℝ (simpleD n j) (simpleD n i) =
      inner ℝ (simpleD n i) (simpleD n j) := real_inner_comm _ _
  rw [cartanMatrix, rootCartan, hs, simpleD_gram_all hn i j, simpleD_gram_all hn i i, ite_eq_left rfl]
  split_ifs <;> norm_num

private theorem chart_D_quotient [FiniteDimensional ℂ L] (hss : IsSemisimple_value ℂ L)
    (e : L ≃ₗ⁅ℂ⁆ Specs.LieAlgebrasAndRepresentations.ClassicalRootsD.algebra n) (hn : 3 ≤ n) :
    ∃ h : (innerAut L).Normal, letI := h;
      Nonempty ((Aut L ⧸ innerAut L) ≃* Equiv.Perm (Fin (if n = 4 then 3 else 2))) := by
  classical
  let c := typeDDiagonalChart e
  let v := regularBCD n 1
  have hR : IsRootSystem (rootsD n) := ⟨pairRoots_axioms n, pairRoots_span n (by omega)⟩
  obtain ⟨b, hb, hsb⟩ := simpleD_coordinate_basis n hn
  have hroot := typeD_chart_roots e
  let k := simpleChartEquiv c (rootsD n) hroot v b hsb
  obtain ⟨h, ⟨q⟩⟩ := diagram_quotient hss c.H c.maximal (chartDirection c v)
    (chart_regular c _ hroot v (regularD_regular n))
  letI := h
  have hGrp : ∀ p : Equiv.Perm (Fin n), p ∈ forkGroup n ↔
      k.permCongr p ∈ diagramAutomorphisms c.H (chartDirection c v) := by
    intro p
    have ht :
        k.permCongr p ∈ diagramAutomorphisms c.H (chartDirection c v) ↔
          ∀ i j, cartanMatrix b (p i) (p j) = cartanMatrix b i j :=
      chart_diagram_transport hss c _ hR hroot v b hsb p
    rw [ht]
    have hCb (i j : Fin n) :
        cartanMatrix b i j = if i = j then 2 else if forkAdjacent i j then -1 else 0 := by
      simpa only [cartanMatrix, hb] using simpleD_cartan hn i j
    change (∀ i j, forkAdjacent (p i) (p j) ↔ forkAdjacent i j) ↔ _
    constructor
    · intro hp i j
      simp only [hCb, p.injective.eq_iff, hp]
    · intro hp i j
      by_cases hij : i = j
      · subst j
        have hne (z : Fin n) : ¬ forkAdjacent z z := by
          unfold forkAdjacent
          omega
        simp [hne]
      have he := hp i j
      rw [hCb, hCb, ite_eq_right (p.injective.ne hij), ite_eq_right hij] at he
      by_cases h₁ : forkAdjacent (p i) (p j) <;>
        by_cases h₂ : forkAdjacent i j <;> norm_num [h₁, h₂] at *
  let p := k.permCongrHom
  let E : forkGroup n ≃* diagramAutomorphisms c.H (chartDirection c v) := by
    refine (p.subgroupMap (forkGroup n)).trans (MulEquiv.subgroupCongr ?_)
    ext x
    change (∃ y ∈ forkGroup n, k.permCongr y = x) ↔ _
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hGrp y).mp hy
    · intro hx
      obtain ⟨y, rfl⟩ := p.surjective x
      exact ⟨y, (hGrp y).mpr hx, rfl⟩
  obtain ⟨iso⟩ := fork_group_iso n hn
  exact ⟨h, ⟨q.trans (E.symm.trans iso)⟩⟩

end RootCoordinates

section MatrixForms

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

private def reindexSo (e : ι ≃ κ) : Orthogonal.so ι ℂ ≃ₗ⁅ℂ⁆ Orthogonal.so κ ℂ := by
  let E := Matrix.reindexAlgEquiv ℂ ℂ e
  have h (X : Matrix ι ι ℂ) : (E X)ᵀ = E Xᵀ := Matrix.transpose_reindex _ _ _
  refine LieEquiv.ofSubalgebras _ _ E.toLieEquiv ?_
  ext X
  rw [LieSubalgebra.mem_map, Orthogonal.mem_so]
  constructor
  · rintro ⟨Y, hY, rfl⟩
    change (E Y)ᵀ = -E Y
    rw [h, (Orthogonal.mem_so _ _ _).mp hY, map_neg]
  · intro hX
    refine ⟨E.symm X, (Orthogonal.mem_so _ _ _).mpr ?_, E.apply_symm_apply X⟩
    apply E.injective
    rw [← h, map_neg, E.apply_symm_apply, hX]

private def symmetricInvolutionSo (J : Matrix κ κ ℂ) (hJ : Jᵀ = J) (hJJ : J * J = 1) :
    skewAdjointMatricesLieSubalgebra J ≃ₗ⁅ℂ⁆ Orthogonal.so κ ℂ := by
  let a : ℂ := (1 + Complex.I) / 2
  let b : ℂ := (1 - Complex.I) / 2
  have ha : a * a + b * b = 0 := by
    dsimp [a,b]
    linear_combination (1/2 : ℂ) * Complex.I_sq
  have hb : a * b + b * a = 1 := by
    dsimp [a,b]
    linear_combination (-1/2 : ℂ) * Complex.I_sq
  let P := a • (1 : Matrix κ κ ℂ) + b • J
  have hp : P * P = J := by
    change (a • 1 + b • J) * (a • 1 + b • J) = J
    simp only [mul_add, add_mul, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one,
      hJJ, smul_smul]
    rw [show (a * a) • (1 : Matrix κ κ ℂ) + (a * b) • J +
       ((b * a) • J + (b * b) • (1 : Matrix κ κ ℂ)) =
      ((a * a) • (1 : Matrix κ κ ℂ) + (b * b) • (1 : Matrix κ κ ℂ)) +
        ((a * b) • J + (b * a) • J) by abel,
      ← add_smul, ← add_smul, ha, hb, zero_smul, one_smul, zero_add]
  have hpt : Pᵀ = P := by simp [P, hJ]
  have hP : P * (P * J) = 1 := by rw [← mul_assoc, hp, hJJ]
  have hPJ : Pᵀ * J * P = 1 := by
    calc
      _ = P * (P * P) * P := by rw [hpt, hp]
      _ = (P * P) * (P * P) := by noncomm_ring
      _ = 1 := by rw [hp, hJJ]
  exact (skewAdjointMatricesLieSubalgebraEquiv J P
    (invertibleOfRightInverse _ _ hP)).trans
      (LieEquiv.ofEq _ _ (by rw [hPJ]; rfl))

end MatrixForms

section ReflectionDeterminant

open Module

private theorem skew_entry {α : Type*} [DecidableEq α] [Fintype α] (X : so α) (i k : α) :
      X.val k i = -X.val i k :=
  congrArg (fun M : Matrix α α ℂ => M i k) ((Orthogonal.mem_so _ _ _).mp X.property)

private def skewCoordinates {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ι) :
    so ι ≃ₗ[ℂ] (({i : ι // i ≠ j} → ℂ) × so {i : ι // i ≠ j}) := by
  let K := {i : ι // i ≠ j}
  let cut (X : so ι) : so K :=
    ⟨fun i k => X.val i k, (Orthogonal.mem_so _ _ _).mpr
      (Matrix.ext fun i k => by exact skew_entry X (i : ι) (k : ι))⟩
  let f : so ι →ₗ[ℂ] ((K → ℂ) × so K) :=
    { toFun := fun X => (fun i => X.val j i, cut X)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply LinearEquiv.ofBijective f
  constructor
  · intro X Y h
    have h1 (i : K) : X.val j i = Y.val j i :=
      congrArg (fun z : (K → ℂ) × so K => z.1 i) h
    have h2 (i k : K) : X.val i k = Y.val i k :=
      congrArg (fun z : (K → ℂ) × so K => z.2.val i k) h
    apply Subtype.ext
    ext i k
    by_cases hi : i = j
    · subst i
      by_cases hk : k = j
      · subst k
        have hx := skew_entry X j j
        have hy := skew_entry Y j j
        linear_combination (1/2 : ℂ) * hx - (1/2 : ℂ) * hy
      · exact h1 ⟨k, hk⟩
    · by_cases hk : k = j
      · subst k
        rw [skew_entry X j i, skew_entry Y j i, h1 ⟨i, hi⟩]
      · exact h2 ⟨i, hi⟩ ⟨k, hk⟩
  · rintro ⟨v, X⟩
    let Y : Matrix ι ι ℂ := fun i k =>
      if hi : i = j then
        if hk : k = j then 0 else v ⟨k, hk⟩
      else if hk : k = j then -v ⟨i, hi⟩ else X.val ⟨i, hi⟩ ⟨k, hk⟩
    have hy : Y ∈ so ι := by
      rw [Orthogonal.mem_so]
      ext i k
      change Y k i = -Y i k
      by_cases hi : i = j <;> by_cases hk : k = j <;>
        simp [Y, hi, hk]
      exact skew_entry X ⟨i, hi⟩ ⟨k, hk⟩
    refine ⟨⟨Y, hy⟩, Prod.ext ?_ ?_⟩
    · funext i
      change Y j i = v i
      simp [Y, i.property]
    · apply Subtype.ext
      ext i k
      change Y i k = X.val i k
      simp [Y, i.property, k.property]

private theorem skewCoordinates_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j : ι) (X : so ι) : (skewCoordinates j X).1 = fun i : {i : ι // i ≠ j} => X.val j i := rfl

private theorem skewCoordinates_apply_snd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j : ι) (X : so ι) (i k : {i : ι // i ≠ j}) :
      (skewCoordinates j X).2.val i k = X.val i k := rfl

private theorem reflectionDet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j : ι) (a : so ι ≃ₗ⁅ℂ⁆ so ι)
    (ha : ∀ X : so ι, (a X).val =
       diagonal (fun i => if i = j then (-1 : ℂ) else 1) *
       X.val * diagonal (fun i => if i = j then (-1 : ℂ) else 1)) :
    LinearMap.det a.toLinearMap = (-1 : ℂ) ^ (Fintype.card ι - 1) := by
  let K := {i : ι // i ≠ j}
  let E := skewCoordinates j
  let f : Module.End ℂ (K → ℂ) := (-1 : ℂ) • 1
  let g : Module.End ℂ (so K) := 1
  have hc : E.toLinearMap ∘ₗ a.toLinearMap ∘ₗ E.symm.toLinearMap =
      LinearMap.prodMap f g := by
    apply LinearMap.ext
    intro x
    obtain ⟨X, rfl⟩ := E.surjective x
    change E (a (E.symm (E X))) = (f ((E X).1), g ((E X).2))
    rw [E.symm_apply_apply]
    have he (i k : ι) : (a X).val i k =
        (if i = j then (-1 : ℂ) else 1) * X.val i k *
          (if k = j then (-1 : ℂ) else 1) := by
      rw [ha, mul_diagonal, diagonal_mul]
    apply Prod.ext
    · funext i
      show (E (a X)).1 i = f (E X).1 i
      rw [show f (E X).1 i = -(E X).1 i by simp [f]]
      simp [E, skewCoordinates_apply, he, i.property]
    · apply Subtype.ext
      ext i k
      change (E (a X)).2.val i k = (E X).2.val i k
      simp [E, skewCoordinates_apply_snd, he, i.property, k.property]
  have hK : Fintype.card K = Fintype.card ι - 1 := by
    change Fintype.card {i : ι // ¬ i = j} = _
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  rw [← LinearMap.det_conj a.toLinearMap E, hc, LinearMap.det_prodMap,
    show g = 1 by rfl, map_one, mul_one, show f = (-1 : ℂ) • 1 by rfl,
    LinearMap.det_smul, map_one, mul_one, Module.finrank_fintype_fun_eq_card, hK]

end ReflectionDeterminant

section Orientation

open Module
open Specs.LieAlgebrasAndRepresentations.SolvableRadical (IsSemisimple_value)
open Specs.LieAlgebrasAndRepresentations.CartanConjugacy (exponentialOperator)

private def autDet (L : Type u) [LieRing L] [LieAlgebra ℂ L] : Aut L →* ℂ where
  toFun a := LinearMap.det a.val.toLinearMap
  map_one' := map_one (LinearMap.det : Module.End ℂ L →* ℂ)
  map_mul' a b := LinearMap.det_comp a.val.toLinearMap b.val.toLinearMap

private theorem autDet_sq {L : Type u} [LieRing L] [LieAlgebra ℂ L]
    [FiniteDimensional ℂ L] (hss : IsSemisimple_value ℂ L) (a : Aut L) :
    autDet L a ^ 2 = 1 := by
  let B := killingForm ℂ L
  have hn : B.Nondegenerate :=
    (semisimple_iff_killingForm_nondegenerate ℂ L).mp hss
  let E := B.toDual hn
  let f := a.val.toLinearMap
  let g := E.symm.toLinearMap ∘ₗ f.dualMap ∘ₗ E.toLinearMap
  have hg : LinearMap.det g = LinearMap.det f := by
    calc
      LinearMap.det g = LinearMap.det f.dualMap := by
        simpa only [g, LinearEquiv.symm_symm] using LinearMap.det_conj f.dualMap E.symm
      _ = LinearMap.det f := LinearMap.det_dualMap f
  have hcomp : g ∘ₗ f = 1 := by
    apply LinearMap.ext
    intro x
    change E.symm (f.dualMap (E (f x))) = x
    apply E.injective
    rw [E.apply_symm_apply]
    apply LinearMap.ext
    intro y
    change E (f x) (f y) = E x y
    exact LieAlgebra.killingForm_of_equiv_apply (asLieEquiv a) x y
  change LinearMap.det f ^ 2 = 1
  calc
    LinearMap.det f ^ 2 = LinearMap.det g * LinearMap.det f := by rw [hg, pow_two]
    _ = LinearMap.det (g ∘ₗ f) := (LinearMap.det_comp g f).symm
    _ = 1 := by rw [hcomp, map_one]

private theorem expAd_double {L : Type u} [LieRing L] [LieAlgebra ℂ L]
    [FiniteDimensional ℂ L] (x : L) :
    toAut (RegularSemisimple.expAdEquiv (x + x)) =
      toAut (RegularSemisimple.expAdEquiv x) ^ 2 := by
  letI : NormedAddCommGroup L := Specs.LieAlgebrasAndRepresentations.RegularSemisimple.algebraNorm
  letI : NormedSpace ℂ L := NormedSpace.induced ℂ L
    (Fin (Module.finrank ℂ L) → ℂ) (Module.finBasis ℂ L).equivFun
  letI : Algebra ℚ (L →L[ℂ] L) := RestrictScalars.algebra ℚ ℂ _
  letI : NormedAlgebra ℚ (L →L[ℂ] L) := NormedAlgebra.restrictScalars ℚ ℂ _
  let F := LinearMap.toContinuousLinearMap.toLinearMap.comp (LieAlgebra.ad ℂ L).toLinearMap
  have h := NormedSpace.exp_add_of_commute (Commute.refl (F x))
  have he (z : L) : (toAut (RegularSemisimple.expAdEquiv z)).val.toLinearMap =
      exponentialOperator z := rfl
  rw [pow_two]
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  change (toAut (RegularSemisimple.expAdEquiv (x+x))).val.toLinearMap =
    (toAut (RegularSemisimple.expAdEquiv x)).val.toLinearMap *
      (toAut (RegularSemisimple.expAdEquiv x)).val.toLinearMap
  rw [he, he]
  change (NormedSpace.exp (F (x+x))).toLinearMap =
    (NormedSpace.exp (F x)).toLinearMap * (NormedSpace.exp (F x)).toLinearMap
  rw [map_add, h, ContinuousLinearMap.toLinearMap_mul]

private theorem det_inner {L : Type u} [LieRing L] [LieAlgebra ℂ L]
    [FiniteDimensional ℂ L] (hss : IsSemisimple_value ℂ L) {a : Aut L}
    (ha : a ∈ innerAut L) : autDet L a = 1 := by
  rw [AutomorphismDecomposition.innerGenerated L] at ha
  have hle : Subgroup.closure {g : Aut L | ∃ x : L,
      g.val.toLinearMap = exponentialOperator x} ≤ (autDet L).ker := by
    rw [Subgroup.closure_le]
    rintro a ⟨x, hx⟩
    let y := (1/2 : ℂ) • x
    have hy : y + y = x := by dsimp [y]; module
    have he : a = toAut (RegularSemisimple.expAdEquiv (y+y)) := by
      rw [hy]
      exact Subtype.ext (LinearEquiv.toLinearMap_injective hx)
    change autDet L a = 1
    rw [he, expAd_double, map_pow, autDet_sq hss]
  exact hle ha

end Orientation

section OrthogonalQuotient

open private inner_normal from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.AutomorphismDecomposition
open Specs.LieAlgebrasAndRepresentations.SolvableRadical (IsSemisimple_value)
open LieAlgebra.Orthogonal

private def typeBEquiv {ι : Type u} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (hcard : Fintype.card ι = 2*n+1) :
    so ι ≃ₗ⁅ℂ⁆ Specs.LieAlgebrasAndRepresentations.ClassicalRootsB.algebra n := by
  let J := Specs.LieAlgebrasAndRepresentations.ClassicalRootsB.form n
  obtain ⟨hJ, hJJ, hcardB⟩ := ClassicalRootsB.form_properties n
  let e : ι ≃ Specs.LieAlgebrasAndRepresentations.ClassicalRootsB.Index n :=
    Fintype.equivOfCardEq (hcard.trans hcardB.symm)
  exact (reindexSo e).trans (symmetricInvolutionSo J hJ hJJ).symm

private def typeDEquiv {ι : Type u} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (hcard : Fintype.card ι = 2*n) :
    so ι ≃ₗ⁅ℂ⁆ Specs.LieAlgebrasAndRepresentations.ClassicalRootsD.algebra n := by
  let e : ι ≃ Fin n ⊕ Fin n := Fintype.equivOfCardEq (by
    rw [Fintype.card_sum, Fintype.card_fin, hcard, two_mul])
  letI : Invertible (2 : ℂ) := invertibleOfNonzero (by norm_num)
  let D := (Orthogonal.typeDEquivSo' (Fin n) ℂ).trans
    (Orthogonal.soIndefiniteEquiv (Fin n) (Fin n) ℂ Complex.I_mul_I)
  exact (reindexSo e).trans D.symm

private theorem reflection_involutive {ι : Type u} [Fintype ι] [DecidableEq ι]
    (j : ι) (a : so ι ≃ₗ⁅ℂ⁆ so ι) (ha : ActsByReflection ι j a) :
    Function.Involutive a := by
  let A := Complex.ofRealHom.mapMatrix (reflectionMatrix ι j)
  have ht : Aᵀ = A := (reflection_transpose_mul j).1
  have hs : A * A = 1 := (reflection_transpose_mul j).2
  have hact (X : so ι) : (a X).val = A * X.val * A := by
    rw [show (a X).val = A * X.val * Aᵀ from ha X, ht]
  intro X
  apply Subtype.ext
  change (a (a X)).val = X.val
  rw [hact, hact]
  calc
    _ = (A * A) * X.val * (A * A) := by noncomm_ring
    _ = _ := by rw [hs, one_mul, mul_one]

private theorem reflection_diagonal_action {ι : Type u} [Fintype ι] [DecidableEq ι]
    (j : ι) (a : so ι ≃ₗ⁅ℂ⁆ so ι) (ha : ActsByReflection ι j a) (X : so ι) :
    (a X).val =
      diagonal (fun i => if i = j then (-1 : ℂ) else 1) *
        X.val * diagonal (fun i => if i = j then (-1 : ℂ) else 1) := by
  let A := Complex.ofRealHom.mapMatrix (reflectionMatrix ι j)
  have hd : A = diagonal (fun i => if i = j then (-1 : ℂ) else 1) := complex_reflection j
  have he : (a X).val = A * X.val * Aᵀ := ha X
  simpa only [hd, diagonal_transpose] using he

theorem reflection_commutes : reflectionCommutesType.{u} := by
  intro ι _ _ j a ha ω hω X
  have he (Y : so ι) (i k : ι) : (a Y).val i k =
      (if i = j then (-1 : ℂ) else 1) * Y.val i k *
        (if k = j then (-1 : ℂ) else 1) := by
    rw [reflection_diagonal_action j a ha Y, mul_diagonal, diagonal_mul]
  apply Subtype.ext
  ext i k
  rw [hω, he, he, hω]
  by_cases hi : i = j <;> by_cases hk : k = j <;> simp [hi, hk]

private theorem reflection_not_inner {ι : Type u} [Fintype ι] [DecidableEq ι]
    (hss : IsSemisimple_value ℂ (so ι)) {n : ℕ} (hn : 3 ≤ n)
    (hcard : Fintype.card ι = 2*n) (j : ι)
    (a : so ι ≃ₗ⁅ℂ⁆ so ι) (ha : ActsByReflection ι j a) :
    toAut a ∉ innerAut (so ι) := by
  intro ha'
  have h := det_inner hss ha'
  change LinearMap.det a.toLinearMap = 1 at h
  have hd := reflectionDet j a (reflection_diagonal_action j a ha)
  rw [hd, hcard, show 2*n-1 = 2*(n-1)+1 by omega, pow_succ, pow_mul] at h
  norm_num at h

theorem outerQuotient : outerQuotientType.{u} := by
  intro ι _ _ hss _
  letI normal := inner_normal (L := so ι)
  refine ⟨normal, ?_, ?_, ?_, ?_⟩
  · intro n _ hcard
    obtain ⟨_, hsub⟩ := chart_B_quotient hss (typeBEquiv hcard)
    exact hsub
  · intro n hn h4 hcard
    obtain ⟨h, hiso⟩ := chart_D_quotient hss (typeDEquiv hcard) hn
    rw [ite_eq_right h4] at hiso
    exact hiso
  · intro hcard
    obtain ⟨h, hD4⟩ := chart_D_quotient hss (typeDEquiv (n := 4) hcard) (by decide)
    simpa using hD4
  · intro n hn hcard j a ha
    constructor
    · intro h
      exact reflection_not_inner hss hn hcard j a ha ((QuotientGroup.eq_one_iff _).mp h)
    · change (QuotientGroup.mk' (innerAut (so ι)) (toAut a)) ^ 2 = 1
      rw [← map_pow, toAut_involutive_sq a (reflection_involutive j a ha), map_one]

theorem outerClassReduction : outerClassReductionType.{u} :=
  reduction_of_quotient outerQuotient

theorem involutionReduction : involutionReductionType.{u} := by
  intro ι _ _ hss hcard ω hω hc a ha j
  letI normal := inner_normal (L := so ι)
  exact outerClassReduction ι hss hcard ω hω hc normal a
    (by
      change (QuotientGroup.mk' (innerAut (so ι)) (toAut a)) ^ 2 = 1
      rw [← map_pow, toAut_involutive_sq a ha, map_one]) j

end OrthogonalQuotient

/-- The real orthogonal reflection used as an outer representative. -/
def reflectionMatrix : reflectionMatrixType.{u} :=
  Specs.LieAlgebrasAndRepresentations.OrthogonalDiagramReduction.reflectionMatrix

end LieAlgebrasAndRepresentations.OrthogonalDiagramReduction
