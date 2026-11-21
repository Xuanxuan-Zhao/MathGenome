import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ComplexClassification
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleIdealDecomposition
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CartanConjugacy
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClassicalLowRank
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClassicalMatrixCartans
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RealRootSpace
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.Reconstruction
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.DynkinExhaustion
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SerreSimplicity
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ExceptionalCoordinateE
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClassicalRootsA
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClassicalRootsB
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClassicalRootsC
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClassicalRootsD
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.WeylChambersLength
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Finset.Sort
import Batteries.Tactic.OpenPrivate

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LieAlgebrasAndRepresentations.ComplexClassification

open Specs.LieAlgebrasAndRepresentations.ComplexClassification
open scoped DirectSum Classical
open Module
open Specs.LieAlgebrasAndRepresentations.RootDecomposition (rootSet_value)
open Specs.LieAlgebrasAndRepresentations.RootForm (coroot_value)
open Specs.LieAlgebrasAndRepresentations.SerreRelations (simple positive)
open Specs.LieAlgebrasAndRepresentations.RealRootSpace
open Serre (Algebra CartanConditions MatrixConnected)
open private exists_normalized_simple_vectors from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.Reconstruction

private theorem relabel_relations {α β : Type*} [DecidableEq α] [DecidableEq β]
    (C : Matrix α α ℤ) (D : Matrix β β ℤ) (s : α ≃ β)
    (hs : ∀ i j, D (s i) (s j) = C i j) (hD : ∀ i j, i ≠ j → D i j ≤ 0) :
    Serre.RelationsHold C (fun i => Serre.e D (s i)) (fun i => Serre.f D (s i))
      (fun i => Serre.h D (s i)) := by
  obtain ⟨hh, he, hf, hef, se, sf⟩ := Serre.relations_spec D hD
  refine ⟨fun i j => hh _ _, fun i j => ?_, fun i j => ?_,
    fun i j => ?_, fun i j hij => ?_, fun i j hij => ?_⟩
  · simpa [hs] using he (s i) (s j)
  · simpa [hs] using hf (s i) (s j)
  · simpa using hef (s i) (s j)
  · simpa [hs] using se (s i) (s j) (s.injective.ne hij)
  · simpa [hs] using sf (s i) (s j) (s.injective.ne hij)

/-- Relabeling preserves the presentation and carries each generator to the
corresponding generator of the relabeled algebra. -/
private def serre_reindex {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι ι ℤ) (B : Matrix κ κ ℤ) (e : ι ≃ κ)
    (h : ∀ i j, B (e i) (e j) = A i j) (hA : ∀ i j, i ≠ j → A i j ≤ 0) :
    Algebra A ≃ₗ⁅ℂ⁆ Algebra B := by
  have h' (i j) : A (e.symm i) (e.symm j) = B i j := by
    simpa using (h (e.symm i) (e.symm j)).symm
  have hB (i j) (hij : i ≠ j) : B i j ≤ 0 := by
    rw [← h']
    exact hA _ _ (e.symm.injective.ne hij)
  let f := Serre.lift A hA _ _ _ (relabel_relations A B e h hB)
  let g := Serre.lift B hB _ _ _ (relabel_relations B A e.symm h' hA)
  have hf : g.comp f = LieHom.id := by
    apply Serre.hom_ext A <;> intro i <;> simp [f, g]
  have hg : f.comp g = LieHom.id := by
    apply Serre.hom_ext B <;> intro i <;> simp [f, g]
  refine LieEquiv.ofBijective f ⟨?_, ?_⟩
  · exact Function.LeftInverse.injective (LieHom.congr_fun hf)
  · intro y
    exact ⟨g y, LieHom.congr_fun hg y⟩

private noncomputable def restrictRootLinear {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    [FiniteDimensional ℂ L] (H : LieSubalgebra ℂ L) : Module.Dual ℂ H →ₗ[ℝ] E H where
  toFun := rootRestriction H
  map_add' α β := by
    ext x
    change (α x + β x).re = (α x).re + (β x).re
    exact Complex.add_re _ _
  map_smul' r α := by
    ext x
    change ((r : ℂ) * α x).re = r * (α x).re
    simp [Complex.mul_re]

private theorem exists_regular_vector {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {R : Set V} (hR : IsRootSystem R) :
    ∃ v : V, RootRegular R v := by
  let : Finite R := hR.finite
  let form (a : R) : V →ₗ[ℝ] ℝ := innerₗ V a.val
  have hproper (a : R) : (form a).ker ≠ ⊤ := by
    intro h
    have hz : a.val ∈ (form a).ker := by rw [h]; trivial
    exact (_root_.inner_self_ne_zero.mpr (hR.nonzero _ a.property)) hz
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (fun a => (form a).ker) hproper
  refine ⟨v, fun a ha haz => hv ⟨a, ha⟩ ?_⟩
  change inner ℝ a v = 0
  rw [real_inner_comm v a]
  exact haz

private theorem simple_root_restriction {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    [FiniteDimensional ℂ L] {H : LieSubalgebra ℂ L} (d : Realization H) :
    letI := d.normedAddCommGroup
    letI := d.innerProductSpace
    ∀ v : E H, ∃ p : Module.Dual ℂ H →ₗ[ℝ] ℝ,
      (∀ α, p α = inner ℝ v (rootRestriction H α)) ∧
      ∃ e : simple H p ≃ simpleRoots (realRoots H) v,
        ∀ a, (e a).val = rootRestriction H a.val := by
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  intro v
  let p := (innerₗ (E H) v).comp (restrictRootLinear H)
  have hp (a : Module.Dual ℂ H) : p a = inner ℝ v (rootRestriction H a) := rfl
  have hj {x : E H} (hx : x ∈ realRoots H) :
      d.j x ∈ rootSet_value H ∧ rootRestriction H (d.j x) = x := by
    obtain ⟨a, ha, rfl⟩ := hx
    rw [d.extension_root a ha]
    exact ⟨ha, rfl⟩
  have into (a : simple H p) : rootRestriction H a.val ∈ simpleRoots (realRoots H) v := by
    refine ⟨⟨⟨a.val, a.property.1.1, rfl⟩, a.property.1.2⟩, ?_⟩
    intro b hb c hc h
    apply a.property.2 (d.j b) ⟨(hj hb.1).1, by rw [hp, (hj hb.1).2]; exact hb.2⟩
      (d.j c) ⟨(hj hc.1).1, by rw [hp, (hj hc.1).2]; exact hc.2⟩
    rw [← map_add, ← h, d.extension_root a.val a.property.1.1]
  have out (a : simpleRoots (realRoots H) v) : d.j a.val ∈ simple H p := by
    refine ⟨⟨(hj a.property.1.1).1, by rw [hp, (hj a.property.1.1).2]; exact a.property.1.2⟩, ?_⟩
    intro b hb c hc h
    apply a.property.2 (rootRestriction H b) ⟨⟨b, hb.1, rfl⟩, hb.2⟩
      (rootRestriction H c) ⟨⟨c, hc.1, rfl⟩, hc.2⟩
    rw [← (hj a.property.1.1).2, h]
    exact (restrictRootLinear H).map_add b c
  exact ⟨p, hp, ⟨fun a => ⟨_, into a⟩, fun a => ⟨_, out a⟩,
      fun a => Subtype.ext (d.extension_root a.val a.property.1.1),
      fun a => Subtype.ext (hj a.property.1.1).2⟩, fun _ => rfl⟩

/-- The actual Killing realization supplies the Cartan matrix in reconstruction. -/
private theorem reconstruct_from_real_basis {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    [FiniteDimensional ℂ L] (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H) (d : Realization H) :
    letI := d.normedAddCommGroup
    letI := d.innerProductSpace
    ∃ (v : E H) (hv : RootRegular (realRoots H) v)
      (b : Basis (simpleRoots (realRoots H) v) ℝ (E H)),
      IsSimpleBasis (realRoots H) v b ∧
      ∃ (A : Matrix (simpleRoots (realRoots H) v) (simpleRoots (realRoots H) v) ℤ),
        (∀ i j, (A i j : ℝ) = cartanMatrix b i j) ∧ Nonempty (Serre.Algebra A ≃ₗ⁅ℂ⁆ L) := by
  classical
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  obtain ⟨v, hv⟩ := exists_regular_vector d.root_system
  obtain ⟨b, hb⟩ := simpleRoots_basis (realRoots H) d.root_system v hv
  have hb' : IsSimpleBasis (realRoots H) v b := by
    change Set.range b = _
    have hfun : (b : simpleRoots (realRoots H) v → E H) = Subtype.val := funext hb
    rw [hfun, Subtype.range_coe]
  obtain ⟨p, hp, e, he⟩ := simple_root_restriction d v
  have hp' (a) (ha : a ∈ rootSet_value H) : p a ≠ 0 := by
    rw [hp]
    exact hv _ ⟨a, ha, rfl⟩
  obtain ⟨X, Y, hXY⟩ := exists_normalized_simple_vectors hss H hH p
  obtain ⟨A, g, hA, _, _⟩ := serre_reconstruction hss H hH p hp' X Y hXY
  let A' : Matrix (simpleRoots (realRoots H) v) (simpleRoots (realRoots H) v) ℤ :=
    fun i j => A (e.symm i) (e.symm j)
  have hA' (i j) : (A' i j : ℝ) = cartanMatrix b i j := by
    have hi := he (e.symm i)
    have hj := he (e.symm j)
    rw [e.apply_symm_apply] at hi hj
    have h := d.coroot_evaluation (rootRestriction H (e.symm j).val) (e.symm i).val
      (e.symm i).property.1.1
    rw [d.extension_root _ (e.symm j).property.1.1, hA] at h
    apply Complex.ofReal_injective
    rw [Complex.ofReal_intCast]
    change (A (e.symm i) (e.symm j) : ℂ) = _
    rw [h, ← hi, ← hj]
    simp [cartanMatrix, hb, rootCartan, coroot, inner_smul_right, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  refine ⟨v, hv, b, hb', A', hA', ?_⟩
  have hCond := Serre.cartanConditions_spec (realRoots H) d.root_system v hv b hb' A' hA'
  have hOff : ∀ i j, i ≠ j → A i j ≤ 0 := by
    intro i j hij
    simpa [A'] using hCond.2.1 (e i) (e j) (e.injective.ne hij)
  exact ⟨(serre_reindex A A' e (fun i j => by simp [A']) hOff).symm.trans g⟩


private theorem standard_diagonal (t : FiniteDynkinType) (i : Fin t.rank) :
    t.cartan i i = 2 := by
  cases t with
  | A n h => exact congrFun (CartanMatrix.A_diag n) i
  | B n h => exact CartanMatrix.C_diag n i
  | C n h => exact CartanMatrix.B_diag n i
  | D n h => exact CartanMatrix.D_diag n i
  | E6 => exact CartanMatrix.E_diag 6 i
  | E7 => exact CartanMatrix.E_diag 7 i
  | E8 => exact CartanMatrix.E_diag 8 i
  | F4 => fin_cases i <;> decide
  | G2 => fin_cases i <;> decide

private theorem standard_cartan_pairs (t : FiniteDynkinType) (i j : Fin t.rank) (hij : i ≠ j) :
    (t.cartan i j, t.cartan j i) ∈
      ({(0, 0), (-1, -1), (-1, -2), (-2, -1), (-1, -3), (-3, -1)} : Set (ℤ × ℤ)) := by
  have hji := Ne.symm hij
  have hval := Fin.val_ne_of_ne hij
  cases t <;> dsimp only [FiniteDynkinType.rank] at *
  case A n h =>
    change (CartanMatrix.A n i j, CartanMatrix.A n j i) ∈ _
    simp only [CartanMatrix.A, Matrix.of_apply, ite_eq_right hij, ite_eq_right hji]
    split_ifs <;> simp_all <;> omega
  case B n h =>
    change (CartanMatrix.C n i j, CartanMatrix.C n j i) ∈ _
    simp only [CartanMatrix.C, Matrix.of_apply, ite_eq_right hij, ite_eq_right hji]
    split_ifs <;> simp_all <;> omega
  case C n h =>
    change (CartanMatrix.B n i j, CartanMatrix.B n j i) ∈ _
    simp only [CartanMatrix.B, Matrix.of_apply, ite_eq_right hij, ite_eq_right hji]
    split_ifs <;> simp_all <;> omega
  case D n h =>
    change (CartanMatrix.D n i j, CartanMatrix.D n j i) ∈ _
    have hd : CartanMatrix.D n j i = CartanMatrix.D n i j :=
      (CartanMatrix.D_isSymm n).apply i j
    rw [hd]
    simp only [CartanMatrix.D, Matrix.of_apply, ite_eq_right hij]
    split_ifs <;> simp
  case E6 | E7 | E8 =>
    simp only [FiniteDynkinType.cartan, CartanMatrix.E, Matrix.of_apply, ite_eq_right hij, ite_eq_right hji]
    split_ifs <;> simp_all <;> omega
  case F4 | G2 => fin_cases i <;> fin_cases j <;> first | contradiction | decide

private theorem recover_standard_cartan {V ι : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {R : Set V} {v : V} {b : Basis ι ℝ V}
    (hR : IsRootSystem R) (hv : RootRegular R v) (hb : IsSimpleBasis R v b)
    (t : FiniteDynkinType) (e : ι ≃ Fin t.rank)
    (hedge : ∀ i j, (dynkinDiagram b).edges i j = t.diagram.edges (e i) (e j))
    (harrow : ∀ i j, (dynkinDiagram b).arrow i j ↔ t.diagram.arrow (e i) (e j)) :
    ∀ i j, cartanMatrix b i j = (t.cartan (e i) (e j) : ℝ) := by
  intro i j
  by_cases hij : i = j
  · subst j
    rw [cartan_diagonal R hR v hv b hb, standard_diagonal]
    norm_num
  have heij := e.injective.ne hij
  have h₁ := cartan_pair_values hR hv hb hij
  have h₂ := standard_cartan_pairs t (e i) (e j) heij
  have h₃ := hedge i j
  rw [FiniteDynkinType.diagram] at h₃
  simp only [ite_eq_right heij] at h₃
  have hp := dynkin_edges_cast hR hv hb hij
  have ha := harrow i j
  rw [dynkin_arrow_iff_cartan_lt hR hv hb hij, FiniteDynkinType.diagram] at ha
  simp only [heij, true_and] at ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h₁ h₂
  rcases h₁ with h | h | h | h | h | h <;> rcases h with ⟨h₁, h₁'⟩ <;>
    rcases h₂ with h | h | h | h | h | h <;> rcases h with ⟨h₂, h₂'⟩ <;>
    simp_all <;> norm_num at *

private theorem standard_rank_pos (t : FiniteDynkinType) : 0 < t.rank := by
  cases t <;> dsimp [FiniteDynkinType.rank] <;> omega

private theorem matrix_connected_of_decreasing {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (step : ∀ i : Fin n, i.val ≠ 0 → ∃ j : Fin n, j.val < i.val ∧ MatrixConnected A j i) :
    ∀ i j, MatrixConnected A i j := by
  let base : Fin n := ⟨0, hn⟩
  have hbase (k : ℕ) : ∀ i : Fin n, i.val = k → MatrixConnected A base i := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hi
      by_cases h : i.val = 0
      · have his : i = base := Fin.ext h
        exact his ▸ Relation.EqvGen.refl base
      · obtain ⟨j, hj, hji⟩ := step i h
        exact Relation.EqvGen.trans _ _ _ (ih j.val (hi ▸ hj) j rfl) hji
  exact fun i j => Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hbase i.val i rfl)) (hbase j.val j rfl)

private theorem standard_connected (t : FiniteDynkinType) :
    ∀ i j, MatrixConnected t.cartan i j := by
  have ht := standard_rank_pos t
  apply matrix_connected_of_decreasing ht
  intro i hi
  have hip := i.isLt
  let prev : Fin t.rank := ⟨i.val - 1, by omega⟩
  have hprev : prev.val + 1 = i.val := by dsimp [prev]; omega
  have hne : prev ≠ i := by intro h; have := congrArg Fin.val h; omega
  have hne' : i.val + 1 ≠ prev.val := by omega
  have hlt : prev.val < i.val := by omega
  cases t <;> dsimp only [FiniteDynkinType.rank] at *
  case A n hn =>
    exact ⟨prev, hlt, .rel _ _ ⟨hne, by
      simp [FiniteDynkinType.cartan, CartanMatrix.A, Matrix.of_apply, hne, hprev]⟩⟩
  case B n hn =>
    exact ⟨prev, hlt, .rel _ _ ⟨hne, by
      simp [FiniteDynkinType.cartan, CartanMatrix.C, Matrix.of_apply, hne, hprev]⟩⟩
  case C n hn =>
    exact ⟨prev, hlt, .rel _ _ ⟨hne, by
      simp [FiniteDynkinType.cartan, CartanMatrix.B, Matrix.of_apply, hne, hprev]
      split_ifs <;> norm_num⟩⟩
  case D n hn =>
    change i.val < n at hip
    by_cases h : i.val + 2 < n
    · exact ⟨prev, hlt, .rel _ _ ⟨hne, by
        simp [FiniteDynkinType.cartan, CartanMatrix.D, Matrix.of_apply, hne, hprev, h, show ¬n ≤ 2 by omega]⟩⟩
    · let j : Fin n := ⟨n - 3, by omega⟩
      have hj : j.val < i.val := by dsimp [j]; omega
      have hji : j ≠ i := by intro he; rw [he] at hj; omega
      have hd : j.val + 3 = n ∧ (i.val + 2 = n ∨ i.val + 1 = n) := by dsimp [j]; omega
      exact ⟨j, hj, .rel _ _ ⟨hji, by
        simp [FiniteDynkinType.cartan, CartanMatrix.D, Matrix.of_apply, hji, h, hd, show ¬n ≤ 2 by omega]⟩⟩
  case E6 =>
    change ∃ j : Fin 6, j.val < i.val ∧ MatrixConnected (CartanMatrix.E 6) j i
    have h02 : MatrixConnected (CartanMatrix.E 6) 0 2 := .rel _ _ ⟨by decide, by decide⟩
    have h23 : MatrixConnected (CartanMatrix.E 6) 2 3 := .rel _ _ ⟨by decide, by decide⟩
    have h31 : MatrixConnected (CartanMatrix.E 6) 3 1 := .rel _ _ ⟨by decide, by decide⟩
    by_cases h : i.val = 1
    · have h1 : i = (1 : Fin 6) := Fin.ext h
      subst i
      exact ⟨0, by decide, Relation.EqvGen.trans _ _ _ h02 (Relation.EqvGen.trans _ _ _ h23 h31)⟩
    by_cases h' : i.val = 2
    · have h2 : i = (2 : Fin 6) := Fin.ext h'
      subst i
      exact ⟨0, by decide, h02⟩
    have hp2 : 2 ≤ prev.val := by omega
    exact ⟨prev, hlt, .rel _ _ ⟨hne, by
      simp [FiniteDynkinType.cartan, CartanMatrix.E, Matrix.of_apply, hne, hp2, hprev]⟩⟩
  case E7 =>
    change ∃ j : Fin 7, j.val < i.val ∧ MatrixConnected (CartanMatrix.E 7) j i
    have h02 : MatrixConnected (CartanMatrix.E 7) 0 2 := .rel _ _ ⟨by decide, by decide⟩
    have h23 : MatrixConnected (CartanMatrix.E 7) 2 3 := .rel _ _ ⟨by decide, by decide⟩
    have h31 : MatrixConnected (CartanMatrix.E 7) 3 1 := .rel _ _ ⟨by decide, by decide⟩
    by_cases h : i.val = 1
    · have h1 : i = (1 : Fin 7) := Fin.ext h
      subst i
      exact ⟨0, by decide, Relation.EqvGen.trans _ _ _ h02 (Relation.EqvGen.trans _ _ _ h23 h31)⟩
    by_cases h' : i.val = 2
    · have h2 : i = (2 : Fin 7) := Fin.ext h'
      subst i
      exact ⟨0, by decide, h02⟩
    have hp2 : 2 ≤ prev.val := by omega
    exact ⟨prev, hlt, .rel _ _ ⟨hne, by
      simp [FiniteDynkinType.cartan, CartanMatrix.E, Matrix.of_apply, hne, hp2, hprev]⟩⟩
  case E8 =>
    change ∃ j : Fin 8, j.val < i.val ∧ MatrixConnected (CartanMatrix.E 8) j i
    have h02 : MatrixConnected (CartanMatrix.E 8) 0 2 := .rel _ _ ⟨by decide, by decide⟩
    have h23 : MatrixConnected (CartanMatrix.E 8) 2 3 := .rel _ _ ⟨by decide, by decide⟩
    have h31 : MatrixConnected (CartanMatrix.E 8) 3 1 := .rel _ _ ⟨by decide, by decide⟩
    by_cases h : i.val = 1
    · have h1 : i = (1 : Fin 8) := Fin.ext h
      subst i
      exact ⟨0, by decide, Relation.EqvGen.trans _ _ _ h02 (Relation.EqvGen.trans _ _ _ h23 h31)⟩
    by_cases h' : i.val = 2
    · have h2 : i = (2 : Fin 8) := Fin.ext h'
      subst i
      exact ⟨0, by decide, h02⟩
    have hp2 : 2 ≤ prev.val := by omega
    exact ⟨prev, hlt, .rel _ _ ⟨hne, by
      simp [FiniteDynkinType.cartan, CartanMatrix.E, Matrix.of_apply, hne, hp2, hprev]⟩⟩
  case F4 | G2 =>
    refine ⟨prev, hlt, .rel _ _ ⟨hne, ?_⟩⟩
    revert hprev
    generalize prev = j
    fin_cases i <;> fin_cases j <;> decide

private def standardRootCount : FiniteDynkinType → ℕ
  | .A n _ => n * (n + 1)
  | .B n _ | .C n _ => 2 * n ^ 2
  | .D n _ => 2 * n * (n - 1)
  | .E6 => 72
  | .E7 => 126
  | .E8 => 240
  | .F4 => 48
  | .G2 => 12

private structure StandardRootRealization (t : FiniteDynkinType) where
  V : Type
  [normedGroup : NormedAddCommGroup V]
  [innerSpace : InnerProductSpace ℝ V]
  roots : Set V
  roots_axioms : IsRootSystem roots
  root_count : roots.ncard = standardRootCount t
  regular : V
  regular_spec : RootRegular roots regular
  basis : Basis (Fin t.rank) ℝ V
  simple_basis : IsSimpleBasis roots regular basis
  matrix_entry : ∀ i j, (t.cartan i j : ℝ) = cartanMatrix basis i j

private theorem cartan_reindex {V ι κ : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (b : Basis ι ℝ V) (e : ι ≃ κ) (i j : κ) :
    cartanMatrix (b.reindex e) i j = cartanMatrix b (e.symm i) (e.symm j) := by
  simp only [cartanMatrix, Basis.reindex_apply]

private theorem standard_cartan_b {n : ℕ} (i j : Fin n) :
    (CartanMatrix.C n i j : ℝ) = cartanMatrix (ClassicalCoordinates.simpleB n) i j := by
  open ClassicalCoordinates in
  have hi : i.val < n := i.isLt
  have hj : j.val < n := j.isLt
  simp only [cartanMatrix, rootCartan, simpleB_gram, ite_true, CartanMatrix.C, Matrix.of_apply, adjacent]
  split_ifs <;> norm_num <;> omega

private theorem standard_cartan_c {n : ℕ} (i j : Fin n) :
    (CartanMatrix.B n i j : ℝ) = cartanMatrix (ClassicalCoordinates.simpleC n) i j := by
  open ClassicalCoordinates in
  have hi : i.val < n := i.isLt
  have hj : j.val < n := j.isLt
  simp only [cartanMatrix, rootCartan, simpleC_gram, ite_true, CartanMatrix.B, Matrix.of_apply, terminalEdge, adjacent]
  split_ifs <;> norm_num <;> omega

private theorem standard_cartan_d {n : ℕ} (hn : 4 ≤ n) (i j : Fin n) :
    (CartanMatrix.D n i j : ℝ) = cartanMatrix (ClassicalCoordinates.simpleD n) i j := by
  open ClassicalCoordinates in
  have hi : i.val < n := i.isLt
  have hj : j.val < n := j.isLt
  simp only [cartanMatrix, rootCartan, simpleD_gram hn, ite_true, CartanMatrix.D, Matrix.of_apply, forkAdjacent]
  split_ifs <;> norm_num <;> omega

private theorem standard_root_realization (t : FiniteDynkinType) :
    Nonempty (StandardRootRealization t) := by
  classical
  cases t with
  | A n hn =>
    open ClassicalCoordinates in
    obtain ⟨v, b, hb, hv, hs, _, _⟩ := simpleDiagramA n hn
    refine ⟨⟨zeroSum n, rootsA n, rootSystemA n hn, countA n hn, v, hv, b, hs, ?_⟩⟩
    intro i j
    change ((CartanMatrix.A n i j : ℤ) : ℝ) = cartanMatrix b i j
    rw [show (b : Fin n → zeroSum n) = simpleA n from funext hb, simpleA_cartan]
    simp [CartanMatrix.A, Matrix.of_apply, adjacent] <;> split_ifs <;> norm_num
  | B n hn =>
    open ClassicalCoordinates in
    obtain ⟨v, b, hb, hv, hs, _, _⟩ := simpleDiagramB n hn
    refine ⟨⟨Space n, rootsB n, rootSystemB n hn, countB n hn, v, hv, b, hs, ?_⟩⟩
    intro i j
    change ((CartanMatrix.C n i j : ℤ) : ℝ) = cartanMatrix b i j
    rw [show (b : Fin n → Space n) = simpleB n from funext hb]
    exact standard_cartan_b i j
  | C n hn =>
    open ClassicalCoordinates in
    obtain ⟨v, b, hb, hv, hs, _, _⟩ := simpleDiagramC n hn
    refine ⟨⟨Space n, rootsC n, rootSystemC n hn, countC n hn, v, hv, b, hs, ?_⟩⟩
    intro i j
    change ((CartanMatrix.B n i j : ℤ) : ℝ) = cartanMatrix b i j
    rw [show (b : Fin n → Space n) = simpleC n from funext hb]
    exact standard_cartan_c i j
  | D n hn =>
    open ClassicalCoordinates in
    obtain ⟨v, b, hb, hv, hs, _, _⟩ := simpleDiagramD n hn
    refine ⟨⟨Space n, rootsD n, rootSystemD n hn, countD n hn, v, hv, b, hs, ?_⟩⟩
    intro i j
    change ((CartanMatrix.D n i j : ℤ) : ℝ) = cartanMatrix b i j
    rw [show (b : Fin n → Space n) = simpleD n from funext hb]
    exact standard_cartan_d hn i j
  | E6 =>
    open ExceptionalE in
    obtain ⟨hv, b, hb, hs⟩ := e6_basis
    refine ⟨⟨e6Space, e6Roots, e6_isRootSystem, e6_count.1, e6Regular, hv, b, hs, ?_⟩⟩
    intro i j
    change ((CartanMatrix.E 6 i j : ℤ) : ℝ) = cartanMatrix b i j
    rw [show (b : Fin 6 → e6Space) = e6Simple from funext hb, e6_diagram.1]
    simp only [CartanMatrix.E, Matrix.of_apply, adjacent, Fin.ext_iff,
      Fin.val_castLE, Fin.val_castSucc, Fin.val_zero, Fin.val_one, Fin.coe_ofNat_eq_mod,
      Nat.reduceMod, FiniteDynkinType.rank]
    split_ifs <;> norm_num
  | E7 =>
    open ExceptionalE in
    obtain ⟨hv, b, hb, hs⟩ := e7_basis
    refine ⟨⟨e7Space, e7Roots, e7_isRootSystem, e7_count.1, e7Regular, hv, b, hs, ?_⟩⟩
    intro i j
    change ((CartanMatrix.E 7 i j : ℤ) : ℝ) = cartanMatrix b i j
    rw [show (b : Fin 7 → e7Space) = e7Simple from funext hb, e7_diagram.1]
    simp only [CartanMatrix.E, Matrix.of_apply, adjacent, Fin.ext_iff,
      Fin.val_castLE, Fin.val_castSucc, Fin.val_zero, Fin.val_one, Fin.coe_ofNat_eq_mod,
      Nat.reduceMod, FiniteDynkinType.rank]
    split_ifs <;> norm_num
  | E8 =>
    open ExceptionalE in
    obtain ⟨hv, b, hb, hs⟩ := e8_basis
    refine ⟨⟨ExceptionalGF.Space 8, e8Roots, e8_isRootSystem, e8_count.1, e8Regular, hv, b, hs, ?_⟩⟩
    intro i j
    change ((CartanMatrix.E 8 i j : ℤ) : ℝ) = cartanMatrix b i j
    rw [show (b : Fin 8 → ExceptionalGF.Space 8) = e8Simple from funext hb, e8_diagram.1]
    simp only [CartanMatrix.E, Matrix.of_apply, adjacent, Fin.ext_iff,
      Fin.val_castLE, Fin.val_castSucc, Fin.val_zero, Fin.val_one, Fin.coe_ofNat_eq_mod,
      Nat.reduceMod, FiniteDynkinType.rank]
    split_ifs <;> norm_num
  | G2 =>
    open ExceptionalGF in
    obtain ⟨hv, b, hb, hs⟩ := g2_basis
    refine ⟨⟨g2Plane, g2Roots, g2_isRootSystem, g2_count, g2Regular, hv, b, hs, ?_⟩⟩
    intro i j
    change ((CartanMatrix.G₂ i j : ℤ) : ℝ) = cartanMatrix b i j
    rw [show (b : Fin 2 → g2Plane) = g2Simple from funext hb, g2_diagram.1]
    fin_cases i <;> fin_cases j <;> norm_num [CartanMatrix.G₂, Matrix.cons_val, Matrix.head_cons]
  | F4 =>
    open ExceptionalGF in
    obtain ⟨hv, b, hb, hs⟩ := f4_basis
    let e : Equiv.Perm (Fin 4) := Fin.revPerm
    have hs' : IsSimpleBasis f4Roots f4Regular (b.reindex e) := by
      unfold IsSimpleBasis at *
      rw [Basis.coe_reindex, e.symm.surjective.range_comp, hs]
    refine ⟨⟨Space 4, f4Roots, f4_isRootSystem, f4_count.1, f4Regular, hv, b.reindex e, hs', ?_⟩⟩
    intro i j
    change ((CartanMatrix.F₄ i j : ℤ) : ℝ) = cartanMatrix (b.reindex e) i j
    rw [cartan_reindex, show (b : Fin 4 → Space 4) = f4Simple from funext hb, f4_diagram.1]
    fin_cases i <;> fin_cases j <;> norm_num [CartanMatrix.F₄, e, Fin.revPerm, Fin.rev,
      Matrix.cons_val, Matrix.head_cons]

theorem models_simple : modelsSimpleType := by
  intro t
  obtain ⟨d⟩ := standard_root_realization t
  letI := d.normedGroup
  letI := d.innerSpace
  letI : Nonempty (Fin t.rank) := Fin.pos_iff_nonempty.mp (standard_rank_pos t)
  refine ⟨?_, Serre.isSimple_spec _ d.roots_axioms _ d.regular_spec _ d.simple_basis _
    d.matrix_entry (standard_connected t)⟩
  exact (Serre.finiteType_spec _ d.roots_axioms _ d.regular_spec _ d.simple_basis _
    d.matrix_entry).1

private theorem model_finrank (t : FiniteDynkinType) :
    finrank ℂ (Model t) = t.rank + standardRootCount t := by
  obtain ⟨d⟩ := standard_root_realization t
  letI := d.normedGroup
  letI := d.innerSpace
  have h := (Serre.finiteType_spec _ d.roots_axioms _ d.regular_spec _ d.simple_basis _
    d.matrix_entry).2.2.2.2.2.2
  rw [Fintype.card_fin] at h
  exact h.trans (congrArg (t.rank + ·) d.root_count)

/-- A direct sum of nontrivial algebras is simple only when it has a single summand. -/
private theorem index_subsingleton_of_simple_sum {ι : Type*} (M : ι → Type*)
    [∀ i, LieRing (M i)] [∀ i, LieAlgebra ℂ (M i)] [∀ i, Nontrivial (M i)]
    {L : Type*} [LieRing L] [LieAlgebra ℂ L] [LieAlgebra.IsSimple ℂ L]
    (g : (⨁ i, M i) ≃ₗ⁅ℂ⁆ L) : Subsingleton ι := by
  classical
  refine ⟨fun i j => ?_⟩
  by_contra h
  let p := (DirectSum.lieAlgebraComponent ℂ ι M i).comp g.symm.toLieHom
  have hp (x : ⨁ i, M i) : p (g x) = x i := by
    simp only [p, LieHom.comp_apply, LieEquiv.coe_toLieHom, LieEquiv.symm_apply_apply]
    rfl
  obtain ⟨x, hx⟩ := exists_ne (0 : M j)
  have hx' : g (DirectSum.of M j x) ∈ p.ker := by
    rw [LieHom.mem_ker, hp, DirectSum.of_eq_of_ne _ _ _ h]
  obtain ⟨y, hy⟩ := exists_ne (0 : M i)
  have hy' : g (DirectSum.of M i y) ∉ p.ker := by
    rw [LieHom.mem_ker, hp, DirectSum.of_eq_same]
    exact hy
  rcases LieAlgebra.IsSimple.eq_bot_or_eq_top (R := ℂ) p.ker with hb | ht
  · rw [hb, LieSubmodule.mem_bot] at hx'
    have hz : g (DirectSum.of M j x) = g (DirectSum.of M j 0) := by simpa using hx'
    exact hx (DirectSum.of_injective j (g.injective hz))
  · exact hy' (ht ▸ LieSubmodule.mem_top _)

theorem simple_classification : simpleClassificationType := by
  classical
  intro L _ _ _ hL
  have hss : IsSemisimple ℂ L := LieAlgebra.radical_eq_bot
  obtain ⟨H, hH⟩ := exists_maximal_toral L hss
  let d := RealRootSpace.realization_of_maximalToral hss H hH
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  obtain ⟨v, hv, b, hb, A, hA, ⟨g⟩⟩ := reconstruct_from_real_basis hss H hH d
  let ι := simpleRoots (realRoots H) v
  letI : Fintype ι := (simpleRoots_finite d.root_system.toRootAxioms v).fintype
  letI : Nonempty ι := by
    by_contra h
    haveI : IsEmpty ι := not_nonempty_iff.mp h
    letI : Subsingleton (Algebra A) := Serre.emptySimplicity_spec A
    letI : Subsingleton L := g.symm.injective.subsingleton
    exact LieAlgebra.not_isSimple_of_subsingleton (R := ℂ) (L := L) hL
  let M (c : Serre.Component A) := Algebra (Serre.componentMatrix A c)
  letI (c : Serre.Component A) : LieAlgebra.IsSimple ℂ (M c) :=
    Serre.componentSimple_spec (realRoots H) d.root_system v hv b hb A hA c
  letI (c : Serre.Component A) : Nontrivial (M c) :=
    LieAlgebra.IsSimple.nontrivial (R := ℂ) (L := M c)
  obtain ⟨f, _⟩ := Serre.componentSum_spec (realRoots H) d.root_system v hv b hb A hA
  letI : Subsingleton (Serre.Component A) := index_subsingleton_of_simple_sum M (f.trans g)
  have hconn (i j : ι) : MatrixConnected A i j :=
    Quotient.exact (Subsingleton.elim (Serre.componentOf A i) (Serre.componentOf A j))
  have hD : (dynkinDiagram b).IsConnected := ⟨inferInstance, fun i j =>
    (Serre.matrixConnected_iff_dynkinConnected A d.root_system hv hb hA i j).mp (hconn i j)⟩
  obtain ⟨t, e, hedge, harrow⟩ := dynkin_exhaustion (realRoots H) d.root_system v hv b hb hD
  have hm i j : t.cartan (e i) (e j) = A i j := by
    apply Int.cast_injective (α := ℝ)
    rw [hA, recover_standard_cartan d.root_system hv hb t e hedge harrow]
  have hcond := Serre.cartanConditions_spec (realRoots H) d.root_system v hv b hb A hA
  exact ⟨t, ⟨(serre_reindex A t.cartan e hm hcond.2.1).symm.trans g⟩⟩

theorem semisimple_classification : semisimpleClassificationType := by
  classical
  intro L _ _ _ h
  obtain ⟨S, hSfin, hS, hSsimple, g, hg⟩ := simple_ideal_lie_decomposition ℂ L h
  subst S
  let S := {I : LieIdeal ℂ L | IsAtom I}
  have model (I : S) : ∃ t : FiniteDynkinType, Nonempty (Model t ≃ₗ⁅ℂ⁆ I.val) := by
    letI := hSsimple I.val I.property
    exact simple_classification I.val
  choose t ht using model
  let f (I : S) := (ht I).some
  let m : (⨁ I : S, Model (t I)) ≃ₗ⁅ℂ⁆ (⨁ I : S, I.val) :=
    { DirectSum.congrLinearEquiv (fun I => (f I).toLinearEquiv) with
      map_lie' := fun {x y} => by
        apply DFinsupp.ext
        intro I
        let m' := DirectSum.congrLinearEquiv (fun I => (f I).toLinearEquiv)
        change (m' ⁅x, y⁆) I = ⁅m' x, m' y⁆ I
        dsimp only [m']
        rw [DirectSum.coe_congrLinearEquiv, DirectSum.bracket_apply,
          DirectSum.lmap_apply, DirectSum.lmap_apply, DirectSum.lmap_apply,
          DirectSum.bracket_apply]
        exact (f I).map_lie (x I) (y I) }
  refine ⟨hSfin, t, f, m.trans g, ?_⟩
  intro I x
  change g (m (DirectSum.of _ I x)) = _
  rw [show m (DirectSum.of (fun J : S => Model (t J)) I x) =
      DirectSum.of (fun J : S => ↥J.val) I (f I x) by
    change DirectSum.congrLinearEquiv (fun I => (f I).toLinearEquiv) _ = _
    rw [DirectSum.coe_congrLinearEquiv]
    exact DirectSum.lmap_lof (fun I => (f I).toLinearEquiv.toLinearMap) I x]
  exact hg I (f I x)


theorem empty_classification : emptyClassificationType := by
  intro L _ _ _
  exact fun (h : Specs.LieAlgebrasAndRepresentations.SolvableRadical.IsSemisimple_value ℂ L) =>
    Set.isEmpty_coe_sort.trans (simple_factors_empty_iff ℂ L (show IsSemisimple ℂ L from h))


section MatrixDimension
attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

variable {ι L : Type*} [Fintype ι] [AddCommGroup L] [Module ℂ L]

private def upperEntries [LinearOrder ι] (f : L →ₗ[ℂ] Matrix ι ι ℂ) :
    L →ₗ[ℂ] ({p : ι × ι // p.1 < p.2} → ℂ) :=
  LinearMap.pi fun p => ((Matrix.entryLinearMap ℂ ℂ p.val.1 p.val.2)).comp f

private def diagonalEntries (f : L →ₗ[ℂ] Matrix ι ι ℂ) : L →ₗ[ℂ] (ι → ℂ) :=
  LinearMap.pi fun p => (Matrix.entryLinearMap ℂ ℂ p p).comp f

omit [Fintype ι] in
private theorem eq_of_upper_and_diagonal [LinearOrder ι] (f : L →ₗ[ℂ] Matrix ι ι ℂ)
    (c : ℂ) (hs : ∀ (x : L) (p q : ι), f x p q = c * f x q p) {x y : L}
    (hu : upperEntries f x = upperEntries f y)
    (hd : ∀ p : ι, f x p p = f y p p) : f x = f y := by
  ext p q
  rcases lt_trichotomy p q with hpq | rfl | hqp
  · exact congrFun hu ⟨(p, q), hpq⟩
  · exact hd p
  · have he : f x q p = f y q p := congrFun hu ⟨(q, p), hqp⟩
    rw [hs x p q, hs y p q, he]

private theorem card_strict_pairs [LinearOrder ι] :
    Fintype.card {p : ι × ι // p.1 < p.2} = (Fintype.card ι).choose 2 := by
  let S : Set (ι × ι) := {p | p.1 < p.2}
  calc
    _ = Fintype.card S := Fintype.card_congr (Equiv.refl _)
    _ = S.toFinset.card := (Set.toFinset_card S).symm
    _ = _ := by
      convert Fintype.card_product_filter_lt (α := ι) using 1
      congr 1
      ext p
      simp [S]

private theorem finrank_le_of_skew (f : L →ₗ[ℂ] Matrix ι ι ℂ)
    (hf : Function.Injective f) (hs : ∀ (x : L) (p q : ι), f x p q = -f x q p) :
    Module.finrank ℂ L ≤ (Fintype.card ι).choose 2 := by
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have he (x : L) (p : ι) : f x p p = 0 := by linear_combination (hs x p p) / 2
  have hu : Function.Injective (upperEntries f) := by
    intro x y h
    apply hf
    apply eq_of_upper_and_diagonal f (-1) (fun x p q => by simpa using hs x p q) h
    intro p
    rw [he x p, he y p]
  simpa only [Module.finrank_fintype_fun_eq_card, card_strict_pairs] using
    LinearMap.finrank_le_finrank_of_injective hu

private theorem finrank_le_of_symmetric (f : L →ₗ[ℂ] Matrix ι ι ℂ)
    (hf : Function.Injective f) (hs : ∀ (x : L) (p q : ι), f x p q = f x q p) :
    Module.finrank ℂ L ≤ (Fintype.card ι).choose 2 + Fintype.card ι := by
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  let F := (upperEntries f).prod (diagonalEntries f)
  have hF : Function.Injective F := by
    intro x y h
    apply hf
    apply eq_of_upper_and_diagonal f 1 (fun x p q => by simpa using hs x p q)
      (congrArg Prod.fst h)
    intro p
    exact congrFun (congrArg Prod.snd h) p
  simpa only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
    card_strict_pairs] using LinearMap.finrank_le_finrank_of_injective hF

private def reindexColumns (op : ι ≃ ι) : Matrix ι ι ℂ ≃ₗ[ℂ] Matrix ι ι ℂ :=
  Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl ι) op.symm

private theorem odd_choose_two (n : ℕ) : (2 * n + 1).choose 2 = n + 2 * n ^ 2 := by
  rw [Nat.choose_two_right]
  apply Nat.div_eq_of_eq_mul_right (by decide : 0 < 2)
  rw [Nat.add_sub_cancel]
  ring

private theorem even_choose_two (n : ℕ) : (2 * n).choose 2 = n + 2 * n * (n - 1) := by
  rw [Nat.choose_two_right]
  apply Nat.div_eq_of_eq_mul_right (by decide : 0 < 2)
  cases n with
  | zero => decide
  | succ n =>
    have h : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
    rw [h, Nat.add_sub_cancel]
    ring

private theorem even_choose_two_add (n : ℕ) : (2 * n).choose 2 + 2 * n = n + 2 * n ^ 2 := by
  rw [Nat.choose_two_right]
  have h : 2 * n * (2 * n - 1) / 2 = n * (2 * n - 1) := by
    apply Nat.div_eq_of_eq_mul_right (by decide : 0 < 2)
    ring
  rw [h]
  cases n with
  | zero => decide
  | succ n =>
    have h : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
    rw [h]
    ring


private theorem finrank_classical_b_le (n : ℕ) :
    Module.finrank ℂ (Specs.LieAlgebrasAndRepresentations.ClassicalRootsB.algebra n) ≤
      n + 2 * n ^ 2 := by
  open Specs.LieAlgebrasAndRepresentations.ClassicalRootsB in
  let op : Index n ≃ Index n := ⟨opposite, opposite, opposite_opposite, opposite_opposite⟩
  let f := (reindexColumns op).toLinearMap.comp (algebra n).toSubmodule.subtype
  have hf : Function.Injective f := (reindexColumns op).injective.comp Subtype.val_injective
  have hs (x : algebra n) (p q : Index n) : f x p q = -f x q p := by
    change x.val p (opposite q) = -x.val q (opposite p)
    simpa only [opposite_opposite] using
      (ClassicalRootsB.algebra_entries n x.val).mp x.property p (opposite q)
  have h := finrank_le_of_skew f hf hs
  rw [(ClassicalRootsB.form_properties n).2.2, odd_choose_two] at h
  exact h

private theorem finrank_classical_d_le (n : ℕ) :
    Module.finrank ℂ (Specs.LieAlgebrasAndRepresentations.ClassicalRootsD.algebra n) ≤
      n + 2 * n * (n - 1) := by
  open Specs.LieAlgebrasAndRepresentations.ClassicalRootsD in
  let op : Idx n ≃ Idx n := Equiv.sumComm _ _
  let f := (reindexColumns op).toLinearMap.comp (algebra n).toSubmodule.subtype
  have hf : Function.Injective f := (reindexColumns op).injective.comp Subtype.val_injective
  have hs (x : algebra n) (p q : Idx n) : f x p q = -f x q p := by
    change x.val p (op q) = -x.val q (op p)
    obtain ⟨h₁, h₂, h₃⟩ := (ClassicalRootsD.mem_algebra x.val).mp x.property
    cases p with
    | inl i =>
      cases q with
      | inl j => exact h₂ i j
      | inr j => exact neg_eq_iff_eq_neg.mp (h₁ j i).symm
    | inr i =>
      cases q with
      | inl j => exact h₁ i j
      | inr j => exact h₃ i j
  have h := finrank_le_of_skew f hf hs
  have hcard : Fintype.card (Idx n) = 2 * n := by simp [Idx]; omega
  rw [hcard, even_choose_two] at h
  exact h

private def scaleMatrixRows {ι : Type*} (c : ι → ℂ) :
    Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun x p q := c p * x p q
  map_add' x y := by ext p q; exact mul_add _ _ _
  map_smul' a x := by
    ext p q
    change c p * (a * x p q) = a * (c p * x p q)
    ring

private theorem scaleMatrixRows_injective {ι : Type*} (c : ι → ℂ) (hc : ∀ p, c p ≠ 0) :
    Function.Injective (scaleMatrixRows c) := by
  intro x y h
  ext p q
  exact mul_left_cancel₀ (hc p) (congrArg (fun Z : Matrix ι ι ℂ => Z p q) h)

open private entry_relations from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClassicalRootsC

private theorem finrank_classical_c_le (n : ℕ) :
    Module.finrank ℂ (Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.sp n) ≤
      n + 2 * n ^ 2 := by
  open Specs.LieAlgebrasAndRepresentations.ClassicalRootsC in
  let op : Fin n ⊕ Fin n ≃ Fin n ⊕ Fin n := Equiv.sumComm _ _
  let signs : Fin n ⊕ Fin n → ℂ := Sum.elim (fun _ => 1) fun _ => -1
  let f := (scaleMatrixRows signs).comp <|
    (reindexColumns op).toLinearMap.comp (sp n).toSubmodule.subtype
  have hsign (p : Fin n ⊕ Fin n) : signs p ≠ 0 := by cases p <;> simp [signs]
  have hf : Function.Injective f := (scaleMatrixRows_injective signs hsign).comp <|
    (reindexColumns op).injective.comp Subtype.val_injective
  have hs (x : sp n) (p q : Fin n ⊕ Fin n) : f x p q = f x q p := by
    change signs p * x.val p (op q) = signs q * x.val q (op p)
    obtain ⟨h₁, h₂, h₃⟩ := entry_relations x.val x.property
    cases p with
    | inl i =>
      cases q with
      | inl j => simpa [signs, op] using h₂ i j
      | inr j => simp [signs, op, h₁]
    | inr i =>
      cases q with
      | inl j => simp [signs, op, h₁]
      | inr j => simpa [signs, op] using h₃ i j
  have h := finrank_le_of_symmetric f hf hs
  have hcard : Fintype.card (Fin n ⊕ Fin n) = 2 * n := by simp; omega
  rw [hcard, even_choose_two_add] at h
  exact h

end MatrixDimension

section ClassicalModels
open Serre

private theorem serre_relations_of_triples {ι L : Type*} [DecidableEq ι]
    [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (A : Matrix ι ι ℤ) (E F H : ι → L) (hOff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hh : ∀ i j, ⁅H i, H j⁆ = 0)
    (he : ∀ i j, ⁅H i, E j⁆ = (A i j : ℂ) • E j)
    (hf : ∀ i j, ⁅H i, F j⁆ = -((A i j : ℂ) • F j))
    (hef : ∀ i j, ⁅E i, F j⁆ = if i = j then H i else 0)
    (hsl2 : ∀ i, IsSl2Triple (H i) (E i) (F i)) : RelationsHold A E F H := by
  refine ⟨hh, (fun i j => by simpa only [Int.cast_smul_eq_zsmul] using he i j),
    (fun i j => by simpa only [Int.cast_smul_eq_zsmul] using hf i j), hef, ?_, ?_⟩
  · intro i j hij
    by_cases hz : E j = 0
    · rw [hz]
      induction (1 - A i j).toNat with
      | zero => rfl
      | succ n ih => rw [iterBracket, ih, lie_zero]
    let t := (hsl2 i).symm
    have hzero : ⁅F i, E j⁆ = 0 := by rw [← lie_skew, hef j i, ite_eq_right hij.symm, neg_zero]
    have hw : t.HasPrimitiveVectorWith (E j) (-(A i j : ℂ)) :=
      ⟨hz, by rw [neg_lie, he, neg_smul], hzero⟩
    have hle : 0 ≤ -A i j := neg_nonneg.mpr (hOff i j hij)
    have hn : (-(A i j : ℂ)) = (((-A i j).toNat : ℕ) : ℂ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hle, Int.cast_neg]
    rw [Serre.iterBracket_eq_pow, show (1 - A i j).toNat = (-A i j).toNat + 1 by omega]
    exact hw.pow_toEnd_f_eq_zero_of_eq_nat hn
  · intro i j hij
    by_cases hz : F j = 0
    · rw [hz]
      induction (1 - A i j).toNat with
      | zero => rfl
      | succ n ih => rw [iterBracket, ih, lie_zero]
    have hw : (hsl2 i).HasPrimitiveVectorWith (F j) (-(A i j : ℂ)) :=
      ⟨hz, by rw [hf, neg_smul], by rw [hef i j, ite_eq_right hij]⟩
    have hle : 0 ≤ -A i j := neg_nonneg.mpr (hOff i j hij)
    have hn : (-(A i j : ℂ)) = (((-A i j).toNat : ℕ) : ℂ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hle, Int.cast_neg]
    rw [Serre.iterBracket_eq_pow, show (1 - A i j).toNat = (-A i j).toNat + 1 by omega]
    exact hw.pow_toEnd_f_eq_zero_of_eq_nat hn
private theorem equivalence_of_triple_hom {ι L : Type*} [DecidableEq ι]
    [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (A : Matrix ι ι ℤ) [FiniteDimensional ℂ (Algebra A)] [LieAlgebra.IsSimple ℂ (Algebra A)]
    (g : Algebra A →ₗ⁅ℂ⁆ L) (hne : ∃ x, g x ≠ 0)
    (hdim : finrank ℂ L ≤ finrank ℂ (Algebra A)) : Nonempty (Algebra A ≃ₗ⁅ℂ⁆ L) := by
  have hginj : Function.Injective g := by
    apply (LieHom.ker_eq_bot g).mp
    rcases LieAlgebra.IsSimple.eq_bot_or_eq_top g.ker with h | h
    · exact h
    · obtain ⟨x, hx⟩ := hne
      exact (hx (LieHom.mem_ker.mp (h ▸ LieSubmodule.mem_top x))).elim
  have hle := LinearMap.finrank_le_finrank_of_injective (f := g.toLinearMap) hginj
  have heq := le_antisymm hle hdim
  exact ⟨LieEquiv.ofBijective g ⟨hginj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mp hginj⟩⟩

section ClassicalA

open Specs.LieAlgebrasAndRepresentations.ClassicalRootsA
open LieAlgebrasAndRepresentations.ClassicalRootsA

private theorem a_indices_ne {n : ℕ} (i : Fin n) : i.castSucc ≠ i.succ := by
  intro h
  have := congrArg Fin.val h
  simp at this

private def aE {n : ℕ} (i : Fin n) : sl n := rootVector n i.castSucc i.succ (a_indices_ne i)
private def aF {n : ℕ} (i : Fin n) : sl n := rootVector n i.succ i.castSucc (a_indices_ne i).symm
private def aH {n : ℕ} (i : Fin n) : cartan n :=
  killingCoroot (cartan n) (root n i.castSucc i.succ)

private theorem aH_eq {n : ℕ} (i : Fin n) :
    aH i = Specs.LieAlgebrasAndRepresentations.ClassicalRootsA.coroot n i.castSucc i.succ :=
  killing_coroot n i.castSucc i.succ (a_indices_ne i)

private theorem a_cartan_entry {n : ℕ} (i j : Fin n) :
    root n j.castSucc j.succ (aH i) = (CartanMatrix.A n i j : ℂ) := by
  have h := a_indices_ne i
  by_cases hij : i = j
  · subst j
    norm_num [aH_eq, Matrix.single, h, h.symm, CartanMatrix.A]
  simp only [root_apply, aH_eq, coroot_apply, Matrix.single, Matrix.of_apply,
    Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, CartanMatrix.A]
  split_ifs <;> norm_num <;> omega

private theorem a_mixed_bracket {n : ℕ} (i j : Fin n) :
    ⁅aE i, aF j⁆ = if i = j then (aH i : sl n) else 0 := by
  by_cases hij : i = j
  · subst j
    simpa [aE, aF, aH_eq] using opposite_bracket i.castSucc i.succ (a_indices_ne i)
  rw [ite_eq_right hij]
  apply Subtype.ext
  have hs : i.succ ≠ j.succ := fun e => hij (Fin.succ_injective _ e)
  have hc : j.castSucc ≠ i.castSucc := fun e => hij (Fin.castSucc_injective _ e).symm
  change Matrix.single i.castSucc i.succ (1 : ℂ) * Matrix.single j.succ j.castSucc 1 -
    Matrix.single j.succ j.castSucc 1 * Matrix.single i.castSucc i.succ 1 = 0
  rw [Matrix.single_mul_single_of_ne 1 i.castSucc i.succ j.succ hs 1,
    Matrix.single_mul_single_of_ne 1 j.succ j.castSucc i.castSucc hc 1, sub_self]

private theorem a_coroot_ne {n : ℕ} (i : Fin n) : (aH i : sl n) ≠ 0 := by
  obtain ⟨hss, hH⟩ := ClassicalMatrixCartans.type_a n
  let α := root n i.castSucc i.succ
  have hα : α ∈ rootSet (cartan n) :=
    (root_set n α).mpr ⟨i.castSucc, i.succ, a_indices_ne i, rfl⟩
  have hpair : α (aH i) = 2 := by
    change α (killingCoroot (cartan n) α) = 2
    rw [killingCoroot_pairing hss _ hH,
      mul_div_cancel_right₀ _ (rootForm_self_ne_zero hss _ hH _ hα)]
  intro h
  have hz : aH i = 0 := Subtype.ext h
  rw [hz, map_zero] at hpair
  norm_num at hpair

private theorem a_dim (n : ℕ) : Module.finrank ℂ (sl n) = n + n * (n+1) := by
  let m := Matrix.traceLinearMap (Fin (n+1)) ℂ ℂ
  have hs : Function.Surjective m := fun c => ⟨Matrix.single 0 0 c, by simp [m]⟩
  have h := m.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_self,
    Module.finrank_matrix, Module.finrank_self, mul_one] at h
  simp only [Fintype.card_fin] at h
  change 1 + Module.finrank ℂ (sl n) = (n+1) * (n+1) at h
  nlinarith only [h]

private theorem a_relations (n : ℕ) :
    RelationsHold (CartanMatrix.A n) (@aE n) (@aF n) (fun i => (aH i : sl n)) := by
  have hoff (i j : Fin n) (hij : i ≠ j) : CartanMatrix.A n i j ≤ 0 := by
    simp only [CartanMatrix.A, Matrix.of_apply, ite_eq_right hij]
    split_ifs <;> decide
  have he (i j : Fin n) : ⁅(aH i : sl n), aE j⁆ = (CartanMatrix.A n i j : ℂ) • aE j := by
    rw [← a_cartan_entry]
    exact (LieAlgebrasAndRepresentations.mem_rootSpace _ _ _).mp (rootVector_mem _ _ (a_indices_ne j)) (aH i)
  have hf (i j : Fin n) : ⁅(aH i : sl n), aF j⁆ = -((CartanMatrix.A n i j : ℂ) • aF j) := by
    rw [← a_cartan_entry]
    have h := (LieAlgebrasAndRepresentations.mem_rootSpace _ _ _).mp (rootVector_mem _ _ (a_indices_ne j).symm) (aH i)
    rw [← neg_smul, root_apply, neg_sub]
    exact h
  have hh (i j : Fin n) : ⁅(aH i : sl n), (aH j : sl n)⁆ = 0 := by
    exact congrArg Subtype.val (trivial_lie_zero (cartan n) (cartan n) (aH i) (aH j))
  refine serre_relations_of_triples _ _ _ _ hoff hh he hf a_mixed_bracket ?_
  intro i
  obtain ⟨heq, hpos, hneg⟩ := root_triple n i.castSucc i.succ (a_indices_ne i)
  exact ⟨a_coroot_ne i, by simpa only [aE, aF, aH_eq] using heq,
    by simpa only [aE, aH_eq, two_smul] using hpos,
    by simpa only [aF, aH_eq, neg_smul, two_smul] using hneg⟩

private theorem classical_a_of_model (n : ℕ) (hn : 1 ≤ n)
    [FiniteDimensional ℂ (Algebra (CartanMatrix.A n))]
    [LieAlgebra.IsSimple ℂ (Algebra (CartanMatrix.A n))]
    (hdim : n + n * (n+1) ≤ Module.finrank ℂ (Algebra (CartanMatrix.A n))) :
    Nonempty (Algebra (CartanMatrix.A n) ≃ₗ⁅ℂ⁆ sl n) := by
  have hoff (i j : Fin n) (hij : i ≠ j) : CartanMatrix.A n i j ≤ 0 := by
    simp only [CartanMatrix.A, Matrix.of_apply, ite_eq_right hij]
    split_ifs <;> decide
  let g := Serre.lift (CartanMatrix.A n) hoff (@aE n) (@aF n) _ (a_relations n)
  let i : Fin n := ⟨0, by omega⟩
  exact equivalence_of_triple_hom _ g ⟨Serre.h _ i, by simpa [g] using a_coroot_ne i⟩
    (a_dim n ▸ hdim)
end ClassicalA

section SignedCoordinates
open ClassicalCoordinates (Space epsilon)

private def ofRealCoordinates {n : ℕ} (x : Space n) : Fin n → ℂ := fun i => (x i : ℂ)

private def coordinateWeightMap (n : ℕ) : Space n →ₗ[ℝ] Module.Dual ℂ (Fin n → ℂ) where
  toFun x := ∑ i, (x i : ℂ) • LinearMap.proj i
  map_add' x y := by
    apply LinearMap.ext
    intro t
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul,
      LinearMap.add_apply, PiLp.add_apply, Complex.ofReal_add, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    apply LinearMap.ext
    intro t
    simp [PiLp.smul_apply, Complex.ofReal_mul, mul_assoc, Finset.mul_sum, Algebra.smul_def]

@[simp] private theorem coordinateWeightMap_apply {n : ℕ} (x : Space n) (t : Fin n → ℂ) :
    coordinateWeightMap n x t = ∑ i, (x i : ℂ) * t i := by
  simp [coordinateWeightMap]

@[simp] private theorem coordinateWeightMap_apply_single {n : ℕ} (x : Space n) (i : Fin n) :
    coordinateWeightMap n x (Pi.single i 1) = (x i : ℂ) := by
  rw [coordinateWeightMap_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

@[simp] private theorem coordinateWeightMap_epsilon {n : ℕ} (i : Fin n) :
    coordinateWeightMap n (epsilon i) = LinearMap.proj i := by
  apply LinearMap.ext
  intro t
  simp only [coordinateWeightMap_apply, epsilon, PiLp.single_apply, LinearMap.proj_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

private theorem coordinateWeightMap_inj (n : ℕ) : Function.Injective (coordinateWeightMap n) := by
  intro a b h
  ext i
  exact Complex.ofReal_injective (by simpa only [coordinateWeightMap_apply_single] using congrArg (fun w : Module.Dual ℂ (Fin n → ℂ) => w (Pi.single i 1)) h)

private theorem coordinateWeightMap_inner {n : ℕ} (a b : Space n) :
    coordinateWeightMap n a (ofRealCoordinates b) = (inner ℝ a b : ℂ) := by
  simp [PiLp.inner_apply, ofRealCoordinates, RCLike.inner_apply, mul_comm]

private theorem coordinateWeightMap_cartan {n : ℕ} (b : Fin n → Space n) (i j : Fin n) :
    coordinateWeightMap n (b j) (ofRealCoordinates (coroot (b i))) =
      (cartanMatrix b i j : ℂ) := by
  rw [coordinateWeightMap_inner]
  simp [cartanMatrix, rootCartan, coroot, inner_smul_right, div_eq_mul_inv]
  ring

private theorem simple_diff_not_in_roots {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {R : Set E} (hR : IsRootSystem R) {z : E}
    (hz : RootRegular R z) {ι : Type*} {b : Basis ι ℝ E} (hb : IsSimpleBasis R z b)
    (i j : ι) : b i - b j ∉ R := by
  intro hr
  have hi : b i ∈ simpleRoots R z := hb ▸ ⟨i, rfl⟩
  have hj : b j ∈ simpleRoots R z := hb ▸ ⟨j, rfl⟩
  rcases lt_or_gt_of_ne (hz _ hr) with h | h
  · have hn : -(b i - b j) ∈ positiveRoots R z := by
      refine ⟨hR.toRootAxioms.neg_mem hr, ?_⟩
      rw [inner_neg_right, neg_pos]
      exact h
    exact hj.2 _ hn _ hi.1 (by abel)
  · exact hi.2 _ ⟨hr, h⟩ _ hj.1 (by abel)

private theorem coordinate_matrix_equiv {n : ℕ} {L : Type*} [LieRing L]
    [LieAlgebra ℂ L] [FiniteDimensional ℂ L] (R : Set (Space n)) (hR : IsRootSystem R)
    (z : Space n) (hz : RootRegular R z) (b : Basis (Fin n) ℝ (Space n))
    (hb : IsSimpleBasis R z b) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ i j, (A i j : ℝ) = cartanMatrix b i j)
    [FiniteDimensional ℂ (Algebra A)] [LieAlgebra.IsSimple ℂ (Algebra A)]
    (hn : 0 < n) (hdim : Module.finrank ℂ L ≤ Module.finrank ℂ (Algebra A))
    (d : (Fin n → ℂ) →ₗ[ℂ] L) (H : LieSubalgebra ℂ L)
    (e : (Fin n → ℂ) ≃ₗ[ℂ] H) (hd : ∀ t, (e t : L) = d t)
    (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (hcoordinate : ∀ i,
      let a := (coordinateWeightMap n (b i)).comp e.symm.toLinearMap
      a ∈ rootSet H ∧
        (killingCoroot H a : L) = d (ofRealCoordinates (coroot (b i))))
    (hsupport : ∀ (w : Module.Dual ℂ (Fin n → ℂ)) (X : L), w ≠ 0 → X ≠ 0 →
      (∀ t, ⁅d t, X⁆ = w t • X) → w ∈ coordinateWeightMap n '' R) :
    Nonempty (Algebra A ≃ₗ⁅ℂ⁆ L) := by
  classical
  let a (i : Fin n) := (coordinateWeightMap n (b i)).comp e.symm.toLinearMap
  choose E F hEroot hFroot hEnz hFnz hEF hHE hHF using
    fun i => exists_root_triple hss H hH (a i) (hcoordinate i).1
  let C (i : Fin n) := d (ofRealCoordinates (coroot (b i)))
  have hc (i : Fin n) : (killingCoroot H (a i) : L) = C i := (hcoordinate i).2
  have hsl2 (i : Fin n) : IsSl2Triple (C i) (E i) (F i) := by
    refine ⟨?_, (hEF i).trans (hc i), ?_, ?_⟩
    · intro hz
      have he := hHE i
      rw [hc i, hz, zero_lie] at he
      exact hEnz i ((smul_eq_zero.mp he.symm).resolve_left (by norm_num))
    · simpa only [hc i, two_smul] using hHE i
    · simpa only [hc i, neg_smul, two_smul] using hHF i
  have hE (i : Fin n) (t : Fin n → ℂ) : ⁅d t, E i⁆ = coordinateWeightMap n (b i) t • E i := by
    simpa [a, hd] using
      (LieAlgebrasAndRepresentations.mem_rootSpace H _ _).mp (hEroot i) (e t)
  have hF (i : Fin n) (t : Fin n → ℂ) : ⁅d t, F i⁆ = -(coordinateWeightMap n (b i) t • F i) := by
    simpa [a, hd, neg_smul] using
      (LieAlgebrasAndRepresentations.mem_rootSpace H _ _).mp (hFroot i) (e t)
  have hoff := (Serre.cartanConditions_spec R hR z hz b hb A hA).2.1
  let _ : IsLieAbelian H := hH.1.1
  have hh (i j : Fin n) : ⁅C i, C j⁆ = 0 := by
    rw [← hc i, ← hc j]
    exact congrArg Subtype.val (trivial_lie_zero H H (killingCoroot H (a i)) (killingCoroot H (a j)))
  have he (i j : Fin n) : ⁅C i, E j⁆ = (A i j : ℂ) • E j := by
    change ⁅d (ofRealCoordinates (coroot (b i))), E j⁆ = _
    rw [hE, coordinateWeightMap_cartan, ← hA, Complex.ofReal_intCast]
  have hf (i j : Fin n) : ⁅C i, F j⁆ = -((A i j : ℂ) • F j) := by
    change ⁅d (ofRealCoordinates (coroot (b i))), F j⁆ = _
    rw [hF, coordinateWeightMap_cartan, ← hA, Complex.ofReal_intCast]
  have hef (i j : Fin n) : ⁅E i, F j⁆ = if i = j then C i else 0 := by
    by_cases hij : i = j
    · subst j
      simpa using (hsl2 i).lie_e_f
    rw [ite_eq_right hij]
    by_contra hne
    have hwne : coordinateWeightMap n (b i - b j) ≠ 0 := by
      intro hw
      rw [← (coordinateWeightMap n).map_zero] at hw
      exact hij (b.injective (sub_eq_zero.mp (coordinateWeightMap_inj n hw)))
    have hw (t : Fin n → ℂ) :
        ⁅d t, ⁅E i, F j⁆⁆ = coordinateWeightMap n (b i - b j) t • ⁅E i, F j⁆ := by
      rw [leibniz_lie, hE, hF, smul_lie, lie_neg, lie_smul, ← sub_eq_add_neg, ← sub_smul,
        map_sub, LinearMap.sub_apply]
    obtain ⟨c, hc, heq⟩ := hsupport _ _ hwne hne hw
    exact simple_diff_not_in_roots hR hz hb i j ((coordinateWeightMap_inj n heq) ▸ hc)
  let g := Serre.lift A hoff E F C (serre_relations_of_triples A E F C hoff hh he hf hef hsl2)
  let i : Fin n := ⟨0, hn⟩
  exact equivalence_of_triple_hom A g ⟨Serre.h A i, by
    simpa [g, C] using (hsl2 i).h_ne_zero⟩ hdim

private theorem coordinate_pair_weights {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    let p : Module.Dual ℂ (Fin n → ℂ) := LinearMap.proj i
    let q : Module.Dual ℂ (Fin n → ℂ) := LinearMap.proj j
    p + q ∈ coordinateWeightMap n '' ClassicalCoordinates.pairRoots n ∧
    p - q ∈ coordinateWeightMap n '' ClassicalCoordinates.pairRoots n ∧
    -p + q ∈ coordinateWeightMap n '' ClassicalCoordinates.pairRoots n ∧
    -p - q ∈ coordinateWeightMap n '' ClassicalCoordinates.pairRoots n := by
  have m (s t : Bool) : ClassicalCoordinates.sign s • LinearMap.proj (R := ℂ) i +
      ClassicalCoordinates.sign t • LinearMap.proj (R := ℂ) j ∈
        coordinateWeightMap n '' ClassicalCoordinates.pairRoots n := by
    refine ⟨_, ⟨i, j, hij, s, t, rfl⟩, ?_⟩
    simp
  exact ⟨by simpa [ClassicalCoordinates.sign] using m false false,
    by simpa [ClassicalCoordinates.sign, sub_eq_add_neg] using m false true,
    by simpa [ClassicalCoordinates.sign] using m true false,
    by simpa [ClassicalCoordinates.sign, sub_eq_add_neg] using m true true⟩

private theorem coordinate_axis_weights {n : ℕ} (i : Fin n) (c : ℝ) :
    let p : Module.Dual ℂ (Fin n → ℂ) := LinearMap.proj i
    ((c : ℂ) • p) ∈ coordinateWeightMap n '' ClassicalCoordinates.axisRoots n c ∧
    -((c : ℂ) • p) ∈ coordinateWeightMap n '' ClassicalCoordinates.axisRoots n c := by
  have m (s : Bool) : (c * ClassicalCoordinates.sign s) • LinearMap.proj (R := ℂ) i ∈
        coordinateWeightMap n '' ClassicalCoordinates.axisRoots n c := by
    refine ⟨_, ⟨i, s, rfl⟩, ?_⟩
    simp
  exact ⟨by simpa [ClassicalCoordinates.sign, Complex.real_smul] using m false,
    by simpa [ClassicalCoordinates.sign, Complex.real_smul] using m true⟩

private theorem ofRealCoordinates_coroot {n : ℕ} (x : Space n) :
    ofRealCoordinates (coroot x) = fun i => (2 / (∑ j, (coordinateWeightMap n x (Pi.single j 1)) ^ 2)) *
      coordinateWeightMap n x (Pi.single i 1) := by
  funext i
  simp only [ofRealCoordinates, coroot, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_ofNat, coordinateWeightMap_apply_single]
  congr 2
  rw [PiLp.inner_apply, Complex.ofReal_sum]
  simp [pow_two]

section Symplectic

open Specs.LieAlgebrasAndRepresentations.ClassicalRootsC
open LieAlgebrasAndRepresentations.ClassicalRootsC
open ClassicalCoordinates (rootsC simpleC)

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

private def symplecticDiagonal (n : ℕ) : V n →ₗ[ℂ] sp n :=
  (diagonalMap n).codRestrict (sp n).toSubmodule (diagonal_mem n)

private theorem coordinateWeightMap_eps {n : ℕ} (i : Fin n) :
    coordinateWeightMap n (epsilon i) = eps i :=
  coordinateWeightMap_epsilon i

private theorem coordinateWeightMap_two_eps {n : ℕ} (i : Fin n) :
    coordinateWeightMap n ((2 : ℝ) • epsilon i) = (2 : ℂ) • eps i := by
  rw [two_smul, map_add, coordinateWeightMap_eps, two_smul]

private theorem symplectic_weight_support (n : ℕ)
    (w : Module.Dual ℂ (Fin n → ℂ)) (X : sp n) (hw : w ≠ 0) (hX : X ≠ 0)
    (h : ∀ t, ⁅symplecticDiagonal n t, X⁆ = w t • X) :
    w ∈ coordinateWeightMap n '' rootsC n := by
  have hXmem : X.val ∈ Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.rootSpace w :=
    ⟨X.property, fun t => congrArg Subtype.val (h t)⟩
  have hwt : w ∈ Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.rootSet n := ⟨hw, fun hz => hX (Subtype.ext (by
    rw [hz, Submodule.mem_bot] at hXmem
    exact hXmem))⟩
  rw [roots n] at hwt
  rcases hwt with ⟨i, hpos | hneg⟩ | ⟨i, j, hij, h1 | h2 | h3 | h4⟩
  · refine ⟨(2 : ℝ) • epsilon i, Or.inl ⟨i, false, ?_⟩, ?_⟩
    · simp [ClassicalCoordinates.sign]
    · rw [coordinateWeightMap_two_eps, hpos]
  · refine ⟨-((2 : ℝ) • epsilon i), Or.inl ⟨i, true, ?_⟩, ?_⟩
    · simp [ClassicalCoordinates.sign, neg_smul]
    · rw [map_neg, coordinateWeightMap_two_eps, hneg]
  · refine ⟨epsilon i - epsilon j, Or.inr ⟨i, j, hij.ne, false, true, ?_⟩, ?_⟩
    · simp [ClassicalCoordinates.sign, sub_eq_add_neg]
    · rw [map_sub, coordinateWeightMap_eps, coordinateWeightMap_eps, h1]
  · refine ⟨-(epsilon i - epsilon j), Or.inr ⟨i, j, hij.ne, true, false, ?_⟩, ?_⟩
    · simp [ClassicalCoordinates.sign, sub_eq_add_neg, add_comm]
    · rw [map_neg, map_sub, coordinateWeightMap_eps, coordinateWeightMap_eps, h2]
  · refine ⟨epsilon i + epsilon j, Or.inr ⟨i, j, hij.ne, false, false, ?_⟩, ?_⟩
    · simp [ClassicalCoordinates.sign]
    · rw [map_add, coordinateWeightMap_eps, coordinateWeightMap_eps, h3]
  · refine ⟨-(epsilon i + epsilon j), Or.inr ⟨i, j, hij.ne, true, true, ?_⟩, ?_⟩
    · simp [ClassicalCoordinates.sign, add_comm]
    · rw [map_neg, map_add, coordinateWeightMap_eps, coordinateWeightMap_eps, h4]

private theorem c_simple_is_root (n : ℕ) (i : Fin n) :
    coordinateWeightMap n (simpleC n i) ∈ Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.rootSet n := by
  rw [roots n]
  unfold simpleC
  split
  · rename_i hi
    let j : Fin n := ⟨i.val + 1, hi⟩
    refine Or.inr ⟨i, j, Fin.lt_def.mpr (Nat.lt_succ_self i.val), Or.inl ?_⟩
    rw [map_sub, coordinateWeightMap_eps, coordinateWeightMap_eps]
  · refine Or.inl ⟨i, Or.inl ?_⟩
    simpa only [← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_ofNat] using coordinateWeightMap_two_eps i

private theorem classical_c_of_realization (n : ℕ) (hn : 2 ≤ n)
    (z : Space n) (b : Basis (Fin n) ℝ (Space n))
    (hbForm : ∀ i, b i = simpleC n i) (hz : RootRegular (rootsC n) z)
    (hb : IsSimpleBasis (rootsC n) z b)
    (hA : ∀ i j, (CartanMatrix.B n i j : ℝ) = cartanMatrix b i j)
    [FiniteDimensional ℂ (Algebra (CartanMatrix.B n))]
    [LieAlgebra.IsSimple ℂ (Algebra (CartanMatrix.B n))]
    (hdim : Module.finrank ℂ (sp n) ≤ finrank ℂ (Algebra (CartanMatrix.B n))) :
    Nonempty (Algebra (CartanMatrix.B n) ≃ₗ⁅ℂ⁆ sp n) := by
  obtain ⟨hss, H, e, hH, he, hmem, hcoroot⟩ := ClassicalMatrixCartans.type_c n
  have hd (t : V n) : (e t : sp n) = symplecticDiagonal n t := Subtype.ext (he t)
  refine coordinate_matrix_equiv (rootsC n) (ClassicalCoordinates.rootSystemC n hn) z hz b hb
    (CartanMatrix.B n) hA (by omega) hdim (symplecticDiagonal n) H e hd hss hH
    ?_ (symplectic_weight_support n)
  intro i
  dsimp only
  have hi : coordinateWeightMap n (b i) ∈
      Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.rootSet n := by
    rw [hbForm]
    exact c_simple_is_root n i
  refine ⟨(hmem _).mpr hi, ?_⟩
  have hc := hcoroot _ hi
  apply Subtype.ext
  change _ = diagonal (ofRealCoordinates (LieAlgebrasAndRepresentations.coroot (b i)))
  simpa only [Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.coroot, euclidean, coordinates,
    ofRealCoordinates_coroot, pow_two] using hc

end Symplectic

end SignedCoordinates

section ClassicalB

attribute [local instance 100] LieRing.ofAssociativeRing

open Specs.LieAlgebrasAndRepresentations.ClassicalRootsB (Index Mat Parameters Weight algebra epsilon diagonal weightSpace roots listedRoots)
open LieAlgebrasAndRepresentations.ClassicalRootsB

private def bDiagonal (n : ℕ) : Parameters n →ₗ[ℂ] algebra n :=
  (diagonal n).codRestrict (algebra n).toSubmodule (diagonal_mem n)

private theorem b_support (n : ℕ) (w : Weight n) (X : algebra n)
    (hw : w ≠ 0) (hX : X ≠ 0) (h : ∀ t, ⁅bDiagonal n t, X⁆ = w t • X) :
    w ∈ coordinateWeightMap n '' ClassicalCoordinates.rootsB n := by
  have hm : (X : Mat n) ∈ weightSpace w := (mem_weightSpace w X.val).mpr
    ⟨X.property, fun t => congrArg Subtype.val (h t)⟩
  have hr : w ∈ roots n := ⟨hw, fun he => hX (Subtype.ext (by simpa [he] using hm))⟩
  rw [roots_eq n] at hr
  change w ∈ coordinateWeightMap n '' (ClassicalCoordinates.axisRoots n 1 ∪ ClassicalCoordinates.pairRoots n)
  rw [Set.image_union]
  rcases hr with ⟨i, rfl | rfl⟩ | ⟨i, j, hij, rfl | rfl | rfl | rfl⟩
  · exact Or.inl (by simpa [epsilon] using (coordinate_axis_weights i 1).1)
  · exact Or.inl (by simpa [epsilon] using (coordinate_axis_weights i 1).2)
  · exact Or.inr (coordinate_pair_weights i j hij.ne).1
  · exact Or.inr (coordinate_pair_weights i j hij.ne).2.1
  · exact Or.inr (coordinate_pair_weights i j hij.ne).2.2.1
  · exact Or.inr (coordinate_pair_weights i j hij.ne).2.2.2

private theorem b_simple_is_root (n : ℕ) (i : Fin n) :
    coordinateWeightMap n (ClassicalCoordinates.simpleB n i) ∈ roots n := by
  rw [roots_eq n]
  by_cases hs : i.val + 1 < n
  · let j : Fin n := ⟨i.val + 1, hs⟩
    have h : i < j := Fin.lt_def.mpr (Nat.lt_succ_self i.val)
    refine Or.inr ⟨i, j, h, Or.inr (Or.inl ?_)⟩
    simp [ClassicalCoordinates.simpleB, epsilon, hs, j]
  · refine Or.inl ⟨i, Or.inl ?_⟩
    simp [ClassicalCoordinates.simpleB, epsilon, hs]

private theorem classical_b_of_model (n : ℕ) (hn : 2 ≤ n)
    (z : ClassicalCoordinates.Space n) (hz : RootRegular (ClassicalCoordinates.rootsB n) z)
    (b : Basis (Fin n) ℝ (ClassicalCoordinates.Space n))
    (hb : IsSimpleBasis (ClassicalCoordinates.rootsB n) z b)
    (hbi : ∀ i, b i = ClassicalCoordinates.simpleB n i)
    (hA : ∀ i j, (CartanMatrix.C n i j : ℝ) = cartanMatrix b i j)
    [FiniteDimensional ℂ (Algebra (CartanMatrix.C n))] [LieAlgebra.IsSimple ℂ (Algebra (CartanMatrix.C n))]
    (hdim : Module.finrank ℂ (algebra n) ≤ Module.finrank ℂ (Algebra (CartanMatrix.C n))) :
    Nonempty (Algebra (CartanMatrix.C n) ≃ₗ⁅ℂ⁆ algebra n) := by
  obtain ⟨hss, hH, hmem, hcoroot⟩ := ClassicalMatrixCartans.type_b n
  let H := Specs.LieAlgebrasAndRepresentations.ClassicalRootsB.cartan n
  let coordinates := Specs.LieAlgebrasAndRepresentations.ClassicalRootsB.coordinates n
  let e : Parameters n ≃ₗ[ℂ] H :=
    (LinearEquiv.ofBijective coordinates (cartan_identification n).1).symm
  have hd (t : Parameters n) : (e t : algebra n) = bDiagonal n t := by
    apply Subtype.ext
    exact (cartan_reconstruction (e t)).symm.trans
      (congrArg (diagonal n) (e.symm_apply_apply t))
  refine coordinate_matrix_equiv _ (ClassicalCoordinates.rootSystemB n hn) z hz b hb _ hA
    (by omega) hdim (bDiagonal n) H e hd hss hH ?_ (b_support n)
  intro i
  dsimp only
  have hi : coordinateWeightMap n (b i) ∈ roots n := by
    rw [hbi]
    exact b_simple_is_root n i
  refine ⟨(hmem _).mpr hi, ?_⟩
  have hc := hcoroot _ hi
  apply Subtype.ext
  change _ = diagonal n (ofRealCoordinates (LieAlgebrasAndRepresentations.coroot (b i)))
  change ((killingCoroot H ((coordinateWeightMap n (b i)).comp e.symm.toLinearMap) :
    algebra n) : Mat n) = _ at hc
  rw [hc, ofRealCoordinates_coroot]
  rfl

end ClassicalB


section ClassicalD

open Specs.LieAlgebrasAndRepresentations.ClassicalRootsD hiding epsilon coroot
open LieAlgebrasAndRepresentations.ClassicalRootsD
open ClassicalCoordinates (Space epsilon rootsD simpleD simpleD_gram simpleDiagramD rootSystemD)

private def dDiagonal (n : ℕ) : Params n →ₗ[ℂ] algebra n where
  toFun t := ⟨diagonal n t, diagonal_mem t⟩
  map_add' t u := Subtype.ext (diagonal_add t u)
  map_smul' c t := Subtype.ext (by
    change diagonal n (c • t) = c • diagonal n t
    ext p q
    by_cases hpq : p = q
    · subst q
      cases p <;> simp [diagonal, show ∀ i, (c • t) i = c * t i by intro i; rfl]
    · simp [diagonal, hpq])

private theorem d_mem_weight {n : ℕ} (x : algebra n) (w : Dual n) :
    x.val ∈ Specs.LieAlgebrasAndRepresentations.ClassicalRootsD.weightSpace n w ↔ ∀ t, ⁅dDiagonal n t, x⁆ = w t • x :=
  ⟨fun hx t => Subtype.ext (hx.2 t), fun hx => ⟨x.property, fun t => congrArg Subtype.val (hx t)⟩⟩

private theorem d_coordinate_support {n : ℕ} (w : Dual n) (x : algebra n)
    (hw : w ≠ 0) (hx : x ≠ 0) (h : ∀ t, ⁅dDiagonal n t, x⁆ = w t • x) :
    w ∈ coordinateWeightMap n '' rootsD n := by
  have hr : w ∈ roots n := by
    refine ⟨hw, ?_⟩
    intro hz
    have hm := (d_mem_weight x w).mpr h
    rw [hz, Submodule.mem_bot] at hm
    exact hx (Subtype.ext hm)
  obtain ⟨i, j, hij, hw | hw | hw⟩ := (roots_iff w).mp hr
  · refine ⟨epsilon i - epsilon j, ⟨i, j, hij, false, true, ?_⟩, ?_⟩
    · simp [ClassicalCoordinates.sign, sub_eq_add_neg]
    · rw [map_sub, coordinateWeightMap_epsilon, coordinateWeightMap_epsilon, hw]
      rfl
  · refine ⟨epsilon i + epsilon j, ⟨i, j, hij, false, false, ?_⟩, ?_⟩
    · simp [ClassicalCoordinates.sign]
    · rw [map_add, coordinateWeightMap_epsilon, coordinateWeightMap_epsilon, hw]
      rfl
  · refine ⟨-(epsilon i + epsilon j), ⟨i, j, hij, true, true, ?_⟩, ?_⟩
    · simp [ClassicalCoordinates.sign, add_comm]
    · rw [map_neg, map_add, coordinateWeightMap_epsilon, coordinateWeightMap_epsilon, hw]
      rfl

private theorem d_simple_is_root {n : ℕ} (hn : 4 ≤ n) (i : Fin n) :
    coordinateWeightMap n (simpleD n i) ∈ roots n := by
  apply (roots_iff _).mpr
  by_cases h : i.val + 1 < n
  · let j : Fin n := ⟨i.val + 1, h⟩
    have hij : i ≠ j := by
      intro he
      have he' := congrArg Fin.val he
      dsimp [j] at he'
      omega
    refine ⟨i, j, hij, Or.inl ?_⟩
    simp [simpleD, h, j, Specs.LieAlgebrasAndRepresentations.ClassicalRootsD.epsilon]
  · let j : Fin n := ⟨n - 2, by omega⟩
    have hji : j ≠ i := by
      intro he
      have he' := congrArg Fin.val he
      dsimp [j] at he'
      have := i.isLt
      omega
    refine ⟨j, i, hji, Or.inr (Or.inl ?_)⟩
    simp [simpleD, h, j, Specs.LieAlgebrasAndRepresentations.ClassicalRootsD.epsilon]

private theorem classical_d_of_model (n : ℕ) (hn : 4 ≤ n)
    [FiniteDimensional ℂ (Algebra (CartanMatrix.D n))]
    [LieAlgebra.IsSimple ℂ (Algebra (CartanMatrix.D n))]
    (hdim : n + 2 * n * (n - 1) ≤ finrank ℂ (Algebra (CartanMatrix.D n)))
    (hA : ∀ i j, (CartanMatrix.D n i j : ℝ) = cartanMatrix (simpleD n) i j) :
    Nonempty (Algebra (CartanMatrix.D n) ≃ₗ⁅ℂ⁆ algebra n) := by
  obtain ⟨v, b, hb, hv, hs, _, _⟩ := simpleDiagramD n hn
  have hD (i j) : (CartanMatrix.D n i j : ℝ) = cartanMatrix b i j := by
    simpa only [show (b : Fin n → Space n) = simpleD n from funext hb] using hA i j
  obtain ⟨hss, H, e, hH, he, hmem, hcoroot⟩ := ClassicalMatrixCartans.type_d n (by omega)
  have hd (t : Params n) : (e t : algebra n) = dDiagonal n t := Subtype.ext (he t)
  refine coordinate_matrix_equiv _ (rootSystemD n hn) v hv b hs _ hD (by omega)
    ((finrank_classical_d_le n).trans hdim) (dDiagonal n) H e hd hss hH
    ?_ d_coordinate_support
  intro i
  dsimp only
  have hi : coordinateWeightMap n (b i) ∈ roots n := by
    rw [hb]
    exact d_simple_is_root hn i
  refine ⟨(hmem _).mpr hi, ?_⟩
  have hc := hcoroot _ hi
  apply Subtype.ext
  change _ = diagonal n (ofRealCoordinates (LieAlgebrasAndRepresentations.coroot (b i)))
  rw [hc, Specs.LieAlgebrasAndRepresentations.ClassicalRootsD.coroot, ofRealCoordinates_coroot]
  apply congrArg (diagonal n)
  funext j
  simp only [dot, coordinate, pow_two, Pi.smul_apply, smul_eq_mul]

end ClassicalD

theorem classical_a : classicalAType := by
  intro n hn
  let _ : FiniteDimensional ℂ (Algebra (CartanMatrix.A n)) := (models_simple (.A n hn)).1
  let _ : LieAlgebra.IsSimple ℂ (Algebra (CartanMatrix.A n)) := (models_simple (.A n hn)).2
  exact classical_a_of_model n hn (model_finrank (.A n hn)).ge

theorem classical_b : classicalBType := by
  intro n hn
  let _ : FiniteDimensional ℂ (Algebra (CartanMatrix.C n)) := (models_simple (.B n hn)).1
  let _ : LieAlgebra.IsSimple ℂ (Algebra (CartanMatrix.C n)) := (models_simple (.B n hn)).2
  obtain ⟨z, b, hi, hz, hb, _, _⟩ := ClassicalCoordinates.simpleDiagramB n hn
  have hA (i j : Fin n) : (CartanMatrix.C n i j : ℝ) = cartanMatrix b i j := by
    rw [show (b : Fin n → ClassicalCoordinates.Space n) = ClassicalCoordinates.simpleB n
      from funext hi]
    exact standard_cartan_b i j
  have hd := model_finrank (.B n hn)
  change finrank ℂ (Algebra (CartanMatrix.C n)) = n + 2 * n ^ 2 at hd
  exact classical_b_of_model n hn z hz b hb hi hA (hd ▸ finrank_classical_b_le n)

theorem classical_c : classicalCType := by
  intro n hn
  let _ : FiniteDimensional ℂ (Algebra (CartanMatrix.B n)) := (models_simple (.C n hn)).1
  let _ : LieAlgebra.IsSimple ℂ (Algebra (CartanMatrix.B n)) := (models_simple (.C n hn)).2
  obtain ⟨z, b, hi, hz, hb, _, _⟩ := ClassicalCoordinates.simpleDiagramC n hn
  have hA (i j : Fin n) : (CartanMatrix.B n i j : ℝ) = cartanMatrix b i j := by
    rw [show (b : Fin n → ClassicalCoordinates.Space n) = ClassicalCoordinates.simpleC n
      from funext hi]
    exact standard_cartan_c i j
  have hd := model_finrank (.C n hn)
  change finrank ℂ (Algebra (CartanMatrix.B n)) = n + 2 * n ^ 2 at hd
  exact classical_c_of_realization n hn z b hi hz hb hA (hd ▸ finrank_classical_c_le n)

theorem classical_d : classicalDType := by
  intro n hn
  let _ : FiniteDimensional ℂ (Algebra (CartanMatrix.D n)) := (models_simple (.D n hn)).1
  let _ : LieAlgebra.IsSimple ℂ (Algebra (CartanMatrix.D n)) := (models_simple (.D n hn)).2
  exact classical_d_of_model n hn (model_finrank (.D n hn)).ge (standard_cartan_d hn)

end ClassicalModels

open Module
open Serre

section SerreCartan

variable {ι : Type*} [DecidableEq ι] (A : Matrix ι ι ℤ)

private theorem weight_zero_lie (x y : Algebra A) (hx : x ∈ cartan A)
    (hy : y ∈ weightSpace A 0) : ⁅x, y⁆ = 0 := by
  change x ∈ Submodule.span ℂ (Set.range (h A)) at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    simpa using hy i
  | zero => exact zero_lie y
  | add x z _ _ hx hz => simp [add_lie, hx, hz]
  | smul r x _ hx => simp [smul_lie, hx]

private def serreCartan : LieSubalgebra ℂ (Algebra A) where
  __ := cartan A
  lie_mem' := by
    intro x y hx hy
    rw [weight_zero_lie A x y hx (cartan_le_zero_weightSpace A hy)]
    exact (cartan A).zero_mem

private theorem serreCartan_cartan (hzero : weightSpace A 0 = cartan A) :
    (serreCartan A).IsCartanSubalgebra := by
  classical
  let H := serreCartan A
  letI : IsLieAbelian H := ⟨fun x y =>
    Subtype.ext (weight_zero_lie A x y x.property
      (cartan_le_zero_weightSpace A y.property))⟩
  refine ⟨inferInstance, le_antisymm (fun x hx => ?_) H.le_normalizer⟩
  change x ∈ cartan A
  rw [← hzero]
  intro i
  have hi : h A i ∈ H := Submodule.subset_span ⟨i, rfl⟩
  have hxi : ⁅h A i, x⁆ ∈ H := by
    rw [← lie_skew]
    exact H.neg_mem ((H.mem_normalizer_iff x).mp hx _ hi)
  let f := LieAlgebra.ad ℂ (Algebra A) (h A i)
  have hrange : LinearMap.range f ≤ ⨆ (χ : ι → ℂ) (_ : χ ≠ 0), weightSpace A χ := by
    rw [← Submodule.map_top, ← weightSpace_iSup_eq_top A, Submodule.map_iSup]
    apply iSup_le
    intro χ
    rintro _ ⟨z, hz, rfl⟩
    by_cases hc : χ = 0
    · simp only [f, LieAlgebra.ad_apply, hz i, hc, Pi.zero_apply, zero_smul]
      exact Submodule.zero_mem _
    · change ⁅h A i, z⁆ ∈ _
      rw [hz i]
      have hle : weightSpace A χ ≤ ⨆ (ψ : ι → ℂ) (_ : ψ ≠ 0), weightSpace A ψ :=
        le_iSup_of_le χ (le_iSup (fun _ : χ ≠ 0 => weightSpace A χ) hc)
      exact hle ((weightSpace A χ).smul_mem _ hz)
  have hd := weightSpace_iSupIndep A 0
  rw [disjoint_iff_inf_le] at hd
  have hh : f x ∈ weightSpace A 0 ⊓ (⨆ (χ : ι → ℂ) (_ : χ ≠ 0), weightSpace A χ) :=
    ⟨cartan_le_zero_weightSpace A hxi, hrange ⟨x, rfl⟩⟩
  have hz := hd hh
  simpa [f] using hz

end SerreCartan

section SerreRootCoordinates

open Serre
open Specs.LieAlgebrasAndRepresentations.RootDecomposition (rootSpace_value rootSet_value)

variable {ι : Type*} [DecidableEq ι] (A : Matrix ι ι ℤ)

private theorem serreCartan_basis (hA : CartanConditions A) :
    ∃ c : Basis ι ℂ (serreCartan A), ∀ i, (c i : Algebra A) = h A i :=
  (triangular_of_cartanConditions A hA).2.1

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private def cartanRootCoordinates (b : Basis ι ℝ V) (c : Basis ι ℂ (serreCartan A)) :
    V →ₗ[ℝ] Module.Dual ℂ (serreCartan A) where
  toFun a := c.constr ℂ (Serre.rootWeight b a)
  map_add' a d := by
    apply c.ext
    intro i
    simp only [LinearMap.add_apply, Basis.constr_basis, Serre.rootWeight,
      rootCartan, inner_add_left, mul_add, add_div, Complex.ofReal_add]
  map_smul' r a := by
    apply c.ext
    intro i
    simp only [LinearMap.smul_apply, Basis.constr_basis, Serre.rootWeight, rootCartan,
      real_inner_smul_left, ← mul_assoc, mul_left_comm (2 : ℝ) r, mul_div_assoc,
      Complex.ofReal_mul, Complex.real_smul]
    rfl

private theorem cartanRootCoordinates_injective (b : Basis ι ℝ V)
    (c : Basis ι ℂ (serreCartan A)) :
    Function.Injective (cartanRootCoordinates A b c) :=
  (c.constr ℂ).injective.comp (Serre.rootWeight_injective b)

private theorem serre_root_space_eq (c : Basis ι ℂ (serreCartan A))
    (hc : ∀ i, (c i : Algebra A) = h A i) (α : Module.Dual ℂ (serreCartan A)) :
    rootSpace_value (serreCartan A) α = Serre.weightSpace A (fun i => α (c i)) := by
  ext x
  rw [mem_rootSpace]
  constructor
  · intro hx i
    simpa only [← hc] using hx (c i)
  · intro hx
    let f : serreCartan A →ₗ[ℂ] Algebra A :=
      { toFun := fun y => ⁅(y : Algebra A), x⁆
        map_add' := fun y z => add_lie (y : Algebra A) (z : Algebra A) x
        map_smul' := fun r y => smul_lie r (y : Algebra A) x }
    have heq : f = α.smulRight x := c.ext (fun i => by
      change ⁅(c i : Algebra A), x⁆ = α (c i) • x
      rw [hc]
      exact hx i)
    exact LinearMap.congr_fun heq

private theorem serre_roots_eq_image {R : Set V} (hR : IsRootSystem R)
    (v : V) (hv : RootRegular R v) (b : Basis ι ℝ V) (hb : IsSimpleBasis R v b)
    [Fintype ι] (hA : ∀ i j, (A i j : ℝ) = cartanMatrix b i j)
    (c : Basis ι ℂ (serreCartan A)) (hc : ∀ i, (c i : Algebra A) = h A i) :
    cartanRootCoordinates A b c '' R = rootSet_value (serreCartan A) := by
  have hs := (Serre.finiteType_spec R hR v hv b hb A hA).2.2.1
  have char (α : Module.Dual ℂ (serreCartan A)) :
      α ∈ rootSet_value (serreCartan A) ↔
        (fun i => α (c i)) ≠ 0 ∧ Serre.weightSpace A (fun i => α (c i)) ≠ ⊥ := by
    change (α ≠ 0 ∧ rootSpace_value (serreCartan A) α ≠ ⊥) ↔ _
    rw [serre_root_space_eq A c hc]
    refine and_congr_left' ⟨fun h he => h (c.ext fun i => congrFun he i), ?_⟩
    rintro h rfl
    exact h rfl
  ext α
  rw [char]
  constructor
  · rintro ⟨a, ha, rfl⟩
    change (fun i => (c.constr ℂ (Serre.rootWeight b a)) (c i)) ≠ 0 ∧
      Serre.weightSpace A (fun i => (c.constr ℂ (Serre.rootWeight b a)) (c i)) ≠ ⊥
    simp only [Basis.constr_basis]
    have hne : Serre.rootWeight b a ≠ 0 := by
      rw [← Serre.rootWeight_zero b]
      exact (Serre.rootWeight_injective b).ne (hR.nonzero a ha)
    exact ⟨hne, (hs _ hne).mpr ⟨a, ha, rfl⟩⟩
  · rintro ⟨hne, hw⟩
    obtain ⟨a, ha, he⟩ := (hs _ hne).mp hw
    refine ⟨a, ha, c.ext (fun i => ?_)⟩
    change (c.constr ℂ (Serre.rootWeight b a)) (c i) = α (c i)
    rw [Basis.constr_basis, ← he]

end SerreRootCoordinates

section TransportRootCoordinates

open Specs.LieAlgebrasAndRepresentations.RootDecomposition (rootSpace_value rootSet_value)
variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L] [LieRing M] [LieAlgebra ℂ M]
variable (g : L ≃ₗ⁅ℂ⁆ M) {H : LieSubalgebra ℂ L} {K : LieSubalgebra ℂ M}
variable (hg : H.map g.toLieHom = K)

private def transportCartanDual : Module.Dual ℂ H ≃ₗ[ℝ] Module.Dual ℂ K :=
  (LinearEquiv.arrowCongr (g.ofSubalgebras H K hg).toLinearEquiv (LinearEquiv.refl ℂ ℂ)).restrictScalars ℝ

private theorem coe_ofSubalgebras_apply (x : H) :
    ((g.ofSubalgebras H K hg x : K) : M) = g (x : L) := rfl

private theorem transport_rootSpace (α : Module.Dual ℂ H) {x : L} :
    g x ∈ rootSpace_value K (transportCartanDual g hg α) ↔ x ∈ rootSpace_value H α := by
  rw [mem_rootSpace, mem_rootSpace]
  let k := g.ofSubalgebras H K hg
  have he (a : H) : transportCartanDual g hg α (k a) = α a := by
    change α (k.symm (k a)) = α a
    rw [LieEquiv.symm_apply_apply]
  have hp (a : H) : ⁅((k a : K) : M), g x⁆ = g ⁅(a : L), x⁆ := by
    rw [coe_ofSubalgebras_apply]
    exact (g.map_lie _ _).symm
  constructor
  · intro h a
    apply g.injective
    change g ⁅(a : L), x⁆ = g (α a • x)
    rw [← hp, show g (α a • x) = α a • g x from g.toLinearEquiv.map_smul _ _, ← he]
    exact h (k a)
  · intro h a
    obtain ⟨b, rfl⟩ := k.surjective a
    change ⁅((k b : K) : M), g x⁆ = transportCartanDual g hg α (k b) • g x
    rw [hp, h, he]
    exact g.toLinearEquiv.map_smul _ _

private theorem transport_root_set :
    transportCartanDual g hg '' rootSet_value H = rootSet_value K := by
  let e := transportCartanDual g hg
  ext α
  obtain ⟨β, rfl⟩ := e.surjective α
  rw [Set.mem_image, show (e β ∈ rootSet_value K) =
    (e β ≠ 0 ∧ rootSpace_value K (e β) ≠ ⊥) from rfl]
  constructor
  · rintro ⟨δ, ⟨hne, hw⟩, he⟩
    have hδ : δ = β := e.injective he
    subst δ
    refine ⟨by simpa only [← e.map_zero, ne_eq, e.injective.eq_iff] using hne, ?_⟩
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hw
    exact (Submodule.ne_bot_iff _).mpr
      ⟨g x, (transport_rootSpace g hg β).2 hx, fun hh => hx0 (g.injective (hh.trans g.toLinearEquiv.map_zero.symm))⟩
  · rintro ⟨hne, hw⟩
    refine ⟨β, ⟨by simpa only [← e.map_zero, ne_eq, e.injective.eq_iff] using hne, ?_⟩, rfl⟩
    obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).mp hw
    obtain ⟨x, rfl⟩ := g.surjective y
    exact (Submodule.ne_bot_iff _).mpr
      ⟨x, (transport_rootSpace g hg β).1 hy, fun hh => hy0 (by subst x; exact g.toLinearEquiv.map_zero)⟩

end TransportRootCoordinates

section RootSystemComparison
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

private theorem rootReflection_affine (a b : E) (hb : b ≠ 0) (t : ℝ) :
    rootReflection b (a + t • b) = a + (-rootCartan a b - t) • b := by
  have hbb : inner ℝ b b ≠ 0 := _root_.inner_self_ne_zero.mpr hb
  have hcoef : 2 * inner ℝ (a + t • b) b / inner ℝ b b =
      rootCartan a b + 2 * t := by
    rw [inner_add_left, real_inner_smul_left, mul_add, add_div, rootCartan]
    congr 1
    rw [← mul_assoc, mul_div_cancel_right₀ _ hbb]
  rw [rootReflection, hcoef]
  calc
    _ = a + (t - (rootCartan a b + 2 * t)) • b := by rw [sub_smul, add_sub_assoc]
    _ = _ := by ring_nf

private def affineRootParameters (R : Set E) (a b : E) : Set ℝ :=
  {t | a + t • b ∈ R}

private theorem affineRootParameters_finite {R : Set E} (hR : RootAxioms R)
    (a : E) {b : E} (hb : b ∈ R) :
    (affineRootParameters R a b).Finite := by
  apply hR.finite.preimage
  intro r hr s hs h
  exact smul_left_injective ℝ (hR.nonzero b hb) (add_left_cancel h)

private theorem affineRootParameters_nonempty {R : Set E} {a : E} (ha : a ∈ R) (b : E) :
    (affineRootParameters R a b).Nonempty :=
  ⟨0, by simpa [affineRootParameters] using ha⟩

private theorem affineRootParameters_symmetric {R : Set E} (hR : RootAxioms R) {a b : E}
    (hb : b ∈ R) {t : ℝ} (ht : t ∈ affineRootParameters R a b) :
    -rootCartan a b - t ∈ affineRootParameters R a b := by
  change a + (-rootCartan a b - t) • b ∈ R
  rw [← rootReflection_affine a b (hR.nonzero b hb)]
  exact hR.reflection_mem b hb _ ht

/-- The extreme affine parameters determine an ordered Cartan pairing using only
the root set, including when the two roots are proportional. -/
private theorem rootCartan_eq_neg_add_extrema {R : Set E} (hR : RootAxioms R) {a b : E}
    (hb : b ∈ R) {T : Set ℝ} (hT : T = affineRootParameters R a b)
    (hfin : T.Finite) (hne : hfin.toFinset.Nonempty) :
    rootCartan a b = -(hfin.toFinset.min' hne + hfin.toFinset.max' hne) := by
  let U := hfin.toFinset
  let lo := U.min' hne
  let hi := U.max' hne
  have hlo : lo ∈ affineRootParameters R a b := by
    rw [← hT, ← hfin.mem_toFinset]
    exact Finset.min'_mem _ _
  have hhi : hi ∈ affineRootParameters R a b := by
    rw [← hT, ← hfin.mem_toFinset]
    exact Finset.max'_mem _ _
  have hlo' : -rootCartan a b - hi ∈ U := by
    rw [hfin.mem_toFinset, hT]
    exact affineRootParameters_symmetric hR hb hhi
  have hhi' : -rootCartan a b - lo ∈ U := by
    rw [hfin.mem_toFinset, hT]
    exact affineRootParameters_symmetric hR hb hlo
  change rootCartan a b = -(lo + hi)
  have h₁ : lo ≤ -rootCartan a b - hi := U.min'_le _ hlo'
  have h₂ : -rootCartan a b - lo ≤ hi := U.le_max' _ hhi'
  linarith

/-- A real linear equivalence carrying a root set onto a root set automatically
carries all its ordered Cartan pairings. -/
private theorem rootCartan_eq_of_linear_equiv {R : Set E} {S : Set F}
    (hR : RootAxioms R) (hS : RootAxioms S) (f : E ≃ₗ[ℝ] F) (himage : f '' R = S)
    {a b : E} (ha : a ∈ R) (hb : b ∈ R) :
    rootCartan (f a) (f b) = rootCartan a b := by
  have hfb : f b ∈ S := himage ▸ Set.mem_image_of_mem f hb
  let T := affineRootParameters R a b
  have hT : T = affineRootParameters S (f a) (f b) := by
    ext t
    change a + t • b ∈ R ↔ f a + t • f b ∈ S
    rw [← map_smul, ← map_add, ← himage]
    constructor
    · exact Set.mem_image_of_mem f
    · rintro ⟨r, hr, he⟩
      exact f.injective he ▸ hr
  have hfin : T.Finite := affineRootParameters_finite hR a hb
  have hne : hfin.toFinset.Nonempty := hfin.toFinset_nonempty.mpr (affineRootParameters_nonempty ha b)
  exact (rootCartan_eq_neg_add_extrema hS hfb hT hfin hne).trans
    (rootCartan_eq_neg_add_extrema hR hb rfl hfin hne).symm


section RootFormEquivalence

variable {U V : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]

private theorem range_eq_span_image {E : Type*} [AddCommGroup E] [Module ℝ E]
    (R : Set E) (hR : Submodule.span ℝ R = ⊤) (j : E →ₗ[ℝ] U) :
    LinearMap.range j = Submodule.span ℝ (j '' R) := by
  rw [← Submodule.map_span, hR, Submodule.map_top]

/-- A linear equivalence of the containing spaces which carries the embedded
root sets onto one another restricts to their real spans. -/
private theorem lift_root_set_equiv {R : Set E} {S : Set F}
    (hR : Submodule.span ℝ R = ⊤) (hS : Submodule.span ℝ S = ⊤)
    (j : E →ₗ[ℝ] U) (k : F →ₗ[ℝ] V)
    (hj : Function.Injective j) (hk : Function.Injective k)
    (g : U ≃ₗ[ℝ] V) (himage : g '' (j '' R) = k '' S) :
    ∃ f : E ≃ₗ[ℝ] F, (∀ a, k (f a) = g (j a)) ∧ f '' R = S := by
  have hmap : (LinearMap.range j).map (g : U →ₗ[ℝ] V) = LinearMap.range k := by
    rw [range_eq_span_image R hR j, range_eq_span_image S hS k, Submodule.map_span]
    exact congrArg (Submodule.span ℝ) himage
  let g' := g.ofSubmodules (LinearMap.range j) (LinearMap.range k) hmap
  let f := (LinearEquiv.ofInjective j hj).trans (g'.trans (LinearEquiv.ofInjective k hk).symm)
  have hf (a : E) : k (f a) = g (j a) := by simp [f, g']
  refine ⟨f, hf, ?_⟩
  apply Set.image_injective.mpr hk
  rw [← Set.image_comp, show (k ∘ f : E → V) = g ∘ j from funext hf, Set.image_comp, himage]

end RootFormEquivalence

section DiagramEquivalence

open Module

private theorem exists_vector_realizing_transport (f : E ≃ₗ[ℝ] F) (v : E)
    [FiniteDimensional ℝ F] : ∃ z : F, ∀ a : E, inner ℝ z (f a) = inner ℝ v a := by
  let m : F →ₗ[ℝ] ℝ := (innerₗ E v).comp f.symm.toLinearMap
  refine ⟨(InnerProductSpace.toDual ℝ F).symm m.toContinuousLinearMap, fun a => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  change inner ℝ v (f.symm (f a)) = _
  rw [f.symm_apply_apply]

private theorem simpleRoots_transport {R : Set E} {S : Set F} {v : E} {w : F}
    (f : E ≃ₗ[ℝ] F)
    (hp : ∀ a : E, a ∈ positiveRoots R v ↔ f a ∈ positiveRoots S w)
    (a : E) : a ∈ simpleRoots R v ↔ f a ∈ simpleRoots S w := by
  constructor
  · intro ha
    refine ⟨(hp a).mp ha.1, fun y hy z hz eq => ?_⟩
    have hy' : f.symm y ∈ positiveRoots R v := (hp _).mpr (by simpa using hy)
    have hz' : f.symm z ∈ positiveRoots R v := (hp _).mpr (by simpa using hz)
    apply ha.2 _ hy' _ hz'
    apply f.injective
    rw [map_add, f.apply_symm_apply, f.apply_symm_apply, eq]
  · intro ha
    exact ⟨(hp a).mpr ha.1, fun y hy z hz eq =>
      ha.2 _ ((hp y).mp hy) _ ((hp z).mp hz) (by rw [eq, map_add])⟩

private def indexEquivSimpleRoots {ι : Type*} {R : Set E} {v : E} (b : Basis ι ℝ E)
    (hb : IsSimpleBasis R v b) :
    ι ≃ simpleRoots R v :=
  Equiv.ofBijective (fun i => ⟨b i, hb ▸ ⟨i, rfl⟩⟩)
    ⟨fun _ _ h => b.injective (congrArg Subtype.val h),
      fun x => by
        have hx : x.val ∈ Set.range b := hb.symm ▸ x.property
        obtain ⟨i, hi⟩ := hx
        exact ⟨i, Subtype.ext hi⟩⟩

/-- The oriented Dynkin diagram is invariant under a linear equivalence
carrying one root set onto another. The chosen chambers can be arbitrary. -/
private theorem dynkin_isomorphic_of_linear_equiv {ι κ : Type*} {R : Set E} {S : Set F}
    {v : E} {w : F} {b : Basis ι ℝ E} {c : Basis κ ℝ F}
    (hR : IsRootSystem R) (hS : IsRootSystem S)
    (hv : RootRegular R v) (hw : RootRegular S w)
    (hb : IsSimpleBasis R v b) (hc : IsSimpleBasis S w c)
    (f : E ≃ₗ[ℝ] F) (himage : f '' R = S) :
    (dynkinDiagram b).Isomorphic (dynkinDiagram c) := by
  have hsfd : FiniteDimensional ℝ (⊤ : Submodule ℝ F) :=
    hS.span_eq_top ▸ FiniteDimensional.span_of_finite ℝ hS.finite
  let : FiniteDimensional ℝ F := (Submodule.topEquiv : (⊤ : Submodule ℝ F) ≃ₗ[ℝ] F).finiteDimensional
  obtain ⟨z, hz⟩ := exists_vector_realizing_transport f v
  have hreg : RootRegular S z := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := himage.symm ▸ hy
    rw [hz]
    exact hv a ha
  obtain ⟨g, hg⟩ := exists_weyl_into_simpleChamber hS hw hreg
  let f' : E ≃ₗ[ℝ] F := f.trans g.val
  have hgpos (y : F) (hy : y ∈ S) :
      0 < inner ℝ (g.val z) y ↔ 0 < inner ℝ w y := by
    constructor
    · intro hry
      rcases positive_or_neg_positive hS.toRootAxioms hw hy with hp | hm
      · exact hp.2
      · have hn := simpleChamber_pairing_positive hS.toRootAxioms hg hm
        rw [inner_neg_right, neg_pos] at hn
        exact (not_lt_of_ge hn.le hry).elim
    · intro hry
      exact simpleChamber_pairing_positive hS.toRootAxioms hg ⟨hy, hry⟩
  have hmem (a : E) : a ∈ R ↔ f' a ∈ S := by
    have hf : a ∈ R ↔ f a ∈ S := by
      rw [← himage]
      constructor
      · exact Set.mem_image_of_mem f
      · rintro ⟨x, hx, hxa⟩
        exact f.injective hxa ▸ hx
    exact hf.trans (rootWeylGroup_mem_iff hS.toRootAxioms g.property (f a))
  have hp (a : E) : a ∈ positiveRoots R v ↔ f' a ∈ positiveRoots S w := by
    have he : inner ℝ (g.val z) (f' a) = inner ℝ v a := by
      change inner ℝ (g.val z) (g.val (f a)) = _
      rw [rootWeylGroup_inner g.property, hz]
    constructor
    · intro ha
      have hfa := (hmem a).mp ha.1
      exact ⟨hfa, (hgpos _ hfa).mp (he.symm ▸ ha.2)⟩
    · intro ha
      exact ⟨(hmem a).mpr ha.1, he ▸ (hgpos _ ha.1).mpr ha.2⟩
  have hsimple := simpleRoots_transport f' hp
  let d : simpleRoots R v ≃ simpleRoots S w :=
    { toFun := fun a => ⟨f' a.val, (hsimple a.val).mp a.property⟩
      invFun := fun a => ⟨f'.symm a.val, (hsimple _).mpr (by simpa using a.property)⟩
      left_inv := fun a => Subtype.ext (f'.symm_apply_apply a.val)
      right_inv := fun a => Subtype.ext (f'.apply_symm_apply a.val) }
  let iR := indexEquivSimpleRoots b hb
  let iS := indexEquivSimpleRoots c hc
  let e := iR.trans (d.trans iS.symm)
  have he (i : ι) : c (e i) = f' (b i) :=
    congrArg Subtype.val (iS.apply_symm_apply (d (iR i)))
  have hm : f' '' R = S := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hmem x).mp hx
    · intro hy
      exact ⟨f'.symm y, (hmem _).mpr (by simp [hy]), f'.apply_symm_apply y⟩
  have hcartan (i j : ι) : cartanMatrix b i j = cartanMatrix c (e i) (e j) := by
    change rootCartan (b j) (b i) = rootCartan (c (e j)) (c (e i))
    rw [he i, he j]
    exact (rootCartan_eq_of_linear_equiv hR.toRootAxioms hS.toRootAxioms f' hm
      (iR j).property.1.1 (iR i).property.1.1).symm
  refine ⟨e, ?_, ?_⟩
  · intro i j
    by_cases hij : i = j
    · subst j
      simp [dynkinDiagram]
    · apply Nat.cast_injective (R := ℝ)
      rw [dynkin_edges_cast hR hv hb hij, dynkin_edges_cast hS hw hc (e.injective.ne hij),
        hcartan, hcartan]
  · intro i j
    by_cases hij : i = j
    · subst j
      simp [dynkinDiagram]
    · rw [dynkin_arrow_iff_cartan_lt hR hv hb hij,
        dynkin_arrow_iff_cartan_lt hS hw hc (e.injective.ne hij), hcartan, hcartan]

end DiagramEquivalence

end RootSystemComparison

section ModelIsomorphism

open Serre

private theorem diagram_isomorphic_of_cartan_preserving
    (t s : FiniteDynkinType) (g : Model t ≃ₗ⁅ℂ⁆ Model s)
    (hg : (serreCartan t.cartan).map g.toLieHom = serreCartan s.cartan) :
    t.diagram.Isomorphic s.diagram := by
  obtain ⟨d⟩ := standard_root_realization t
  obtain ⟨d'⟩ := standard_root_realization s
  letI := d.normedGroup
  letI := d.innerSpace
  letI := d'.normedGroup
  letI := d'.innerSpace
  have ht := Serre.cartanConditions_spec _ d.roots_axioms _ d.regular_spec _ d.simple_basis _
    d.matrix_entry
  have hs := Serre.cartanConditions_spec _ d'.roots_axioms _ d'.regular_spec _ d'.simple_basis _
    d'.matrix_entry
  obtain ⟨c, hc⟩ := serreCartan_basis t.cartan ht
  obtain ⟨c', hc'⟩ := serreCartan_basis s.cartan hs
  let F := cartanRootCoordinates t.cartan d.basis c
  let G := cartanRootCoordinates s.cartan d'.basis c'
  let q := transportCartanDual g hg
  have hF : F '' d.roots = rootSet_value (serreCartan t.cartan) :=
    serre_roots_eq_image t.cartan d.roots_axioms _ d.regular_spec _ d.simple_basis d.matrix_entry c hc
  have hG : G '' d'.roots = rootSet_value (serreCartan s.cartan) :=
    serre_roots_eq_image s.cartan d'.roots_axioms _ d'.regular_spec _ d'.simple_basis d'.matrix_entry c' hc'
  have hq : q '' (F '' d.roots) = G '' d'.roots := by
    rw [hF, hG]
    exact transport_root_set g hg
  obtain ⟨f, _, hf⟩ := lift_root_set_equiv d.roots_axioms.span_eq_top d'.roots_axioms.span_eq_top
    F G (cartanRootCoordinates_injective _ _ _) (cartanRootCoordinates_injective _ _ _) q hq
  obtain ⟨e, hedge, harrow⟩ := dynkin_isomorphic_of_linear_equiv
    d.roots_axioms d'.roots_axioms d.regular_spec d'.regular_spec d.simple_basis d'.simple_basis f hf
  have hed {t : FiniteDynkinType} (d : StandardRootRealization t) (i j : Fin t.rank) :
      letI := d.normedGroup
      letI := d.innerSpace
      (dynkinDiagram d.basis).edges i j = t.diagram.edges i j := by
    letI := d.normedGroup
    letI := d.innerSpace
    by_cases hij : i = j
    · simp [dynkinDiagram, FiniteDynkinType.diagram, hij]
    have he := dynkin_edges_cast d.roots_axioms d.regular_spec d.simple_basis hij
    rw [← d.matrix_entry, ← d.matrix_entry, ← Int.cast_mul] at he
    change _ = if i = j then 0 else (t.cartan i j * t.cartan j i).toNat
    rw [ite_eq_right hij]
    have hn' : (0 : ℝ) ≤ ((t.cartan i j * t.cartan j i : ℤ) : ℝ) := he ▸ Nat.cast_nonneg _
    have hn : 0 ≤ t.cartan i j * t.cartan j i := by exact_mod_cast hn'
    apply Nat.cast_injective (R := ℝ)
    rw [he, ← Int.cast_natCast, Int.toNat_of_nonneg hn]
  have har {t : FiniteDynkinType} (d : StandardRootRealization t) (i j : Fin t.rank) :
      letI := d.normedGroup
      letI := d.innerSpace
      (dynkinDiagram d.basis).arrow i j ↔ t.diagram.arrow i j := by
    letI := d.normedGroup
    letI := d.innerSpace
    by_cases hij : i = j
    · simp [dynkinDiagram, FiniteDynkinType.diagram, hij]
    rw [dynkin_arrow_iff_cartan_lt d.roots_axioms d.regular_spec d.simple_basis hij,
      ← d.matrix_entry, ← d.matrix_entry]
    simp [FiniteDynkinType.diagram, hij]
  exact ⟨e, fun i j => (hed d i j).symm.trans ((hedge i j).trans (hed d' (e i) (e j))),
    fun i j => (har d i j).symm.trans ((harrow i j).trans (har d' (e i) (e j)))⟩

end ModelIsomorphism

section
universe u v w z

variable {R : Type u} [CommRing R]
variable {ι : Type v} (M : ι → Type w)
variable [∀ i, LieRing (M i)] [∀ i, LieAlgebra R (M i)]

private theorem lie_single_right (i : ι) (y : ⨁ j, M j) (x : M i) :
    ⁅y, DirectSum.of M i x⁆ = DirectSum.of M i ⁅y i, x⁆ := by
  apply DFinsupp.ext
  intro j
  by_cases hj : j = i
  · subst j
    simp only [DirectSum.bracket_apply, DirectSum.of_eq_same]
  · rw [DirectSum.bracket_apply, DirectSum.of_eq_of_ne _ _ _ hj, lie_zero,
      DirectSum.of_eq_of_ne _ _ _ hj]

/-- The ideal consisting of elements supported at a given coordinate. -/
private def factorIdeal (i : ι) : LieIdeal R (⨁ i, M i) where
  __ := LinearMap.range (DirectSum.lof R ι M i)
  lie_mem := by
    intro y z hz
    obtain ⟨x, rfl⟩ := hz
    exact ⟨⁅y i, x⁆, lie_single_right M i y x |>.symm⟩

private theorem mem_factorIdeal (i : ι) (y : ⨁ j, M j) :
    y ∈ factorIdeal (R := R) M i ↔ ∃ x, DirectSum.of M i x = y :=
  Iff.rfl

private theorem factorIdeal_ne_bot [∀ i, Nontrivial (M i)] (i : ι) :
    factorIdeal (R := R) M i ≠ ⊥ := by
  obtain ⟨x, hx⟩ := exists_ne (0 : M i)
  intro h
  have hmem : DirectSum.of M i x ∈ factorIdeal (R := R) M i := ⟨x, rfl⟩
  rw [h, LieSubmodule.mem_bot] at hmem
  have hzero : DirectSum.of M i x = DirectSum.of M i 0 := by simpa using hmem
  exact hx (DirectSum.of_injective i hzero)

private theorem factorIdeal_le_of_inter_ne_bot [∀ i, LieAlgebra.IsSimple R (M i)]
    (J : LieIdeal R (⨁ i, M i)) (i : ι) (x : M i) (hx : x ≠ 0)
    (hmem : DirectSum.of M i x ∈ J) : factorIdeal (R := R) M i ≤ J := by
  let P := J.comap (DirectSum.lieAlgebraOf R ι M i)
  have hp : P ≠ ⊥ := by
    intro h
    have hxp : x ∈ P := hmem
    rw [h, LieSubmodule.mem_bot] at hxp
    exact hx hxp
  have htop := (LieAlgebra.IsSimple.eq_bot_or_eq_top P).resolve_left hp
  intro y hy
  obtain ⟨z, rfl⟩ := (mem_factorIdeal M i y).mp hy
  change z ∈ P
  rw [htop]
  exact LieSubmodule.mem_top z

private theorem factorIdeal_isAtom [∀ i, LieAlgebra.IsSimple R (M i)] (i : ι) :
    IsAtom (factorIdeal (R := R) M i) := by
  let (j : ι) : Nontrivial (M j) := LieAlgebra.IsSimple.nontrivial R (M j)
  refine isAtom_iff_le_of_ge.mpr ⟨factorIdeal_ne_bot M i, ?_⟩
  intro J hJ hle
  obtain ⟨x, hxJ, hxn⟩ : ∃ x ∈ J, x ≠ (0 : ⨁ j, M j) := by
    by_contra! h
    exact hJ (eq_bot_iff.mpr fun x hx => by rw [LieSubmodule.mem_bot]; exact h x hx)
  obtain ⟨y, rfl⟩ := (mem_factorIdeal M i x).mp (hle hxJ)
  have hy : y ≠ 0 := fun hz => hxn (by simp [hz])
  exact factorIdeal_le_of_inter_ne_bot M J i y hy hxJ

private theorem exists_factorIdeal_le [∀ i, LieAlgebra.IsSimple R (M i)]
    (J : LieIdeal R (⨁ i, M i)) (hJ : J ≠ ⊥) : ∃ i, factorIdeal (R := R) M i ≤ J := by
  obtain ⟨x, hxJ, hxn⟩ : ∃ x ∈ J, x ≠ (0 : ⨁ j, M j) := by
    by_contra! h
    exact hJ (eq_bot_iff.mpr fun x hx => by rw [LieSubmodule.mem_bot]; exact h x hx)
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra! h
    exact hxn (DFinsupp.ext h)
  obtain ⟨y, hy⟩ : ∃ y : M i, ⁅y, x i⁆ ≠ 0 := by
    by_contra! h
    have hmem : x i ∈ LieAlgebra.center R (M i) := h
    rw [LieAlgebra.center_eq_bot, LieSubmodule.mem_bot] at hmem
    exact hi hmem
  refine ⟨i, factorIdeal_le_of_inter_ne_bot M J i _ hy ?_⟩
  have hmem : ⁅x, DirectSum.of M i y⁆ ∈ J := by
    rw [← lie_skew]
    exact J.neg_mem (J.lie_mem hxJ)
  rw [lie_single_right, ← lie_skew (x i) y, map_neg] at hmem
  exact J.neg_mem_iff.mp hmem

private def factorAtoms [∀ i, LieAlgebra.IsSimple R (M i)] :
    ι ≃ {J : LieIdeal R (⨁ i, M i) // IsAtom J} := by
  refine Equiv.ofBijective (fun i => ⟨factorIdeal M i, factorIdeal_isAtom M i⟩) ⟨?_, ?_⟩
  · intro i j h
    by_contra hij
    let : Nontrivial (M i) := LieAlgebra.IsSimple.nontrivial R (M i)
    obtain ⟨x, hx⟩ := exists_ne (0 : M i)
    have hi : DirectSum.of M i x ∈ factorIdeal (R := R) M i := ⟨x, rfl⟩
    rw [show factorIdeal (R := R) M i = factorIdeal M j from congrArg Subtype.val h] at hi
    obtain ⟨y, hy⟩ := (mem_factorIdeal M j _).mp hi
    have hz := congrArg (fun v : ⨁ k, M k => v i) hy
    rw [DirectSum.of_eq_of_ne _ _ _ hij, DirectSum.of_eq_same] at hz
    exact hx hz.symm
  · intro J
    obtain ⟨i, hi⟩ := exists_factorIdeal_le M J.val J.property.ne_bot
    refine ⟨i, Subtype.ext ?_⟩
    exact le_antisymm hi ((isAtom_iff_le_of_ge.mp J.property).2 _
      (factorIdeal_isAtom M i).ne_bot hi)

private def factorEquiv (i : ι) : factorIdeal (R := R) M i ≃ₗ⁅R⁆ M i :=
  LieEquiv.ofBijective ((DirectSum.lieAlgebraComponent R ι M i).comp (factorIdeal M i).incl)
    ⟨by
      intro x y h
      change x.val i = y.val i at h
      obtain ⟨a, ha⟩ := (mem_factorIdeal M i x.val).mp x.property
      obtain ⟨b, hb⟩ := (mem_factorIdeal M i y.val).mp y.property
      rw [← ha, ← hb, DirectSum.of_eq_same, DirectSum.of_eq_same] at h
      apply Subtype.ext
      rw [← ha, ← hb, h],
      fun x => ⟨⟨DirectSum.of M i x, ⟨x, rfl⟩⟩, DirectSum.of_eq_same i x⟩⟩

variable (N : Type z) [LieRing N] [LieAlgebra R N]
variable {L : Type*} [LieRing L] [LieAlgebra R L]

private def lieIdealOrderIso (g : L ≃ₗ⁅R⁆ N) : LieIdeal R L ≃o LieIdeal R N where
  toFun J := J.comap g.symm.toLieHom
  invFun J := J.comap g.toLieHom
  left_inv J := by ext; simp
  right_inv J := by ext; simp
  map_rel_iff' := by
    intro I J
    constructor
    · intro h x hx
      have hm : g x ∈ I.comap g.symm.toLieHom := by simpa using hx
      simpa using h hm
    · intro h x hx
      exact h hx

private def lieIdealAtomsEquiv (g : L ≃ₗ⁅R⁆ N) :
    {J : LieIdeal R L // IsAtom J} ≃ {J : LieIdeal R N // IsAtom J} where
  toFun J := ⟨lieIdealOrderIso N g J.val, ((lieIdealOrderIso N g).isAtom_iff _).2 J.property⟩
  invFun J := ⟨(lieIdealOrderIso N g).symm J.val,
    ((lieIdealOrderIso N g).symm.isAtom_iff _).2 J.property⟩
  left_inv _ := Subtype.ext ((lieIdealOrderIso N g).symm_apply_apply _)
  right_inv _ := Subtype.ext ((lieIdealOrderIso N g).apply_symm_apply _)

private def idealEquiv (g : L ≃ₗ⁅R⁆ N) (J : LieIdeal R L) :
    J ≃ₗ⁅R⁆ lieIdealOrderIso N g J where
  toFun x := ⟨g x.val, by change g.symm (g x.val) ∈ J; simp⟩
  invFun x := ⟨g.symm x.val, x.property⟩
  left_inv x := Subtype.ext (g.symm_apply_apply x.val)
  right_inv x := Subtype.ext (g.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (g.map_add x.val y.val)
  map_smul' r x := Subtype.ext (g.map_smul r x.val)
  map_lie' := Subtype.ext (g.map_lie _ _)

/-- An isomorphism between sums of nonabelian simple algebras permutes the
summands and induces an isomorphism on every matched pair. -/
private theorem simple_sum_factors {κ : Type*} (M' : κ → Type*)
    [∀ j, LieRing (M' j)] [∀ j, LieAlgebra R (M' j)]
    [∀ i, LieAlgebra.IsSimple R (M i)] [∀ j, LieAlgebra.IsSimple R (M' j)]
    (g : (⨁ i, M i) ≃ₗ⁅R⁆ (⨁ j, M' j)) :
    ∃ p : ι ≃ κ, ∀ i, Nonempty (M i ≃ₗ⁅R⁆ M' (p i)) := by
  let a := factorAtoms (R := R) M
  let b := factorAtoms (R := R) M'
  let c := lieIdealAtomsEquiv (⨁ j, M' j) g
  let p := a.trans (c.trans b.symm)
  refine ⟨p, fun i => ?_⟩
  have hp : b (p i) = c (a i) := b.apply_symm_apply _
  have hp' : factorIdeal (R := R) M' (p i) =
      lieIdealOrderIso (⨁ j, M' j) g (factorIdeal (R := R) M i) :=
    congrArg Subtype.val hp
  let e := idealEquiv (⨁ j, M' j) g (factorIdeal (R := R) M i)
  let f := factorEquiv (R := R) M' (p i)
  exact ⟨(factorEquiv (R := R) M i).symm.trans (e.trans (hp' ▸ f))⟩

end

open Specs.LieAlgebrasAndRepresentations.ComplexClassification

private theorem semisimple_uniqueness_of_models (hs : modelsSimpleType) (hu : modelUniquenessType) :
    semisimpleUniquenessType := by
  classical
  intro ι κ _ _ t s h
  obtain ⟨g⟩ := h
  let (i : ι) : LieAlgebra.IsSimple ℂ (Model (t i)) := (hs (t i)).2
  let (j : κ) : LieAlgebra.IsSimple ℂ (Model (s j)) := (hs (s j)).2
  obtain ⟨p, hp⟩ := simple_sum_factors (fun i => Model (t i)) (fun j => Model (s j)) g
  exact ⟨p, fun i => (hu (t i) (s (p i))).mp (hp i)⟩

section Uniqueness

open Serre

private theorem cartan_map_of_equiv {L M : Type*} [LieRing L] [LieAlgebra ℂ L]
    [LieRing M] [LieAlgebra ℂ M] (g : L ≃ₗ⁅ℂ⁆ M) (H : LieSubalgebra ℂ L)
    (hH : H.IsCartanSubalgebra) : (H.map g.toLieHom).IsCartanSubalgebra := by
  let K := H.map g.toLieHom
  let e := H.equivMapOfInjective g.toLieHom g.injective
  refine ⟨e.nilpotent_iff_equiv_nilpotent.mp hH.nilpotent, le_antisymm ?_ K.le_normalizer⟩
  intro x hx
  have hn : g.symm x ∈ H.normalizer := by
    apply (H.mem_normalizer_iff _).mpr
    intro y hy
    have hgy : g y ∈ K := ⟨y, hy, rfl⟩
    obtain ⟨z, hz, he⟩ := (K.mem_normalizer_iff x).mp hx (g y) hgy
    change g z = ⁅x, g y⁆ at he
    have he' : g ⁅g.symm x, y⁆ = ⁅x, g y⁆ := by
      rw [LieEquiv.map_lie, LieEquiv.apply_symm_apply]
    exact g.injective (he.trans he'.symm) ▸ hz
  rw [hH.self_normalizing] at hn
  exact ⟨g.symm x, hn, g.apply_symm_apply x⟩

private theorem model_cartan_isCartan (t : FiniteDynkinType) :
    (serreCartan t.cartan).IsCartanSubalgebra := by
  obtain ⟨d⟩ := standard_root_realization t
  letI := d.normedGroup
  letI := d.innerSpace
  exact serreCartan_cartan t.cartan
    (Serre.finiteType_spec _ d.roots_axioms _ d.regular_spec _ d.simple_basis _
      d.matrix_entry).2.2.2.2.1

private theorem same_type_isomorphic {t s : FiniteDynkinType} (h : SameType t s) :
    Nonempty (Model t ≃ₗ⁅ℂ⁆ Model s) := by
  have bc : Nonempty (Model (.B 2 (by decide)) ≃ₗ⁅ℂ⁆ Model (.C 2 (by decide))) := by
    obtain ⟨eB⟩ := classical_b 2 (by decide)
    obtain ⟨eC⟩ := classical_c 2 (by decide)
    obtain ⟨eBC⟩ := ClassicalLowRank.b2_c2
    exact ⟨eB.trans (eBC.trans eC.symm)⟩
  rcases h with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨LieEquiv.refl⟩
  · exact bc
  · exact bc.map LieEquiv.symm

theorem model_uniqueness : modelUniquenessType := by
  intro t s
  refine ⟨?_, same_type_isomorphic⟩
  rintro ⟨g⟩
  let _ : FiniteDimensional ℂ (Model s) := (models_simple s).1
  let _ : LieAlgebra.IsSimple ℂ (Model s) := (models_simple s).2
  have hss : IsSemisimple ℂ (Model s) := LieAlgebra.radical_eq_bot
  let H := serreCartan t.cartan
  let K := serreCartan s.cartan
  have hH := cartan_map_of_equiv g H (model_cartan_isCartan t)
  have hK := model_cartan_isCartan s
  obtain ⟨f, _, hf⟩ := cartan_conjugacy (Model s) hss (H.map g.toLieHom) K
    ⟨hH.nilpotent, hH.self_normalizing⟩ ⟨hK.nilpotent, hK.self_normalizing⟩
  have he : H.map (g.trans f).toLieHom = K := by
    rw [← hf]
    ext z
    change (∃ x ∈ H, f (g x) = z) ↔ (∃ y ∈ H.map g.toLieHom, f y = z)
    constructor
    · rintro ⟨x, hx, hz⟩
      exact ⟨g x, ⟨x, hx, rfl⟩, hz⟩
    · rintro ⟨y, ⟨x, hx, hxy⟩, hz⟩
      exact ⟨x, hx, (congrArg f hxy).trans hz⟩
  exact dynkin_uniqueness t s (diagram_isomorphic_of_cartan_preserving t s (g.trans f) he)

theorem semisimple_uniqueness : semisimpleUniquenessType :=
  semisimple_uniqueness_of_models models_simple model_uniqueness

end Uniqueness

end LieAlgebrasAndRepresentations.ComplexClassification
