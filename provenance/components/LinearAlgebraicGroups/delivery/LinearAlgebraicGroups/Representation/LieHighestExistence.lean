import Specs.LinearAlgebraicGroups.Representation.LieHighestExistence
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CompleteReducibility
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.Sl2SimpleModules
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing

open Module LieModule
open LieAlgebrasAndRepresentations (sl2_expansion sl2_relations sl2Coordinates sl2_simple)
open Specs.LieAlgebrasAndRepresentations.Sl2Model

namespace LinearAlgebraicGroups.Representation.LieHighestExistence

universe u v w t i j
variable {k : Type u} [Field k] [CharZero k]
variable {L : Type v} [LieRing L] [LieAlgebra k L]
variable {V : Type w} [AddCommGroup V] [Module k V]
variable [FiniteDimensional k V]
variable [LieRingModule L V] [LieModule k L V]

section Primitive

attribute [local instance] LieRing.ofAssociativeRing

variable {A B : End k V}

omit [CharZero k] [FiniteDimensional k V] in
private lemma bracket_mul (X Y Z : End k V) :
    ⁅X, Y * Z⁆ = ⁅X, Y⁆ * Z + Y * ⁅X, Z⁆ := by
  simp only [LieRing.of_associative_ring_bracket]
  noncomm_ring

omit [CharZero k] [FiniteDimensional k V] in
private lemma bracket_pow {c : k} (h : ⁅A, B⁆ = c • B) (n : ℕ) :
    ⁅A, B ^ n⁆ = ((n : k) * c) • B ^ n := by
  induction n with
  | zero => simp [LieRing.of_associative_ring_bracket]
  | succ n ih =>
    rw [pow_succ, bracket_mul, ih, h, smul_mul_assoc, mul_smul_comm, ← add_smul,
      Nat.cast_succ, add_mul, one_mul]

/-- A nonzero commutator eigenvalue forces the corresponding operator to be nilpotent. -/
private lemma nilpotent_of_bracket {c : k} (hc : c ≠ 0) (h : ⁅A, B⁆ = c • B) :
    IsNilpotent B := by
  by_contra hn
  have hne (n : ℕ) : B ^ n ≠ 0 := fun hz => hn ⟨n, hz⟩
  have hind := (LieAlgebra.ad k (End k V) A).eigenvectors_linearIndependent'
    (fun n : ℕ => (n : k) * c)
    (fun _ _ hab => Nat.cast_injective (mul_right_cancel₀ hc hab))
    (fun n => B ^ n)
    (fun n => ⟨End.mem_eigenspace_iff.mpr (bracket_pow h n), hne n⟩)
  let : Finite ℕ := hind.finite
  exact not_finite ℕ

omit [CharZero k] [FiniteDimensional k V] in
/-- The usual lowering identity before requiring a scalar eigenvalue for h. -/
private lemma lowering_bracket (A B C : End k V) (hBC : ⁅B, C⁆ = A)
    (hAC : ⁅A, C⁆ = (-2 : k) • C) (n : ℕ) :
    ⁅B, C ^ (n + 1)⁆ =
      ((n : k) + 1) • (C ^ n * A) - (((n : k) + 1) * n) • C ^ n := by
  induction n with
  | zero => simpa using hBC
  | succ n ih =>
    have hh : A * C ^ (n + 1) =
        C ^ (n + 1) * A + (((n : k) + 1) * (-2)) • C ^ (n + 1) := by
      have hp := bracket_pow hAC (n + 1)
      rw [LieRing.of_associative_ring_bracket, Nat.cast_succ, sub_eq_iff_eq_add] at hp
      rw [hp, add_comm]
    calc
      ⁅B, C ^ (n + 1 + 1)⁆ =
          A * C ^ (n + 1) + C * ⁅B, C ^ (n + 1)⁆ := by
        rw [pow_succ', bracket_mul, hBC]
      _ = _ := by
        rw [hh, ih, mul_sub, mul_smul_comm, mul_smul_comm, ← mul_assoc, ← pow_succ']
        push_cast
        module

/-- A primitive vector over the ground field is obtained by minimizing the
lowering length among the nonzero vectors in the kernel of the raising operator. -/
private lemma exists_primitive [Nontrivial V] {h e f : L} (triple : IsSl2Triple h e f) :
    ∃ (n : ℕ) (m : V), triple.HasPrimitiveVectorWith m (n : k) := by
  classical
  let ρ := toEnd k L V
  let A := ρ h
  let B := ρ e
  let C := ρ f
  have hab : ⁅A, B⁆ = (2 : k) • B := by
    change ⁅ρ h, ρ e⁆ = _
    rw [← LieHom.map_lie, triple.lie_h_e_smul k, map_smul]
  have hac : ⁅A, C⁆ = (-2 : k) • C := by
    change ⁅ρ h, ρ f⁆ = _
    rw [← LieHom.map_lie, triple.lie_lie_smul_f k, map_neg, map_smul, neg_smul]
  have hbc : ⁅B, C⁆ = A := by
    change ⁅ρ e, ρ f⁆ = ρ h
    rw [← LieHom.map_lie, triple.lie_e_f]
  obtain ⟨b, hb⟩ := nilpotent_of_bracket (by norm_num : (2 : k) ≠ 0) hab
  obtain ⟨c, hc⟩ := nilpotent_of_bracket (by norm_num : (-2 : k) ≠ 0) hac
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  obtain ⟨r, hr, hr'⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists (p := fun n => (B ^ n) x = 0)
    (show (B ^ 0) x ≠ 0 by simpa using hx) ⟨b, by simp [hb]⟩
  let P (n : ℕ) := ∃ m : V, m ≠ 0 ∧ B m = 0 ∧ (C ^ (n + 1)) m = 0
  have hP : ∃ n, P n := ⟨c, (B ^ r) x, hr,
    by simpa only [pow_succ', End.mul_apply] using hr',
    by simp [pow_succ, hc]⟩
  let n := Nat.find hP
  obtain ⟨m, hm, hBm, hCm⟩ : P n := Nat.find_spec hP
  have hBAm : B (A m) = 0 := by
    have hh := LinearMap.congr_fun hab m
    simpa [LieRing.of_associative_ring_bracket, End.mul_apply, hBm] using hh
  have hsmall : (C ^ n) (A m - (n : k) • m) = 0 := by
    have hh := LinearMap.congr_fun (lowering_bracket A B C hbc hac n) m
    simp only [LieRing.of_associative_ring_bracket, End.mul_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, hCm, hBm, map_zero, sub_self] at hh
    rw [map_sub, map_smul]
    have hs : ((n : k) + 1) • ((C ^ n) (A m) - (n : k) • (C ^ n) m) = 0 := by
      rw [smul_sub, smul_smul, ← hh]
    exact (smul_eq_zero.mp hs).resolve_left (Nat.cast_add_one_ne_zero n)
  have hz : A m - (n : k) • m = 0 := by
    by_contra hn
    cases hn' : n with
    | zero => exact hn (by simpa [hn'] using hsmall)
    | succ s =>
      have hs : s < Nat.find hP := by
        change s < n
        rw [hn']
        exact Nat.lt_succ_self s
      exact (Nat.find_min hP hs)
        ⟨A m - (n : k) • m, hn, by simp [hBAm, hBm], by simpa [hn'] using hsmall⟩
  exact ⟨n, m, hm, sub_eq_zero.mp hz, hBm⟩

end Primitive

section RankOne

variable {h e f : L}

private def tripleLinearMap (h e f : L) : Model k →ₗ[k] L where
  toFun x := x.val 0 1 • e + x.val 1 0 • f + x.val 0 0 • h
  map_add' x y := by
    change (x.val 0 1 + y.val 0 1) • e + (x.val 1 0 + y.val 1 0) • f +
      (x.val 0 0 + y.val 0 0) • h = _
    simp only [add_smul]
    abel
  map_smul' a x := by
    change (a * _) • e + (a * _) • f + (a * _) • h = _
    simp only [smul_add, mul_smul, RingHom.id_apply]

omit [CharZero k] in
@[simp] private lemma tripleLinearMap_E : tripleLinearMap h e f (E k) = e := by
  simp [tripleLinearMap, E, Matrix.single]

omit [CharZero k] in
@[simp] private lemma tripleLinearMap_F : tripleLinearMap h e f (F k) = f := by
  simp [tripleLinearMap, F, Matrix.single]

omit [CharZero k] in
@[simp] private lemma tripleLinearMap_H : tripleLinearMap h e f (H k) = h := by
  simp [tripleLinearMap, H, Matrix.single]

omit [CharZero k] in
private def tripleHom (triple : IsSl2Triple h e f) : Model k →ₗ⁅k⁆ L where
  __ := tripleLinearMap h e f
  map_lie' {x y} := by
    have ⟨he₀, hf₀, hef₀⟩ := sl2_relations k
    have he := triple.lie_h_e_smul k
    have hf : ⁅h, f⁆ = (-2 : k) • f := by rw [triple.lie_lie_smul_f k, neg_smul]
    have eh₀ : ⁅E k, H k⁆ = -((2 : k) • E k) := by rw [← lie_skew, he₀]
    have fh₀ : ⁅F k, H k⁆ = -((-2 : k) • F k) := by rw [← lie_skew, hf₀]
    have fe₀ : ⁅F k, E k⁆ = -H k := by rw [← lie_skew, hef₀]
    have eh : ⁅e, h⁆ = -((2 : k) • e) := by rw [← lie_skew, he]
    have fh : ⁅f, h⁆ = -((-2 : k) • f) := by rw [← lie_skew, hf]
    have fe : ⁅f, e⁆ = -h := by rw [← lie_skew, triple.lie_e_f]
    change tripleLinearMap h e f ⁅x, y⁆ = ⁅tripleLinearMap h e f x, tripleLinearMap h e f y⁆
    conv_lhs => rw [sl2_expansion k x, sl2_expansion k y]
    conv_rhs => rw [sl2_expansion k x, sl2_expansion k y]
    simp only [add_lie, lie_add, smul_lie, lie_smul, map_add, map_smul,
      LieAlgebrasAndRepresentations.sl2_e, LieAlgebrasAndRepresentations.sl2_f,
      LieAlgebrasAndRepresentations.sl2_h, lie_self, he₀, hf₀, hef₀, eh₀, fh₀, fe₀,
      map_zero, map_neg, tripleLinearMap_E, tripleLinearMap_F, tripleLinearMap_H,
      he, hf, triple.lie_e_f, eh, fh, fe]

/-- Apply complete reducibility to the actual split rank-one algebra. Each
simple summand has a lowering-string basis over k. -/
theorem rankOneDiagonalization :
    Specs.LinearAlgebraicGroups.Representation.LieHighestExistence.RankOneDiagonalization.{u,v,w} := by
  classical
  intro k L V _ _ _ _ _ _ _ _ _ h e f triple
  let := LieRingModule.compLieHom V (tripleHom (k := k) triple)
  let := LieModule.compLieHom V (tripleHom (k := k) triple)
  let : FiniteDimensional k (Model k) :=
    FiniteDimensional.of_injective (sl2Coordinates k).toLinearMap (sl2Coordinates k).injective
  let : LieAlgebra.IsSimple k (Model k) := sl2_simple k
  have hss : Specs.LieAlgebrasAndRepresentations.SolvableRadical.IsSemisimple_value k (Model k) :=
    LieAlgebra.HasTrivialRadical.radical_eq_bot
  obtain ⟨S, _, hsimple, hS⟩ :=
    LieAlgebrasAndRepresentations.CompleteReducibility.finite_simple_decomposition k (Model k) V hss
  apply top_unique
  rw [← hS.submodule_iSup_eq_top]
  apply iSup_le
  intro W
  let : LieModule.IsIrreducible k (Model k) W.val := hsimple W.val W.property
  let : Nontrivial W.val := (LieSubmodule.nontrivial_iff k (Model k) W.val).mp
    (hsimple W.val W.property).toNontrivial
  obtain ⟨n, m, hm⟩ := exists_primitive (k := k) (V := W.val)
    (LieAlgebrasAndRepresentations.Sl2SimpleModules.standardTriple k)
  let b := LieAlgebrasAndRepresentations.Sl2SimpleModules.highestWeightBasis hm
  have hb := LieAlgebrasAndRepresentations.Sl2SimpleModules.highestWeightBasis_isStandard hm
  intro y hy
  let yW : W.val := ⟨y, hy⟩
  change (yW : V) ∈ _
  rw [← b.sum_repr yW]
  push_cast
  apply Submodule.sum_mem
  intro l _
  apply Submodule.smul_mem
  apply (le_iSup (fun z : ℤ => (toEnd k L V h).eigenspace (z : k))
    ((n : ℤ) - 2 * (l.val : ℤ)))
  apply End.mem_eigenspace_iff.mpr
  push_cast
  have hh := congrArg (fun z : W.val => (z : V)) (hb l).1
  change ⁅tripleLinearMap h e f (H k), (b l : V)⁆ =
    ((n : k) - 2 * (l.val : k)) • (b l : V) at hh
  simpa only [tripleLinearMap_H, toEnd_apply_apply] using hh

end RankOne

section Weights

attribute [local instance] LieRing.ofAssociativeRing

variable {H : Type t} [LieRing H] [LieAlgebra k H]

private abbrev toralOperator (inclusion : H →ₗ⁅k⁆ L) (h : H) : End k V :=
  toEnd k L V (inclusion h)

private abbrev toralWeightSpace (inclusion : H →ₗ⁅k⁆ L) (lam : Dual k H) : Submodule k V :=
  ⨅ h : H, (toralOperator inclusion h).eigenspace (lam h)

omit [CharZero k] in
private lemma maxGenEigenspace_eq_of_eigenspaces_span (A : End k V)
    (hA : (⨆ a : k, A.eigenspace a) = ⊤) (a : k) :
    A.maxGenEigenspace a = A.eigenspace a := by
  have hinv := End.mapsTo_maxGenEigenspace_of_comm (Commute.refl A) a
  rw [Submodule.eq_iSup_inf_genEigenspace (p := A.maxGenEigenspace a) 1 hinv hA]
  change (⨆ b, A.maxGenEigenspace a ⊓ A.eigenspace b) = A.eigenspace a
  refine le_antisymm (iSup_le fun b => ?_) ?_
  · rcases eq_or_ne a b with rfl | hab
    · exact inf_le_right
    · have hd := (A.disjoint_genEigenspace hab ⊤ 1).eq_bot
      exact hd.le.trans bot_le
  · have h := End.eigenspace_le_maxGenEigenspace (f := A) (μ := a)
    simpa only [inf_of_le_right h] using
      (le_iSup (fun b => A.maxGenEigenspace a ⊓ A.eigenspace b) a)

omit [CharZero k] [FiniteDimensional k V] in
private lemma eigenvector_on_span (inclusion : H →ₗ⁅k⁆ L)
    {ι : Type i} (coroot : ι → H) (hspan : Submodule.span k (Set.range coroot) = ⊤)
    (v : V) (hv : v ≠ 0) (a : ι → k)
    (hv' : ∀ l, ⁅inclusion (coroot l), v⁆ = a l • v) :
    ∃ lam : Dual k H, v ∈ (toralWeightSpace inclusion lam : Submodule k V) := by
  obtain ⟨d, hd⟩ := Projective.exists_dual_eq_one k hv
  let T : H →ₗ[k] V := (LinearMap.applyₗ v).comp ((toEnd k L V).comp inclusion).toLinearMap
  let lam := d.comp T
  refine ⟨lam, (Submodule.mem_iInf _).mpr fun h => End.mem_eigenspace_iff.mpr ?_⟩
  have hgen (l : ι) : T (coroot l) = lam (coroot l) • v := by
    change T (coroot l) = d (T (coroot l)) • v
    rw [show T (coroot l) = a l • v from hv' l, map_smul, hd, smul_eq_mul, mul_one]
  have heq : Submodule.span k (Set.range coroot) ≤
      LinearMap.ker (T - (LinearMap.toSpanSingleton k V v).comp lam) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨l, rfl⟩
    exact LinearMap.mem_ker.mpr (sub_eq_zero.mpr (hgen l))
  exact sub_eq_zero.mp (LinearMap.mem_ker.mp (heq (hspan ▸ Submodule.mem_top)))

private lemma toralWeightSpaces_span [IsLieAbelian H] (inclusion : H →ₗ⁅k⁆ L)
    {ι : Type i} (coroot : ι → H) (hspan : Submodule.span k (Set.range coroot) = ⊤)
    (htriple : ∀ l, ∃ e f : L, IsSl2Triple (inclusion (coroot l)) e f) :
    (⨆ lam : Dual k H, (toralWeightSpace inclusion lam : Submodule k V)) = ⊤ := by
  let A (l : ι) : End k V := toralOperator inclusion (coroot l)
  have hcomm (l m : ι) : Commute (A l) (A m) := by
    apply sub_eq_zero.mp
    change ⁅toEnd k L V (inclusion (coroot l)), toEnd k L V (inclusion (coroot m))⁆ = 0
    rw [← LieHom.map_lie, ← LieHom.map_lie, trivial_lie_zero H H, map_zero, map_zero]
  have hspanA (l : ι) : (⨆ a : k, (A l).eigenspace a) = ⊤ := by
    obtain ⟨e, f, ht⟩ := htriple l
    have hr := rankOneDiagonalization k L V ht
    apply top_unique
    rw [← hr]
    exact iSup_le fun n => le_iSup (fun a : k => (A l).eigenspace a) (n : k)
  have hgen (l : ι) (a : k) : (A l).maxGenEigenspace a = (A l).eigenspace a :=
    maxGenEigenspace_eq_of_eigenspaces_span (A l) (hspanA l) a
  have hjoint := End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    A (fun l m _ => hcomm l m) (fun l => by simpa only [hgen] using hspanA l)
  simp only [hgen] at hjoint
  apply top_unique
  rw [← hjoint]
  apply iSup_le
  intro a v hv
  by_cases hz : v = 0
  · simp [hz]
  obtain ⟨lam, hlam⟩ := eigenvector_on_span inclusion coroot hspan v hz a
    (fun l => End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hv l))
  exact le_iSup (fun lam : Dual k H => toralWeightSpace inclusion lam) lam hlam

/-- Maximality is taken in an integer translate in the actual field's spectrum. -/
private lemma exists_maximal_integer_shift [Nontrivial V] (A : End k V)
    (hA : ∃ a, A.HasEigenvalue a) :
    ∃ a, A.HasEigenvalue a ∧ ∀ n : ℤ, 0 < n → ¬ A.HasEigenvalue (a + (n : k)) := by
  classical
  obtain ⟨a, ha⟩ := hA
  let S : Set ℤ := {n | A.HasEigenvalue (a + (n : k))}
  have hS : S.Finite := A.finite_hasEigenvalue.preimage
    (fun _ _ _ _ he => Int.cast_injective (add_left_cancel he))
  have hzero : (0 : ℤ) ∈ S := by simpa [S] using ha
  obtain ⟨n, hn, hnmax⟩ :=
    hS.toFinset.exists_max_image id ⟨0, hS.mem_toFinset.mpr hzero⟩
  refine ⟨a + (n : k), hS.mem_toFinset.mp hn, fun m hm he => ?_⟩
  have hnm : n + m ∈ S := by simpa [S, Int.cast_add, add_assoc] using he
  exact (not_le_of_gt (lt_add_of_pos_right n hm)) (hnmax _ (hS.mem_toFinset.mpr hnm))

omit [CharZero k] [FiniteDimensional k V] in
/-- Each eigenvalue of a toral element occurs on a common toral eigenspace. -/
private lemma weight_of_eigenvalue (inclusion : H →ₗ⁅k⁆ L) (h₀ : H) {a : k}
    (hweights : (⨆ lam : Dual k H, (toralWeightSpace inclusion lam : Submodule k V)) = ⊤)
    (ha : (toralOperator inclusion h₀ : End k V).HasEigenvalue a) :
    ∃ lam : Dual k H, lam h₀ = a ∧ (toralWeightSpace inclusion lam : Submodule k V) ≠ ⊥ := by
  let A : End k V := toralOperator inclusion h₀
  let S : Set k := {b | b ≠ a}
  by_contra! h
  have hle : (⨆ lam : Dual k H, (toralWeightSpace inclusion lam : Submodule k V)) ≤
      ⨆ b ∈ S, A.eigenspace b := by
    apply iSup_le
    intro lam
    by_cases he : lam h₀ = a
    · rw [h lam he]
      exact bot_le
    · exact (iInf_le _ h₀).trans (le_iSup₂ (f := fun b (_ : b ∈ S) => A.eigenspace b) (lam h₀) he)
  rw [hweights] at hle
  have hd := A.eigenspaces_iSupIndep.disjoint_biSup (y := S) (x := a) (by simp [S])
  have hbot : A.eigenspace a = ⊥ := by simpa using (hd.mono_right hle).eq_bot
  exact ha hbot

theorem highestWeightExistence :
    Specs.LinearAlgebraicGroups.Representation.LieHighestExistence.HighestWeightExistence.{u,v,w,t,i,j} := by
  intro k L V H _ _ _ _ _ _ _ _ _ _ _ _ _ inclusion _ ι _ coroot hspan htriple h₀ J x degree hpos
  let A : End k V := toralOperator inclusion h₀
  have hweights := toralWeightSpaces_span (V := V) inclusion coroot hspan htriple
  have hA : ∃ a, A.HasEigenvalue a := by
    by_contra! h
    have hz (lam : Dual k H) : (toralWeightSpace inclusion lam : Submodule k V) = ⊥ :=
      bot_unique ((iInf_le _ h₀).trans (le_of_eq (not_not.mp (h (lam h₀)))))
    have hbot : (⊤ : Submodule k V) = ⊥ := by rw [← hweights]; simp [hz]
    exact top_ne_bot hbot
  obtain ⟨a, ha, hamax⟩ := exists_maximal_integer_shift A hA
  obtain ⟨lam, hlam, hW⟩ := weight_of_eigenvalue inclusion h₀ hweights ha
  obtain ⟨v, hv, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hlie (h : H) : ⁅inclusion h, v⁆ = lam h • v :=
    End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hv h)
  refine ⟨lam, v, hvne, hlie, fun l => ?_⟩
  by_contra hn
  apply hamax (degree l) (hpos l).1
  apply End.hasEigenvalue_of_hasEigenvector
  refine ⟨End.mem_eigenspace_iff.mpr ?_, hn⟩
  change ⁅inclusion h₀, ⁅x l, v⁆⁆ = (a + (degree l : k)) • ⁅x l, v⁆
  rw [leibniz_lie, (hpos l).2, hlie h₀, hlam, smul_lie, lie_smul, ← add_smul, add_comm]

end Weights

end LinearAlgebraicGroups.Representation.LieHighestExistence
