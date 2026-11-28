import MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.SuperMatrices
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.SuperRankOneSimples
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

namespace LieNotes.SuperRestricted.SuperRankOneSimples

open Specs.LieNotes.SuperRestricted.SuperRankOneSimples
open Specs.LieNotes.SuperRestricted.SuperMatrices (Mat parity_cases bracketTable
  zValue hValue eValue fValue)
open SuperMatrices (z h e f generator basis generator_mem)

universe u v

variable {L : Algebra} {M : Type u} [AddCommGroup M] [Module ℂ M]
  {G : Grading ℂ M} (A : GradedModule L G)
variable {N : Type v} [AddCommGroup N] [Module ℂ N] {J : Grading ℂ N}

theorem concrete_model : MatrixModel (SuperMatrices.gl ℂ) := ⟨rfl, rfl⟩

private theorem zero_ne_one : (0 : ZMod 2) ≠ 1 := by decide

private theorem opposite_ne (p : ZMod 2) : 1 + p ≠ p := by
  rcases parity_cases p with rfl | rfl <;> decide

private theorem parity_compl (G : Grading ℂ M) : IsCompl (G.piece 0) (G.piece 1) := by
  apply (DirectSum.isInternal_submodule_iff_isCompl G.piece zero_ne_one ?_).1 G.isInternal
  ext i
  simpa using parity_cases i

private theorem split (G : Grading ℂ M) (m : M) :
    ∃ a ∈ G.piece 0, ∃ b ∈ G.piece 1, a + b = m :=
  Submodule.mem_sup.mp (by rw [(parity_compl G).sup_eq_top]; exact Submodule.mem_top)

private theorem distinct_pieces (G : Grading ℂ M) {i j : ZMod 2} (hij : i ≠ j)
    {x : M} (hi : x ∈ G.piece i) (hj : x ∈ G.piece j) : x = 0 := by
  rcases parity_cases i with rfl | rfl <;> rcases parity_cases j with rfl | rfl
  · exact (hij rfl).elim
  · exact Submodule.disjoint_def.mp (parity_compl G).disjoint x hi hj
  · exact Submodule.disjoint_def.mp (parity_compl G).disjoint x hj hi
  · exact (hij rfl).elim

private theorem stable_of_generators {S : Submodule ℂ M}
    (hs : ∀ i : Fin 4, ∀ m ∈ S, A.act (generator ℂ i) m ∈ S) : Stable A S := by
  intro x m hm
  let T : Submodule ℂ (Mat ℂ) := S.comap ((LinearMap.applyₗ (R := ℂ) m).comp A.act)
  have hle : Submodule.span ℂ (Set.range (basis ℂ)) ≤ T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [SuperMatrices.basis_apply]
    exact hs i m hm
  exact hle (by rw [(basis ℂ).span_eq]; exact Submodule.mem_top)

private theorem graded_span {v w : M} {p : ZMod 2} (hv : v ∈ G.piece p)
    (hw : w ∈ G.piece (1 + p)) : IsGraded G ((ℂ ∙ v) ⊔ (ℂ ∙ w)) := by
  intro m hm
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hm
  have hpa := ((Submodule.span_singleton_le_iff_mem _ _).mpr hv) ha
  have hpb := ((Submodule.span_singleton_le_iff_mem _ _).mpr hw) hb
  rcases parity_cases p with rfl | rfl
  · exact ⟨a, hpa, b, by simpa using hpb, (show ℂ ∙ v ≤ (ℂ ∙ v) ⊔ (ℂ ∙ w) from le_sup_left) ha, (show ℂ ∙ w ≤ (ℂ ∙ v) ⊔ (ℂ ∙ w) from le_sup_right) hb, hab⟩
  · exact ⟨b, by simpa only [show (1 : ZMod 2) + 1 = 0 by decide] using hpb,
      a, hpa, (show ℂ ∙ w ≤ (ℂ ∙ v) ⊔ (ℂ ∙ w) from le_sup_right) hb, (show ℂ ∙ v ≤ (ℂ ∙ v) ⊔ (ℂ ∙ w) from le_sup_left) ha, (add_comm b a).trans hab⟩

private theorem gen_mem (hm : MatrixModel L) (i : Fin 4) :
    generator ℂ i ∈ L.grading.piece (if i < 2 then 0 else 1) :=
  hm.1.symm ▸ generator_mem ℂ i

private theorem matrix_bracket (hm : MatrixModel L) : L.bracket = SuperMatrices.bracket ℂ := hm.2

private theorem z_comm (hm : MatrixModel L) (i : Fin 4) (m : M) :
    A.act (z ℂ) (A.act (generator ℂ i) m) =
      A.act (generator ℂ i) (A.act (z ℂ) m) := by
  have hz : z ℂ ∈ L.grading.piece 0 := gen_mem hm 0
  have hr := A.map_bracket hz (gen_mem hm i)
  rw [matrix_bracket hm, (SuperMatrices.central ℂ _).1, map_zero, paritySign_zero_left, one_smul] at hr
  exact sub_eq_zero.mp (by
    symm
    exact LinearMap.congr_fun hr m)

private theorem even_mem (hm : MatrixModel L) :
    h ℂ ∈ L.grading.piece 0 := gen_mem hm 1

private theorem e_mem (hm : MatrixModel L) :
    e ℂ ∈ L.grading.piece 1 := gen_mem hm 2

private theorem f_mem (hm : MatrixModel L) :
    f ℂ ∈ L.grading.piece 1 := gen_mem hm 3

private theorem odd_square {x : Mat ℂ}
    (hx : x ∈ L.grading.piece 1) (hb : L.bracket x x = 0) (m : M) :
    A.act x (A.act x m) = 0 := by
  have hr := A.map_bracket hx hx
  rw [hb, map_zero, paritySign_one_one, neg_one_smul, sub_neg_eq_add] at hr
  have hzero : (2 : ℂ) • A.act x (A.act x m) = 0 := by
    simpa only [two_smul, LinearMap.zero_apply, LinearMap.add_apply, Module.End.mul_apply]
      using (LinearMap.congr_fun hr m).symm
  exact (smul_eq_zero.mp hzero).resolve_left (by norm_num)

private theorem e_square (hm : MatrixModel L) (m : M) : A.act (e ℂ) (A.act (e ℂ) m) = 0 :=
  odd_square A (e_mem hm) (by rw [matrix_bracket hm]; exact SuperMatrices.bracket_e_e ℂ) m

private theorem f_square (hm : MatrixModel L) (m : M) : A.act (f ℂ) (A.act (f ℂ) m) = 0 :=
  odd_square A (f_mem hm) (by rw [matrix_bracket hm]; exact SuperMatrices.bracket_f_f ℂ) m

private theorem e_h (hm : MatrixModel L) (m : M) :
    A.act (e ℂ) (A.act (h ℂ) m) = A.act (h ℂ) (A.act (e ℂ) m) - A.act (e ℂ) m := by
  have hr := A.map_bracket (even_mem hm) (e_mem hm)
  rw [matrix_bracket hm, SuperMatrices.bracket_h_e, paritySign_zero_left, one_smul] at hr
  have hr' := LinearMap.congr_fun hr m
  exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans (eq_sub_iff_add_eq.mp hr'))

private theorem h_f (hm : MatrixModel L) (m : M) :
    A.act (h ℂ) (A.act (f ℂ) m) = A.act (f ℂ) (A.act (h ℂ) m) - A.act (f ℂ) m := by
  have hr := A.map_bracket (even_mem hm) (f_mem hm)
  rw [matrix_bracket hm, SuperMatrices.bracket_h_f, map_neg, paritySign_zero_left, one_smul] at hr
  have hr' := LinearMap.congr_fun hr m
  exact (sub_eq_iff_eq_add.mp hr'.symm).trans (neg_add_eq_sub _ _)

private theorem e_f (hm : MatrixModel L) (m : M) :
    A.act (e ℂ) (A.act (f ℂ) m) =
      A.act (z ℂ) m - A.act (f ℂ) (A.act (e ℂ) m) := by
  have hr := A.map_bracket (e_mem hm) (f_mem hm)
  rw [matrix_bracket hm, SuperMatrices.bracket_e_f, paritySign_one_one, neg_one_smul, sub_neg_eq_add] at hr
  exact eq_sub_iff_add_eq.mpr (LinearMap.congr_fun hr m).symm

private theorem central_scalar [FiniteDimensional ℂ M] (hm : MatrixModel L)
    (hs : Simple A) : ∃ γ : ℂ, ∀ m : M, A.act (z ℂ) m = γ • m := by
  let ⟨m, hm0⟩ := hs.1
  let : Nontrivial M := ⟨⟨m, 0, hm0⟩⟩
  obtain ⟨γ, hγ⟩ := (A.act (z ℂ)).exists_eigenvalue
  obtain ⟨t, ht, ht0⟩ := hγ.exists_hasEigenvector
  let S := (A.act (z ℂ)).eigenspace γ
  have hsgrade : IsGraded G S := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := split G x
    have hz : z ℂ ∈ L.grading.piece 0 := gen_mem hm 0
    have ha' : A.act (z ℂ) a - γ • a ∈ G.piece 0 :=
      (G.piece 0).sub_mem (by simpa using A.act_mem hz ha) ((G.piece 0).smul_mem _ ha)
    have hb' : A.act (z ℂ) b - γ • b ∈ G.piece 1 :=
      (G.piece 1).sub_mem (by simpa using A.act_mem hz hb) ((G.piece 1).smul_mem _ hb)
    have hx' := Module.End.mem_eigenspace_iff.mp hx
    rw [map_add, smul_add] at hx'
    have hsum : (A.act (z ℂ) a - γ • a) + (A.act (z ℂ) b - γ • b) = 0 := by
      rw [sub_add_sub_comm, hx', sub_self]
    have ha0 := distinct_pieces G zero_ne_one ha'
      (by rw [eq_neg_iff_add_eq_zero.mpr hsum]; exact (G.piece 1).neg_mem hb')
    have hb0 : A.act (z ℂ) b - γ • b = 0 := by simpa only [ha0, zero_add] using hsum
    exact ⟨a, ha, b, hb, Module.End.mem_eigenspace_iff.mpr (sub_eq_zero.mp ha0),
      Module.End.mem_eigenspace_iff.mpr (sub_eq_zero.mp hb0), rfl⟩
  have hstable : Stable A S := by
    apply stable_of_generators A
    intro i x hx
    exact Module.End.mem_eigenspace_iff.mpr (by
      rw [z_comm A hm i, Module.End.mem_eigenspace_iff.mp hx, map_smul])
  have htop : S = ⊤ := (hs.2 S hsgrade hstable).resolve_left
    (fun h => ht0 ((Submodule.eq_bot_iff S).mp h t ht))
  exact ⟨γ, fun x => Module.End.mem_eigenspace_iff.mp
    (show x ∈ S by rw [htop]; exact Submodule.mem_top)⟩

private theorem highest_vector [FiniteDimensional ℂ M] (hm : MatrixModel L)
    (m : M) (hm0 : m ≠ 0) :
    ∃ (p : ZMod 2) (lam : ℂ) (v : M), v ≠ 0 ∧ v ∈ G.piece p ∧
      A.act (e ℂ) v = 0 ∧ A.act (h ℂ) v = lam • v := by
  obtain ⟨p, x, hx, hx0⟩ : ∃ (p : ZMod 2) (x : M), x ∈ G.piece p ∧ x ≠ 0 := by
    obtain ⟨a, ha, b, hb, rfl⟩ := split G m
    by_cases ha0 : a = 0
    · exact ⟨1, b, hb, by simpa [ha0] using hm0⟩
    · exact ⟨0, a, ha, ha0⟩
  obtain ⟨p, y, hy, hy0, hey⟩ : ∃ (p : ZMod 2) (y : M),
      y ∈ G.piece p ∧ y ≠ 0 ∧ A.act (e ℂ) y = 0 := by
    by_cases he : A.act (e ℂ) x = 0
    · exact ⟨p, x, hx, hx0, he⟩
    · exact ⟨1 + p, A.act (e ℂ) x, A.act_mem (e_mem hm) hx, he, e_square A hm x⟩
  let S := (A.act (e ℂ)).ker ⊓ G.piece p
  let : Nontrivial S := ⟨⟨⟨y, LinearMap.mem_ker.mpr hey, hy⟩, 0,
    fun h => hy0 (congrArg Subtype.val h)⟩⟩
  let H : Module.End ℂ S := (A.act (h ℂ)).restrict (by
    intro s hs
    refine ⟨LinearMap.mem_ker.mpr ?_, ?_⟩
    · rw [e_h A hm, LinearMap.mem_ker.mp hs.1, map_zero, sub_zero]
    · simpa using A.act_mem (even_mem hm) hs.2)
  obtain ⟨lam, hlam⟩ := H.exists_eigenvalue
  obtain ⟨v, hv, hv0⟩ := hlam.exists_hasEigenvector
  exact ⟨p, lam, v, fun h => hv0 (Subtype.ext h), v.property.2,
    LinearMap.mem_ker.mp v.property.1,
    congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp hv)⟩

private theorem span_stable {v w : M}
    (hv : ∀ i : Fin 4, A.act (generator ℂ i) v ∈ (ℂ ∙ v) ⊔ (ℂ ∙ w))
    (hw : ∀ i : Fin 4, A.act (generator ℂ i) w ∈ (ℂ ∙ v) ⊔ (ℂ ∙ w)) :
    Stable A ((ℂ ∙ v) ⊔ (ℂ ∙ w)) := by
  apply stable_of_generators A
  intro i m hm
  obtain ⟨_, ha, _, hb, rfl⟩ := Submodule.mem_sup.mp hm
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp ha
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hb
  rw [map_add, map_smul, map_smul]
  exact Submodule.add_mem _ (Submodule.smul_mem _ a (hv i)) (Submodule.smul_mem _ b (hw i))

theorem exhaust : exhaustType.{u} := by
  intro L hm M _ _ _ G A hs
  obtain ⟨γ, hz⟩ := central_scalar A hm hs
  obtain ⟨m, hm0⟩ := hs.1
  obtain ⟨p, lam, v, hv0, hvp, hev, hhv⟩ := highest_vector A hm m hm0
  let w := A.act (f ℂ) v
  have hwp : w ∈ G.piece (1 + p) := A.act_mem (f_mem hm) hvp
  have hfw : A.act (f ℂ) w = 0 := f_square A hm v
  have hew : A.act (e ℂ) w = γ • v := by dsimp only [w]; rw [e_f A hm, hz, hev, map_zero, sub_zero]
  have hhw : A.act (h ℂ) w = (lam - 1) • w := by
    dsimp only [w]
    rw [h_f A hm, hhv, map_smul, sub_smul, one_smul]
  let S := (ℂ ∙ v) ⊔ (ℂ ∙ w)
  have hvS : v ∈ S := Submodule.mem_sup.mpr ⟨v, Submodule.mem_span_singleton_self v, 0, Submodule.zero_mem _, add_zero _⟩
  have hwS : w ∈ S := Submodule.mem_sup.mpr ⟨0, Submodule.zero_mem _, w, Submodule.mem_span_singleton_self w, zero_add _⟩
  have htop : S = ⊤ := by
    apply (hs.2 S (graded_span hvp hwp) ?_).resolve_left
    · exact fun h => hv0 ((Submodule.eq_bot_iff S).mp h v hvS)
    · apply span_stable A
      · intro i
        fin_cases i
        · exact hz v ▸ S.smul_mem γ hvS
        · exact hhv ▸ S.smul_mem lam hvS
        · exact hev ▸ S.zero_mem
        · exact hwS
      · intro i
        fin_cases i
        · exact hz w ▸ S.smul_mem γ hwS
        · exact hhw ▸ S.smul_mem (lam - 1) hwS
        · exact hew ▸ S.smul_mem γ hvS
        · exact hfw ▸ S.zero_mem
  refine ⟨γ, lam, p, hz, ⟨v, w, hv0, hvp, hwp, htop, ?_, hhv, hhw, rfl, hfw,
    hev, hew, hz v, hz w⟩⟩
  intro hγ
  by_contra hw0
  let W := ℂ ∙ w
  have hwW : w ∈ W := Submodule.mem_span_singleton_self w
  have hWstable : Stable A W := by
    apply stable_of_generators A
    intro i t ht
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp ht
    rw [map_smul]
    apply W.smul_mem
    fin_cases i
    · exact hz w ▸ W.smul_mem γ hwW
    · exact hhw ▸ W.smul_mem (lam - 1) hwW
    · change A.act (e ℂ) w ∈ W
      rw [hew, hγ, zero_smul]
      exact W.zero_mem
    · exact hfw ▸ W.zero_mem
  have hWgraded : IsGraded G W := by
    simpa only [Submodule.span_zero_singleton, sup_bot_eq] using
      (graded_span hwp (show (0 : M) ∈ G.piece (1 + (1 + p)) from Submodule.zero_mem _))
  have hWtop := (hs.2 W hWgraded hWstable).resolve_left
    (fun h => hw0 ((Submodule.eq_bot_iff W).mp h w hwW))
  have hvW : v ∈ W := by rw [hWtop]; exact Submodule.mem_top
  exact hv0 (distinct_pieces G (Ne.symm (opposite_ne p)) hvp
    (((Submodule.span_singleton_le_iff_mem _ _).mpr hwp) hvW))

section Forms

variable {A} {B : GradedModule L J} {γ lam : ℂ} {p : ZMod 2}
variable (P : Form A γ lam p)

private theorem coordinates (m : M) : ∃ a b : ℂ, a • P.v + b • P.w = m := by
  have hm : m ∈ (ℂ ∙ P.v) ⊔ (ℂ ∙ P.w) := by rw [P.generates]; exact Submodule.mem_top
  obtain ⟨_, ha, _, hb, rfl⟩ := Submodule.mem_sup.mp hm
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp ha
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hb
  exact ⟨a, b, rfl⟩

private theorem w_ne_zero (hγ : γ ≠ 0) : P.w ≠ 0 := by
  intro hw
  have hs : γ • P.v = 0 := by simpa only [hw, map_zero] using P.ew.symm
  exact P.v_ne ((smul_eq_zero.mp hs).resolve_left hγ)

private theorem action_e_coords (a b : ℂ) :
    A.act (e ℂ) (a • P.v + b • P.w) = (b * γ) • P.v := by
  rw [map_add, map_smul, map_smul, P.ev, P.ew, smul_zero, zero_add, smul_smul]

private theorem action_f_coords (a b : ℂ) :
    A.act (f ℂ) (a • P.v + b • P.w) = a • P.w := by
  rw [map_add, map_smul, map_smul, P.fv, P.fw, smul_zero, add_zero]

private theorem ker_e : (A.act (e ℂ)).ker = ℂ ∙ P.v := by
  apply le_antisymm
  · intro m hm
    obtain ⟨a, b, rfl⟩ := coordinates P m
    have hab : (b * γ) • P.v = 0 := (action_e_coords P a b).symm.trans (LinearMap.mem_ker.mp hm)
    rcases mul_eq_zero.mp ((smul_eq_zero.mp hab).resolve_right P.v_ne) with hb | hγ
    · exact Submodule.mem_span_singleton.mpr ⟨a, by simp [hb]⟩
    · exact Submodule.mem_span_singleton.mpr ⟨a, by simp [P.w_zero hγ]⟩
  · exact (Submodule.span_singleton_le_iff_mem _ _).mpr (LinearMap.mem_ker.mpr P.ev)

theorem opposite : oppositeType.{u} := by
  intro L M _ _ G A γ lam p P
  refine ⟨ker_e P, ?_, ?_⟩
  · intro hγ
    refine ⟨?_, P.v_ne, P.v_mem, P.hv⟩
    apply le_antisymm
    · intro m _
      obtain ⟨a, b, rfl⟩ := coordinates P m
      exact Submodule.mem_span_singleton.mpr ⟨a, by simp [P.w_zero hγ]⟩
    · apply (Submodule.span_singleton_le_iff_mem _ _).mpr
      exact LinearMap.mem_ker.mpr (P.fv.trans (P.w_zero hγ))
  · intro hγ
    refine ⟨?_, w_ne_zero P hγ, P.w_mem, opposite_ne p, P.hw⟩
    apply le_antisymm
    · intro m hm
      obtain ⟨a, b, rfl⟩ := coordinates P m
      have hab : a • P.w = 0 := (action_f_coords P a b).symm.trans (LinearMap.mem_ker.mp hm)
      have ha := (smul_eq_zero.mp hab).resolve_right (w_ne_zero P hγ)
      exact Submodule.mem_span_singleton.mpr ⟨b, by simp [ha]⟩
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr (LinearMap.mem_ker.mpr P.fw)

private theorem smul_mem_of_ne_zero {S : Submodule ℂ M} {c : ℂ} (hc : c ≠ 0)
    {x : M} (hx : c • x ∈ S) : x ∈ S := by
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using S.smul_mem c⁻¹ hx

theorem forms_simple : formsSimpleType.{u} := by
  intro L _ M _ _ G A γ lam p P
  refine ⟨⟨P.v, P.v_ne⟩, fun S _ hs => ?_⟩
  by_cases hS : S = ⊥
  · exact Or.inl hS
  · right
    obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
    obtain ⟨a, b, rfl⟩ := coordinates P m
    have hv : P.v ∈ S := by
      by_cases hbγ : b * γ = 0
      · have hb : b • P.w = 0 := by
          rcases mul_eq_zero.mp hbγ with hb | hγ
          · simp [hb]
          · simp [P.w_zero hγ]
        rw [hb, add_zero] at hm hm0
        exact smul_mem_of_ne_zero (fun ha => hm0 (by simp [ha])) hm
      · exact smul_mem_of_ne_zero hbγ (action_e_coords P a b ▸ hs (e ℂ) hm)
    have hw : P.w ∈ S := P.fv ▸ hs (f ℂ) hv
    apply top_unique
    rw [← P.generates]
    exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hv)
      ((Submodule.span_singleton_le_iff_mem _ _).mpr hw)

theorem form_basis : basisType.{u} := by
  intro L M _ _ G A γ lam p P
  constructor
  · intro hγ
    have hspan : ℂ ∙ P.v = ⊤ := by simpa [P.w_zero hγ] using P.generates
    let q : Fin 1 → M := fun _ => P.v
    have hli : LinearIndependent ℂ q := linearIndependent_unique_iff.mpr P.v_ne
    have hsp : ⊤ ≤ Submodule.span ℂ (Set.range q) := by simpa [q] using hspan.ge
    exact ⟨Module.Basis.mk hli hsp, Module.Basis.mk_apply _ _ _⟩
  · intro hγ
    let q : Fin 2 → M := ![P.v, P.w]
    have hli : LinearIndependent ℂ q := by
      apply linearIndependent_fin2.mpr
      refine ⟨w_ne_zero P hγ, fun a ha => P.v_ne ?_⟩
      change a • P.w = P.v at ha
      exact distinct_pieces G (Ne.symm (opposite_ne p)) P.v_mem
        (ha ▸ (G.piece (1 + p)).smul_mem a P.w_mem)
    have hspan : ⊤ ≤ Submodule.span ℂ (Set.range q) := by
      rw [← P.generates]
      exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr (Submodule.subset_span ⟨0, rfl⟩))
        ((Submodule.span_singleton_le_iff_mem _ _).mpr (Submodule.subset_span ⟨1, rfl⟩))
    exact ⟨Module.Basis.mk hli hspan, Module.Basis.mk_apply _ _ _, Module.Basis.mk_apply _ _ _⟩

private def coordinateMap : (ℂ × ℂ) →ₗ[ℂ] M where
  toFun c := c.1 • P.v + c.2 • P.w
  map_add' a b := by simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel
  map_smul' a b := by simp [smul_add, smul_smul]

private theorem coordinateMap_apply (a b : ℂ) :
    coordinateMap P (a, b) = a • P.v + b • P.w := rfl

private theorem coordinateMap_surj : Function.Surjective (coordinateMap P) :=
  fun m => (coordinates P m).elim fun a ⟨b, hab⟩ => ⟨(a, b), hab⟩

private theorem coordinateMap_zero (a b : ℂ) :
    coordinateMap P (a, b) = 0 ↔ a = 0 ∧ (γ = 0 ∨ b = 0) := by
  rw [coordinateMap_apply]
  constructor
  · intro h
    have ha : a • P.v = 0 := distinct_pieces G (Ne.symm (opposite_ne p))
      ((G.piece p).smul_mem a P.v_mem)
      (by rw [eq_neg_iff_add_eq_zero.mpr h]; exact (G.piece _).neg_mem ((G.piece _).smul_mem b P.w_mem))
    refine ⟨(smul_eq_zero.mp ha).resolve_right P.v_ne, ?_⟩
    by_cases hγ : γ = 0
    · exact Or.inl hγ
    · rw [ha, zero_add] at h
      exact Or.inr ((smul_eq_zero.mp h).resolve_right (w_ne_zero P hγ))
  · rintro ⟨rfl, hγ | rfl⟩
    · simp [P.w_zero hγ]
    · simp

include P in
private theorem same_parameters_iso (Q : Form B γ lam p) : GradedIso A B := by
  have hker : (coordinateMap P).ker = (coordinateMap Q).ker := by
    ext ⟨a, b⟩
    rw [LinearMap.mem_ker, LinearMap.mem_ker, coordinateMap_zero, coordinateMap_zero]
  let T := (coordinateMap P).liftOfSurjective (coordinateMap_surj P)
    ⟨coordinateMap Q, hker.le⟩
  have hT (c : ℂ × ℂ) : T (coordinateMap P c) = coordinateMap Q c :=
    LinearMap.equivOfSurjective_apply (coordinateMap_surj P) hker.le
  have hT' (a b : ℂ) : T (a • P.v + b • P.w) = a • Q.v + b • Q.w := hT (a, b)
  have hTv : T P.v = Q.v := by simpa using hT' 1 0
  have hTw : T P.w = Q.w := by simpa using hT' 0 1
  refine ⟨⟨T, ?_, ?_⟩, ?_, ?_⟩
  · intro i m hm
    obtain ⟨a, b, rfl⟩ := coordinates P m
    by_cases hip : i = p
    · subst i
      have hb : b • P.w ∈ G.piece p := by
        simpa only [add_sub_cancel_left] using
          (G.piece p).sub_mem hm ((G.piece p).smul_mem a P.v_mem)
      have hb0 := distinct_pieces G (opposite_ne p) ((G.piece _).smul_mem b P.w_mem) hb
      rw [hb0, add_zero, map_smul, hTv]
      exact (J.piece p).smul_mem a Q.v_mem
    · have hi : i = 1 + p := by
        rcases parity_cases i with rfl | rfl <;> rcases parity_cases p with rfl | rfl
        · exact (hip rfl).elim
        · decide
        · decide
        · exact (hip rfl).elim
      subst i
      have ha : a • P.v ∈ G.piece (1 + p) := by
        simpa only [add_sub_cancel_right] using
          (G.piece (1 + p)).sub_mem hm ((G.piece (1 + p)).smul_mem b P.w_mem)
      rw [distinct_pieces G (Ne.symm (opposite_ne p)) ((G.piece p).smul_mem a P.v_mem) ha,
        zero_add, map_smul, hTw]
      exact (J.piece _).smul_mem b Q.w_mem
  · intro x m
    have hgen (i : Fin 4) : T (A.act (generator ℂ i) m) = B.act (generator ℂ i) (T m) := by
      have hv : T (A.act (generator ℂ i) P.v) = B.act (generator ℂ i) (T P.v) := by
        fin_cases i
        · change T (A.act (z ℂ) P.v) = B.act (z ℂ) (T P.v)
          rw [P.zv, map_smul, hTv, Q.zv]
        · change T (A.act (h ℂ) P.v) = B.act (h ℂ) (T P.v)
          rw [P.hv, map_smul, hTv, Q.hv]
        · change T (A.act (e ℂ) P.v) = B.act (e ℂ) (T P.v)
          rw [P.ev, map_zero, hTv, Q.ev]
        · change T (A.act (f ℂ) P.v) = B.act (f ℂ) (T P.v)
          rw [P.fv, hTv, hTw, Q.fv]
      have hw : T (A.act (generator ℂ i) P.w) = B.act (generator ℂ i) (T P.w) := by
        fin_cases i
        · change T (A.act (z ℂ) P.w) = B.act (z ℂ) (T P.w)
          rw [P.zw, map_smul, hTw, Q.zw]
        · change T (A.act (h ℂ) P.w) = B.act (h ℂ) (T P.w)
          rw [P.hw, map_smul, hTw, Q.hw]
        · change T (A.act (e ℂ) P.w) = B.act (e ℂ) (T P.w)
          rw [P.ew, map_smul, hTv, hTw, Q.ew]
        · change T (A.act (f ℂ) P.w) = B.act (f ℂ) (T P.w)
          rw [P.fw, map_zero, hTw, Q.fw]
      obtain ⟨a, b, rfl⟩ := coordinates P m
      simp only [map_add, map_smul, hv, hw]
    let U := T.comp ((LinearMap.applyₗ (R := ℂ) m).comp A.act)
    let V := (LinearMap.applyₗ (R := ℂ) (T m)).comp B.act
    have huv : U = V := (basis ℂ).ext (fun i => by
      rw [SuperMatrices.basis_apply]
      exact hgen i)
    exact LinearMap.congr_fun huv x
  · apply LinearMap.ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).2
    intro m hm
    obtain ⟨c, rfl⟩ := coordinateMap_surj P m
    have hq : c ∈ (coordinateMap Q).ker :=
      LinearMap.mem_ker.mpr ((hT c).symm.trans (LinearMap.mem_ker.mp hm))
    rw [← hker] at hq
    exact LinearMap.mem_ker.mp hq
  · intro n
    obtain ⟨c, rfl⟩ := coordinateMap_surj Q n
    exact ⟨coordinateMap P c, hT c⟩

theorem isomorphic : isomorphicType.{u, v} := by
  intro L _ M _ _ G N _ _ J A B γ lam γ' lam' p p' P Q
  constructor
  · rintro ⟨T, hinj, _⟩
    have hTv : T.toLinearMap P.v ≠ 0 := fun hz => P.v_ne (hinj (hz.trans (map_zero _).symm))
    have hE : T.toLinearMap P.v ∈ (B.act (e ℂ)).ker := LinearMap.mem_ker.mpr (by
      rw [← T.intertwines, P.ev, map_zero])
    rw [ker_e Q] at hE
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hE
    have hγ : γ • T.toLinearMap P.v = γ' • T.toLinearMap P.v := by
      rw [← map_smul, ← P.zv, T.intertwines, ← ha, map_smul, Q.zv, smul_comm a γ']
    have hlam : lam • T.toLinearMap P.v = lam' • T.toLinearMap P.v := by
      rw [← map_smul, ← P.hv, T.intertwines, ← ha, map_smul, Q.hv, smul_comm a lam']
    have hp : p = p' := by
      by_contra h
      exact hTv (distinct_pieces J h (T.map_piece P.v_mem)
        (ha ▸ (J.piece p').smul_mem a Q.v_mem))
    exact ⟨smul_left_injective ℂ hTv hγ, smul_left_injective ℂ hTv hlam, hp⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact same_parameters_iso P Q

end Forms

section Construction

private def degree (i : Fin 4) : ZMod 2 := if i < 2 then 0 else 1

private def homogeneousGenerators (i : ZMod 2) : Set (Mat ℂ) :=
  {x | ∃ j : Fin 4, generator ℂ j = x ∧ degree j = i}

private theorem homogeneous_span (hm : MatrixModel L) {i : ZMod 2} {x : Mat ℂ}
    (hx : x ∈ L.grading.piece i) : x ∈ Submodule.span ℂ (homogeneousGenerators i) := by
  have hgen (j : Fin 4) : generator ℂ j ∈ Submodule.span ℂ (homogeneousGenerators (degree j)) :=
    Submodule.subset_span ⟨j, rfl, rfl⟩
  rw [hm.1] at hx
  rcases parity_cases i with rfl | rfl
  · obtain ⟨h01, h10⟩ := (SuperMatrices.mem_even ℂ).mp hx
    have hx' : x = x 1 1 • z ℂ + (x 0 0 - x 1 1) • h ℂ := by
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [zValue, hValue, Matrix.single, h01, h10]
    rw [hx']
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hgen 0)) (Submodule.smul_mem _ _ (hgen 1))
  · obtain ⟨h00, h11⟩ := (SuperMatrices.mem_odd ℂ).mp hx
    have hx' : x = x 0 1 • e ℂ + x 1 0 • f ℂ := by
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [eValue, fValue, Matrix.single, h00, h11]
    rw [hx']
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hgen 2)) (Submodule.smul_mem _ _ (hgen 3))

private noncomputable def matrixAction (T : Fin 4 → Module.End ℂ M) :
    Mat ℂ →ₗ[ℂ] Module.End ℂ M :=
  (basis ℂ).constr ℂ T

@[simp] private theorem matrixAction_generator (T : Fin 4 → Module.End ℂ M) (i : Fin 4) :
    matrixAction T (generator ℂ i) = T i := by
  rw [← SuperMatrices.basis_apply, matrixAction]
  exact (basis ℂ).constr_basis ℂ T i

private theorem matrixAction_z (T : Fin 4 → Module.End ℂ M) :
    matrixAction T (zValue ℂ) = T 0 := matrixAction_generator T 0

private theorem matrixAction_e (T : Fin 4 → Module.End ℂ M) :
    matrixAction T (eValue ℂ) = T 2 := matrixAction_generator T 2

private theorem matrixAction_f (T : Fin 4 → Module.End ℂ M) :
    matrixAction T (fValue ℂ) = T 3 := matrixAction_generator T 3

private noncomputable def moduleOfGenerators (hm : MatrixModel L)
    (T : Fin 4 → Module.End ℂ M)
    (hgrade : ∀ (i : Fin 4) (j : ZMod 2) (m : M), m ∈ G.piece j →
      T i m ∈ G.piece (degree i + j))
    (hrel : ∀ i j : Fin 4, matrixAction T (bracketTable ℂ i j) =
      T i * T j - paritySign ℂ (degree i) (degree j) • (T j * T i)) :
    GradedModule L G where
  act := matrixAction T
  act_mem := by
    intro i j x m hx hm'
    refine Submodule.span_induction (p := fun x _ => matrixAction T x m ∈ G.piece (i + j))
      ?_ ?_ ?_ ?_ (homogeneous_span hm hx)
    · rintro _ ⟨a, rfl, rfl⟩
      rw [matrixAction_generator]
      exact hgrade a j m hm'
    · simp
    · intro x y _ _ hx hy
      simp only [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ hx hy
    · intro c x _ hx
      simp only [map_smul, LinearMap.smul_apply]
      exact Submodule.smul_mem _ c hx
  map_bracket := by
    intro i j x y hx hy
    let ρ := matrixAction T
    let mult := (LinearMap.mul ℂ (Module.End ℂ M)).compl₁₂ ρ ρ
    let D := L.bracket.compr₂ ρ - (mult - paritySign ℂ i j • mult.flip)
    apply sub_eq_zero.mp
    change D x y = 0
    refine Submodule.span_induction₂ (p := fun x y _ _ => D x y = 0)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ (homogeneous_span hm hx) (homogeneous_span hm hy)
    · rintro _ _ ⟨a, rfl, rfl⟩ ⟨b, rfl, rfl⟩
      change ρ (L.bracket (generator ℂ a) (generator ℂ b)) -
        (ρ (generator ℂ a) * ρ (generator ℂ b) -
          paritySign ℂ (degree a) (degree b) • (ρ (generator ℂ b) * ρ (generator ℂ a))) = 0
      dsimp only [ρ]
      rw [matrix_bracket hm, SuperMatrices.bracket_table, matrixAction_generator,
        matrixAction_generator, hrel, sub_self]
    · simp
    · simp
    · intro x y z _ _ _ hx hy
      simp [hx, hy]
    · intro x y z _ _ _ hy hz
      simp [hy, hz]
    · intro c x y _ _ hxy
      simp [hxy]
    · intro c x y _ _ hxy
      simp [hxy]

private def gradingFromCompl (p : ZMod 2) (S T : Submodule ℂ M)
    (hST : IsCompl S T) : Grading ℂ M where
  piece i := if i = p then S else T
  isInternal := by
    apply (DirectSum.isInternal_submodule_iff_isCompl _ zero_ne_one ?_).2
    · rcases parity_cases p with rfl | rfl
      · simpa [Ne.symm zero_ne_one] using hST
      · simpa [zero_ne_one] using hST.symm
    · ext i
      simpa using parity_cases i

private def firstAxis : Submodule ℂ (ℂ × ℂ) := (LinearMap.snd ℂ ℂ ℂ).ker

private def secondAxis : Submodule ℂ (ℂ × ℂ) := (LinearMap.fst ℂ ℂ ℂ).ker

private theorem axes_compl : IsCompl firstAxis secondAxis := by
  refine ⟨Submodule.disjoint_def.mpr ?_, codisjoint_iff.mpr (top_unique ?_)⟩
  · rintro ⟨a, b⟩ hb ha
    exact Prod.ext (LinearMap.mem_ker.mp ha) (LinearMap.mem_ker.mp hb)
  · rintro ⟨a, b⟩ _
    exact Submodule.mem_sup.mpr ⟨(a, 0), rfl, (0, b), rfl, by simp⟩

private def lineOperators (lam : ℂ) : Fin 4 → Module.End ℂ ℂ :=
  ![0, lam • LinearMap.id, 0, 0]

private def pairOperators (γ lam : ℂ) : Fin 4 → Module.End ℂ (ℂ × ℂ) :=
  ![γ • LinearMap.id,
    (lam • LinearMap.fst ℂ ℂ ℂ).prod ((lam - 1) • LinearMap.snd ℂ ℂ ℂ),
    (γ • LinearMap.snd ℂ ℂ ℂ).prod 0,
    (0 : (ℂ × ℂ) →ₗ[ℂ] ℂ).prod (LinearMap.fst ℂ ℂ ℂ)]

private theorem line_grade (lam : ℂ) (p : ZMod 2) :
    let G : Grading ℂ ℂ := gradingFromCompl p ⊤ ⊥ isCompl_top_bot
    ∀ (i : Fin 4) (j : ZMod 2) (m : ℂ), m ∈ G.piece j →
      lineOperators lam i m ∈ G.piece (degree i + j) := by
  dsimp only
  intro i j m hm
  fin_cases i <;> rcases parity_cases j with rfl | rfl <;>
    rcases parity_cases p with rfl | rfl <;>
    simp [lineOperators, gradingFromCompl, degree, Ne.symm zero_ne_one,
      show (1 : ZMod 2) + 1 = 0 by decide] at hm ⊢ <;> simp [hm]

private theorem pair_grade (γ lam : ℂ) (p : ZMod 2) :
    let G := gradingFromCompl p firstAxis secondAxis axes_compl
    ∀ (i : Fin 4) (j : ZMod 2) (m : ℂ × ℂ), m ∈ G.piece j →
      pairOperators γ lam i m ∈ G.piece (degree i + j) := by
  dsimp only
  intro i j m hm
  fin_cases i <;> rcases parity_cases j with rfl | rfl <;>
    rcases parity_cases p with rfl | rfl <;>
    simp [pairOperators, gradingFromCompl, firstAxis, secondAxis, degree,
      Ne.symm zero_ne_one, show (1 : ZMod 2) + 1 = 0 by decide] at hm ⊢ <;> simp [hm]

private theorem line_relations (lam : ℂ) (i j : Fin 4) :
    matrixAction (lineOperators lam) (bracketTable ℂ i j) =
      lineOperators lam i * lineOperators lam j -
        paritySign ℂ (degree i) (degree j) • (lineOperators lam j * lineOperators lam i) := by
  fin_cases i <;> fin_cases j <;>
    simp [lineOperators, bracketTable, degree,
      matrixAction_z, matrixAction_e, matrixAction_f]

private theorem pair_relations (γ lam : ℂ) (i j : Fin 4) :
    matrixAction (pairOperators γ lam) (bracketTable ℂ i j) =
      pairOperators γ lam i * pairOperators γ lam j -
        paritySign ℂ (degree i) (degree j) • (pairOperators γ lam j * pairOperators γ lam i) := by
  apply LinearMap.ext
  intro x
  apply Prod.ext <;> fin_cases i <;> fin_cases j <;>
    simp [pairOperators, bracketTable, degree,
      matrixAction_z, matrixAction_e, matrixAction_f, Module.End.mul_apply] <;> ring

theorem existence : existenceType := by
  intro L hm γ lam p
  by_cases hγ : γ = 0
  · subst γ
    let G : Grading ℂ ℂ := gradingFromCompl p ⊤ ⊥ isCompl_top_bot
    let A : GradedModule L G :=
      moduleOfGenerators hm (lineOperators lam) (line_grade lam p) (line_relations lam)
    have hA (i : Fin 4) : A.act (generator ℂ i) = lineOperators lam i :=
      matrixAction_generator _ _
    let P : Form A 0 lam p := by
      refine ⟨1, 0, one_ne_zero, ?_, Submodule.zero_mem _, ?_, fun _ => rfl,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [G, gradingFromCompl]
      · apply top_unique
        intro x _
        refine Submodule.mem_sup.mpr ⟨x, ?_, 0, Submodule.zero_mem _, add_zero _⟩
        exact Submodule.mem_span_singleton.mpr ⟨x, by simp⟩
      · change A.act (generator ℂ 1) 1 = _
        rw [hA]
        simp [lineOperators]
      · simp
      · change A.act (generator ℂ 3) 1 = _
        rw [hA]
        simp [lineOperators]
      · simp
      · change A.act (generator ℂ 2) 1 = _
        rw [hA]
        simp [lineOperators]
      · simp
      · change A.act (generator ℂ 0) 1 = _
        rw [hA]
        simp [lineOperators]
      · simp
    exact ⟨ℂ, inferInstance, inferInstance, inferInstance, G, A, forms_simple hm P, ⟨P⟩⟩
  · let G := gradingFromCompl p firstAxis secondAxis axes_compl
    let A : GradedModule L G :=
      moduleOfGenerators hm (pairOperators γ lam) (pair_grade γ lam p) (pair_relations γ lam)
    have hA (i : Fin 4) : A.act (generator ℂ i) = pairOperators γ lam i :=
      matrixAction_generator _ _
    let P : Form A γ lam p := by
      refine ⟨(1, 0), (0, 1), ?_, ?_, ?_, ?_, fun h => (hγ h).elim,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp
      · simp [G, gradingFromCompl, firstAxis]
      · simp [G, gradingFromCompl, secondAxis, opposite_ne p]
      · apply top_unique
        rintro ⟨a, b⟩ _
        exact Submodule.mem_sup.mpr ⟨(a, 0), Submodule.mem_span_singleton.mpr ⟨a, by simp⟩,
          (0, b), Submodule.mem_span_singleton.mpr ⟨b, by simp⟩, by simp⟩
      · change A.act (generator ℂ 1) (1, 0) = _
        rw [hA]
        simp [pairOperators]
      · change A.act (generator ℂ 1) (0, 1) = _
        rw [hA]
        simp [pairOperators]
      · change A.act (generator ℂ 3) (1, 0) = _
        rw [hA]
        simp [pairOperators]
      · change A.act (generator ℂ 3) (0, 1) = _
        rw [hA]
        simp [pairOperators]
      · change A.act (generator ℂ 2) (1, 0) = _
        rw [hA]
        simp [pairOperators]
      · change A.act (generator ℂ 2) (0, 1) = _
        rw [hA]
        simp [pairOperators]
      · change A.act (generator ℂ 0) (1, 0) = _
        rw [hA]
        simp [pairOperators]
      · change A.act (generator ℂ 0) (0, 1) = _
        rw [hA]
        simp [pairOperators]
    exact ⟨ℂ × ℂ, inferInstance, inferInstance, inferInstance, G, A, forms_simple hm P, ⟨P⟩⟩

end Construction

end LieNotes.SuperRestricted.SuperRankOneSimples
