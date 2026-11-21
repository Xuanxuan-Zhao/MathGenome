import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SerreRelations
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootStrings
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootTriples
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleIdealDecomposition
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Linarith

/-! The simple-root generators of a complex semisimple Lie algebra satisfy
the Serre relations. -/

universe u
noncomputable section
namespace LieAlgebrasAndRepresentations
namespace SerreProof
open Specs.LieAlgebrasAndRepresentations.SerreRelations

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
variable (H : LieSubalgebra ℂ L) (φ : Module.Dual ℂ H →ₗ[ℝ] ℝ)

private lemma neg_root_mem (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    {α : Module.Dual ℂ H} (ha : α ∈ rootSet H) : -α ∈ rootSet H := by
  obtain ⟨e, f, he, hf, hen, hfn, _⟩ := exists_root_triple hss H hH α ha
  exact ⟨neg_ne_zero.mpr ha.1, fun hb => hfn (by simpa [hb] using hf)⟩

private lemma positive_or_neg (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (hr : ∀ α ∈ rootSet H, φ α ≠ 0) {α : Module.Dual ℂ H}
    (ha : α ∈ rootSet H) : α ∈ positive H φ ∨ -α ∈ positive H φ := by
  rcases lt_or_gt_of_ne (hr α ha) with h | h
  · exact Or.inr ⟨neg_root_mem H hss hH ha, by simpa using neg_pos.mpr h⟩
  · exact Or.inl ⟨ha, h⟩

private lemma simple_sub_not_root (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (hr : ∀ α ∈ rootSet H, φ α ≠ 0)
    (i j : simple H φ) : i.val - j.val ∉ rootSet H := by
  intro hd
  rcases positive_or_neg H φ hss hH hr hd with hp | hp
  · exact i.property.2 (i.val-j.val) hp j.val j.property.1 (by abel)
  · exact j.property.2 (-(i.val-j.val)) hp i.val i.property.1 (by abel)

private lemma simple_ne_neg (i j : simple H φ) : j.val ≠ -i.val := by
  intro heq
  have hi := i.property.1.2
  have hj := j.property.1.2
  rw [heq, map_neg] at hj
  linarith

private lemma sub_ne_zero (i j : simple H φ) (hne : i ≠ j) : i.val - j.val ≠ 0 := by
  intro hz
  exact hne (Subtype.ext (sub_eq_zero.mp hz))

private lemma bracket_eq_zero_of_absent {α β : Module.Dual ℂ H}
    (hne : α + β ≠ 0) (hn : α + β ∉ rootSet H)
    {x y : L} (hx : x ∈ rootSpace H α) (hy : y ∈ rootSpace H β) : ⁅x,y⁆ = 0 := by
  have h := rootSpace_bracket H α β x y hx hy
  rw [rootSpace_eq_bot_of_not_mem H _ hne hn] at h
  exact h

private lemma rootSpace_le_of_nonzero (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    {α : Module.Dual ℂ H} (ha : α ∈ rootSet H) (S : LieSubalgebra ℂ L)
    {x : L} (hx : x ∈ rootSpace H α) (hxn : x ≠ 0) (hxs : x ∈ S) :
    rootSpace H α ≤ S.toSubmodule := by
  rw [eq_span_singleton_of_mem_of_finrank_eq_one
    (finrank_rootSpace_eq_one hss H hH α ha) hx hxn]
  exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hxs)

private lemma ad_pow_mem {α β : Module.Dual ℂ H} {x y : L}
    (hx : x ∈ rootSpace H α) (hy : y ∈ rootSpace H β) (n : ℕ) :
    ((LieAlgebra.ad ℂ L x)^n) y ∈ rootSpace H (β + n • α) := by
  induction n with
  | zero => simpa using hy
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    have hm := rootSpace_bracket H α (β + n • α) x _ hx ih
    convert hm using 1 <;> simp [add_smul] <;> abel
private lemma simple_string
    (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (hr : ∀ α ∈ rootSet H, φ α ≠ 0)
    (i j : simple H φ) (hne : i ≠ j) :
    ∃ q : ℕ, j.val (killingCoroot H i.val) = -(q : ℂ) ∧
      j.val + (q+1) • i.val ∉ rootSet H := by
  obtain ⟨p, q, hpq, hs⟩ := RootStrings.root_string hss H hH i.val j.val
    i.property.1.1 j.property.1.1
    (fun h => hne (Subtype.ext h.symm)) (simple_ne_neg H φ i j)
  have hp : p = 0 := by
    by_contra hn
    have ht : j.val - i.val ∈ rootSet H := by
      have := (hs (-1)).mpr (by constructor <;> omega)
      simpa [sub_eq_add_neg] using this
    exact simple_sub_not_root H φ hss hH hr j i ht
  subst p
  refine ⟨q, by simpa using hpq, ?_⟩
  intro hn
  have ht : j.val + ((q+1 : ℕ) : ℤ) • i.val ∈ rootSet H := by simpa only [natCast_zsmul] using hn
  have := (hs ((q+1 : ℕ) : ℤ)).mp ht
  omega

private lemma positive_shift_ne_zero (i j : simple H φ) (n : ℕ) :
    j.val + n • i.val ≠ 0 := by
  intro hz
  have ht : 0 < φ (j.val + n • i.val) := by
    rw [map_add, map_nsmul]
    exact add_pos_of_pos_of_nonneg j.property.1.2 (nsmul_nonneg i.property.1.2.le n)
  rw [hz, map_zero] at ht
  exact lt_irrefl _ ht

private lemma serre_powers
    (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (hr : ∀ α ∈ rootSet H, φ α ≠ 0)
    (i j : simple H φ) (hne : i ≠ j)
    (a : ℤ) (ha : j.val (killingCoroot H i.val) = (a : ℂ))
    {e f x y : L} (he : e ∈ rootSpace H i.val) (hf : f ∈ rootSpace H (-i.val))
    (hx : x ∈ rootSpace H j.val) (hy : y ∈ rootSpace H (-j.val)) :
    a ≤ 0 ∧ ((LieAlgebra.ad ℂ L e)^(1-a).toNat) x = 0 ∧
      ((LieAlgebra.ad ℂ L f)^(1-a).toNat) y = 0 := by
  obtain ⟨q, hq, hnot⟩ := simple_string H φ hss hH hr i j hne
  have heqa : a = -(q : ℤ) := by
    apply Int.cast_injective (α := ℂ)
    simpa using ha.symm.trans hq
  have hn : (1-a).toNat = q+1 := by omega
  have hz := positive_shift_ne_zero H φ i j (q+1)
  have hbot := rootSpace_eq_bot_of_not_mem H _ hz hnot
  have hnegnot : -(j.val + (q+1) • i.val) ∉ rootSet H := by
    intro h
    exact hnot (by simpa using neg_root_mem H hss hH h)
  have hnegbot := rootSpace_eq_bot_of_not_mem H _ (neg_ne_zero.mpr hz) hnegnot
  refine ⟨by omega, ?_, ?_⟩
  · have hm := ad_pow_mem H he hx (q+1)
    rw [hbot] at hm
    simpa [hn] using hm
  · have hm := ad_pow_mem H hf hy (q+1)
    have hw : -j.val + (q+1) • (-i.val) = -(j.val + (q+1) • i.val) := by
      simp [neg_add_rev]
      abel
    rw [hw, hnegbot] at hm
    simpa [hn] using hm
/-- Decomposition into positive roots terminates, since the root set is finite.
Both signs are treated together to avoid any choice of negative simple system. -/
private lemma positive_spaces_in_subalgebra
    (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (S : LieSubalgebra ℂ L)
    (hsimple : ∀ i : simple H φ,
      rootSpace H i.val ≤ S.toSubmodule ∧ rootSpace H (-i.val) ≤ S.toSubmodule) :
    ∀ β ∈ positive H φ,
      rootSpace H β ≤ S.toSubmodule ∧ rootSpace H (-β) ≤ S.toSubmodule := by
  intro β hβ
  by_contra hbad
  let B : Set (Module.Dual ℂ H) := {β | β ∈ positive H φ ∧
    ¬ (rootSpace H β ≤ S.toSubmodule ∧ rootSpace H (-β) ≤ S.toSubmodule)}
  have hf : B.Finite := (rootSet_finite H hH.1).subset (fun _ h => h.1.1)
  obtain ⟨b, hb⟩ := hf.exists_minimalFor φ B ⟨β, hβ, hbad⟩
  have hbpos := hb.prop.1
  have hbnot := hb.prop.2
  have hbs : b ∉ simple H φ := by
    intro h
    exact hbnot (hsimple ⟨b,h⟩)
  obtain ⟨γ,hγ,δ,hδ,hbadd⟩ :
      ∃ γ ∈ positive H φ, ∃ δ ∈ positive H φ, b = γ + δ := by
    by_contra hn
    apply hbs
    exact ⟨hbpos, by simpa using hn⟩
  have hsum : φ b = φ γ + φ δ := by rw [hbadd, map_add]
  have hsmall {a : Module.Dual ℂ H} (ha : a ∈ positive H φ) (hlt : φ a < φ b) :
      rootSpace H a ≤ S.toSubmodule ∧ rootSpace H (-a) ≤ S.toSubmodule := by
    by_contra hn
    exact (not_le.mpr hlt) (hb.le_of_le (show a ∈ B from ⟨ha,hn⟩) hlt.le)
  have hg := hsmall hγ (by linarith [hδ.2])
  have hd := hsmall hδ (by linarith [hγ.2])
  apply hbnot
  have hnb : -b ∈ rootSet H := neg_root_mem H hss hH hbpos.1
  have combine {a c t : Module.Dual ℂ H}
      (ha : a ∈ rootSet H) (hc : c ∈ rootSet H) (ht : t ∈ rootSet H)
      (heq : a + c = t)
      (hsa : rootSpace H a ≤ S.toSubmodule)
      (hsc : rootSpace H c ≤ S.toSubmodule) : rootSpace H t ≤ S.toSubmodule := by
    obtain ⟨x,hx,hxn⟩ := (rootSpace H a).ne_bot_iff.mp ha.2
    obtain ⟨y,hy,hyn⟩ := (rootSpace H c).ne_bot_iff.mp hc.2
    have hxy : ⁅x,y⁆ ≠ 0 :=
      RootStrings.root_bracket_ne_zero hss H hH a c ha hc (heq ▸ ht) x y hx hy hxn hyn
    have hm : ⁅x,y⁆ ∈ rootSpace H t := heq ▸ rootSpace_bracket H a c x y hx hy
    exact rootSpace_le_of_nonzero H hss hH ht S hm hxy (S.lie_mem (hsa hx) (hsc hy))
  constructor
  · exact combine hγ.1 hδ.1 hbpos.1 hbadd.symm hg.1 hd.1
  · exact combine (neg_root_mem H hss hH hγ.1) (neg_root_mem H hss hH hδ.1) hnb
      (by rw [hbadd]; abel) hg.2 hd.2

/-- The bracket span of a semisimple algebra is the whole algebra. Every
bracket of weight vectors belongs to a subalgebra containing the root spaces. -/
private lemma subalgebra_eq_top_of_root_spaces
    (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (S : LieSubalgebra ℂ L)
    (hs : ∀ α ∈ rootSet H, rootSpace H α ≤ S.toSubmodule) : S = ⊤ := by
  have hn {α : Module.Dual ℂ H} (ha : α ≠ 0) : rootSpace H α ≤ S.toSubmodule := by
    by_cases hα : α ∈ rootSet H
    · exact hs α hα
    · rw [rootSpace_eq_bot_of_not_mem H α ha hα]
      exact bot_le
  have hroot (α β : Module.Dual ℂ H) (x y : L)
      (hx : x ∈ rootSpace H α) (hy : y ∈ rootSpace H β) : ⁅x,y⁆ ∈ S := by
    by_cases ha : α = 0
    · by_cases hb : β = 0
      · subst α; subst β
        rw [rootSpace_zero hss H hH] at hx hy
        letI : IsLieAbelian H := hH.1.1
        have hz := congrArg Subtype.val (trivial_lie_zero H H (⟨x,hx⟩ : H) (⟨y,hy⟩ : H))
        change ⁅x,y⁆ = 0 at hz
        rw [hz]
        exact S.zero_mem
      · subst α
        exact hn hb (by simpa using rootSpace_bracket H 0 β x y hx hy)
    · by_cases hb : β = 0
      · subst β
        exact hn ha (by simpa using rootSpace_bracket H α 0 x y hx hy)
      · exact S.lie_mem (hn ha hx) (hn hb hy)
  have hspan := iSup_rootSpace_eq_top H hH.1
  have hall (x y : L) : ⁅x,y⁆ ∈ S := by
    have hx : x ∈ ⨆ α, rootSpace H α := by rw [hspan]; trivial
    have hy : y ∈ ⨆ β, rootSpace H β := by rw [hspan]; trivial
    refine Submodule.iSup_induction (rootSpace H) (motive := fun x => ⁅x,y⁆ ∈ S) hx ?_ ?_ ?_
    · intro α x hx
      refine Submodule.iSup_induction (rootSpace H) (motive := fun y => ⁅x,y⁆ ∈ S) hy ?_ ?_ ?_
      · intro β y hy
        exact hroot α β x y hx hy
      · simpa using S.zero_mem
      · intro y z hy hz
        simpa only [lie_add] using S.add_mem hy hz
    · simpa using S.zero_mem
    · intro x z hx hz
      simpa only [add_lie] using S.add_mem hx hz
  apply LieSubalgebra.toSubmodule_injective
  apply top_unique
  have hp := congrArg LieSubmodule.toSubmodule (semisimple_perfect ℂ L hss)
  rw [LieSubmodule.lieIdeal_oper_eq_linear_span] at hp
  change Submodule.span ℂ _ = (⊤ : Submodule ℂ L) at hp
  rw [← hp]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨x,y,rfl⟩
  exact hall x y

end SerreProof

open Specs.LieAlgebrasAndRepresentations.SerreRelations

/-- Every choice of normalized simple-root triples generates the algebra
and satisfies the Serre relations for its Cartan matrix. -/
theorem serre_relations :
    Specs.LieAlgebrasAndRepresentations.SerreRelations.serre_relations_type.{u} := by
  intro L _ _ _ hss H hH φ hr e f hv
  classical
  have integral (i j : simple H φ) :=
    RootStrings.coroot_pairing_integral hss H hH i.val j.val i.property.1.1 j.property.1.1
  let A (i j : simple H φ) : ℤ := Classical.choose (integral i j)
  have hA (i j : simple H φ) :
      j.val (killingCoroot H i.val) = (A i j : ℂ) :=
    (Classical.choose_spec (integral i j)).1
  refine ⟨A, hA, ?_, ?_, ?_⟩
  · intro i j
    refine ⟨?_, ?_, ?_, ?_⟩
    · letI : IsLieAbelian H := hH.1.1
      exact congrArg Subtype.val (trivial_lie_zero H H (killingCoroot H i.val) (killingCoroot H j.val))
    · rw [← hA]
      exact (mem_rootSpace H j.val (e j)).mp (hv j).1 (killingCoroot H i.val)
    · rw [← hA]
      simpa using (mem_rootSpace H (-j.val) (f j)).mp (hv j).2.1 (killingCoroot H i.val)
    · by_cases hij : i = j
      · subst j
        simpa using (hv i).2.2.2.2
      · rw [ite_eq_right hij]
        apply SerreProof.bracket_eq_zero_of_absent H
        · simpa [sub_eq_add_neg] using SerreProof.sub_ne_zero H φ i j hij
        · simpa [sub_eq_add_neg] using SerreProof.simple_sub_not_root H φ hss hH hr i j
        · exact (hv i).1
        · exact (hv j).2.1
  · intro i j hij
    exact SerreProof.serre_powers H φ hss hH hr i j hij (A i j) (hA i j)
      (hv i).1 (hv i).2.1 (hv j).1 (hv j).2.1
  · let S := LieSubalgebra.lieSpan ℂ L
      (Set.range e ∪ Set.range f ∪ Set.range
        (fun i : simple H φ => (killingCoroot H i.val : L)))
    have he (i) : e i ∈ S :=
      LieSubalgebra.subset_lieSpan (Or.inl (Or.inl (Set.mem_range_self i)))
    have hf (i) : f i ∈ S :=
      LieSubalgebra.subset_lieSpan (Or.inl (Or.inr (Set.mem_range_self i)))
    have hpos := SerreProof.positive_spaces_in_subalgebra H φ hss hH S
      (fun i => ⟨SerreProof.rootSpace_le_of_nonzero H hss hH i.property.1.1 S
          (hv i).1 (hv i).2.2.1 (he i),
        SerreProof.rootSpace_le_of_nonzero H hss hH
          (SerreProof.neg_root_mem H hss hH i.property.1.1) S
          (hv i).2.1 (hv i).2.2.2.1 (hf i)⟩)
    apply SerreProof.subalgebra_eq_top_of_root_spaces H hss hH S
    intro α hα
    rcases SerreProof.positive_or_neg H φ hss hH hr hα with hp | hp
    · exact (hpos α hp).1
    · simpa using (hpos (-α) hp).2

end LieAlgebrasAndRepresentations
