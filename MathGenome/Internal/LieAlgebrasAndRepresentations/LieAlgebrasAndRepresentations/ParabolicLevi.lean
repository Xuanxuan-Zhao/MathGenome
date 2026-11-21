import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ParabolicLevi
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.StandardParabolics
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.Nilradical
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleIdealDecomposition
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

noncomputable section

universe u

namespace LieAlgebrasAndRepresentations.ParabolicLevi

open Module Set
open Specs.LieAlgebrasAndRepresentations.ParabolicLevi
open Specs.LieAlgebrasAndRepresentations.StandardParabolics
open Specs.LieAlgebrasAndRepresentations.RealRootSpace
open Specs.LieAlgebrasAndRepresentations.CompactConjugation (PositiveRoot)
open scoped Classical

local notation "borelSpace" => Specs.LieAlgebrasAndRepresentations.CompactFlagOrbit.borel
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  {H : LieSubalgebra ℂ L}

set_option hygiene false in
local notation "D" => Module.Dual ℂ H

private def weightSpan (A : Set D) : Submodule ℂ L :=
  ⨆ a ∈ A, rootSpace H a

private theorem root_le_weightSpan {A : Set D} {a : D} (ha : a ∈ A) :
    rootSpace H a ≤ weightSpan A :=
  le_iSup_of_le a (le_iSup (fun _ : a ∈ A => rootSpace H a) ha)

private theorem weightSpan_mono_supported {A B : Set D}
    (h : ∀ a ∈ A, (a = 0 ∨ a ∈ rootSet H) → a ∈ B) :
    weightSpan A ≤ weightSpan B := by
  refine iSup₂_le fun a ha => ?_
  by_cases hs : a = 0 ∨ a ∈ rootSet H
  · exact root_le_weightSpan (h a ha hs)
  · rw [rootSpace_eq_bot_of_not_mem H a (fun hz => hs (.inl hz)) (fun hr => hs (.inr hr))]
    exact bot_le

private theorem weightSpan_union (A B : Set D) :
    weightSpan (A ∪ B) = weightSpan A ⊔ weightSpan B := by
  apply le_antisymm
  · refine iSup₂_le fun a ha => ?_
    exact ha.elim (fun h => (root_le_weightSpan h).trans le_sup_left)
      (fun h => (root_le_weightSpan h).trans le_sup_right)
  · exact sup_le (weightSpan_mono_supported fun _ h _ => Or.inl h)
      (weightSpan_mono_supported fun _ h _ => Or.inr h)

private theorem weightSpan_bracket {A B C : Set D}
    (h : ∀ a ∈ A, ∀ b ∈ B, a + b ∈ C) {x y : L}
    (hx : x ∈ weightSpan A) (hy : y ∈ weightSpan B) :
    ⁅x, y⁆ ∈ weightSpan C := by
  let f : L →ₗ[ℂ] L →ₗ[ℂ] L := (LieAlgebra.ad ℂ L).toLinearMap
  apply (show Submodule.map₂ f (weightSpan A) (weightSpan B) ≤ weightSpan C from ?_)
    (Submodule.apply_mem_map₂ f hx hy)
  unfold weightSpan
  simp only [Submodule.map₂_iSup_left, Submodule.map₂_iSup_right]
  exact iSup₂_le fun b hb => iSup₂_le fun a ha => Submodule.map₂_le.mpr fun x hx y hy =>
    root_le_weightSpan (h a ha b hb) (rootSpace_bracket H a b x y hx hy)

private theorem weightSpan_disjoint (hH : IsMaximalToral H) {A B : Set D}
    (h : Disjoint A B) : Disjoint (weightSpan A) (weightSpan B) :=
  (rootSpace_independent H hH.1).disjoint_biSup_biSup h

open private rootSpace_eq_gen from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootDecomposition

private theorem weightSpan_of_stable (hH : IsMaximalToral H) (X : Submodule ℂ L)
    (hx : ∀ (h : H) (x : L), x ∈ X → ⁅(h : L), x⁆ ∈ X) :
    X = ⨆ a : D, X ⊓ rootSpace H a := by
  letI : IsLieAbelian H := hH.1.1
  let N : LieSubmodule ℂ H L := { X with lie_mem := fun {h x} hmem => hx h x hmem }
  have hN := congrArg LieSubmodule.toSubmodule (LieModule.eq_iSup_inf_genWeightSpace ℂ H L N)
  simp only [LieSubmodule.iSup_toSubmodule, LieSubmodule.inf_toSubmodule] at hN
  change X = _ at hN
  apply le_antisymm ?_ (iSup_le fun _ => inf_le_left)
  conv_lhs => rw [hN]
  refine iSup_le fun χ => ?_
  let a : D := χ
  have he := rootSpace_eq_gen H hH.1 a
  simp only [a, LieModule.Weight.coe_coe] at he
  rw [← he]
  exact le_iSup (fun a : D => X ⊓ rootSpace H a) a

open private rootSpace_le_of_nonzero_mem from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.StandardParabolics
open private standard standard_solvable from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.BorelSubalgebras

private abbrev idealSpace {P : LieSubalgebra ℂ L} (I : LieIdeal ℂ P) : Submodule ℂ L :=
  I.toSubmodule.map P.incl.toLinearMap

/-- The Cartan and the subsystem root spaces form an internal direct sum. -/
theorem levi_rootSpaces_independent (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (d : Realization H) (v : E H) (S : Set (Simple d v)) :
    iSupIndep (fun i : Option (SubsystemRoot d v S) => match i with
      | none => H.toSubmodule
      | some a => rootSpace H a.val.val) := by
  let : DecidableEq (Option (rootSet H)) := Classical.decEq _
  let index : Option (SubsystemRoot d v S) → Option (rootSet H) := Option.map Subtype.val
  have hIndex : Function.Injective index := Option.map_injective Subtype.val_injective
  convert (root_decomposition hss H hH).submodule_iSupIndep.comp hIndex using 1
  funext i
  cases i <;> rfl

/-- The root spaces in the formula for either signed nilradical form an
internal direct sum. -/
theorem nilSpace_rootSpaces_independent (hH : IsMaximalToral H)
    (d : Realization H) (v : E H) (S : Set (Simple d v)) (f : D →ₗ[ℝ] ℝ) :
    iSupIndep (fun a : {a : PositiveRoot H f //
      rootRestriction H a.val ∉ subsystemSpan d v S} => rootSpace H a.val.val) :=
  (rootSpace_independent H hH.1).comp fun _ _ h => Subtype.ext (Subtype.ext h)

private theorem idealSpace_le {P : LieSubalgebra ℂ L} (I : LieIdeal ℂ P) :
    idealSpace I ≤ P.toSubmodule := by
  rintro _ ⟨x, _, rfl⟩
  exact x.property

private theorem idealSpace_lie {P : LieSubalgebra ℂ L} (I : LieIdeal ℂ P)
    {x y : L} (hx : x ∈ P.toSubmodule) (hy : y ∈ idealSpace I) : ⁅x, y⁆ ∈ idealSpace I := by
  obtain ⟨z, hz, rfl⟩ := hy
  exact ⟨⁅(⟨x, hx⟩ : P), z⁆, I.lie_mem hz, rfl⟩

private theorem idealSpace_weightSplit (hH : IsMaximalToral H)
    {P : LieSubalgebra ℂ L} (hHP : H.toSubmodule ≤ P.toSubmodule) (I : LieIdeal ℂ P) :
    idealSpace I = ⨆ a : D, idealSpace I ⊓ rootSpace H a :=
  weightSpan_of_stable hH _ fun h _ hx => idealSpace_lie I (hHP h.property) hx

private theorem eigen_eq_zero_of_nilpotent {V : Type u} [AddCommGroup V] [Module ℂ V]
    {T : End ℂ V} (hT : IsNilpotent T) {a : ℂ} {x : V} (hx : x ≠ 0)
    (h : T x = a • x) : a = 0 := by
  have he : T.HasEigenvalue a := (Module.End.hasEigenvalue_iff).2
    ((Submodule.ne_bot_iff _).2 ⟨x, Module.End.mem_eigenspace_iff.mpr h, hx⟩)
  exact (he.isNilpotent_of_isNilpotent hT).eq_zero

private theorem no_root_in_solvable (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    {P : LieSubalgebra ℂ L} (I : LieIdeal ℂ P) [LieAlgebra.IsSolvable I]
    {a : D} (ha : a ∈ rootSet H) (hop : rootSpace H (-a) ≤ P.toSubmodule)
    {x : L} (hx : x ∈ rootSpace H a) (hxI : x ∈ idealSpace I) : x = 0 := by
  by_contra hn
  obtain ⟨e, f, he, hf, he₀, _, hef, hhe, _⟩ := exists_root_triple hss H hH a ha
  have heI := rootSpace_le_of_nonzero_mem hss hH ha hx hn hxI he
  obtain ⟨e', he', hval⟩ := heI
  change (e' : L) = e at hval
  let f' : P := ⟨f, hop hf⟩
  have hnil := isNilpotent_toEnd_lie_of_solvable_ideal (V := P) I ⟨e', he'⟩ f'
  have heq : (LieModule.toEnd ℂ P P ⁅f', e'⁆) e' = (-2 : ℂ) • e' := by
    apply Subtype.ext
    change ⁅⁅f, (e' : L)⁆, (e' : L)⁆ = (-2 : ℂ) • (e' : L)
    rw [hval, ← lie_skew f e, hef, neg_lie, hhe, neg_smul]
  have hz := eigen_eq_zero_of_nilpotent hnil
    (fun h => he₀ (hval.symm.trans (congrArg Subtype.val h))) heq
  norm_num at hz

private theorem no_cartan_in_nilradical (d : Realization H)
    {P : LieSubalgebra ℂ L} (f : D →ₗ[ℝ] ℝ)
    (hregular : ∀ a ∈ rootSet H, f a ≠ 0)
    (hneg : ∀ a ∈ rootSet H, -a ∈ rootSet H)
    (hB : borelSpace H f ≤ P.toSubmodule) {x : L} (hx : x ∈ H)
    (hxn : x ∈ idealSpace (nilradical ℂ P)) : x = 0 := by
  obtain ⟨x', hxn', rfl⟩ := hxn
  have hnil := (mem_nilradical_iff ℂ P x').mp hxn' |>.2
  let h : H := ⟨x', hx⟩
  have hpositive (a : D) (ha : a ∈ rootSet H) (hp : 0 < f a) : a h = 0 := by
    obtain ⟨y, hy, hy₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ha.2
    let y' : P := ⟨y, hB ((le_iSup (fun b : PositiveRoot H f => rootSpace H b.val)
      ⟨a, ha, hp⟩).trans le_sup_right hy)⟩
    apply eigen_eq_zero_of_nilpotent hnil (x := y') (fun e => hy₀ (congrArg Subtype.val e))
    apply Subtype.ext
    exact (mem_rootSpace H a y).mp hy h
  have hvanish (a : D) (ha : a ∈ rootSet H) : a h = 0 := by
    rcases lt_or_gt_of_ne (hregular a ha) with hn | hp
    · have h' := hpositive (-a) (hneg a ha) (by simpa only [map_neg, neg_pos] using hn)
      simpa only [LinearMap.neg_apply, neg_eq_zero] using h'
    · exact hpositive a ha hp
  have hm : Submodule.span ℂ (rootSet H) ≤ LinearMap.ker (Module.Dual.eval ℂ H h) :=
    Submodule.span_le.mpr hvanish
  rw [d.roots_span] at hm
  have hz : h = 0 := (Module.forall_dual_apply_eq_zero_iff ℂ h).mp fun a =>
    hm (Submodule.mem_top (x := a))
  exact congrArg Subtype.val hz

private theorem nilradical_weightSpan (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (d : Realization H) (f g : D →ₗ[ℝ] ℝ)
    (hregular : ∀ a ∈ rootSet H, f a ≠ 0)
    (hneg : ∀ a ∈ rootSet H, -a ∈ rootSet H)
    {P : LieSubalgebra ℂ L} (hP : P.toSubmodule = weightSpan {a : D | 0 ≤ g a})
    (hB : borelSpace H f ≤ P.toSubmodule)
    (hg : ∀ a ∈ rootSet H, 0 < g a → 0 < f a) :
    idealSpace (nilradical ℂ P) = weightSpan {a : D | 0 < g a} := by
  have hHP : H.toSubmodule ≤ P.toSubmodule := le_sup_left.trans hB
  apply le_antisymm
  · let I := nilradical ℂ P
    letI : LieRing.IsNilpotent I := nilradical_nilpotent ℂ P
    letI : LieAlgebra.IsSolvable I := inferInstance
    rw [idealSpace_weightSplit hH hHP I]
    refine iSup_le fun a x hx => ?_
    by_cases hz : a = 0
    · have hxH : x ∈ H := by
        change x ∈ H.toSubmodule
        simpa only [hz, rootSpace_zero hss H hH] using (show x ∈ rootSpace H a from hx.2)
      rw [no_cartan_in_nilradical d f hregular hneg hB hxH hx.1]
      exact Submodule.zero_mem _
    by_cases hpos : 0 < g a
    · exact root_le_weightSpan hpos hx.2
    by_cases hr : a ∈ rootSet H
    · by_cases hg₀ : g a = 0
      · have hop : rootSpace H (-a) ≤ P.toSubmodule := by
          rw [hP]
          exact root_le_weightSpan (show 0 ≤ g (-a) by simp [hg₀])
        rw [no_root_in_solvable hss hH I hr hop hx.2 hx.1]
        exact Submodule.zero_mem _
      · have hgn : g a < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hg₀
        have hdis : Disjoint (weightSpan {a : D | 0 ≤ g a}) (rootSpace H a) :=
          ((rootSpace_independent H hH.1).disjoint_biSup (show a ∉ {a : D | 0 ≤ g a} from
            not_le_of_gt hgn)).symm
        have hxP : x ∈ weightSpan {a : D | 0 ≤ g a} := hP ▸ idealSpace_le I hx.1
        rw [Submodule.disjoint_def.mp hdis x hxP hx.2]
        exact Submodule.zero_mem _
    · have hzero : x = 0 := by
        have hm : x ∈ rootSpace H a := hx.2
        rwa [rootSpace_eq_bot_of_not_mem H a hz hr, Submodule.mem_bot] at hm
      rw [hzero]
      exact Submodule.zero_mem _
  let U : LieIdeal ℂ P :=
    { (weightSpan {a : D | 0 < g a}).comap P.incl.toLinearMap with
      lie_mem := fun {x y} hy => by
        apply weightSpan_bracket (A := {a : D | 0 ≤ g a}) (B := {a : D | 0 < g a}) _
          (hP ▸ x.property) hy
        intro a ha b hb
        change 0 < g (a + b)
        exact (map_add g a b).symm ▸ add_pos_of_nonneg_of_pos ha hb }
  have hU : idealSpace U = weightSpan {a : D | 0 < g a} := by
    change Submodule.map P.incl.toLinearMap (Submodule.comap P.incl.toLinearMap _) = _
    rw [Submodule.map_comap_eq]
    rw [show P.incl.toLinearMap.range = P.toSubmodule from Submodule.range_subtype _,
      inf_eq_right, hP]
    exact weightSpan_mono_supported fun a (h : 0 < g a) _ => (show 0 ≤ g a from le_of_lt h)
  let B := standard hss H hH f
  letI : LieAlgebra.IsSolvable B := standard_solvable hss H hH f
  let J := nilradical ℂ B
  letI : LieRing.IsNilpotent J := nilradical_nilpotent ℂ B
  have hxJ : weightSpan {a : D | 0 < g a} ≤ idealSpace J := by
    refine iSup₂_le fun a ha x hx => ?_
    by_cases hr : a ∈ rootSet H
    · have hpos := hg a hr ha
      obtain ⟨h, hh⟩ : ∃ h : H, a h ≠ 0 := by
        by_contra! hh
        exact hr.1 (LinearMap.ext hh)
      let h' : B := ⟨h, (le_sup_left : H.toSubmodule ≤ borelSpace H f) h.property⟩
      let x' : B := ⟨x, (le_iSup (fun c : PositiveRoot H f => rootSpace H c.val)
        ⟨a, hr, hpos⟩).trans le_sup_right hx⟩
      have hLie : ⁅h', x'⁆ = a h • x' := Subtype.ext ((mem_rootSpace H a x).mp hx h)
      have hJ : ⁅h', x'⁆ ∈ J := by
        apply bracket_radical_le_nilradical ℂ B
        apply LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _)
        rw [LieAlgebrasAndRepresentations.radical, LieAlgebra.radical_eq_top_of_isSolvable]
        exact LieSubmodule.mem_top _
      rw [hLie] at hJ
      exact ⟨x', (J.toSubmodule.smul_mem_iff hh).mp hJ, rfl⟩
    · have hn : a ≠ 0 := by
        intro e
        subst a
        simp at ha
      rw [rootSpace_eq_bot_of_not_mem H a hn hr, Submodule.mem_bot] at hx
      simp [hx]
  have hxJ' (x : U) : ∃ y : J, (y.val : L) = (x.val : L) := by
    obtain ⟨y, hy, he⟩ := hxJ (hU ▸ (show (x.val : L) ∈ idealSpace U from
      ⟨x.val, x.property, rfl⟩))
    exact ⟨⟨y, hy⟩, he⟩
  let emb : U →ₗ⁅ℂ⁆ J :=
    { toFun := fun x => (hxJ' x).choose
      map_add' := fun x y => by
        apply Subtype.ext
        apply Subtype.ext
        exact ((hxJ' (x + y)).choose_spec).trans
          (congrArg₂ (· + ·) (hxJ' x).choose_spec (hxJ' y).choose_spec).symm
      map_smul' := fun c x => by
        apply Subtype.ext
        apply Subtype.ext
        exact ((hxJ' (c • x)).choose_spec).trans
          (congrArg (c • ·) (hxJ' x).choose_spec).symm
      map_lie' := fun {x y} => by
        apply Subtype.ext
        apply Subtype.ext
        exact ((hxJ' ⁅x, y⁆).choose_spec).trans
          (congrArg₂ (fun a b : L => ⁅a, b⁆) (hxJ' x).choose_spec (hxJ' y).choose_spec).symm }
  have hinj : Function.Injective emb := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact (hxJ' x).choose_spec.symm.trans
      ((congrArg (fun z : J => (z.val : L)) he).trans (hxJ' y).choose_spec)
  have hUn : LieRing.IsNilpotent U := hinj.lieAlgebra_isNilpotent
  rw [← hU]
  exact Submodule.map_mono (nilpotent_ideal_le_nilradical U hUn)

section Geometry

variable [Fact (Realization H)]
set_option hygiene false in
local notation "d" => (Fact.out : Realization H)
local instance : NormedAddCommGroup (E H) := (d).normedAddCommGroup
local instance : InnerProductSpace ℝ (E H) := (d).innerProductSpace

variable {v : E H}
set_option hygiene false in
local notation "ρ" => restrictRoot H
set_option hygiene false in
local notation "φ" => positiveFunctional d v
set_option hygiene false in
local notation "Π" => Simple d v

open private restrict_mem functional_regular neg_root coord_nonneg mem_subsystem_iff
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.StandardParabolics

variable (b : Basis Π ℝ (E H)) (S : Set Π)

local instance : Fintype Π := (simpleRoots_finite (d).root_system.toRootAxioms v).fintype

private def grading : D →ₗ[ℝ] ℝ := by
  classical
  exact ∑ i ∈ Finset.univ.filter (fun i => i ∉ S), (b.coord i).comp ρ

private theorem grading_apply (a : D) :
    grading b S a = ∑ i ∈ Finset.univ.filter (fun i => i ∉ S), b.repr (ρ a) i := by
  classical
  simp only [grading, LinearMap.sum_apply, LinearMap.comp_apply, Basis.coord_apply]

variable (hb : ∀ i, b i = (i : E H))

include hb in
private theorem grading_nonneg {a : D} (ha : a ∈ rootSet H) (hp : 0 < φ a) :
    0 ≤ grading b S a := by
  classical
  rw [grading_apply]
  exact Finset.sum_nonneg fun i _ => coord_nonneg b hb ⟨restrict_mem ha, hp⟩ i

include hb in
private theorem grading_zero_iff (hv : RootRegular (realRoots H) v) {a : D}
    (ha : a = 0 ∨ a ∈ rootSet H) : grading b S a = 0 ↔ ρ a ∈ subsystemSpan d v S := by
  classical
  rcases ha with rfl | ha
  · simp
  have pos (c : D) (hc : c ∈ rootSet H) (hp : 0 < φ c) :
      grading b S c = 0 ↔ ρ c ∈ subsystemSpan d v S := by
    rw [grading_apply, Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => coord_nonneg b hb ⟨restrict_mem hc, hp⟩ i), mem_subsystem_iff b hb S]
    simp
  rcases lt_or_gt_of_ne (functional_regular hv a ha) with hn | hp
  · have h := pos (-a) (neg_root ha) (by simpa only [map_neg, neg_pos] using hn)
    simpa only [map_neg, neg_eq_zero, Submodule.neg_mem_iff] using h
  · exact pos a ha hp

include hb in
private theorem grading_pos_iff (hv : RootRegular (realRoots H) v) {a : D}
    (ha : a = 0 ∨ a ∈ rootSet H) :
    0 < grading b S a ↔ a ∈ rootSet H ∧ 0 < φ a ∧ ρ a ∉ subsystemSpan d v S := by
  rcases ha with rfl | ha
  · simp
  rw [← grading_zero_iff b S hb hv (Or.inr ha)]
  rcases lt_or_gt_of_ne (functional_regular hv a ha) with hn | hp
  · have hh := grading_nonneg b S hb (neg_root ha) (by simpa only [map_neg, neg_pos] using hn)
    rw [map_neg, neg_nonneg] at hh
    simp [not_lt_of_ge hh, not_lt_of_ge hn.le]
  · exact ⟨fun h => ⟨ha, hp, ne_of_gt h⟩,
      fun h => lt_of_le_of_ne (grading_nonneg b S hb ha hp) (Ne.symm h.2.2)⟩

include hb in
private theorem grading_neg_iff (hv : RootRegular (realRoots H) v) {a : D}
    (ha : a = 0 ∨ a ∈ rootSet H) :
    0 < (-grading b S) a ↔
      a ∈ rootSet H ∧ 0 < (-φ) a ∧ ρ a ∉ subsystemSpan d v S := by
  have hn : -a = 0 ∨ -a ∈ rootSet H :=
    ha.imp (fun hz => by simp [hz]) (fun hr => neg_root hr)
  have hr : -a ∈ rootSet H ↔ a ∈ rootSet H :=
    ⟨fun h => by simpa only [neg_neg] using neg_root h, fun h => neg_root h⟩
  simpa only [LinearMap.neg_apply, map_neg, hr, Submodule.neg_mem_iff] using
    grading_pos_iff b S hb hv hn

private theorem leviSpace_eq (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H) :
    leviSpace d v S = weightSpan {a : D | ρ a ∈ subsystemSpan d v S} := by
  unfold leviSpace
  apply le_antisymm
  · refine sup_le ?_ (iSup_le fun a => root_le_weightSpan a.property)
    rw [← rootSpace_zero hss H hH]
    exact root_le_weightSpan (show ρ (0 : D) ∈ subsystemSpan d v S by simp)
  · refine iSup₂_le fun a ha => ?_
    by_cases hz : a = 0
    · rw [hz, rootSpace_zero hss H hH]
      exact le_sup_left
    by_cases hr : a ∈ rootSet H
    · exact (le_iSup (fun c : SubsystemRoot d v S => rootSpace H c.val.val)
        ⟨⟨a, hr⟩, ha⟩).trans le_sup_right
    · rw [rootSpace_eq_bot_of_not_mem H a hz hr]
      exact bot_le

include hb in
private theorem leviSpace_eq_zero (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (hv : RootRegular (realRoots H) v) :
    leviSpace d v S = weightSpan {a : D | grading b S a = 0} := by
  rw [leviSpace_eq S hss hH]
  exact le_antisymm
    (weightSpan_mono_supported fun _ ha hs => (grading_zero_iff b S hb hv hs).mpr ha)
    (weightSpan_mono_supported fun _ ha hs => (grading_zero_iff b S hb hv hs).mp ha)

private theorem nilSpace_eq (f g : D →ₗ[ℝ] ℝ)
    (hg : ∀ a : D, (a = 0 ∨ a ∈ rootSet H) →
      (0 < g a ↔ a ∈ rootSet H ∧ 0 < f a ∧ ρ a ∉ subsystemSpan d v S)) :
    nilSpace d v S f = weightSpan {a : D | 0 < g a} := by
  apply le_antisymm
  · exact iSup_le fun a => root_le_weightSpan
      ((hg a.val.val (.inr a.val.property.1)).mpr ⟨a.val.property.1, a.val.property.2, a.property⟩)
  · refine iSup₂_le fun a ha => ?_
    by_cases hs : a = 0 ∨ a ∈ rootSet H
    · obtain ⟨hr, hp, hw⟩ := (hg a hs).mp ha
      exact le_iSup (fun c : {c : PositiveRoot H f // ρ c.val ∉ subsystemSpan d v S} =>
        rootSpace H c.val.val) ⟨⟨a, hr, hp⟩, hw⟩
    · rw [rootSpace_eq_bot_of_not_mem H a (fun hz => hs (.inl hz)) (fun hr => hs (.inr hr))]
      exact bot_le

private theorem parabolicSpace_sup (hv : RootRegular (realRoots H) v) :
    parabolicSpace d v S = leviSpace d v S ⊔ nilSpace d v S φ := by
  unfold parabolicSpace negativeSpace Specs.LieAlgebrasAndRepresentations.CompactFlagOrbit.borel leviSpace nilSpace
  apply le_antisymm
  · refine sup_le (sup_le (le_sup_left.trans le_sup_left) (iSup_le fun a => ?_))
      (iSup_le fun a => ?_)
    · by_cases h : ρ a.val ∈ subsystemSpan d v S
      · exact (le_iSup (fun c : SubsystemRoot d v S => rootSpace H c.val.val)
          ⟨⟨a.val, a.property.1⟩, h⟩).trans (le_sup_right.trans le_sup_left)
      · exact (le_iSup (fun c : {c : PositiveRoot H φ // ρ c.val ∉ subsystemSpan d v S} =>
          rootSpace H c.val.val) ⟨a, h⟩).trans le_sup_right
    · have h : ρ (-a.val.val) ∈ subsystemSpan d v S := by
        simpa only [map_neg, Submodule.neg_mem_iff] using (show ρ _ ∈ subsystemSpan d v S from a.property)
      exact (le_iSup (fun c : SubsystemRoot d v S => rootSpace H c.val.val)
        ⟨⟨-a.val.val, neg_root a.val.property.1⟩, h⟩).trans (le_sup_right.trans le_sup_left)
  · refine sup_le (sup_le (le_sup_left.trans le_sup_left) (iSup_le fun a => ?_))
      (iSup_le fun a => ?_)
    · rcases lt_or_gt_of_ne (functional_regular hv a.val.val a.val.property) with hn | hp
      · have hp' : 0 < φ (-a.val.val) := by simpa only [map_neg, neg_pos] using hn
        have h : ρ (-a.val.val) ∈ subsystemSpan d v S := by
          simpa only [map_neg, Submodule.neg_mem_iff] using (show ρ _ ∈ subsystemSpan d v S from a.property)
        have hh := le_iSup (fun c : SubsystemPositiveRoot d v S => rootSpace H (-c.val.val))
          ⟨⟨-a.val.val, neg_root a.val.property, hp'⟩, h⟩
        simpa only [neg_neg] using hh.trans
          (le_sup_right : (⨆ c : SubsystemPositiveRoot d v S, rootSpace H (-c.val.val)) ≤ _)
      · exact (le_iSup (fun c : PositiveRoot H φ => rootSpace H c.val)
          ⟨a.val.val, a.val.property, hp⟩).trans (le_sup_right.trans le_sup_left)
    · exact (le_iSup (fun c : PositiveRoot H φ => rootSpace H c.val) a.val).trans
        (le_sup_right.trans le_sup_left)

private theorem oppositeSpace_sup (hv : RootRegular (realRoots H) v) :
    oppositeSpace d v S = leviSpace d v S ⊔ nilSpace d v S (-φ) := by
  unfold oppositeSpace Specs.LieAlgebrasAndRepresentations.CompactFlagOrbit.borel leviSpace nilSpace
  apply le_antisymm
  · refine sup_le (sup_le (le_sup_left.trans le_sup_left) (iSup_le fun a => ?_))
      (iSup_le fun a => ?_)
    · by_cases h : ρ a.val ∈ subsystemSpan d v S
      · exact (le_iSup (fun c : SubsystemRoot d v S => rootSpace H c.val.val)
          ⟨⟨a.val, a.property.1⟩, h⟩).trans (le_sup_right.trans le_sup_left)
      · exact (le_iSup (fun c : {c : PositiveRoot H (-φ) // ρ c.val ∉ subsystemSpan d v S} =>
          rootSpace H c.val.val) ⟨a, h⟩).trans le_sup_right
    · exact (le_iSup (fun c : SubsystemRoot d v S => rootSpace H c.val.val)
        ⟨⟨a.val.val, a.val.property.1⟩, a.property⟩).trans (le_sup_right.trans le_sup_left)
  · refine sup_le (sup_le (le_sup_left.trans le_sup_left) (iSup_le fun a => ?_))
      (iSup_le fun a => ?_)
    · rcases lt_or_gt_of_ne (functional_regular hv a.val.val a.val.property) with hn | hp
      · exact (le_iSup (fun c : PositiveRoot H (-φ) => rootSpace H c.val)
          ⟨a.val.val, a.val.property, by simpa only [LinearMap.neg_apply, neg_pos] using hn⟩).trans
          (le_sup_right.trans le_sup_left)
      · exact (le_iSup (fun c : SubsystemPositiveRoot d v S => rootSpace H c.val.val)
          ⟨⟨a.val.val, a.val.property, hp⟩, a.property⟩).trans le_sup_right
    · exact (le_iSup (fun c : PositiveRoot H (-φ) => rootSpace H c.val) a.val).trans
        (le_sup_right.trans le_sup_left)

private theorem weightSpan_nonneg (g : D →ₗ[ℝ] ℝ) :
    weightSpan {a : D | 0 ≤ g a} =
      weightSpan {a : D | g a = 0} ⊔ weightSpan {a : D | 0 < g a} := by
  rw [← weightSpan_union]
  congr 1
  ext a
  change 0 ≤ g a ↔ g a = 0 ∨ 0 < g a
  exact le_iff_eq_or_lt.trans (or_congr eq_comm Iff.rfl)

private theorem weightSpan_opposite_inf (hH : IsMaximalToral H) (g : D →ₗ[ℝ] ℝ) :
    weightSpan {a : D | 0 ≤ g a} ⊓ weightSpan {a : D | 0 ≤ (-g) a} =
      weightSpan {a : D | g a = 0} := by
  let A := weightSpan {a : D | g a = 0}
  let B := weightSpan {a : D | 0 < g a}
  let C := weightSpan {a : D | 0 < (-g) a}
  rw [weightSpan_nonneg, weightSpan_nonneg]
  have he : {a : D | (-g) a = 0} = {a : D | g a = 0} := by
    ext a
    exact neg_eq_zero
  rw [he]
  change (A ⊔ B) ⊓ (A ⊔ C) = A
  have hd : Disjoint (A ⊔ B) C := by
    change Disjoint (weightSpan _ ⊔ weightSpan _) (weightSpan _)
    rw [← weightSpan_nonneg]
    apply weightSpan_disjoint hH
    rw [Set.disjoint_left]
    intro a ha hc
    change 0 ≤ g a at ha
    change 0 < -(g a) at hc
    linarith
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left le_sup_left)
  obtain ⟨y, hy, z, hz, hsum⟩ := Submodule.mem_sup.mp hx.2
  have hz' : z ∈ A ⊔ B := by
    have hsub := (A ⊔ B).sub_mem hx.1 ((show A ≤ A ⊔ B from le_sup_left) hy)
    rw [← hsum, add_sub_cancel_left] at hsub
    exact hsub
  have hz₀ := Submodule.disjoint_def.mp hd z hz' hz
  simpa only [hz₀, add_zero, ← hsum] using hy

private theorem leviSpace_univ (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (b : Basis Π ℝ (E H)) (hb : ∀ i, b i = (i : E H)) :
    leviSpace d v (Set.univ : Set Π) = ⊤ := by
  rw [leviSpace_eq _ hss hH]
  have he : {a : D | ρ a ∈ subsystemSpan d v (Set.univ : Set Π)} = Set.univ := by
    ext a
    change (ρ a ∈ subsystemSpan d v (Set.univ : Set Π)) ↔ True
    rw [mem_subsystem_iff b hb]
    simp
  rw [he]
  simp only [weightSpan, Set.mem_univ, iSup_true]
  exact iSup_rootSpace_eq_top H hH.1

private theorem leviSpace_empty :
    leviSpace d v (∅ : Set Π) = H.toSubmodule := by
  unfold leviSpace
  haveI : IsEmpty (SubsystemRoot d v (∅ : Set Π)) := ⟨fun a => by
    have hh : ρ a.val.val = 0 := by
      have hm := a.property
      change ρ a.val.val ∈ Submodule.span ℝ (Subtype.val '' (∅ : Set Π)) at hm
      simpa only [Set.image_empty, Submodule.span_empty, Submodule.mem_bot] using hm
    exact a.val.property.1 (by
      have he := (d).extension_root a.val.val a.val.property
      change (d).j (ρ a.val.val) = a.val.val at he
      simpa [hh] using he.symm)⟩
  simp

private theorem oppositeSpace_empty :
    oppositeSpace d v (∅ : Set Π) = borelSpace H (-φ) := by
  apply sup_eq_left.mpr
  refine iSup_le fun a => ?_
  have hr : ρ a.val.val = 0 := by simpa [subsystemSpan] using a.property
  have hp : 0 < φ a.val.val := a.val.property.2
  change 0 < inner ℝ v (ρ a.val.val) at hp
  rw [hr, inner_zero_right] at hp
  exact (lt_irrefl 0 hp).elim

end Geometry

open private functional_regular neg_root parabolicSpace_empty from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.StandardParabolics

/-- The two standard parabolics have the indicated common Levi, and the
strictly signed summands are their largest nilpotent ideals. -/
theorem decomposition : decompositionType.{u} := by
  intro L _ _ _ hss H hH d₀ v hv S P hP
  letI : Fact (Realization H) := ⟨d₀⟩
  letI := d₀.normedAddCommGroup
  letI := d₀.innerProductSpace
  obtain ⟨b, hb⟩ := simpleRoots_basis (realRoots H) d₀.root_system v hv
  let g := grading b S
  let f := positiveFunctional d₀ v
  have h𝔩 : leviSpace d₀ v S = weightSpan {a : D | g a = 0} := leviSpace_eq_zero b S hb hss hH hv
  have hplus : nilSpace d₀ v S f = weightSpan {a : D | 0 < g a} :=
    nilSpace_eq S f g (fun _ h => grading_pos_iff b S hb hv h)
  have hminus : nilSpace d₀ v S (-f) = weightSpan {a : D | 0 < (-g) a} :=
    nilSpace_eq S (-f) (-g) (fun _ h => grading_neg_iff b S hb hv h)
  have h𝔭 : P.toSubmodule = weightSpan {a : D | 0 ≤ g a} := by
    rw [hP, parabolicSpace_sup S hv, h𝔩, hplus, weightSpan_nonneg]
  let M : LieSubalgebra ℂ L :=
    { toSubmodule := weightSpan {a : D | g a = 0}, lie_mem' := fun hx hy =>
      weightSpan_bracket (fun a ha b hb => by
        change g a = 0 at ha
        change g b = 0 at hb
        change g (a + b) = 0
        rw [map_add, ha, hb, add_zero]) hx hy }
  let Q : LieSubalgebra ℂ L :=
    { toSubmodule := weightSpan {a : D | 0 ≤ (-g) a}, lie_mem' := fun hx hy =>
      weightSpan_bracket (fun a ha b hb => by
        change 0 ≤ (-g) (a + b)
        rw [map_add]
        exact add_nonneg ha hb) hx hy }
  have hQ : Q.toSubmodule = oppositeSpace d₀ v S := by
    change weightSpan _ = _
    rw [oppositeSpace_sup S hv, h𝔩, hminus, weightSpan_nonneg]
    congr 2
    ext a
    exact neg_eq_zero
  let U := nilradical ℂ P
  let V := nilradical ℂ Q
  have hU : idealSpace U = nilSpace d₀ v S f := by
    rw [hplus]
    exact nilradical_weightSpan hss hH d₀ f g (functional_regular hv) (fun _ => neg_root)
      h𝔭 (hP.symm ▸ le_sup_left) (fun a ha hp => ((grading_pos_iff b S hb hv (.inr ha)).mp hp).2.1)
  have hfneg : ∀ a ∈ rootSet H, (-f) a ≠ 0 :=
    fun a ha => neg_ne_zero.mpr (functional_regular hv a ha)
  have hV : idealSpace V = nilSpace d₀ v S (-f) := by
    rw [hminus]
    exact nilradical_weightSpan hss hH d₀ (-f) (-g) hfneg (fun _ => neg_root)
      rfl (hQ.symm ▸ le_sup_left) (fun a ha hp => ((grading_neg_iff b S hb hv (.inr ha)).mp hp).2.1)
  refine ⟨M, Q, U, V, h𝔩.symm, hQ, hU, hV, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl,
    nilradical_nilpotent ℂ P, nilradical_nilpotent ℂ Q, ?_, ?_⟩
  · change Disjoint (weightSpan {a : D | g a = 0}) (idealSpace U)
    rw [hU, hplus]
    apply weightSpan_disjoint hH
    exact Set.disjoint_left.mpr fun a (ha : g a = 0) (hb : 0 < g a) => (ne_of_gt hb) ha
  · change P.toSubmodule = M.toSubmodule ⊔ idealSpace U
    rw [hP, parabolicSpace_sup S hv, hU, h𝔩]
  · change Disjoint (weightSpan {a : D | g a = 0}) (idealSpace V)
    rw [hV, hminus]
    apply weightSpan_disjoint hH
    exact Set.disjoint_left.mpr fun a (ha : g a = 0) (hb : 0 < -(g a)) => by simpa [ha] using hb
  · change Q.toSubmodule = M.toSubmodule ⊔ idealSpace V
    rw [hQ, oppositeSpace_sup S hv, hV, h𝔩]
  · obtain ⟨B, hB, hsolv, _⟩ := BorelSubalgebras.standard_borel hss H hH (-f) hfneg
    refine ⟨B, hB, hsolv, ?_⟩
    change B.toSubmodule ≤ Q.toSubmodule
    rw [hB, hQ]
    exact le_sup_left
  · apply LieSubalgebra.toSubmodule_injective
    change P.toSubmodule ⊓ weightSpan {a : D | 0 ≤ (-g) a} = weightSpan {a : D | g a = 0}
    rw [h𝔭, weightSpan_opposite_inf hH]
  · rintro rfl
    have ht : M = ⊤ := LieSubalgebra.toSubmodule_injective
      (h𝔩.symm.trans (leviSpace_univ hss hH b hb))
    have hg : g = 0 := by
      simp [g, grading]
    have hbot (J : LieSubalgebra ℂ L) (I : LieIdeal ℂ J) (he : idealSpace I = ⊥) : I = ⊥ := by
      apply LieSubmodule.toSubmodule_injective
      apply Submodule.map_injective_of_injective (f := J.incl.toLinearMap) Subtype.val_injective
      change idealSpace I = Submodule.map J.incl.toLinearMap (⊥ : Submodule ℂ J)
      rwa [Submodule.map_bot]
    have hspan : weightSpan {a : D | 0 < (0 : D →ₗ[ℝ] ℝ) a} = ⊥ := by
      apply bot_unique
      exact iSup₂_le fun a ha => (lt_irrefl (0 : ℝ) ha).elim
    refine ⟨ht, hbot P U ?_, hbot Q V ?_⟩
    · rw [hU, hplus, hg, hspan]
    · rw [hV, hminus, hg, neg_zero, hspan]
  · rintro rfl
    exact ⟨LieSubalgebra.toSubmodule_injective (h𝔩.symm.trans (leviSpace_empty (v := v))),
      hP.trans (parabolicSpace_empty (v := v)), hQ.trans (oppositeSpace_empty (v := v))⟩

section Cartan

variable [Fact (Realization H)]
set_option hygiene false in
local notation "d" => (Fact.out : Realization H)
local instance : NormedAddCommGroup (E H) := (d).normedAddCommGroup
local instance : InnerProductSpace ℝ (E H) := (d).innerProductSpace

variable {v : E H} (S : Set (Simple d v))
set_option hygiene false in
local notation "W" => subsystemSpan d v S
set_option hygiene false in
local notation "C" => subsystemCartan d v S
set_option hygiene false in
local notation "Z" => centralCartan d v S
open private extend_root from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.StandardParabolics
open scoped InnerProductSpace

private theorem mem_centralCartan_iff (h : H) :
    h ∈ Z ↔ ∀ w ∈ W, (d).j w h = 0 := by
  change (h ∈ ⨅ i : S, LinearMap.ker ((d).j (i.val : E H))) ↔ _
  rw [Submodule.mem_iInf]
  constructor
  · intro hh w hw
    have hm : W ≤ LinearMap.ker ((Module.Dual.eval ℂ H h).restrictScalars ℝ |>.comp (d).j) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, hi, rfl⟩
      exact hh ⟨i, hi⟩
    exact hm hw
  · intro hh i
    exact hh (i.val : E H) (Submodule.subset_span ⟨i.val, i.property, rfl⟩)

private theorem subsystem_root_vanish {h : H} (hh : h ∈ Z)
    (a : SubsystemRoot d v S) : a.val.val h = 0 := by
  rw [← (d).extension_root _ a.val.property]
  exact (mem_centralCartan_iff S h).mp hh _ a.property

private theorem vanishes_simple_of_vanishes_subsystem (h : H)
    (hh : ∀ a : SubsystemRoot d v S, a.val.val h = 0) : h ∈ Z := by
  apply (Submodule.mem_iInf _).mpr
  intro i
  change (d).j (i.val : E H) h = 0
  have hi := simpleRoots_subset (realRoots H) v i.val.property
  obtain ⟨hr, he⟩ := extend_root hi
  exact hh ⟨⟨(d).j (i.val : E H), hr⟩, by
    change restrictRoot H ((d).j (i.val : E H)) ∈ W
    rw [he]
    exact Submodule.subset_span ⟨i.val, i.property, rfl⟩⟩

private theorem tAlpha_eq_riesz (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (a : D) (ha : a ∈ rootSet H) :
    tAlpha H a = ((d).q (restrictRoot H a) : H) := by
  symm
  apply tAlpha_unique hss H hH
  intro h
  exact congrArg (fun f : D => f h) ((d).extension_root a ha)

private theorem riesz_mem_subsystemCartan (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    {w : E H} (hw : w ∈ W) : ((d).q w : H) ∈ C := by
  have hm : W ≤ ((C).restrictScalars ℝ).comap
      ((realCartan H).subtype.comp (d).q.toLinearMap) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    have hr := simpleRoots_subset (realRoots H) v i.property
    obtain ⟨ha, he⟩ := extend_root hr
    let a := (d).j (i : E H)
    have hmem : restrictRoot H a ∈ W := by
      rw [he]
      exact Submodule.subset_span ⟨i, hi, rfl⟩
    have hcoroot : killingCoroot H a ∈ C :=
      Submodule.subset_span ⟨⟨⟨a, ha⟩, hmem⟩, rfl⟩
    have hne : (2 / rootForm H a a : ℂ) ≠ 0 :=
      div_ne_zero (by norm_num) (rootForm_self_ne_zero hss H hH a ha)
    have ht : tAlpha H a ∈ C :=
      ((C).smul_mem_iff hne).mp hcoroot
    rw [tAlpha_eq_riesz hss hH a ha, he] at ht
    exact ht
  exact hm hw

private theorem pair_riesz (a b : E H) : a ((d).q b) = inner ℝ a b := by
  have h := congrArg Complex.re ((d).riesz_pairing a ((d).q b))
  exact h.symm

private def cartanCoords : H ≃ₗ[ℝ] E H × E H :=
  (d).cartanDecomposition.symm.trans ((d).q.symm.prodCongr (d).q.symm)

private theorem cartanCoords_symm_apply (a b : E H) :
    (cartanCoords (H := H)).symm (a, b) = ((d).q a : H) + Complex.I • ((d).q b : H) := rfl

private theorem cartanCoords_smul (c : ℂ) (h : H) :
    cartanCoords (c • h) =
      (c.re • (cartanCoords h).1 - c.im • (cartanCoords h).2,
       c.im • (cartanCoords h).1 + c.re • (cartanCoords h).2) := by
  let a := (cartanCoords h).1
  let b := (cartanCoords h).2
  have hh : ((d).q a : H) + Complex.I • ((d).q b : H) = h := by
    rw [← cartanCoords_symm_apply, show (a, b) = cartanCoords h from Prod.eta _]
    exact LinearEquiv.symm_apply_apply _ _
  apply (cartanCoords (H := H)).symm.injective
  rw [LinearEquiv.symm_apply_apply, cartanCoords_symm_apply]
  conv_lhs => rw [← hh]
  change c • (((d).q a : H) + Complex.I • ((d).q b : H)) =
    ((d).q (c.re • a - c.im • b) : H) + Complex.I • ((d).q (c.im • a + c.re • b) : H)
  simp only [map_sub, map_add, map_smul, Submodule.coe_sub, Submodule.coe_add,
    Submodule.coe_smul, smul_add, smul_smul]
  have hc : (c.re : ℂ) + Complex.I * (c.im : ℂ) = c := by simpa only [mul_comm] using Complex.re_add_im c
  have hci : Complex.I * c = -(c.im : ℂ) + Complex.I * (c.re : ℂ) := by
    rw [← hc]
    ring_nf
    simp [sub_eq_add_neg]
  match_scalars
  · exact hc.symm
  · change c * Complex.I = -(c.im : ℂ) + Complex.I * (c.re : ℂ)
    rwa [mul_comm c Complex.I]

private theorem cartanCoords_mem (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    {h : H} (hh : h ∈ C) :
    (cartanCoords h).1 ∈ W ∧ (cartanCoords h).2 ∈ W := by
  refine Submodule.span_induction (p := fun h _ => (cartanCoords h).1 ∈ W ∧
    (cartanCoords h).2 ∈ W) ?_ (by simp) ?_ ?_ hh
  · rintro _ ⟨a, rfl⟩
    change (cartanCoords (killingCoroot H a.val.val)).1 ∈ W ∧
      (cartanCoords (killingCoroot H a.val.val)).2 ∈ W
    rw [killingCoroot_eq, tAlpha_eq_riesz hss hH _ a.val.property, cartanCoords_smul]
    have he : cartanCoords ((d).q (restrictRoot H a.val.val) : H) =
        (restrictRoot H a.val.val, 0) := by
      rw [← LinearEquiv.apply_symm_apply (cartanCoords (H := H)) (restrictRoot H a.val.val, 0),
        cartanCoords_symm_apply]
      simp
    rw [he]
    simpa using ⟨(W).smul_mem (2 / rootForm H a.val.val a.val.val : ℂ).re a.property,
      (W).smul_mem (2 / rootForm H a.val.val a.val.val : ℂ).im a.property⟩
  · intro x y _ _ hx hy
    rw [map_add]
    exact ⟨(W).add_mem hx.1 hy.1, (W).add_mem hx.2 hy.2⟩
  · intro c x _ hx
    rw [cartanCoords_smul]
    exact ⟨(W).sub_mem ((W).smul_mem _ hx.1) ((W).smul_mem _ hx.2),
      (W).add_mem ((W).smul_mem _ hx.1) ((W).smul_mem _ hx.2)⟩

private theorem cartan_extension (w a b : E H) :
    (d).j w (cartanCoords.symm (a, b)) =
      (inner ℝ w a : ℂ) + Complex.I * (inner ℝ w b : ℂ) := by
  rw [cartanCoords_symm_apply, (d).extension_formula, pair_riesz, pair_riesz]

private theorem subsystemCartan_isCompl (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H) :
    IsCompl C Z := by
  haveI : FiniteDimensional ℝ H := FiniteDimensional.trans ℝ ℂ H
  constructor
  · rw [Submodule.disjoint_def]
    intro h hc hz
    obtain ⟨ha, hb⟩ := cartanCoords_mem S hss hH hc
    let a := (cartanCoords h).1
    let b := (cartanCoords h).2
    have he : cartanCoords.symm (a, b) = h := LinearEquiv.symm_apply_apply _ _
    have hparts (w : E H) (hw : w ∈ W) :
        (inner ℝ w a : ℂ) + Complex.I * (inner ℝ w b : ℂ) = 0 :=
      (cartan_extension w a b).symm.trans (he ▸ (mem_centralCartan_iff S h).mp hz w hw)
    have ha₀ : a = 0 := by
      apply (inner_self_eq_zero (𝕜 := ℝ)).mp
      simpa only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, zero_mul, one_mul, sub_zero, add_zero] using congrArg Complex.re (hparts a ha)
    have hb₀ : b = 0 := by
      apply (inner_self_eq_zero (𝕜 := ℝ)).mp
      simpa only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.zero_im, zero_mul, one_mul, zero_add] using congrArg Complex.im (hparts b hb)
    rw [ha₀, hb₀, cartanCoords_symm_apply] at he
    simpa using he.symm
  · rw [codisjoint_iff_le_sup]
    intro h _
    let a := (cartanCoords h).1
    let b := (cartanCoords h).2
    obtain ⟨a₁, ha₁, a₂, ha₂, ea⟩ := Submodule.mem_sup.mp
      (show a ∈ W ⊔ Wᗮ from (W).isCompl_orthogonal.sup_eq_top ▸ Submodule.mem_top)
    obtain ⟨b₁, hb₁, b₂, hb₂, eb⟩ := Submodule.mem_sup.mp
      (show b ∈ W ⊔ Wᗮ from (W).isCompl_orthogonal.sup_eq_top ▸ Submodule.mem_top)
    refine Submodule.mem_sup.mpr ⟨cartanCoords.symm (a₁, b₁), ?_, cartanCoords.symm (a₂, b₂), ?_, ?_⟩
    · rw [cartanCoords_symm_apply]
      exact (C).add_mem (riesz_mem_subsystemCartan S hss hH ha₁)
        ((C).smul_mem _ (riesz_mem_subsystemCartan S hss hH hb₁))
    · apply (mem_centralCartan_iff S _).mpr
      intro w hw
      rw [cartan_extension, ha₂ w hw, hb₂ w hw]
      simp
    · rw [← map_add]
      exact (congrArg cartanCoords.symm (Prod.ext ea eb)).trans (LinearEquiv.symm_apply_apply _ _)

private theorem levi_cartan_le {M : LieSubalgebra ℂ L} (hM : M.toSubmodule = leviSpace d v S) :
    H.toSubmodule ≤ M.toSubmodule :=
  hM.symm ▸ le_sup_left

private theorem levi_root_le {M : LieSubalgebra ℂ L} (hM : M.toSubmodule = leviSpace d v S)
    (a : SubsystemRoot d v S) : rootSpace H a.val.val ≤ M.toSubmodule := by
  rw [hM]
  exact (le_iSup (fun c : SubsystemRoot d v S => rootSpace H c.val.val) a).trans le_sup_right

private theorem levi_radical_le_cartan (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    {M : LieSubalgebra ℂ L} (hM : M.toSubmodule = leviSpace d v S) :
    idealSpace (LieAlgebra.radical ℂ M) ≤ H.toSubmodule := by
  let I := LieAlgebra.radical ℂ M
  rw [idealSpace_weightSplit hH (levi_cartan_le S hM) I]
  refine iSup_le fun a x hx => ?_
  by_cases hzero : a = 0
  · exact (rootSpace_zero hss H hH ▸ (hzero ▸ hx.2 : x ∈ rootSpace H 0))
  suffices x = 0 by simp [this]
  by_cases hr : a ∈ rootSet H
  · by_cases hm : restrictRoot H a ∈ W
    · exact no_root_in_solvable hss hH I hr
        (levi_root_le S hM ⟨⟨-a, neg_root hr⟩, by
          change restrictRoot H (-a) ∈ W
          rwa [map_neg, Submodule.neg_mem_iff]⟩) hx.2 hx.1
    · have hdis : Disjoint (rootSpace H a) M.toSubmodule := by
        rw [hM, leviSpace_eq S hss hH]
        exact (rootSpace_independent H hH.1).disjoint_biSup hm
      exact Submodule.disjoint_def.mp hdis x hx.2 (idealSpace_le I hx.1)
  · have hx' : x ∈ rootSpace H a := hx.2
    rwa [rootSpace_eq_bot_of_not_mem H a hzero hr, Submodule.mem_bot] at hx'

private theorem center_is_centralCartan (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    {M : LieSubalgebra ℂ L} (hM : M.toSubmodule = leviSpace d v S) :
    LieAlgebra.HasCentralRadical ℂ M ∧
      idealSpace (LieAlgebra.center ℂ M) = (Z).map H.incl.toLinearMap := by
  let I := LieAlgebra.radical ℂ M
  have hrad := levi_radical_le_cartan S hss hH hM
  have hcartan : idealSpace I ≤ (Z).map H.incl.toLinearMap := by
    intro x hx
    let h : H := ⟨x, hrad hx⟩
    refine ⟨h, vanishes_simple_of_vanishes_subsystem S h ?_, rfl⟩
    intro a
    obtain ⟨y, hy, hy₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot a.val.property.2
    have hlie : ⁅x, y⁆ ∈ idealSpace I := by
      rw [← lie_skew x y]
      exact (idealSpace I).neg_mem (idealSpace_lie I (levi_root_le S hM a hy) hx)
    have he := (mem_rootSpace H a.val.val y).mp hy h
    change ⁅x, y⁆ = _ at he
    have hbr : ⁅x, y⁆ ∈ rootSpace H a.val.val := he.symm ▸ (rootSpace H a.val.val).smul_mem _ hy
    have hd : Disjoint (rootSpace H a.val.val) H.toSubmodule := by
      rw [← rootSpace_zero hss H hH]
      exact (rootSpace_independent H hH.1).pairwiseDisjoint a.val.property.1
    exact (smul_eq_zero.mp (he.symm.trans (Submodule.disjoint_def.mp hd _ hbr (hrad hlie)))).resolve_right hy₀
  have hcenter : (Z).map H.incl.toLinearMap ≤ idealSpace (LieAlgebra.center ℂ M) := by
    rintro _ ⟨h, hh, rfl⟩
    let z : M := ⟨h, levi_cartan_le S hM h.property⟩
    refine ⟨z, (LieModule.mem_maxTrivSubmodule _ _ _ _).mpr ?_, rfl⟩
    intro y
    apply Subtype.ext
    change ⁅(y : L), (h : L)⁆ = 0
    rw [← neg_eq_zero, lie_skew]
    have hy : (y : L) ∈ H.toSubmodule ⊔
        ⨆ a : SubsystemRoot d v S, rootSpace H a.val.val := by
      change (y : L) ∈ leviSpace d v S
      rw [← hM]
      exact y.property
    have hc : H.toSubmodule ≤ LinearMap.ker (LieAlgebra.ad ℂ L (h : L)) := by
      rw [← rootSpace_zero hss H hH]
      exact fun x hx => by simpa using (mem_rootSpace H 0 x).mp hx h
    have hr : (⨆ a : SubsystemRoot d v S, rootSpace H a.val.val) ≤
        LinearMap.ker (LieAlgebra.ad ℂ L (h : L)) := by
      refine iSup_le fun a x hx => ?_
      change ⁅(h : L), x⁆ = 0
      rw [(mem_rootSpace H a.val.val x).mp hx h, subsystem_root_vanish S hh a, zero_smul]
    exact sup_le hc hr hy
  have hrc : I ≤ LieAlgebra.center ℂ M := by
    intro x hx
    obtain ⟨y, hy, he⟩ := hcenter (hcartan ⟨x, hx, rfl⟩)
    have hey : y = x := Subtype.ext he
    exact hey ▸ hy
  have hre := LieAlgebra.hasCentralRadical_of_radical_le ℂ M hrc
  exact ⟨hre, le_antisymm (hre.radical_eq_center ▸ hcartan) hcenter⟩

private theorem derived_space (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    {M : LieSubalgebra ℂ L} (hM : M.toSubmodule = leviSpace d v S) :
    idealSpace (LieAlgebra.derivedSeries ℂ M 1) =
      (C).map H.incl.toLinearMap ⊔ ⨆ a : SubsystemRoot d v S, rootSpace H a.val.val := by
  let K := LieAlgebra.derivedSeries ℂ M 1
  let X := (C).map H.incl.toLinearMap ⊔ ⨆ a : SubsystemRoot d v S, rootSpace H a.val.val
  have hcomm (x y : M) : ⁅(x : L), (y : L)⁆ ∈ idealSpace K := by
    refine ⟨⁅x, y⁆, ?_, rfl⟩
    change ⁅x, y⁆ ∈ K.toLieSubalgebra.toSubmodule
    rw [LieAlgebra.coe_derivedSeries_one_eq]
    exact Submodule.subset_span ⟨x, y, rfl⟩
  apply le_antisymm
  · have hsub : K.toSubmodule ≤ X.comap M.incl.toLinearMap := by
      change K.toLieSubalgebra.toSubmodule ≤ _
      rw [LieAlgebra.coe_derivedSeries_one_eq, Submodule.span_le]
      rintro _ ⟨x, y, rfl⟩
      change ⁅(x : L), (y : L)⁆ ∈ X
      let A : Set D := {a | a = 0 ∨ a ∈ rootSet H ∧ restrictRoot H a ∈ W}
      have hweight : M.toSubmodule = weightSpan A := by
        rw [hM, leviSpace_eq S hss hH]
        apply le_antisymm <;> apply weightSpan_mono_supported
        · intro a ha hs
          exact hs.imp id (fun hr => ⟨hr, ha⟩)
        · rintro a (rfl | ⟨_, hw⟩) _
          · change restrictRoot H 0 ∈ W
            simp
          · exact hw
      let bracket : L →ₗ[ℂ] L →ₗ[ℂ] L := (LieAlgebra.ad ℂ L).toLinearMap
      apply (show Submodule.map₂ bracket (weightSpan A) (weightSpan A) ≤ X from ?_)
        (Submodule.apply_mem_map₂ bracket (hweight ▸ x.property) (hweight ▸ y.property))
      unfold weightSpan
      simp only [Submodule.map₂_iSup_left, Submodule.map₂_iSup_right]
      refine iSup₂_le fun b hb => iSup₂_le fun a ha => Submodule.map₂_le.mpr fun e he f hf => ?_
      change ⁅e, f⁆ ∈ X
      have hw (a : D) (ha : a ∈ A) : restrictRoot H a ∈ W := by
        rcases ha with rfl | ⟨_, h⟩
        · simp
        · exact h
      by_cases hz : a + b = 0
      · have hb' : b = -a := (add_eq_zero_iff_neg_eq.mp hz).symm
        subst b
        by_cases ha₀ : a = 0
        · subst a
          have he' : e ∈ rootSpace H (0 : D) := he
          rw [rootSpace_zero hss H hH] at he'
          have heq := (mem_rootSpace H (-(0 : D)) f).mp hf ⟨e, he'⟩
          have heq' : ⁅e, f⁆ = 0 := by simpa using heq
          rw [heq']
          exact Submodule.zero_mem _
        have har := (show a = 0 ∨ a ∈ rootSet H ∧ restrictRoot H a ∈ W from ha).resolve_left ha₀
        have ht := riesz_mem_subsystemCartan S hss hH har.2
        rw [← tAlpha_eq_riesz hss hH a har.1] at ht
        apply (show (C).map H.incl.toLinearMap ≤ X from le_sup_left)
        rw [opposite_root_bracket hss H hH a e f he hf]
        exact Submodule.smul_mem _ _ ⟨tAlpha H a, ht, rfl⟩
      · have hbr := rootSpace_bracket H a b e f he hf
        by_cases hr : a + b ∈ rootSet H
        · have hh : restrictRoot H (a + b) ∈ W := by
            rw [map_add]
            exact (W).add_mem (hw a ha) (hw b hb)
          exact ((le_iSup (fun a : SubsystemRoot d v S => rootSpace H a.val.val)
            ⟨⟨a + b, hr⟩, hh⟩).trans le_sup_right : rootSpace H (a + b) ≤ X) hbr
        · rw [rootSpace_eq_bot_of_not_mem H _ hz hr, Submodule.mem_bot] at hbr
          rw [hbr]
          exact Submodule.zero_mem _
    exact (Submodule.map_le_iff_le_comap.mpr hsub)
  · refine sup_le ?_ (iSup_le fun a y hy => ?_)
    · rw [subsystemCartan, Submodule.map_span]
      apply Submodule.span_le.mpr
      rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
      obtain ⟨e, f, he, hf, _, _, hef, _, _⟩ := exists_root_triple hss H hH a.val.val a.val.property
      have hn : restrictRoot H (-a.val.val) ∈ W := by
        rw [map_neg, Submodule.neg_mem_iff]
        exact a.property
      change (killingCoroot H a.val.val : L) ∈ idealSpace K
      rw [← hef]
      exact hcomm ⟨e, levi_root_le S hM a he⟩
        ⟨f, levi_root_le S hM ⟨⟨-a.val.val, neg_root a.val.property⟩, hn⟩ hf⟩
    · obtain ⟨h, hh⟩ : ∃ h : H, a.val.val h ≠ 0 := by
        by_contra! hn
        exact a.val.property.1 (LinearMap.ext hn)
      apply ((idealSpace K).smul_mem_iff hh).mp
      rw [← (mem_rootSpace H a.val.val y).mp hy h]
      exact hcomm ⟨h, levi_cartan_le S hM h.property⟩ ⟨y, levi_root_le S hM a hy⟩

private theorem derived_compl_center (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    {M : LieSubalgebra ℂ L} (hM : M.toSubmodule = leviSpace d v S) :
    IsCompl (LieAlgebra.derivedSeries ℂ M 1) (LieAlgebra.center ℂ M) := by
  let K := LieAlgebra.derivedSeries ℂ M 1
  let J := LieAlgebra.center ℂ M
  let C' := (C).map H.incl.toLinearMap
  let Z' := (Z).map H.incl.toLinearMap
  let A := ⨆ a : SubsystemRoot d v S, rootSpace H a.val.val
  obtain ⟨_, hZ⟩ := center_is_centralCartan S hss hH hM
  have hK := derived_space S hss hH hM
  have hCZ := subsystemCartan_isCompl S hss hH
  have hdisj : Disjoint C' Z' := Submodule.disjoint_map
    (f := H.incl.toLinearMap) Subtype.val_injective hCZ.disjoint
  have hsup : C' ⊔ Z' = H.toSubmodule := by
    change (C).map H.incl.toLinearMap ⊔ (Z).map H.incl.toLinearMap = _
    rw [← Submodule.map_sup, hCZ.sup_eq_top, Submodule.map_top]
    exact Submodule.range_subtype _
  have hAH : Disjoint A H.toSubmodule := by
    rw [← rootSpace_zero hss H hH]
    have h₀ : (0 : D) ∉ Set.range (fun a : SubsystemRoot d v S => a.val.val) := by
      rintro ⟨a, ha⟩
      exact a.val.property.1 ha
    refine ((rootSpace_independent H hH.1).disjoint_biSup h₀).symm.mono_left ?_
    exact iSup_le fun a => root_le_weightSpan (Set.mem_range_self a)
  have hdisj' : Disjoint (C' ⊔ A) Z' := by
    rw [Submodule.disjoint_def]
    intro x hx hz
    obtain ⟨y, hy, z, hzA, hsum⟩ := Submodule.mem_sup.mp hx
    have hzH : z ∈ H.toSubmodule := by
      have hyH : y ∈ H.toSubmodule :=
        (show C' ≤ H.toSubmodule from hsup ▸ le_sup_left) hy
      have hxH : x ∈ H.toSubmodule :=
        (show Z' ≤ H.toSubmodule from hsup ▸ le_sup_right) hz
      have he := H.toSubmodule.sub_mem hxH hyH
      rwa [← hsum, add_sub_cancel_left] at he
    have hz₀ := Submodule.disjoint_def.mp hAH z hzA hzH
    have he : y = x := by simpa [hz₀] using hsum
    exact Submodule.disjoint_def.mp hdisj x (he ▸ hy) hz
  constructor
  · rw [disjoint_iff]
    apply LieSubmodule.toSubmodule_injective
    apply Submodule.map_injective_of_injective (f := M.incl.toLinearMap) Subtype.val_injective
    change Submodule.map M.incl.toLinearMap (K.toSubmodule ⊓ J.toSubmodule) =
      Submodule.map M.incl.toLinearMap (⊥ : Submodule ℂ M)
    rw [Submodule.map_inf _ Subtype.val_injective, Submodule.map_bot]
    change idealSpace K ⊓ idealSpace J = ⊥
    rw [hK, hZ]
    exact disjoint_iff.mp hdisj'
  · rw [codisjoint_iff]
    apply LieSubmodule.toSubmodule_injective
    apply Submodule.map_injective_of_injective (f := M.incl.toLinearMap) Subtype.val_injective
    change Submodule.map M.incl.toLinearMap (K.toSubmodule ⊔ J.toSubmodule) =
      Submodule.map M.incl.toLinearMap (⊤ : Submodule ℂ M)
    rw [Submodule.map_sup, Submodule.map_top,
      show M.incl.toLinearMap.range = M.toSubmodule from Submodule.range_subtype _]
    change idealSpace K ⊔ idealSpace J = M.toSubmodule
    rw [hK, hZ, hM]
    change (C' ⊔ A) ⊔ Z' = H.toSubmodule ⊔ A
    rw [sup_right_comm, hsup]

end Cartan

private theorem semisimple_of_central_complement
    {M : Type u} [LieRing M] [LieAlgebra ℂ M] [FiniteDimensional ℂ M]
    (hre : LieAlgebra.HasCentralRadical ℂ M) (K : LieIdeal ℂ M)
    (hc : IsCompl K (LieAlgebra.center ℂ M)) :
    LieAlgebra.IsSemisimple ℂ K := by
  apply semisimple_structure
  let J := LieAlgebra.radical ℂ K
  let J' : LieIdeal ℂ M :=
    { J.toSubmodule.map K.incl.toLinearMap with
      lie_mem := by
        rintro x _ ⟨y, hy, rfl⟩
        have hx : x ∈ K.toSubmodule ⊔ (LieAlgebra.center ℂ M).toSubmodule := by
          change x ∈ (K ⊔ LieAlgebra.center ℂ M : LieIdeal ℂ M)
          rw [hc.sup_eq_top]
          trivial
        obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
        have hcenter : ⁅z, (y : M)⁆ = 0 := by
          rw [← neg_eq_zero, lie_skew]
          exact (LieModule.mem_maxTrivSubmodule ℂ M M z).mp hz y
        refine ⟨⁅(⟨w, hw⟩ : K), y⁆, J.lie_mem hy, ?_⟩
        change ⁅w, (y : M)⁆ = ⁅w + z, (y : M)⁆
        rw [add_lie, hcenter, add_zero] }
  let f : J →ₗ⁅ℂ⁆ J' :=
    { toFun := fun x => ⟨x.val, ⟨x.val, x.property, rfl⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      map_lie' := fun {_ _} => rfl }
  have hf : Function.Surjective f := by
    rintro ⟨_, ⟨y, hy, rfl⟩⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  have hJ' : J' ≤ LieAlgebra.radical ℂ M :=
    solvable_ideal_le_radical J' hf.lieAlgebra_isSolvable
  rw [hre.radical_eq_center] at hJ'
  show LieAlgebra.radical ℂ K = ⊥
  apply bot_unique
  intro x hx
  have hx' : (x : M) ∈ J' := ⟨x, hx, rfl⟩
  have hzero : (x : M) = 0 := by
    have hd : Disjoint K.toSubmodule (LieAlgebra.center ℂ M).toSubmodule := by
      rw [disjoint_iff, ← LieSubmodule.inf_toSubmodule, disjoint_iff.mp hc.disjoint]
      rfl
    exact Submodule.disjoint_def.mp hd x x.property (hJ' hx')
  exact (LieSubmodule.mem_bot x).mpr (Subtype.ext hzero)

/-- The derived ideal is the semisimple subsystem, and its direct complement
is the part of the original Cartan annihilated by the selected simples. -/
theorem levi_structure : structureType.{u} := by
  intro L _ _ _ hss H hH d₀ v _ S M hM
  letI : Fact (Realization H) := ⟨d₀⟩
  obtain ⟨hre, hz⟩ := center_is_centralCartan S hss hH hM
  have hc := derived_compl_center S hss hH hM
  exact ⟨hre, hz, LieAlgebra.derivedSeries ℂ M 1,
    semisimple_of_central_complement hre _ hc, derived_space S hss hH hM, hc⟩

end LieAlgebrasAndRepresentations.ParabolicLevi
