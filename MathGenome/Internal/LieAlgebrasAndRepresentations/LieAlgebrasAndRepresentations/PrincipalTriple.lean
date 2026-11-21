import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.PrincipalTriple
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.HighestRoot
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootTriples
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClebschGordan
import Mathlib.LinearAlgebra.RootSystem.BaseExists

noncomputable section
open scoped Classical BigOperators
open Function Set Module

namespace LieAlgebrasAndRepresentations.PrincipalTriple

open HighestRoot IsAddIndecomposable
open Specs.LieAlgebrasAndRepresentations.RootDecomposition
open Specs.LieAlgebrasAndRepresentations.RootForm
open Specs.LieAlgebrasAndRepresentations.Sl2Model
open Specs.LieAlgebrasAndRepresentations.Sl2SimpleModules
open private maximalToral_isCartan rootSpace_eq_generalized rootWeight rootWeight_nonzero
  coroot_rootWeight from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootTriples

universe u v

section Base
variable {ι M N : Type*} [Finite ι] [AddCommGroup M] [AddCommGroup N]
  [Module ℂ M] [Module ℂ N] [Module ℝ M] [Module ℝ N]
  [IsScalarTower ℝ ℂ M] [IsScalarTower ℝ ℂ N]
  (P : RootPairing ι ℂ M N) [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
  (φ : Dual ℝ M) (hφ : ∀ i, φ (P.root i) ≠ 0)

omit [Finite ι] [Module ℝ N] [IsScalarTower ℝ ℂ M] [IsScalarTower ℝ ℂ N]
  [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] in
private theorem span_baseOf_eq {K : Type*} [Field K] [Module K M]
    (h : ∀ i, P.root i ∈ AddSubmonoid.closure (P.root '' baseOf P.root φ.toAddMonoidHom) ∨
              -P.root i ∈ AddSubmonoid.closure (P.root '' baseOf P.root φ.toAddMonoidHom)) :
    Submodule.span K (P.root '' baseOf P.root φ.toAddMonoidHom) =
      Submodule.span K (range P.root) := by
  apply le_antisymm (Submodule.span_mono (image_subset_range _ _))
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  have hm : AddSubmonoid.closure (P.root '' baseOf P.root φ.toAddMonoidHom) ≤
      (Submodule.span K (P.root '' baseOf P.root φ.toAddMonoidHom)).toAddSubmonoid :=
    AddSubmonoid.closure_le.mpr Submodule.subset_span
  rcases h i with hi | hi
  · exact hm hi
  · exact (Submodule.neg_mem_iff _).mp (hm hi)

include hφ

private def baseOfFunctional : P.Base := by
  let s := baseOf P.root φ.toAddMonoidHom
  letI := P.indexNeg
  letI : P.IsValuedIn ℝ := RootPairing.IsValuedIn.trans P (T := ℤ) (S := ℝ)
  have hgen (i : ι) : P.root i ∈ AddSubmonoid.closure (P.root '' s) ∨
      -P.root i ∈ AddSubmonoid.closure (P.root '' s) :=
    mem_or_neg_mem_closure_baseOf P.root φ.toAddMonoidHom i (hφ i) (by simp)
  have hr : LinearIndepOn ℝ P.root s := P.linearIndepOn_root_baseOf' φ hφ
  let v (i : s) : P.rootSpan ℝ := P.rootSpanMem ℝ i
  have hspan : Submodule.span ℝ (range v) = ⊤ := by
    apply (Submodule.map_injective_of_injective (P.rootSpan ℝ).injective_subtype)
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← range_comp,
      show (P.rootSpan ℝ).subtype ∘ v = fun i : s => P.root i from rfl, ← image_eq_range,
      span_baseOf_eq P φ hgen]
  have hlin : LinearIndependent ℝ v := by
    apply LinearIndependent.of_comp (P.rootSpan ℝ).subtype
    exact hr
  let b : Basis s ℝ (P.rootSpan ℝ) := Basis.mk hlin (by rw [hspan])
  have hc : Nat.card s = finrank ℂ M := by
    rw [← P.finrank_rootSpanIn ℝ, finrank_eq_nat_card_basis b]
  have hs : Submodule.span ℂ (range fun i : s => P.root i) = ⊤ := by
    rw [← image_eq_range, span_baseOf_eq P φ hgen, RootPairing.IsRootSystem.span_root_eq_top]
  letI : Fintype s := Fintype.ofFinite s
  apply RootPairing.Base.mk' P s _ hgen
  change LinearIndependent ℂ (fun i : s => P.root i)
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hs, finrank_top,
    Fintype.card_eq_nat_card, hc]

private theorem mem_baseOfFunctional (i : ι) :
    i ∈ (baseOfFunctional P φ hφ).support ↔ i ∈ baseOf P.root φ.toAddMonoidHom := by
  simp [baseOfFunctional, RootPairing.Base.mk']

private theorem baseOfFunctional_isPos (i : ι) :
    (baseOfFunctional P φ hφ).IsPos i ↔ 0 < φ (P.root i) := by
  let b := baseOfFunctional P φ hφ
  obtain ⟨f, hf, hs, he⟩ := b.exists_root_eq_sum_int i
  have hsimple (j : ι) (hj : j ∈ b.support) : 0 < φ (P.root j) :=
    ((mem_baseOfFunctional P φ hφ j).mp hj).1
  have hh := b.height_eq_sum he
  have hval : φ (P.root i) = ∑ j ∈ b.support, (f j : ℝ) * φ (P.root j) := by
    conv_lhs => rw [he]
    simp
  change 0 < b.height i ↔ _
  rcases hs with hp | hn
  · have hnon (j : ι) : 0 ≤ f j := hp.le j
    obtain ⟨j, hj⟩ : ∃ j, 0 < f j := by
      by_contra! h
      exact hp.ne (funext fun j => le_antisymm (hnon j) (h j))
    have hj' : j ∈ b.support := hf hj.ne'
    have h₁ : 0 < ∑ j ∈ b.support, f j := Finset.sum_pos' (fun i _ => hnon i) ⟨j, hj', hj⟩
    have h₂ : 0 < ∑ j ∈ b.support, (f j : ℝ) * φ (P.root j) :=
      Finset.sum_pos' (fun i hi => mul_nonneg (by exact_mod_cast hnon i) (hsimple i hi).le)
        ⟨j, hj', mul_pos (by exact_mod_cast hj) (hsimple j hj')⟩
    simp [hh, hval, h₁, h₂]
  · have h₁ : ∑ j ∈ b.support, f j ≤ 0 := Finset.sum_nonpos fun j _ => hn.le j
    have h₂ : ∑ j ∈ b.support, (f j : ℝ) * φ (P.root j) ≤ 0 :=
      Finset.sum_nonpos fun j hj => mul_nonpos_of_nonpos_of_nonneg
        (by exact_mod_cast hn.le j) (hsimple j hj).le
    simp [hh, hval, not_lt.mpr h₁, not_lt.mpr h₂]
omit hφ [Module ℝ M] [Module ℝ N] [IsScalarTower ℝ ℂ M] [IsScalarTower ℝ ℂ N]
  [P.IsRootSystem] in
private theorem simple_eval_sum_coroots [Fintype ι] (b : P.Base) {i : ι}
    (hi : i ∈ b.support) :
    P.toLinearMap (P.root i) (∑ j ∈ Finset.univ.filter b.IsPos, P.coroot j) = 2 := by
  let s := Finset.univ.filter b.IsPos
  have hi' : i ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.isPos_of_mem_support hi⟩
  have hs {j : ι} (hj : j ∈ s.erase i) : P.reflectionPerm i j ∈ s.erase i := by
    obtain ⟨hne, hpos⟩ := Finset.mem_erase.mp hj
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp hpos).2.reflectionPerm hi hne⟩⟩
    intro h
    have hj' : j = P.reflectionPerm i i :=
      (P.reflectionPerm_self i j).symm.trans (congrArg (P.reflectionPerm i) h)
    have hpos' := (Finset.mem_filter.mp hpos).2
    letI := P.indexNeg
    change j = -i at hj'
    rw [hj', RootPairing.Base.isPos_iff, b.height_reflectionPerm_self,
      b.height_one_of_mem_support hi] at hpos'
    norm_num at hpos'
  have hperm : ∑ j ∈ s.erase i, P.coroot (P.reflectionPerm i j) =
      ∑ j ∈ s.erase i, P.coroot j := by
    apply Finset.sum_bij (fun j _ => P.reflectionPerm i j)
    · exact fun _ hj => hs hj
    · exact fun _ _ _ _ he => (P.reflectionPerm i).injective he
    · exact fun j hj => ⟨P.reflectionPerm i j, hs hj, P.reflectionPerm_self i j⟩
    · simp
  let z := ∑ j ∈ s.erase i, P.coroot j
  have hz : P.coreflection i z = z := by
    simp only [z, map_sum, ← P.coroot_reflectionPerm]
    exact hperm
  have hn : P.toLinearMap (P.root i) z = 0 := by
    have hz' : z - P.toLinearMap (P.root i) z • P.coroot i = z := by
      simpa only [P.coreflection_apply, RootPairing.root'] using hz
    exact (smul_eq_zero.mp (sub_eq_self.mp hz')).resolve_right (P.flip.ne_zero i)
  change P.toLinearMap (P.root i) (∑ j ∈ s, P.coroot j) = 2
  rw [← Finset.sum_erase_add _ _ hi', map_add, show (∑ j ∈ s.erase i, P.coroot j) = z from rfl,
    hn, zero_add]
  exact P.root_coroot_two i

end Base

section Cartan
variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
variable (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
  [H.IsCartanSubalgebra] [LieModule.IsTriangularizable ℂ H L] [LieAlgebra.IsKilling ℂ L]

private abbrev P := LieAlgebra.IsKilling.rootSystem H

include hH

private theorem pairingRoot_mem (i : H.root) : (P H).root i ∈ rootSet_value H := by
  constructor
  · intro hz
    exact (P H).ne_zero i hz
  · intro hz
    apply i.val.genWeightSpace_ne_bot
    apply LieSubmodule.toSubmodule_injective
    rw [LieSubmodule.bot_toSubmodule, rootSpace_eq_generalized H hH]
    exact hz

private def adjointRootEquiv : H.root ≃ rootSet_value H :=
  Equiv.ofBijective (fun i => ⟨(P H).root i, pairingRoot_mem H hH i⟩)
    ⟨fun i j hij => (P H).root.injective (congrArg Subtype.val hij),
      fun ⟨α, hα⟩ => ⟨⟨rootWeight H hH α hα, by
        simpa using rootWeight_nonzero H hH α hα⟩, rfl⟩⟩

private theorem pairingRoot_range : range (P H).root = rootSet_value H := by
  apply Subset.antisymm
  · rintro _ ⟨i, rfl⟩
    exact pairingRoot_mem H hH i
  · intro α hα
    obtain ⟨i, hi⟩ := (adjointRootEquiv H hH).surjective ⟨α, hα⟩
    exact ⟨i, congrArg Subtype.val hi⟩

variable (φ : Dual ℝ (Dual ℂ H)) (hφ : ∀ α ∈ rootSet_value H, φ α ≠ 0)

private abbrev cartanBase :=
  baseOfFunctional (P H) φ (fun i => hφ _ (pairingRoot_mem H hH i))

private theorem cartanBase_pos (i : H.root) :
    (cartanBase H hH φ hφ).IsPos i ↔ (P H).root i ∈ _root_.LieAlgebrasAndRepresentations.HighestRoot.positiveRoots H φ := by
  rw [baseOfFunctional_isPos]
  exact ⟨fun hi => ⟨pairingRoot_mem H hH i, hi⟩, And.right⟩

private theorem cartanBase_simple (i : H.root) :
    i ∈ (cartanBase H hH φ hφ).support ↔ (P H).root i ∈ _root_.LieAlgebrasAndRepresentations.HighestRoot.simpleRoots H φ := by
  rw [mem_baseOfFunctional]
  constructor
  · rintro ⟨hi, hind⟩
    refine ⟨⟨pairingRoot_mem H hH i, hi⟩, ?_⟩
    intro β hβ γ hγ
    obtain ⟨j, rfl⟩ := (pairingRoot_range H hH).symm ▸ hβ.1
    obtain ⟨k, rfl⟩ := (pairingRoot_range H hH).symm ▸ hγ.1
    intro he
    exact (hind j hβ.2 k hγ.2 he).elim ((P H).ne_zero j) ((P H).ne_zero k)
  · rintro ⟨hi, hind⟩
    exact ⟨hi.2, fun j hj k hk he => (hind _ ⟨pairingRoot_mem H hH j, hj⟩
      _ ⟨pairingRoot_mem H hH k, hk⟩ he).elim⟩

private def simpleRootEquiv : (cartanBase H hH φ hφ).support ≃ _root_.LieAlgebrasAndRepresentations.HighestRoot.simpleRoots H φ :=
  Equiv.ofBijective (fun i => ⟨(P H).root i, (cartanBase_simple H hH φ hφ i).mp i.property⟩)
    ⟨fun i j hij => Subtype.ext ((P H).root.injective (congrArg Subtype.val hij)),
      fun ⟨α, hα⟩ => by
        obtain ⟨i, rfl⟩ := (pairingRoot_range H hH).symm ▸ hα.1.1
        exact ⟨⟨i, (cartanBase_simple H hH φ hφ i).mpr hα⟩, rfl⟩⟩

private theorem pairing_coroot_eq
    (hss : IsSemisimple ℂ L) (i : H.root) :
    (P H).coroot i = coroot_value H ((P H).root i) := by
  have hi : rootWeight H hH ((P H).root i) (pairingRoot_mem H hH i) = i.val := by
    ext x
    rfl
  change LieAlgebra.IsKilling.coroot i.val = killingCoroot H ((P H).root i)
  rw [← hi]
  exact coroot_rootWeight hss H hH ((P H).root i) (pairingRoot_mem H hH i)

include hφ

private theorem simple_eval_twiceCorootRho (hss : IsSemisimple ℂ L) (a : _root_.LieAlgebrasAndRepresentations.HighestRoot.simpleRoots H φ) :
    a.val (twiceCorootRho H φ) = 2 := by
  let b := cartanBase H hH φ hφ
  let e := simpleRootEquiv H hH φ hφ
  let i := e.symm a
  have hi : (P H).root i = a.val := congrArg Subtype.val (e.apply_symm_apply a)
  let s := Finset.univ.filter b.IsPos
  have hsum : twiceCorootRho H φ = ∑ j ∈ s, (P H).coroot j := by
    have hs : (_root_.LieAlgebrasAndRepresentations.HighestRoot.positiveRoots H φ).Finite := (rootSet_finite H hH.1).subset (fun _ hx => hx.1)
    rw [twiceCorootRho, finsum_mem_eq_finite_toFinset_sum _ hs]
    symm
    apply Finset.sum_bij (fun j _ => (P H).root j)
    · intro j hj
      exact hs.mem_toFinset.mpr ((cartanBase_pos H hH φ hφ j).mp (Finset.mem_filter.mp hj).2)
    · exact fun _ _ _ _ hjk => (P H).root.injective hjk
    · intro α hα
      have hp := hs.mem_toFinset.mp hα
      obtain ⟨j, rfl⟩ := (pairingRoot_range H hH).symm ▸ hp.1
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (cartanBase_pos H hH φ hφ j).mpr hp⟩,
        rfl⟩
    · exact fun j _ => pairing_coroot_eq H hH hss j
  rw [hsum, ← hi]
  exact simple_eval_sum_coroots (P H) b i.property

private theorem pos_or_neg_mem_monoid (i : H.root) :
    (P H).root i ∈ positiveRootMonoid H φ ∨ -(P H).root i ∈ positiveRootMonoid H φ := by
  have he : (P H).root '' (cartanBase H hH φ hφ).support = _root_.LieAlgebrasAndRepresentations.HighestRoot.simpleRoots H φ := by
    ext α
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact (cartanBase_simple H hH φ hφ j).mp hj
    · intro hα
      obtain ⟨j, rfl⟩ := (pairingRoot_range H hH).symm ▸ hα.1.1
      exact ⟨j, (cartanBase_simple H hH φ hφ j).mpr hα, rfl⟩
  simpa only [positiveRootMonoid, ← he] using (cartanBase H hH φ hφ).root_mem_or_neg_mem i

private def simpleCorootBasis :
    Basis (_root_.LieAlgebrasAndRepresentations.HighestRoot.simpleRoots H φ) ℂ H :=
  (cartanBase H hH φ hφ).toCoweightBasis.reindex (simpleRootEquiv H hH φ hφ)

private theorem simpleCorootBasis_apply (hss : IsSemisimple ℂ L) (a : _root_.LieAlgebrasAndRepresentations.HighestRoot.simpleRoots H φ) :
    simpleCorootBasis H hH φ hφ a = coroot_value H a := by
  let e := simpleRootEquiv H hH φ hφ
  have he : (P H).root (e.symm a) = a.val := congrArg Subtype.val (e.apply_symm_apply a)
  rw [simpleCorootBasis, Basis.reindex_apply, RootPairing.Base.toCoweightBasis_apply]
  exact (pairing_coroot_eq H hH hss _).trans (congrArg (coroot_value H) he)

end Cartan


section Triple
variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
variable (H : LieSubalgebra ℂ L) (φ : Dual ℝ (Dual ℂ H))
variable (hsimple : ∀ a : _root_.LieAlgebrasAndRepresentations.HighestRoot.simpleRoots H φ, a.val (twiceCorootRho H φ) = 2)

private theorem list_of_mem_positiveRootMonoid {α : Dual ℂ H} (ha : α ∈ positiveRootMonoid H φ) :
    ∃ l : List (_root_.LieAlgebrasAndRepresentations.HighestRoot.simpleRoots H φ), (l.map Subtype.val).sum = α := by
  refine AddSubmonoid.closure_induction ?_ ?_ ?_ ha
  · intro a ha
    exact ⟨[⟨a, ha⟩], by simp⟩
  · exact ⟨[], rfl⟩
  · rintro a b _ _ ⟨l, rfl⟩ ⟨k, rfl⟩
    exact ⟨l ++ k, by simp⟩

include hsimple in
private theorem eval_list_simple (l : List (_root_.LieAlgebrasAndRepresentations.HighestRoot.simpleRoots H φ)) :
    (l.map Subtype.val).sum (twiceCorootRho H φ) = 2 * (l.length : ℂ) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, LinearMap.add_apply, hsimple, ih, List.length_cons,
      Nat.cast_add, Nat.cast_one]
    ring

include hsimple in
private theorem height_eq_length {α : Dual ℂ H} {l : List (_root_.LieAlgebrasAndRepresentations.HighestRoot.simpleRoots H φ)}
    (hl : (l.map Subtype.val).sum = α) : positiveHeight H φ α = l.length := by
  let s : Set ℕ := {n | ∃ k : List (_root_.LieAlgebrasAndRepresentations.HighestRoot.simpleRoots H φ), k.length = n ∧
    (k.map Subtype.val).sum = α}
  have he : sInf s ∈ s := Nat.sInf_mem ⟨l.length, l, rfl, hl⟩
  obtain ⟨k, hk, he⟩ := he
  have h₁ := eval_list_simple H φ hsimple l
  have h₂ := eval_list_simple H φ hsimple k
  rw [hl] at h₁
  rw [he] at h₂
  change sInf s = l.length
  rw [← hk]
  exact Nat.cast_injective (R := ℂ) (mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)
    (h₂.symm.trans h₁))

omit [FiniteDimensional ℂ L] in
private theorem functional_nonneg_of_mem_monoid {α : Dual ℂ H}
    (ha : α ∈ positiveRootMonoid H φ) : 0 ≤ φ α := by
  refine AddSubmonoid.closure_induction (fun x hx => ?_) (by simp)
    (fun x y _ _ hx hy => by simpa using add_nonneg hx hy) ha
  exact (show x ∈ _root_.LieAlgebrasAndRepresentations.HighestRoot.simpleRoots H φ from hx).1.2.le

private theorem positive_mem_monoid {α : Dual ℂ H} (ha : α ∈ _root_.LieAlgebrasAndRepresentations.HighestRoot.positiveRoots H φ)
    (hm : α ∈ positiveRootMonoid H φ ∨ -α ∈ positiveRootMonoid H φ) :
    α ∈ positiveRootMonoid H φ := by
  refine hm.resolve_right fun hn => ?_
  have h := functional_nonneg_of_mem_monoid H φ hn
  rw [map_neg, neg_nonneg] at h
  exact (not_lt_of_ge h) ha.2

include hsimple in
private theorem eval_positiveHeight {α : Dual ℂ H} (ha : α ∈ positiveRootMonoid H φ) :
    α (twiceCorootRho H φ) = 2 * (positiveHeight H φ α : ℂ) := by
  obtain ⟨l, hl⟩ := list_of_mem_positiveRootMonoid H φ ha
  rw [height_eq_length H φ hsimple hl, ← eval_list_simple H φ hsimple, hl]

omit [FiniteDimensional ℂ L] in
private theorem distinct_simple_root_difference_not_root
    (hφ : ∀ α ∈ rootSet_value H, φ α ≠ 0)
    (hneg : ∀ α ∈ rootSet_value H, -α ∈ rootSet_value H)
    (a b : _root_.LieAlgebrasAndRepresentations.HighestRoot.simpleRoots H φ) : a.val - b.val ∉ rootSet_value H := by
  intro hr
  rcases (hφ _ hr).lt_or_gt with hn | hp
  · have hn' : ¬ b.val = a.val + -(a.val - b.val) :=
      b.property.2 a.val a.property.1 _ ⟨hneg _ hr, by simpa using neg_pos.mpr hn⟩
    apply hn'
    abel
  · have hp' : ¬ a.val = b.val + (a.val - b.val) :=
      a.property.2 b.val b.property.1 _ ⟨hr, hp⟩
    apply hp'
    abel

private theorem simple_root_bracket (hp : ∀ α ∈ rootSet_value H, φ α ≠ 0)
    (hneg : ∀ α ∈ rootSet_value H, -α ∈ rootSet_value H)
    (d : SimpleTripleData H φ) (a b : _root_.LieAlgebrasAndRepresentations.HighestRoot.simpleRoots H φ) :
    ⁅d.e a, d.f b⁆ = if a = b then (coroot_value H a : L) else 0 := by
  split_ifs with hab
  · subst b
    exact (d.triple a).lie_e_f
  · have hbr := rootSpace_bracket H a.val (-b.val) _ _ (d.e_mem a) (d.f_mem b)
    rw [← sub_eq_add_neg, rootSpace_eq_bot_of_not_mem H _
        (sub_ne_zero.mpr (Subtype.coe_injective.ne hab))
        (distinct_simple_root_difference_not_root H φ hp hneg a b)] at hbr
    simpa using hbr

include hsimple in
private theorem principal_relations
    [Fintype (_root_.LieAlgebrasAndRepresentations.HighestRoot.simpleRoots H φ)] [Nonempty (_root_.LieAlgebrasAndRepresentations.HighestRoot.simpleRoots H φ)]
    (hp : ∀ α ∈ rootSet_value H, φ α ≠ 0)
    (hneg : ∀ α ∈ rootSet_value H, -α ∈ rootSet_value H)
    (d : SimpleTripleData H φ) :
    IsSl2Triple (twiceCorootRho H φ : L) (principalE H φ d) (principalF H φ d) := by
  let h := twiceCorootRho H φ
  have hne : h ≠ 0 := by
    obtain ⟨a⟩ := ‹Nonempty (_root_.LieAlgebrasAndRepresentations.HighestRoot.simpleRoots H φ)›
    have he := hsimple a
    change a.val h = 2 at he
    intro hz
    rw [hz, map_zero] at he
    norm_num at he
  have he (a : _root_.LieAlgebrasAndRepresentations.HighestRoot.simpleRoots H φ) : ⁅(h : L), d.e a⁆ = (2 : ℂ) • d.e a :=
    (mem_rootSpace H a.val (d.e a)).mp (d.e_mem a) h |>.trans (by rw [hsimple a])
  have hf (a : _root_.LieAlgebrasAndRepresentations.HighestRoot.simpleRoots H φ) : ⁅(h : L), d.f a⁆ = (-2 : ℂ) • d.f a :=
    (mem_rootSpace H (-a.val) (d.f a)).mp (d.f_mem a) h |>.trans
      (by rw [LinearMap.neg_apply, hsimple a])
  have hc := congrArg H.toSubmodule.subtype d.coroot_sum
  simp only [finsum_eq_sum_of_fintype, map_sum, map_smul, Submodule.subtype_apply] at hc
  refine ⟨fun hz => hne (Subtype.coe_injective hz), ?_, ?_, ?_⟩
  · rw [principalE, principalF, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, sum_lie]
    simp_rw [lie_sum, lie_smul, simple_root_bracket H φ hp hneg d]
    simpa [smul_ite, Finset.sum_ite_eq, eq_comm] using hc
  · rw [principalE, finsum_eq_sum_of_fintype, lie_sum, ← Nat.cast_smul_eq_nsmul ℂ, Finset.smul_sum]
    apply Finset.sum_congr rfl
    exact fun a _ => he a
  · rw [principalF, finsum_eq_sum_of_fintype, lie_sum, ← Nat.cast_smul_eq_nsmul ℂ, ← neg_smul,
      Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [lie_smul, show ⁅(twiceCorootRho H φ : L), d.f a⁆ = (-2 : ℂ) • d.f a from hf a,
      smul_comm (d.c a) (-2 : ℂ)]
    norm_num
end Triple

section Embedding
variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] {h e f : L}

private def tripleLinearMap (h e f : L) : Model ℂ →ₗ[ℂ] L where
  toFun x := x.val 0 1 • e + x.val 1 0 • f + x.val 0 0 • h
  map_add' x y := by
    change (x.val 0 1 + y.val 0 1) • e + (x.val 1 0 + y.val 1 0) • f +
      (x.val 0 0 + y.val 0 0) • h = _
    simp only [add_smul]
    abel
  map_smul' a x := by
    change (a * _) • e + (a * _) • f + (a * _) • h = _
    simp only [smul_add, mul_smul, RingHom.id_apply]

@[simp] private theorem tripleLinearMap_E : tripleLinearMap h e f (E ℂ) = e := by
  simp [tripleLinearMap, E, Matrix.single]

@[simp] private theorem tripleLinearMap_F : tripleLinearMap h e f (F ℂ) = f := by
  simp [tripleLinearMap, F, Matrix.single]

@[simp] private theorem tripleLinearMap_H : tripleLinearMap h e f (Specs.LieAlgebrasAndRepresentations.Sl2Model.H ℂ) = h := by
  simp [tripleLinearMap, Specs.LieAlgebrasAndRepresentations.Sl2Model.H, Matrix.single]

private def tripleEmbedding (t : IsSl2Triple h e f) : Model ℂ →ₗ⁅ℂ⁆ L where
  __ := tripleLinearMap h e f
  map_lie' {x y} := by
    have hem := (sl2_relations ℂ).1
    have hfm := (sl2_relations ℂ).2.1
    have hefm := (sl2_relations ℂ).2.2
    have he := t.lie_h_e_smul ℂ
    have hf : ⁅h, f⁆ = (-2 : ℂ) • f := by rw [t.lie_lie_smul_f ℂ, neg_smul]
    have ehm : ⁅E ℂ, Specs.LieAlgebrasAndRepresentations.Sl2Model.H ℂ⁆ = -((2 : ℂ) • E ℂ) := by rw [← lie_skew, hem]
    have fhm : ⁅F ℂ, Specs.LieAlgebrasAndRepresentations.Sl2Model.H ℂ⁆ = -((-2 : ℂ) • F ℂ) := by rw [← lie_skew, hfm]
    have fem : ⁅F ℂ, E ℂ⁆ = -Specs.LieAlgebrasAndRepresentations.Sl2Model.H ℂ := by rw [← lie_skew, hefm]
    have eh : ⁅e, h⁆ = -((2 : ℂ) • e) := by rw [← lie_skew, he]
    have fh : ⁅f, h⁆ = -((-2 : ℂ) • f) := by rw [← lie_skew, hf]
    have fe : ⁅f, e⁆ = -h := by rw [← lie_skew, t.lie_e_f]
    change tripleLinearMap h e f ⁅x, y⁆ =
      ⁅tripleLinearMap h e f x, tripleLinearMap h e f y⁆
    conv_lhs => rw [sl2_expansion ℂ x, sl2_expansion ℂ y]
    conv_rhs => rw [sl2_expansion ℂ x, sl2_expansion ℂ y]
    simp only [add_lie, lie_add, smul_lie, lie_smul, map_add, map_smul,
      sl2_e, sl2_f, sl2_h, lie_self, hem, hfm, hefm, ehm, fhm, fem,
      map_zero, map_neg, tripleLinearMap_E, tripleLinearMap_F, tripleLinearMap_H,
      he, hf, t.lie_e_f, eh, fh, fe]

private theorem tripleEmbedding_injective (t : IsSl2Triple h e f) :
    Injective (tripleEmbedding t) := by
  apply (LieHom.ker_eq_bot _).mp
  rcases sl2_ideal_eq_bot_or_top ℂ (tripleEmbedding t).ker with hb | ht
  · exact hb
  · have hm : Specs.LieAlgebrasAndRepresentations.Sl2Model.H ℂ ∈ (tripleEmbedding t).ker := by rw [ht]; trivial
    exact (t.h_ne_zero ((tripleLinearMap_H (h := h) (e := e) (f := f)).symm.trans hm)).elim
end Embedding


section Spectrum
variable {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {ι : Type*} [Fintype ι] (A : End ℂ M) (b : Basis ι ℂ M) (w : ι → ℤ)
variable (hw : ∀ i, A (b i) = (w i : ℂ) • b i)

include hw in
private theorem spectrum_card (p : ℤ → Prop) :
    Nat.card {i // p (w i)} =
      finrank ℂ ((⨆ z : {z // p z}, A.eigenspace (z.val : ℂ)) : Submodule ℂ M) := by
  let W := Submodule.span ℂ (range fun i : {i // p (w i)} => b i.val)
  have hspan : W = ⨆ z : {z // p z}, A.eigenspace (z.val : ℂ) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro - ⟨i, rfl⟩
      exact (le_iSup (fun z : {z // p z} => A.eigenspace (z.val : ℂ)) ⟨w i.val, i.property⟩)
        (End.mem_eigenspace_iff.mpr (hw i.val))
    · apply iSup_le
      rintro ⟨z, hz⟩ x hx
      have hAx := End.mem_eigenspace_iff.mp hx
      have hcoord : A x = ∑ j, ((b.repr x j) * (w j : ℂ)) • b j := by
        conv_lhs => rw [← b.sum_repr x]
        simp only [map_sum, map_smul, hw, smul_smul]
      have hc (j : ι) : ¬ p (w j) → b.repr x j = 0 := by
        intro hj
        have hzw : z ≠ w j := fun he => hj (he ▸ hz)
        have hEq := congrArg (fun v => b.repr v j) (hAx.symm.trans hcoord)
        simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, Basis.repr_sum_self] at hEq
        have hn : (z : ℂ) - (w j : ℂ) ≠ 0 :=
          sub_ne_zero.mpr (Int.cast_injective.ne hzw)
        apply (mul_eq_zero.mp ?_).resolve_left hn
        rw [sub_mul, mul_comm (w j : ℂ), hEq, sub_self]
      rw [← b.sum_repr x]
      apply Submodule.sum_mem
      intro j _
      by_cases hj : p (w j)
      · exact W.smul_mem _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
      · simp [hc j hj]
  rw [← hspan, Nat.card_eq_fintype_card]
  exact (finrank_span_eq_card (b.linearIndependent.comp _ Subtype.val_injective)).symm
end Spectrum

section RootSpectrum
variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
variable (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
  [H.IsCartanSubalgebra] [LieModule.IsTriangularizable ℂ H L] [LieAlgebra.IsKilling ℂ L]
variable (φ : Dual ℝ (Dual ℂ H)) (hφ : ∀ α ∈ rootSet_value H, φ α ≠ 0)

private def signedHeight (a : rootSet_value H) : ℤ :=
  (cartanBase H hH φ hφ).height ((adjointRootEquiv H hH).symm a)

private theorem signedHeight_ne_zero (a : rootSet_value H) :
    signedHeight H hH φ hφ a ≠ 0 := (cartanBase H hH φ hφ).height_ne_zero _

private theorem signedHeight_pos (a : rootSet_value H) :
    0 < signedHeight H hH φ hφ a ↔ a.val ∈ _root_.LieAlgebrasAndRepresentations.HighestRoot.positiveRoots H φ := by
  have ha : (P H).root ((adjointRootEquiv H hH).symm a) = a.val :=
    congrArg Subtype.val ((adjointRootEquiv H hH).apply_symm_apply a)
  simpa only [signedHeight, ← ha, RootPairing.Base.isPos_iff] using
    cartanBase_pos H hH φ hφ ((adjointRootEquiv H hH).symm a)

private theorem eval_signedHeight (hss : IsSemisimple ℂ L) (a : rootSet_value H) :
    a.val (twiceCorootRho H φ) = (2 : ℂ) * (signedHeight H hH φ hφ a : ℂ) := by
  let b := cartanBase H hH φ hφ
  let i := (adjointRootEquiv H hH).symm a
  have ha : (P H).root i = a.val := congrArg Subtype.val ((adjointRootEquiv H hH).apply_symm_apply a)
  obtain ⟨f, -, -, hf⟩ := b.exists_root_eq_sum_int i
  change a.val (twiceCorootRho H φ) = 2 * (b.height i : ℂ)
  rw [← ha, hf, b.height_eq_sum hf]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Int.cast_sum, zsmul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : (P H).root j (twiceCorootRho H φ) = 2 :=
    simple_eval_twiceCorootRho H hH φ hφ hss
      ⟨(P H).root j, (cartanBase_simple H hH φ hφ j).mp hj⟩
  rw [hj', mul_comm]

include hH hφ in
private theorem positiveRoot_mem_monoid {a : Dual ℂ H} (ha : a ∈ _root_.LieAlgebrasAndRepresentations.HighestRoot.positiveRoots H φ) :
    a ∈ positiveRootMonoid H φ := by
  obtain ⟨i, hi⟩ := (show a ∈ range (P H).root from (pairingRoot_range H hH).symm ▸ ha.1)
  exact positive_mem_monoid H φ ha (hi ▸ pos_or_neg_mem_monoid H hH φ hφ i)

private theorem signedHeight_eq_of_pos (hss : IsSemisimple ℂ L) (a : rootSet_value H)
    (ha : a.val ∈ _root_.LieAlgebrasAndRepresentations.HighestRoot.positiveRoots H φ) :
    signedHeight H hH φ hφ a = positiveHeight H φ a.val := by
  have h₁ := eval_signedHeight H hH φ hφ hss a
  have h₂ := eval_positiveHeight H φ (simple_eval_twiceCorootRho H hH φ hφ hss)
    (positiveRoot_mem_monoid H hH φ hφ ha)
  exact Int.cast_injective (α := ℂ) (by
    push_cast
    exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) (h₁.symm.trans h₂))

private abbrev rootBasisIndex (H : LieSubalgebra ℂ L) (i : Option (rootSet_value H)) : ℕ :=
  match i with
  | none => finrank ℂ H
  | some _ => 1

private def rootBasisIndexEquiv :
    (Σ i : Option (rootSet_value H), Fin (rootBasisIndex H i)) ≃
      Fin (finrank ℂ H) ⊕ rootSet_value H where
  toFun
    | ⟨none, k⟩ => .inl k
    | ⟨some a, _⟩ => .inr a
  invFun
    | .inl k => ⟨none, k⟩
    | .inr a => ⟨some a, 0⟩
  left_inv := by
    rintro ⟨_ | a, k⟩
    · rfl
    · change (⟨some a, 0⟩ : Σ i, Fin (rootBasisIndex H i)) = ⟨some a, k⟩
      rw [Subsingleton.elim k (0 : Fin 1)]
  right_inv := by rintro (k | a) <;> rfl

include hH in
private def rootBasis (hss : IsSemisimple ℂ L) :
    Basis (Fin (finrank ℂ H) ⊕ rootSet_value H) ℂ L := by
  let W := rootSummand_value H
  letI : DecidableEq (Option (rootSet_value H)) := Classical.decEq _
  have hin : DirectSum.IsInternal W := root_decomposition hss H hH
  let b (i : Option (rootSet_value H)) : Basis (Fin (rootBasisIndex H i)) ℂ (W i) := by
    cases i with
    | none => exact Module.finBasis ℂ (W none)
    | some a =>
      exact (Module.finBasis ℂ (W (some a))).reindex
        (finCongr (finrank_rootSpace_eq_one hss H hH a.val a.property))
  exact (hin.collectedBasis b).reindex (rootBasisIndexEquiv H)

private def rootBasisWeight : Fin (finrank ℂ H) ⊕ rootSet_value H → ℤ :=
  Sum.elim (fun _ => 0) (fun a => 2 * signedHeight H hH φ hφ a)

private theorem rootBasis_eigen (hss : IsSemisimple ℂ L)
    (i : Fin (finrank ℂ H) ⊕ rootSet_value H) :
    LieAlgebra.ad ℂ L (twiceCorootRho H φ : L) (rootBasis H hH hss i) =
      (rootBasisWeight H hH φ hφ i : ℂ) • rootBasis H hH hss i := by
  letI : DecidableEq (Option (rootSet_value H)) := Classical.decEq _
  let b := rootBasis H hH hss
  have hb : b i ∈ rootSummand_value H ((rootBasisIndexEquiv H).symm i).1 := by
    unfold b rootBasis
    rw [Basis.reindex_apply]
    exact DirectSum.IsInternal.collectedBasis_mem _ _ _
  cases i with
  | inl i =>
    change b (.inl i) ∈ H.toSubmodule at hb
    have h := (mem_rootSpace H (0 : Dual ℂ H) (b (.inl i))).mp
      (rootSpace_zero hss H hH ▸ hb) (twiceCorootRho H φ)
    simpa [rootBasisWeight] using h
  | inr a =>
    change b (.inr a) ∈ rootSpace_value H a.val at hb
    have h := (mem_rootSpace H a.val (b (.inr a))).mp hb (twiceCorootRho H φ)
    change ⁅(twiceCorootRho H φ : L), b (.inr a)⁆ =
      ((2 * signedHeight H hH φ hφ a : ℤ) : ℂ) • b (.inr a)
    simpa only [Int.cast_mul, Int.cast_ofNat, eval_signedHeight H hH φ hφ hss] using h


include hH hφ in
private theorem height_pos (hss : IsSemisimple ℂ L) {a : Dual ℂ H}
    (ha : a ∈ _root_.LieAlgebrasAndRepresentations.HighestRoot.positiveRoots H φ) : 0 < positiveHeight H φ a := by
  let i : rootSet_value H := ⟨a, ha.1⟩
  have hp := (signedHeight_pos H hH φ hφ i).mpr ha
  rw [signedHeight_eq_of_pos H hH φ hφ hss i ha] at hp
  exact_mod_cast hp

private theorem rootBasis_card_at (hss : IsSemisimple ℂ L) [Finite (rootSet_value H)]
    (n : ℕ) :
    Nat.card {i // rootBasisWeight H hH φ hφ i = 2 * (n : ℤ)} =
      heightCount H φ n := by
  rw [Nat.card_congr Equiv.subtypeSum, Nat.card_sum]
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero]
    have he : {k : Fin (finrank ℂ H) // rootBasisWeight H hH φ hφ (.inl k) = 2 * (0 : ℤ)} ≃
        Fin (finrank ℂ H) :=
      Equiv.subtypeUnivEquiv (fun _ => by simp [rootBasisWeight])
    haveI : IsEmpty {a : rootSet_value H // rootBasisWeight H hH φ hφ (.inr a) = 2 * (0 : ℤ)} :=
      ⟨fun ⟨a, ha⟩ => by
        have hne := signedHeight_ne_zero H hH φ hφ a
        change 2 * signedHeight H hH φ hφ a = 2 * (0 : ℤ) at ha
        omega⟩
    have hz : Nat.card {a : rootSet_value H // rootBasisWeight H hH φ hφ (.inr a) = 2 * (0 : ℤ)} = 0 :=
      Nat.card_eq_zero.mpr (Or.inl inferInstance)
    rw [Nat.card_congr he, hz, add_zero, heightCount, ite_eq_left rfl]
    exact Nat.card_fin _
  · haveI : IsEmpty {k : Fin (finrank ℂ H) // rootBasisWeight H hH φ hφ (.inl k) = 2 * (n : ℤ)} :=
      ⟨fun ⟨_, hk⟩ => by change (0 : ℤ) = 2 * (n : ℤ) at hk; omega⟩
    have hf (a : rootSet_value H) :
        rootBasisWeight H hH φ hφ (.inr a) = 2 * (n : ℤ) ↔
          a.val ∈ _root_.LieAlgebrasAndRepresentations.HighestRoot.positiveRoots H φ ∧ positiveHeight H φ a.val = n := by
      change 2 * signedHeight H hH φ hφ a = 2 * (n : ℤ) ↔ _
      constructor
      · intro he
        have hp : a.val ∈ _root_.LieAlgebrasAndRepresentations.HighestRoot.positiveRoots H φ :=
          (signedHeight_pos H hH φ hφ a).mp (by omega)
        have h := signedHeight_eq_of_pos H hH φ hφ hss a hp
        exact ⟨hp, by omega⟩
      · rintro ⟨hp, rfl⟩
        rw [signedHeight_eq_of_pos H hH φ hφ hss a hp]
    have he : {a : rootSet_value H // rootBasisWeight H hH φ hφ (.inr a) = 2 * (n : ℤ)} ≃
        {a ∈ _root_.LieAlgebrasAndRepresentations.HighestRoot.positiveRoots H φ | positiveHeight H φ a = n} :=
      { toFun := fun a => ⟨a.val.val, (hf a.val).mp a.property⟩
        invFun := fun a => ⟨⟨a.val, a.property.1.1⟩, (hf ⟨a.val, a.property.1.1⟩).mpr a.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hz : Nat.card {k : Fin (finrank ℂ H) // rootBasisWeight H hH φ hφ (.inl k) = 2 * (n : ℤ)} = 0 :=
      Nat.card_eq_zero.mpr (Or.inl inferInstance)
    rw [hz, zero_add, Nat.card_congr he, Nat.card_coe_set_eq, heightCount, ite_eq_right hn]

private theorem rootBasis_card_positive [Finite (rootSet_value H)] :
    Nat.card {i // 0 < rootBasisWeight H hH φ hφ i} = (_root_.LieAlgebrasAndRepresentations.HighestRoot.positiveRoots H φ).ncard := by
  haveI : IsEmpty {k : Fin (finrank ℂ H) // 0 < rootBasisWeight H hH φ hφ (.inl k)} :=
    ⟨fun ⟨_, hk⟩ => (lt_irrefl (0 : ℤ)) hk⟩
  have hf (a : rootSet_value H) :
      0 < rootBasisWeight H hH φ hφ (.inr a) ↔ a.val ∈ _root_.LieAlgebrasAndRepresentations.HighestRoot.positiveRoots H φ := by
    rw [← signedHeight_pos H hH φ hφ a]
    change 0 < 2 * signedHeight H hH φ hφ a ↔ _
    omega
  have he : {a : rootSet_value H // 0 < rootBasisWeight H hH φ hφ (.inr a)} ≃
      _root_.LieAlgebrasAndRepresentations.HighestRoot.positiveRoots H φ :=
    { toFun := fun a => ⟨a.val.val, (hf a.val).mp a.property⟩
      invFun := fun a => ⟨⟨a.val, a.property.1⟩, (hf ⟨a.val, a.property.1⟩).mpr a.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hz : Nat.card {k : Fin (finrank ℂ H) // 0 < rootBasisWeight H hH φ hφ (.inl k)} = 0 :=
    Nat.card_eq_zero.mpr (Or.inl inferInstance)
  rw [Nat.card_congr Equiv.subtypeSum, Nat.card_sum, Nat.card_congr he, hz, zero_add,
    Nat.card_coe_set_eq]

include hH hφ in
private theorem heightCount_one (hss : IsSemisimple ℂ L) :
    heightCount H φ 1 = finrank ℂ H := by
  let e := simple_eval_twiceCorootRho H hH φ hφ hss
  have hs : {a ∈ _root_.LieAlgebrasAndRepresentations.HighestRoot.positiveRoots H φ | positiveHeight H φ a = 1} = _root_.LieAlgebrasAndRepresentations.HighestRoot.simpleRoots H φ := by
    ext a
    constructor
    · rintro ⟨ha, hht⟩
      obtain ⟨l, hl⟩ := list_of_mem_positiveRootMonoid H φ
        (positiveRoot_mem_monoid H hH φ hφ ha)
      have hn := (height_eq_length H φ e hl).symm.trans hht
      obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp hn
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hl
      exact hl ▸ b.property
    · intro ha
      exact ⟨ha.1, height_eq_length H φ e (l := [⟨a, ha⟩]) (by simp)⟩
  rw [heightCount, ite_eq_right (by decide : (1 : ℕ) ≠ 0), hs, ← Nat.card_coe_set_eq,
    finrank_eq_nat_card_basis (simpleCorootBasis H hH φ hφ)]

include hH hφ in
private theorem highest_bounds_height (hss : IsSemisimple ℂ L) {θ a : Dual ℂ H}
    (hθ : θ ∈ _root_.LieAlgebrasAndRepresentations.HighestRoot.positiveRoots H φ) (ha : a ∈ _root_.LieAlgebrasAndRepresentations.HighestRoot.positiveRoots H φ)
    (hdom : θ - a ∈ positiveRootMonoid H φ) :
    positiveHeight H φ a ≤ positiveHeight H φ θ := by
  let e := simple_eval_twiceCorootRho H hH φ hφ hss
  have hv (b : Dual ℂ H) (hb : b ∈ _root_.LieAlgebrasAndRepresentations.HighestRoot.positiveRoots H φ) :=
    eval_positiveHeight H φ e (positiveRoot_mem_monoid H hH φ hφ hb)
  have hc := eval_positiveHeight H φ e hdom
  rw [LinearMap.sub_apply, hv θ hθ, hv a ha, ← mul_sub] at hc
  have he := mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) hc
  have he' : (positiveHeight H φ θ : ℤ) - (positiveHeight H φ a : ℤ) =
      (positiveHeight H φ (θ - a) : ℤ) := by exact_mod_cast he
  omega

end RootSpectrum


section ExponentCounts
variable {ι : Type*} [Fintype ι] (m : ι → ℕ)

omit [Fintype ι] in
private theorem standard_card_at (k : ℕ) :
    Nat.card {ij : Σ i, Fin (2 * m i + 1) // (2 : ℤ) * m ij.1 - 2 * ij.2.val = 2 * k} =
      Nat.card {i // k ≤ m i} := by
  apply Nat.card_congr
  refine Equiv.ofBijective (fun ij => ⟨ij.val.1, ?_⟩) ?_
  · have h := ij.property
    omega
  · constructor
    · rintro ⟨⟨i, j⟩, hj⟩ ⟨⟨i', j'⟩, hj'⟩ he
      have hi : i = i' := congrArg Subtype.val he
      subst i'
      apply Subtype.ext
      apply congrArg (Sigma.mk i)
      apply Fin.ext
      dsimp at hj hj'
      omega
    · intro i
      let j : Fin (2 * m i.val + 1) := ⟨m i.val - k, by have := i.property; omega⟩
      have hj : (2 : ℤ) * m i.val - 2 * j.val = 2 * k := by
        have := i.property
        dsimp [j]
        omega
      exact ⟨⟨⟨i.val, j⟩, hj⟩, Subtype.ext rfl⟩

private theorem standard_card_positive :
    Nat.card {ij : Σ i, Fin (2 * m i + 1) // 0 < (2 : ℤ) * m ij.1 - 2 * ij.2.val} =
      ∑ i, m i := by
  have e : {ij : Σ i, Fin (2 * m i + 1) // 0 < (2 : ℤ) * m ij.1 - 2 * ij.2.val} ≃
      Σ i, Fin (m i) :=
    { toFun := fun ⟨⟨i, j⟩, hj⟩ => ⟨i, ⟨j.val, by dsimp at hj; omega⟩⟩
      invFun := fun ⟨i, j⟩ =>
        ⟨⟨i, ⟨j.val, by have := j.isLt; omega⟩⟩, by have := j.isLt; dsimp; omega⟩
      left_inv := by rintro ⟨⟨i, j⟩, _⟩; rfl
      right_inv := by rintro ⟨i, j⟩; rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  simp

end ExponentCounts


section Decomposition
variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
variable (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
  [H.IsCartanSubalgebra] [LieModule.IsTriangularizable ℂ H L] [LieAlgebra.IsKilling ℂ L]
variable (φ : Dual ℝ (Dual ℂ H)) (hφ : ∀ α ∈ rootSet_value H, φ α ≠ 0)

include hH hφ in
private theorem principal_exponents (hss : IsSemisimple ℂ L)
    (j : Model ℂ →ₗ⁅ℂ⁆ L) (hj : j (sl2_h ℂ) = (twiceCorootRho H φ : L))
    (θ : Dual ℂ H) (hθ : θ ∈ _root_.LieAlgebrasAndRepresentations.HighestRoot.positiveRoots H φ)
    (hdom : ∀ β ∈ rootSet_value H, θ - β ∈ positiveRootMonoid H φ) :
    HasExponentDecomposition H φ j θ := by
  classical
  letI : LieRingModule (Model ℂ) L := LieRingModule.compLieHom L j
  letI : LieModule ℂ (Model ℂ) L := LieModule.compLieHom L j
  obtain ⟨S, hS, hsum, hstd⟩ := ClebschGordan.finite_standard_decomposition ℂ L
  letI : Fintype S := hS.fintype
  letI : Fintype (rootSet_value H) := (rootSet_finite H hH.1).fintype
  have hstd' (i : S) := hstd i.val i.property
  choose n b hb using hstd'
  let A : End ℂ L := LieAlgebra.ad ℂ L (twiceCorootRho H φ : L)
  let r := rootBasis H hH hss
  let w := rootBasisWeight H hH φ hφ
  have compare (d : S → ℕ) (c : ∀ i : S, Basis (Fin (d i + 1)) ℂ i.val)
      (hc : ∀ i, IsStandardBasis (c i)) (p : ℤ → Prop) :
      Nat.card {i // p (w i)} = Nat.card {ij : Σ i, Fin (d i + 1) //
        p ((d ij.1 : ℤ) - 2 * ij.2.val)} := by
    let q := hsum.collectedBasis c
    have hq (ij : Σ i, Fin (d i + 1)) :
        A (q ij) = (((d ij.1 : ℤ) - 2 * ij.2.val : ℤ) : ℂ) • q ij := by
      have he := congrArg Subtype.val (hc ij.1 ij.2).1
      change ⁅j (sl2_h ℂ), ((c ij.1 ij.2 : ij.1.val) : L)⁆ =
        ((d ij.1 : ℂ) - 2 * (ij.2.val : ℂ)) • ((c ij.1 ij.2 : ij.1.val) : L) at he
      rw [hj] at he
      change ⁅(twiceCorootRho H φ : L), q ij⁆ = _
      simpa only [q, DirectSum.IsInternal.collectedBasis_coe, Int.cast_sub, Int.cast_mul,
        Int.cast_ofNat, Int.cast_natCast] using he
    exact (spectrum_card A r w (rootBasis_eigen H hH φ hφ hss) p).trans
      (spectrum_card A q _ hq p).symm
  have heven (i : S) : ∃ m : ℕ, n i = 2 * m := by
    let p := fun z : ℤ => z = (n i : ℤ)
    have hP : Nonempty {ij : Σ i, Fin (n i + 1) // p ((n ij.1 : ℤ) - 2 * ij.2.val)} :=
      ⟨⟨⟨i, 0⟩, by simp [p]⟩⟩
    have hp := Nat.card_pos_iff.mpr ⟨hP, inferInstance⟩
    rw [← compare n b hb p] at hp
    obtain ⟨⟨k, hk⟩⟩ := (Nat.card_pos_iff.mp hp).1
    cases k with
    | inl k =>
      change (0 : ℤ) = (n i : ℤ) at hk
      exact ⟨0, by omega⟩
    | inr a =>
      change 2 * signedHeight H hH φ hφ a = (n i : ℤ) at hk
      exact ⟨(signedHeight H hH φ hφ a).toNat, by omega⟩
  choose m hm using heven
  have hs' (i : S) : ∃ c : Basis (Fin (2 * m i + 1)) ℂ i.val, IsStandardBasis c := by
    rw [← hm i]
    exact ⟨b i, hb i⟩
  choose c hc using hs'
  let T (k : ℕ) : Set S := {i | k ≤ m i}
  have hcount (k : ℕ) : heightCount H φ k = (T k).ncard := by
    rw [← rootBasis_card_at H hH φ hφ hss k]
    have he := compare (fun i => 2 * m i) c hc (· = 2 * (k : ℤ))
    push_cast at he
    exact he.trans (standard_card_at m k)
  have hzero : heightCount H φ 0 = Nat.card S := by
    rw [hcount, show T 0 = univ by ext i; exact ⟨fun _ => trivial, fun _ => Nat.zero_le _⟩]
    simp
  have hmult (k : ℕ) :
      heightCount H φ (k + 1) ≤ heightCount H φ k ∧
      Nat.card {i : S | m i = k} = heightCount H φ k - heightCount H φ (k + 1) := by
    have hsub : T (k + 1) ⊆ T k := fun i hi => Nat.le_trans (Nat.le_succ k) hi
    have he : {i : S | m i = k} = T k \ T (k + 1) := by
      ext i
      change m i = k ↔ k ≤ m i ∧ ¬ k + 1 ≤ m i
      omega
    rw [hcount, hcount]
    exact ⟨ncard_le_ncard hsub, by rw [Nat.card_coe_set_eq, he, ncard_sdiff hsub]⟩
  have hmpos (i : S) : 0 < m i := by
    by_contra! hh
    have he : m i = 0 := Nat.eq_zero_of_le_zero hh
    have hp : 0 < Nat.card {i : S | m i = 0} :=
      Nat.card_pos_iff.mpr ⟨⟨⟨i, he⟩⟩, inferInstance⟩
    rw [(hmult 0).2, heightCount_one H hH φ hφ hss, heightCount, ite_eq_left rfl, Nat.sub_self]
      at hp
    exact (lt_irrefl 0) hp
  have htotal : (∑ᶠ i : S, m i) = (_root_.LieAlgebrasAndRepresentations.HighestRoot.positiveRoots H φ).ncard := by
    rw [← rootBasis_card_positive H hH φ hφ, finsum_eq_sum_of_fintype]
    have he := compare (fun i => 2 * m i) c hc (0 < ·)
    push_cast at he
    exact (he.trans (standard_card_positive m)).symm
  have hmax (i : S) : m i ≤ positiveHeight H φ θ := by
    have hp : 0 < heightCount H φ (m i) := by
      rw [hcount, ← Nat.card_coe_set_eq]
      exact Nat.card_pos_iff.mpr ⟨⟨⟨i, show m i ≤ m i from le_rfl⟩⟩, inferInstance⟩
    simp only [heightCount, ite_eq_right (hmpos i).ne'] at hp
    obtain ⟨a, ha, he⟩ := nonempty_of_ncard_ne_zero hp.ne'
    rw [← he]
    exact highest_bounds_height H hH φ hφ hss hθ ha (hdom a ha.1)
  have htop : 0 < heightCount H φ (positiveHeight H φ θ) := by
    have hp := height_pos H hH φ hφ hss hθ
    rw [heightCount, ite_eq_right hp.ne']
    apply (ncard_pos ((rootSet_finite H hH.1).subset (fun _ ha => ha.1.1))).mpr
    exact ⟨θ, hθ, rfl⟩
  rw [hcount] at htop
  obtain ⟨i, hi⟩ := nonempty_of_ncard_ne_zero htop.ne'
  have hg : IsGreatest (range m) (positiveHeight H φ θ) :=
    ⟨⟨i, le_antisymm (hmax i) hi⟩, fun _ ⟨a, ha⟩ => ha ▸ hmax a⟩
  refine ⟨S, hS, hsum, m, ?_, fun i => ⟨hmpos i, c i, hc i⟩, hmult, htotal, hg, ?_⟩
  · simpa [heightCount] using hzero.symm
  · rw [coxeterNumber, hg.csSup_eq]

end Decomposition

/-- The principal triple and its adjoint exponent decomposition. -/
theorem principal_triple :
    Specs.LieAlgebrasAndRepresentations.PrincipalTriple.principal_triple_type.{u} := by
  intro L _ _ _ _ _ H hH φ hφ
  change IsMaximalToral H at hH
  have hss : IsSemisimple ℂ L := LieAlgebra.radical_eq_bot
  letI : H.IsCartanSubalgebra := maximalToral_isCartan hss H hH
  obtain ⟨θ, ⟨hθ, hdom⟩, _⟩ := highest_root H hH φ hφ
  letI : Fintype (_root_.LieAlgebrasAndRepresentations.HighestRoot.simpleRoots H φ) := ((rootSet_finite H hH.1).subset
    (fun _ ha => ha.1.1)).fintype
  have hn : Nonempty (_root_.LieAlgebrasAndRepresentations.HighestRoot.simpleRoots H φ) := by
    obtain ⟨l, hl⟩ := list_of_mem_positiveRootMonoid H φ
      (positiveRoot_mem_monoid H hH φ hφ hθ)
    cases l with
    | nil =>
      exfalso
      exact hθ.1.1 (by simpa using hl.symm)
    | cons a _ => exact ⟨a⟩
  have hneg (α : Dual ℂ H) (hα : α ∈ rootSet_value H) : -α ∈ rootSet_value H := by
    obtain ⟨i, rfl⟩ := (show α ∈ range (P H).root from (pairingRoot_range H hH).symm ▸ hα)
    have hi := pairingRoot_mem H hH ((P H).reflectionPerm i i)
    rwa [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self] at hi
  let b := simpleCorootBasis H hH φ hφ
  have he (a : _root_.LieAlgebrasAndRepresentations.HighestRoot.simpleRoots H φ) : ∃ e f : L, e ∈ rootSpace_value H a.val ∧
      f ∈ rootSpace_value H (-a.val) ∧ IsSl2Triple (coroot_value H a.val : L) e f := by
    obtain ⟨e, f, he, hf, he0, _, hef, hhe, hhf⟩ := exists_root_triple hss H hH a.val a.property.1.1
    refine ⟨e, f, he, hf, ⟨?_, hef, ?_, ?_⟩⟩
    · intro hz
      rw [show (killingCoroot H a.val : L) = 0 from hz, zero_lie] at hhe
      exact he0 ((smul_eq_zero.mp hhe.symm).resolve_left (by norm_num : (2 : ℂ) ≠ 0))
    · simpa only [two_smul] using hhe
    · simpa only [neg_smul, two_smul] using hhf
  choose e f hem hfm ht using he
  refine ⟨⟨⟨e, f, b.repr (twiceCorootRho H φ), hem, hfm, ht, ?_⟩⟩, ?_⟩
  · rw [finsum_eq_sum_of_fintype]
    simpa only [b, simpleCorootBasis_apply H hH φ hφ hss] using b.sum_repr (twiceCorootRho H φ)
  · intro d
    have t := principal_relations H φ (simple_eval_twiceCorootRho H hH φ hφ hss) hφ hneg d
    let j := tripleEmbedding t
    have hj : j (sl2_h ℂ) = (twiceCorootRho H φ : L) := tripleLinearMap_H
    exact ⟨t, j, tripleEmbedding_injective t, tripleLinearMap_E, hj, tripleLinearMap_F,
      θ, hθ, hdom, principal_exponents H hH φ hφ hss j hj θ hθ hdom⟩

/-- The regular vector determines the same positive and simple adjoint roots
as the functional used for the principal triple. -/
theorem principal_triple_regular_vector :
    Specs.LieAlgebrasAndRepresentations.PrincipalTriple.principal_triple_regular_vector_type.{u,v} := by
  intro L _ _ _ _ _ H hH V _ _ ι hι hR R w hw
  let φ : Dual ℝ (Dual ℂ H) := (innerₗ V w).comp ι.leftInverse
  have hφj (a : V) : φ (ι a) = inner ℝ w a := by
    change inner ℝ w (ι.leftInverse (ι a)) = _
    rw [LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hι)]
  have hφ (α : Dual ℂ H) (hα : α ∈ rootSet_value H) : φ α ≠ 0 := by
    obtain ⟨a, rfl⟩ := hR hα
    simpa only [hφj] using hw a hα
  have hpos (a : V) : a ∈ _root_.LieAlgebrasAndRepresentations.positiveRoots R w ↔
      ι a ∈ HighestRoot.positiveRoots H φ := by
    change (ι a ∈ rootSet_value H ∧ 0 < inner ℝ w a) ↔
      (ι a ∈ rootSet_value H ∧ 0 < φ (ι a))
    rw [hφj]
  have hpos_image : ι '' _root_.LieAlgebrasAndRepresentations.positiveRoots R w =
      HighestRoot.positiveRoots H φ := by
    ext α
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (hpos a).mp ha
    · intro hα
      obtain ⟨a, rfl⟩ := hR hα.1
      exact ⟨a, (hpos a).mpr hα, rfl⟩
  refine ⟨φ, hφj, hpos_image, ?_, principal_triple H hH φ hφ⟩
  ext α
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨(hpos a).mp ha.1, ?_⟩
    intro β hβ γ hγ hsum
    rw [← hpos_image] at hβ hγ
    obtain ⟨b, hb, rfl⟩ := hβ
    obtain ⟨c, hc, rfl⟩ := hγ
    exact ha.2 b hb c hc (hι (hsum.trans (map_add ι b c).symm))
  · intro hα
    obtain ⟨a, ha, rfl⟩ := hpos_image.symm ▸ hα.1
    refine ⟨a, ⟨ha, ?_⟩, rfl⟩
    intro b hb c hc hsum
    exact hα.2 _ ((hpos b).mp hb) _ ((hpos c).mp hc)
      ((congrArg ι hsum).trans (map_add ι b c))

end LieAlgebrasAndRepresentations.PrincipalTriple
