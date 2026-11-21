import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.Reconstruction
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SerreFiniteType
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SerreRelations
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootTriples
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleRoots
import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.LinearAlgebra.Isomorphisms
import Batteries.Tactic.OpenPrivate

noncomputable section
open Set Module
open Specs.LieAlgebrasAndRepresentations.SerreRelations (simple)
open Specs.LieAlgebrasAndRepresentations.Reconstruction
open LieAlgebrasAndRepresentations.Serre (Algebra RelationsHold)
open scoped BigOperators Classical

set_option backward.isDefEq.respectTransparency false

namespace LieAlgebrasAndRepresentations

universe u v
open private maximalToral_isCartan rootWeight rootWeight_nonzero rootWeight_toLinear
  coroot_rootWeight from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootTriples
open private rootSpace_eq_gen from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootDecomposition

namespace Reconstruction

section Pairing

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
variable (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
variable [H.IsCartanSubalgebra]

/-- Match the source's ordinary nonzero roots with the library root-pairing indices. -/
private def rootIndex : rootSet H ≃ H.root (K := ℂ) where
  toFun a := ⟨rootWeight H hH a.val a.property, by
    simpa using rootWeight_nonzero H hH a.val a.property⟩
  invFun a := ⟨(a.val : Dual ℂ H), by
    refine ⟨?_, ?_⟩
    · intro hz
      apply LieSubalgebra.isNonZero_coe_root a
      change (a.val : H → ℂ) = 0
      exact congrArg DFunLike.coe hz
    · intro hz
      exact a.val.genWeightSpace_ne_bot'
        (LieSubmodule.toSubmodule_injective
          ((rootSpace_eq_gen H hH.1 (a.val : Dual ℂ H)).symm.trans hz))⟩
  left_inv a := Subtype.ext (rootWeight_toLinear H hH a.val a.property)
  right_inv a := by
    apply Subtype.ext
    ext x
    rfl

variable [LieAlgebra.IsKilling ℂ L]

private abbrev liePairing := LieAlgebra.IsKilling.rootSystem (K := ℂ) (L := L) H

private theorem pairing_root_eq (a : rootSet H) :
    (liePairing H).root (rootIndex H hH a) = a.val :=
  rootWeight_toLinear H hH a.val a.property

private theorem pairing_coroot_eq (hss : IsSemisimple ℂ L)
    (a : rootSet H) :
    (liePairing H).coroot (rootIndex H hH a) = killingCoroot H a.val :=
  coroot_rootWeight hss H hH a.val a.property

end Pairing

section Realization

variable {ι M N : Type u} [Fintype ι] [AddCommGroup M] [Module ℂ M]
  [Module ℝ M] [IsScalarTower ℝ ℂ M] [AddCommGroup N] [Module ℂ N]
  [Module ℝ N] [IsScalarTower ℝ ℂ N]
variable (P : RootPairing ι ℂ M N) [P.IsRootSystem] [P.IsCrystallographic]

private abbrev RealSpan := P.rootSpan ℝ

omit [Fintype ι] [Module ℝ M] [IsScalarTower ℝ ℂ M] [Module ℝ N]
  [IsScalarTower ℝ ℂ N] [P.IsCrystallographic] in
private theorem eq_zero_of_coroot_eval {x : M} (hx : ∀ i, P.coroot' i x = 0) : x = 0 := by
  apply P.toPerfPair.injective
  rw [map_zero]
  ext y
  change P.toLinearMap x y = 0
  have hy : y ∈ Submodule.span ℂ (Set.range P.coroot) := by
    rw [RootPairing.IsRootSystem.span_coroot_eq_top]
    trivial
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact hx i
  | zero => simp
  | add y z _ _ hy hz => simp [hy, hz]
  | smul c y _ hy => simp [hy]

private local instance realValued : P.IsValuedIn ℝ where
  exists_value i j := ⟨(P.pairingIn ℤ i j : ℝ), by
    simpa [algebraMap_int_eq] using P.algebraMap_pairingIn ℤ i j⟩

omit [Module ℝ N] [IsScalarTower ℝ ℂ N] [P.IsRootSystem] in
private theorem root_form_real_apply (x y : RealSpan P) :
    P.RootFormIn ℝ x y = ∑ i, P.coroot'In ℝ i x * P.coroot'In ℝ i y := by
  simp [RootPairing.RootFormIn]

@[instance_reducible]
private def realSpanCore : InnerProductSpace.Core ℝ (RealSpan P) where
  inner x y := P.RootFormIn ℝ x y
  conj_inner_symm x y := by simpa using (LinearMap.isSymm_def.mp (P.rootFormIn_isSymm ℝ) y x)
  re_inner_nonneg x := by
    change 0 ≤ P.RootFormIn ℝ x x
    rw [root_form_real_apply]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  add_left x y z := by simp
  smul_left x y r := by simp
  definite x hx := by
    apply Subtype.ext
    apply eq_zero_of_coroot_eval P
    intro i
    have h : ∀ j : ι, P.coroot'In ℝ j x * P.coroot'In ℝ j x = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg _)).mp
        ((root_form_real_apply P x x).symm.trans hx) |> fun h j => h j (Finset.mem_univ j)
    rw [← P.algebraMap_coroot'In_apply ℝ i x, mul_self_eq_zero.mp (h i), map_zero]

private local instance realSpanNorm : NormedAddCommGroup (RealSpan P) :=
  (realSpanCore P).toNormedAddCommGroup

private local instance realSpanInner : InnerProductSpace ℝ (RealSpan P) :=
  InnerProductSpace.ofCore (realSpanCore P).toCore

private theorem rootCartan_realSpan (i : ι) (x : RealSpan P) :
    rootCartan x (P.rootSpanMem ℝ i) = P.coroot'In ℝ i x := by
  let a : RealSpan P := P.rootSpanMem ℝ i
  have ha : a ≠ 0 := fun hz => P.ne_zero i (congrArg Subtype.val hz)
  have hd : P.RootFormIn ℝ a a ≠ 0 := (realSpanCore P).definite a |>.mt ha
  apply (FaithfulSMul.algebraMap_injective ℝ ℂ)
  change algebraMap ℝ ℂ (2 * P.RootFormIn ℝ x a / P.RootFormIn ℝ a a) = _
  rw [map_div₀, map_mul, P.algebraMap_coroot'In_apply]
  apply (div_eq_iff ((map_ne_zero (algebraMap ℝ ℂ)).2 hd)).2
  have he := congrArg (P.toLinearMap (x : M)) (P.rootFormIn_self_smul_coroot ℝ i)
  change P.toLinearMap (x : M) (P.RootFormIn ℝ a a • P.coroot i) =
    P.toLinearMap (x : M) (2 • P.PolarizationIn ℝ a) at he
  rw [← algebraMap_smul ℂ, LinearMap.map_smul, two_nsmul, map_add,
    P.toLinearMap_apply_PolarizationIn] at he
  have hsymm : P.RootFormIn ℝ x a = P.RootFormIn ℝ a x := by
    simpa using LinearMap.isSymm_def.mp (P.rootFormIn_isSymm ℝ) x a
  rw [hsymm, map_ofNat]
  change 2 * _ = P.toLinearMap (x : M) (P.coroot i) * _
  rw [mul_comm (P.toLinearMap (x : M) (P.coroot i))]
  simpa only [smul_eq_mul, ← two_mul] using he.symm

private theorem realSpan_isRootSystem [P.IsReduced] :
    IsRootSystem (Set.range (P.rootSpanMem ℝ)) where
  finite := Set.finite_range _
  nonzero := by
    rintro _ ⟨i, rfl⟩ hz
    exact P.ne_zero i (congrArg Subtype.val hz)
  reflection_mem := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    refine ⟨P.reflectionPerm i j, ?_⟩
    change P.rootSpanMem ℝ (P.reflectionPerm i j) =
      P.rootSpanMem ℝ j - rootCartan (P.rootSpanMem ℝ j) (P.rootSpanMem ℝ i) •
        P.rootSpanMem ℝ i
    apply Subtype.ext
    change P.root (P.reflectionPerm i j) =
      P.root j - rootCartan (P.rootSpanMem ℝ j) (P.rootSpanMem ℝ i) • P.root i
    rw [rootCartan_realSpan, P.coroot'In_rootSpanMem_eq_pairingIn,
      P.root_reflectionPerm, P.reflection_apply_root' ℝ]
  integral := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    change ∃ z : ℤ, rootCartan (P.rootSpanMem ℝ j) (P.rootSpanMem ℝ i) = (z : ℝ)
    refine ⟨P.pairingIn ℤ j i, ?_⟩
    apply (FaithfulSMul.algebraMap_injective ℝ ℂ)
    rw [rootCartan_realSpan, P.algebraMap_coroot'In_apply, map_intCast]
    change P.pairing j i = (P.pairingIn ℤ j i : ℂ)
    simpa [algebraMap_int_eq] using (P.algebraMap_pairingIn ℤ j i).symm
  reduced := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hj
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hj
    have hroot : (algebraMap ℝ ℂ r) • P.root i = P.root j := by
      rw [algebraMap_smul]
      exact congrArg Subtype.val hr
    have hd : ¬ LinearIndependent ℂ ![(P.root i : M), P.root j] := by
      rw [LinearIndependent.pair_iff' (P.ne_zero i)]
      push Not
      exact ⟨_, hroot⟩
    rcases RootPairing.IsReduced.eq_or_eq_neg (P := P) i j hd with h | h
    · exact Or.inl (Subtype.ext h.symm)
    · exact Or.inr (Subtype.ext (neg_eq_iff_eq_neg.mp h.symm))
  span_eq_top := by
    apply top_unique
    intro x _
    obtain ⟨x, hx⟩ := x
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => exact Submodule.zero_mem _
    | add x y hx hy h₁ h₂ => exact Submodule.add_mem _ (h₁ trivial) (h₂ trivial)
    | smul c x hx h => exact Submodule.smul_mem _ _ (h trivial)

end Realization

section SingleAlgebra

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
variable (hss : IsSemisimple ℂ L) (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
include hss hH

private theorem span_normalized_coroots :
    Submodule.span ℂ (Set.range (fun a : rootSet H => killingCoroot H a.val)) = ⊤ := by
  let : LieAlgebra.HasTrivialRadical ℂ L := ⟨hss⟩
  let : H.IsCartanSubalgebra := maximalToral_isCartan hss H hH
  have hr : Set.range (fun a : rootSet H => killingCoroot H a.val) =
      Set.range (liePairing H).coroot := by
    rw [← (rootIndex H hH).surjective.range_comp]
    congr 1
    funext a
    exact (pairing_coroot_eq H hH hss a).symm
  rw [hr, RootPairing.IsRootSystem.span_coroot_eq_top]

private theorem span_ordinary_roots :
    Submodule.span ℂ (Set.range (fun a : rootSet H => a.val)) = ⊤ := by
  let : LieAlgebra.HasTrivialRadical ℂ L := ⟨hss⟩
  let : H.IsCartanSubalgebra := maximalToral_isCartan hss H hH
  have hr : Set.range (fun a : rootSet H => a.val) = Set.range (liePairing H).root := by
    rw [← (rootIndex H hH).surjective.range_comp]
    congr 1
  rw [hr, RootPairing.IsRootSystem.span_root_eq_top]

private theorem cartan_eq_of_root_eval {x y : H} (h : ∀ a : rootSet H, a.val x = a.val y) :
    x = y := by
  apply Module.eval_apply_injective ℂ
  ext a
  change a x = a y
  have ha : a ∈ Submodule.span ℂ (Set.range (fun b : rootSet H => b.val)) := by
    rw [span_ordinary_roots hss H hH]
    trivial
  induction ha using Submodule.span_induction with
  | mem a ha => obtain ⟨b, rfl⟩ := ha; exact h b
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb]
  | smul c a _ ha => simp [ha]

private theorem rank_eq_rank_cartan_add_card_roots :
    Module.finrank ℂ L = Module.finrank ℂ H + Nat.card (rootSet H) := by
  classical
  let : Fintype (rootSet H) := (rootSet_finite H hH.1).fintype
  let : DecidableEq (Option (rootSet H)) := Classical.decEq _
  let s := rootSummand H
  let g := LinearEquiv.ofBijective (DirectSum.coeLinearMap s) (root_decomposition hss H hH)
  rw [← g.finrank_eq, Module.finrank_directSum, Fintype.sum_option]
  change Module.finrank ℂ H + ∑ a : rootSet H, Module.finrank ℂ (rootSpace H a.val) = _
  simp only [finrank_rootSpace_eq_one hss H hH _ (Subtype.property _),
    Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, Nat.card_eq_fintype_card]

private theorem finite_serre_of_cartan_entries
    (p : Dual ℂ H →ₗ[ℝ] ℝ) (hp : ∀ a ∈ rootSet H, p a ≠ 0)
    (A : Matrix (simple H p) (simple H p) ℤ)
    (hA : ∀ i j, j.val (killingCoroot H i.val) = (A i j : ℂ)) :
    Module.Finite ℂ (Algebra A) ∧ Module.finrank ℂ (Algebra A) = Module.finrank ℂ L ∧
      Serre.weightSpace A 0 = Serre.cartan A := by
  classical
  let : LieAlgebra.HasTrivialRadical ℂ L := ⟨hss⟩
  let : H.IsCartanSubalgebra := maximalToral_isCartan hss H hH
  let : Fintype (simple H p) :=
    ((rootSet_finite H hH.1).subset fun _ hi => hi.1.1).fintype
  let P := liePairing H
  let := realValued P
  let := realSpanNorm P
  let := realSpanInner P
  let j (a : rootSet H) : RealSpan P := P.rootSpanMem ℝ (rootIndex H hH a)
  have hj (a : rootSet H) : (j a : Dual ℂ H) = a.val :=
    pairing_root_eq H hH a
  let R := Set.range (P.rootSpanMem ℝ)
  have hR : IsRootSystem R := realSpan_isRootSystem P
  have hrange (x : RealSpan P) : x ∈ R ↔ (x : Dual ℂ H) ∈ rootSet H := by
    constructor
    · rintro ⟨i, rfl⟩
      let a := (rootIndex H hH).symm i
      have ha : (j a : Dual ℂ H) = P.root i := by
        change P.root (rootIndex H hH a) = P.root i
        rw [Equiv.apply_symm_apply]
      exact (ha.symm.trans (hj a)).symm ▸ a.property
    · intro hx
      exact ⟨rootIndex H hH ⟨x.val, hx⟩, Subtype.ext (hj ⟨x.val, hx⟩)⟩
  let : FiniteDimensional ℝ (RealSpan P) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range P.root)
  let pR : RealSpan P →ₗ[ℝ] ℝ := p.comp (RealSpan P).subtype
  let z : RealSpan P := (InnerProductSpace.toDual ℝ (RealSpan P)).symm pR.toContinuousLinearMap
  have hz_eval (x : RealSpan P) : inner ℝ z x = p x.val :=
    InnerProductSpace.toDual_symm_apply
  have hz : RootRegular R z := fun x hx => (hz_eval x) ▸ hp x.val ((hrange x).mp hx)
  have hpos (x : RealSpan P) :
      x ∈ positiveRoots R z ↔ x.val ∈ Specs.LieAlgebrasAndRepresentations.SerreRelations.positive H p := by
    change (x ∈ R ∧ 0 < inner ℝ z x) ↔ (x.val ∈ rootSet H ∧ 0 < p x.val)
    rw [hrange, hz_eval]
  have hsimp (x : RealSpan P) : x ∈ simpleRoots R z ↔ x.val ∈ simple H p := by
    constructor
    · rintro ⟨hx, hd⟩
      refine ⟨(hpos x).mp hx, ?_⟩
      intro a ha b hb hab
      let a' := j ⟨a, ha.1⟩
      let b' := j ⟨b, hb.1⟩
      have ha' : a'.val = a := hj _
      have hb' : b'.val = b := hj _
      exact hd a' ((hpos a').mpr (ha'.symm ▸ ha))
        b' ((hpos b').mpr (hb'.symm ▸ hb)) (Subtype.ext (by
          change x.val = a'.val + b'.val
          rwa [ha', hb']))
    · rintro ⟨hx, hd⟩
      refine ⟨(hpos x).mpr hx, ?_⟩
      intro a ha b hb hab
      exact hd a.val ((hpos a).mp ha) b.val ((hpos b).mp hb) (congrArg Subtype.val hab)
  let ξ : simple H p ≃ simpleRoots R z :=
    { toFun := fun i => ⟨j ⟨i.val, i.property.1.1⟩,
        (hsimp _).mpr ((hj ⟨i.val, i.property.1.1⟩).symm ▸ i.property)⟩
      invFun := fun i => ⟨i.val.val, (hsimp i.val).mp i.property⟩
      left_inv := fun i => Subtype.ext (hj ⟨i.val, i.property.1.1⟩)
      right_inv := fun i => Subtype.ext (Subtype.ext (hj ⟨i.val.val,
        (hrange i.val).mp i.property.1.1⟩)) }
  obtain ⟨b₀, hb₀⟩ := simpleRoots_basis R hR z hz
  let b := b₀.reindex ξ.symm
  have hb (i : simple H p) : b i = j ⟨i.val, i.property.1.1⟩ := by
    rw [Module.Basis.reindex_apply, hb₀]
    rfl
  have hbS : IsSimpleBasis R z b := by
    unfold IsSimpleBasis
    have hfun : (b : simple H p → RealSpan P) = Subtype.val ∘ ξ := funext hb
    rw [hfun, ξ.surjective.range_comp, Subtype.range_coe]
  have hA' (i j' : simple H p) : (A i j' : ℝ) = cartanMatrix b i j' := by
    apply (FaithfulSMul.algebraMap_injective ℝ ℂ)
    rw [map_intCast, ← hA i j']
    change j'.val (killingCoroot H i.val) = algebraMap ℝ ℂ (rootCartan (b j') (b i))
    rw [hb i, hb j', rootCartan_realSpan, P.algebraMap_coroot'In_apply]
    change j'.val (killingCoroot H i.val) = (j ⟨j'.val, j'.property.1.1⟩ : Dual ℂ H)
      (P.coroot (rootIndex H hH ⟨i.val, i.property.1.1⟩))
    rw [hj, pairing_coroot_eq H hH hss]
  obtain ⟨hfinite, _, _, _, hzero, _, hdim⟩ :=
    Serre.finiteType_spec R hR z hz b hbS A hA'
  refine ⟨hfinite, ?_, hzero⟩
  have he : rootSet H ≃ R := Equiv.ofBijective
    (fun a => ⟨j a, Set.mem_range_self (rootIndex H hH a)⟩) (by
      constructor
      · intro a c hac
        apply Subtype.ext
        rw [← hj a, ← hj c]
        exact congrArg (fun x : R => x.val.val) hac
      · rintro ⟨x, i, rfl⟩
        refine ⟨(rootIndex H hH).symm i, Subtype.ext (Subtype.ext ?_)⟩
        change P.root (rootIndex H hH ((rootIndex H hH).symm i)) = P.root i
        rw [Equiv.apply_symm_apply])
  rw [hdim, rank_eq_rank_cartan_add_card_roots hss H hH, ← Nat.card_congr he,
    ← Module.finrank_eq_card_basis b, P.finrank_rootSpanIn ℝ, Subspace.dual_finrank_eq]

end SingleAlgebra


section Presentation

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

private theorem serre_presentation_data
    (hss : IsSemisimple ℂ L) (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    (p : Dual ℂ H →ₗ[ℝ] ℝ) (hp : ∀ a ∈ rootSet H, p a ≠ 0)
    (E F : simple H p → L) (hn : NormalizedSimpleVectors H p E F)
    {ι : Type v} [DecidableEq ι] (t : ι ≃ simple H p) :
    ∃ A : Matrix ι ι ℤ,
      (∀ i j, (t j).val (killingCoroot H (t i).val) = (A i j : ℂ)) ∧
      (∀ i j, i ≠ j → A i j ≤ 0) ∧
      RelationsHold A (E ∘ t) (F ∘ t) (fun i => (killingCoroot H (t i).val : L)) ∧
      LieSubalgebra.lieSpan ℂ L (Set.range (E ∘ t) ∪ Set.range (F ∘ t) ∪
        Set.range (fun i => (killingCoroot H (t i).val : L))) = ⊤ := by
  obtain ⟨A, hA, hbr, hserre, hgen⟩ := serre_relations hss H hH p hp E F hn
  refine ⟨fun i j => A (t i) (t j), fun i j => hA (t i) (t j),
    fun i j hij => (hserre (t i) (t j) (t.injective.ne hij)).1, ?_, ?_⟩
  · refine ⟨fun i j => (hbr (t i) (t j)).1, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j
      simpa only [Function.comp_apply, killingCoroot, Int.cast_smul_eq_zsmul] using (hbr (t i) (t j)).2.1
    · intro i j
      simpa only [Function.comp_apply, killingCoroot, neg_smul, Int.cast_smul_eq_zsmul] using (hbr (t i) (t j)).2.2.1
    · intro i j
      simpa only [Function.comp_apply, killingCoroot, t.injective.eq_iff] using (hbr (t i) (t j)).2.2.2
    · intro i j hij
      rw [Serre.iterBracket_eq_pow]
      exact (hserre (t i) (t j) (t.injective.ne hij)).2.1
    · intro i j hij
      rw [Serre.iterBracket_eq_pow]
      exact (hserre (t i) (t j) (t.injective.ne hij)).2.2
  · change LieSubalgebra.lieSpan ℂ L (Set.range (E ∘ t) ∪ Set.range (F ∘ t) ∪
      Set.range ((fun i : simple H p => (killingCoroot H i.val : L)) ∘ t)) = ⊤
    simpa only [t.surjective.range_comp] using hgen

/-- Equal dimensions turn the presentation map associated to generating
triples into a Lie equivalence. -/
private theorem serre_equiv_of_generators {ι : Type v} [DecidableEq ι]
    (A : Matrix ι ι ℤ) [Module.Finite ℂ (Algebra A)]
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (E F T : ι → L) (hr : RelationsHold A E F T)
    (hgen : LieSubalgebra.lieSpan ℂ L (Set.range E ∪ Set.range F ∪ Set.range T) = ⊤)
    (hdim : Module.finrank ℂ (Algebra A) = Module.finrank ℂ L) :
    ∃ g : Algebra A ≃ₗ⁅ℂ⁆ L, ∀ i,
      g (Serre.e A i) = E i ∧ g (Serre.f A i) = F i ∧ g (Serre.h A i) = T i := by
  let g := Serre.lift A hoff E F T hr
  have hrange : g.range = ⊤ := by
    apply top_unique
    rw [← hgen, LieSubalgebra.lieSpan_le]
    rintro x ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    · exact ⟨Serre.e A i, Serre.lift_e A hoff E F T hr i⟩
    · exact ⟨Serre.f A i, Serre.lift_f A hoff E F T hr i⟩
    · exact ⟨Serre.h A i, Serre.lift_h A hoff E F T hr i⟩
  have hsurj : Function.Surjective (g : Algebra A → L) :=
    LinearMap.range_eq_top.mp (show LinearMap.range g.toLinearMap = ⊤ from
      congrArg LieSubalgebra.toSubmodule hrange)
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := g.toLinearMap)).mpr hsurj
  exact ⟨LieEquiv.ofBijective g ⟨hinj, hsurj⟩, fun i =>
    ⟨Serre.lift_e A hoff E F T hr i, Serre.lift_f A hoff E F T hr i,
      Serre.lift_h A hoff E F T hr i⟩⟩

omit [FiniteDimensional ℂ L] in
private theorem serre_cartan_image {ι : Type u} [DecidableEq ι] {A : Matrix ι ι ℤ}
    (g : Algebra A ≃ₗ⁅ℂ⁆ L) (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    (T : ι → H) (hg : ∀ i, g (Serre.h A i) = (T i : L))
    (hzero : Serre.weightSpace A 0 = Serre.cartan A) :
    (Serre.cartan A).map g.toLinearEquiv.toLinearMap = H.toSubmodule := by
  apply le_antisymm
  · rw [Serre.cartan, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    change g (Serre.h A i) ∈ H.toSubmodule
    rw [hg]
    exact (T i).property
  · intro x hx
    refine ⟨g.symm x, ?_, g.apply_symm_apply x⟩
    rw [← hzero]
    intro i
    simp only [Pi.zero_apply, zero_smul]
    apply g.injective
    change g ⁅Serre.h A i, g.symm x⁆ = g 0
    rw [LieEquiv.map_lie, hg, g.apply_symm_apply, map_zero]
    let : IsLieAbelian H := hH.1.1
    exact congrArg (fun z : H => (z : L)) (trivial_lie_zero H H (T i) ⟨x, hx⟩)

end Presentation

end Reconstruction

open Reconstruction

/-- The Serre quotient presents the given algebra on any normalized choice of
simple-root triples. Its Cartan span maps onto the fixed Cartan. -/
theorem serre_reconstruction : serre_reconstruction_type.{u} := by
  intro L _ _ _ hss H hH p hp E F hn
  obtain ⟨A, hA, hoff, hr, hgen⟩ :=
    serre_presentation_data hss H hH p hp E F hn (Equiv.refl (simple H p))
  obtain ⟨hfinite, hdim, hzero⟩ := finite_serre_of_cartan_entries hss H hH p hp A hA
  let := hfinite
  obtain ⟨g, hg⟩ := serre_equiv_of_generators A hoff _ _ _ hr hgen hdim
  exact ⟨A, g, hA, hg, serre_cartan_image g H hH _
    (fun i => (hg i).2.2) hzero⟩

namespace Reconstruction

section CartanIsomorphism

variable {L : Type u} {M : Type v} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  [LieRing M] [LieAlgebra ℂ M] [FiniteDimensional ℂ M]
variable (hss : IsSemisimple ℂ L) (hss' : IsSemisimple ℂ M)
variable (H : LieSubalgebra ℂ L) (K : LieSubalgebra ℂ M)
variable (hH : IsMaximalToral H) (hK : IsMaximalToral K)
include hss hss' hH hK

private theorem cartan_isomorphism_of_pairings
    (σ : rootSet H ≃ rootSet K)
    (hσ : ∀ a b, (σ b).val (killingCoroot K (σ a).val) = b.val (killingCoroot H a.val)) :
    ∃ c : H ≃ₗ[ℂ] K, (∀ a : rootSet H, ∀ x : H, (σ a).val (c x) = a.val x) ∧
      ∀ a : rootSet H, c (killingCoroot H a.val) = killingCoroot K (σ a).val := by
  let S := Finsupp.linearCombination ℂ (fun a : rootSet H => killingCoroot H a.val)
  let T := Finsupp.linearCombination ℂ (fun a : rootSet H => killingCoroot K (σ a).val)
  have hS : Function.Surjective S := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact span_normalized_coroots hss H hH
  have hT : Function.Surjective T := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    change Submodule.span ℂ (Set.range ((fun a : rootSet K => killingCoroot K a.val) ∘ σ)) = ⊤
    rw [σ.surjective.range_comp]
    exact span_normalized_coroots hss' K hK
  have hpair (w : rootSet H →₀ ℂ) (a : rootSet H) :
      (σ a).val (T w) = a.val (S w) := by
    simp only [S, T, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, hσ]
  have hker : S.ker ≤ T.ker := by
    intro w hw
    rw [LinearMap.mem_ker] at hw ⊢
    apply cartan_eq_of_root_eval hss' K hK
    intro a
    obtain ⟨b, rfl⟩ := σ.surjective a
    rw [hpair, hw, map_zero, map_zero]
  let c := S.liftOfSurjective hS ⟨T, hker⟩
  have hc (w : rootSet H →₀ ℂ) : c (S w) = T w :=
    LinearMap.equivOfSurjective_apply hS hker
  have h_eval (a : rootSet H) (x : H) : (σ a).val (c x) = a.val x := by
    obtain ⟨w, rfl⟩ := hS x
    rw [hc, hpair]
  have hc_inj : Function.Injective c := by
    intro x y hxy
    apply cartan_eq_of_root_eval hss H hH
    intro a
    rw [← h_eval a x, ← h_eval a y, hxy]
  have hc_surj : Function.Surjective c := by
    intro y
    obtain ⟨w, rfl⟩ := hT y
    exact ⟨S w, hc w⟩
  refine ⟨LinearEquiv.ofBijective c ⟨hc_inj, hc_surj⟩, h_eval, ?_⟩
  intro a
  apply cartan_eq_of_root_eval hss' K hK
  intro b
  obtain ⟨b, rfl⟩ := σ.surjective b
  exact (h_eval b _).trans (hσ a b).symm

omit hss hss' hH hK [FiniteDimensional ℂ L] [FiniteDimensional ℂ M] in
private theorem transport_simple_roots
    (σ : rootSet H ≃ rootSet K)
    (c : H ≃ₗ[ℂ] K) (hc : ∀ a : rootSet H, ∀ x : H, (σ a).val (c x) = a.val x)
    (p : Dual ℂ H →ₗ[ℝ] ℝ) (hp : ∀ a ∈ rootSet H, p a ≠ 0) :
    ∃ (q : Dual ℂ K →ₗ[ℝ] ℝ) (s : simple H p ≃ simple K q),
      (∀ a ∈ rootSet K, q a ≠ 0) ∧
      (∀ i, (s i).val = (σ ⟨i.val, i.property.1.1⟩).val) := by
  let d := c.dualMap.symm
  let q := p.comp (c.dualMap.toLinearMap.restrictScalars ℝ)
  have hq (a : Dual ℂ H) : q (d a) = p a := by
    change p (c.dualMap (c.dualMap.symm a)) = p a
    rw [LinearEquiv.apply_symm_apply]
  have hd (a : rootSet H) : d a.val = (σ a).val := by
    apply c.dualMap.injective
    change c.dualMap (c.dualMap.symm a.val) = c.dualMap (σ a).val
    rw [LinearEquiv.apply_symm_apply]
    ext x
    exact (hc a x).symm
  have hr (a : Dual ℂ H) : a ∈ rootSet H ↔ d a ∈ rootSet K := by
    constructor
    · intro ha
      rw [hd ⟨a, ha⟩]
      exact (σ ⟨a, ha⟩).property
    · intro ha
      obtain ⟨b, hb⟩ := σ.surjective ⟨d a, ha⟩
      have hab := d.injective ((hd b).trans (congrArg Subtype.val hb))
      exact hab ▸ b.property
  have hpos (a : Dual ℂ H) :
      a ∈ Specs.LieAlgebrasAndRepresentations.SerreRelations.positive H p ↔
        d a ∈ Specs.LieAlgebrasAndRepresentations.SerreRelations.positive K q := by
    change (a ∈ rootSet H ∧ 0 < p a) ↔ (d a ∈ rootSet K ∧ 0 < q (d a))
    rw [← hr, hq]
  have hs (a : Dual ℂ H) : a ∈ simple H p ↔ d a ∈ simple K q := by
    constructor
    · rintro ⟨ha, hs⟩
      refine ⟨(hpos a).mp ha, ?_⟩
      intro b hb e he heq
      obtain ⟨b, rfl⟩ := d.surjective b
      obtain ⟨e, rfl⟩ := d.surjective e
      rw [← map_add] at heq
      exact hs b ((hpos b).mpr hb) e ((hpos e).mpr he) (d.injective heq)
    · rintro ⟨ha, hs⟩
      refine ⟨(hpos a).mpr ha, ?_⟩
      intro b hb e he heq
      exact hs (d b) ((hpos b).mp hb) (d e) ((hpos e).mp he) (by rw [heq, map_add])
  refine ⟨q, Equiv.subtypeEquiv d.toEquiv hs, ?_, fun i => hd ⟨i.val, i.property.1.1⟩⟩
  intro a ha
  obtain ⟨b, rfl⟩ := d.surjective a
  rw [hq]
  exact hp b ((hr b).mpr ha)

end CartanIsomorphism

section Choices

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

private theorem exists_regular_cartan_functional (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H) :
    ∃ p : Dual ℂ H →ₗ[ℝ] ℝ, ∀ a ∈ rootSet H, p a ≠ 0 := by
  let : Finite (rootSet H) := rootSet_finite H hH.1
  let ev (a : rootSet H) : H →ₗ[ℝ] ℝ := Complex.reLm.comp (a.val.restrictScalars ℝ)
  have hk (a : rootSet H) : (ev a).ker ≠ ⊤ := by
    obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp a.property.1
    have hx' : a.val x ≠ 0 := hx
    intro h
    have hz : (a.val x)⁻¹ • x ∈ (ev a).ker := by rw [h]; trivial
    rw [LinearMap.mem_ker] at hz
    change (a.val ((a.val x)⁻¹ • x)).re = 0 at hz
    simp [hx'] at hz
  obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top (fun a => (ev a).ker) hk
  refine ⟨Complex.reLm.comp ((Module.Dual.eval ℂ H x).restrictScalars ℝ), ?_⟩
  intro a ha h
  exact hx ⟨a, ha⟩ h

private theorem exists_normalized_simple_vectors (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H) (p : Dual ℂ H →ₗ[ℝ] ℝ) :
    ∃ E F : simple H p → L, NormalizedSimpleVectors H p E F := by
  have ht (i : simple H p) := exists_root_triple hss H hH i.val i.property.1.1
  choose E F he hf he0 hf0 hbr _ _ using ht
  exact ⟨E, F, fun i => ⟨he i, hf i, he0 i, hf0 i, hbr i⟩⟩

private theorem span_simple_coroots_of_cartan_image
    (H : LieSubalgebra ℂ L) (p : Dual ℂ H →ₗ[ℝ] ℝ)
    {A : Matrix (simple H p) (simple H p) ℤ} (g : Algebra A ≃ₗ⁅ℂ⁆ L)
    (hg : ∀ i, g (Serre.h A i) = (killingCoroot H i.val : L))
    (hc : (Serre.cartan A).map g.toLinearEquiv.toLinearMap = H.toSubmodule) :
    Submodule.span ℂ (Set.range (fun i : simple H p => killingCoroot H i.val)) = ⊤ := by
  apply top_unique
  intro x _
  have hx : (x : L) ∈ H.toSubmodule := x.property
  rw [← hc, Serre.cartan, Submodule.map_span] at hx
  have he : g.toLinearEquiv.toLinearMap '' Set.range (Serre.h A) =
      H.subtype '' Set.range (fun i : simple H p => killingCoroot H i.val) := by
    rw [← Set.range_comp, ← Set.range_comp]
    exact congrArg Set.range (funext hg)
  rw [he, ← Submodule.map_span] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  exact (Subtype.ext hxy : y = x) ▸ hy

end Choices
end Reconstruction

/-- A pairing-preserving bijection of the roots lifts to a Lie equivalence
between the original algebras and induces the designated bijection on roots. -/
theorem root_system_reconstruction : root_system_reconstruction_type.{u, v} := by
  intro L M _ _ _ _ _ _ hss hss' H K hH hK σ hσ
  obtain ⟨c, hc, hc_coroot⟩ := cartan_isomorphism_of_pairings hss hss' H K hH hK σ hσ
  obtain ⟨p, hp⟩ := exists_regular_cartan_functional H hH
  obtain ⟨q, s, hq, hs⟩ := transport_simple_roots H K σ c hc p hp
  obtain ⟨E, F, hEF⟩ := exists_normalized_simple_vectors hss H hH p
  obtain ⟨E', F', hEF'⟩ := exists_normalized_simple_vectors hss' K hK q
  obtain ⟨A, g₁, hA, hg₁, hcartan⟩ :=
    serre_reconstruction hss H hH p hp E F hEF
  -- Use the first algebra's simple roots to index the presentation in the target.
  obtain ⟨A', hA', hoff, hr, hgen⟩ :=
    serre_presentation_data hss' K hK q hq E' F' hEF' s
  have hAeq : A = A' := by
    funext i j
    apply Int.cast_injective (α := ℂ)
    rw [← hA i j, ← hA' i j, hs i, hs j]
    exact (hσ ⟨i.val, i.property.1.1⟩ ⟨j.val, j.property.1.1⟩).symm
  subst A'
  let : Module.Finite ℂ (Algebra A) := Module.Finite.equiv g₁.symm.toLinearEquiv
  have hd : Module.finrank ℂ L = Module.finrank ℂ M := by
    rw [rank_eq_rank_cartan_add_card_roots hss H hH,
      rank_eq_rank_cartan_add_card_roots hss' K hK, c.finrank_eq, Nat.card_congr σ]
  obtain ⟨g₂, hg₂⟩ := serre_equiv_of_generators A hoff _ _ _ hr hgen (g₁.toLinearEquiv.finrank_eq.trans hd)
  let g := g₁.symm.trans g₂
  have htriple (i : simple H p) :
      g (E i) = E' (s i) ∧ g (F i) = F' (s i) ∧
        g (killingCoroot H i.val : L) = (killingCoroot K (s i).val : M) := by
    obtain ⟨he, hf, hh⟩ := hg₁ i
    rw [← he, ← hf, ← hh]
    simpa only [g, LieEquiv.trans_apply, LieEquiv.symm_apply_apply, Function.comp_apply] using hg₂ i
  refine ⟨p, q, s, E, F, E', F', c, g, hp, hq, hs, hEF, hEF', hc, ?_, htriple⟩
  intro x
  have hx : x ∈ Submodule.span ℂ (Set.range (fun i : simple H p => killingCoroot H i.val)) := by
    rw [span_simple_coroots_of_cartan_image H p g₁ (fun i => (hg₁ i).2.2) hcartan]
    trivial
  let l : H →ₗ[ℂ] M := g.toLinearEquiv.toLinearMap.comp H.subtype
  let r : H →ₗ[ℂ] M := K.subtype.comp c.toLinearMap
  change l x = r x
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    change g (killingCoroot H i.val : L) = (c (killingCoroot H i.val) : M)
    rw [(htriple i).2.2, hs i, hc_coroot ⟨i.val, i.property.1.1⟩]
  | zero => simp
  | add y z _ _ hy hz => simp [hy, hz]
  | smul a y _ hy => simp [hy]

end LieAlgebrasAndRepresentations
