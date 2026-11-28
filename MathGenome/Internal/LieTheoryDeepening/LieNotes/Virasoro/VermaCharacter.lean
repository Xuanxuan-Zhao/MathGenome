import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Virasoro.VermaCharacter
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Virasoro.VermaModules
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.WeightExtraction
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.Data.Multiset.Sort
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

noncomputable section

namespace LieNotes.Virasoro.VermaCharacter

open VermaSpec VermaCharacterSpec PowerSeries
open scoped PowerSeries.WithPiTopology

universe u

private def wordPartition (d : ℕ) (w : {w : Word // wordDegree w = d}) :
    Nat.Partition d where
  parts := ↑(w.val.val.map Nat.succ)
  parts_pos := by
    simp only [Multiset.mem_coe, List.mem_map]
    rintro i ⟨j, -, rfl⟩
    exact Nat.succ_pos j
  parts_sum := w.property

/-- Add one to the zero-based indices of the ordered word to get its multiset of parts. -/
private def degreeWordsEquivPartitions (d : ℕ) :
    {w : Word // wordDegree w = d} ≃ Nat.Partition d :=
  Equiv.ofBijective (wordPartition d) <| by
    constructor
    · intro a b hab
      have hp : (a.val.val.map Nat.succ).Perm (b.val.val.map Nat.succ) :=
        Multiset.coe_eq_coe.mp (congrArg Nat.Partition.parts hab)
      have hs : a.val.val.map Nat.succ = b.val.val.map Nat.succ :=
        hp.eq_of_pairwise' (a.val.property.map _ fun _ _ => Nat.succ_le_succ)
          (b.val.property.map _ fun _ _ => Nat.succ_le_succ)
      have he := congrArg (List.map Nat.pred) hs
      apply Subtype.ext
      apply Subtype.ext
      have hcomp : Nat.pred ∘ Nat.succ = id := funext Nat.pred_succ
      simpa only [List.map_map, hcomp, List.map_id] using he
    · intro p
      let l := p.parts.sort (· ≤ ·)
      have hl : (↑l : Multiset ℕ) = p.parts := Multiset.sort_eq _ _
      have hm : (l.map Nat.pred).map Nat.succ = l := by
        rw [List.map_map]
        calc
          _ = l.map id := List.map_congr_left fun i hi => Nat.succ_pred_eq_of_pos
            (p.parts_pos (hl ▸ Multiset.mem_coe.mpr hi))
          _ = l := List.map_id _
      let w : Word := ⟨l.map Nat.pred,
        (Multiset.pairwise_sort _ _).map _ fun _ _ hij => Nat.pred_le_pred hij⟩
      have hd : wordDegree w = d := by
        change ((l.map Nat.pred).map Nat.succ).sum = d
        rw [hm]
        exact (congrArg Multiset.sum hl).trans p.parts_sum
      refine ⟨⟨w, hd⟩, Nat.Partition.ext ?_⟩
      change (↑((l.map Nat.pred).map Nat.succ) : Multiset ℕ) = p.parts
      rw [hm, hl]

theorem eulerFactorInverse : EulerFactorInverse := by
  intro i
  exact WithPiTopology.one_sub_mul_tsum_pow_of_constantCoeff_eq_zero (by simp)

private theorem eulerProduct : HasProd eulerFactor (Nat.Partition.genFun (fun _ _ => (1 : ℤ))) := by
  convert Nat.Partition.hasProd_genFun (fun _ _ => (1 : ℤ)) using 1
  funext i
  have hzero : (X ^ (i + 1) : PowerSeries ℤ).constantCoeff = 0 := by simp
  unfold eulerFactor
  rw [(WithPiTopology.summable_pow_of_constantCoeff_eq_zero hzero).tsum_eq_zero_add]
  congr 1
  apply tsum_congr
  intro j
  change ((X ^ (i + 1) : PowerSeries ℤ) ^ (j + 1)) =
    (1 : ℤ) • (X ^ ((i + 1) * (j + 1)) : PowerSeries ℤ)
  rw [one_smul, ← pow_mul]

private theorem coeff_eulerProduct {f : PowerSeries ℤ} (hf : HasProd eulerFactor f)
    (d : ℕ) (s : Finset ℕ) (hs : Finset.range d ⊆ s) :
    coeff d f = coeff d (∏ i ∈ s, eulerFactor i) := by
  have hstable (t : Finset ℕ) (ht : Finset.range d ⊆ t) :
      coeff d (∏ i ∈ t, eulerFactor i) =
        coeff d (∏ i ∈ Finset.range d, eulerFactor i) := by
    have hinv : (∏ i ∈ t \ Finset.range d, (1 - X ^ (i + 1) : PowerSeries ℤ)) *
        (∏ i ∈ t, eulerFactor i) = ∏ i ∈ Finset.range d, eulerFactor i := by
      have hfactor (i : ℕ) : (1 - X ^ (i + 1)) * eulerFactor i = 1 := eulerFactorInverse i
      rw [← Finset.prod_sdiff ht, ← mul_assoc, ← Finset.prod_mul_distrib]
      simp only [hfactor, Finset.prod_const_one, one_mul]
    have horder (i : ℕ) (hi : i ∈ t \ Finset.range d) :
        (d : ℕ∞) < (X ^ (i + 1) : PowerSeries ℤ).order := by
      have hle : d ≤ i := Nat.le_of_not_lt ((Finset.mem_sdiff.mp hi).2 ∘ Finset.mem_range.mpr)
      rw [order_X_pow]
      exact_mod_cast Nat.lt_succ_of_le hle
    calc
      _ = coeff d ((∏ i ∈ t, eulerFactor i) *
          ∏ i ∈ t \ Finset.range d, (1 - X ^ (i + 1) : PowerSeries ℤ)) :=
        (coeff_mul_prod_one_sub_of_lt_order d (t \ Finset.range d) _
          (fun i => X ^ (i + 1)) horder).symm
      _ = _ := by rw [mul_comm, hinv]
  have hf' := (WithPiTopology.continuous_coeff ℤ d).continuousAt.tendsto.comp hf
  have hc := tendsto_atTop_of_eventually_const hstable
  exact (tendsto_nhds_unique hf' hc).trans (hstable s hs).symm

section
variable [LieRing V] [LieAlgebra ℂ V]

private theorem degreeBasis (D : InducingData) (H : ModelProperties.{u} D)
    (c h : ℂ) (d : ℕ) :
    ∃ b : Module.Basis (Nat.Partition d) ℂ (D.degree c h d),
      ∀ p, (b p : D.Verma c h) =
        D.applyWord c h ((degreeWordsEquivPartitions d).symm p).val.val := by
  obtain ⟨b, hb⟩ := H.orderedBasis c h
  let e := degreeWordsEquivPartitions d
  let v : Nat.Partition d → D.Verma c h := fun p => b (e.symm p).val
  have hi : LinearIndependent ℂ v :=
    b.linearIndependent.comp _ (Subtype.val_injective.comp e.symm.injective)
  have hs : Submodule.span ℂ (Set.range v) = D.degree c h d := by
    rw [H.degree_span]
    congr 1
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨(e.symm p).val, congrArg Int.ofNat (e.symm p).property, hb _⟩
    · rintro ⟨w, hw, rfl⟩
      have hd : wordDegree w = d := by exact_mod_cast hw
      refine ⟨e ⟨w, hd⟩, ?_⟩
      dsimp only [v]
      rw [e.symm_apply_apply, hb]
  refine ⟨(Module.Basis.span hi).map (LinearEquiv.ofEq _ _ hs), ?_⟩
  intro p
  simpa only [Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply, Module.Basis.coe_span_apply, v]
    using hb (e.symm p).val

theorem hasCharacter (D : InducingData) (H : ModelProperties.{u} D) (c h : ℂ) :
    HasCharacter D c h := by
  have hd (d : ℕ) := degreeBasis D H c h d
  refine ⟨fun d => ⟨degreeWordsEquivPartitions d, fun _ => rfl, hd d⟩, ?_, ?_⟩
  · intro d
    obtain ⟨b, -⟩ := hd d
    exact Module.Finite.of_basis b
  · have he : gradedDimension D c h = Nat.Partition.genFun (fun _ _ => (1 : ℤ)) := by
      ext d
      obtain ⟨b, -⟩ := hd d
      simp [gradedDimension, Module.finrank_eq_card_basis b, Finsupp.prod]
    have hp : HasProd eulerFactor (gradedDimension D c h) := he ▸ eulerProduct
    exact ⟨hp, coeff_eulerProduct hp⟩

open LieNotes.Contragredient in
private theorem properSum (D : InducingData) (H : ModelProperties.{u} D) (c h : ℂ) :
    ∃ N : LieSubmodule ℂ V (D.Verma c h), N ≠ ⊤ ∧
      ∀ P : LieSubmodule ℂ V (D.Verma c h), P ≠ ⊤ → P ≤ N := by
  classical
  let T := LieModule.toEnd ℂ V (D.Verma c h) (VirasoroSpec.mode 0)
  let μ (d : ℕ) : Module.Dual ℂ ℂ :=
    LinearMap.toSpanSingleton ℂ ℂ (h + (d : ℂ))
  have hμ : Function.Injective μ := by
    intro d e he
    have hval : h + (d : ℂ) = h + (e : ℂ) := by
      simpa [μ] using DFunLike.congr_fun he (1 : ℂ)
    exact_mod_cast add_left_cancel hval
  have hweight (d : ℕ) :
      weightSpace (singleOperatorFamily T) (μ d) = D.degree c h d := by
    rw [weightSpace_singleOperatorFamily]
    simp [T, μ, InducingData.degree]
  obtain ⟨b, hb⟩ := H.orderedBasis c h
  have hspan : (⨆ d : ℕ, D.degree c h d) = ⊤ := by
    rw [eq_top_iff, ← b.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    rw [hb]
    exact (le_iSup (fun d : ℕ => D.degree c h d) (wordDegree w)) (H.word_weight c h w)
  have hsplit (P : LieSubmodule ℂ V (D.Verma c h)) :
      (⨆ d : ℕ, P.toSubmodule ⊓ D.degree c h d) = P.toSubmodule := by
    have hstable (z : ℂ) ⦃x : D.Verma c h⦄ (hx : x ∈ P.toSubmodule) :
        singleOperatorFamily T z x ∈ P.toSubmodule := by
      change z • ⁅VirasoroSpec.mode 0, x⁆ ∈ P.toSubmodule
      exact P.toSubmodule.smul_mem _ (P.lie_mem hx)
    have ht : (⨆ d, weightSpace (singleOperatorFamily T) (μ d)) = ⊤ := by
      simpa only [hweight] using hspan
    simpa only [hweight] using iSup_inf_weightSpace_eq
      (singleOperatorFamily T) P.toSubmodule hstable μ hμ ht
  let empty := Shared.Lie.PBW.emptyWord ℕ
  let coord := b.coord empty
  have htop : coord (D.top c h) = 1 := by
    have he : b empty = D.top c h := hb empty
    rw [← he]
    simp [coord, Module.Basis.coord_apply, Module.Basis.repr_self]
  have hker (P : LieSubmodule ℂ V (D.Verma c h)) (hP : P ≠ ⊤) :
      P.toSubmodule ≤ LinearMap.ker coord := by
    rw [← hsplit P]
    apply iSup_le
    intro d
    by_cases hd : d = 0
    · subst d
      rw [Nat.cast_zero, H.degree_zero]
      rintro x ⟨hxP, hxspan⟩
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hxspan
      have ha : a = 0 := by
        by_contra hne
        have ht : D.top c h ∈ P := by
          have hm := P.toSubmodule.smul_mem a⁻¹ hxP
          simpa [smul_smul, hne] using hm
        apply hP
        rw [eq_top_iff, ← H.cyclic c h]
        exact LieSubmodule.lieSpan_le.mpr (Set.singleton_subset_iff.mpr ht)
      simp [ha]
    · refine inf_le_right.trans ?_
      rw [H.degree_span]
      apply Submodule.span_le.mpr
      rintro _ ⟨w, hw, rfl⟩
      have hn : empty ≠ w := by
        rintro rfl
        have hz : (wordDegree empty : ℤ) = 0 := rfl
        exact hd (by omega)
      change D.applyWord c h w.val ∈ LinearMap.ker coord
      rw [← hb w, LinearMap.mem_ker]
      simp [coord, Module.Basis.coord_apply, Module.Basis.repr_self, hn]
  let S := {P : LieSubmodule ℂ V (D.Verma c h) // P ≠ ⊤}
  let N : LieSubmodule ℂ V (D.Verma c h) := ⨆ P : S, P.val
  have hN : N.toSubmodule ≤ LinearMap.ker coord := by
    change (⨆ P : S, P.val).toSubmodule ≤ _
    rw [LieSubmodule.iSup_toSubmodule]
    exact iSup_le fun P => hker P.val P.property
  refine ⟨N, ?_, fun P hP => le_iSup (fun Q : S => Q.val) ⟨P, hP⟩⟩
  intro he
  have hm : D.top c h ∈ N.toSubmodule := by
    rw [he]
    trivial
  have hz := LinearMap.mem_ker.mp (hN hm)
  rw [htop] at hz
  exact one_ne_zero hz

theorem hasUniqueSimpleQuotient (D : InducingData) (H : ModelProperties.{u} D) (c h : ℂ) :
    HasUniqueSimpleQuotient.{u} D c h := by
  classical
  obtain ⟨N, hN, hmax⟩ := properSum D H c h
  let π := LieSubmodule.Quotient.mk' N
  have hπ : Function.Surjective π := LieSubmodule.Quotient.surjective_mk' N
  refine ⟨N, hN, hmax, ?_, ?_⟩
  · have hne : (⊥ : LieSubmodule ℂ V (D.Verma c h ⧸ N)) ≠ ⊤ := by
      intro he
      apply hN
      rw [eq_top_iff]
      intro x _
      apply (LieSubmodule.Quotient.mk_eq_zero N).mp
      apply (LieSubmodule.mem_bot (R := ℂ) (L := V) (π x)).mp
      rw [he]
      trivial
    let := nontrivial_of_ne _ _ hne
    constructor
    intro P
    by_cases hP : P = ⊤
    · exact Or.inr hP
    left
    have hproper : P.comap π ≠ ⊤ := by
      intro he
      apply hP
      rw [eq_top_iff]
      rintro y -
      obtain ⟨x, rfl⟩ := hπ y
      change x ∈ P.comap π
      rw [he]
      trivial
    apply bot_unique
    intro y hy
    obtain ⟨x, rfl⟩ := hπ y
    exact (LieSubmodule.mem_bot (R := ℂ) (L := V) (π x)).mpr <|
      (LieSubmodule.Quotient.mk_eq_zero N).mpr (hmax _ hproper hy)
  · intro Q _ _ _ _ hsimple f hf
    let := hsimple
    have hproper : f.ker ≠ ⊤ := by
      intro he
      have hbot : (⊥ : LieSubmodule ℂ V Q) = ⊤ := by
        apply top_unique
        rintro y -
        obtain ⟨x, rfl⟩ := hf y
        apply (LieSubmodule.mem_bot (R := ℂ) (L := V) (f x)).mpr
        apply LieModuleHom.mem_ker.mp
        rw [he]
        trivial
      exact bot_ne_top hbot
    have hker : f.ker = N := by
      have hle := hmax _ hproper
      apply le_antisymm hle
      rcases hsimple.eq_bot_or_eq_top (N.map f) with himage | himage
      · exact (LieModuleHom.le_ker_iff_map N).mpr himage
      · exfalso
        apply hN
        rw [eq_top_iff]
        rintro x -
        have hx : f x ∈ N.map f := by rw [himage]; trivial
        obtain ⟨y, hy, he⟩ := (LieSubmodule.mem_map _).mp hx
        have hd : x - y ∈ f.ker := by
          exact LieModuleHom.mem_ker.mpr (by rw [map_sub, he, sub_self])
        simpa using N.add_mem (hle hd) hy
    let fl : D.Verma c h →ₗ[ℂ] Q := f
    have hk : N.toSubmodule = fl.ker := congrArg LieSubmodule.toSubmodule hker.symm
    let eLinear : (D.Verma c h ⧸ N) ≃ₗ[ℂ] Q :=
      (Submodule.quotEquivOfEq _ _ hk).trans (fl.quotKerEquivOfSurjective hf)
    have he (x : D.Verma c h) : eLinear (π x) = f x := by
      change eLinear (Submodule.Quotient.mk x) = fl x
      rw [show eLinear = _ from rfl, LinearEquiv.trans_apply,
        Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
    let e : (D.Verma c h ⧸ N) ≃ₗ⁅ℂ,V⁆ Q :=
      { eLinear with
        map_lie' := by
          intro z y
          obtain ⟨x, rfl⟩ := hπ y
          change eLinear ⁅z, π x⁆ = ⁅z, eLinear (π x)⁆
          rw [← LieModuleHom.map_lie, he, he, LieModuleHom.map_lie] }
    refine ⟨hker, e, he, ?_⟩
    intro g hg
    ext y
    obtain ⟨x, rfl⟩ := hπ y
    exact (hg x).trans (he x).symm

end

theorem characterModelExists : CharacterModelExists.{u} := by
  obtain ⟨r, a, hadd, hsmul, hbr, D, H⟩ := Verma.modelExists.{u}
  exact ⟨r, a, hadd, hsmul, hbr, D, H, fun c h =>
    ⟨hasCharacter D H c h, hasUniqueSimpleQuotient D H c h⟩⟩

end LieNotes.Virasoro.VermaCharacter
