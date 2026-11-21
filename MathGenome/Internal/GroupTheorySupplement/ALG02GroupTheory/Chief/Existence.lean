import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Chief.Series
import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Chief.Existence
import Mathlib.Data.Fintype.Powerset
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Order.OrderIsoNat

/-! Existence and the minimal normal criterion for chief series. -/

namespace ALG02GroupTheory.Chief

open Specs.ALG02GroupTheory.Chief.Existence

universe u

/-- Minimal nontrivial normality in the ambient group. -/
abbrev IsMinimalNormal : IsMinimalNormalType.{u} := isMinimalNormalValue

/-- The finite poset of ambient normal subgroups has a saturated chain
from the trivial subgroup to the full group. -/
theorem chiefSeries_exists (G : Type u) [Group G] [Finite G] : Nonempty (ChiefSeries G) := by
  let P := {H : Subgroup G // H.Normal}
  let : Finite P := Finite.of_injective (fun H : P => (H.1 : Set G))
    (SetLike.coe_injective.comp Subtype.val_injective)
  let bottom : P := ⟨⊥, inferInstance⟩
  let top : P := ⟨⊤, inferInstance⟩
  have h : bottom ≤ top := show (⊥ : Subgroup G) ≤ ⊤ from bot_le
  obtain ⟨a, hFirst, r, hLast, hStep⟩ :=
    exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le h
  refine ⟨⟨r, fun i => (a i).1, congrArg Subtype.val hFirst, congrArg Subtype.val hLast,
    fun i => (a i).2, fun i => ?_⟩⟩
  have cover := hStep i i.isLt
  exact ⟨cover.1, fun M hM hLower hUpper => cover.2 (c := ⟨M, hM⟩) hLower hUpper⟩

/-- The first isomorphism theorem for the restriction of the quotient
projection to the upper subgroup. -/
theorem factor_equiv_quotient_image {G : Type u} [Group G] (K L : Subgroup G)
    [K.Normal] (_ : K ≤ L) :
    ∃ e : Factor K L ≃* L.map (QuotientGroup.mk' K),
      ∀ x : L, (e (factorMk K L x) : G ⧸ K) = QuotientGroup.mk' K (x : G) := by
  let f := (QuotientGroup.mk' K).comp L.subtype
  have hker : f.ker = K.subgroupOf L := by
    change ((QuotientGroup.mk' K).comp L.subtype).ker = _
    simp only [← MonoidHom.comap_ker, QuotientGroup.ker_mk', Subgroup.subgroupOf]
  have hrange : f.range = L.map (QuotientGroup.mk' K) := by
    change ((QuotientGroup.mk' K).comp L.subtype).range = _
    rw [MonoidHom.range_comp, L.range_subtype]
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange f)).trans (MulEquiv.subgroupCongr hrange), fun _ => rfl⟩

/-- Quotient correspondence identifies ambient normal cover steps above `K`
with minimal nontrivial normal subgroups in `G ⧸ K`. -/
theorem ambientCovBy_iff_minimalNormal {G : Type u} [Group G] (K L : Subgroup G)
    [K.Normal] [L.Normal] (hKL : K < L) :
    AmbientCovBy K L ↔ IsMinimalNormal (L.map (QuotientGroup.mk' K)) := by
  let π := QuotientGroup.mk' K
  let e := QuotientGroup.comapMk'OrderIso K
  have hBot : (e ⊥).val = K := QuotientGroup.ker_mk' K
  have hImage : (e (L.map π)).val = L := by
    change (L.map π).comap π = L
    rw [QuotientGroup.comap_map_mk', sup_eq_right.mpr hKL.le]
  have hlt {A B : Subgroup (G ⧸ K)} : (e A).val < (e B).val ↔ A < B := e.lt_iff_lt
  change AmbientCovBy K L ↔ IsMinimalNormal (L.map π)
  constructor
  · rintro ⟨_, hCover⟩
    refine ⟨inferInstanceAs (L.map (QuotientGroup.mk' K)).Normal,
      hlt.mp (by simpa only [hBot, hImage] using hKL), ?_⟩
    intro M hM hNontrivial hLe
    by_contra hNe
    have hLower := hlt.mpr hNontrivial
    have hUpper := hlt.mpr (lt_of_le_of_ne hLe hNe)
    rw [hBot] at hLower
    rw [hImage] at hUpper
    exact hCover (M.comap π) (hM.comap π) hLower hUpper
  · rintro ⟨_, _, hMinimal⟩
    refine ⟨hKL, fun M hM hLower hUpper => ?_⟩
    have hMiddle : (e (M.map π)).val = M := by
      change (M.map π).comap π = M
      rw [QuotientGroup.comap_map_mk', sup_eq_right.mpr hLower.le]
    have hLower' : ⊥ < M.map π := hlt.mp (by simpa only [hBot, hMiddle] using hLower)
    have hUpper' : M.map π < L.map π := hlt.mp (by simpa only [hMiddle, hImage] using hUpper)
    exact hUpper'.ne (hMinimal _ (hM.map π (QuotientGroup.mk'_surjective K)) hLower' hUpper'.le)

/-- A strictly increasing chain of ambient normal subgroups from bottom to
top is chief precisely when each quotient image is minimal normal. -/
theorem chief_iff_minimalNormal (G : Type u) [Group G] [Finite G]
    (r : ℕ) (N : Fin (r + 1) → Subgroup G) (hFirst : N 0 = ⊥) (hLast : N (Fin.last r) = ⊤)
    (hNormal : ∀ i, (N i).Normal) (hStrict : StrictMono N) :
    IsChiefSeries r N ↔ ∀ i : Fin r,
      letI := hNormal i.castSucc
      IsMinimalNormal ((N i.succ).map (QuotientGroup.mk' (N i.castSucc))) := by
  have step (i : Fin r) :=
    letI := hNormal i.castSucc
    letI := hNormal i.succ
    ambientCovBy_iff_minimalNormal _ _ (hStrict (Fin.castSucc_lt_succ (i := i)))
  exact ⟨fun h i => (step i).mp (h.2.2.2 i),
    fun h => ⟨hFirst, hLast, hNormal, fun i => (step i).mpr (h i)⟩⟩

end ALG02GroupTheory.Chief
