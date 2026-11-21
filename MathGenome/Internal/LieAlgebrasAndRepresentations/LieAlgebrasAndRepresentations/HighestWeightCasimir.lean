import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.HighestWeightCasimir
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ModuleCasimir
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RealRootSpace
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SerreRelations
import Batteries.Tactic.OpenPrivate

/-! The quadratic Casimir for an arbitrary nondegenerate invariant form, and its
action on cyclic highest-weight modules. -/

noncomputable section

namespace LieAlgebrasAndRepresentations.HighestWeightCasimir

open Specs.LieAlgebrasAndRepresentations.HighestWeightCasimir
open Specs.LieAlgebrasAndRepresentations.VermaModules (Direction Regular positive_value)
open Module
open UniversalEnvelopingAlgebra (ι)
open scoped BigOperators Classical

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v i j

abbrev casimir := @casimir_value
abbrev weightRepresentative := @weightRepresentative_value
abbrev weightForm := @weightForm_value
abbrev rho := @rho_value
abbrev eigenvalue := @eigenvalue_value

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

private def productMap : L →ₗ[ℂ] L →ₗ[ℂ] UniversalEnvelopingAlgebra ℂ L :=
  ((LinearMap.mul ℂ (UniversalEnvelopingAlgebra ℂ L)).compl₁₂
    (ι ℂ (L := L)).toLinearMap (ι ℂ (L := L)).toLinearMap)

theorem basis_independent : basis_independent_type.{u,i,j} := by
  intro L _ _ B hB I J _ _ b c
  classical
  let d := B.dualBasis hB b
  let e := B.dualBasis hB c
  change ∑ k, productMap (b k) (d k) = ∑ l, productMap (c l) (e l)
  calc
    _ = ∑ k, ∑ l, B (e l) (b k) • productMap (c l) (d k) := by
      apply Finset.sum_congr rfl
      intro k _
      conv_lhs => rw [← c.sum_repr (b k)]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        ModuleCasimir.dualBasis_pairing ℂ B hB c, e]
    _ = ∑ l, ∑ k, B (e l) (b k) • productMap (c l) (d k) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l _
      have he : (∑ k, B (e l) (b k) • d k) = e l := by
        simpa only [d, LinearMap.BilinForm.dualBasis_repr_apply] using d.sum_repr (e l)
      calc
        _ = productMap (c l) (∑ k, B (e l) (b k) • d k) := by
          simp only [map_sum, map_smul]
        _ = _ := by rw [he]

theorem central : central_type.{u,i} := by
  intro L _ _ B hB hInv I _ b
  change casimir B hB b ∈ _
  have hgen (x : L) : ι ℂ x * casimir B hB b = casimir B hB b * ι ℂ x := by
    classical
    let D := LieAlgebra.ad ℂ L x
    have hD : ∀ y z, B (D y) z = -B y (D z) := hInv x
    have h := ModuleCasimir.skew_contraction ℂ B hB b D hD productMap
    have he (y : L) : ι ℂ (D y) = ι ℂ x * ι ℂ y - ι ℂ y * ι ℂ x :=
      (ι ℂ).map_lie x y
    change (∑ k, ι ℂ (D (b k)) * ι ℂ (B.dualBasis hB b k)) +
      (∑ k, ι ℂ (b k) * ι ℂ (D (B.dualBasis hB b k))) = 0 at h
    simp only [he, sub_mul, mul_sub, mul_assoc] at h
    rw [← Finset.sum_add_distrib] at h
    simp only [sub_add_sub_cancel] at h
    simpa only [casimir, casimir_value, Finset.mul_sum, Finset.sum_mul, mul_assoc,
      Finset.sum_sub_distrib, sub_eq_zero] using h
  rw [Subalgebra.mem_center_iff]
  intro a
  induction a using Shared.Lie.enveloping_induction ℂ L with
  | scalar r => exact Algebra.commutes r _
  | generator x => exact hgen x
  | mul a b ha hb => rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  | add a b ha hb => simp only [add_mul, mul_add, ha, hb]

section Forms

variable [FiniteDimensional ℂ L]

omit [FiniteDimensional ℂ L] in
private theorem invariant_assoc (B : Form (L := L)) (hInv : B.lieInvariant L)
    (x y z : L) : B ⁅x, y⁆ z = B x ⁅y, z⁆ := by
  rw [← lie_skew x y, map_neg, LinearMap.neg_apply, hInv y x z, neg_neg]

/-- Semisimple algebras are perfect, so invariance alone implies symmetry. -/
theorem symmetry : symmetry_type.{u} := by
  intro L _ _ _ hss B hInv
  constructor
  intro x y
  have hx : x ∈ (⁅(⊤ : LieIdeal ℂ L), (⊤ : LieIdeal ℂ L)⁆ : LieIdeal ℂ L).toSubmodule := by
    rw [semisimple_perfect ℂ L hss]
    trivial
  rw [LieSubmodule.lieIdeal_oper_eq_linear_span'] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨a, _, b, _, rfl⟩ := hz
      rw [invariant_assoc B hInv a b y, ← invariant_assoc B hInv y a b, hInv y a b,
        ← lie_skew b y, map_neg]
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb]
  | smul c a _ ha => simp [ha]

variable (H : LieSubalgebra ℂ L) (B : Form (L := L))

omit [FiniteDimensional ℂ L] in
private theorem orthogonal (hInv : B.lieInvariant L) {α β : Module.Dual ℂ H}
    {x y : L} (hx : x ∈ rootSpace H α) (hy : y ∈ rootSpace H β) (h : α + β ≠ 0) :
    B x y = 0 := by
  have hne : ∃ a : H, (α + β) a ≠ 0 := by
    by_contra! hzero
    exact h (LinearMap.ext hzero)
  obtain ⟨a, ha⟩ := hne
  have eq := hInv (a : L) x y
  rw [(mem_rootSpace H α x).mp hx a, (mem_rootSpace H β y).mp hy a] at eq
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at eq
  have hz : (α + β) a * B x y = 0 := by
    rw [LinearMap.add_apply, add_mul, eq, neg_add_cancel]
  exact (mul_eq_zero.mp hz).resolve_left ha

/-- Nondegeneracy on the full algebra implies nondegeneracy on each pair of opposite summands. -/
private theorem separates_opposite (hT : IsToral H) (hInv : B.lieInvariant L)
    (hB : B.Nondegenerate) {α : Module.Dual ℂ H} {x : L}
    (hx : x ∈ rootSpace H α) (hOpp : ∀ y ∈ rootSpace H (-α), B x y = 0) : x = 0 := by
  apply hB.1 x
  intro y
  have hy : y ∈ ⨆ β, rootSpace H β := by
    rw [iSup_rootSpace_eq_top H hT]
    trivial
  refine Submodule.iSup_induction (rootSpace H) (motive := fun z => B x z = 0)
    hy (fun β z hz => ?_) (by simp) (fun a b ha hb => by simp [ha, hb])
  by_cases he : α + β = 0
  · have he' : β = -α := (add_eq_zero_iff_neg_eq.mp he).symm
    exact hOpp z (he' ▸ hz)
  · exact orthogonal H B hInv hx hz he

private theorem restrict_nondegenerate (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (hInv : B.lieInvariant L) (hB : B.Nondegenerate) :
    (B.restrict H.toSubmodule).Nondegenerate := by
  have hleft (x : H) (hx : ∀ y : H, B (x : L) (y : L) = 0) : x = 0 := by
    apply Subtype.ext
    change (x : L) = 0
    have hmem : (x : L) ∈ rootSpace H 0 := by
      rw [rootSpace_zero hss H hH]
      exact x.property
    apply separates_opposite H B hH.1 hInv hB hmem
    intro y hy
    rw [neg_zero, rootSpace_zero hss H hH] at hy
    exact hx ⟨y, hy⟩
  exact ⟨hleft, fun x hx => hleft x fun y => (symmetry hss B hInv).eq _ _ |>.trans (hx y)⟩

private theorem pairing (hC : (B.restrict H.toSubmodule).Nondegenerate)
    (α : Module.Dual ℂ H) (h : H) :
    B (weightRepresentative H B α : L) (h : L) = α h := by
  change (B.restrict H.toSubmodule) (weightRepresentative H B α) h = α h
  simp only [weightRepresentative, weightRepresentative_value, dite_eq_left hC]
  exact congrArg (fun f : Module.Dual ℂ H => f h)
    ((B.restrict H.toSubmodule).toDual hC |>.apply_symm_apply α)

theorem representative_pairing : representative_pairing_type.{u} := by
  intro L _ _ _ H _ hss B hInv hB
  have hC := restrict_nondegenerate H B hss (RealRootSpace.cartan_isMaximalToral hss H) hInv hB
  exact ⟨hC, pairing H B hC⟩

theorem normalized_exists : normalized_exists_type.{u} := by
  intro L _ _ _ H _ hss φ B hInv hB
  classical
  have hH := RealRootSpace.cartan_isMaximalToral hss H
  choose x hx hx0 using fun α : PositiveRoot H φ =>
    (rootSpace H α.val).ne_bot_iff.mp α.property.1.2
  have he (α : PositiveRoot H φ) : ∃ y ∈ rootSpace H (-α.val), B (x α) y ≠ 0 := by
    by_contra! hz
    exact hx0 α (separates_opposite H B hH.1 hInv hB (hx α) hz)
  choose y hy hy0 using he
  refine ⟨x, fun α => (B (x α) (y α))⁻¹ • y α, fun α => ⟨hx α, ?_, ?_⟩⟩
  · exact (rootSpace H (-α.val)).smul_mem _ (hy α)
  · simp [hy0 α]

private theorem opposite_bracket (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (hInv : B.lieInvariant L) (hC : (B.restrict H.toSubmodule).Nondegenerate)
    {α : Module.Dual ℂ H} {x y : L}
    (hx : x ∈ rootSpace H α) (hy : y ∈ rootSpace H (-α)) (hxy : B x y = 1) :
    ⁅x, y⁆ = (weightRepresentative H B α : L) := by
  have hm := rootSpace_bracket H α (-α) x y hx hy
  rw [add_neg_cancel, rootSpace_zero hss H hH] at hm
  let z : H := ⟨⁅x, y⁆, hm⟩
  suffices z = weightRepresentative H B α from congrArg Subtype.val this
  apply ((B.restrict H.toSubmodule).toDual hC).injective
  ext a
  change B ⁅x, y⁆ (a : L) = B (weightRepresentative H B α : L) (a : L)
  rw [pairing H B hC, invariant_assoc B hInv, ← lie_skew y (a : L),
    (mem_rootSpace H (-α) y).mp hy a]
  simp [hxy]

theorem eigenvalue_difference : eigenvalue_difference_type.{u} := by
  intro L _ _ _ H hss φ B hInv lam
  let f := weightForm H B
  have hs (x y : Module.Dual ℂ H) : f x y = f y x := by
    exact (symmetry hss B hInv).eq _ _
  change f lam (lam + (2 : ℂ) • rho H φ) =
    f (lam + rho H φ) (lam + rho H φ) - f (rho H φ) (rho H φ)
  simp only [map_add, map_smul, LinearMap.add_apply, smul_eq_mul]
  rw [hs (rho H φ) lam]
  ring

end Forms

section Ordering

open private SerreProof.positive_or_neg from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SerreRelations

variable [FiniteDimensional ℂ L]
variable (H : LieSubalgebra ℂ L) (φ : Direction H) (B : Form (L := L))

@[instance_reducible] private def positives_finite (hT : IsToral H) : Fintype (PositiveRoot H φ) :=
  ((rootSet_finite H hT).subset (fun _ h => h.1)).fintype

omit [FiniteDimensional ℂ L] in
private theorem root_vectors_ne_zero {x y : PositiveRoot H φ → L}
    (hn : Normalized H φ B x y) (a : PositiveRoot H φ) : x a ≠ 0 ∧ y a ≠ 0 :=
  ⟨fun h => by simpa [h] using (hn a).2.2, fun h => by simpa [h] using (hn a).2.2⟩

private theorem unordered (hss : IsSemisimple ℂ L)
    (hH : IsMaximalToral H) (hφ : Regular H φ)
    (hB : B.Nondegenerate) (hInv : B.lieInvariant L)
    (hC : (B.restrict H.toSubmodule).Nondegenerate)
    {I : Type i} [Fintype I] (b : Basis I ℂ L) {J : Type j} [Fintype J] (h : Basis J ℂ H)
    (x y : PositiveRoot H φ → L) (hn : Normalized H φ B x y) :
    casimir B hB b =
      (∑ a, ι ℂ (h a : L) * ι ℂ (((B.restrict H.toSubmodule).dualBasis hC h a : H) : L)) +
      ∑ᶠ α : PositiveRoot H φ, (ι ℂ (x α) * ι ℂ (y α) + ι ℂ (y α) * ι ℂ (x α)) := by
  classical
  let _ : Fintype (PositiveRoot H φ) := positives_finite H φ hH.1
  let d := (B.restrict H.toSubmodule).dualBasis hC h
  let K := J ⊕ (PositiveRoot H φ ⊕ PositiveRoot H φ)
  let _ : DecidableEq K := fun a b => Classical.propDecidable (a = b)
  let f : K → L := Sum.elim (fun a => (h a : L)) (Sum.elim x y)
  let g : K → L := Sum.elim (fun a => (d a : L)) (Sum.elim y x)
  have hs := (symmetry hss B hInv).eq
  have hc (a : H) : (a : L) ∈ rootSpace H 0 := by
    rw [rootSpace_zero hss H hH]
    exact a.property
  have hcx (a : H) (p : PositiveRoot H φ) : B (a : L) (x p) = 0 :=
    orthogonal H B hInv (hc a) (hn p).1 (by simpa using p.property.1.1)
  have hcy (a : H) (p : PositiveRoot H φ) : B (a : L) (y p) = 0 :=
    orthogonal H B hInv (hc a) (hn p).2.1 (by simpa using p.property.1.1)
  have hxx (p q : PositiveRoot H φ) : B (x p) (x q) = 0 := by
    apply orthogonal H B hInv (hn p).1 (hn q).1
    intro he
    have hh := congrArg φ he
    simp only [map_add, map_zero] at hh
    exact (ne_of_gt (add_pos p.property.2 q.property.2)) hh
  have hyy (p q : PositiveRoot H φ) : B (y p) (y q) = 0 := by
    apply orthogonal H B hInv (hn p).2.1 (hn q).2.1
    intro he
    have hh := congrArg φ he
    simp only [map_add, map_neg, map_zero] at hh
    exact (ne_of_lt (add_neg (neg_neg_of_pos p.property.2) (neg_neg_of_pos q.property.2))) hh
  have hxy (p q : PositiveRoot H φ) : B (x p) (y q) = if p = q then 1 else 0 := by
    by_cases he : p = q
    · subst q
      simp [(hn p).2.2]
    · rw [ite_eq_right he]
      exact orthogonal H B hInv (hn p).1 (hn q).2.1
        (fun hz => he (Subtype.ext (sub_eq_zero.mp hz)))
  have hdual (a b : K) : B (g a) (f b) = if b = a then 1 else 0 := by
    rcases a with a | (a | a) <;> rcases b with b | (b | b)
    · simpa [f, g, d, K, Sum.inl.injEq] using (B.restrict H.toSubmodule).apply_dualBasis_left hC h a b
    · simp [f, g, K, hcx]
    · simp [f, g, K, hcy]
    · simp [f, g, K, hs (y a) (h b), hcy]
    · simp [f, g, K, Sum.inl.injEq, Sum.inr.injEq, hs (y a) (x b), hxy]
    · simp [f, g, K, Sum.inr.injEq, hyy]
    · simp [f, g, K, hs (x a) (h b), hcx]
    · simp [f, g, K, Sum.inr.injEq, hxx]
    · simp [f, g, K, Sum.inr.injEq, hxy, eq_comm]
  have hli : LinearIndependent ℂ f := by
    rw [Fintype.linearIndependent_iff]
    intro c hzero a
    have he := congrArg (B (g a)) hzero
    have hz : (∑ k : K, if k = a then c k else 0) = 0 := by
      simpa only [map_sum, map_smul, smul_eq_mul, map_zero, hdual,
        mul_ite, mul_one, mul_zero] using he
    rw [Finset.sum_eq_single a] at hz
    · simpa using hz
    · intro k _ hka
      simp [hka]
    · simp
  have hspan : Submodule.span ℂ (Set.range f) = ⊤ := by
    apply top_unique
    rw [← iSup_rootSpace_eq_top H hH.1]
    apply iSup_le
    intro α
    by_cases hα₀ : α = 0
    · subst α
      rw [rootSpace_zero hss H hH]
      intro z hz
      let a : H := ⟨z, hz⟩
      have he := congrArg (H.incl.toLinearMap) (h.sum_repr a)
      change (z : L) ∈ Submodule.span ℂ (Set.range f)
      simp only [map_sum, map_smul] at he
      change (∑ k, h.repr a k • (h k : L)) = z at he
      rw [← he]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl k, rfl⟩)
    · by_cases ha : α ∈ rootSet H
      · rcases SerreProof.positive_or_neg H φ hss hH hφ ha with hp | hp
        · let p : PositiveRoot H φ := ⟨α, hp⟩
          rw [eq_span_singleton_of_mem_of_finrank_eq_one
            (finrank_rootSpace_eq_one hss H hH α ha) (hn p).1 (root_vectors_ne_zero H φ B hn p).1]
          apply Submodule.span_le.mpr
          rintro _ rfl
          exact Submodule.subset_span ⟨Sum.inr (Sum.inl p), rfl⟩
        · let p : PositiveRoot H φ := ⟨-α, hp⟩
          have hm : y p ∈ rootSpace H α := by simpa [p] using (hn p).2.1
          rw [eq_span_singleton_of_mem_of_finrank_eq_one
            (finrank_rootSpace_eq_one hss H hH α ha) hm (root_vectors_ne_zero H φ B hn p).2]
          apply Submodule.span_le.mpr
          rintro _ rfl
          exact Submodule.subset_span ⟨Sum.inr (Sum.inr p), rfl⟩
      · rw [rootSpace_eq_bot_of_not_mem H α hα₀ ha]
        exact bot_le
  let c : Basis K ℂ L := Basis.mk hli hspan.ge
  have hcf : (c : K → L) = f := Basis.coe_mk _ _
  have hcg : (B.dualBasis hB c : K → L) = g :=
    (B.dualBasis_eq_iff hB c g).mpr (by simpa only [hcf] using hdual)
  change casimir_value B hB b = _
  rw [basis_independent B hB b c]
  unfold casimir_value
  calc
    _ = (∑ a : K, ι ℂ (f a) * ι ℂ (g a)) := Finset.sum_congr rfl fun a _ => by
      exact congrArg₂ (fun z w : L => ι ℂ z * ι ℂ w) (congrFun hcf a) (congrFun hcg a)
    _ = _ := by
      dsimp only [K, f, g]
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type, finsum_eq_sum_of_fintype,
        Finset.sum_add_distrib]
      rfl

theorem normal_order : normal_order_type.{u,i,j} := by
  intro L _ _ _ H _ hss φ hφ B hB hInv hC I _ b J _ h x y hn
  classical
  have hH := RealRootSpace.cartan_isMaximalToral hss H
  let _ : Fintype (PositiveRoot H φ) := positives_finite H φ hH.1
  have hbr (a : PositiveRoot H φ) :
      ι ℂ (x a) * ι ℂ (y a) + ι ℂ (y a) * ι ℂ (x a) =
        ι ℂ (weightRepresentative H B a.val : L) + (2 : ℂ) • (ι ℂ (y a) * ι ℂ (x a)) := by
    have he := (ι ℂ).map_lie (x a) (y a)
    rw [opposite_bracket H B hss hH hInv hC (hn a).1 (hn a).2.1 (hn a).2.2] at he
    change _ = ι ℂ (x a) * ι ℂ (y a) - ι ℂ (y a) * ι ℂ (x a) at he
    rw [he, two_smul]
    abel
  let t : Module.Dual ℂ H →ₗ[ℂ] UniversalEnvelopingAlgebra ℂ L :=
    (ι ℂ).toLinearMap.comp (H.incl.toLinearMap.comp (weightRepresentative H B))
  have hsum : (∑ a : PositiveRoot H φ, ι ℂ (weightRepresentative H B a.val : L)) =
      (2 : ℂ) • ι ℂ (weightRepresentative H B (rho H φ) : L) := by
    change (∑ a : PositiveRoot H φ, t a.val) = (2 : ℂ) • t (rho H φ)
    rw [← map_sum, ← map_smul]
    congr 1
    rw [rho, rho_value, finsum_eq_sum_of_fintype, smul_smul]
    norm_num
  have he := unordered H φ B hss hH hφ hB hInv hC b h x y hn
  change casimir_value B hB b = _ at he
  rw [he]
  simp only [finsum_eq_sum_of_fintype, hbr, Finset.sum_add_distrib, ← Finset.smul_sum,
    hsum, add_assoc]

end Ordering

theorem real_norm_difference : real_norm_difference_type.{u} := by
  intro L _ _ _ H _ hss φ B hInv _ hPos lam hlam
  let S := Submodule.span ℝ (rootSet H)
  have hH := RealRootSpace.cartan_isMaximalToral hss H
  let _ : Fintype (PositiveRoot H φ) := positives_finite H φ hH.1
  have hrho : rho H φ ∈ S := by
    have hsum : (∑ a : PositiveRoot H φ, a.val) ∈ S :=
      Submodule.sum_mem S fun a _ => Submodule.subset_span a.property.1
    unfold rho rho_value
    rw [finsum_eq_sum_of_fintype, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      Complex.coe_smul]
    exact S.smul_mem _ hsum
  have hdiag (μ : Module.Dual ℂ H) (hμ : μ ∈ S) :
      ((Real.sqrt (weightForm H B μ μ).re ^ 2 : ℝ) : ℂ) = weightForm H B μ μ := by
    by_cases hz : μ = 0
    · subst μ
      simp
    obtain ⟨hp, hi⟩ := hPos μ hμ hz
    rw [Real.sq_sqrt hp.le]
    exact Complex.ext (Complex.ofReal_re _) ((Complex.ofReal_im _).trans hi.symm)
  dsimp only
  rw [Complex.ofReal_sub]
  change eigenvalue_value H φ B lam =
    ((Real.sqrt (weightForm H B (lam + rho H φ) (lam + rho H φ)).re ^ 2 : ℝ) : ℂ) -
      ((Real.sqrt (weightForm H B (rho H φ) (rho H φ)).re ^ 2 : ℝ) : ℂ)
  rw [hdiag _ (S.add_mem hlam hrho), hdiag _ hrho]
  exact eigenvalue_difference H hss φ B hInv lam

section Action

open ModuleCasimir (action centralAction)

set_option maxHeartbeats 700000 in
theorem eigenvalue_action : eigenvalue_action_type.{u,v,i} := by
  intro L _ _ _ H _ hss φ hφ B hB hInv I _ b V _ _ _ _ lam w hw hpos hcyc
  classical
  have hH := RealRootSpace.cartan_isMaximalToral hss H
  let _ : Fintype (PositiveRoot H φ) := positives_finite H φ hH.1
  let _ : DecidableEq (Fin (finrank ℂ H)) := fun a b => Classical.propDecidable (a = b)
  let h := Module.finBasis ℂ H
  have hC := (representative_pairing H hss B hInv hB).1
  let d := (B.restrict H.toSubmodule).dualBasis hC h
  obtain ⟨x, y, hn⟩ := normalized_exists H hss φ B hInv hB
  let f := action ℂ L V
  let Ω := casimir B hB b
  have hi (z : L) (m : V) : f (ι ℂ z) m = ⁅z, m⁆ := by
    change (UniversalEnvelopingAlgebra.lift ℂ (LieModule.toEnd ℂ L V)) (ι ℂ z) m = _
    rw [UniversalEnvelopingAlgebra.lift_ι_apply]
    rfl
  have hx (a : PositiveRoot H φ) : f (ι ℂ (x a)) w = 0 := by
    rw [hi]
    exact hpos _ (LieSubalgebra.subset_lieSpan ⟨a.val, a.property.2, (hn a).1⟩)
  have hm (a : Fin (Module.finrank ℂ H)) :
      f (ι ℂ (h a : L) * ι ℂ (d a : L)) w = (lam (h a) * lam (d a)) • w := by
    rw [map_mul, Module.End.mul_apply, hi (d a : L) w, hw (d a), map_smul,
      hi (h a : L) w, hw (h a), smul_smul, mul_comm]
  have ht : weightRepresentative H B lam = ∑ a, lam (h a) • d a := by
    calc
      _ = (∑ a, d.repr (weightRepresentative H B lam) a • d a) := (d.sum_repr _).symm
      _ = _ := Finset.sum_congr rfl fun a _ => by
        rw [show d.repr (weightRepresentative H B lam) a = lam (h a) by
          dsimp only [d]
          rw [LinearMap.BilinForm.dualBasis_repr_apply]
          exact pairing H B hC lam (h a)]
  have hsum : (∑ a, lam (h a) * lam (d a)) = lam (weightRepresentative H B lam) := by
    conv_rhs => rw [ht]
    simp only [map_sum, map_smul, smul_eq_mul]
  have hfirst (μ : Module.Dual ℂ H) : weightForm H B lam μ =
      lam (weightRepresentative H B μ) :=
    pairing H B hC lam _
  let A := ∑ a, ι ℂ (h a : L) * ι ℂ (d a : L)
  let T := ι ℂ (weightRepresentative H B (rho H φ) : L)
  let R := ∑ᶠ a : PositiveRoot H φ, ι ℂ (y a) * ι ℂ (x a)
  have hΩ : Ω = A + (2 : ℂ) • T + (2 : ℂ) • R :=
    normal_order H hss φ hφ B hB hInv hC b h x y hn
  have hA : f A w = lam (weightRepresentative H B lam) • w := by
    dsimp only [A]
    rw [map_sum, LinearMap.sum_apply]
    simp_rw [hm]
    rw [← Finset.sum_smul, hsum]
  have hT : f T w = lam (weightRepresentative H B (rho H φ)) • w := by
    dsimp only [T]
    rw [hi, hw]
  have hR : f R w = 0 := by
    dsimp only [R]
    rw [finsum_eq_sum_of_fintype, map_sum, LinearMap.sum_apply]
    simp only [map_mul, Module.End.mul_apply, hx, map_zero, Finset.sum_const_zero]
  have hv : f Ω w = eigenvalue H φ B lam • w := by
    rw [hΩ]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hA, hT, hR,
      smul_zero, add_zero, smul_smul, ← add_smul]
    congr 1
    change _ = weightForm H B lam (lam + (2 : ℂ) • rho H φ)
    rw [hfirst]
    simp only [map_add, map_smul, smul_eq_mul]
  let F := centralAction ℂ L V Ω (central B hB hInv b)
  let D : V →ₗ⁅ℂ,L⁆ V := F - eigenvalue H φ B lam • LieModuleHom.id
  have hk : D.ker = ⊤ := by
    apply top_unique
    rw [← hcyc, LieSubmodule.lieSpan_le]
    rintro _ rfl
    exact D.mem_ker.mpr (sub_eq_zero.mpr hv)
  intro m
  have hz : m ∈ D.ker := by rw [hk]; trivial
  change f Ω m = eigenvalue H φ B lam • m
  have he : f Ω m - eigenvalue H φ B lam • m = 0 := D.mem_ker.mp hz
  exact sub_eq_zero.mp he

end Action

end LieAlgebrasAndRepresentations.HighestWeightCasimir
