import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.WeylDenominatorData
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.LongestElementRho
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.DominantFundamentalDomain
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.FiniteModuleWeights
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Algebra.BigOperators.Ring.Finset

noncomputable section

namespace LieAlgebrasAndRepresentations.WeylDenominator

open AddMonoidAlgebra Set Module
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {R : Set E} {v : E}

private lemma finiteDimensional_of_rootSystem (hR : IsRootSystem R) :
    FiniteDimensional ℝ E := by
  letI := FiniteDimensional.span_of_finite ℝ hR.finite
  exact FiniteDimensional.of_surjective (Submodule.span ℝ R).subtype (fun x => by
    have hx : x ∈ Submodule.span ℝ R := by rw [hR.span_eq_top]; trivial
    exact ⟨⟨x, hx⟩, rfl⟩)

private lemma reflection_eq_sub_coroot (a x : E) :
    rootReflectionEquiv a x = x - inner ℝ x (coroot a) • a := by
  rw [rootReflectionEquiv_apply, rootReflection, coroot, real_inner_smul_right]
  congr 2
  ring

private lemma reflection_det [FiniteDimensional ℝ E] {a : E} (ha : a ≠ 0) :
    LinearMap.det (rootReflectionEquiv a).toLinearMap = (-1 : ℝ) := by
  let K := (ℝ ∙ a)ᗮ
  have he : (rootReflectionEquiv a).toLinearMap = K.reflection.toLinearMap := by
    ext x
    change rootReflectionEquiv a x = K.reflection x
    have hd : x - (inner ℝ x (coroot a) / 2) • a ∈ K := by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right,
        real_inner_smul_right, coroot, real_inner_smul_right, real_inner_comm a x]
      field_simp [_root_.inner_self_ne_zero.mpr ha]
      ring
    let t := inner ℝ x (coroot a) / 2
    have hx : x = (x - t • a) + t • a := (sub_add_cancel x _).symm
    have hK : K.reflection (x - t • a) = x - t • a :=
      K.reflection_mem_subspace_eq_self hd
    have hKa : K.reflection a = -a :=
      Submodule.reflection_orthogonalComplement_singleton_eq_neg a
    nth_rw 2 [hx]
    rw [map_add, map_smul, hK, hKa, reflection_eq_sub_coroot, smul_neg,
      ← sub_eq_add_neg, sub_sub, ← add_smul]
    congr 2
    dsimp [t]
    ring
  rw [he, Submodule.det_reflection]
  have hK : Kᗮ = ℝ ∙ a := Submodule.orthogonal_orthogonal _
  rw [hK, finrank_span_singleton ha, pow_one]

/-- The integer sign is the determinant, viewed in the reals. -/
theorem sign_cast (hR : IsRootSystem R) (w : rootWeylGroup R) :
    (sign w : ℝ) = LinearMap.det w.val.toLinearMap := by
  haveI := finiteDimensional_of_rootSystem hR
  have hd : LinearMap.det w.val.toLinearMap = 1 ∨
      LinearMap.det w.val.toLinearMap = -1 := by
    let G : Subgroup (E ≃ₗ[ℝ] E) := {
      carrier := {g | LinearMap.det g.toLinearMap = 1 ∨ LinearMap.det g.toLinearMap = -1}
      one_mem' := Or.inl (by simp)
      mul_mem' := by
        intro f g hf hg
        change LinearMap.det (f.toLinearMap.comp g.toLinearMap) = 1 ∨
          LinearMap.det (f.toLinearMap.comp g.toLinearMap) = -1
        rw [LinearMap.det_comp]
        rcases hf with hf | hf <;> rcases hg with hg | hg <;> norm_num [hf, hg]
      inv_mem' := by
        intro f hf
        have hp : LinearMap.det f.toLinearMap *
            LinearMap.det f.symm.toLinearMap = 1 := by
          rw [← LinearMap.det_comp]
          simp
        change LinearMap.det f.symm.toLinearMap = 1 ∨ LinearMap.det f.symm.toLinearMap = -1
        rcases hf with hf | hf
        · exact Or.inl (by simpa [hf] using hp)
        · exact Or.inr (by rw [hf] at hp; linarith) }
    have hle : rootWeylGroup R ≤ G := (Subgroup.closure_le G).mpr (by
      rintro _ ⟨a, ha, rfl⟩
      exact Or.inr (reflection_det (hR.nonzero a ha)))
    exact hle w.property
  rcases hd with hd | hd <;> norm_num [sign, hd]

private lemma sign_mul (hR : IsRootSystem R) (w z : rootWeylGroup R) :
    sign (w * z) = sign w * sign z := by
  exact_mod_cast (show (sign (w * z) : ℝ) = (sign w : ℝ) * (sign z : ℝ) by
    rw [sign_cast hR, sign_cast hR, sign_cast hR]
    exact LinearMap.det_comp _ _)

private lemma sign_ne_zero (w : rootWeylGroup R) : sign w ≠ 0 := by
  unfold sign
  split <;> norm_num

private abbrev e (a : E) : AddMonoidAlgebra ℤ E := single a 1

private def onGroupRing (w : E ≃ₗ[ℝ] E) :
    AddMonoidAlgebra ℤ E ≃+* AddMonoidAlgebra ℤ E :=
  mapDomainRingEquiv ℤ w.toAddEquiv

private lemma onGroupRing_e (w : E ≃ₗ[ℝ] E) (a : E) : onGroupRing w (e a) = e (w a) := by
  simp [onGroupRing]

private lemma onGroupRing_coeff (w : E ≃ₗ[ℝ] E) (F : AddMonoidAlgebra ℤ E) (x : E) :
    (onGroupRing w F).coeff (w x) = F.coeff x := by
  simp [onGroupRing]

private lemma onGroupRing_mul (w z : E ≃ₗ[ℝ] E) (F : AddMonoidAlgebra ℤ E) :
    onGroupRing (w * z) F = onGroupRing w (onGroupRing z F) := by
  apply AddMonoidAlgebra.ext
  ext x
  obtain ⟨y, rfl⟩ := (w * z).surjective x
  rw [onGroupRing_coeff]
  change F.coeff y = (onGroupRing w (onGroupRing z F)).coeff (w (z y))
  rw [onGroupRing_coeff, onGroupRing_coeff]

private lemma simple_on_denominator (hR : IsRootSystem R) (hv : RootRegular R v)
    {a : E} (ha : a ∈ simpleRoots R v) :
    onGroupRing (rootReflectionEquiv a)
      (denominator (rootRho R v) ((positiveRoots_finite hR.toRootAxioms v).toFinset) id) =
    -denominator (rootRho R v) ((positiveRoots_finite hR.toRootAxioms v).toFinset) id := by
  classical
  let S := (positiveRoots_finite hR.toRootAxioms v).toFinset
  let s := rootReflectionEquiv a
  let f := fun x : E => (1 : AddMonoidAlgebra ℤ E) - e (-x)
  have haS : a ∈ S := by simpa [S] using ha.1
  have hsa : s a = -a := by
    simp [s, reflection_self (hR.nonzero a ha.1.1)]
  have hi (x : E) : s (s x) = x := by
    simp [s, reflection_involutive]
  have hm {x : E} (hx : x ∈ S.erase a) : s x ∈ S.erase a := by
    obtain ⟨hne, hxS⟩ := Finset.mem_erase.mp hx
    have hxP : x ∈ positiveRoots R v := by simpa [S] using hxS
    have hp := simple_reflection_positive hR hv ha hxP hne
    refine Finset.mem_erase.mpr ⟨?_, by simpa [S, s] using hp⟩
    intro he
    have hxna : x = -a := by rw [← hi x, he, hsa]
    have hxp := hxP.2
    rw [hxna, inner_neg_right] at hxp
    linarith [ha.1.2]
  have hperm : ∏ x ∈ S.erase a, f (s x) = ∏ x ∈ S.erase a, f x := by
    apply Finset.prod_bij (fun x _ => s x)
    · exact fun _ hx => hm hx
    · exact fun _ _ _ _ he => s.injective he
    · exact fun x hx => ⟨s x, hm hx, hi x⟩
    · intros
      rfl
  have hfactor : e (rootRho R v - a) * (1 - e a) =
      -(e (rootRho R v) * f a) := by
    dsimp [f]
    rw [mul_sub, mul_sub, mul_one, mul_one, single_mul_single, single_mul_single]
    rw [sub_add_cancel, ← sub_eq_add_neg (rootRho R v) a]
    simp
  change onGroupRing s (e (rootRho R v) * ∏ x ∈ S, f x) =
    -(e (rootRho R v) * ∏ x ∈ S, f x)
  rw [← Finset.prod_erase_mul S f haS, map_mul, map_mul, map_prod, onGroupRing_e]
  have hf (x : E) : onGroupRing s (f x) = f (s x) := by
    simp [f, onGroupRing_e]
  simp_rw [hf]
  rw [hperm, show s (rootRho R v) = rootRho R v - a by
    simpa [s] using simple_reflection_rho hR hv ha, hsa]
  have hfa : f (-a) = 1 - e a := by simp [f]
  rw [hfa]
  calc
    _ = (∏ x ∈ S.erase a, f x) * (e (rootRho R v - a) * (1 - e a)) := by ac_rfl
    _ = _ := by rw [hfactor, mul_neg, mul_left_comm]

private lemma sign_one : sign (1 : rootWeylGroup R) = 1 := by
  simp [sign]

private lemma sign_reflection (hR : IsRootSystem R) {a : E} (ha : a ∈ R) :
    sign (⟨rootReflectionEquiv a, Subgroup.subset_closure ⟨a, ha, rfl⟩⟩ :
      rootWeylGroup R) = -1 := by
  haveI := finiteDimensional_of_rootSystem hR
  norm_num [sign, reflection_det (hR.nonzero a ha)]

private lemma sign_sq (w : rootWeylGroup R) : sign w * sign w = 1 := by
  unfold sign
  split <;> norm_num

private lemma weyl_on_denominator (hR : IsRootSystem R) (hv : RootRegular R v)
    (w : rootWeylGroup R) :
    let D := denominator (rootRho R v) ((positiveRoots_finite hR.toRootAxioms v).toFinset) id
    onGroupRing w.val D = sign w • D := by
  dsimp only
  obtain ⟨l, hl⟩ := exists_weylWord hR hv w
  let D := denominator (rootRho R v) ((positiveRoots_finite hR.toRootAxioms v).toFinset) id
  have hw : w = ⟨weylWordProduct l, weylWordProduct_mem l⟩ := Subtype.ext hl.symm
  rw [hw]
  clear hw hl w
  change onGroupRing (weylWordProduct l) D =
    sign (⟨weylWordProduct l, weylWordProduct_mem l⟩ : rootWeylGroup R) • D
  induction l with
  | nil =>
    change onGroupRing (1 : E ≃ₗ[ℝ] E) D = sign (1 : rootWeylGroup R) • D
    rw [sign_one, one_smul]
    apply AddMonoidAlgebra.ext
    ext x
    exact onGroupRing_coeff 1 D x
  | cons a l ih =>
    let s : rootWeylGroup R :=
      ⟨rootReflectionEquiv a, Subgroup.subset_closure ⟨a, a.property.1.1, rfl⟩⟩
    let z : rootWeylGroup R := ⟨weylWordProduct l, weylWordProduct_mem l⟩
    change onGroupRing (s.val * z.val) D = sign (s * z) • D
    rw [onGroupRing_mul, show onGroupRing z.val D = sign z • D from ih, map_zsmul,
      show onGroupRing s.val D = -D from simple_on_denominator hR hv a.property,
      sign_mul hR, show sign s = -1 from sign_reflection hR a.property.1.1]
    simp

private lemma denominator_coeff_weyl (hR : IsRootSystem R) (hv : RootRegular R v)
    (w : rootWeylGroup R) (x : E) :
    let D := denominator (rootRho R v) ((positiveRoots_finite hR.toRootAxioms v).toFinset) id
    D.coeff (w.val x) = sign w * D.coeff x := by
  let D := denominator (rootRho R v) ((positiveRoots_finite hR.toRootAxioms v).toFinset) id
  have he := onGroupRing_coeff w.val D x
  rw [weyl_on_denominator hR hv w] at he
  change sign w * D.coeff (w.val x) = D.coeff x at he
  change D.coeff (w.val x) = sign w * D.coeff x
  rw [← he, ← mul_assoc, sign_sq, one_mul]

omit [InnerProductSpace ℝ E] in
private lemma denominator_expansion (r : E) (S : Finset E) :
    denominator r S id =
      ∑ T ∈ S.powerset, single (r - ∑ a ∈ T, a) ((-1 : ℤ) ^ T.card) := by
  classical
  unfold denominator
  simp only [id_eq]
  rw [Finset.prod_sub, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  simp only [Finset.prod_const_one, mul_one, prod_single]
  have hn : ((-1 : AddMonoidAlgebra ℤ E) ^ T.card) =
      single 0 ((-1 : ℤ) ^ T.card) := by
    change _ = singleZeroRingHom _
    simp
  rw [hn, single_mul_single, single_mul_single]
  rw [Finset.sum_neg_distrib]
  simp [sub_eq_add_neg]

private lemma denominator_support (r : E) (S : Finset E) {x : E}
    (hx : (denominator r S id).coeff x ≠ 0) :
    ∃ T ⊆ S, x = r - ∑ a ∈ T, a := by
  classical
  rw [denominator_expansion, coeff_sum, Finsupp.finsetSum_apply] at hx
  by_contra! hn
  apply hx
  apply Finset.sum_eq_zero
  intro T hT
  simp [Ne.symm (hn T (Finset.mem_powerset.mp hT))]

private lemma denominator_coeff_top (r : E) (S : Finset E)
    (hS : ∀ a ∈ S, 0 < inner ℝ v a) :
    (denominator r S id).coeff r = 1 := by
  classical
  rw [denominator_expansion, coeff_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro T hT hne
    have ht : 0 < inner ℝ v (∑ a ∈ T, a) := by
      rw [inner_sum]
      exact Finset.sum_pos (fun a ha => hS a (Finset.mem_powerset.mp hT ha))
        (Finset.nonempty_iff_ne_empty.mpr hne)
    have hs : ∑ a ∈ T, a ≠ 0 := by
      intro hh
      simp [hh] at ht
    simp [hs]
  · simp

section WeightLattice

variable {ι : Type*} {b : Basis ι ℝ E} (hb : IsSimpleBasis R v b)
include hb

private lemma root_mem_weightLattice (hR : IsRootSystem R) {a : E} (ha : a ∈ R) :
    a ∈ weightLattice b := by
  apply (weightLattice_mem_iff b a).mpr
  intro i
  simpa only [inner_coroot, rootCartan] using hR.integral (b i) (hb.root_mem i) a ha

private lemma rho_mem_weightLattice (hR : IsRootSystem R) (hv : RootRegular R v) :
    rootRho R v ∈ weightLattice b := by
  exact (weightLattice_mem_iff b _).mpr fun i =>
    ⟨1, by simpa using rho_simple_coroot_pairing R hR v hv (b i) (hb.mem i)⟩

private lemma reflection_mem_weightLattice (hR : IsRootSystem R) {a x : E}
    (ha : a ∈ simpleRoots R v) (hx : x ∈ weightLattice b) :
    rootReflectionEquiv a x ∈ weightLattice b := by
  have hr : a ∈ Set.range b := hb.symm ▸ ha
  obtain ⟨i, hi⟩ := hr
  obtain ⟨n, hn⟩ := (weightLattice_mem_iff b x).mp hx i
  rw [hi] at hn
  rw [reflection_eq_sub_coroot, hn, Int.cast_smul_eq_zsmul ℝ]
  exact sub_mem hx (Submodule.smul_mem _ n (root_mem_weightLattice hb hR ha.1.1))

private lemma weyl_mem_weightLattice (hR : IsRootSystem R) (hv : RootRegular R v)
    (w : rootWeylGroup R) {x : E} (hx : x ∈ weightLattice b) :
    w.val x ∈ weightLattice b := by
  obtain ⟨l, hl⟩ := exists_weylWord hR hv w
  rw [← hl]
  clear hl w
  induction l with
  | nil => exact hx
  | cons a l ih =>
    exact reflection_mem_weightLattice hb hR a.property ih

omit hb in
private lemma simple_inner_nonneg_of_coroot {d a : E}
    (h : 0 ≤ inner ℝ d (coroot a)) :
    0 ≤ inner ℝ d a := by
  by_cases ha : a = 0
  · simp [ha]
  have hpos : 0 < 2 / inner ℝ a a :=
    div_pos two_pos (real_inner_self_pos.mpr ha)
  rw [coroot, real_inner_smul_right] at h
  exact nonneg_of_mul_nonneg_right h hpos

omit hb in
private lemma weak_dominant_inner_nonneg (hR : IsRootSystem R) {d a : E}
    (hd : ∀ i ∈ simpleRoots R v, 0 ≤ inner ℝ d i) (ha : a ∈ positiveRoots R v) :
    0 ≤ inner ℝ d a := by
  have h : ∀ x ∈ AddSubmonoid.closure (simpleRoots R v), 0 ≤ inner ℝ d x := by
    intro x hx
    refine AddSubmonoid.closure_induction hd (by simp) (fun a b _ _ ha hb => ?_) hx
    rw [inner_add_right]
    exact add_nonneg ha hb
  exact h a (positive_mem_closure_simple hR.toRootAxioms v ha)

omit hb in
private lemma dominant_of_nonzero_coeff (hR : IsRootSystem R) (hv : RootRegular R v)
    {x : E} (hx : x ∈ closedSimpleChamber R v)
    (hc : (denominator (rootRho R v) ((positiveRoots_finite hR.toRootAxioms v).toFinset) id).coeff x ≠ 0) :
    x ∈ simpleChamber R v := by
  intro a ha
  have hn := hx a ha
  by_contra! hna
  have hz := le_antisymm hna hn
  let s : rootWeylGroup R := ⟨rootReflectionEquiv a, Subgroup.subset_closure ⟨a, ha.1.1, rfl⟩⟩
  have hs : s.val x = x := by
    change rootReflectionEquiv a x = x
    simp [rootReflection, hz]
  have hcoeff := denominator_coeff_weyl hR hv s x
  dsimp only at hcoeff
  rw [hs, show sign s = -1 from sign_reflection hR ha.1.1] at hcoeff
  apply hc
  linarith

private lemma dominant_exponent_eq_rho (hR : IsRootSystem R) (hv : RootRegular R v)
    {x : E} (hx : x ∈ simpleChamber R v)
    (hc : (denominator (rootRho R v) ((positiveRoots_finite hR.toRootAxioms v).toFinset) id).coeff x ≠ 0) :
    x = rootRho R v := by
  obtain ⟨T, hT, he⟩ := denominator_support _ _ hc
  have hTa (a : E) (ha : a ∈ T) : a ∈ positiveRoots R v := by
    simpa only [Set.Finite.mem_toFinset] using hT ha
  have hxP : x ∈ weightLattice b := by
    rw [he]
    exact sub_mem (rho_mem_weightLattice hb hR hv) (Submodule.sum_mem _ (fun a ha =>
      root_mem_weightLattice hb hR (hTa a ha).1))
  have hd (a : E) (ha : a ∈ simpleRoots R v) : 0 ≤ inner ℝ (x - rootRho R v) a := by
    have hr : a ∈ Set.range b := hb.symm ▸ ha
    obtain ⟨i, hi⟩ := hr
    obtain ⟨n, hn⟩ := (weightLattice_mem_iff b x).mp hxP i
    rw [hi] at hn
    have hxp : 0 < inner ℝ x (coroot a) := by
      rw [coroot, real_inner_smul_right]
      exact mul_pos (div_pos two_pos (real_inner_self_pos.mpr (hR.nonzero a ha.1.1))) (hx a ha)
    have hn₀ : (0 : ℤ) < n := by exact_mod_cast (hn ▸ hxp)
    have hn₁ : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ n by omega)
    apply simple_inner_nonneg_of_coroot
    rw [inner_sub_left, hn, rho_simple_coroot_pairing R hR v hv a ha]
    exact sub_nonneg.mpr hn₁
  have he' : x - rootRho R v = -(∑ a ∈ T, a) := by rw [he]; abel
  have hs : inner ℝ (x - rootRho R v) (x - rootRho R v) ≤ 0 := by
    nth_rw 2 [he']
    rw [inner_neg_right, inner_sum, neg_nonpos]
    exact Finset.sum_nonneg (fun a ha => weak_dominant_inner_nonneg hR hd (hTa a ha))
  exact sub_eq_zero.mp (_root_.inner_self_eq_zero.mp
    (le_antisymm hs (real_inner_self_nonneg)))

end WeightLattice

private lemma rho_in_simpleChamber (hR : IsRootSystem R) (hv : RootRegular R v) :
    rootRho R v ∈ simpleChamber R v := by
  intro a ha
  have he := rho_simple_coroot_pairing R hR v hv a ha
  have hc : 0 < 2 / inner ℝ a a :=
    div_pos two_pos (real_inner_self_pos.mpr (hR.nonzero a ha.1.1))
  rw [coroot, real_inner_smul_right] at he
  exact pos_of_mul_pos_right (he.symm ▸ zero_lt_one) hc.le

private lemma rho_orbit_injective (hR : IsRootSystem R) (hv : RootRegular R v) :
    Function.Injective (fun w : rootWeylGroup R => w.val (rootRho R v)) := by
  intro w z hwz
  change w.val (rootRho R v) = z.val (rootRho R v) at hwz
  let t := z⁻¹ * w
  have ht : t.val (rootRho R v) = rootRho R v := by
    change z.val.symm (w.val (rootRho R v)) = rootRho R v
    rw [hwz, LinearEquiv.symm_apply_apply]
  have hr := rho_in_simpleChamber hR hv
  have hreg := simpleChamber_regular hR.toRootAxioms hv hr
  have hc := rootWeylGroup_image_component hR.toRootAxioms t hreg
  rw [ht] at hc
  have hC := simpleChamber_connectedComponent R hR v hv
  have hm : rootRho R v ∈ connectedComponentIn (rootHyperplaneComplement R) v := hC ▸ hr
  have hcomp : connectedComponentIn (rootHyperplaneComplement R) (rootRho R v) =
      simpleChamber R v := (connectedComponentIn_eq hm).symm.trans hC.symm
  rw [hcomp] at hc
  exact (inv_mul_eq_one.mp (weyl_simpleChamber_stabilizer hR hv t hc)).symm

private theorem denominator_identity_ambient (hR : IsRootSystem R) (hv : RootRegular R v) :
    denominator (rootRho R v) ((positiveRoots_finite hR.toRootAxioms v).toFinset) id =
      alternant sign (fun w : rootWeylGroup R => w.val (rootRho R v)) := by
  classical
  letI := rootWeylGroup_finite hR
  letI := Fintype.ofFinite (rootWeylGroup R)
  let S := (positiveRoots_finite hR.toRootAxioms v).toFinset
  let D := denominator (rootRho R v) S id
  let A := alternant sign (fun w : rootWeylGroup R => w.val (rootRho R v))
  obtain ⟨b, hb⟩ := simpleRoots_basis R hR v hv
  have hb' : IsSimpleBasis R v b := by
    change Set.range b = simpleRoots R v
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      rw [hb]
      exact i.property
    · intro ha
      exact ⟨⟨a, ha⟩, hb ⟨a, ha⟩⟩
  have htop : D.coeff (rootRho R v) = 1 :=
    denominator_coeff_top _ S (fun a ha => (show a ∈ positiveRoots R v from by simpa [S] using ha).2)
  apply AddMonoidAlgebra.ext
  ext x
  change D.coeff x = A.coeff x
  have hA : A.coeff x =
      ∑ w : rootWeylGroup R, (single (w.val (rootRho R v)) (sign w)).coeff x := by
    simp only [A, alternant,
      finsum_eq_sum_of_fintype, coeff_sum, Finsupp.finsetSum_apply]
  rw [hA]
  by_cases h : ∃ w : rootWeylGroup R, w.val (rootRho R v) = x
  · obtain ⟨w, rfl⟩ := h
    rw [denominator_coeff_weyl hR hv, htop, mul_one, Finset.sum_eq_single w]
    · simp
    · intro z _ hzw
      have hn : z.val (rootRho R v) ≠ w.val (rootRho R v) :=
        fun he => hzw (rho_orbit_injective hR hv he)
      simp [hn]
    · simp
  · have hAx : (∑ w : rootWeylGroup R,
        (single (w.val (rootRho R v)) (sign w)).coeff x) = 0 := by
      apply Finset.sum_eq_zero
      intro w _
      have hn : w.val (rootRho R v) ≠ x := fun he => h ⟨w, he⟩
      simp [hn]
    rw [hAx]
    by_contra hx
    obtain ⟨w, hw⟩ := exists_weyl_into_closedSimpleChamber hR v x
    have he := denominator_coeff_weyl hR hv w x
    dsimp only at he
    have hc : D.coeff (w.val x) ≠ 0 := by
      change D.coeff (w.val x) = sign w * D.coeff x at he
      rw [he]
      exact mul_ne_zero (sign_ne_zero w) hx
    have hd := dominant_of_nonzero_coeff hR hv hw hc
    have hr := dominant_exponent_eq_rho hb' hR hv hd hc
    apply h
    exact ⟨w⁻¹, by change w.val.symm (rootRho R v) = x; rw [← hr, LinearEquiv.symm_apply_apply]⟩

section Cartan

open _root_.Specs.LieAlgebrasAndRepresentations
open RealRootSpace RootDecomposition RootForm FormalCharacters FiniteModuleWeights
open SerreRelations VermaModules HighestWeightData
open scoped TensorProduct

universe u

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
variable {H : LieSubalgebra ℂ L} (d : Realization H)

open private complexifyAutomorphism complexifyAutomorphism_apply extension_injective
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.FiniteModuleWeights

private lemma complexify_det [FiniteDimensional ℝ (RealRootSpace.E H)]
    (w : RealRootSpace.E H ≃ₗ[ℝ] RealRootSpace.E H) :
    LinearMap.det (complexifyAutomorphism d w).toLinearMap =
      ((LinearMap.det w.toLinearMap : ℝ) : ℂ) := by
  change LinearMap.det (d.complexification.toLinearMap.comp
    ((w.toLinearMap.baseChange ℂ).comp d.complexification.symm.toLinearMap)) = _
  rw [LinearMap.det_conj, LinearMap.det_baseChange]
  rfl

private lemma extension_image_roots : d.j '' realRoots H = rootSet_value H := by
  ext α
  constructor
  · rintro ⟨_, ⟨β, hβ, rfl⟩, rfl⟩
    simpa only [d.extension_root β hβ] using hβ
  · intro hα
    exact ⟨rootRestriction H α, ⟨α, hα, rfl⟩, d.extension_root α hα⟩

private lemma extension_mem_positive (φ : Direction H)
    (v : RealRootSpace.E H) (hv : ∀ x,
      letI := d.normedAddCommGroup
      letI := d.innerProductSpace
      inner ℝ v x = φ (d.j x)) (x : RealRootSpace.E H) :
    letI := d.normedAddCommGroup
    letI := d.innerProductSpace
    d.j x ∈ positive H φ ↔ x ∈ positiveRoots (realRoots H) v := by
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  have hx : d.j x ∈ rootSet_value H ↔ x ∈ realRoots H := by
    rw [← extension_image_roots d]
    exact (extension_injective d).mem_set_image
  change (d.j x ∈ rootSet_value H ∧ 0 < φ (d.j x)) ↔
      (x ∈ realRoots H ∧ 0 < inner ℝ v x)
  rw [hx, hv]

private lemma extension_image_positive (φ : Direction H)
    (v : RealRootSpace.E H) (hv : ∀ x,
      letI := d.normedAddCommGroup
      letI := d.innerProductSpace
      inner ℝ v x = φ (d.j x)) :
    letI := d.normedAddCommGroup
    letI := d.innerProductSpace
    d.j '' positiveRoots (realRoots H) v = positive H φ := by
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  ext α
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (extension_mem_positive d φ v hv x).mpr hx
  · intro ha
    have hr : α ∈ d.j '' realRoots H := (extension_image_roots d).symm ▸ ha.1
    obtain ⟨x, _, rfl⟩ := hr
    exact ⟨x, (extension_mem_positive d φ v hv x).mp ha, rfl⟩

private lemma extension_mem_simple (φ : Direction H)
    (v : RealRootSpace.E H) (hv : ∀ x,
      letI := d.normedAddCommGroup
      letI := d.innerProductSpace
      inner ℝ v x = φ (d.j x)) (x : RealRootSpace.E H) :
    letI := d.normedAddCommGroup
    letI := d.innerProductSpace
    d.j x ∈ simple H φ ↔ x ∈ simpleRoots (realRoots H) v := by
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  have hpos := extension_mem_positive d φ v hv
  constructor
  · intro hx
    refine ⟨(hpos x).mp hx.1, ?_⟩
    intro a ha b hb he
    exact hx.2 (d.j a) ((hpos a).mpr ha) (d.j b) ((hpos b).mpr hb) (by rw [← map_add, ← he])
  · intro hx
    refine ⟨(hpos x).mpr hx.1, ?_⟩
    intro α hα β hβ he
    rw [← extension_image_positive d φ v hv] at hα hβ
    obtain ⟨a, ha, rfl⟩ := hα
    obtain ⟨b, hb, rfl⟩ := hβ
    apply hx.2 a ha b hb
    exact extension_injective d (by rw [map_add]; exact he)

private lemma map_denominator {P Q : Type*} [AddCommGroup P] [AddCommGroup Q]
    {I : Type*} (f : P →+ Q) (r : P) (S : Finset I) (α : I → P) :
    mapDomainRingHom ℤ f (denominator r S α) = denominator (f r) S (f ∘ α) := by
  simp only [denominator, map_mul, map_prod, map_sub, map_one,
    mapDomainRingHom_apply, mapDomain_single, map_neg, Function.comp_apply]

private lemma map_alternant {P Q : Type*} [AddCommGroup P] [AddCommGroup Q]
    {W : Type*} [Fintype W] (f : P →+ Q) (ε : W → ℤ) (o : W → P) :
    mapDomainRingHom ℤ f (alternant ε o) = alternant ε (f ∘ o) := by
  simp only [alternant, finsum_eq_sum_of_fintype, map_sum,
    mapDomainRingHom_apply, mapDomain_single, Function.comp_apply]

/-- The source's denominator identity in the same integral group ring used
for finite characters, for every Cartan and regular choice of positives. -/
theorem cartan_identity (hss : SolvableRadical.IsSemisimple_value ℂ L)
    (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (φ : Direction H) (hφ : Regular H φ) :
    ∃ (hS : (positive H φ).Finite) (hρ : cartanRho H φ hS ∈ integralWeights H φ)
      (hP : ∀ a ∈ positive H φ, a ∈ integralWeights H φ)
      (hW : ∀ w : weightWeylGroup H, ∀ x ∈ integralWeights H φ,
        w.val x ∈ integralWeights H φ),
      Finite (weightWeylGroup H) ∧
      (∀ w : weightWeylGroup H, (cartanSign H w : ℂ) = LinearMap.det w.val.toLinearMap) ∧
      cartanDenominator H φ hS hρ hP =
        cartanAlternant H φ hW ⟨cartanRho H φ hS, hρ⟩ := by
  classical
  obtain ⟨d, hd⟩ := LieAlgebrasAndRepresentations.HighestWeight.cartan_lattice_comparison.{u, u}
    hss H
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  let R := realRoots H
  have hR : IsRootSystem R := d.root_system
  letI := finiteDimensional_of_rootSystem hR
  let v := (InnerProductSpace.toDual ℝ (RealRootSpace.E H)).symm
    (φ.comp d.j).toContinuousLinearMap
  have hv (x : RealRootSpace.E H) : inner ℝ v x = φ (d.j x) :=
    InnerProductSpace.toDual_symm_apply
  have hvR : RootRegular R v := by
    rintro x ⟨α, hα, rfl⟩
    rw [hv, d.extension_root α hα]
    exact hφ α hα
  have hj := extension_injective d
  have hpos := extension_image_positive d φ v hv
  have hsimp := extension_mem_simple d φ v hv
  let s₀ : simpleRoots R v → simple H φ := fun a => ⟨d.j a.val, (hsimp a).mpr a.property⟩
  have hs₀ : Function.Bijective s₀ := by
    constructor
    · intro a b he
      exact Subtype.ext (hj (congrArg Subtype.val he))
    · intro a
      have ha : a.val ∈ d.j '' positiveRoots R v := hpos.symm ▸ a.property.1
      obtain ⟨x, _, hxa⟩ := ha
      exact ⟨⟨x, (hsimp x).mp (hxa ▸ a.property)⟩, Subtype.ext hxa⟩
  let s : simple H φ ≃ simpleRoots R v := (Equiv.ofBijective s₀ hs₀).symm
  have hs (i : simple H φ) : d.j (s i : RealRootSpace.E H) = i.val :=
    congrArg Subtype.val ((Equiv.ofBijective s₀ hs₀).apply_symm_apply i)
  obtain ⟨b, c, a, hb, _, _, _, _, _, hLattice, _⟩ := hd v hvR s
  simp only [hs] at hLattice
  change (weightLattice b).map (d.j.restrictScalars ℤ) = integralWeights H φ at hLattice
  have hmem (x : RealRootSpace.E H) (hx : x ∈ weightLattice b) :
      d.j x ∈ integralWeights H φ := by
    rw [← hLattice]
    exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  have hf := positiveRoots_finite hR.toRootAxioms v
  let S := hf.toFinset
  let hS : (positive H φ).Finite := hpos ▸ hf.image d.j
  have hSF : hS.toFinset = S.image d.j := by
    ext α
    simp only [Set.Finite.mem_toFinset, Finset.mem_image, S]
    rw [← hpos]
    rfl
  have hρj : cartanRho H φ hS = d.j (rootRho R v) := by
    unfold cartanRho rootRho
    rw [hSF, Finset.sum_image hj.injOn, finsum_mem_eq_finite_toFinset_sum _ hf, map_smul, map_sum]
    rw [← IsScalarTower.algebraMap_smul ℂ (1 / 2 : ℝ)]
    congr 1
    norm_num [Complex.coe_algebraMap]
  have hρ : cartanRho H φ hS ∈ integralWeights H φ := hρj.symm ▸
    hmem (rootRho R v) (rho_mem_weightLattice hb hR hvR)
  have hP (α : Module.Dual ℂ H) (hα : α ∈ positive H φ) : α ∈ integralWeights H φ := by
    rw [← hpos] at hα
    obtain ⟨x, hx, rfl⟩ := hα
    exact hmem x (root_mem_weightLattice hb hR hx.1)
  obtain ⟨_, g, hg⟩ := LieAlgebrasAndRepresentations.FiniteModuleWeights.weyl_complexification H d
  have hact (w : rootWeylGroup R) (x : RealRootSpace.E H) : (g w).val (d.j x) = d.j (w.val x) := by
    exact (hg w x).symm
  have hW (w : weightWeylGroup H) (χ : Module.Dual ℂ H) (hχ : χ ∈ integralWeights H φ) :
      w.val χ ∈ integralWeights H φ := by
    rw [← hLattice] at hχ
    obtain ⟨x, hx, hχ⟩ := Submodule.mem_map.mp hχ
    change d.j x = χ at hχ
    obtain ⟨z, rfl⟩ := g.surjective w
    rw [← hχ, hact]
    exact hmem _ (weyl_mem_weightLattice hb hR hvR z hx)
  have hdet (w : rootWeylGroup R) :
      LinearMap.det (g w).val.toLinearMap = (sign w : ℂ) := by
    have hw : (g w).val = complexifyAutomorphism d w.val := by
      apply LinearEquiv.toLinearMap_injective
      apply LinearMap.ext_on d.roots_span
      intro α hα
      change (g w).val α = complexifyAutomorphism d w.val α
      rw [← d.extension_root α hα, complexifyAutomorphism_apply]
      exact hact w _
    rw [hw, complexify_det, ← sign_cast hR w]
    norm_cast
  have hsign (w : rootWeylGroup R) : cartanSign H (g w) = sign w := by
    unfold cartanSign
    rw [hdet]
    unfold sign
    split <;> norm_num
  letI := rootWeylGroup_finite hR
  letI : Finite (weightWeylGroup H) := Finite.of_injective g.symm g.symm.injective
  refine ⟨hS, hρ, hP, hW, ‹Finite (weightWeylGroup H)›, ?_, ?_⟩
  · intro w
    obtain ⟨z, rfl⟩ := g.surjective w
    change (cartanSign H (g z) : ℂ) = _
    rw [hsign, hdet]
  letI := Fintype.ofFinite (rootWeylGroup R)
  letI := Fintype.ofFinite (weightWeylGroup H)
  let incl := (integralWeights H φ).subtype.toAddMonoidHom
  let F := mapDomainRingHom ℤ incl
  let J := mapDomainRingHom ℤ d.j.toAddMonoidHom
  apply mapDomain_injective (f := incl) (by exact Subtype.val_injective)
  change F (cartanDenominator H φ hS hρ hP) =
    F (cartanAlternant H φ hW ⟨cartanRho H φ hS, hρ⟩)
  calc
    F (cartanDenominator H φ hS hρ hP) =
        J (denominator (rootRho R v) S id) := by
      unfold cartanDenominator F J
      rw [map_denominator, map_denominator]
      change denominator (cartanRho H φ hS) hS.toFinset
          (fun x => incl (if hx : x ∈ positive H φ then ⟨x, hP x hx⟩ else 0)) =
        denominator (d.j (rootRho R v)) S d.j
      rw [hρj]
      unfold denominator
      congr 1
      rw [hSF, Finset.prod_image hj.injOn]
      apply Finset.prod_congr rfl
      intro x hx
      have hxp : x ∈ positiveRoots R v := hf.mem_toFinset.mp hx
      have hx' : d.j x ∈ positive H φ := (extension_mem_positive d φ v hv x).mpr hxp
      simp [dite_eq_left hx']
      rfl
    _ = J (alternant sign (fun w : rootWeylGroup R => w.val (rootRho R v))) :=
      congrArg J (denominator_identity_ambient hR hvR)
    _ = F (cartanAlternant H φ hW ⟨cartanRho H φ hS, hρ⟩) := by
      unfold cartanAlternant F J
      rw [map_alternant, map_alternant]
      change alternant sign (fun w : rootWeylGroup R => d.j (w.val (rootRho R v))) =
        alternant (cartanSign H) (fun w : weightWeylGroup H => w.val (cartanRho H φ hS))
      rw [hρj]
      simp only [alternant, finsum_eq_sum_of_fintype]
      rw [← Equiv.sum_comp g.toEquiv]
      apply Finset.sum_congr rfl
      intro w _
      rw [show g.toEquiv w = g w from rfl, hsign, hact]

/-- In rank zero the denominator is the unit of the integral group ring. -/
theorem cartan_rank_zero (H : LieSubalgebra ℂ L) (φ : Direction H)
    (hS : (positive H φ).Finite) (hρ : cartanRho H φ hS ∈ integralWeights H φ)
    (hP : ∀ a ∈ positive H φ, a ∈ integralWeights H φ) (hR : rootSet_value H = ∅) :
    cartanDenominator H φ hS hρ hP = 1 := by
  have hEmpty : hS.toFinset = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have h := (hS.mem_toFinset.mp ha).1
    simp [hR] at h
  have hr : cartanRho H φ hS = 0 := by simp [cartanRho, hEmpty]
  have hr' : (⟨cartanRho H φ hS, hρ⟩ : integralWeights H φ) = 0 := Subtype.ext hr
  unfold cartanDenominator denominator
  rw [hr', hEmpty, Finset.prod_empty, mul_one, AddMonoidAlgebra.one_def]

end Cartan

end LieAlgebrasAndRepresentations.WeylDenominator
