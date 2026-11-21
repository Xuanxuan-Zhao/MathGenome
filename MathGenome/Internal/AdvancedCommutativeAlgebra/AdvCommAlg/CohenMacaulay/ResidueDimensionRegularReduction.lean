import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.ResidueDimensionRegularReduction
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.AuslanderBuchsbaum
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.RegularQuotient
import Mathlib.RingTheory.Regular.Free
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Ideal.Cotangent

/-! CM-19: reduce the first syzygy m modulo x. The module m/xm has finite
projective dimension over R/(x). The nonzero class of x in m/m² supplies
a retraction onto k. Auslander–Buchsbaum then gives the exact dimension. -/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped Pointwise
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
namespace AdvCommAlg.CohenMacaulay

variable {R : Type u} [CommRing R]

/-- Reducing a short exact sequence modulo x remains injective on the left
when x is regular on its last term. -/
lemma quotSMulTop_map_injective (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (x : R) (hx : IsSMulRegular S.X₃ x) :
    Function.Injective (QuotSMulTop.map x S.f.hom) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm _ bot_le
  intro z hz
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (x • (⊤ : Submodule R S.X₁)) z
  have ha : S.f.hom a ∈ x • (⊤ : Submodule R S.X₂) := by
    exact (Submodule.Quotient.mk_eq_zero _).mp hz
  obtain ⟨b, _, hb⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp ha
  have hgb : S.g.hom b = 0 := by
    apply hx.right_eq_zero_of_smul
    rw [← map_smul, hb]
    exact S.moduleCat_zero_apply a
  obtain ⟨c, hc⟩ := (S.moduleCat_exact_iff.mp hS.exact) b hgb
  have hac : x • c = a := by
    apply hS.moduleCat_injective_f
    rw [map_smul, hc]
    exact hb
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (hac ▸ Submodule.smul_mem_pointwise_smul c x ⊤ trivial)

/-- The quotient short exact sequence, with its quotient-ring scalar action. -/
noncomputable def quotientShortComplex (S : ShortComplex (ModuleCat.{u} R)) (x : R) :
    ShortComplex (ModuleCat.{u} (R ⧸ Ideal.span {x})) :=
  ShortComplex.moduleCatMk
    ((QuotSMulTop.map x S.f.hom).extendScalarsOfSurjective Ideal.Quotient.mk_surjective)
    ((QuotSMulTop.map x S.g.hom).extendScalarsOfSurjective Ideal.Quotient.mk_surjective)
    (by
      ext z
      obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (x • (⊤ : Submodule R S.X₁)) z
      change Submodule.Quotient.mk (S.g.hom (S.f.hom a)) =
        (0 : QuotSMulTop x S.X₃)
      rw [S.moduleCat_zero_apply, Submodule.Quotient.mk_zero])

lemma quotientShortComplex_shortExact (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (x : R) (hx : IsSMulRegular S.X₃ x) :
    (quotientShortComplex S x).ShortExact := by
  have hi : Mono (quotientShortComplex S x).f :=
    (ModuleCat.mono_iff_injective _).mpr (quotSMulTop_map_injective S hS x hx)
  have hs : Epi (quotientShortComplex S x).g :=
    (ModuleCat.epi_iff_surjective _).mpr
      (QuotSMulTop.map_surjective x hS.moduleCat_surjective_g)
  refine { exact := ?_ }
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  exact QuotSMulTop.map_exact x
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact)
    hS.moduleCat_surjective_g

/-- A finite projective-dimension bound descends when both the ring and the
module are regular for x. Exactness is proved on every reduced first step. -/
lemma quotient_hasProjectiveDimensionLE [IsNoetherianRing R] [IsLocalRing R]
    (x : R) (hxR : IsSMulRegular R x) (n : ℕ)
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (hM : HasProjectiveDimensionLE M n) (hxM : IsSMulRegular M x) :
    HasProjectiveDimensionLE
      (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) n := by
  induction n generalizing M with
  | zero =>
    have : Projective M := (projective_iff_hasProjectiveDimensionLE_zero M).mpr hM
    have : Module.Projective R M := inferInstance
    have : Module.Free R M := finite_projective_free M
    infer_instance
  | succ n ih =>
    obtain ⟨F, hFfin, hFfree, f, hf, _⟩ := exists_minimalFreeCover M
    letI := hFfin
    letI := hFfree
    let S := f.hom.shortComplexKer
    have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hf
    have : Module.Finite R S.X₁ := inferInstanceAs (Module.Finite R (LinearMap.ker f.hom))
    have : Module.Free R S.X₂ := hFfree
    have hK : HasProjectiveDimensionLE S.X₁ n :=
      hS.hasProjectiveDimensionLT_X₁ (n + 1) inferInstance hM
    have hxF : IsSMulRegular F x :=
      Module.Flat.isSMulRegular_of_isRegular
        ((Commute.isRegular_iff (fun a => mul_comm x a)).mpr hxR)
    have hxK : IsSMulRegular S.X₁ x :=
      hxF.of_injective S.f.hom hS.moduleCat_injective_f
    have hQK := ih S.X₁ hK hxK
    let T := quotientShortComplex S x
    have hT : T.ShortExact := quotientShortComplex_shortExact S hS x hxM
    have : Module.Free (R ⧸ Ideal.span {x}) T.X₂ := by
      change Module.Free (R ⧸ Ideal.span {x}) (QuotSMulTop x F)
      infer_instance
    exact hT.hasProjectiveDimensionLT_X₃ (n + 1) hQK inferInstance

/-- The class of a minimal generator splits off a copy of the residue field
from m/xm. This is exactly where x outside m² is used. -/
lemma residueField_retract_quotient_maximalIdeal [IsLocalRing R]
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hx₂ : x ∉ (IsLocalRing.maximalIdeal R) ^ 2) :
    letI := residueFieldQuotientModule x hx
    Nonempty (Retract
      (ModuleCat.of (R ⧸ Ideal.span {x}) (IsLocalRing.ResidueField R))
      (ModuleCat.of (R ⧸ Ideal.span {x})
        (QuotSMulTop x (IsLocalRing.maximalIdeal R)))) := by
  classical
  letI := residueFieldQuotientModule x hx
  let m := IsLocalRing.maximalIdeal R
  let v : m := ⟨x, hx⟩
  have hv : m.toCotangent v ≠ 0 := by
    exact fun h => hx₂ ((m.toCotangent_eq_zero v).mp h)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one
    (IsLocalRing.ResidueField R) hv
  let j : R →ₗ[R] QuotSMulTop x m :=
    LinearMap.toSpanSingleton R _ (Submodule.Quotient.mk v)
  have hj : m ≤ LinearMap.ker j := by
    intro a ha
    change Submodule.Quotient.mk (a • v) = (0 : QuotSMulTop x m)
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    have heq : a • v = x • (⟨a, ha⟩ : m) := by
      apply Subtype.ext
      exact mul_comm a x
    rw [heq]
    exact Submodule.smul_mem_pointwise_smul _ x ⊤ trivial
  let i : IsLocalRing.ResidueField R →ₗ[R] QuotSMulTop x m := m.liftQ j hj
  have hq : x • (⊤ : Submodule R m) ≤ LinearMap.ker m.toCotangent := by
    intro z hz
    obtain ⟨a, _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hz
    apply (m.toCotangent_eq_zero _).mpr
    change x * (a : R) ∈ m ^ 2
    rw [pow_two]
    exact Ideal.mul_mem_mul hx a.property
  let q : QuotSMulTop x m →ₗ[R] m.Cotangent :=
    (x • (⊤ : Submodule R m)).liftQ m.toCotangent hq
  let r : QuotSMulTop x m →ₗ[R] IsLocalRing.ResidueField R :=
    φ.restrictScalars R ∘ₗ q
  have hri : r.comp i = LinearMap.id := by
    apply LinearMap.ext
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    change φ (m.toCotangent (a • v)) = IsLocalRing.residue R a
    rw [map_smul]
    calc
      φ (a • m.toCotangent v) = a • φ (m.toCotangent v) :=
        (φ.restrictScalars R).map_smul a _
      _ = IsLocalRing.residue R a := by simp [hφ, Algebra.smul_def]
  refine ⟨⟨ModuleCat.ofHom
    (i.extendScalarsOfSurjective Ideal.Quotient.mk_surjective),
    ModuleCat.ofHom (r.extendScalarsOfSurjective Ideal.Quotient.mk_surjective), ?_⟩⟩
  apply ModuleCat.hom_ext
  ext a
  exact DFunLike.congr_fun hri a

/-- Finiteness over the quotient comes from the reduced first syzygy,
followed by the residue-field retraction. No regularity criterion is used. -/
lemma residueField_quotient_hasProjectiveDimensionLE
    [IsNoetherianRing R] [IsLocalRing R] (q : ℕ)
    (hn : projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
      ((q + 1 : ℕ) : WithBot ℕ∞))
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hx₂ : x ∉ (IsLocalRing.maximalIdeal R) ^ 2) (hxR : IsSMulRegular R x) :
    letI := residueFieldQuotientModule x hx
    HasProjectiveDimensionLE
      (ModuleCat.of (R ⧸ Ideal.span {x}) (IsLocalRing.ResidueField R)) q := by
  let m := IsLocalRing.maximalIdeal R
  let S := ShortComplex.moduleCatMk m.subtype m.mkQ
    (by ext a; exact Ideal.Quotient.eq_zero_iff_mem.mpr a.property)
  have hS : S.ShortExact := by
    have : Mono S.f := (ModuleCat.mono_iff_injective _).mpr m.injective_subtype
    have : Epi S.g := (ModuleCat.epi_iff_surjective _).mpr m.mkQ_surjective
    refine { exact := ?_ }
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact m.range_subtype.trans m.ker_mkQ.symm
  have hk : HasProjectiveDimensionLE S.X₃ (q + 1) :=
    (projectiveDimension_le_iff _ _).mp hn.le
  have : Projective S.X₂ := inferInstanceAs (Projective (ModuleCat.of R R))
  have hm : HasProjectiveDimensionLE S.X₁ q :=
    hS.hasProjectiveDimensionLT_X₁ (q + 1) inferInstance hk
  have hxm : IsSMulRegular m x := hxR.submodule m x
  have hQ := quotient_hasProjectiveDimensionLE x hxR q
    (ModuleCat.of R m) hm hxm
  letI := residueFieldQuotientModule x hx
  obtain ⟨r⟩ := residueField_retract_quotient_maximalIdeal x hx hx₂
  exact r.hasProjectiveDimensionLT (q + 1)

lemma residueField_depth_zero [IsNoetherianRing R] [IsLocalRing R] :
    Depth.depth R (IsLocalRing.ResidueField R) = 0 := by
  rw [Depth.depth_eq_residueDepth (ModuleCat.of R (IsLocalRing.ResidueField R))]
  apply (ModuleCat.depth_eq_zero_iff_nontrivial_linearMap _ _).mpr
  infer_instance

lemma quotient_residueField_depth_zero [IsNoetherianRing R] [IsLocalRing R]
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R)
    [IsLocalRing (R ⧸ Ideal.span {x})] :
    letI := residueFieldQuotientModule x hx
    Depth.depth (R ⧸ Ideal.span {x}) (IsLocalRing.ResidueField R) = 0 := by
  letI := residueFieldQuotientModule x hx
  change Depth.grade (IsLocalRing.maximalIdeal (R ⧸ Ideal.span {x})) _ = 0
  rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk (Ideal.span {x}))
    Ideal.Quotient.mk_surjective]
  exact (Depth.grade_map_of_surjective (R := R) (S := R ⧸ Ideal.span {x})
    (IsLocalRing.ResidueField R) Ideal.Quotient.mk_surjective
    (IsLocalRing.maximalIdeal R)).trans residueField_depth_zero

lemma depth_quotient_ring [IsNoetherianRing R] [IsLocalRing R]
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) (hxR : IsSMulRegular R x)
    [IsLocalRing (R ⧸ Ideal.span {x})] :
    Depth.depth (R ⧸ Ideal.span {x}) (R ⧸ Ideal.span {x}) = Depth.depth R R - 1 := by
  have hreg : RingTheory.Sequence.IsRegular R [x] := by
    refine ⟨(RingTheory.Sequence.isWeaklyRegular_singleton_iff R x).mpr hxR, ?_⟩
    simpa only [Ideal.ofList_singleton, Ideal.smul_eq_mul, Ideal.mul_top] using
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top
        (Ideal.span_le.mpr (by simpa using hx))).symm
  have hmem : ∀ a ∈ [x], a ∈ IsLocalRing.maximalIdeal R := by simpa using hx
  have hI : IsLocalRing.maximalIdeal R • (⊤ : Submodule R R) ≠ ⊤ := by
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  have h := Depth.grade_quotient_regular R (IsLocalRing.maximalIdeal R) hI [x] hreg hmem
  have he : (Ideal.ofList [x] • (⊤ : Submodule R R)) = Ideal.span {x} := by
    rw [Ideal.ofList_singleton, Ideal.smul_eq_mul, Ideal.mul_top]
  let e := Submodule.quotEquivOfEq _ _ he
  change Depth.grade (IsLocalRing.maximalIdeal (R ⧸ Ideal.span {x})) _ = _
  rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk (Ideal.span {x}))
    Ideal.Quotient.mk_surjective]
  have hcongr := (IsLocalRing.maximalIdeal R).depth_eq_of_iso e.toModuleIso
  rw [← Depth.grade_eq_idealDepth, ← Depth.grade_eq_idealDepth] at hcongr
  calc
    _ = Depth.grade (IsLocalRing.maximalIdeal R) (R ⧸ Ideal.span {x}) :=
      Depth.grade_map_of_surjective (R := R) (S := R ⧸ Ideal.span {x})
        (R ⧸ Ideal.span {x}) Ideal.Quotient.mk_surjective (IsLocalRing.maximalIdeal R)
    _ = Depth.grade (IsLocalRing.maximalIdeal R)
        (R ⧸ (Ideal.ofList [x] • (⊤ : Submodule R R))) := hcongr.symm
    _ = _ := by simpa only [Depth.depth_eq_grade, List.length_singleton, Nat.cast_one] using h

/-- CM-19, the finite projective-dimension reduction by a regular minimal generator. -/
theorem residueField_projectiveDimension_quotient :
    Specs.residueField_projectiveDimension_quotientType := by
  intro R _ _ _ n hnpos hn x hx hx₂ hxR
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
  let B := R ⧸ Ideal.span {x}
  have hle : Ideal.span {x} ≤ IsLocalRing.maximalIdeal R :=
    Ideal.span_le.mpr (by simpa using hx)
  letI : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hle)
  letI : IsLocalRing B :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  letI := residueFieldQuotientModule x hx
  let k := ModuleCat.of B (IsLocalRing.ResidueField R)
  have : Module.Finite B k :=
    Module.Finite.of_restrictScalars_finite R B (IsLocalRing.ResidueField R)
  have hfin : HasProjectiveDimensionLE k q :=
    residueField_quotient_hasProjectiveDimensionLE q hn x hx hx₂ hxR
  have hbound : projectiveDimension k ≤ (q : WithBot ℕ∞) :=
    (projectiveDimension_le_iff k q).mpr hfin
  have hbot : projectiveDimension k ≠ ⊥ := by
    intro hz
    have hs := ModuleCat.isZero_iff_subsingleton.mp
      ((projectiveDimension_eq_bot_iff k).mp hz)
    exact not_subsingleton_iff_nontrivial.mpr (inferInstance : Nontrivial k) hs
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hbot
  have hdq : d ≤ (q : ℕ∞) := by
    exact WithBot.coe_le_coe.mp (hd.symm ▸ hbound)
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top (by simp : (q : ℕ∞) ≠ ⊤) hdq)
  have hp : projectiveDimension k = (e : WithBot ℕ∞) :=
    hd.symm.trans (congrArg (fun t : ℕ∞ => (t : WithBot ℕ∞)) he.symm)
  have hdR := Depth.auslanderBuchsbaum
    (ModuleCat.of R (IsLocalRing.ResidueField R)) (q + 1) hn
  rw [residueField_depth_zero, add_zero] at hdR
  have hdB : Depth.depth B B = (q : ℕ∞) := by
    rw [depth_quotient_ring x hx hxR, ← hdR]
    simp
  have hAB := Depth.auslanderBuchsbaum k e hp
  rw [quotient_residueField_depth_zero x hx, add_zero, hdB] at hAB
  have heq : e = q := by exact_mod_cast hAB
  simpa only [Nat.succ_sub_one, heq] using hp

end AdvCommAlg.CohenMacaulay
