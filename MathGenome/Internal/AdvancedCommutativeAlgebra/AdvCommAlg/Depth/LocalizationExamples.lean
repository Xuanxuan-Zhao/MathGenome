import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.LocalizationExamples
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.DimensionBounds
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.ZeroTest
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Localization.Algebra

/-! The two examples of depth changing under localization, paper.tex:3019–3023. -/

noncomputable section
set_option maxHeartbeats 800000
open scoped Pointwise
open Polynomial RingTheory.Sequence
universe u
namespace AdvCommAlg.Depth.LocalizationExamples

variable (k : Type u) [Field k]

theorem originIdeal_eq_span : originIdeal k = Ideal.span {X, C X} := by
  apply le_antisymm
  · intro f hf
    have hf0 : (f.coeff 0).coeff 0 = 0 := hf
    obtain ⟨g, hg⟩ := (Polynomial.X_dvd_iff).mpr hf0
    have hd : X ∣ f - C (f.coeff 0) := by
      apply Polynomial.X_dvd_iff.mpr
      simp
    obtain ⟨h, hh⟩ := hd
    have hc : C (f.coeff 0) ∈ (Ideal.span {X, C X} : Ideal (Plane k)) := by
      rw [hg, map_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    have hx : f - C (f.coeff 0) ∈ (Ideal.span {X, C X} : Ideal (Plane k)) := by
      rw [hh]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    simpa using (Ideal.span {X, C X} : Ideal (Plane k)).add_mem hx hc
  · apply Ideal.span_le.mpr
    intro f hf
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl <;> simp [originIdeal, RingHom.mem_ker, originEvaluation]

theorem maximalIdeal_eq_span : Specs.maximalIdealType.{u} := by
  intro k _
  calc
    IsLocalRing.maximalIdeal (LocalPlane k) =
        (originIdeal k).map (algebraMap (Plane k) (LocalPlane k)) :=
      (Localization.AtPrime.map_eq_maximalIdeal (I := originIdeal k)).symm
    _ = (Ideal.span {X, C X}).map (algebraMap (Plane k) (LocalPlane k)) :=
      congrArg (fun I : Ideal (Plane k) => I.map (algebraMap (Plane k) (LocalPlane k)))
        (originIdeal_eq_span k)
    _ = Ideal.span {x k, y k} := by
      simp only [Ideal.map_span, Set.image_insert_eq, Set.image_singleton, x, y]

theorem localAxisIdeal_eq_span : Specs.localAxisIdealType.{u} := by
  intro k _
  simp [localAxisIdeal, axisIdeal, Polynomial.ker_constantCoeff, Ideal.map_span, x]

/-- Evaluation of the outer polynomial variable identifies the first quotient. -/
def quotientXEquiv : QuotSMulTop (X : Plane k) (Plane k) ≃+* Polynomial k := by
  have he : (X : Plane k) • (⊤ : Ideal (Plane k)) = Ideal.span {(X : Plane k) - C (0 : Polynomial k)} := by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
    simp
  exact (Ideal.quotientEquivAlgOfEq (Polynomial k) he).toRingEquiv.trans
    (Polynomial.quotientSpanXSubCAlgEquiv 0).toRingEquiv

@[simp] theorem quotientXEquiv_mk (f : Plane k) :
    quotientXEquiv k (Submodule.Quotient.mk f) = f.eval 0 := by
  simp [quotientXEquiv, Ideal.quotientEquivAlgOfEq_mk]

theorem planeParameters_weaklyRegular :
    IsWeaklyRegular (Plane k) [(X : Plane k), C (X : Polynomial k)] := by
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff]
  refine ⟨Polynomial.isRegular_X.left, ?_⟩
  intro a b hab
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  apply (quotientXEquiv k).injective
  change a.eval 0 = b.eval 0
  apply Polynomial.isRegular_X.left
  have h := congrArg (quotientXEquiv k) hab
  change (C X * a).eval 0 = (C X * b).eval 0 at h
  simpa using h

theorem parameters_regular : Specs.parametersRegularType.{u} := by
  intro k _
  have h := (planeParameters_weaklyRegular k).isRegular_of_isLocalization_of_mem
    (LocalPlane k) (originIdeal k) (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl <;>
        simp [originIdeal, RingHom.mem_ker, originEvaluation])
  exact h

theorem dimension_le_two : ringKrullDim (LocalPlane k) ≤ 2 := by
  have h : ringKrullDim (LocalPlane k) ≤ ringKrullDim (Plane k) := by
    let e := IsLocalization.AtPrime.primeSpectrumOrderIso (LocalPlane k) (originIdeal k)
    exact Order.krullDim_le_of_strictMono (fun p => (e p).val) (fun _ _ h => e.strictMono h)
  calc
    ringKrullDim (LocalPlane k) ≤ ringKrullDim (Plane k) := h
    _ = 2 := by norm_num [Plane, Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]

theorem dimension_eq_two : Specs.dimensionType.{u} := by
  intro k _
  apply le_antisymm (dimension_le_two k)
  letI : Module.Finite (LocalPlane k) (LocalPlane k) := Module.Finite.self _
  have h := regular_length_le_supportDim (R := LocalPlane k) (LocalPlane k) [x k, y k] (parameters_regular k)
  simpa [Module.supportDim_self_eq_ringKrullDim] using h

theorem depth_eq_two : Specs.ringDepthType.{u} := by
  intro k _
  change depth (LocalPlane k) (LocalPlane k) = 2
  letI : Module.Finite (LocalPlane k) (LocalPlane k) := Module.Finite.self _
  have hproper : IsLocalRing.maximalIdeal (LocalPlane k) •
      (⊤ : Submodule (LocalPlane k) (LocalPlane k)) ≠ ⊤ := by
    simpa using (IsLocalRing.maximalIdeal.isMaximal (LocalPlane k)).ne_top
  apply le_antisymm
  · have h := depth_le_supportDim (R := LocalPlane k) (LocalPlane k)
    rw [Module.supportDim_self_eq_ringKrullDim, dimension_eq_two k] at h
    exact WithBot.coe_le_coe.mp h
  · rw [depth_eq_grade, grade_of_smul_ne_top _ _ hproper]
    apply le_sSup
    refine ⟨[x k, y k], parameters_regular k, ?_, by simp⟩
    intro a ha
    rw [maximalIdeal_eq_span k]
    exact Ideal.subset_span (by simpa using ha)

@[simp] theorem residueMap_algebraMap (f : Plane k) :
    residueMap k (algebraMap (Plane k) (LocalPlane k) f) = originEvaluation k f :=
  IsLocalization.lift_eq _ _

theorem residueMap_surjective : Function.Surjective (residueMap k) := by
  intro a
  exact ⟨algebraMap (Plane k) (LocalPlane k) (C (C a)), by simp [originEvaluation]⟩

instance finiteResidue : Module.Finite (LocalPlane k) k :=
  Module.Finite.of_surjective (Algebra.linearMap (LocalPlane k) k) (residueMap_surjective k)

theorem residueMap_ker : RingHom.ker (residueMap k) = IsLocalRing.maximalIdeal (LocalPlane k) :=
  IsLocalRing.ker_eq_maximalIdeal _ (residueMap_surjective k)

@[simp] theorem residueMap_y : residueMap k (y k) = 0 := by
  simp [y, originEvaluation]

theorem module_depth_eq_zero : Specs.moduleDepthType.{u} := by
  intro k _
  change depth (LocalPlane k) (SplitModule k) = 0
  apply (depth_zero_iff_socle_ne_bot (LocalPlane k) (SplitModule k)).mpr
  have hw : ((0, 1) : SplitModule k) ∈ Submodule.torsionBySet (LocalPlane k)
      (SplitModule k) (IsLocalRing.maximalIdeal (LocalPlane k) : Set (LocalPlane k)) := by
    rw [Submodule.mem_torsionBySet_iff]
    intro a
    have ha : residueMap k a = 0 := by
      exact (show a.val ∈ RingHom.ker (residueMap k) from (residueMap_ker k).symm ▸ a.property)
    ext
    · simp
    · change residueMap k a * 1 = 0
      rw [ha, zero_mul]
  intro hbot
  have hz : ((0, 1) : SplitModule k) = 0 := by simpa [hbot] using hw
  exact one_ne_zero (congrArg Prod.snd hz)

theorem y_not_mem_localAxis : y k ∉ localAxisIdeal k := by
  have hu := IsLocalization.under_map_of_isPrime_disjoint
    (originIdeal k).primeCompl (LocalPlane k) (axisIdeal_isPrime k)
    (Set.disjoint_left.mpr fun _ hs hp => hs (axisIdeal_le_originIdeal k hp))
  intro hy
  have h : C (X : Polynomial k) ∈ axisIdeal k := by
    rw [← hu]
    exact hy
  change Polynomial.constantCoeff (C (X : Polynomial k)) = 0 at h
  simpa using h

/-- The first projection becomes a localization map because y kills the second summand. -/
def splitProjection : SplitModule k →ₗ[LocalPlane k] AxisLocalization k :=
  (Algebra.linearMap (LocalPlane k) (AxisLocalization k)).comp
    (LinearMap.fst (LocalPlane k) (LocalPlane k) k)

instance splitProjection_isLocalizedModule :
    IsLocalizedModule (localAxisIdeal k).primeCompl (splitProjection k) where
  map_units := IsLocalizedModule.map_units
    (Algebra.linearMap (LocalPlane k) (AxisLocalization k))
  surj z := by
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (localAxisIdeal k).primeCompl z
    refine ⟨((a, 0), s), ?_⟩
    simpa [splitProjection, Submonoid.smul_def, Algebra.smul_def, mul_comm] using hs
  exists_of_eq {a b} h := by
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (localAxisIdeal k).primeCompl
      (AxisLocalization k)).mp h
    refine ⟨c * ⟨y k, y_not_mem_localAxis k⟩, ?_⟩
    ext
    · change (c.val * y k) * a.1 = (c.val * y k) * b.1
      calc
        (c.val * y k) * a.1 = y k * (c.val * a.1) := by ring
        _ = y k * (c.val * b.1) := congrArg (fun z => y k * z) hc
        _ = (c.val * y k) * b.1 := by ring
    · change residueMap k (c.val * y k) * a.2 = residueMap k (c.val * y k) * b.2
      simp

def localizedSplitEquiv : LocalizedSplitModule k ≃ₗ[AxisLocalization k] AxisLocalization k :=
  (IsLocalizedModule.linearEquiv (localAxisIdeal k).primeCompl
    (LocalizedModule.mkLinearMap (localAxisIdeal k).primeCompl (SplitModule k))
    (splitProjection k)).extendScalarsOfIsLocalization (localAxisIdeal k).primeCompl
      (AxisLocalization k)

theorem localizedModule_equiv : Specs.localizedModuleEquivType.{u} :=
  fun k _ => ⟨localizedSplitEquiv k⟩

/-- Local depth is unchanged by a linear isomorphism of modules. -/
lemma depth_congr {R : Type*} [CommRing R] [IsLocalRing R]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (e : M ≃ₗ[R] N) : depth R M = depth R N := by
  classical
  have ht : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) = ⊤ ↔
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R N) = ⊤ := by
    rw [← Submodule.map_injective_of_injective e.injective |>.eq_iff]
    simp only [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective]
  by_cases hm : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) = ⊤
  · rw [depth_eq_grade, depth_eq_grade, grade_of_smul_eq_top _ _ hm,
      grade_of_smul_eq_top _ _ (ht.mp hm)]
  · rw [depth_eq_grade, depth_eq_grade, grade_of_smul_ne_top _ _ hm,
      grade_of_smul_ne_top _ _ (mt ht.mpr hm)]
    congr 1
    ext n
    constructor <;> rintro ⟨xs, hx, hmem, rfl⟩
    · exact ⟨xs, (e.isRegular_congr xs).mp hx, hmem, rfl⟩
    · exact ⟨xs, (e.isRegular_congr xs).mpr hx, hmem, rfl⟩

lemma depth_eq_one_of_principal_maximalIdeal {S : Type*} [CommRing S]
    [IsNoetherianRing S] [IsLocalRing S] [IsDomain S] (t : S) (ht : t ≠ 0)
    (hm : IsLocalRing.maximalIdeal S = Ideal.span {t}) : depth S S = 1 := by
  have hproper : IsLocalRing.maximalIdeal S • (⊤ : Submodule S S) ≠ ⊤ := by
    simpa using (IsLocalRing.maximalIdeal.isMaximal S).ne_top
  have hr : IsRegular S [t] := by
    refine ⟨(isWeaklyRegular_singleton_iff S t).mpr ?_, ?_⟩
    · exact mul_right_injective₀ ht
    · simpa only [Ideal.ofList_singleton, ← hm] using hproper.symm
  apply le_antisymm
  · have hd := depth_le_supportDim (R := S) S
    rw [Module.supportDim_self_eq_ringKrullDim] at hd
    have hb : ringKrullDim S ≤ 1 := by
      apply (ringKrullDim_le_spanFinrank_maximalIdeal S).trans
      rw [hm]
      exact_mod_cast (Submodule.spanFinrank_span_le_ncard_of_finite (R := S)
        (Set.finite_singleton t)).trans (by simp)
    exact WithBot.coe_le_coe.mp (hd.trans hb)
  · rw [depth_eq_grade, grade_of_smul_ne_top _ _ hproper]
    exact le_sSup ⟨[t], hr, by simpa [hm] using (Ideal.subset_span (Set.mem_singleton t)), by simp⟩

theorem localized_ring_depth_eq_one : Specs.localizedRingDepthType.{u} := by
  intro k _
  let t := algebraMap (LocalPlane k) (AxisLocalization k) (x k)
  have hx : x k ≠ 0 := by
    intro h
    apply Polynomial.X_ne_zero (R := Polynomial k)
    apply IsLocalization.injective (LocalPlane k) (originIdeal k).primeCompl_le_nonZeroDivisors
    simpa [x] using h
  have ht : t ≠ 0 := by
    have h := (IsLocalization.injective (AxisLocalization k)
      (localAxisIdeal k).primeCompl_le_nonZeroDivisors).ne hx
    simpa [t] using h
  have hm : IsLocalRing.maximalIdeal (AxisLocalization k) = Ideal.span {t} := by
    calc
      _ = (localAxisIdeal k).map (algebraMap (LocalPlane k) (AxisLocalization k)) :=
        (Localization.AtPrime.map_eq_maximalIdeal (I := localAxisIdeal k)).symm
      _ = (Ideal.span {x k}).map (algebraMap (LocalPlane k) (AxisLocalization k)) :=
        congrArg (fun I : Ideal (LocalPlane k) =>
          I.map (algebraMap (LocalPlane k) (AxisLocalization k))) (localAxisIdeal_eq_span k)
      _ = Ideal.span {t} := by rw [Ideal.map_span, Set.image_singleton]
  exact depth_eq_one_of_principal_maximalIdeal t ht hm

theorem localized_module_depth_eq_one : Specs.localizedModuleDepthType.{u} := by
  intro k _
  change depth (AxisLocalization k) (LocalizedSplitModule k) = 1
  rw [depth_congr (localizedSplitEquiv k)]
  exact localized_ring_depth_eq_one k

/-- Both iterated localizations invert precisely the complement of (x) in k[y][x]. -/
theorem localization_equiv : Specs.localizationEquivType.{u} := by
  intro k _
  letI : Algebra (Plane k) (GenericLine k) := Polynomial.algebra (Polynomial k) (RatFunc k)
  let T := (nonZeroDivisors (Polynomial k)).map (Polynomial.C : Polynomial k →+* Plane k)
  letI : IsLocalization T (GenericLine k) := Polynomial.isLocalization _ _
  have hc : (genericAxisIdeal k).comap (algebraMap (Plane k) (GenericLine k)) = axisIdeal k := by
    ext f
    change ((f.map (algebraMap (Polynomial k) (RatFunc k))).coeff 0 = 0) ↔ f.coeff 0 = 0
    rw [Polynomial.coeff_map]
    exact (map_eq_zero_iff _ (IsFractionRing.injective (Polynomial k) (RatFunc k)))
  have hu : (localAxisIdeal k).comap (algebraMap (Plane k) (LocalPlane k)) = axisIdeal k :=
    IsLocalization.under_map_of_isPrime_disjoint
      (originIdeal k).primeCompl (LocalPlane k) (axisIdeal_isPrime k)
      (Set.disjoint_left.mpr fun _ hs hp => hs (axisIdeal_le_originIdeal k hp))
  have h₁ := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (originIdeal k).primeCompl (AxisLocalization k) (localAxisIdeal k)
  have h₂ := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    T (GenericLocalLine k) (genericAxisIdeal k)
  have he₁ : ((localAxisIdeal k).comap (algebraMap (Plane k) (LocalPlane k))).primeCompl =
      (axisIdeal k).primeCompl := by
    ext f
    change (f ∉ (localAxisIdeal k).comap (algebraMap (Plane k) (LocalPlane k))) ↔ f ∉ axisIdeal k
    rw [hu]
  have he₂ : ((genericAxisIdeal k).comap (algebraMap (Plane k) (GenericLine k))).primeCompl =
      (axisIdeal k).primeCompl := by
    ext f
    change (f ∉ (genericAxisIdeal k).comap (algebraMap (Plane k) (GenericLine k))) ↔ f ∉ axisIdeal k
    rw [hc]
  change IsLocalization _ (AxisLocalization k) at h₁
  change IsLocalization _ (GenericLocalLine k) at h₂
  rw [he₁] at h₁
  rw [he₂] at h₂
  letI := h₁
  letI := h₂
  exact ⟨(IsLocalization.algEquiv (axisIdeal k).primeCompl
    (AxisLocalization k) (GenericLocalLine k)).toRingEquiv⟩

end AdvCommAlg.Depth.LocalizationExamples
