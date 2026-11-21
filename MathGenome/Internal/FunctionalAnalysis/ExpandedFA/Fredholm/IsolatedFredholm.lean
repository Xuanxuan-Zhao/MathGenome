import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.IsolatedFredholm
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.LocalSpectralAlternatives
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.RieszPoles
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

noncomputable section
namespace ExpandedFA.Fredholm.IsolatedFredholm
open Set Filter
open scoped Topology
open BanachAlgebra BanachAlgebra.RieszSplitting BanachAlgebra.RieszPoles
universe u

section Banach
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [CompleteSpace X] in
/-- Compression of a compact operator to a projection range is compact. -/
lemma compact_compress (P K : X →L[ℂ] X)
    (hK : Compactness.IsCompactLinearMap K.toLinearMap) :
    Compactness.IsCompactLinearMap (compressBlock P K).toLinearMap := by
  have h := (Compactness.compact_iff_isCompactOperator _).mp hK
  exact (Compactness.compact_iff_isCompactOperator _).mpr
    ((h.comp_clm P.range.subtypeL).clm_comp P.rangeRestrict)

/-- Fredholmness passes to an invariant complemented block. -/
lemma fredholm_block (A P : X →L[ℂ] X) (hP : P * P = P) (hc : Commute A P)
    (hcl : IsClosed (P.range : Set X))
    (B : P.range →L[ℂ] P.range) (hB : ∀ x : P.range, (B x : X) = A x)
    (hA : IsFredholm A) : IsFredholm B := by
  let : CompleteSpace P.range := hcl.completeSpace_coe
  obtain ⟨S, hS₁, hS₂⟩ := (atkinson_compact A).mp hA
  apply isFredholm_of_compact_parametrix B (compressBlock P S)
  · have he : (compressBlock P S).comp B - ContinuousLinearMap.id ℂ P.range =
        compressBlock P (S.comp A - ContinuousLinearMap.id ℂ X) := by
      ext x
      change P (S (B x)) - (x : X) = P (S (A x) - x)
      rw [hB, map_sub, projection_fixed hP x.property]
    rw [he]
    exact compact_compress P _ hS₁
  · have he : B.comp (compressBlock P S) - ContinuousLinearMap.id ℂ P.range =
        compressBlock P (A.comp S - ContinuousLinearMap.id ℂ X) := by
      ext x
      change (B (compressBlock P S x) : X) - x = P (A (S x) - x)
      rw [hB]
      change A (P (S x)) - x = P (A (S x) - x)
      rw [map_sub, projection_fixed hP x.property]
      exact congrArg (fun y => y - (x : X))
        (congrArg (fun Q : X →L[ℂ] X => Q (S x)) hc.eq)
    rw [he]
    exact compact_compress P _ hS₂

/-- A Fredholm operator with singleton spectrum acts on a finite-dimensional
space: otherwise its Calkin class has a nonempty spectrum contained in that
singleton, although that point is in its resolvent. -/
lemma finite_of_singleton_fredholm (B : X →L[ℂ] X) (lam : ℂ)
    (hspec : spectrum ℂ B = {lam})
    (hf : IsFredholm (B - algebraMap ℂ (X →L[ℂ] X) lam)) :
    FiniteDimensional ℂ X := by
  classical
  by_contra hn
  have hne : (0 : Calkin ℂ X) ≠ 1 := by
    intro he
    have hh : calkinProjection ℂ X (1 : X →L[ℂ] X) = 0 := by rw [map_one, ← he]
    have hc := (Compactness.compact_iff_isCompactOperator _).mp
      ((calkinProjection_eq_zero _).mp hh)
    exact hn (FiniteDimensional.of_isCompactOperator_id hc)
  let : Nontrivial (Calkin ℂ X) := ⟨⟨0, 1, hne⟩⟩
  obtain ⟨z, hz⟩ := spectrum.nonempty (calkinProjection ℂ X B)
  have hz' := AlgHom.spectrum_apply_subset (calkinProjection ℂ X) B hz
  have hez : z = lam := mem_singleton_iff.mp (hspec ▸ hz')
  subst z
  have hu := (atkinson_calkin _).mp hf
  change IsUnit (calkinProjection ℂ X (B - algebraMap ℂ (X →L[ℂ] X) lam)) at hu
  have hu' : IsUnit (algebraMap ℂ (Calkin ℂ X) lam - calkinProjection ℂ X B) := by
    simpa only [map_sub, AlgHom.commutes, neg_sub] using hu.neg
  exact hz hu'

/-- A finite projection range and an invertible complementary block give a
parametrix whose two defects are the negative of that projection. -/
lemma fredholm_of_finite_block (A P : X →L[ℂ] X)
    (hc : Commute A P) [FiniteDimensional ℂ P.range]
    (B : (1 - P).range →L[ℂ] (1 - P).range)
    (hB : ∀ x : (1 - P).range, (B x : X) = A x) (hu : IsUnit B) :
    IsFredholm A := by
  obtain ⟨C, hBC, hCB⟩ := isUnit_iff_exists.mp hu
  let Q : X →L[ℂ] X := 1 - P
  let S : X →L[ℂ] X := liftBlock Q C
  have hcomm (x : X) : Q (A x) = A (Q x) := by
    change A x - P (A x) = A (x - P x)
    rw [map_sub]
    have hh := congrArg (fun R : X →L[ℂ] X => R x) hc.eq
    exact congrArg (fun y => A x - y) hh.symm
  have hr : A.comp S = Q := by
    ext x
    change A (C (Q.rangeRestrict x)) = Q x
    rw [← hB]
    exact congrArg (fun R : Q.range →L[ℂ] Q.range => (R (Q.rangeRestrict x) : X)) hBC
  have hl : S.comp A = Q := by
    ext x
    have he : Q.rangeRestrict (A x) = B (Q.rangeRestrict x) := by
      apply Subtype.ext
      exact (hcomm x).trans (hB (Q.rangeRestrict x)).symm
    change (C (Q.rangeRestrict (A x)) : X) = Q x
    rw [he]
    exact congrArg (fun R : Q.range →L[ℂ] Q.range => (R (Q.rangeRestrict x) : X)) hCB
  have hk : Compactness.IsCompactLinearMap (-P).toLinearMap := by
    simpa only [neg_one_smul, ContinuousLinearMap.toLinearMap_neg] using
      Compactness.compact_smul (-1 : ℂ) P.toLinearMap (compact_of_finiteDimensional_range P)
  apply isFredholm_of_compact_parametrix A S
  · rw [hl]
    change Compactness.IsCompactLinearMap ((1 - P) - (1 : X →L[ℂ] X)).toLinearMap
    simpa only [sub_sub_cancel_left] using hk
  · rw [hr]
    change Compactness.IsCompactLinearMap ((1 - P) - (1 : X →L[ℂ] X)).toLinearMap
    simpa only [sub_sub_cancel_left] using hk

end Banach

section Hilbert
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma eventually_resolvent (T : H →L[ℂ] H) (lam : ℂ)
    (hi : RieszPoles.Spec.IsolatedSpectralPoint T lam) :
    ∀ᶠ z in 𝓝[≠] lam, z ∉ spectrum ℂ T := by
  obtain ⟨_, U, hU, hlU, he⟩ := hi
  have hev : ∀ᶠ z in 𝓝 lam, z ∈ U := hU.mem_nhds hlU
  filter_upwards [hev.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz hne
  intro hspec
  exact hne (mem_singleton_iff.mp (he ▸ (show z ∈ U ∩ spectrum ℂ T from ⟨hz, hspec⟩)))

lemma fredholm_of_resolvent (T : H →L[ℂ] H) (z : ℂ) (hz : z ∉ spectrum ℂ T) :
    IsFredholm (T - z • (1 : H →L[ℂ] H)) := by
  have hb := (LocalSpectralAlternatives.notMem_spectrum_iff_bijective_shift T z).mp hz
  exact isFredholm_of_native (ContinuousLinearEquiv.isFredholm
    (ContinuousLinearEquiv.ofBijective _
      (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)))

/-- At an isolated spectral point semi-Fredholmness already forces both
finite defects, since resolvent points occur arbitrarily close. -/
lemma fredholm_of_semi (T : H →L[ℂ] H) (lam : ℂ)
    (hi : RieszPoles.Spec.IsolatedSpectralPoint T lam)
    (hs : IsSemiFredholm (T - lam • (1 : H →L[ℂ] H))) :
    IsFredholm (T - lam • (1 : H →L[ℂ] H)) := by
  have hc : Continuous (fun z : ℂ => T - z • (1 : H →L[ℂ] H)) := by fun_prop
  have he : ∀ᶠ z in 𝓝 lam,
      IsFredholm (T - z • (1 : H →L[ℂ] H)) ↔
        IsFredholm (T - lam • (1 : H →L[ℂ] H)) := by
    rcases hs with hl | hr
    · exact ((hc.tendsto lam).eventually
        (IsLeftSemiFredholm.eventually_nhds _ hl)).mono (fun _ h => h.2)
    · exact ((hc.tendsto lam).eventually
        (IsRightSemiFredholm.eventually_nhds _ hr)).mono (fun _ h => h.2)
  obtain ⟨z, hz, hez⟩ := ((eventually_resolvent T lam hi).and
    (he.filter_mono nhdsWithin_le_nhds)).exists
  exact hez.mp (fredholm_of_resolvent T z hz)

lemma index_zero (T : H →L[ℂ] H) (lam : ℂ)
    (hi : RieszPoles.Spec.IsolatedSpectralPoint T lam)
    (hf : IsFredholm (T - lam • (1 : H →L[ℂ] H))) :
    fredholmIndex (T - lam • (1 : H →L[ℂ] H)) hf = 0 := by
  have hc : Continuous (fun z : ℂ => T - z • (1 : H →L[ℂ] H)) := by fun_prop
  have he := (hc.tendsto lam).eventually (fredholmIndex_eventually_eq _ hf)
  obtain ⟨z, hz, hfz, hez⟩ := ((eventually_resolvent T lam hi).and
    (he.filter_mono nhdsWithin_le_nhds)).exists
  rw [← hez, fredholmIndex_eq_native]
  exact LinearMap.index_of_bijective
    ((LocalSpectralAlternatives.notMem_spectrum_iff_bijective_shift T z).mp hz)

end Hilbert

/-- All three source conditions for every actual Riesz projection at an
isolated spectral point. -/
theorem isolated_fredholm : Spec.IsolatedFiniteRieszRank.{u} := by
  intro H _ _ _ T lam hi U₁ U₂ f ho₁ ho₂ hd hlU hKU hf₁ hf₂
  let P := ContourCalculus.Spec.HolomorphicValueValue (H →L[ℂ] H) T (U₁ ∪ U₂) f
  have hs := (isolated_riesz_poles H T lam hi U₁ U₂ f ho₁ ho₂ hd hlU hKU hf₁ hf₂).1
  change RieszSplitting.Spec.SplittingData T P {lam} (spectrum ℂ T \ {lam}) at hs
  have hsave := hs
  obtain ⟨hP, hTP, hcl₁, hcl₂, S₁, S₂, h₁, h₂, hspec₁, hspec₂, he⟩ := hs
  let : CompleteSpace P.range := hcl₁.completeSpace_coe
  let : CompleteSpace (1 - P).range := hcl₂.completeSpace_coe
  let A := T - lam • (1 : H →L[ℂ] H)
  let B₁ := S₁ - algebraMap ℂ (P.range →L[ℂ] P.range) lam
  let B₂ := S₂ - algebraMap ℂ ((1 - P).range →L[ℂ] (1 - P).range) lam
  have hc : Commute A P := by
    apply ContinuousLinearMap.ext
    intro x
    change T (P x) - lam • P x = P (T x - lam • x)
    rw [map_sub, map_smul]
    exact congrArg (fun y => y - lam • P x)
      (congrArg (fun R : H →L[ℂ] H => R x) hTP.eq)
  have hB₁ (x : P.range) : (B₁ x : H) = A x := by
    change (S₁ x : H) - lam • (x : H) = T x - lam • (x : H)
    rw [h₁]
  have hB₂ (x : (1 - P).range) : (B₂ x : H) = A x := by
    change (S₂ x : H) - lam • (x : H) = T x - lam • (x : H)
    rw [h₂]
  have hu : IsUnit B₂ := complement_invertible H T P lam _ hsave
    (fun h => h.2 (mem_singleton lam)) S₂ h₂
  have hforward (hA : IsFredholm A) : FiniteDimensional ℂ P.range := by
    exact finite_of_singleton_fredholm S₁ lam hspec₁
      (fredholm_block A P hP hc hcl₁ B₁ hB₁ hA)
  have hback (hfin : FiniteDimensional ℂ P.range) : IsFredholm A := by
    let := hfin
    exact fredholm_of_finite_block A P hc B₂ hB₂ hu
  change (IsSemiFredholm A ↔ FiniteDimensional ℂ P.range) ∧
    (FiniteDimensional ℂ P.range ↔ ∃ h : IsFredholm A, fredholmIndex A h = 0)
  refine ⟨⟨fun hs => hforward (fredholm_of_semi T lam hi hs), ?_⟩,
    ⟨fun hfin => ⟨hback hfin, index_zero T lam hi (hback hfin)⟩,
      fun ⟨hA, _⟩ => hforward hA⟩⟩
  intro hfin
  have hA := hback hfin
  exact Or.inl ⟨hA.1, hA.2.1⟩

end ExpandedFA.Fredholm.IsolatedFredholm
