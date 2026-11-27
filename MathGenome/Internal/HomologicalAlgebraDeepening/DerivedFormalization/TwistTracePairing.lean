import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.TwistTracePairing
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.ProjectiveTwistCohomology
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.CechCochains
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ClassicalDerivedValues

set_option Elab.async false
set_option cleanup.letToHave false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AdvancedHomologicalAlgebra.Cech AdvancedHomologicalAlgebra.SheafTheory
open AdvancedHomologicalAlgebra.SheafUniverseTransport
open AdvancedHomologicalAlgebra.AcyclicCoverOriginalCoefficients
open Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open DerivedFormalization.ProjectiveTwists
open DerivedFormalization.LaurentCechCohomology
open Specs.DerivedFormalization.OrderedCechComparison
open Specs.DerivedFormalization.ProjectiveCechComparison
open Specs.DerivedFormalization.ProjectiveTwistCohomology
open Specs.DerivedFormalization.TwistTracePairing

namespace DerivedFormalization.TwistTracePairing

universe u
attribute [local instance] HasDerivedCategory.standard MvPolynomial.gradedAlgebra

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable (k : Type u) [Field k] (n : ℕ)

private theorem sectionUnit_isIso [EnoughInjectives (AmbientSheaves.{u} (R k n))]
    (F : SheafOfModules.{u} (R k n)) : IsIso (sectionUnit k n F) := by
  haveI : IsIso (rightDegreeZeroUnit (sectionsValue.{u} (R k n) (globalOpen k n))) :=
    AdvancedHomologicalAlgebra.ClassicalDerivedValues.rightZero _ _ _
  unfold sectionUnit
  haveI : IsIso (ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap (R := GlobalRing k n)
      (M := F.val.obj (op (globalOpen k n))))) := by
    exact ((ULift.moduleEquiv (R := GlobalRing k n)
      (M := F.val.obj (op (globalOpen k n)))).symm.toModuleIso).isIso_hom
  infer_instance

variable (c : Cover (globalOpen k n) (Index n))
  {T : TwistFamily k n} {w : SectionCoordinates k n T} {d : LocalizedCoordinates k n c T}

private theorem tupleIndices_nonempty {p : ℕ} (t : Fin (p + 1) → Index n) :
    (tupleIndices n t).Nonempty :=
  ⟨t 0, Finset.mem_image_of_mem _ (Finset.mem_univ 0)⟩

private theorem tupleOpen_eq_intersection (hc : c.opens = chart k n)
    {p : ℕ} (t : Fin (p + 1) → Index n) :
    tupleOpen c t = intersection k n (tupleIndices n t) := by
  rw [tupleOpen_eq_iInf, hc, intersection, tupleIndices, Finset.inf_image, Finset.inf_univ_eq_iInf]
  rfl

private theorem tupleOpen_nonempty (hc : c.opens = chart k n)
    {p : ℕ} (t : Fin (p + 1) → Index n) : Nonempty (tupleOpen c t) := by
  rw [tupleOpen_eq_intersection k n c hc t]
  have hJ := tupleIndices_nonempty n t
  obtain ⟨e⟩ := affineCharts k n _ hJ
  haveI : Nontrivial (ChartRing k n (tupleIndices n t)) :=
    (chartRingToFraction k n (tupleIndices n t)).domain_nontrivial
  let x : PrimeSpectrum (ChartRing k n (tupleIndices n t)) := Classical.choice inferInstance
  exact ⟨e.inv.base x⟩

private def cochainLaurent {m : ℤ} {p : ℕ} (d : LocalizedCoordinates k n c T)
    (x : IncreasingCochains (R k n) c (T m).val p) (t : IncreasingTuple (Index n) p) :
    LaurentPolynomials k n :=
  chartToLaurent k n (tupleIndices n t.1) ((d m p t.1).symm (x t)).val

private theorem coordinate_add {m : ℤ} {p : ℕ}
    (hc : c.opens = chart k n) (hw : TwistCoordinates k n w) (hd : LocalizedTerms k n c w d)
    (t : Fin (p + 1) → Index n) (s z : (T m).val.obj (op (tupleOpen c t))) :
    ((d m p t).symm (s + z)).val = ((d m p t).symm s).val + ((d m p t).symm z).val := by
  let x := Classical.choice (tupleOpen_nonempty k n c hc t)
  let r := chartToFraction k n (tupleIndices n t)
  apply (localizationToFraction_injective k n _ _)
  change r _ = r (_ + _)
  have hsz := hd m p t ((d m p t).symm (s + z)) x
  have hs := hd m p t ((d m p t).symm s) x
  have hz := hd m p t ((d m p t).symm z) x
  simp only [Equiv.apply_symm_apply] at hsz hs hz
  calc
    _ = (w m (tupleOpen c t) (s + z)).val x := hsz.symm
    _ = (w m (tupleOpen c t) s).val x + (w m (tupleOpen c t) z).val x :=
      hw.1 m (tupleOpen c t) s z x
    _ = r (((d m p t).symm s).val) + r (((d m p t).symm z).val) := congrArg₂ (· + ·) hs hz
    _ = _ := (map_add r _ _).symm

private def readLaurent (hc : c.opens = chart k n)
    (hw : TwistCoordinates k n w) (hd : LocalizedTerms k n c w d)
    (m : ℤ) (p : ℕ) (t : IncreasingTuple (Index n) p) :
    (GroundComplex k n c (T m)).X p →+ LaurentPolynomials k n where
  toFun x := cochainLaurent k n c d x t
  map_zero' := by
    have h := coordinate_add k n c hc hw hd t.1
      (0 : (T m).val.obj (op (tupleOpen c t.1))) 0
    rw [zero_add, left_eq_add] at h
    change chartToLaurent k n _ ((d m p t.1).symm 0).val = 0
    rw [h, map_zero]
  map_add' x y := by
    change chartToLaurent k n _ ((d m p t.1).symm (x t + y t)).val = _
    rw [coordinate_add k n c hc hw hd, map_add]
    rfl

private theorem coordinate_restrict {m : ℤ} {p q : ℕ}
    (hc : c.opens = chart k n) (hw : TwistCoordinates k n w) (hd : LocalizedTerms k n c w d)
    (f : Fin (p + 1) → Fin (q + 1)) (t : Fin (q + 1) → Index n)
    (z : (T m).val.obj (op (tupleOpen c (t ∘ f)))) :
    let J := tupleIndices n (t ∘ f)
    let K := tupleIndices n t
    let h : J ⊆ K := by
      intro i hi
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_image_of_mem _ (Finset.mem_univ (f j))
    ((d m q t).symm ((T m).val.map (homOfLE (tupleOpen_reindex_le c f t)).op z)).val =
      localizationRestriction k n h ((d m p (t ∘ f)).symm z).val := by
  dsimp only
  let x := Classical.choice (tupleOpen_nonempty k n c hc t)
  apply localizationToFraction_injective
  rw [localizationRestriction_value]
  let le := tupleOpen_reindex_le c f t
  let y : (T m).val.obj (op (tupleOpen c t)) := (T m).val.map (homOfLE le).op z
  have H := congrArg (fun s : TwistSections k n m (tupleOpen c t) ↦ s.val x)
    (hw.2.2 m _ _ le z)
  change (w m _ y).val x = (w m _ z).val ⟨x.1, le x.2⟩ at H
  have h₁ := hd m q t ((d m q t).symm y) x
  have h₂ := hd m p (t ∘ f) ((d m p (t ∘ f)).symm z) ⟨x.1, le x.2⟩
  rw [Equiv.apply_symm_apply] at h₁ h₂
  exact h₁.symm.trans (H.trans h₂)

private theorem omitted_coefficient {m : ℤ} (p : ℕ)
    (t : IncreasingTuple (Index n) (p + 1)) (j : Fin (p + 2))
    (a : DegreePiece k n (tupleIndices n (t.1 ∘ j.succAbove)) m) :
    (chartToLaurent k n _ a.val).coeff (traceExponent n).val.val = 0 := by
  let J := tupleIndices n (t.1 ∘ j.succAbove)
  have hJ := tupleIndices_nonempty n (t.1 ∘ j.succAbove)
  have h := ((chartCoefficientComparison k n).1 J hJ m a.val).2 ⟨a, rfl⟩
  change chartToLaurent k n J a.val ∈ AddMonoidAlgebra.supported k k (exponentSet n m J) at h
  rw [AddMonoidAlgebra.mem_supported] at h
  by_contra hn
  have hm := h (Finsupp.mem_support_iff.mpr hn)
  have hmem : t.val j ∈ J := hm.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (traceExponent n).2 _⟩)
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
  exact (Fin.succAbove_ne j i) (t.2.injective hi)

private def fullTuple (n : ℕ) : IncreasingTuple (Index n) n :=
  ⟨id, strictMono_id⟩

private theorem boundary_coefficient
    (hc : c.opens = chart k n) (hw : TwistCoordinates k n w) (hd : LocalizedTerms k n c w d)
    (m : ℤ) (hn : 1 ≤ n) (x : (GroundComplex k n c (T m)).X (n - 1)) :
    (readLaurent k n c hc hw hd m n (fullTuple n)
      ((GroundComplex k n c (T m)).d (n - 1) n x)).coeff (traceExponent n).val.val = 0 := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let t := fullTuple (p + 1)
  let C := GroundComplex k (p + 1) c (T m)
  have hdif : C.d p (p + 1) x =
      increasingDifferential (R k (p + 1)) c (T m).val p x := by
    change (CechComplex k (p + 1) c (T m)).d p (p + 1) x = _
    rw [increasingComplex_d]
    rfl
  change (readLaurent k (p + 1) c hc hw hd m (p + 1) t (C.d p (p + 1) x)).coeff _ = _
  rw [hdif]
  have he : (increasingDifferential (R k (p + 1)) c (T m).val p x) =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val • (fun s : IncreasingTuple _ (p + 1) ↦
        localRestriction (R k (p + 1)) (T m).val (globalOpen k (p + 1)) (tupleOpen_le c s.val)
          (tupleOpen_le c (s.val ∘ j.succAbove)) (tupleOpen_reindex_le c j.succAbove s.val)
          (x ⟨s.val ∘ j.succAbove, s.2.comp j.strictMono_succAbove⟩)) := by
    funext s
    rw [increasingDifferential_apply, Finset.sum_apply]
    rfl
  rw [he, map_sum]
  simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro j _
  rw [map_zsmul, AddMonoidAlgebra.coeff_smul_apply]
  change ((-1 : ℤ) ^ j.val) • (chartToLaurent k (p + 1) _
    ((d m (p + 1) t.val).symm ((T m).val.map (homOfLE (tupleOpen_reindex_le c j.succAbove t.val)).op
      (x ⟨t.val ∘ j.succAbove, t.2.comp j.strictMono_succAbove⟩))).val).coeff _ = 0
  rw [coordinate_restrict k (p + 1) c hc hw hd, (chartCoefficientComparison k (p + 1)).2.1,
    omitted_coefficient k (p + 1) p t j, smul_zero]


private abbrev restrictGlobal (F : SheafOfModules.{u} (R k n)) :
    GroundSections k n F ⟶ (GroundComplex k n c F).X 0 :=
  (GroundRestriction k n).map (ModuleCat.ofHom
    ((projectionComponent (R k n) c F.val 0).comp (augmentation (R k n) F.val c)))

private theorem restrictGlobal_closed (F : SheafOfModules.{u} (R k n)) :
    restrictGlobal k n c F ≫ (GroundComplex k n c F).d 0 1 = 0 := by
  apply ModuleCat.hom_ext
  ext s : 1
  change (CechComplex k n c F).d 0 1 (projectionComponent (R k n) c F.val 0
    (augmentation (R k n) F.val c s)) = 0
  rw [increasingComplex_d]
  change increasingDifferential (R k n) c F.val 0 _ = _
  rw [projection_comm_apply]
  have ha := LinearMap.congr_fun
    (AdvancedHomologicalAlgebra.CechCochains.augmentation_closed (R k n) F.val c) s
  change differential (R k n) F.val c 0 (augmentation (R k n) F.val c s) = 0 at ha
  rw [ha, map_zero]

private def restrictGlobalToCycles (F : SheafOfModules.{u} (R k n)) :
    GroundSections k n F ⟶ (GroundComplex k n c F).cycles 0 :=
  (GroundComplex k n c F).liftCycles (restrictGlobal k n c F) 1
    (CochainComplex.next ℕ 0)
    (restrictGlobal_closed k n c F)

private theorem restrictGlobalToCycles_value (F : SheafOfModules.{u} (R k n))
    (s : GroundSections k n F) (t : IncreasingTuple (Index n) 0) :
    (show IncreasingCochains (R k n) c F.val 0 from
      (GroundComplex k n c F).iCycles 0 (restrictGlobalToCycles k n c F s)) t =
    F.val.map (homOfLE (tupleOpen_le c t.1)).op s := by
  have h := (GroundComplex k n c F).liftCycles_i
    (restrictGlobal k n c F) 1
    (CochainComplex.next ℕ 0) (restrictGlobal_closed k n c F)
  exact congrArg (fun f ↦ (show IncreasingCochains (R k n) c F.val 0 from f s) t) h

private theorem projection_zero_mono (F : SheafOfModules.{u} (R k n)) :
    Function.Injective (restrictGlobalToCycles k n c F) := by
  intro s z e
  apply (AdvancedHomologicalAlgebra.CechCochains.sectionsKernelEquiv (R k n) c F).injective
  apply Subtype.ext
  funext t
  let t' : IncreasingTuple (Index n) 0 := ⟨t, fun i j hij ↦
    by omega⟩
  change F.val.map (homOfLE (tupleOpen_le c t)).op s =
    F.val.map (homOfLE (tupleOpen_le c t)).op z
  have H := congrArg (fun v ↦
    (show IncreasingCochains (R k n) c F.val 0 from (GroundComplex k n c F).iCycles 0 v) t') e
  rw [restrictGlobalToCycles_value, restrictGlobalToCycles_value] at H
  exact H

private def polynomialSectionValue {m : ℤ} (f : polynomialDegree k n m) :
    TwistSections k n m (globalOpen k n) := by
  refine ⟨fun _ ↦ intoFraction k n f.val, ?_⟩
  by_cases h : f.val = 0
  · rw [h, map_zero]
    exact section_zero k n m (globalOpen k n)
  · apply TopCat.PrelocalPredicate.sheafifyOf
    obtain ⟨b, hb⟩ := MvPolynomial.exists_coeff_ne_zero h
    have hm := f.property b hb
    have hmn : 0 ≤ m := hm ▸ Finset.sum_nonneg (fun i _ ↦ Int.natCast_nonneg (b i))
    have he := Int.toNat_of_nonneg hmn
    refine ⟨f.val, 1, m.toNat, 0, ?_, SetLike.one_mem_graded _, ?_, ?_, ?_⟩
    · rw [← (polynomialGrading k n).1, he]
      exact f.property
    · simpa using he
    · intro x
      exact Ideal.one_notMem (ProjectiveSpectrum.asHomogeneousIdeal x.1).toIdeal
    · simp [fraction]

private theorem polynomialGlobalCoordinates
    [EnoughInjectives (AmbientSheaves.{u} (R k n))]
    (hw : TwistCoordinates k n w) (hd : LocalizedTerms k n c w d)
    (hA : ∀ m, AcyclicOnIntersections (R k n) c (T m))
    (hOrd : OrderedComparison (R k n) c)
    (m : ℤ)
    (e : polynomialDegree k n m ≃ₗ[k] GroundCohomology k n (T m) 0)
    (he : ∀ f, ∃ z : (GroundComplex k n c (T m)).cycles 0,
      (descentIso k n c hOrd (T m) (hA m) 0).hom
        ((GroundComplex k n c (T m)).homologyπ 0 z) = e f ∧
      ∀ t, localizedRepresentative k n c d z t = algebraMap _ _ f.val) :
    ∃ e' : polynomialDegree k n m ≃ₗ[k] GroundSections k n (T m),
      ∀ f x, (w m (globalOpen k n) (e' f)).val x = intoFraction k n f.val := by
  let C := GroundComplex k n c (T m)
  let iso := (CochainComplex.isoHomologyπ₀ C ≪≫ descentIso k n c hOrd (T m) (hA m) 0).toLinearEquiv
  have hglue (f : polynomialDegree k n m) : ∃ s : GroundSections k n (T m),
      iso (restrictGlobalToCycles k n c (T m) s) = e f ∧
      ∀ x, (w m (globalOpen k n) s).val x = intoFraction k n f.val := by
    let s := (w m (globalOpen k n)).symm (polynomialSectionValue k n f)
    have hs : ∀ x, (w m (globalOpen k n) s).val x = intoFraction k n f.val := by
      intro x
      simp only [s, Equiv.apply_symm_apply]
      rfl
    refine ⟨s, ?_, hs⟩
    obtain ⟨z, hz, hloc⟩ := he f
    have hZ : restrictGlobalToCycles k n c (T m) s = z := by
      apply (ModuleCat.mono_iff_injective _).mp (inferInstance : Mono (C.iCycles 0))
      funext t
      change (show IncreasingCochains (R k n) c (T m).val 0 from
        (GroundComplex k n c (T m)).iCycles 0 (restrictGlobalToCycles k n c (T m) s)) t =
        (show IncreasingCochains (R k n) c (T m).val 0 from C.iCycles 0 z) t
      rw [restrictGlobalToCycles_value]
      apply (w m (tupleOpen c t.1)).injective
      apply Subtype.ext
      funext x
      have h1 := congrArg (fun a : TwistSections k n m (tupleOpen c t.1) ↦ a.val x)
        (hw.2.2 m _ _ (tupleOpen_le c t.1) s)
      change _ = (w m _ s).val ⟨x.1, tupleOpen_le c t.1 x.2⟩ at h1
      rw [hs] at h1
      have h2 := hd m 0 t.1 ((d m 0 t.1).symm
        ((show IncreasingCochains (R k n) c (T m).val 0 from C.iCycles 0 z) t)) x
      rw [Equiv.apply_symm_apply] at h2
      change _ = chartToFraction k n _ (localizedRepresentative k n c d z t) at h2
      rw [hloc t] at h2
      exact h1.trans (h2.trans (IsLocalization.lift_eq _ f.val)).symm
    rw [hZ]
    exact hz
  have hsurj : Function.Surjective (restrictGlobalToCycles k n c (T m)) := by
    intro z
    obtain ⟨s, hs, _⟩ := hglue (e.symm (iso z))
    exact ⟨s, iso.injective (hs.trans (e.apply_symm_apply _))⟩
  let aug := LinearEquiv.ofBijective (restrictGlobalToCycles k n c (T m)).hom
    ⟨projection_zero_mono k n c (T m), hsurj⟩
  refine ⟨e.trans (iso.symm.trans aug.symm), ?_⟩
  intro f x
  obtain ⟨s, hs, hval⟩ := hglue f
  have hh : e.trans (iso.symm.trans aug.symm) f = s := by
    apply aug.injective
    apply iso.injective
    change iso (aug (aug.symm (iso.symm (e f)))) = iso (restrictGlobalToCycles k n c (T m) s)
    rw [aug.apply_symm_apply, iso.apply_symm_apply, hs]
  rw [hh, hval]


private def polynomialBasis (m : ℤ) : Module.Basis (PolynomialExponents n m) k
    (polynomialDegree k n m) := by
  let S : Set (Index n →₀ ℕ) := {a | (∑ i, (a i : ℤ)) = m}
  have he : polynomialDegree k n m = AddMonoidAlgebra.supported k k S := by
    ext f
    change _ ↔ (AddMonoidAlgebra.ofCoeff f.coeff : AddMonoidAlgebra k _) ∈ _
    rw [AddMonoidAlgebra.mem_supported]
    exact ⟨fun h a ha ↦ h a (Finsupp.mem_support_iff.mp ha),
      fun h a ha ↦ h (Finsupp.mem_support_iff.mpr ha)⟩
  exact Module.Basis.ofRepr ((LinearEquiv.ofEq _ _ he).trans
    (AddMonoidAlgebra.supportedEquivFinsupp (R := k) (S := k) S))

private theorem polynomialBasis_apply {m : ℤ} (a : PolynomialExponents n m) :
    polynomialBasis k n m a = polynomialMonomial k n a := by
  apply (polynomialBasis k n m).repr.injective
  rw [Module.Basis.repr_self]
  ext b
  change Finsupp.single a 1 b = (MvPolynomial.monomial a.val (1 : k)).coeff b.val
  classical
  simp [Finsupp.single_apply, MvPolynomial.coeff_monomial, Subtype.ext_iff]

private theorem polynomialExponents_finite (m : ℤ) : Finite (PolynomialExponents n m) := by
  let f (a : PolynomialExponents n m) (i : Index n) : Fin (m.toNat + 1) := ⟨a.val i, by
    have h := Finset.single_le_sum (s := Finset.univ) (f := fun j ↦ (a.val j : ℤ))
      (fun j _ ↦ Int.natCast_nonneg (a.val j)) (Finset.mem_univ i)
    rw [a.property] at h
    omega⟩
  exact Finite.of_injective f (fun a b h ↦ Subtype.ext (Finsupp.ext
    (fun i ↦ congrArg Fin.val (congrFun h i))))

private theorem complement_bijective (m : ℤ) :
    Function.Bijective (complement (n := n) (m := m)) := by
  constructor
  · intro a b h
    apply Subtype.ext
    ext i
    have H := congrArg (fun (x : TopExponents n (traceDegree n - m)) ↦ x.val.val i) h
    change -1 - (a.val i : ℤ) = -1 - (b.val i : ℤ) at H
    omega
  · intro b
    let f : Index n →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i ↦ (-1 - b.val.val i).toNat)
    have hf (i : Index n) : (f i : ℤ) = -1 - b.val.val i := by
      change ((Finsupp.equivFunOnFinite.symm _ : Index n →₀ ℕ) i : ℤ) = _
      rw [Finsupp.equivFunOnFinite_symm_apply_apply, Int.toNat_of_nonneg (by have := b.2 i; omega)]
    have hm : ∑ i, (f i : ℤ) = m := by
      simp_rw [hf]
      rw [Finset.sum_sub_distrib, b.val.property]
      simp [traceDegree, Index]
      omega
    refine ⟨⟨f, hm⟩, Subtype.ext (Subtype.ext ?_)⟩
    funext i
    change -1 - (f i : ℤ) = b.val.val i
    rw [hf]
    omega

private def embedTop (m : ℤ) : (TopExponents n m →₀ k) →ₗ[k] LaurentPolynomials k n :=
  (AddMonoidAlgebra.coeffLinearEquiv k).symm.toLinearMap.comp
    (Finsupp.lmapDomain k k (fun a : TopExponents n m ↦ a.val.val))

private def laurentPair (a b : ℤ) : polynomialDegree k n a →ₗ[k] (TopExponents n b →₀ k) →ₗ[k] k where
  toFun f := ((Finsupp.lapply (traceExponent n).val.val).comp
    (AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap).comp
    ((Algebra.lmul k (LaurentPolynomials k n) (polynomialToLaurent k n f.val)).comp (embedTop k n b))
  map_add' f g := by ext z; simp
  map_smul' r f := by ext z; simp

private theorem laurentPair_monomial (m : ℤ) (a : PolynomialExponents n m)
    (b : TopExponents n (traceDegree n - m)) :
    laurentPair k n m _ (polynomialMonomial k n a) (Finsupp.single b 1) =
      if b = complement a then 1 else 0 := by
  classical
  change (polynomialToLaurent k n (MvPolynomial.monomial a.val 1) *
    AddMonoidAlgebra.ofCoeff (Finsupp.mapDomain (fun b : TopExponents n _ ↦ b.val.val)
      (Finsupp.single b 1))).coeff (traceExponent n).val.val = _
  have h : polynomialToLaurent k n (MvPolynomial.monomial a.val 1) =
      AddMonoidAlgebra.single (naturalExponent n a.val) 1 :=
    AddMonoidAlgebra.mapDomain_single
  rw [h, Finsupp.mapDomain_single, ← AddMonoidAlgebra.single, AddMonoidAlgebra.single_mul_single,
    one_mul, AddMonoidAlgebra.coeff_single]
  rw [Finsupp.single_apply]
  congr 1
  apply propext
  constructor
  · intro eq
    apply Subtype.ext
    apply Subtype.ext
    funext i
    have hi := congrFun eq i
    change (a.val i : ℤ) + b.val.val i = -1 at hi
    change b.val.val i = -1 - (a.val i : ℤ)
    omega
  · intro eq
    subst b
    funext i
    change (a.val i : ℤ) + (-1 - (a.val i : ℤ)) = -1
    omega

private theorem laurentPair_perfect (m : ℤ) :
    (laurentPair k n m (traceDegree n - m)).IsPerfPair := by
  classical
  haveI := polynomialExponents_finite n m
  let e := Equiv.ofBijective _ (complement_bijective n m)
  let B := polynomialBasis k n m
  let D := (Finsupp.basisSingleOne (R := k) (ι := TopExponents n (traceDegree n - m))).reindex e.symm
  haveI : FiniteDimensional k (polynomialDegree k n m) := B.finiteDimensional_of_finite
  let p := laurentPair k n m (traceDegree n - m)
  have h (i j : PolynomialExponents n m) : p (B i) (D j) = if i = j then 1 else 0 := by
    change p (B i) ((Finsupp.basisSingleOne (R := k)).reindex e.symm j) = _
    rw [Module.Basis.reindex_apply, Finsupp.coe_basisSingleOne, polynomialBasis_apply,
      laurentPair_monomial]
    simp [e, (complement_bijective n m).1.eq_iff, eq_comm]
  apply LinearMap.IsPerfPair.of_injective
  · apply (injective_iff_map_eq_zero p).mpr
    intro v hv
    apply B.repr.injective
    rw [map_zero]
    ext i
    have h0 := DFunLike.congr_fun hv (D i)
    have hcoord : (p.flip (D i)) = B.coord i := by
      apply B.ext
      intro j
      simp [h, Module.Basis.coord_apply, Finsupp.single_apply, eq_comm]
    rw [← Module.Basis.coord_apply, ← hcoord]
    exact h0
  · apply (injective_iff_map_eq_zero p.flip).mpr
    intro v hv
    apply D.repr.injective
    rw [map_zero]
    ext i
    have h0 := DFunLike.congr_fun hv (B i)
    have hcoord : p (B i) = D.coord i := by
      apply D.ext
      intro j
      simp [h, Module.Basis.coord_apply, Finsupp.single_apply, eq_comm]
    rw [← Module.Basis.coord_apply, ← hcoord]
    exact h0


section Trace

variable [EnoughInjectives (AmbientSheaves.{u} (R k n))]
  (hA : ∀ m, AcyclicOnIntersections (R k n) c (T m))
  (hOrd : OrderedComparison (R k n) c)

local notation "Ctw" => (fun m : ℤ ↦ GroundComplex k n c (T m))
local notation "Htw" => (fun (m : ℤ) (q : ℕ) ↦ GroundCohomology k n (T m) q)
local notation "descent" => (fun (m : ℤ) (q : ℕ) ↦ descentIso k n c hOrd (T m) (hA m) q)

private abbrev TopBasis (m : ℤ) := (TopExponents n m →₀ k) ≃ₗ[k] Htw m n

private def RepresentsTop (m : ℤ) (e : TopBasis k n (T := T) m) : Prop :=
  ∀ f, ∃ z : (Ctw m).cycles n, (descent m n).hom ((Ctw m).homologyπ n z) = e f ∧
    ∀ t, cochainLaurent k n c d ((Ctw m).iCycles n z) t = embedTop k n m f

private def traceOf (e : TopBasis k n (T := T) (traceDegree n)) :
    Htw (traceDegree n) n →ₗ[k] k :=
  (Finsupp.lapply (traceExponent n)).comp e.symm.toLinearMap

private theorem trace_cycle
    (hc : c.opens = chart k n) (hw : TwistCoordinates k n w) (hd : LocalizedTerms k n c w d)
    (hn : 1 ≤ n) (e : TopBasis k n (T := T) (traceDegree n))
    (he : RepresentsTop k n c (d := d) hA hOrd (traceDegree n) e)
    (z : (Ctw (traceDegree n)).cycles n) :
    traceOf k n e ((descent (traceDegree n) n).hom ((Ctw (traceDegree n)).homologyπ n z)) =
      (cochainLaurent k n c d ((Ctw (traceDegree n)).iCycles n z) (fullTuple n)).coeff
        (traceExponent n).val.val := by
  let m := traceDegree n
  let K := Ctw m
  let l := readLaurent k n c hc hw hd m n (fullTuple n)
  let F : K.cycles n →+ k :=
    { toFun := fun s ↦ (l (K.iCycles n s)).coeff (traceExponent n).val.val
      map_zero' := by simp
      map_add' := by intro a b; simp }
  let f := e.symm ((descent m n).hom (K.homologyπ n z))
  obtain ⟨z', hz', hr⟩ := he f
  have heq : K.homologyπ n z = K.homologyπ n z' := by
    apply (descent m n).toLinearEquiv.injective
    rw [Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply, hz']
    exact (e.apply_symm_apply _).symm
  have hprev : (ComplexShape.up ℕ).prev n = n - 1 := by
    obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact CochainComplex.prev_nat_succ p
  let S := ShortComplex.mk (K.toCycles (n - 1) n) (K.homologyπ n)
    (K.toCycles_comp_homologyπ _ _)
  have hExact : S.Exact := S.exact_of_g_is_cokernel (K.homologyIsCokernel (i := n - 1) (j := n) hprev)
  obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff S).mp hExact (z - z') (by
    change K.homologyπ n (z - z') = 0
    rw [map_sub, heq, sub_self])
  have hF : F (z - z') = 0 := by
    change K.toCycles (n - 1) n x = z - z' at hx
    rw [← hx]
    change (l (K.iCycles n (K.toCycles (n - 1) n x))).coeff _ = _
    rw [← ModuleCat.comp_apply, HomologicalComplex.toCycles_i]
    exact boundary_coefficient k n c hc hw hd m hn x
  rw [map_sub, sub_eq_zero] at hF
  change f (traceExponent n) = F z
  rw [hF]
  change f (traceExponent n) = (cochainLaurent k n c d (K.iCycles n z') _).coeff _
  rw [hr]
  exact (Finsupp.mapDomain_apply_of_injective
    (fun a b h ↦ Subtype.ext (Subtype.ext h)) f (traceExponent n)).symm

private theorem transportHomology_natural {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    {K L : CochainComplex A ℕ} (f : K ⟶ L) (q : ℕ)
    {M N : A} (α : K.homology q ≅ M) (β : L.homology q ≅ N) (g : M ⟶ N)
    (h : HomologicalComplex.homologyMap f q ≫ β.hom = α.hom ≫ g) :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map f) q ≫
        ((L.sc q).mapHomologyIso F ≪≫ F.mapIso β).hom =
      ((K.sc q).mapHomologyIso F ≪≫ F.mapIso α).hom ≫ F.map g := by
  have hm : HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map f) q ≫
      ((L.sc q).mapHomologyIso F).hom =
        ((K.sc q).mapHomologyIso F).hom ≫ F.map (HomologicalComplex.homologyMap f q) :=
    ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor A (.up ℕ) q).map f) F
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, hm]
  simp only [Category.assoc, ← Functor.map_comp, h]

private theorem orderedDescent_naturality {X : TopCat.{u}} (S : X.Sheaf RingCat.{u})
    {U : Opens X} {I : Type} [LinearOrder I] (c₀ : Cover U I)
    [EnoughInjectives (SheafOfModules.{u} S)] (h : OrderedComparison S c₀)
    {M N : SheafOfModules.{u} S}
    (hM : AcyclicOnIntersections S c₀ M) (hN : AcyclicOnIntersections S c₀ N)
    (f : M ⟶ N) (q : ℕ) {K : Type u} [Ring K] (r : K →+* sectionRing S U) :
    let α := h.choose_spec.choose_spec.choose_spec.choose
    let A := ModuleCat.restrictScalars.{u} r
    let C := increasingComplex S c₀ M.val
    let D := increasingComplex S c₀ N.val
    let φ := increasingMap S c₀ f.val
    let φH := (SectionH S (U := U) q).map f
    HomologicalComplex.homologyMap ((A.mapHomologicalComplex (.up ℕ)).map φ) q ≫
        ((D.sc q).mapHomologyIso A ≪≫ A.mapIso (α N hN q)).hom =
      ((C.sc q).mapHomologyIso A ≪≫ A.mapIso (α M hM q)).hom ≫ A.map φH := by
  intro α A C D φ φH
  have he : HomologicalComplex.homologyMap φ q ≫ (α N hN q).hom =
      (α M hM q).hom ≫ φH :=
    h.choose_spec.choose_spec.choose_spec.choose_spec.2.2 M N hM hN f q
  exact transportHomology_natural (A := ModuleCat.{u} (sectionRing S U))
    (B := ModuleCat.{u} K) A φ q (α M hM q) (α N hN q) φH he

private theorem multiply_cochain
    (hc : c.opens = chart k n) (hd : LocalizedTerms k n c w d)
    {μ : GlobalMultiply k n T} (hμ : GlobalMultiplyFormula k n w μ)
    {a b : ℤ} (s : GroundSections k n (T a)) (f : polynomialDegree k n a)
    (hs : ∀ x, (w a (globalOpen k n) s).val x = intoFraction k n f.val)
    (p : ℕ) (x : (Ctw b).X p) (t : IncreasingTuple (Index n) p) :
    let g := ((GroundRestriction k n).mapHomologicalComplex (.up ℕ)).map
      (increasingMap (R k n) c (μ a b s).val)
    cochainLaurent k n c d (g.f p x) t =
      polynomialToLaurent k n f.val * cochainLaurent k n c d x t := by
  intro g
  let U := tupleOpen c t.1
  let y : (T (a + b)).val.obj (op U) := (μ a b s).val.app (op U) (x t)
  have hg : (show IncreasingCochains (R k n) c (T (a + b)).val p from g.f p x) t = y := by
    change increasingMapComponent (R k n) c (μ a b s).val p x t = _
    dsimp only [y]
    obtain ⟨x', hx⟩ := projectionComponent_surjective (R k n) c (T b).val p x
    rw [← hx, increasingMap_projection_apply]
    rfl
  let J := tupleIndices n t.1
  have he : chartToLaurent k n J (algebraMap _ _ f.val) = polynomialToLaurent k n f.val := by
    simp [chartToLaurent, IsLocalization.liftAlgHom_apply]
  let r := chartToFraction k n J
  let pt := Classical.choice (tupleOpen_nonempty k n c hc t.1)
  have hl := hd (a + b) p t.1 ((d (a + b) p t.1).symm y) pt
  have hr := hd b p t.1 ((d b p t.1).symm (x t)) pt
  simp only [Equiv.apply_symm_apply] at hl hr
  have hf : r (algebraMap _ _ f.val) = intoFraction k n f.val := IsLocalization.lift_eq _ _
  have hprod : ((d (a + b) p t.1).symm y).val =
      algebraMap _ _ f.val * ((d b p t.1).symm (x t)).val := by
    apply (localizationToFraction_injective k n _ _)
    change r _ = r (_ * _)
    calc
      _ = (w (a + b) U y).val pt := hl.symm
      _ = (w a (globalOpen k n) s).val ⟨pt, trivial⟩ * (w b U (x t)).val pt :=
        hμ a b s U (x t) pt
      _ = r (algebraMap _ _ f.val) * r (((d b p t.1).symm (x t)).val) :=
        congrArg₂ (· * ·) ((hs _).trans hf.symm) hr
      _ = _ := (map_mul r _ _).symm
  calc
    _ = chartToLaurent k n J ((d (a + b) p t.1).symm y).val :=
      congrArg (fun z ↦ chartToLaurent k n J ((d (a + b) p t.1).symm z).val) hg
    _ = _ := by rw [hprod, map_mul, he]; rfl

private theorem trace_multiplication
    (hc : c.opens = chart k n) (hw : TwistCoordinates k n w) (hd : LocalizedTerms k n c w d)
    (hn : 1 ≤ n) {μ : GlobalMultiply k n T} (hμ : GlobalMultiplyFormula k n w μ)
    (e : ∀ m, TopBasis k n (T := T) m)
    (he : ∀ m, RepresentsTop k n c (d := d) hA hOrd m (e m))
    {a b : ℤ} (hab : a + b = traceDegree n)
    (s : GroundSections k n (T a)) (f : polynomialDegree k n a)
    (hs : ∀ x, (w a (globalOpen k n) s).val x = intoFraction k n f.val)
    (v : TopExponents n b →₀ k) :
    traceOf k n (e (traceDegree n)) (traceAction k n μ hab s (e b v)) =
      laurentPair k n a b f v := by
  obtain ⟨z, hz, hzcoord⟩ := he b v
  have evaluate (m : ℤ) (hm : m = traceDegree n) (f' : T b ⟶ T m) :
      let g := ((GroundRestriction k n).mapHomologicalComplex (.up ℕ)).map
        (increasingMap (R k n) c f'.val)
      traceOf k n (e (traceDegree n))
        (cohomologyMap k n (f' ≫ eqToHom (congrArg T hm)) n (e b v)) =
        (cochainLaurent k n c d (g.f n ((Ctw b).iCycles n z)) (fullTuple n)).coeff
          (traceExponent n).val.val := by
    subst m
    intro g
    simp only [congrArg, eqToHom_refl, Category.comp_id]
    let j := traceDegree n
    let z' := HomologicalComplex.cyclesMap g n z
    let πz := (Ctw b).homologyπ n z
    have hπ : HomologicalComplex.homologyMap g n πz = (Ctw j).homologyπ n z' :=
      congrArg (fun f₀ ↦ f₀ z) (HomologicalComplex.homologyπ_naturality g n)
    have hclass : (descent j n).hom ((Ctw j).homologyπ n z') =
        cohomologyMap k n f' n (e b v) := by
      calc
        _ = (descent j n).hom (HomologicalComplex.homologyMap g n πz) :=
          congrArg (fun x ↦ (descent j n).hom x) hπ.symm
        _ = cohomologyMap k n f' n ((descent b n).hom πz) :=
          congrArg (fun f₀ ↦ f₀ πz)
            (orderedDescent_naturality (X := Base k n) (R k n) (U := globalOpen k n)
              (I := Index n) c hOrd (M := T b) (N := T j) (hA b) (hA j) f' n
              (K := k) (groundScalarsValue k n))
        _ = _ := congrArg (fun x ↦ cohomologyMap k n f' n x) hz
    have hi : (Ctw j).iCycles n z' = g.f n ((Ctw b).iCycles n z) :=
      congrArg (fun f₀ ↦ f₀ z) (HomologicalComplex.cyclesMap_i g n)
    calc
      _ = traceOf k n (e j) ((descent j n).hom ((Ctw j).homologyπ n z')) :=
        congrArg (traceOf k n (e j)) hclass.symm
      _ = (cochainLaurent k n c d ((Ctw j).iCycles n z') (fullTuple n)).coeff
          (traceExponent n).val.val :=
        trace_cycle k n c hA hOrd hc hw hd hn _ (he _) z'
      _ = _ := congrArg (fun x ↦
        (cochainLaurent k n c d x (fullTuple n)).coeff (traceExponent n).val.val) hi
  calc
    _ = _ := evaluate (a + b) hab (μ a b s)
    _ = (polynomialToLaurent k n f.val * cochainLaurent k n c d ((Ctw b).iCycles n z)
        (fullTuple n)).coeff (traceExponent n).val.val :=
      congrArg (fun x : LaurentPolynomials k n ↦ x.coeff (traceExponent n).val.val)
        (multiply_cochain k n c hc hd hμ s f hs n ((Ctw b).iCycles n z) (fullTuple n))
    _ = _ := congrArg (fun x : LaurentPolynomials k n ↦
      (polynomialToLaurent k n f.val * x).coeff (traceExponent n).val.val) (hzcoord (fullTuple n))

end Trace


private theorem perfect_zero {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module k M] [Module k N] [Subsingleton M] [Subsingleton N] :
    (0 : M →ₗ[k] N →ₗ[k] k).IsPerfPair := by
  have singletonDual (A : Type u) [AddCommGroup A] [Module k A] [Subsingleton A] :
      Subsingleton (A →ₗ[k] k) := ⟨fun f g ↦ by
        ext x
        rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
  letI := singletonDual M
  letI := singletonDual N
  exact ⟨Function.bijective_of_subsingleton' _, Function.bijective_of_subsingleton' _⟩

section EndpointPairings

variable [EnoughInjectives (AmbientSheaves.{u} (R k n))]
  (e₀ : ∀ m, polynomialDegree k n m ≃ₗ[k] GroundCohomology k n (T m) 0)
  (eₙ : ∀ m, TopBasis k n (T := T) m)

local notation "Htw" => (fun (m : ℤ) (q : ℕ) ↦ GroundCohomology k n (T m) q)

private def endpointPairing (a b : ℤ) : Htw a 0 →ₗ[k] Htw b n →ₗ[k] k :=
  (laurentPair k n a b).compl₁₂ (e₀ a).symm.toLinearMap (eₙ b).symm.toLinearMap

private theorem endpointPairing_perfect (a b : ℤ) (h : a + b = traceDegree n) :
    (endpointPairing k n e₀ eₙ a b).IsPerfPair := by
  obtain rfl : b = traceDegree n - a := by omega
  haveI := laurentPair_perfect k n a
  exact LinearMap.IsPerfPair.compl₁₂ (p := laurentPair k n a (traceDegree n - a))
    (e₀ a).symm (eₙ (traceDegree n - a)).symm

private def pairing (m : ℤ) : ∀ q r, q + r = n → Htw m q →ₗ[k] Htw (traceDegree n - m) r →ₗ[k] k
  | 0, r, h => by
      have hr : r = n := by omega
      subst r
      exact endpointPairing k n e₀ eₙ m (traceDegree n - m)
  | q + 1, 0, h => by
      obtain he : q + 1 = n := by omega
      exact cast (congrArg (fun i ↦ Htw m i →ₗ[k] Htw (traceDegree n - m) 0 →ₗ[k] k) he.symm)
        (endpointPairing k n e₀ eₙ (traceDegree n - m) m).flip
  | _ + 1, _ + 1, _ => 0

private theorem pairing_left (m : ℤ) :
    pairing k n e₀ eₙ m 0 n (Nat.zero_add n) =
      endpointPairing k n e₀ eₙ m (traceDegree n - m) := by
  simp [pairing]

private theorem pairing_right (hn : 1 ≤ n) (m : ℤ) :
    pairing k n e₀ eₙ m n 0 (Nat.add_zero n) =
      (endpointPairing k n e₀ eₙ (traceDegree n - m) m).flip := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp [pairing]

private theorem pairing_perfect (hn : 1 ≤ n)
    (hzero : ∀ (m : ℤ) (q : ℕ), 0 < q → q ≠ n → IsZero (Htw m q))
    (m : ℤ) (q r : ℕ) (hqr : q + r = n) :
    (pairing k n e₀ eₙ m q r hqr).IsPerfPair := by
  by_cases hq : q = 0
  · subst q
    have hr : r = n := by omega
    subst r
    rw [pairing_left]
    exact endpointPairing_perfect k n e₀ eₙ _ _ (by omega)
  by_cases hr : r = 0
  · subst r
    have he : q = n := by omega
    subst q
    rw [pairing_right k n e₀ eₙ hn]
    exact (endpointPairing_perfect k n e₀ eₙ _ _ (by omega)).flip
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
  haveI := ModuleCat.isZero_iff_subsingleton.mp (hzero m (q + 1) (by omega) (by omega))
  haveI := ModuleCat.isZero_iff_subsingleton.mp
    (hzero (traceDegree n - m) (r + 1) (by omega) (by omega))
  exact perfect_zero k

private theorem pairing_monomial (m : ℤ) (a : PolynomialExponents n m)
    (b : TopExponents n (traceDegree n - m)) :
    pairing k n e₀ eₙ m 0 n (Nat.zero_add n) (e₀ m (polynomialMonomial k n a))
      (eₙ _ (Finsupp.single b 1)) = if b = complement a then 1 else 0 := by
  rw [pairing_left]
  simpa [endpointPairing] using laurentPair_monomial k n m a b

end EndpointPairings

section Assembly

variable [EnoughInjectives (AmbientSheaves.{u} (R k n))]
  (hA : ∀ m, AcyclicOnIntersections (R k n) c (T m))
  (hOrd : OrderedComparison (R k n) c)

private def RepresentsZero (m : ℤ)
    (e : polynomialDegree k n m ≃ₗ[k] GroundCohomology k n (T m) 0) : Prop :=
  ∀ f, ∃ z : (GroundComplex k n c (T m)).cycles 0,
    (descentIso k n c hOrd (T m) (hA m) 0).hom
      ((GroundComplex k n c (T m)).homologyπ 0 z) = e f ∧
    ∀ t, localizedRepresentative k n c d z t = algebraMap _ _ f.val

private theorem endpointPairing_action
    (hc : c.opens = chart k n) (hw : TwistCoordinates k n w) (hd : LocalizedTerms k n c w d)
    (hn : 1 ≤ n) {μ : GlobalMultiply k n T} (hμ : GlobalMultiplyFormula k n w μ)
    (G : ∀ m, polynomialDegree k n m ≃ₗ[k] GroundSections k n (T m))
    (hG : ∀ m f x, (w m (globalOpen k n) (G m f)).val x = intoFraction k n f.val)
    (e₀ : ∀ m, polynomialDegree k n m ≃ₗ[k] GroundCohomology k n (T m) 0)
    (he₀ : ∀ m f, e₀ m f = sectionUnit k n (T m) (G m f))
    (eₙ : ∀ m, TopBasis k n (T := T) m)
    (heₙ : ∀ m, RepresentsTop k n c (d := d) hA hOrd m (eₙ m))
    {a b : ℤ} (hab : a + b = traceDegree n)
    (s : GroundSections k n (T a)) (y : GroundCohomology k n (T b) n) :
    endpointPairing k n e₀ eₙ a b (sectionUnit k n (T a) s) y =
      traceOf k n (eₙ (traceDegree n)) (traceAction k n μ hab s y) := by
  obtain ⟨f, rfl⟩ := (G a).surjective s
  obtain ⟨v, rfl⟩ := (eₙ b).surjective y
  rw [← he₀ a f]
  change laurentPair k n a b ((e₀ a).symm (e₀ a f)) ((eₙ b).symm (eₙ b v)) = _
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact (trace_multiplication k n c hA hOrd hc hw hd hn hμ eₙ heₙ hab (G a f) f (hG a f) v).symm

private theorem tracePairingForModel
    (hc : c.opens = chart k n) (hw : TwistCoordinates k n w) (hd : LocalizedTerms k n c w d)
    (hn : 1 ≤ n) {μ : GlobalMultiply k n T} (hμ : GlobalMultiplyFormula k n w μ)
    (hzero : ∀ m, ∃ e, RepresentsZero k n c (d := d) hA hOrd m e)
    (htop : ∀ m, ∃ e, RepresentsTop k n c (d := d) hA hOrd m e)
    (hv : ∀ (m : ℤ) (q : ℕ), 0 < q → q ≠ n → IsZero (GroundCohomology k n (T m) q)) :
    tracePairingOn k n c T w d μ hA hOrd := by
  classical
  have hg (m : ℤ) : ∃ g : polynomialDegree k n m ≃ₗ[k] GroundSections k n (T m),
      ∀ f x, (w m (globalOpen k n) (g f)).val x = intoFraction k n f.val := by
    obtain ⟨e, he⟩ := hzero m
    exact polynomialGlobalCoordinates k n c hw hd hA hOrd m e he
  choose Eₙ hEₙ using htop
  choose G hG using hg
  haveI (m : ℤ) : IsIso (sectionUnit k n (T m)) := sectionUnit_isIso k n (T m)
  let e₀ (m : ℤ) := (G m).trans (asIso (sectionUnit k n (T m))).toLinearEquiv
  have he₀ (m : ℤ) (f : polynomialDegree k n m) : e₀ m f = sectionUnit k n (T m) (G m f) := rfl
  let τ := traceOf k n (Eₙ (traceDegree n))
  let P := pairing k n e₀ Eₙ
  refine ⟨e₀, Eₙ, τ, P, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m f
    exact ⟨G m f, (he₀ m f).symm, hG m f⟩
  · exact hEₙ
  · intro f
    change (Eₙ _).symm (Eₙ _ f) (traceExponent n) = _
    rw [LinearEquiv.symm_apply_apply]
  · exact pairing_perfect k n e₀ Eₙ hn hv
  · as_aux_lemma =>
      intro m s y
      change pairing k n e₀ Eₙ m 0 n _ _ y = _
      rw [pairing_left]
      exact endpointPairing_action k n c (w := w) (d := d) hA hOrd hc hw hd hn hμ G hG e₀ he₀ Eₙ hEₙ
        (a := m) (b := traceDegree n - m) (by omega) s y
  · as_aux_lemma =>
      intro m y s
      change pairing k n e₀ Eₙ m n 0 _ y _ = _
      rw [pairing_right k n e₀ Eₙ hn]
      exact endpointPairing_action k n c (w := w) (d := d) hA hOrd hc hw hd hn hμ G hG e₀ he₀ Eₙ hEₙ
        (a := traceDegree n - m) (b := m) (by omega) s y
  · intro m q r hqr hq hr
    exact ⟨hv m q hq (by omega), hv (traceDegree n - m) r hr (by omega)⟩
  · exact pairing_monomial k n e₀ Eₙ


private theorem polynomialBasis_of_witnesses
    (data : (∀ m, descendedTwistClassFormula k n c d hOrd m (hA m))) (m : ℤ) :
    ∃ e, RepresentsZero k n c (d := d) hA hOrd m e :=
  (data m).1

private theorem topBasis_of_witnesses
    (data : (∀ m, descendedTwistClassFormula k n c d hOrd m (hA m))) (m : ℤ) :
    ∃ e, RepresentsTop k n c (d := d) hA hOrd m e :=
  (data m).2.1

private theorem isZero_of_witnesses (data : (∀ m, descendedTwistClassFormula k n c d hOrd m (hA m)))
    (m : ℤ) (q : ℕ) (hq : 0 < q) (hne : q ≠ n) :
    IsZero (GroundCohomology k n (T m) q) :=
  (data m).2.2.1 q hq hne

private theorem tracePairingFromWitnesses
    (hc : c.opens = chart k n) (hw : TwistCoordinates k n w) (hd : LocalizedTerms k n c w d)
    (hn : 1 ≤ n) {μ : GlobalMultiply k n T} (hμ : GlobalMultiplyFormula k n w μ)
    (data : (∀ m, descendedTwistClassFormula k n c d hOrd m (hA m))) :
    tracePairingOn k n c T w d μ hA hOrd :=
  tracePairingForModel k n c (w := w) (d := d) (μ := μ) hA hOrd hc hw hd hn hμ
    (polynomialBasis_of_witnesses k n c hA hOrd data)
    (topBasis_of_witnesses k n c hA hOrd data) (isZero_of_witnesses k n c hA hOrd data)

end Assembly

/-- The Laurent coefficient trace yields perfect pairings for all complementary
cohomological degrees of the projective twists. -/
theorem tracePairing : tracePairingType.{u} := by
  intro k _ n hn
  obtain ⟨c, T, w, d, μ, h, hc, hw, hd, hμ, _, hA, hOrd, hclasses⟩ :=
    DerivedFormalization.ProjectiveTwistCohomology.cohomology k n hn
  letI := h
  exact ⟨c, T, w, d, μ, h, hc, hw, hd, hμ, hA, hOrd,
    tracePairingFromWitnesses k n c (w := w) (d := d) (μ := μ) hA hOrd hc hw hd hn hμ hclasses⟩

end DerivedFormalization.TwistTracePairing
