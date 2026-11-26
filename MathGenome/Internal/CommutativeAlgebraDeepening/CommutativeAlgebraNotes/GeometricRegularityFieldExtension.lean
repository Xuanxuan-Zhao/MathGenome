import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.GeometricRegularityFieldExtension
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.RegularAuxiliaryRings
import Mathlib.Algebra.Polynomial.Eval.Subring
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! Geometric regularity under finitely generated field extensions. -/

universe u v w
open scoped TensorProduct
open Algebra.TensorProduct

namespace CommutativeAlgebraNotes.Excellence

private theorem isNoetherianRing_tensor_of_essFiniteType
    (k L T : Type*) [Field k] [Field L] [CommRing T] [Algebra k L] [Algebra k T]
    [Algebra.EssFiniteType k L] [IsNoetherianRing T] : IsNoetherianRing (L ⊗[k] T) := by
  let : IsNoetherianRing (T ⊗[k] L) := Algebra.EssFiniteType.isNoetherianRing T _
  exact isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm k T L).toRingEquiv

private theorem regularRing_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    [IsNoetherianRing A] (e : A ≃+* B) (h : RegularRing A) : RegularRing B := by
  let : IsNoetherianRing B := isNoetherianRing_of_ringEquiv A e
  let : IsRegularRing A := (regularRing_iff A).mp h
  exact (regularRing_iff B).mpr (IsRegularRing.of_ringEquiv e)

private theorem regularRing_localization {A : Type*} [CommRing A] (M : Submonoid A)
    (h : RegularRing A) : RegularRing (Localization M) := by
  intro q hq
  let := h (q.comap (algebraMap A (Localization M)))
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization M q).toRingEquiv

private theorem regularRing_rationalFunctionField (k T ι : Type*) [Field k] [CommRing T]
    [Algebra k T] [IsNoetherianRing T] [Finite ι] (h : RegularRing T) :
    RegularRing (FractionRing (MvPolynomial ι k) ⊗[k] T) := by
  let P := MvPolynomial ι k
  let Q := P ⊗[k] T
  let M := Algebra.algebraMapSubmonoid Q (nonZeroDivisors P)
  let e : Q ≃+* MvPolynomial ι T := (Algebra.TensorProduct.comm k P T).toRingEquiv.trans
    (MvPolynomial.algebraTensorAlgEquiv k T).toRingEquiv
  let : IsNoetherianRing Q := isNoetherianRing_of_ringEquiv _ e.symm
  have hQ := regularRing_of_ringEquiv e.symm (regularRing_mvPolynomial T ι h)
  let eLoc := (Localization.tensorRightAlgEquiv (nonZeroDivisors P) Q).symm.toRingEquiv
  let eCancel := (cancelBaseChange k P (FractionRing P) (FractionRing P) T).toRingEquiv
  exact regularRing_of_ringEquiv (eLoc.trans eCancel) (regularRing_localization M hQ)

private theorem regularRing_of_faithfullyFlat {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [IsNoetherianRing A] [IsNoetherianRing B] [Module.FaithfullyFlat A B]
    (h : RegularRing B) : RegularRing A := by
  intro p hp
  obtain ⟨q, hq, hqp⟩ := p.exists_isPrime_liesOver_of_faithfullyFlat (B := B)
  let := hq
  let := hqp
  let Ap := Localization.AtPrime p
  let Bq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : IsLocalHom (algebraMap Ap Bq) := by
    rw [Localization.AtPrime.algebraMap_eq p q]
    infer_instance
  exact isRegularLocalRing_of_flatLocal_target Ap Bq (h q)

open IntermediateField

private theorem restrictScalars_adjoin_eq_adjoin_range
    (k K E : Type*) [Field k] [Field K] [Field E] [Algebra k K]
    [Algebra K E] [Algebra k E] [IsScalarTower k K E] (s : Set E) :
    (adjoin K s).restrictScalars k = adjoin k (Set.range (algebraMap K E) ∪ s) := by
  apply le_antisymm
  · exact adjoin_le_subfield K s
      (Set.subset_union_left.trans (subset_adjoin k _))
      (Set.subset_union_right.trans (subset_adjoin k _))
  · exact adjoin_le_iff.mpr (Set.union_subset (adjoin.range_algebraMap_subset K s)
      (subset_adjoin K s))

private theorem adjoin_finite_constants_le
    (k K E : Type*) [Field k] [Field K] [Field E] [Algebra k K]
    [Algebra K E] [Algebra k E] [IsScalarTower k K E]
    (s : Set E) (c : Finset E) (hc : ∀ x ∈ c, x ∈ adjoin K s) :
    ∃ d : Finset K, ∀ x ∈ c, x ∈ adjoin (adjoin k (d : Set K)) s := by
  classical
  let A (d : Finset K) := adjoin k (algebraMap K E '' (d : Set K) ∪ s)
  have hA : Monotone A := fun _ _ h ↦ adjoin.mono k _ _
    (Set.union_subset_union_left s (Set.image_mono h))
  have hSup : (adjoin K s).restrictScalars k = ⨆ d, A d := by
    change (adjoin K s).restrictScalars k =
      ⨆ d : Finset K, adjoin k (algebraMap K E '' (d : Set K) ∪ s)
    rw [restrictScalars_adjoin_eq_adjoin_range, ← adjoin_iUnion]
    congr 1
    ext x
    simp only [Set.mem_union, Set.mem_range, Set.mem_iUnion, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro (⟨y, rfl⟩ | hx)
      · exact ⟨{y}, Or.inl ⟨y, Finset.mem_singleton_self y, rfl⟩⟩
      · exact ⟨∅, Or.inr hx⟩
    · rintro ⟨_, ⟨y, _, rfl⟩ | hx⟩
      · exact Or.inl ⟨y, rfl⟩
      · exact Or.inr hx
  have hex (x : c) : ∃ d, (x : E) ∈ A d := by
    have hx : (x : E) ∈ ((adjoin K s).restrictScalars k : Set E) := hc x x.2
    rwa [hSup, coe_iSup_of_directed hA.directed_le, Set.mem_iUnion] at hx
  choose d hd using hex
  refine ⟨c.attach.biUnion d, fun x hx ↦ ?_⟩
  have hmem := hA (show d ⟨x, hx⟩ ⊆ c.attach.biUnion d from
    fun _ hy ↦ Finset.mem_biUnion.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, hy⟩) (hd ⟨x, hx⟩)
  have hr (D : Finset K) : Set.range (algebraMap (adjoin k (D : Set K)) E) =
      (adjoin k (algebraMap K E '' (D : Set K)) : Set E) := by
    let f := IsScalarTower.toAlgHom k K E
    change Set.range (fun x : adjoin k (D : Set K) => f (x : K)) =
      (adjoin k (f '' (D : Set K)) : Set E)
    rw [← adjoin_map k (D : Set K) f]
    ext z
    exact ⟨fun ⟨x, hx⟩ ↦ ⟨x, x.2, hx⟩, fun ⟨x, hx, hz⟩ ↦ ⟨⟨x, hx⟩, hz⟩⟩
  change x ∈ A (c.attach.biUnion d) at hmem
  have heq (D : Finset K) : (adjoin (adjoin k (D : Set K)) s).restrictScalars k = A D := by
    change _ = adjoin k (algebraMap K E '' (D : Set K) ∪ s)
    rw [restrictScalars_adjoin_eq_adjoin_range, hr, adjoin_union, adjoin_self, adjoin_union]
  change x ∈ (adjoin (adjoin k (↑(c.attach.biUnion d) : Set K)) s).restrictScalars k
  rw [heq]
  exact hmem

private theorem regularRing_adjoin_independent
    (k E T : Type*) [Field k] [Field E] [CommRing T] [Algebra k E] [Algebra k T]
    [IsNoetherianRing T] (s : Finset E)
    (hs : AlgebraicIndependent k ((↑) : s → E)) (h : RegularRing T) :
    RegularRing (adjoin k (s : Set E) ⊗[k] T) := by
  let F := FractionRing (MvPolynomial s k)
  have hF := regularRing_rationalFunctionField k T s h
  have : Algebra.EssFiniteType k F := Algebra.EssFiniteType.comp k (MvPolynomial s k) F
  let := isNoetherianRing_tensor_of_essFiniteType k F T
  let e : F ≃ₐ[k] adjoin k (s : Set E) := hs.aevalEquivField.trans
    (IntermediateField.equivOfEq (by rw [Subtype.range_coe]))
  exact regularRing_of_ringEquiv (congr e (AlgEquiv.refl : T ≃ₐ[k] T)).toRingEquiv hF

private theorem regular_tensor_of_finite_separable_tower
    (k G P R : Type*) [Field k] [Field G] [Field P] [CommRing R]
    [Algebra k G] [Algebra k P] [Algebra G P] [IsScalarTower k G P] [Algebra k R]
    [Algebra.EssFiniteType k G] [Module.Finite G P] [Algebra.IsSeparable G P]
    [IsNoetherianRing R] (h : RegularRing (G ⊗[k] R)) :
    IsNoetherianRing (P ⊗[k] R) ∧ RegularRing (P ⊗[k] R) := by
  let := isNoetherianRing_tensor_of_essFiniteType k G R
  have hP := regularRing_separableScalarExtension G P (G ⊗[k] R) h
  let := isNoetherianRing_tensor_of_essFiniteType G P (G ⊗[k] R)
  let e := (cancelBaseChange k G P P R).toRingEquiv
  exact ⟨isNoetherianRing_of_ringEquiv _ e, regularRing_of_ringEquiv e hP⟩

private theorem fieldRange_eq_adjoin_image
    {k L E : Type*} [Field k] [Field L] [Field E] [Algebra k L] [Algebra k E]
    (g : L →ₐ[k] E) {s : Finset L} (hs : adjoin k (s : Set L) = ⊤) :
    g.fieldRange = adjoin k (g '' (s : Set L)) := by
  rw [← adjoin_map, hs, AlgHom.fieldRange_eq_map]

/-- The finitely many separable equations for generators from `L` descend
from the perfect constant field `K` to a finite extension of `k`. -/
private theorem regular_tensor_of_perfect_constants
    (k : Type u) (T : Type v) (L K E : Type w) [Field k] [Field L] [Field K] [Field E]
    [CommRing T] [Algebra k T] [Algebra k L] [Algebra k K] [Algebra K E] [Algebra k E]
    [IsScalarTower k K E] [Algebra.IsAlgebraic k K] [PerfectField K]
    [Algebra.EssFiniteType k L] [Algebra.EssFiniteType K E] [IsNoetherianRing T]
    (g : L →ₐ[k] E) (h : GeometricallyRegular k T) :
    RegularRing (L ⊗[k] T) := by
  classical
  obtain ⟨t, ht, htsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K E
  obtain ⟨s, hs⟩ := IntermediateField.fg_top k L
  let F := adjoin K (t : Set E)
  let : Algebra.IsSeparable F E := htsep
  let p (x : s) : Polynomial E := (minpoly F (g x)).map (algebraMap F E)
  let c : Finset E := Finset.univ.biUnion fun x : s ↦ (p x).coeffs
  obtain ⟨d, hd⟩ := adjoin_finite_constants_le k K E (t : Set E) c (by
    intro z hz
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨n, _, rfl⟩ := Polynomial.mem_coeffs_iff.mp hi
    dsimp only [p]
    rw [Polynomial.coeff_map]
    exact Subtype.property _)
  let K' := adjoin k (d : Set K)
  let : IsScalarTower k K' E := IsScalarTower.of_algebraMap_eq fun x ↦
    IsScalarTower.algebraMap_apply k K E x
  let G := adjoin K' (t : Set E)
  let : IsScalarTower k G E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let S : Set E := g '' (s : Set L)
  let P := adjoin G S
  have hsep (z : E) (hz : z ∈ S) : IsSeparable G z := by
    obtain ⟨x, hx, rfl⟩ := hz
    let i : s := ⟨x, hx⟩
    have hcoeff : (p i) ∈ (Polynomial.mapRingHom (algebraMap G E)).range := by
      apply (Polynomial.mem_map_range _).mpr
      intro n
      by_cases hzero : (p i).coeff n = 0
      · exact ⟨0, by simp [hzero]⟩
      · exact ⟨⟨(p i).coeff n, hd _ (Finset.mem_biUnion.mpr
          ⟨i, Finset.mem_univ _, Polynomial.coeff_mem_coeffs hzero⟩)⟩, rfl⟩
    obtain ⟨q, hq⟩ := hcoeff
    change q.map (algebraMap G E) = p i at hq
    have hroot : Polynomial.aeval (g x) q = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hq]
      simpa only [p, Polynomial.eval_map, ← Polynomial.aeval_def] using minpoly.aeval F (g x)
    have hpmin : (minpoly F (g x)).Separable := Algebra.IsSeparable.isSeparable F (g x)
    have hpsep : (p i).Separable := hpmin.map
    have hqsep : q.Separable := (Polynomial.separable_map _).mp (hq.symm ▸ hpsep)
    exact hqsep.of_dvd (minpoly.dvd G (g x) hroot)
  let : Algebra.IsSeparable G P := (isSeparable_adjoin_iff_isSeparable G E).mpr hsep
  let : Finite S := (s.finite_toSet.image g).to_subtype
  let : Module.Finite G P := Algebra.finite_of_essFiniteType_of_isAlgebraic
  let : Module.Finite k K' := Algebra.finite_of_essFiniteType_of_isAlgebraic
  have hsub : g.fieldRange ≤ P.restrictScalars k := by
    rw [fieldRange_eq_adjoin_image g hs]
    exact adjoin_le_iff.mpr (subset_adjoin G S)
  let gP : L →ₐ[k] P := g.codRestrict (P.restrictScalars k).toSubalgebra fun x ↦ hsub ⟨x, rfl⟩
  let : Algebra L P := gP.toRingHom.toAlgebra
  let : IsScalarTower k L P := IsScalarTower.of_algHom gP
  let : IsScalarTower k K' P := IsScalarTower.of_algebraMap_eq fun x ↦ by
    apply P.val.injective
    change algebraMap k E x = algebraMap K' E (algebraMap k K' x)
    exact IsScalarTower.algebraMap_apply k K' E x
  let R := K' ⊗[k] T
  let : Algebra K' R := inferInstanceAs (Algebra K' (K' ⊗[k] T))
  let : CommRing R := inferInstanceAs (CommRing (K' ⊗[k] T))
  let : Algebra K' G := inferInstanceAs (Algebra K' (adjoin K' (t : Set E)))
  obtain ⟨hR, hreg⟩ := h.regular_tensorProduct K'
  let : IsNoetherianRing R := hR
  have hG := regularRing_adjoin_independent K' E R t
    (ht.1.restrictScalars (RingHom.injective (algebraMap K' K))) hreg
  obtain ⟨hPn, hP⟩ := regular_tensor_of_finite_separable_tower K' G P R hG
  let := hPn
  let A := L ⊗[k] T
  let B := A ⊗[L] P
  let e : B ≃+* P ⊗[k] T := (Algebra.TensorProduct.comm L A P).toRingEquiv.trans
    (cancelBaseChange k L P P T).toRingEquiv
  let e' := (cancelBaseChange k K' P P T).toRingEquiv.trans e.symm
  let : IsNoetherianRing B := isNoetherianRing_of_ringEquiv _ e'
  let : IsNoetherianRing A := isNoetherianRing_tensor_of_essFiniteType k L T
  exact regularRing_of_faithfullyFlat (regularRing_of_ringEquiv e' hP)

private theorem GeometricallyRegular.regular_tensor_of_essFiniteType
    {k : Type u} {T : Type v} {L : Type w} [Field k] [CommRing T] [Field L]
    [Algebra k T] [Algebra k L] [Algebra.EssFiniteType k L]
    (h : GeometricallyRegular k T) :
    IsNoetherianRing (L ⊗[k] T) ∧ RegularRing (L ⊗[k] T) := by
  let : IsNoetherianRing (k ⊗[k] T) := (h.regular_tensorProduct k).1
  let : IsNoetherianRing T := isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.lid k T).toRingEquiv
  refine ⟨isNoetherianRing_tensor_of_essFiniteType k L T, ?_⟩
  obtain ⟨s, hs⟩ := IntermediateField.fg_top k L
  let Ω := AlgebraicClosure L
  let K := algebraicClosure k Ω
  let : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  let f := IsScalarTower.toAlgHom k L Ω
  let S : Set Ω := f '' (s : Set L)
  let M := adjoin K S
  let : Finite S := (s.finite_toSet.image f).to_subtype
  have hsub : f.fieldRange ≤ M.restrictScalars k := by
    rw [fieldRange_eq_adjoin_image f hs]
    exact adjoin_le_iff.mpr (subset_adjoin K S)
  let g : L →ₐ[k] M := f.codRestrict (M.restrictScalars k).toSubalgebra fun x ↦ hsub ⟨x, rfl⟩
  exact regular_tensor_of_perfect_constants k T L K M g h

/-- Geometric regularity persists under finitely generated field extension. -/
theorem GeometricallyRegular.fieldExtension : Specs.geometricallyRegular_fieldExtensionType.{u,v,w} := by
  intro k T L _ _ _ _ _ _ h N _ _ _
  change GeometricallyRegular k T at h
  let : Algebra k N := Algebra.compHom N (algebraMap k L)
  let : IsScalarTower k L N := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.EssFiniteType k N := Algebra.EssFiniteType.comp k L N
  obtain ⟨hn, hr⟩ := h.regular_tensor_of_essFiniteType (L := N)
  let := hn
  let e := (cancelBaseChange k L N N T).symm.toRingEquiv
  exact ⟨isNoetherianRing_of_ringEquiv _ e, regularRing_of_ringEquiv e hr⟩

end CommutativeAlgebraNotes.Excellence
