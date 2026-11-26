import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.RegularElementEulerCancellation
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.RingTheory.Flat.CategoryTheory
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ChangeOfRingsTor
import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Regular.Category
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.BigOperators.Finprod
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.AugmentedDoubleComplexComparison

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct nonZeroDivisors Pointwise BigOperators
open P103.Specs.Ch10.Comparison (LeftResolution)
open P103.Specs.Ch10.Complexes (Homology cycles)
open P103.Specs.Ch12.TorBaseChange (coefficientComplex extendComplex)
open HomologicalComplex
open CommutativeAlgebraNotes.Intersection.IsolatedTorSupport
  (Tor torRightEquiv tor_finite_length_of_tensor)
open CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler
  (cutoffEuler intersectionEuler regularLocalDimension ringKrullDim_eq_regularLocalDimension
    cutoffEuler_eq_of_vanishes_above)

namespace CommutativeAlgebraNotes.Intersection.RegularElementEulerCancellation

open CommutativeAlgebraNotes.Intersection.RegularElementEulerCancellation.Specs
  (QuotientRing restrict IsBoundedFiniteFree)

universe u v w

variable {S : Type u} [CommRing S]

private instance restrictedTower (h : S) (M : ModuleCat.{v} (QuotientRing h)) :
    IsScalarTower S (QuotientRing h) (restrict h M) where
  smul_assoc s a m := mul_smul (Ideal.Quotient.mk _ s) a (show M from m)

private instance finiteRestricted (h : S) (M : ModuleCat.{v} (QuotientRing h))
    [Module.Finite (QuotientRing h) M] : Module.Finite S (restrict h M) := by
  let : Module.Finite S (QuotientRing h) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ S _).toLinearMap Ideal.Quotient.mk_surjective
  let : Module.Finite (QuotientRing h) (restrict h M) :=
    ‹Module.Finite (QuotientRing h) M›
  exact Module.Finite.trans (R := S) (QuotientRing h) (restrict h M)

private def tensorRestrictionEquiv (h : S) (M : ModuleCat.{v} (QuotientRing h))
    (N : ModuleCat.{w} (QuotientRing h)) :
    restrict h (ModuleCat.of (QuotientRing h) (M ⊗[QuotientRing h] N)) ≃ₗ[S]
      (restrict h M ⊗[S] restrict h N) := by
  letI : TensorProduct.CompatibleSMul S (QuotientRing h) (restrict h M) (restrict h N) :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective _ _ (Ideal.Quotient.mk_surjective)
  exact TensorProduct.equivOfCompatibleSMul S (QuotientRing h) S (restrict h M) (restrict h N)

/-- Isolation over the quotient implies finite length of every ambient Tor group. -/
theorem tor_finite_length : Specs.torFiniteLength.{u,v,w} := by
  intro S _ _ _ h M N _ _ hMN i
  apply tor_finite_length_of_tensor (restrict h M) (restrict h N) _ i
  refine Module.length_ne_top_iff.mp ?_
  rw [← (tensorRestrictionEquiv h M N).length_eq,
    Module.length_eq_of_surjective (R := QuotientRing h) (Ideal.Quotient.mk_surjective)]
  exact Module.length_ne_top_iff.mpr hMN

private theorem homology_subsingleton_of_term {R : Type u} [CommRing R]
    (C : ChainComplex (ModuleCat.{v} R) ℕ) (i : ℕ) [Subsingleton (C.X i)] :
    Subsingleton (Homology C i) := by
  have : Subsingleton (cycles C i) := Subtype.coe_injective.subsingleton
  infer_instance

/-- The bound on the ambient free resolution of the second module is a Tor cutoff. -/
theorem tor_vanishes_above : Specs.torVanishesAbove.{u,v,w} := by
  intro S _ h M N Q q hQ i hi
  let := hQ.2.2 i hi
  have hterm : Subsingleton ((coefficientComplex (S := S) Q.complex (restrict h M)).X i) :=
    inferInstanceAs (Subsingleton (restrict h M ⊗[S] Q.complex.X i))
  have he := torRightEquiv (restrict h M) (restrict h N) Q
    (P103.Ch10.ProjectiveResolutions.free_is_projective S _ Q hQ.1) i
  have := homology_subsingleton_of_term (coefficientComplex (S := S) Q.complex (restrict h M)) i
  exact he.injective.subsingleton

/-- All cutoffs above the nonzero ambient Tor groups give the same sum. -/
theorem cutoff_euler_eq_resolution_bound (h : S) (M : ModuleCat.{v} (QuotientRing h))
    (N : ModuleCat.{w} (QuotientRing h)) (Q : LeftResolution S (restrict h N))
    (q d : ℕ) (hQ : IsBoundedFiniteFree Q q)
    (hd : ∀ i : ℕ, d < i → Subsingleton (Tor (restrict h M) (restrict h N) i)) :
    cutoffEuler (restrict h M) (restrict h N) d =
      cutoffEuler (restrict h M) (restrict h N) q := by
  have h₁ := cutoffEuler_eq_of_vanishes_above (restrict h M) (restrict h N)
    d (max d q) (le_max_left ..) hd
  have h₂ := cutoffEuler_eq_of_vanishes_above (restrict h M) (restrict h N)
    q (max d q) (le_max_right ..) (tor_vanishes_above h M N Q q hQ)
  exact h₁.symm.trans h₂

private abbrev quotientFunctor (h : S) : ModuleCat.{v} (QuotientRing h) ⥤ ModuleCat.{v} S :=
  ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span ({h} : Set S)))

private abbrev reduceComplex (h : S) (C : ChainComplex (ModuleCat.{max u v} S) ℕ) :=
  extendComplex (QuotientRing h) C

private abbrev restrictComplex (h : S) (C : ChainComplex (ModuleCat.{v} (QuotientRing h)) ℕ) :=
  ((quotientFunctor h).mapHomologicalComplex (ComplexShape.down ℕ)).obj C

private def reduceMap (h : S) (C : ChainComplex (ModuleCat.{max u v} S) ℕ) :
    C ⟶ restrictComplex h (reduceComplex h C) where
  f i := ModuleCat.ofHom (X := C.X i) (Y := (restrictComplex h (reduceComplex h C)).X i)
    (TensorProduct.mk S (QuotientRing h) (C.X i) 1)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

private theorem quotient_smul_zero (h : S) (M : ModuleCat.{v} (QuotientRing h))
    (x : restrict h M) : h • x = 0 := by
  change Ideal.Quotient.mk (Ideal.span ({h} : Set S)) h • (show M from x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton h)), zero_smul]

private def multiplicationReduction (h : S) (C : ChainComplex (ModuleCat.{max u v} S) ℕ) :
    ShortComplex (ChainComplex (ModuleCat.{max u v} S) ℕ) :=
  ShortComplex.mk (h • 𝟙 C) (reduceMap h C) (by
    apply HomologicalComplex.hom_ext
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (1 : QuotientRing h) ⊗ₜ[S] (h • x) = 0
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    change Ideal.Quotient.mk (Ideal.span ({h} : Set S)) h ⊗ₜ[S] x = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton h)),
      TensorProduct.zero_tmul])

private theorem multiplicationReduction_shortExact (h : S) (hh : h ∈ S⁰)
    (C : ChainComplex (ModuleCat.{max u v} S) ℕ) (hC : ∀ i, Module.Flat S (C.X i)) :
    (multiplicationReduction h C).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  let I : Ideal S := Ideal.span ({h} : Set S)
  let e := TensorProduct.quotTensorEquivQuotSMul (C.X i) I
  let m : C.X i →ₗ[S] (QuotientRing h) ⊗[S] (C.X i) := TensorProduct.mk S _ _ 1
  have he := TensorProduct.quotTensorEquivQuotSMul_comp_mk (M := C.X i) I
  have hs : Function.Surjective m := by
    have hcomp : Function.Surjective (e.toLinearMap.comp m) := by
      rw [he]
      exact Submodule.mkQ_surjective _
    simpa only [LinearMap.coe_comp] using
      Function.Surjective.of_comp_left (f := e) (g := m) hcomp e.injective
  have hex : Function.Exact (LinearMap.lsmul S (C.X i) h) m := by
    intro x
    change m x = 0 ↔ _
    rw [← e.map_eq_zero_iff]
    change (e.toLinearMap.comp m) x = 0 ↔ _
    rw [he]
    change (Submodule.Quotient.mk x : C.X i ⧸ I • ⊤) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    change x ∈ Ideal.span ({h} : Set S) • (⊤ : Submodule S (C.X i)) ↔ _
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    simp
  apply ModuleCat.shortComplex_shortExact
  · exact hex
  · let := hC i
    exact Module.Flat.isSMulRegular_of_nonZeroDivisors (M := C.X i) hh
  · exact hs

open private categoricalHomologyEquiv from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.IsolatedTorSupport

private def resolutionHomologyZero (h : S) (N : ModuleCat.{w} (QuotientRing h))
    (Q : LeftResolution S (restrict h N)) :
    Q.complex.homology 0 ≃ₗ[S] restrict h N :=
  (categoricalHomologyEquiv Q.complex 0).trans
    (P103.Ch10.ProjectiveResolutions.homology_zero S _ Q).choose

private theorem resolutionHomologySucc (h : S) (N : ModuleCat.{w} (QuotientRing h))
    (Q : LeftResolution S (restrict h N)) (n : ℕ) :
    IsZero (Q.complex.homology (n + 1)) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  have := P103.Ch10.ProjectiveResolutions.homology_succ S _ Q n
  exact (categoricalHomologyEquiv Q.complex (n + 1)).injective.subsingleton

private theorem homologyMap_smul_id (C : ChainComplex (ModuleCat.{max u v} S) ℕ)
    (h : S) (i : ℕ) : homologyMap (h • 𝟙 C) i = h • 𝟙 (C.homology i) := by
  change ShortComplex.homologyMap (h • 𝟙 (C.sc i)) = _
  simp only [ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
  rfl

private def restrictHomologyIso (h : S)
    (C : ChainComplex (ModuleCat.{max u v} (QuotientRing h)) ℕ) (i : ℕ) :
    (restrictComplex h C).homology i ≅ restrict h (C.homology i) :=
  (C.sc i).mapHomologyIso (quotientFunctor h)

private def quotientLinearEquiv (h : S) {V : ModuleCat.{v} (QuotientRing h)}
    {W : ModuleCat.{w} (QuotientRing h)} (e : restrict h V ≃ₗ[S] restrict h W) : V ≃ₗ[QuotientRing h] W where
  __ := e.toAddEquiv
  map_smul' a x := by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact e.map_smul s x

private theorem reducedHomologyHigh (h : S) (hh : h ∈ S⁰) (N : ModuleCat.{w} (QuotientRing h))
    (Q : LeftResolution S (restrict h N)) (hQ : Q.IsFree) (n : ℕ) :
    IsZero ((reduceComplex h Q.complex).homology (n + 2)) := by
  let T := multiplicationReduction h Q.complex
  have hT : T.ShortExact :=
    multiplicationReduction_shortExact h hh Q.complex (fun i => by
      have := hQ i
      infer_instance)
  have hz₁ : IsZero (T.X₂.homology (n + 2)) := resolutionHomologySucc h N Q (n + 1)
  have hz₂ : IsZero (T.X₁.homology (n + 1)) := resolutionHomologySucc h N Q n
  have hz : IsZero (T.X₃.homology (n + 2)) :=
    (hT.homology_exact₃ (n + 2) (n + 1) rfl).isZero_of_both_zeros
      (hz₁.eq_of_src _ _) (hz₂.eq_of_tgt _ _)
  have hz' : IsZero (restrict h ((reduceComplex h Q.complex).homology (n + 2))) :=
    IsZero.of_iso hz (restrictHomologyIso h (reduceComplex h Q.complex) (n + 2)).symm
  have hsub := ModuleCat.isZero_iff_subsingleton.mp hz'
  exact ModuleCat.isZero_iff_subsingleton.mpr hsub

/-- The reduction sequence computes the two low homology groups with their quotient action. -/
private def reducedHomologyLow (h : S) (hh : h ∈ S⁰) (N : ModuleCat.{w} (QuotientRing h))
    (Q : LeftResolution S (restrict h N)) (hQ : Q.IsFree) (i : Fin 2) :
    (reduceComplex h Q.complex).homology (i : ℕ) ≃ₗ[QuotientRing h] N := by
  let T := multiplicationReduction h Q.complex
  have hT : T.ShortExact :=
    multiplicationReduction_shortExact h hh Q.complex (fun j => by
      have := hQ j
      infer_instance)
  let e := resolutionHomologyZero h N Q
  have hz : homologyMap T.f 0 = 0 := by
    change homologyMap (h • 𝟙 Q.complex) 0 = 0
    rw [homologyMap_smul_id]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (h • x : Q.complex.homology 0) = 0
    apply e.injective
    rw [e.map_smul, e.map_zero, quotient_smul_zero]
  have hp : IsZero (Q.complex.homology 1) := resolutionHomologySucc h N Q 0
  have e' : T.X₃.homology (i : ℕ) ≃ₗ[S] restrict h N := by
    by_cases hr : (i : ℕ) = 0
    · rw [hr]
      have hm : Mono (homologyMap T.g 0) := (hT.homology_exact₂ 0).mono_g hz
      have he : Epi (homologyMap T.g 0) := by
        have := hT.epi_g
        exact epi_homologyMap_of_epi_of_not_rel T.g 0 (by simp)
      letI := isIso_of_mono_of_epi (homologyMap T.g 0)
      exact (asIso (homologyMap T.g 0)).symm.toLinearEquiv.trans e
    · rw [show (i : ℕ) = 1 by have := i.isLt; omega]
      have hm : Mono (hT.δ 1 0 rfl) := hT.mono_δ 1 0 rfl hp
      have he : Epi (hT.δ 1 0 rfl) := (hT.homology_exact₁ 1 0 rfl).epi_f hz
      letI := isIso_of_mono_of_epi (hT.δ 1 0 rfl)
      exact (asIso (hT.δ 1 0 rfl)).toLinearEquiv.trans e
  exact quotientLinearEquiv h
    ((restrictHomologyIso h (reduceComplex h Q.complex) (i : ℕ)).symm.toLinearEquiv.trans e')

private def integerLength {R : Type u} [CommRing R] (M : ModuleCat.{v} R) : ℤ :=
  (Module.length R M).toNat

private theorem integerLength_iso {R : Type u} [CommRing R] {M N : ModuleCat.{v} R}
    (e : M ≅ N) : integerLength M = integerLength N := by
  unfold integerLength
  rw [e.toLinearEquiv.length_eq]

private theorem integerLength_of_isZero {R : Type u} [CommRing R] {M : ModuleCat.{v} R}
    (hM : IsZero M) : integerLength M = 0 := by
  have := ModuleCat.isZero_iff_subsingleton.mp hM
  simp [integerLength, Module.length_eq_zero]

private theorem length_add_homology {R : Type u} [CommRing R]
    (B : ShortComplex (ModuleCat.{v} R)) :
    Module.length R B.X₂ =
      Module.length R (LinearMap.range B.f.hom) + Module.length R B.homology +
        Module.length R (LinearMap.range B.g.hom) := by
  let Z := LinearMap.ker B.g.hom
  let I := LinearMap.range B.moduleCatToCycles
  have h₁ : Module.length R B.X₂ =
      Module.length R Z + Module.length R (LinearMap.range B.g.hom) := by
    let g := B.g.hom.rangeRestrict
    have h := Module.length_eq_add_of_exact (LinearMap.ker g).subtype g
      (Submodule.subtype_injective _) B.g.hom.surjective_rangeRestrict
      (LinearMap.exact_subtype_ker_map g)
    have hk : g.ker = Z := LinearMap.ker_rangeRestrict B.g.hom
    rwa [hk] at h
  have h₂ : Module.length R Z = Module.length R I + Module.length R B.homology := by
    have he : B.homology ≃ₗ[R] Z ⧸ I := B.moduleCatHomologyIso.toLinearEquiv
    rw [he.length_eq]
    exact Module.length_eq_add_of_exact I.subtype I.mkQ I.subtype_injective
      I.mkQ_surjective (LinearMap.exact_subtype_mkQ I)
  have h₃ : Module.length R I = Module.length R (LinearMap.range B.f.hom) := by
    have he : Submodule.map Z.subtype I = LinearMap.range B.f.hom := by
      change Submodule.map Z.subtype (LinearMap.range (B.f.hom.codRestrict Z
        B.moduleCat_zero_apply)) = _
      rw [← LinearMap.range_comp]
      rfl
    exact ((Submodule.equivMapOfInjective Z.subtype Z.subtype_injective I).trans
      (LinearEquiv.ofEq _ _ he)).length_eq
  rw [h₁, h₂, h₃]

private theorem integerLength_add_homology {R : Type u} [CommRing R]
    (B : ShortComplex (ModuleCat.{v} R)) (hB : IsFiniteLength R B.X₂) :
    integerLength B.X₂ =
      integerLength (ModuleCat.of R (LinearMap.range B.f.hom)) + integerLength B.homology +
        integerLength (ModuleCat.of R (LinearMap.range B.g.hom)) := by
  have h := length_add_homology B
  have hne : Module.length R B.X₂ ≠ ⊤ := Module.length_ne_top_iff.mpr hB
  have hlt := lt_top_iff_ne_top.mpr hne
  rw [h] at hlt
  obtain ⟨h₁, h₂⟩ := ENat.add_lt_top.mp hlt
  obtain ⟨h₃, h₄⟩ := ENat.add_lt_top.mp h₁
  simpa only [integerLength, ENat.toNat_add h₃.ne h₄.ne,
    ENat.toNat_add h₁.ne h₂.ne, Nat.cast_add] using
    congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) h

section Pages

open AdvancedHomologicalAlgebra
open FiniteFiltrationConvergence

variable {R : Type u} [CommRing R] {C : CochainComplex (ModuleCat.{v} R) ℤ}
  (F : Filtration C) (D : F03Specs.PageData F)

private abbrev pageTerm (r : ℤ) (x : ℤ × ℤ) :=
  PageCohomology.object F D r x.1 x.2

private def pageEuler (r : ℤ) : ℤ :=
  ∑ᶠ x : ℤ × ℤ, (x.2.negOnePow : ℤ) * integerLength (pageTerm F D r x)

private def differentialShift (r : ℤ) : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun x := (x.1 + r, x.2 + 1)
  invFun x := (x.1 - r, x.2 - 1)
  left_inv x := by simp
  right_inv x := by simp

private theorem sign_differentialShift (r : ℤ) (x : ℤ × ℤ) :
    ((differentialShift r x).2.negOnePow : ℤ) = -((x.2.negOnePow : ℤ)) := by
  change ((x.2 + 1).negOnePow : ℤ) = _
  simp [Int.negOnePow_succ]

set_option maxHeartbeats 700000 in
/-- The next page is again of finite length and supported in the same set. -/
private theorem page_succ_finite (r : ℤ) (hr : 0 ≤ r) (s : Set (ℤ × ℤ))
    (hfin : ∀ x, IsFiniteLength R (pageTerm F D r x))
    (hzero : ∀ x ∉ s, IsZero (pageTerm F D r x)) :
    (∀ x, IsFiniteLength R (pageTerm F D (r+1) x)) ∧
      (∀ x ∉ s, IsZero (pageTerm F D (r+1) x)) := by
  constructor
  · intro x
    obtain ⟨y, rfl⟩ := (differentialShift r).surjective x
    let B := PageCohomology.shortComplex F D r hr y.1 y.2
    let e : pageTerm F D (r+1) (differentialShift r y) ≅ B.homology :=
      PageCohomology.nextIso F D r hr y.1 y.2
    have hne := Module.length_ne_top_iff.mpr (hfin (differentialShift r y))
    change Module.length R B.X₂ ≠ ⊤ at hne
    have hlt := lt_top_iff_ne_top.mpr hne
    rw [length_add_homology B] at hlt
    apply Module.length_ne_top_iff.mp
    rw [e.toLinearEquiv.length_eq]
    exact (ENat.add_lt_top.mp (ENat.add_lt_top.mp hlt).1).2.ne
  · intro x hx
    obtain ⟨y, rfl⟩ := (differentialShift r).surjective x
    let B := PageCohomology.shortComplex F D r hr y.1 y.2
    have hz : IsZero B.X₂ := hzero (differentialShift r y) hx
    exact IsZero.of_iso ((B.exact_iff_isZero_homology).mp (B.exact_of_isZero_X₂ hz))
      (PageCohomology.nextIso F D r hr y.1 y.2)

set_option maxHeartbeats 3000000 in
private theorem pageEuler_succ (r : ℤ) (hr : 0 ≤ r) (s : Set (ℤ × ℤ))
    (hs : s.Finite) (hfin : ∀ x, IsFiniteLength R (pageTerm F D r x))
    (hzero : ∀ x ∉ s, IsZero (pageTerm F D r x)) :
    pageEuler F D (r+1) = pageEuler F D r := by
  let σ := differentialShift r
  let a (k : ℤ) (x : ℤ × ℤ) := (x.2.negOnePow : ℤ) * integerLength (pageTerm F D k x)
  let b (x : ℤ × ℤ) := (x.2.negOnePow : ℤ) *
    integerLength (ModuleCat.of R (LinearMap.range (D.differential r hr x.1 x.2).hom))
  have hb : Function.HasFiniteSupport b := hs.subset (by
    intro x hx
    by_contra hxs
    have hz := (hzero x hxs).eq_of_src (D.differential r hr x.1 x.2) 0
    apply hx
    have hz' : (D.differential r hr x.1 x.2).hom = 0 := by rw [hz]; rfl
    dsimp only [b, integerLength]
    rw [hz', LinearMap.range_zero, Module.length_bot]
    simp)
  have han : Function.HasFiniteSupport (a (r+1)) := hs.subset (by
    intro x hx
    by_contra hxs
    exact hx (by simp [a, integerLength_of_isZero ((page_succ_finite F D r hr s hfin hzero).2 x hxs)]))
  have hanσ : Function.HasFiniteSupport (fun x => a (r+1) (σ x)) :=
    han.preimage σ.injective.injOn
  have hbσ : Function.HasFiniteSupport (fun x => b (σ x)) :=
    hb.preimage σ.injective.injOn
  have hpoint (x : ℤ × ℤ) :
      a r (σ x) = -b x + (a (r+1) (σ x) + b (σ x)) := by
    let B := PageCohomology.shortComplex F D r hr x.1 x.2
    let e : pageTerm F D (r+1) (σ x) ≅ B.homology := PageCohomology.nextIso F D r hr x.1 x.2
    have h := integerLength_add_homology B (hfin (σ x))
    change integerLength (pageTerm F D r (σ x)) =
      integerLength (ModuleCat.of R (LinearMap.range (D.differential r hr x.1 x.2).hom)) +
      integerLength B.homology +
      integerLength (ModuleCat.of R (LinearMap.range (D.differential r hr (σ x).1 (σ x).2).hom)) at h
    change a r (σ x) = -b x + (a (r+1) (σ x) + b (σ x))
    have hsx : ((σ x).2.negOnePow : ℤ) = -(x.2.negOnePow : ℤ) := sign_differentialShift r x
    dsimp only [a, b]
    rw [integerLength_iso e, h, hsx]
    ring
  have hneg : (∑ᶠ x, -b x) + (∑ᶠ x, b x) = 0 := by
    change finsum (-b) + finsum b = 0
    rw [← finsum_add_distrib hb.neg hb]
    simp
  symm
  change (∑ᶠ x, a r x) = (∑ᶠ x, a (r+1) x)
  rw [← finsum_comp_equiv σ (f := a r), finsum_congr hpoint]
  change finsum (fun x => (-b) x + ((fun y => a (r+1) (σ y)) + fun y => b (σ y)) x) =
    finsum (a (r+1))
  rw [finsum_add_distrib hb.neg (hanσ.add hbσ)]
  change finsum (-b) + finsum (fun x => a (r+1) (σ x) + b (σ x)) = _
  rw [finsum_add_distrib hanσ hbσ,
    finsum_comp_equiv σ (f := a (r+1)), finsum_comp_equiv σ (f := b)]
  change finsum (-b) + (finsum (a (r+1)) + finsum b) = _
  change finsum (-b) + finsum b = 0 at hneg
  omega

private theorem integerLength_add_shortExact (B : ShortComplex (ModuleCat.{v} R))
    (hB : B.ShortExact) (hf : IsFiniteLength R B.X₂) :
    integerLength B.X₂ = integerLength B.X₁ + integerLength B.X₃ := by
  have h := Module.length_eq_add_of_exact B.f.hom B.g.hom hB.moduleCat_injective_f
    hB.moduleCat_surjective_g ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact B).mp hB.exact)
  have hlt := lt_top_iff_ne_top.mpr (Module.length_ne_top_iff.mpr hf)
  rw [h] at hlt
  obtain ⟨ha, hb⟩ := ENat.add_lt_top.mp hlt
  simpa only [integerLength, ENat.toNat_add ha.ne hb.ne, Nat.cast_add] using
    congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) h

private theorem filtrationEuler (hF : DegreewiseFinite F) (n : ℤ)
    (hH : IsFiniteLength R (C.homology n)) :
    (∑ᶠ p : ℤ, integerLength (gradedCohomology F p n)) =
      integerLength (C.homology n) := by
  let P (p : ℤ) := cohomologyPiece F p n
  let g (p : ℤ) := integerLength (gradedCohomology F p n)
  let l (p : ℤ) := integerLength (P p : ModuleCat R)
  have hstep (p : ℤ) : l p = l (p+1) + g p := by
    have hf : IsFiniteLength R (P p : ModuleCat R) :=
      hH.of_injective (f := (P p).arrow.hom) ((ModuleCat.mono_iff_injective _).mp inferInstance)
    exact integerLength_add_shortExact (FiniteTargetComparison.stepSequence F p n)
      (FiniteTargetComparison.stepSequence_shortExact F p n) hf
  obtain ⟨a, b₀, ha, hb₀⟩ := (cohomology_filtration F hF).finite n
  let b := max a b₀
  have hb (p : ℤ) (hp : b ≤ p) : P p = ⊥ := hb₀ p ((le_max_right _ _).trans hp)
  have htop (p : ℤ) (hp : p ≤ a) : l p = integerLength (C.homology n) := by
    have := (Subobject.isIso_arrow_iff_eq_top (P p)).mpr (ha p hp)
    exact integerLength_iso (asIso (P p).arrow)
  have hbot (p : ℤ) (hp : b ≤ p) : l p = 0 :=
    integerLength_of_isZero (FiniteTargetComparison.subobject_isZero_of_eq_bot _ (hb p hp))
  let k := (b-a).toNat
  have hk : a + (k : ℤ) = b := by
    have hz : 0 ≤ b-a := sub_nonneg.mpr (le_max_left a b₀)
    have hh := Int.toNat_of_nonneg hz
    unfold k
    omega
  let e : ℕ ↪ ℤ := ⟨fun j => a + j, fun i j hij => by change a + (i : ℤ) = a + (j : ℤ) at hij; omega⟩
  have hsupport : Function.support g ⊆ ↑((Finset.range k).map e) := by
    intro p hp
    by_cases h₁ : p < a
    · have h := hstep p
      rw [htop p (by omega), htop (p+1) (by omega)] at h
      exact False.elim (hp (by omega))
    · by_cases h₂ : p < b
      · let j := (p-a).toNat
        have hj : (j : ℤ) = p-a := Int.toNat_of_nonneg (by omega)
        apply Finset.mem_map.mpr
        exact ⟨j, Finset.mem_range.mpr (by omega), by change a + (j : ℤ) = p; omega⟩
      · have h := hstep p
        rw [hbot p (by omega), hbot (p+1) (by omega)] at h
        exact False.elim (hp (by omega))
  have hsum (m : ℕ) : l a = l (a + m) + ∑ j ∈ Finset.range m, g (a + j) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, Nat.cast_succ, ← add_assoc a]
      have h := hstep (a + m)
      omega
  change finsum g = _
  rw [finsum_eq_sum_of_support_subset g hsupport, Finset.sum_map]
  change (∑ j ∈ Finset.range k, g (a + j)) = _
  have h := hsum k
  rw [hk, hbot b le_rfl, htop a le_rfl, zero_add] at h
  exact h.symm


/-- A stable page records the lengths of the associated graded objects of total homology. -/
private theorem pageEuler_limit (s t : Finset ℤ)
    (hE : ∀ x, IsFiniteLength R (pageTerm F D 2 x))
    (hE0 : ∀ x ∉ (↑(s ×ˢ t) : Set (ℤ × ℤ)), IsZero (pageTerm F D 2 x))
    (hC : DoubleComplexConvergence.Converges F)
    (hH : ∀ n, IsFiniteLength R (C.homology n)) :
    pageEuler F D 2 = ∑ n ∈ t, (n.negOnePow : ℤ) * integerLength (C.homology n) := by
  let support : Set (ℤ × ℤ) := ↑(s ×ˢ t)
  have hsf : support.Finite := Finset.finite_toSet _
  have hpage (k : ℕ) :
      (∀ x, IsFiniteLength R (pageTerm F D (2+(k : ℤ)) x)) ∧
      (∀ x ∉ support, IsZero (pageTerm F D (2+(k : ℤ)) x)) ∧
      pageEuler F D (2+(k : ℤ)) = pageEuler F D 2 := by
    induction k with
    | zero => rw [Int.natCast_zero, add_zero]; exact ⟨hE, hE0, rfl⟩
    | succ k ih =>
      rw [Nat.cast_succ, ← add_assoc]
      have hpos : 0 ≤ 2 + (k : ℤ) := by omega
      have hnext := page_succ_finite F D (2+(k : ℤ)) hpos support ih.1 ih.2.1
      exact ⟨hnext.1, hnext.2,
        (pageEuler_succ F D (2+(k : ℤ)) hpos support hsf ih.1 ih.2.1).trans ih.2.2⟩
  let bound (n : ℤ) := (hC.stabilization n).choose.toNat
  let k := t.sup bound
  let r : ℤ := 2 + (k : ℤ)
  have hr : 0 ≤ r := by dsimp [r]; omega
  have he (p n : ℤ) (hn : n ∈ t) : pageTerm F D r (p,n) ≅ gradedCohomology F p n := by
    have hb : bound n ≤ k := Finset.le_sup hn
    have hh := (hC.stabilization n).choose_spec
    have hh' : ((bound n : ℕ) : ℤ) = (hC.stabilization n).choose :=
      Int.toNat_of_nonneg hh.1
    exact (hC.limit D r p n hr (hh.2 r (by dsimp [r]; omega) p)).some.iso
  have hgr (n : ℤ) (hn : n ∈ t) :
      (∑ p ∈ s, integerLength (gradedCohomology F p n)) = integerLength (C.homology n) := by
    have hz : Function.support (fun p => integerLength (gradedCohomology F p n)) ⊆ ↑s := by
      intro p hp
      by_contra hps
      apply hp
      have hz := (hpage k).2.1 (p,n) (by simpa [support, Finset.mem_product, hn] using hps)
      exact integerLength_of_isZero (IsZero.of_iso hz (he p n hn).symm)
    rw [← finsum_eq_sum_of_support_subset _ hz]
    exact filtrationEuler F hC.finite n (hH n)
  rw [← (hpage k).2.2]
  have hz : Function.support (fun x => (x.2.negOnePow : ℤ) *
      integerLength (pageTerm F D r x)) ⊆ ↑(s ×ˢ t) := by
    intro x hx
    by_contra hs
    have hh : integerLength (pageTerm F D r x) = 0 :=
      integerLength_of_isZero ((hpage k).2.1 x hs)
    exact hx (by change (x.2.negOnePow : ℤ) * integerLength (pageTerm F D r x) = 0
                 rw [hh, mul_zero])
  change (∑ᶠ x, (x.2.negOnePow : ℤ) * integerLength (pageTerm F D r x)) = _
  rw [finsum_eq_sum_of_support_subset _ hz, Finset.sum_product, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  change (∑ p ∈ s, (n.negOnePow : ℤ) * integerLength (pageTerm F D r (p,n))) = _
  rw [← Finset.mul_sum, ← hgr n hn]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  exact integerLength_iso (he p n hn)

end Pages

section Extension
universe u₁ u₂ v₁ v₂
variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
  [HasZeroMorphisms A] [HasZeroMorphisms B] [HasZeroObject A] [HasZeroObject B]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (F : A ⥤ B) [F.PreservesZeroMorphisms] (C : HomologicalComplex A c) (e : c.Embedding c')
  [DecidableEq ι']

private def extendMapIsoAt (i : ι') :
    ((F.mapHomologicalComplex c').obj (C.extend e)).X i ≅
      (((F.mapHomologicalComplex c).obj C).extend e).X i := by
  classical
  by_cases hi : ∃ j, e.f j = i
  · exact F.mapIso (C.extendXIso e hi.choose_spec) ≪≫
      (((F.mapHomologicalComplex c).obj C).extendXIso e hi.choose_spec).symm
  · exact (F.map_isZero (C.isZero_extend_X e i (by simpa using hi))).iso
      (((F.mapHomologicalComplex c).obj C).isZero_extend_X e i (by simpa using hi))

omit [DecidableEq ι'] in
private theorem extendMapIsoAt_of_mem {i : ι'} {j : ι} (h : e.f j = i) :
    extendMapIsoAt F C e i =
      F.mapIso (C.extendXIso e h) ≪≫
        (((F.mapHomologicalComplex c).obj C).extendXIso e h).symm := by
  have hi : ∃ j, e.f j = i := ⟨j,h⟩
  have hj : hi.choose = j := e.injective_f (hi.choose_spec.trans h.symm)
  subst j
  simp [extendMapIsoAt, hi]

private def extendMapIso :
    (F.mapHomologicalComplex c').obj (C.extend e) ≅
      ((F.mapHomologicalComplex c).obj C).extend e := by
  refine HomologicalComplex.Hom.isoOfComponents (extendMapIsoAt F C e) ?_
  intro i j _
  by_cases hi : ∃ a, e.f a = i
  · by_cases hj : ∃ b, e.f b = j
    · rw [extendMapIsoAt_of_mem F C e hi.choose_spec, extendMapIsoAt_of_mem F C e hj.choose_spec]
      change _ ≫ (((F.mapHomologicalComplex c).obj C).extend e).d i j =
        F.map ((C.extend e).d i j) ≫ _
      rw [extend_d_eq _ _ hi.choose_spec hj.choose_spec, extend_d_eq _ _ hi.choose_spec hj.choose_spec]
      simp [Functor.map_comp]
    · apply (((F.mapHomologicalComplex c).obj C).isZero_extend_X e j (by simpa using hj)).eq_of_tgt
  · apply (F.map_isZero (C.isZero_extend_X e i (by simpa using hi))).eq_of_src

end Extension

section TensorBicomplex
open AdvancedHomologicalAlgebra.DoubleComplexFirstPages

universe a b
variable (R : Type u) [CommRing R]

private def tensorLeft (U : ModuleCat.{a} R) : ModuleCat.{b} R ⥤ ModuleCat.{max a b} R where
  obj V := ModuleCat.of R (U ⊗[R] V)
  map f := ModuleCat.ofHom (f.hom.lTensor U)
  map_id V := ModuleCat.hom_ext (LinearMap.lTensor_id U V)
  map_comp _ _ := ModuleCat.hom_ext (LinearMap.lTensor_comp _ _ _)

private instance (U : ModuleCat.{a} R) : (tensorLeft.{u,a,b} R U).Additive where
  map_add := by
    intros
    apply ModuleCat.hom_ext
    exact LinearMap.lTensor_add _ _ _

private instance (U : ModuleCat.{a} R) [Module.Flat R U] :
    (tensorLeft.{u,a,b} R U).PreservesHomology := by
  apply ((Functor.exact_tfae (tensorLeft R U)).out 2 3).mp
  intro B hB
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hB ⊢
  exact Module.Flat.lTensor_exact U hB

private def tensorBifunctor : ModuleCat.{a} R ⥤ ModuleCat.{b} R ⥤ ModuleCat.{max a b} R where
  obj U := tensorLeft R U
  map f :=
    { app := fun V => ModuleCat.ofHom (f.hom.rTensor V)
      naturality := by
        intro V W g
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro x y
        rfl }
  map_id U := by
    apply NatTrans.ext
    funext V
    apply ModuleCat.hom_ext
    exact LinearMap.rTensor_id (R := R) V U
  map_comp f g := by
    apply NatTrans.ext
    funext V
    apply ModuleCat.hom_ext
    exact LinearMap.rTensor_comp _ _ _

private instance : (tensorBifunctor.{u,a,b} R).Additive where
  map_add := by
    intros
    apply NatTrans.ext
    funext V
    apply ModuleCat.hom_ext
    exact LinearMap.rTensor_add _ _ _

private instance (U : ModuleCat.{a} R) : ((tensorBifunctor.{u,a,b} R).obj U).Additive :=
  inferInstanceAs ((tensorLeft R U).Additive)

private instance (U : ModuleCat.{a} R) [Module.Flat R U] :
    ((tensorBifunctor.{u,a,b} R).obj U).PreservesHomology :=
  inferInstanceAs ((tensorLeft R U).PreservesHomology)

private instance (V : ModuleCat.{b} R) : ((tensorBifunctor.{u,a,b} R).flip.obj V).Additive where
  map_add := by
    intros
    apply ModuleCat.hom_ext
    exact LinearMap.rTensor_add _ _ _

private instance (V : ModuleCat.{b} R) [Module.Flat R V] :
    ((tensorBifunctor.{u,a,b} R).flip.obj V).PreservesHomology := by
  apply ((Functor.exact_tfae ((tensorBifunctor R).flip.obj V)).out 2 3).mp
  intro B hB
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hB ⊢
  exact Module.Flat.rTensor_exact V hB

private abbrev tensorBicomplex (P : CochainComplex (ModuleCat.{a} R) ℤ)
    (Q : CochainComplex (ModuleCat.{b} R) ℤ) :=
  ((Functor.mapBifunctorHomologicalComplex (tensorBifunctor R) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ)).obj P).obj Q

private def tensorVerticalHomologyIso (P : CochainComplex (ModuleCat.{a} R) ℤ)
    (Q : CochainComplex (ModuleCat.{b} R) ℤ) (hP : ∀ p, Module.Flat R (P.X p)) (q : ℤ) :
    verticalHomology (tensorBicomplex R P Q) q ≅
      ((((tensorBifunctor R).flip.obj (Q.homology q)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
  letI (p : ℤ) := hP p
  refine HomologicalComplex.Hom.isoOfComponents (fun p => (Q.sc q).mapHomologyIso
    (tensorLeft R (P.X p))) ?_
  intro p p' hp'
  let f := (tensorBifunctor R).map (P.d p p')
  let e := (Q.sc q).mapHomologyIso ((tensorBifunctor R).obj (P.X p))
  let e' := (Q.sc q).mapHomologyIso ((tensorBifunctor R).obj (P.X p'))
  change e.hom ≫ f.app (Q.sc q).homology =
    ShortComplex.homologyMap ((Q.sc q).mapNatTrans f) ≫ e'.hom
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp [e, e']

end TensorBicomplex


section ChangeOfRings

open AdvancedHomologicalAlgebra
open AdvancedHomologicalAlgebra.ChangeOfRingsTor (negativeChainEmbedding quotientHomologyIso)
open DoubleComplexFirstPages DoubleTotalization FiniteDiagonalFiltrations

private instance : negativeChainEmbedding.IsRelIff where
  rel' i j h := by
    change -(i : ℤ) + 1 = -(j : ℤ) at h
    change j + 1 = i
    omega

private abbrev regrade {R : Type u} [CommRing R] (C : ChainComplex (ModuleCat.{v} R) ℕ) :=
  C.extend negativeChainEmbedding

private theorem regrade_zero {R : Type u} [CommRing R] (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (i : ℤ) (hi : 0 < i) : IsZero ((regrade C).X i) :=
  C.isZero_extend_X negativeChainEmbedding i (fun j hj => by
    change -(j : ℤ) = i at hj
    omega)

private theorem regrade_flat {R : Type u} [CommRing R] (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (hC : ∀ i, Module.Flat R (C.X i)) (i : ℤ) : Module.Flat R ((regrade C).X i) := by
  by_cases hi : i ≤ 0
  · let j := (-i).toNat
    have hj : negativeChainEmbedding.f j = i := by
      change -(j : ℤ) = i
      dsimp [j]
      omega
    have := hC j
    exact Module.Flat.of_linearEquiv (C.extendXIso negativeChainEmbedding hj).toLinearEquiv
  · have := ModuleCat.isZero_iff_subsingleton.mp (regrade_zero C i (by omega))
    infer_instance

private theorem tensorBicomplex_finite {R : Type u} [CommRing R]
    (P : ChainComplex (ModuleCat.{v} R) ℕ) (Q : ChainComplex (ModuleCat.{w} R) ℕ) :
    FiniteDiagonals (tensorBicomplex R (regrade P) (regrade Q)) := by
  intro n
  let K := tensorBicomplex R (regrade P) (regrade Q)
  let s : Set (Diagonal n) := {i | ¬ IsZero (diagonalFamily K n i)}
  have hb (i : Diagonal n) (hi : i ∈ s) : i.val.1 ≤ 0 ∧ i.val.2 ≤ 0 := by
    constructor
    · by_contra! hp
      exact hi (Functor.map_isZero ((tensorBifunctor R).flip.obj ((regrade Q).X i.val.2))
        (regrade_zero P i.val.1 hp))
    · by_contra! hq
      exact hi (Functor.map_isZero ((tensorBifunctor R).obj ((regrade P).X i.val.1))
        (regrade_zero Q i.val.2 hq))
  apply Set.Finite.of_finite_image (f := fun i : Diagonal n => i.val.1)
  · apply (Set.finite_Icc n 0).subset
    rintro _ ⟨i, hi, rfl⟩
    have h := hb i hi
    have hi' := i.property
    refine ⟨?_, h.1⟩
    change n ≤ i.val.1
    omega
  · intro i _ j _ hij
    apply Subtype.ext
    apply Prod.ext hij
    have := i.property
    have := j.property
    dsimp at hij
    omega

private def tensorRightComparison {R : Type u} [CommRing R]
    (C : ChainComplex (ModuleCat.{max u v} R) ℕ) (N : ModuleCat.{w} R) :
    ((((tensorBifunctor R).flip.obj N).mapHomologicalComplex (ComplexShape.down ℕ)).obj C) ≅
      coefficientComplex (S := R) C N := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i => (TensorProduct.comm R (C.X i) N).toModuleIso) ?_
  intro i j _
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  rfl

private def coefficientChangeIso {R : Type u} [CommRing R]
    (C : ChainComplex (ModuleCat.{max u v} R) ℕ)
    (M : ModuleCat.{w} R) (M' : ModuleCat.{max u w} R) (e : M' ≃ₗ[R] M) :
    coefficientComplex (S := R) C M' ≅ coefficientComplex (S := R) C M := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i => (TensorProduct.congr e (LinearEquiv.refl R (C.X i))).toModuleIso) ?_
  intro i j _
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  rfl

private def secondPageRow (h : S) (hh : h ∈ S⁰)
    (M : ModuleCat.{v} (QuotientRing h)) (N : ModuleCat.{w} (QuotientRing h))
    (P : LeftResolution (QuotientRing h) M) (Q : LeftResolution S (restrict h N))
    (hP : P.IsFree) (hQ : Q.IsFree)
    (i : ℕ) (j : Fin 2) :
    (verticalHomology (tensorBicomplex (QuotientRing h)
      (regrade P.complex) (regrade (reduceComplex h Q.complex))) (-(j.val : ℤ))).homology
        (-(i : ℤ)) ≅ ModuleCat.of (QuotientRing h) (Tor M N i) := by
  let A := QuotientRing h
  let Pc := regrade P.complex
  let C := reduceComplex h Q.complex
  let Cc := regrade C
  let j' : ℤ := -(j.val : ℤ)
  let i' : ℤ := -(i : ℤ)
  let F := (tensorBifunctor A).flip
  let N' : ModuleCat.{max u w} A := ModuleCat.of A (ULift.{u} N)
  let el : N' ≃ₗ[A] N := ULift.moduleEquiv
  let eN : Cc.homology j' ≅ N' :=
    C.extendHomologyIso negativeChainEmbedding rfl ≪≫
      ((reducedHomologyLow h hh N Q hQ j).trans el.symm).toModuleIso
  have hFlat : ∀ k, Module.Flat A (Pc.X k) :=
    regrade_flat P.complex (fun k => by have := hP k; infer_instance)
  let e₁ := tensorVerticalHomologyIso A Pc Cc hFlat j'
  let e₂ := (NatIso.mapHomologicalComplex (F.mapIso eN) (ComplexShape.up ℤ)).app Pc
  let e₃ := extendMapIso (F.obj N') P.complex negativeChainEmbedding
  let e₄ := (negativeChainEmbedding.extendFunctor _).mapIso
    (tensorRightComparison P.complex N' ≪≫ coefficientChangeIso P.complex N N' el)
  let e := e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄
  let L := coefficientComplex (S := A) P.complex N
  exact HomologicalComplex.homologyMapIso e i' ≪≫ L.extendHomologyIso negativeChainEmbedding rfl ≪≫
    quotientHomologyIso L i ≪≫
    (CommutativeAlgebraNotes.Intersection.IsolatedTorSupport.torLeftEquiv M N P
      (P103.Ch10.ProjectiveResolutions.free_is_projective A M P hP) i).symm.toModuleIso

private def augmentationTarget {R : Type u} [CommRing R] (M : ModuleCat.{v} R) :
    ModuleCat.{max u v} R := ModuleCat.of R (ULift.{u} M)

private def resolutionAugmentation {R : Type u} [CommRing R]
    (M : ModuleCat.{v} R) (P : LeftResolution R M) :
    P.complex ⟶ (HomologicalComplex.single (ModuleCat.{max u v} R)
      (ComplexShape.down ℕ) 0).obj (augmentationTarget M) := by
  let g : P.complex.X 0 ⟶ augmentationTarget M :=
    ModuleCat.ofHom ((ULift.moduleEquiv : augmentationTarget M ≃ₗ[R] M).symm.toLinearMap.comp P.ε)
  have hg : ∀ i, (ComplexShape.down ℕ).Rel i 0 → P.complex.d i 0 ≫ g = 0 := by
    intro i hi
    change 0+1 = i at hi
    subst i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hx : (P.complex.d 1 0).hom x ∈ LinearMap.ker P.ε := by
      rw [← P.exact_zero]
      exact LinearMap.mem_range_self _ x
    change ULift.up (P.ε ((P.complex.d 1 0).hom x)) = 0
    rw [LinearMap.mem_ker.mp hx]
    rfl
  exact HomologicalComplex.mkHomToSingle g hg

private theorem resolutionAugmentation_quasiIso {R : Type u} [CommRing R]
    (M : ModuleCat.{v} R) (P : LeftResolution R M) :
    QuasiIso (resolutionAugmentation M P) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  cases i with
  | succ i =>
    have := P103.Ch10.ProjectiveResolutions.homology_succ R M P i
    have hP : IsZero (P.complex.homology (i+1)) :=
      ModuleCat.isZero_iff_subsingleton.mpr ((categoricalHomologyEquiv P.complex (i+1)).injective.subsingleton)
    exact hP.isIso (isZero_single_obj_homology _ 0 _ _ (by omega)) _
  | zero =>
    let T := (HomologicalComplex.single (ModuleCat.{max u v} R)
      (ComplexShape.down ℕ) 0).obj (augmentationTarget M)
    let f : P.complex ⟶ T := resolutionAugmentation M P
    let g : P.complex.X 0 ⟶ augmentationTarget M :=
      ModuleCat.ofHom ((ULift.moduleEquiv : augmentationTarget M ≃ₗ[R] M).symm.toLinearMap.comp P.ε)
    have hfg : P.complex.d 1 0 ≫ g = 0 := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      have hx : (P.complex.d 1 0).hom x ∈ LinearMap.ker P.ε := by
        rw [← P.exact_zero]
        exact LinearMap.mem_range_self _ x
      change ULift.up (P.ε ((P.complex.d 1 0).hom x)) = 0
      rw [LinearMap.mem_ker.mp hx]
      rfl
    let B := ShortComplex.mk _ _ hfg
    have hB : B.Exact := by
      apply (ShortComplex.moduleCat_exact_iff_range_eq_ker B).mpr
      change LinearMap.range (P.complex.d 1 0).hom = LinearMap.ker g.hom
      rw [P.exact_zero]
      exact ((ULift.moduleEquiv : augmentationTarget M ≃ₗ[R] M).symm.ker_comp P.ε).symm
    have : Epi B.g := (ModuleCat.epi_iff_surjective _).mpr
      ((ULift.moduleEquiv : augmentationTarget M ≃ₗ[R] M).symm.surjective.comp P.surjective)
    let cp := P.complex.opcyclesIsCokernel (i := 1) (j := 0) (by simp)
    let cg := hB.gIsCokernel
    let eP := cp.coconePointUniqueUpToIso cg
    let eT := singleObjXSelf (ComplexShape.down ℕ) 0 (augmentationTarget M)
    have : IsIso (T.pOpcycles 0) :=
      T.isIso_pOpcycles 1 0 (by simp) (single_obj_d (ComplexShape.down ℕ) 0 (augmentationTarget M) 1 0)
    let eT' := asIso (T.pOpcycles 0)
    have heP : P.complex.pOpcycles 0 ≫ eP.hom = g :=
      IsColimit.comp_coconePointUniqueUpToIso_hom cp cg WalkingParallelPair.one
    have hf : f.f 0 = g ≫ eT.inv := by
      dsimp only [f, resolutionAugmentation]
      exact mkHomToSingle_f _ _
    have he : opcyclesMap f 0 ≫ eT'.inv ≫ eT.hom = eP.hom := by
      rw [← cancel_epi (P.complex.pOpcycles 0), heP, p_opcyclesMap_assoc]
      change f.f 0 ≫ T.pOpcycles 0 ≫ eT'.inv ≫ eT.hom = _
      rw [hf, Category.assoc]
      change g ≫ eT.inv ≫ eT'.hom ≫ eT'.inv ≫ eT.hom = g
      rw [eT'.hom_inv_id_assoc, eT.inv_hom_id, Category.comp_id]
    have hmap : opcyclesMap f 0 = (eP ≪≫ eT.symm ≪≫ eT').hom := by
      apply (cancel_mono (eT'.inv ≫ eT.hom)).mp
      rw [he]
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
        Iso.inv_hom_id, Category.comp_id]
    change IsIso (homologyMap f 0)
    rw [← isIso_comp_right_iff (homologyMap f 0) (T.homologyι 0), homologyι_naturality, hmap]
    infer_instance

private def tensorSingleAxisIso {R : Type u} [CommRing R] (M : ModuleCat.{v} R)
    (C : CochainComplex (ModuleCat.{w} R) ℤ) :
    (tensorBicomplex R ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M) C).flip ≅
    AugmentedDoubleComplexComparison.axisComplex
      (((tensorLeft R M).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) := by
  let F := (tensorBifunctor R).flip
  refine HomologicalComplex.Hom.isoOfComponents (fun j =>
    (singleMapHomologicalComplex (F.obj (C.X j)) (ComplexShape.up ℤ) 0).app M) ?_
  intro i j _
  let τ := F.map (C.d i j)
  change _ ≫ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map (τ.app M) =
    (τ.mapHomologicalComplex (ComplexShape.up ℤ)).app
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M) ≫ _
  rw [natTransMapHomologicalComplex_app_single_obj]
  simp

/-- The augmentation of the first complex gives a quasi-isomorphism on totals. -/
private def abutmentIso {R : Type u} [CommRing R] (M : ModuleCat.{v} R)
    (P : LeftResolution R M) (C : ChainComplex (ModuleCat.{w} R) ℕ)
    (hC : ∀ j, Module.Flat R (C.X j))
    [(tensorBicomplex R (regrade P.complex) (regrade C)).HasTotal (ComplexShape.up ℤ)]
    (n : ℤ) :
    (sumTotal (tensorBicomplex R (regrade P.complex) (regrade C))).homology n ≅
      (regrade (((tensorLeft R (augmentationTarget M)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj C)).homology n := by
  let K := tensorBicomplex R (regrade P.complex) (regrade C)
  let Cc := regrade C
  let L := ((tensorLeft R (augmentationTarget M)).mapHomologicalComplex (ComplexShape.up ℤ)).obj Cc
  let single := HomologicalComplex.single (ModuleCat.{max u v} R) (ComplexShape.up ℤ) 0
  let T := (HomologicalComplex.single _ (ComplexShape.down ℕ) 0).obj (augmentationTarget M)
  let e : regrade T ≅ single.obj (augmentationTarget M) :=
    extendSingleIso negativeChainEmbedding _ 0 0 rfl
  let a : regrade P.complex ⟶ single.obj (augmentationTarget M) :=
    (negativeChainEmbedding.extendFunctor _).map (resolutionAugmentation M P) ≫ e.hom
  have ha : QuasiIso a := by
    have := resolutionAugmentation_quasiIso M P
    change QuasiIso (extendMap (resolutionAugmentation M P) negativeChainEmbedding ≫ e.hom)
    infer_instance
  let J := tensorBicomplex R (single.obj (augmentationTarget M)) Cc
  have hJ : FiniteDiagonals J := by
    intro j
    refine (Set.finite_singleton (⟨(0,j),zero_add j⟩ : Diagonal j)).subset ?_
    intro x hx
    have hs : x.val.1 = 0 := by
      by_contra hne
      apply hx
      exact Functor.map_isZero ((tensorBifunctor R).flip.obj (Cc.X x.val.2))
        (isZero_single_obj_X _ 0 _ _ hne)
    apply Set.mem_singleton_iff.mpr
    apply Subtype.ext
    have hxy := x.property
    exact Prod.ext hs (by change x.val.2 = j; omega)
  letI : J.HasTotal (ComplexShape.up ℤ) := (totalizationsExist J hJ).1
  let f : K ⟶ J :=
    ((Functor.mapBifunctorHomologicalComplex (tensorBifunctor R) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)).map a).app Cc
  have hf : QuasiIso (HomologicalComplex₂.total.map f (ComplexShape.up ℤ)) := by
    apply DoubleComplexConvergence.double_complex_comparison K J
      (tensorBicomplex_finite P.complex C) hJ f
    right
    intro j
    let : Module.Flat R (Cc.X j) := regrade_flat C hC j
    change QuasiIso ((((tensorBifunctor R).flip.obj (Cc.X j)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map a)
    exact HomologicalComplex.quasiIso_map_of_preservesHomology a _
  let eJ : J.flip ≅ AugmentedDoubleComplexComparison.axisComplex L := tensorSingleAxisIso _ Cc
  let b : sumTotal J ≅ L :=
    (J.totalFlipIso (ComplexShape.up ℤ)).symm ≪≫ HomologicalComplex₂.total.mapIso eJ _ ≪≫
      (asIso (AugmentedDoubleComplexComparison.axisInclusion L)).symm
  let eC := extendMapIso (tensorLeft R (augmentationTarget M)) C negativeChainEmbedding
  letI := (quasiIsoAt_iff_isIso_homologyMap _ n).mp (hf.quasiIsoAt n)
  exact asIso (homologyMap (HomologicalComplex₂.total.map f (ComplexShape.up ℤ)) n) ≪≫
    homologyMapIso (b ≪≫ eC) n

private def restrictCoefficientIso (h : S) (M : ModuleCat.{v} (QuotientRing h))
    (C : ChainComplex (ModuleCat.{max u w} S) ℕ) :
    restrictComplex h (coefficientComplex (S := QuotientRing h) C (restrict h M)) ≅
      coefficientComplex (S := S) C (restrict h M) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun i => ?_) ?_
  · let U := restrict h ((coefficientComplex (S := QuotientRing h) C (restrict h M)).X i)
    let V := (coefficientComplex (S := S) C (restrict h M)).X i
    let f : U →ₗ[S] V :=
      { toFun := fun z => z
        map_add' := fun _ _ => rfl
        map_smul' := fun s z => by
          change (algebraMap S (QuotientRing h) s) •
            (show restrict h M ⊗[S] C.X i from z) = (s • z : V)
          exact IsScalarTower.algebraMap_smul (QuotientRing h) s z }
    exact (LinearEquiv.ofBijective f Function.bijective_id).toModuleIso
  · intro i j _
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    rfl

private def leftTensorCoefficientIso {R : Type u} [CommRing R] (M : ModuleCat.{v} R)
    (C : ChainComplex (ModuleCat.{max u w} R) ℕ) :
    ((tensorLeft R M).mapHomologicalComplex (ComplexShape.down ℕ)).obj C ≅
      coefficientComplex (S := R) C M := by
  refine HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) ?_
  intro i j _
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  rfl

/-- Compare total homology over the quotient with ambient Tor after restriction. -/
private theorem totalHomologyLength (h : S) (M : ModuleCat.{v} (QuotientRing h))
    (N : ModuleCat.{w} (QuotientRing h))
    (P : LeftResolution (QuotientRing h) M) (Q : LeftResolution S (restrict h N))
    (hQ : Q.IsFree)
    [(tensorBicomplex (QuotientRing h) (regrade P.complex)
      (regrade (reduceComplex h Q.complex))).HasTotal (ComplexShape.up ℤ)]
    (i : ℕ) :
    Module.length (QuotientRing h)
      ((sumTotal (tensorBicomplex (QuotientRing h) (regrade P.complex)
        (regrade (reduceComplex h Q.complex)))).homology (-(i : ℤ))) =
      Module.length S (Tor (restrict h M) (restrict h N) i) := by
  let A := QuotientRing h
  let C := reduceComplex h Q.complex
  let M' := augmentationTarget M
  let eM : M' ≃ₗ[A] M := ULift.moduleEquiv
  let L := ((tensorLeft A M').mapHomologicalComplex (ComplexShape.down ℕ)).obj C
  have hflat : ∀ j, Module.Flat A (C.X j) := fun j => by
    have := hQ j
    change Module.Flat A (A ⊗[S] Q.complex.X j)
    infer_instance
  let e₁ := abutmentIso M P C hflat (-(i : ℤ)) ≪≫ L.extendHomologyIso negativeChainEmbedding rfl
  let C₁ := coefficientComplex (S := A) Q.complex (restrict h M)
  let e₂ : L ≅ C₁ :=
    leftTensorCoefficientIso M' C ≪≫ coefficientChangeIso C M M' eM ≪≫
      P103.Ch12.TorBaseChange.firstTensorIso (S := A) Q.complex (restrict h M)
  rw [e₁.toLinearEquiv.length_eq, (HomologicalComplex.homologyMapIso e₂ i).toLinearEquiv.length_eq]
  let C₂ := coefficientComplex (S := S) Q.complex (restrict h M)
  let e₃ : restrict h (C₁.homology i) ≅ C₂.homology i :=
    (restrictHomologyIso.{u, max v w} h C₁ i).symm ≪≫
      HomologicalComplex.homologyMapIso (restrictCoefficientIso h M Q.complex) i
  have hl : Module.length S (restrict h (C₁.homology i)) = Module.length A (C₁.homology i) := by
    have : IsScalarTower S A (restrict h (C₁.homology i)) := restrictedTower h (C₁.homology i)
    exact Module.length_eq_of_surjective (R := A) (M := restrict h (C₁.homology i))
      Ideal.Quotient.mk_surjective
  rw [← hl, e₃.toLinearEquiv.length_eq, (quotientHomologyIso C₂ i).toLinearEquiv.length_eq]
  exact (torRightEquiv (restrict h M) (restrict h N) Q
    (P103.Ch10.ProjectiveResolutions.free_is_projective S _ Q hQ) i).length_eq.symm

private abbrev regradedDegrees (d : ℕ) : Finset ℤ :=
  (Finset.range (d + 1)).map (⟨negativeChainEmbedding.f, negativeChainEmbedding.injective_f⟩ : ℕ ↪ ℤ)

private theorem mem_regradedDegrees (d : ℕ) (p : ℤ) :
    p ∈ regradedDegrees d ↔ -(d : ℤ) ≤ p ∧ p ≤ 0 := by
  rw [regradedDegrees, Finset.mem_map]
  change (∃ i ∈ Finset.range (d + 1), -(i : ℤ) = p) ↔ _
  simp only [Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · intro hp
    exact ⟨(-p).toNat, by omega, by omega⟩

private theorem regrade_zero_outside {R : Type u} [CommRing R]
    (C : ChainComplex (ModuleCat.{v} R) ℕ) (d : ℕ)
    (hC : ∀ i : ℕ, d < i → Subsingleton (C.X i))
    (p : ℤ) (hp : p ∉ regradedDegrees d) : IsZero ((regrade C).X p) := by
  by_cases hpos : 0 < p
  · exact regrade_zero C p hpos
  · let i := (-p).toNat
    have hi : negativeChainEmbedding.f i = p := by change -(i : ℤ) = p; dsimp [i]; omega
    have hpi := (mem_regradedDegrees d p).not.mp hp
    have : Subsingleton (C.X i) := hC i (by dsimp [i]; omega)
    exact IsZero.of_iso (ModuleCat.isZero_iff_subsingleton.mpr this)
      (C.extendXIso negativeChainEmbedding hi)

private theorem reducedHomologyRegraded_zero (h : S) (hh : h ∈ S⁰)
    (N : ModuleCat.{w} (QuotientRing h)) (Q : LeftResolution S (restrict h N)) (hQ : Q.IsFree)
    (q : ℤ) (hq₀ : q ≠ 0) (hq₁ : q ≠ -1) :
    IsZero ((regrade (reduceComplex h Q.complex)).homology q) := by
  let C := reduceComplex h Q.complex
  by_cases hpos : 0 < q
  · exact (HomologicalComplex.ExactAt.of_isZero (regrade_zero C q hpos)).isZero_homology
  · let i := (-q-2).toNat
    have hi : negativeChainEmbedding.f (i + 2) = q := by
      change -((i + 2 : ℕ) : ℤ) = q
      dsimp [i]
      omega
    exact IsZero.of_iso (reducedHomologyHigh h hh N Q hQ i)
      (C.extendHomologyIso negativeChainEmbedding hi)

private theorem secondPageVanishing (h : S) (hh : h ∈ S⁰)
    (M : ModuleCat.{v} (QuotientRing h)) (N : ModuleCat.{w} (QuotientRing h))
    (P : LeftResolution (QuotientRing h) M) (Q : LeftResolution S (restrict h N))
    (p : ℕ) (hP : IsBoundedFiniteFree P p) (hQ : Q.IsFree) (a b : ℤ)
    (hz : a ∉ regradedDegrees p ∨ (b ≠ 0 ∧ b ≠ -1)) :
    IsZero ((verticalHomology (tensorBicomplex (QuotientRing h) (regrade P.complex)
      (regrade (reduceComplex h Q.complex))) b).homology a) := by
  let A := QuotientRing h
  let Pc := regrade P.complex
  let Cc := regrade (reduceComplex h Q.complex)
  have hf : ∀ k, Module.Flat A (P.complex.X k) := fun k => by
    have := hP.1 k
    infer_instance
  let e := tensorVerticalHomologyIso A Pc Cc (regrade_flat P.complex hf) b
  apply IsZero.of_iso _ (homologyMapIso e a)
  apply HomologicalComplex.ExactAt.isZero_homology
  apply HomologicalComplex.ExactAt.of_isZero
  change IsZero ((tensorBifunctor A).obj (Pc.X a) |>.obj (Cc.homology b))
  rcases hz with ha | hb
  · exact Functor.map_isZero ((tensorBifunctor A).flip.obj (Cc.homology b))
      (regrade_zero_outside P.complex p hP.2.2 a ha)
  · exact Functor.map_isZero ((tensorBifunctor A).obj (Pc.X a))
      (reducedHomologyRegraded_zero h hh N Q hQ b hb.1 hb.2)

private def columnSecondAt {R : Type u} [CommRing R]
    (K : Bicomplex (ModuleCat.{v} R)) [K.HasTotal (ComplexShape.up ℤ)]
    (F : Filtration (sumTotal K)) (hF : HasFiltrationFormula K Prod.fst F)
    (D : F03Specs.PageData F) (a n : ℤ) :
    pageTerm F D 2 (a,n) ≅ (verticalHomology K (n-a)).homology a :=
  eqToIso (congrArg (PageCohomology.object F D 2 a) (by omega : n = a + (n-a))) ≪≫
    columnSecondIso K F hF D a (n-a)

private theorem twoRowPageEulerZero {R : Type u} [CommRing R]
    {C : CochainComplex (ModuleCat.{v} R) ℤ} (F : Filtration C) (D : F03Specs.PageData F)
    (s t : Finset ℤ)
    (ht : ∀ a ∈ s, a ∈ t ∧ a-1 ∈ t)
    (hz : ∀ a n : ℤ, a ∉ s ∨ (n ≠ a ∧ n ≠ a-1) → IsZero (pageTerm F D 2 (a,n)))
    (he : ∀ a ∈ s, integerLength (pageTerm F D 2 (a,a)) =
      integerLength (pageTerm F D 2 (a,a-1))) :
    pageEuler F D 2 = 0 := by
  classical
  have hs : Function.support (fun x : ℤ × ℤ =>
      (x.2.negOnePow : ℤ) * integerLength (pageTerm F D 2 x)) ⊆ ↑(s ×ˢ t) := by
    rintro ⟨a,n⟩ hx
    by_contra h
    have h' : a ∉ s ∨ (n ≠ a ∧ n ≠ a-1) := by
      by_cases ha : a ∈ s
      · right
        have hn : n ∉ t := fun hn => h (Finset.mem_product.mpr ⟨ha, hn⟩)
        exact ⟨fun eq => hn (eq.symm ▸ (ht a ha).1), fun eq => hn (eq.symm ▸ (ht a ha).2)⟩
      · exact Or.inl ha
    apply hx
    change (n.negOnePow : ℤ) * integerLength (pageTerm F D 2 (a,n)) = 0
    rw [integerLength_of_isZero (hz a n h'), mul_zero]
  unfold pageEuler
  rw [finsum_eq_sum_of_support_subset _ hs, Finset.sum_product]
  apply Finset.sum_eq_zero
  intro a ha
  change (∑ n ∈ t, (n.negOnePow : ℤ) * integerLength (pageTerm F D 2 (a,n))) = 0
  have hsub : ({a,a-1} : Finset ℤ) ⊆ t := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ht a ha
  rw [← Finset.sum_subset hsub (fun n _ hn => by
    have h' : n ≠ a ∧ n ≠ a-1 := by simpa using hn
    rw [integerLength_of_isZero (hz a n (.inr h')), mul_zero])]
  rw [Finset.sum_pair (by omega : a ≠ a-1), he a ha]
  have hsign : (a.negOnePow : ℤ) = -((a-1).negOnePow : ℤ) := by
    have h := Int.negOnePow_succ (a-1)
    rw [sub_add_cancel] at h
    simp [h]
  rw [hsign, neg_mul, neg_add_cancel]

private theorem reduce_flat (h : S) (N : ModuleCat.{w} (QuotientRing h))
    (Q : LeftResolution S (restrict h N)) (hQ : Q.IsFree) (i : ℕ) :
    Module.Flat (QuotientRing h) ((reduceComplex h Q.complex).X i) := by
  have := hQ i
  change Module.Flat (QuotientRing h) ((QuotientRing h) ⊗[S] Q.complex.X i)
  infer_instance

private theorem cutoffEuler_at_resolution_zero [IsNoetherianRing S] [IsLocalRing S]
    (h : S) (hm : h ∈ IsLocalRing.maximalIdeal S) (hh : h ∈ S⁰)
    (M : ModuleCat.{v} (QuotientRing h)) (N : ModuleCat.{w} (QuotientRing h))
    [Module.Finite (QuotientRing h) M] [Module.Finite (QuotientRing h) N]
    (hMN : IsFiniteLength (QuotientRing h) (M ⊗[QuotientRing h] N))
    (P : LeftResolution (QuotientRing h) M) (Q : LeftResolution S (restrict h N))
    (p q : ℕ) (hP : IsBoundedFiniteFree P p) (hQ : IsBoundedFiniteFree Q q) :
    cutoffEuler (restrict h M) (restrict h N) q = 0 := by
  let A := QuotientRing h
  let I : Ideal S := Ideal.span ({h} : Set S)
  have hI : I ≠ ⊤ := by
    have hle : I ≤ IsLocalRing.maximalIdeal S := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hm)
    exact ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal S).ne_top hle
  have : Nontrivial A := Ideal.Quotient.nontrivial_iff.mpr hI
  have : IsLocalRing A := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have : IsNoetherianRing A := inferInstanceAs (IsNoetherianRing (S ⧸ I))
  let C := reduceComplex h Q.complex
  let K := tensorBicomplex A (regrade P.complex) (regrade C)
  have hK : FiniteDiagonals K := tensorBicomplex_finite P.complex C
  let : K.HasTotal (ComplexShape.up ℤ) := (totalizationsExist K hK).1
  obtain ⟨F, _, hF, _, _, _⟩ := filtrations K hK
  let D := FilteredPage.pageData F
  have hConv := DoubleComplexConvergence.converges_of_finite F
    (DoubleComplexConvergence.formula_finite K hK Prod.fst (.inl rfl) F hF)
  let b := max (p+1) q
  let s := regradedDegrees p
  let t := regradedDegrees b
  have ht (a : ℤ) (ha : a ∈ s) : a ∈ t ∧ a-1 ∈ t := by
    have ha' := (mem_regradedDegrees p a).mp ha
    have hb : p+1 ≤ b := le_max_left ..
    exact ⟨(mem_regradedDegrees b a).mpr (by omega), (mem_regradedDegrees b (a-1)).mpr (by omega)⟩
  have hzero (a n : ℤ) (hz : a ∉ s ∨ (n ≠ a ∧ n ≠ a-1)) :
      IsZero (pageTerm F D 2 (a,n)) := by
    apply IsZero.of_iso _ (columnSecondAt K F hF D a n)
    apply secondPageVanishing h hh M N P Q p hP hQ.1
    rcases hz with hz | hz
    · exact Or.inl hz
    · exact Or.inr ⟨by omega, by omega⟩
  have hE0 (x : ℤ × ℤ) (hx : x ∉ (↑(s ×ˢ t) : Set (ℤ × ℤ))) :
      IsZero (pageTerm F D 2 x) := by
    obtain ⟨a,n⟩ := x
    apply hzero
    by_cases ha : a ∈ s
    · right
      have hn : n ∉ t := fun hn => hx (Finset.mem_product.mpr ⟨ha, hn⟩)
      exact ⟨fun eq => hn (eq.symm ▸ (ht a ha).1), fun eq => hn (eq.symm ▸ (ht a ha).2)⟩
    · exact Or.inl ha
  have hrow (i : ℕ) (j : Fin 2) :
      pageTerm F D 2 (-(i : ℤ), -(i : ℤ) - (j.val : ℤ)) ≅
        ModuleCat.of A (Tor M N i) := by
    refine columnSecondAt K F hF D _ _ ≪≫ ?_
    have he : -(i : ℤ) - (j.val : ℤ) - -(i : ℤ) = -(j.val : ℤ) := by omega
    exact eqToIso (congrArg (fun k => (verticalHomology K k).homology (-(i : ℤ))) he) ≪≫
      secondPageRow h hh M N P Q hP.1 hQ.1 i j
  have hrow₀ (i : ℕ) :
      pageTerm F D 2 (-(i : ℤ), -(i : ℤ)) ≅ ModuleCat.of A (Tor M N i) := by
    simpa only [Fin.val_zero, Nat.cast_zero, sub_zero] using hrow i (0 : Fin 2)
  have hrow₁ (i : ℕ) :
      pageTerm F D 2 (-(i : ℤ), -(i : ℤ) - 1) ≅ ModuleCat.of A (Tor M N i) :=
    hrow i (1 : Fin 2)
  have hE (x : ℤ × ℤ) : IsFiniteLength A (pageTerm F D 2 x) := by
    obtain ⟨a,n⟩ := x
    by_cases ha : a ∈ s
    · obtain ⟨i, _, hi⟩ := Finset.mem_map.mp ha
      change -(i : ℤ) = a at hi
      subst a
      by_cases hn : n = -(i : ℤ) ∨ n = -(i : ℤ) - 1
      · have hfin := tor_finite_length_of_tensor M N hMN i
        rcases hn with rfl | rfl
        · exact (hrow₀ i).toLinearEquiv.symm.isFiniteLength hfin
        · exact (hrow₁ i).toLinearEquiv.symm.isFiniteLength hfin
      · have hZ := hzero (-(i : ℤ)) n (.inr (not_or.mp hn))
        have := ModuleCat.isZero_iff_subsingleton.mp hZ
        exact .of_subsingleton
    · have hZ := hzero a n (.inl ha)
      have := ModuleCat.isZero_iff_subsingleton.mp hZ
      exact .of_subsingleton
  have hEzero : pageEuler F D 2 = 0 := by
    apply twoRowPageEulerZero F D s t ht hzero
    intro a ha
    obtain ⟨i, _, hi⟩ := Finset.mem_map.mp ha
    change -(i : ℤ) = a at hi
    subst a
    exact (integerLength_iso (hrow₀ i)).trans (integerLength_iso (hrow₁ i)).symm
  have hH (n : ℤ) : IsFiniteLength A ((sumTotal K).homology n) := by
    by_cases hn : n ≤ 0
    · let i := (-n).toNat
      have hi : n = -(i : ℤ) := by dsimp [i]; omega
      rw [hi]
      apply Module.length_ne_top_iff.mp
      rw [totalHomologyLength h M N P Q hQ.1 i]
      exact Module.length_ne_top_iff.mpr (tor_finite_length h M N hMN i)
    · let L := ((tensorLeft A (augmentationTarget M)).mapHomologicalComplex (ComplexShape.down ℕ)).obj C
      let e := abutmentIso M P C (reduce_flat h N Q hQ.1) n
      have hZ : IsZero ((regrade L).homology n) :=
        (HomologicalComplex.ExactAt.of_isZero (regrade_zero L n (by omega))).isZero_homology
      have := ModuleCat.isZero_iff_subsingleton.mp (IsZero.of_iso hZ e)
      exact .of_subsingleton
  have hlimit := (pageEuler_limit F D s t hE hE0 hConv hH).symm.trans hEzero
  have hbq : q ≤ b := le_max_right ..
  rw [← cutoffEuler_eq_of_vanishes_above (restrict h M) (restrict h N) q b hbq
    (tor_vanishes_above h M N Q q hQ)]
  rw [Finset.sum_map] at hlimit
  unfold cutoffEuler CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler.Specs.cutoffEuler
  refine (Finset.sum_congr rfl (fun i _ => ?_)).trans hlimit
  change (-1 : ℤ)^i * ((Module.length S (Tor (restrict h M) (restrict h N) i)).toNat : ℤ) =
    ((-(i : ℤ)).negOnePow : ℤ) * integerLength ((sumTotal K).homology (-(i : ℤ)))
  rw [Int.negOnePow_neg, Int.coe_negOnePow_natCast, integerLength, totalHomologyLength h M N P Q hQ.1 i]

/-- Every cutoff above the nonzero ambient Tor groups gives Euler sum zero. -/
theorem cutoff_euler_zero : Specs.cutoffEulerZero.{u,v,w} := by
  intro S _ _ _ h hm hh M N _ _ hMN P Q p q hP hQ d hd
  change cutoffEuler (restrict h M) (restrict h N) d = 0
  rw [cutoff_euler_eq_resolution_bound h M N Q q d hQ hd]
  exact cutoffEuler_at_resolution_zero h hm hh M N hMN P Q p q hP hQ

/-- The same cancellation holds for the regular local intersection Euler characteristic. -/
theorem intersection_euler_zero : Specs.intersectionEulerZero.{u,v,w} := by
  intro S _ _ h hm hh M N _ _ hMN P Q p q hP hQ
  change cutoffEuler (restrict h M) (restrict h N) (regularLocalDimension S) = 0
  apply cutoff_euler_zero h hm hh M N hMN P Q p q hP hQ
  exact CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler.tor_vanishes_above
    (restrict h M) (restrict h N) (regularLocalDimension S)
    (ringKrullDim_eq_regularLocalDimension S)

end ChangeOfRings

end CommutativeAlgebraNotes.Intersection.RegularElementEulerCancellation
