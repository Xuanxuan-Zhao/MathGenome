import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.TwoColumnKunneth
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.KunnethSpectralSequence
import MathGenome.Internal.AlgebraCore.P103.Ch11.UniversalCoefficientsHomology
import Batteries.Tactic.OpenPrivate

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v w
namespace AdvancedHomologicalAlgebra.TwoColumnKunneth
open KunnethSpectralSequence
open P103.BalancedTensor
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch02.FlatnessTests
variable {R : Type u} [Ring R]

/-- Both sequences use their actual inclusions, differential and quotient. -/
theorem basic_exact_sequences : Specs.BasicExactSequences.{u,v} := by
  intro R _ P n
  have hn : (ComplexShape.down ℤ).next n = n-1 :=
    (ComplexShape.down ℤ).next_eq' (by simp only [ComplexShape.down_Rel]; omega)
  have hp : (ComplexShape.down ℤ).prev (n-1) = n :=
    (ComplexShape.down ℤ).prev_eq' (by simp only [ComplexShape.down_Rel]; omega)
  constructor
  · refine ⟨Subtype.val_injective, ?_, ?_⟩
    · intro x
      constructor
      · intro hx
        exact ⟨⟨x, by
          change (P.d n ((ComplexShape.down ℤ).next n)).hom x = 0
          have hh : (P.d n (n-1)).hom x = 0 := congrArg Subtype.val hx
          rw [hn]
          exact hh⟩, rfl⟩
      · rintro ⟨z,rfl⟩
        apply Subtype.ext
        change (P.d n (n-1)).hom z.val = 0
        have hz : (P.d n ((ComplexShape.down ℤ).next n)).hom z.val = 0 := z.property
        rw [hn] at hz
        exact hz
    · intro b
      have hb := b.property
      change ∃ x, (P.d ((ComplexShape.down ℤ).prev (n-1)) (n-1)).hom x = b.val at hb
      rw [hp] at hb
      obtain ⟨x,hx⟩ := hb
      refine ⟨x, Subtype.ext ?_⟩
      exact hx
  · refine ⟨fun a b h => Subtype.ext (congrArg (fun z : cycles P n => z.val) h), ?_,
      (cycleBoundaries P n).mkQ_surjective⟩
    intro z
    rw [P103.Ch10.HomologySequence.class_zero_iff]
    exact ⟨fun hz => ⟨⟨z.val,hz⟩, Subtype.ext rfl⟩,
      by rintro ⟨b,rfl⟩; exact b.property⟩

/-- The first cycle/boundary sequence has flat middle and quotient terms. -/
theorem cycles_flat (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (hP : FlatTerms.{u,v,w} P) (hB : ∀ q, RightFlat.{u,v,w} R (boundaries P q))
    (n : ℤ) : RightFlat.{u,v,w} R (cycles P n) := by
  have hs := (basic_exact_sequences R P n).1
  exact P103.Ch11.UniversalCoefficientsHomology.rightFlat_of_shortExact
    (ModuleCat.of Rᵐᵒᵖ (cycles P n)) (P.X n)
    (ModuleCat.of Rᵐᵒᵖ (boundaries P (n-1)))
    (ModuleCat.ofHom (cycles P n).subtype) (ModuleCat.ofHom (boundaryProjection P n))
    hs.1 hs.2.1 hs.2.2 (hP n) (hB (n-1))

/-- A short exact flat presentation yields the original quotient homology. -/
def quotientFlatPresentation (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (n : ℤ) (hZ : RightFlat.{u,v,w} R (cycles P n))
    (hB : RightFlat.{u,v,w} R (boundaries P n))
    (hs : Function.Injective (boundaryToCycles P n) ∧
      Function.Exact (boundaryToCycles P n) (homologyClass P n) ∧
      Function.Surjective (homologyClass P n)) :
    FlatPresentation.{u,v,w} (R := R) (Homology P n) := by
  let eB : ULift.{u} (boundaries P n) ≃ₗ[Rᵐᵒᵖ] boundaries P n := ULift.moduleEquiv
  let eZ : ULift.{u} (cycles P n) ≃ₗ[Rᵐᵒᵖ] cycles P n := ULift.moduleEquiv
  refine {
    F₁ := ModuleCat.of Rᵐᵒᵖ (ULift.{u} (boundaries P n))
    F₀ := ModuleCat.of Rᵐᵒᵖ (ULift.{u} (cycles P n))
    i := eZ.symm.toLinearMap.comp ((boundaryToCycles P n).comp eB.toLinearMap)
    ε := (homologyClass P n).comp eZ.toLinearMap
    injective := eZ.symm.injective.comp (hs.1.comp eB.injective)
    exact := ?_
    surjective := hs.2.2.comp eZ.surjective
    flat₁ := P103.Ch11.FlatResolutions.rightFlat_of_linearEquiv eB hB
    flat₀ := P103.Ch11.FlatResolutions.rightFlat_of_linearEquiv eZ hZ }
  intro z
  change homologyClass P n (eZ z) = 0 ↔ _
  rw [hs.2.1]
  constructor
  · rintro ⟨b,hb⟩
    exact ⟨eB.symm b, by change eZ.symm (boundaryToCycles P n (eB (eB.symm b))) = z
                         rw [eB.apply_symm_apply,hb,eZ.symm_apply_apply]⟩
  · rintro ⟨b,hb⟩
    refine ⟨eB b, ?_⟩
    have hh := congrArg eZ hb
    simpa using hh

/-- Enlarging the augmentation codomain does not alter its resolution complex. -/
def liftedRightResolution {A : ModuleCat.{v} Rᵐᵒᵖ}
    (N : LeftResolution Rᵐᵒᵖ A) : LeftResolution Rᵐᵒᵖ (ULift.{u} A) where
  complex := N.complex
  ε := (ULift.moduleEquiv.symm : A ≃ₗ[Rᵐᵒᵖ] ULift.{u} A).toLinearMap.comp N.ε
  surjective := ULift.moduleEquiv.symm.surjective.comp N.surjective
  exact_zero := by
    rw [N.exact_zero]
    ext x
    change N.ε x = 0 ↔ ULift.up (N.ε x) = (0 : ULift.{u} A)
    exact ⟨fun h => congrArg ULift.up h, fun h => congrArg ULift.down h⟩
  exact_succ := N.exact_succ

/-- Dimension shifting uses a presentation, not a vanishing assumption. -/
theorem higher_tor_vanishes : Specs.HigherTorVanishes.{u,v,w} := by
  intro R _ T A hA M p hp
  obtain ⟨F⟩ := hA
  let A' := ModuleCat.of Rᵐᵒᵖ (ULift.{u} A)
  let ε' : F.F₀ →ₗ[Rᵐᵒᵖ] A' :=
    (ULift.moduleEquiv.symm : A ≃ₗ[Rᵐᵒᵖ] ULift.{u} A).toLinearMap.comp F.ε
  have he : Function.Exact F.i ε' := by
    intro x
    change ULift.up (F.ε x) = (0 : ULift.{u} A) ↔ _
    rw [show ULift.up (F.ε x) = (0 : ULift.{u} A) ↔ F.ε x = 0 from
      ⟨fun h => congrArg ULift.down h, fun h => congrArg ULift.up h⟩]
    exact F.exact x
  have hs : Function.Surjective ε' := ULift.moduleEquiv.symm.surjective.comp F.surjective
  let N := liftedRightResolution (T.rightResolutions A).val
  have hN : N.IsProjective := (T.rightResolutions A).property
  obtain ⟨K,hK⟩ := P103.Ch10.ProjectiveResolutions.exists_projective_resolution Rᵐᵒᵖ F.F₁
  obtain ⟨hH,hseq⟩ := P103.Ch11.DimensionShifting.tor_first R F.F₁ F.F₀ A'
    (ModuleCat.ofHom F.i) (ModuleCat.ofHom ε') F.injective he hs F.flat₀ M K N hK hN
  obtain ⟨H⟩ := hH
  obtain ⟨δ,hδ,heq,hedge⟩ := hseq H
  obtain ⟨k,rfl⟩ : ∃ k : ℕ, p = k+1+1 := ⟨p-2,by omega⟩
  obtain ⟨e,he⟩ := heq k
  letI := P103.Ch11.VanishingAndFlatness.tor_right_flat R F.F₁ M F.flat₁ K hK k
  exact e.injective.subsingleton

/-- Transport the augmentation along a genuine module isomorphism. -/
def FlatPresentation.ofEquiv {A B : Type v} [AddCommGroup A] [AddCommGroup B]
    [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ B]
    (F : FlatPresentation.{u,v,w} (R := R) A) (e : A ≃ₗ[Rᵐᵒᵖ] B) :
    FlatPresentation.{u,v,w} (R := R) B where
  F₁ := F.F₁
  F₀ := F.F₀
  i := F.i
  ε := e.toLinearMap.comp F.ε
  injective := F.injective
  exact := by
    intro x
    change e (F.ε x) = 0 ↔ _
    rw [← e.map_zero, e.injective.eq_iff]
    exact F.exact x
  surjective := e.surjective.comp F.surjective
  flat₁ := F.flat₁
  flat₀ := F.flat₀

/-- The flat-boundary sufficient case supplies the actual flat resolution. -/
theorem flat_boundaries_suffice : Specs.FlatBoundariesSuffice.{u,v,w} := by
  intro R _ P hP hB
  refine ⟨cycles_flat P hP hB, fun n => ?_⟩
  let F := quotientFlatPresentation P n (cycles_flat P hP hB n) (hB n)
    (basic_exact_sequences R P n).2
  exact ⟨F.ofEquiv (categoricalHomologyIso P n).toLinearEquiv.symm⟩

/-- Vanishing of a term propagates to the next page. -/
theorem next_term_isZero
    {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {Q : ChainComplex (ModuleCat.{w} R) ℤ} (S : TensorPages P Q)
    (r : ℤ) (hr : 0 ≤ r) (p q : ℤ) (h : IsZero (S.term r p q)) :
    IsZero (S.term (r+1) p q) := by
  have hm : IsZero (S.pageComplex r hr p q).X₂ := by
    change IsZero (PageCohomology.object S.filtration S.pages r (-p-r+r) (-(p+q)-1+1))
    convert h using 1
    unfold TensorPages.term PageCohomology.object
    congr 1 <;> omega
  exact IsZero.of_iso ((S.pageComplex r hr p q).isZero_homology_of_isZero_X₂ hm)
    (S.nextPageIso r hr p q)

theorem second_page_two_columns
    (T : CanonicalTheory.{u,v,w} R) (X : Input.{u,v,w} R)
    (hX : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q))
    (D : Realization T X.P X.M X.Q X.L) (p q : ℤ) (hp : p < 0 ∨ 1 < p) :
    IsZero (D.tensorPages.term 2 p q) := by
  rcases hp with hp | hp
  · exact D.support 2 p q (Or.inl hp)
  · have hp0 : 0 ≤ p := by omega
    have hz := higher_tor_vanishes R T (X.P.homology q) (hX q) X.M p.toNat (by omega)
    letI := hz
    have ht := ModuleCat.isZero_of_subsingleton (ModuleCat.of ℤ (T.Tor (X.P.homology q) X.M p.toNat))
    have he := D.secondIso p.toNat q
    have hcast : (p.toNat : ℤ) = p := Int.toNat_of_nonneg hp0
    rw [hcast] at he
    exact IsZero.of_iso ht he


private theorem later_pages_isZero
    {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {Q : ChainComplex (ModuleCat.{w} R) ℤ} (S : TensorPages P Q)
    (r : ℤ) (hr : 2 ≤ r) (p q : ℤ) (h : IsZero (S.term 2 p q)) :
    IsZero (S.term r p q) := by
  obtain ⟨k, rfl⟩ := Int.exists_add_of_le hr
  clear hr
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [Int.natCast_succ, ← add_assoc]
    exact next_term_isZero S (2 + k) (by omega) p q ih

theorem later_pages_two_columns
    (T : CanonicalTheory.{u,v,w} R) (X : Input.{u,v,w} R)
    (hX : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q))
    (D : Realization T X.P X.M X.Q X.L) (r : ℤ) (hr : 2 ≤ r)
    (p q : ℤ) (hp : p < 0 ∨ 1 < p) : IsZero (D.tensorPages.term r p q) :=
  later_pages_isZero D.tensorPages r hr p q (second_page_two_columns T X hX D p q hp)

theorem later_differentials_zero
    (T : CanonicalTheory.{u,v,w} R) (X : Input.{u,v,w} R)
    (hX : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q))
    (D : Realization T X.P X.M X.Q X.L) (r : ℤ) (hr : 2 ≤ r)
    (p q : ℤ) : D.tensorPages.differential r (by omega) p q = 0 := by
  by_cases hp : p < 0 ∨ 1 < p
  · exact (later_pages_two_columns T X hX D r hr p q hp).eq_of_src _ _
  · exact (later_pages_two_columns T X hX D r hr (p-r) (q+r-1)
      (Or.inl (by omega))).eq_of_tgt _ _

/-- Actual page support and actual differential vanishing, starting at E₂. -/
theorem two_column_pages : Specs.TwoColumnPages.{u,v,w} := by
  intro R _ T X hX D
  exact ⟨later_pages_two_columns T X hX D, later_differentials_zero T X hX D⟩


/-! Canonical degree-zero Tor and the actual two-step filtration. -/

def canonicalTorZero (T : CanonicalTheory.{u,v,w} R)
    (A : ModuleCat.{v} Rᵐᵒᵖ) (M : ModuleCat.{w} R) :
    T.Tor A M 0 ≃ₗ[ℤ] P103.BalancedTensor.Tensor R A M :=
  (P103.Ch11.ExtTorDefinitions.torZero (T.rightResolutions A).val M).toIntLinearEquiv

theorem canonicalTorZero_class (T : CanonicalTheory.{u,v,w} R)
    (A : ModuleCat.{v} Rᵐᵒᵖ) (M : ModuleCat.{w} R)
    (z : cycles (tensorComplex (T.rightResolutions A).val.complex M) 0) :
    canonicalTorZero T A M (homologyClass _ 0 z) =
      tensorMap (T.rightResolutions A).val.ε LinearMap.id z.val :=
  P103.Ch11.ExtTorDefinitions.torZero_class _ _ _

theorem canonicalTorZero_natural (T : CanonicalTheory.{u,v,w} R)
    {A B : ModuleCat.{v} Rᵐᵒᵖ} {M N : ModuleCat.{w} R}
    (f : A ⟶ B) (g : M ⟶ N) (x : T.Tor A M 0) :
    canonicalTorZero T B N (T.torMap 0 f g x) =
      tensorMap f.hom g.hom (canonicalTorZero T A M x) := by
  let P := T.rightResolutions A
  let Q := T.rightResolutions B
  let l := P103.Ch10.Comparison.chainMap P.val Q.val P.property f.hom
  have hl := P103.Ch10.Comparison.chainMap_lifts P.val Q.val P.property f.hom
  change canonicalTorZero T B N ((T.torMaps 0).map P Q f g x) = _
  rw [(T.torMaps 0).formula P Q f g l hl]
  exact P103.Ch11.ExtTorDefinitions.tor_zero_natural R A B P.val Q.val M N f.hom g.hom l hl
    (P103.Ch11.ExtTorDefinitions.torZero P.val M)
    (P103.Ch11.ExtTorDefinitions.torZero Q.val N)
    (P103.Ch11.ExtTorDefinitions.torZero_class P.val M)
    (P103.Ch11.ExtTorDefinitions.torZero_class Q.val N) x

theorem canonicalTorZero_natural_map (T : CanonicalTheory.{u,v,w} R)
    {A B : ModuleCat.{v} Rᵐᵒᵖ} {M N : ModuleCat.{w} R}
    (f : A ⟶ B) (g : M ⟶ N) :
    (canonicalTorZero T B N).toLinearMap.comp (T.torMap 0 f g) =
      (tensorMap f.hom g.hom).comp (canonicalTorZero T A M).toLinearMap := by
  apply LinearMap.ext
  intro x
  exact canonicalTorZero_natural T f g x


theorem canonicalTorZero_symm_natural (T : CanonicalTheory.{u,v,w} R)
    {A B : ModuleCat.{v} Rᵐᵒᵖ} {M N : ModuleCat.{w} R}
    (f : A ⟶ B) (g : M ⟶ N) (x : P103.BalancedTensor.Tensor R A M) :
    T.torMap 0 f g ((canonicalTorZero T A M).symm x) =
      (canonicalTorZero T B N).symm (tensorMap f.hom g.hom x) := by
  apply (canonicalTorZero T B N).injective
  rw [canonicalTorZero_natural]
  simp only [LinearEquiv.apply_symm_apply]

theorem canonicalTorZero_symm_natural_map (T : CanonicalTheory.{u,v,w} R)
    {A B : ModuleCat.{v} Rᵐᵒᵖ} {M N : ModuleCat.{w} R}
    (f : A ⟶ B) (g : M ⟶ N) :
    (T.torMap 0 f g).comp (canonicalTorZero T A M).symm.toLinearMap =
      (canonicalTorZero T B N).symm.toLinearMap.comp (tensorMap f.hom g.hom) := by
  apply LinearMap.ext
  intro x
  exact canonicalTorZero_symm_natural T f g x


section General
variable {A : Type u} [Category.{v} A] [Abelian A] {H : A}

theorem subobjects_eq_of_zero_quotient (S T : Subobject H) (h : S ≤ T)
    (hz : IsZero (cokernel (Subobject.ofLE S T h))) : S = T := by
  letI : Epi (Subobject.ofLE S T h) := Preadditive.epi_of_isZero_cokernel _ hz
  letI : IsIso (Subobject.ofLE S T h) := isIso_of_mono_of_epi _
  exact Subobject.eq_of_comm (asIso (Subobject.ofLE S T h)) (Subobject.ofLE_arrow h)

private theorem filtration_endpoints_of_step_eq {S : Type*} [PartialOrder S] [OrderBot S]
    [OrderTop S] (P : ℤ → S)
    (hfinite : ∃ a b : ℤ, (∀ p, p ≤ a → P p = ⊥) ∧ (∀ p, b ≤ p → P p = ⊤))
    (heq : ∀ p, p < 0 ∨ 1 < p → P (p-1) = P p) :
    P (-1) = ⊥ ∧ P 1 = ⊤ := by
  obtain ⟨a,b,ha,hb⟩ := hfinite
  constructor
  · have hs : ∀ k : ℕ, min a (-1) + (k : ℤ) ≤ -1 → P (min a (-1) + k) = ⊥ := by
      intro k
      induction k with
      | zero => intro _; simpa using ha (min a (-1)) (min_le_left _ _)
      | succ k ih =>
        rw [Int.natCast_succ, ← add_assoc]
        intro hk
        rw [← heq (min a (-1) + (k : ℤ) + 1) (Or.inl (by omega)), add_sub_cancel_right]
        exact ih (by omega)
    have ht := hs ((-1 - min a (-1)).toNat) (by omega)
    rwa [show min a (-1) + (↑((-1 - min a (-1)).toNat) : ℤ) = -1 by omega] at ht
  · have hs : ∀ k : ℕ, 1 ≤ max b 1 - (k : ℤ) → P (max b 1 - k) = ⊤ := by
      intro k
      induction k with
      | zero => intro _; simpa using hb (max b 1) (le_max_left _ _)
      | succ k ih =>
        rw [Int.natCast_succ, ← sub_sub]
        intro hk
        rw [heq (max b 1 - (k : ℤ)) (Or.inr (by omega))]
        exact ih (by omega)
    have ht := hs ((max b 1 - 1).toNat) (by omega)
    rwa [show max b 1 - (↑((max b 1 - 1).toNat) : ℤ) = 1 by omega] at ht

theorem finite_filtration_two_steps (P : ℤ → Subobject H)
    (hincr : ∀ p, P (p-1) ≤ P p)
    (hfinite : ∃ a b : ℤ, (∀ p, p ≤ a → P p = ⊥) ∧ (∀ p, b ≤ p → P p = ⊤))
    (hzero : ∀ p, p < 0 ∨ 1 < p → IsZero (cokernel (Subobject.ofLE _ _ (hincr p)))) :
    P (-1) = ⊥ ∧ P 1 = ⊤ :=
  filtration_endpoints_of_step_eq P hfinite (fun p hp =>
    subobjects_eq_of_zero_quotient _ _ (hincr p) (hzero p hp))
end General

open KunnethSpectralSequence
open P103.Specs.Ch11.ExtTorDefinitions

theorem target_graded_isZero
    (T : CanonicalTheory.{u,v,w} R) (X : Input.{u,v,w} R)
    (hX : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q))
    (D : Realization T X.P X.M X.Q X.L) (p n : ℤ) (hp : p < 0 ∨ 1 < p) :
    IsZero (D.targetGraded p n) := by
  obtain ⟨r₀,hr₀,hstable⟩ := (kunneth_convergence D).2.2 n
  let r := max r₀ 2
  obtain ⟨e⟩ := hstable r (le_max_left _ _) p
  exact IsZero.of_iso
    (later_pages_two_columns T X hX D r (le_max_right _ _) p (n-p) hp) e.symm

theorem target_filtration_endpoints
    (T : CanonicalTheory.{u,v,w} R) (X : Input.{u,v,w} R)
    (hX : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q))
    (D : Realization T X.P X.M X.Q X.L) (n : ℤ) :
    D.targetPiece (-1) n = ⊥ ∧ D.targetPiece 1 n = ⊤ := by
  apply finite_filtration_two_steps (fun p => D.targetPiece p n)
    (fun p => transportedPiece_increasing _ _ _ _ p) ((kunneth_convergence D).2.1 n)
  exact fun p hp => target_graded_isZero T X hX D p n hp

open KunnethSpectralSequence
open P103.Specs.Ch11.ExtTorDefinitions

theorem cochain_page_isZero
    (T : CanonicalTheory.{u,v,w} R) (X : Input.{u,v,w} R)
    (hX : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q))
    (D : Realization T X.P X.M X.Q X.L) (r : ℤ) (hr : 2 ≤ r)
    (p n : ℤ) (hp : p < -1 ∨ 0 < p) :
    IsZero (PageCohomology.object D.tensorPages.filtration D.tensorPages.pages r p n) := by
  have hz := later_pages_two_columns T X hX D r hr (-p) (p-n) (by omega)
  convert hz using 1
  unfold TensorPages.term PageCohomology.object
  congr 1 <;> omega

theorem cochain_differentials_zero
    (T : CanonicalTheory.{u,v,w} R) (X : Input.{u,v,w} R)
    (hX : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q))
    (D : Realization T X.P X.M X.Q X.L) (r : ℤ) (hr : 2 ≤ r)
    (p n : ℤ) : D.tensorPages.pages.differential r (by omega) p n = 0 := by
  by_cases hp : p < -1 ∨ 0 < p
  · exact (cochain_page_isZero T X hX D r hr p n hp).eq_of_src _ _
  · exact (cochain_page_isZero T X hX D r hr (p+r) (n+1)
      (Or.inr (by omega))).eq_of_tgt _ _


universe x

theorem rightFlat_changeUniverse {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (h : RightFlat.{u,v,w} R A) : RightFlat.{u,v,x} R A :=
  (P103.Ch02.FlatnessTests.rightFlat_iff_opposite R A).mpr
    (P103.Ch11.VanishingAndFlatness.flat_change_universe
      ((P103.Ch02.FlatnessTests.rightFlat_iff_opposite R A).mp h))

def FlatPresentation.changeCoefficientUniverse
    {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (F : FlatPresentation.{u,v,w} (R := R) A) :
    FlatPresentation.{u,v,x} (R := R) A where
  F₁ := F.F₁
  F₀ := F.F₀
  i := F.i
  ε := F.ε
  injective := F.injective
  exact := F.exact
  surjective := F.surjective
  flat₁ := rightFlat_changeUniverse F.flat₁
  flat₀ := rightFlat_changeUniverse F.flat₀

/-- The kernel of a flat module's surjection onto a module of flat dimension at most one is flat. -/
theorem rightFlat_kernel_of_flatDimensionOne
    (B Z H : ModuleCat.{v} Rᵐᵒᵖ) (i : B ⟶ Z) (p : Z ⟶ H)
    (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom)
    (hp : Function.Surjective p.hom) (hZ : RightFlat.{u,v,w} R Z)
    (hH : HasFlatDimensionOne.{u,v,w} (R := R) H) :
    RightFlat.{u,v,w} R B := by
  apply (P103.Ch11.VanishingAndFlatness.right_flat_iff_tor_one R B).mpr
  intro M _ _ L hL
  let T : CanonicalTheory.{u,v,max u v w} R := P103.Ch11.ExtTorDefinitions.theory R
  let N := (T.rightResolutions H).val
  have hN : N.IsProjective := (T.rightResolutions H).property
  have hH' : HasFlatDimensionOne.{u,v,max u v w} (R := R) H := by
    obtain ⟨F⟩ := hH
    exact ⟨F.changeCoefficientUniverse⟩
  letI : Subsingleton (TorWith N M 2) :=
    higher_tor_vanishes R T H hH' (ModuleCat.of R M) 2 (by decide)
  obtain ⟨hdata, hshift⟩ := P103.Ch11.DimensionShifting.tor_first
    R B Z H i p hi he hp (rightFlat_changeUniverse hZ)
    (ModuleCat.of R M) L N hL hN
  obtain ⟨data⟩ := hdata
  obtain ⟨δ, hδ, hsh, hedge⟩ := hshift data
  obtain ⟨e, he⟩ := hsh 0
  exact e.symm.injective.subsingleton


section FlatPresentation

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe a b

private theorem exact_transport {S : Type*} [Semiring S]
    {A B C A' B' C' : Type*}
    [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]
    [AddCommMonoid A'] [AddCommMonoid B'] [AddCommMonoid C']
    [Module S A] [Module S B] [Module S C]
    [Module S A'] [Module S B'] [Module S C']
    (eA : A ≃ₗ[S] A') (eB : B ≃ₗ[S] B') (eC : C ≃ₗ[S] C')
    (i : A →ₗ[S] B) (p : B →ₗ[S] C) (h : Function.Exact i p) :
    Function.Exact ((eB.toLinearMap.comp i).comp eA.symm.toLinearMap)
      (eC.toLinearMap.comp (p.comp eB.symm.toLinearMap)) :=
  LinearEquiv.precomp_exact_iff_exact.mpr
    (LinearEquiv.postcomp_exact_iff_exact.mpr ((eB.conj_exact_iff_exact i p).mpr h))

/-- A flat presentation with arbitrary term levels can be replaced by the
free module on the original module and the kernel of its augmentation. -/
theorem hasFlatDimensionOne_of_flat_presentation
    {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {F₁ : Type a} [AddCommGroup F₁] [Module Rᵐᵒᵖ F₁]
    {F₀ : Type b} [AddCommGroup F₀] [Module Rᵐᵒᵖ F₀]
    (i : F₁ →ₗ[Rᵐᵒᵖ] F₀) (ε : F₀ →ₗ[Rᵐᵒᵖ] A)
    (hi : Function.Injective i) (he : Function.Exact i ε) (hs : Function.Surjective ε)
    (h₁ : RightFlat.{u,a,x} R F₁) (h₀ : RightFlat.{u,b,x} R F₀) :
    HasFlatDimensionOne.{u,v,w} (R := R) A := by
  let p := Finsupp.linearCombination Rᵐᵒᵖ (id : A → A)
  let K := LinearMap.ker p
  have hp : Function.Surjective p := Finsupp.linearCombination_surjective _ Function.surjective_id
  have hfree : RightFlat.{u,max u v,w} R (A →₀ Rᵐᵒᵖ) :=
    (P103.Ch02.FlatnessTests.right_tensor_characterizations R _).2.2.2.1 inferInstance

  -- Lift all carriers for the dimension-shifting calculation.
  let eA : A ≃ₗ[Rᵐᵒᵖ] ULift.{max u a b} A := ULift.moduleEquiv.symm
  let e₁ : F₁ ≃ₗ[Rᵐᵒᵖ] ULift.{max u v b} F₁ := ULift.moduleEquiv.symm
  let e₀ : F₀ ≃ₗ[Rᵐᵒᵖ] ULift.{max u v a} F₀ := ULift.moduleEquiv.symm
  let eF : (A →₀ Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] ULift.{max a b} (A →₀ Rᵐᵒᵖ) := ULift.moduleEquiv.symm
  let eK : K ≃ₗ[Rᵐᵒᵖ] ULift.{max a b} K := ULift.moduleEquiv.symm
  let H := ModuleCat.of Rᵐᵒᵖ (ULift.{max u a b} A)
  let F := ModuleCat.of Rᵐᵒᵖ (ULift.{max a b} (A →₀ Rᵐᵒᵖ))
  let B := ModuleCat.of Rᵐᵒᵖ (ULift.{max a b} K)
  let j := (eF.toLinearMap.comp K.subtype).comp eK.symm.toLinearMap
  let q := eA.toLinearMap.comp (p.comp eF.symm.toLinearMap)
  have hH : HasFlatDimensionOne.{u,max u v a b,w} (R := R) H :=
    ⟨{ F₁ := ModuleCat.of Rᵐᵒᵖ (ULift.{max u v b} F₁)
       F₀ := ModuleCat.of Rᵐᵒᵖ (ULift.{max u v a} F₀)
       i := (e₀.toLinearMap.comp i).comp e₁.symm.toLinearMap
       ε := eA.toLinearMap.comp (ε.comp e₀.symm.toLinearMap)
       injective := e₀.injective.comp (hi.comp e₁.symm.injective)
       exact := exact_transport e₁ e₀ eA i ε he
       surjective := eA.surjective.comp (hs.comp e₀.symm.surjective)
       flat₁ := P103.Ch11.FlatResolutions.rightFlat_of_linearEquiv e₁.symm (rightFlat_changeUniverse h₁)
       flat₀ := P103.Ch11.FlatResolutions.rightFlat_of_linearEquiv e₀.symm (rightFlat_changeUniverse h₀) }⟩
  have hj : Function.Injective j := eF.injective.comp (Subtype.val_injective.comp eK.symm.injective)
  have hq : Function.Exact j q := by
    dsimp only [j, q]
    exact exact_transport (A := ↥K) eK eF eA K.subtype p
      (show Function.Exact K.subtype p from p.exact_subtype_ker_map)
  have hsurj : Function.Surjective q := eA.surjective.comp (hp.comp eF.symm.surjective)
  have hF : RightFlat.{u,max u v a b,w} R F :=
    P103.Ch11.FlatResolutions.rightFlat_of_linearEquiv eF.symm hfree
  have hB : RightFlat.{u,max u v a b,w} R B :=
    rightFlat_kernel_of_flatDimensionOne.{u,max u v a b,w}
      B F H (ModuleCat.ofHom j) (ModuleCat.ofHom q) hj hq hsurj hF hH
  exact ⟨{ F₁ := ModuleCat.of Rᵐᵒᵖ K
           F₀ := ModuleCat.of Rᵐᵒᵖ (A →₀ Rᵐᵒᵖ)
           i := K.subtype
           ε := p
           injective := Subtype.val_injective
           exact := p.exact_subtype_ker_map
           surjective := hp
           flat₁ := P103.Ch11.FlatResolutions.rightFlat_of_linearEquiv eK hB
           flat₀ := hfree }⟩

end FlatPresentation

open KunnethSpectralSequence

/-- Below the source lower bound the actual boundary module is zero. -/
theorem boundaries_flat_below
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (L n : ℤ)
    (hP : BoundedBelow P L) (hn : n < L) : RightFlat.{u,v,w} R (boundaries P n) := by
  letI := ModuleCat.subsingleton_of_isZero (hP n hn)
  exact P103.Ch11.FlatResolutions.rightFlat_of_subsingleton _

/-- The length-one homology hypothesis passes flatness from one boundary
to the next, using the two actual cycle and boundary sequences. -/
theorem boundary_flat_step
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (n : ℤ)
    (hP : FlatTerms.{u,v,w} P)
    (hH : HasFlatDimensionOne.{u,v,w} (R := R) (P.homology n))
    (hB : RightFlat.{u,v,w} R (boundaries P (n-1))) :
    RightFlat.{u,v,w} R (boundaries P n) := by
  have hs := basic_exact_sequences R P n
  have hZ : RightFlat.{u,v,w} R (cycles P n) :=
    P103.Ch11.UniversalCoefficientsHomology.rightFlat_of_shortExact
      (ModuleCat.of Rᵐᵒᵖ (cycles P n)) (P.X n)
      (ModuleCat.of Rᵐᵒᵖ (boundaries P (n-1)))
      (ModuleCat.ofHom (cycles P n).subtype) (ModuleCat.ofHom (boundaryProjection P n))
      hs.1.1 hs.1.2.1 hs.1.2.2 (hP n) hB
  have hH' : HasFlatDimensionOne.{u,v,w} (R := R) (Homology P n) := by
    obtain ⟨F⟩ := hH
    exact ⟨F.ofEquiv (categoricalHomologyIso P n).toLinearEquiv⟩
  exact rightFlat_kernel_of_flatDimensionOne
    (ModuleCat.of Rᵐᵒᵖ (boundaries P n)) (ModuleCat.of Rᵐᵒᵖ (cycles P n))
    (ModuleCat.of Rᵐᵒᵖ (Homology P n))
    (ModuleCat.ofHom (boundaryToCycles P n)) (ModuleCat.ofHom (homologyClass P n))
    hs.2.1 hs.2.2.1 hs.2.2.2 hZ hH'

/-- For a bounded-below flat complex, flat dimension at most one of all
homology modules also forces all its boundary modules to be flat. -/
theorem flat_boundaries_of_flatDimensionOne
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (L : ℤ)
    (hbound : BoundedBelow P L) (hP : FlatTerms.{u,v,w} P)
    (hH : ∀ n, HasFlatDimensionOne.{u,v,w} (R := R) (P.homology n)) :
    ∀ n, RightFlat.{u,v,w} R (boundaries P n) := by
  have hi : ∀ k : ℕ, RightFlat.{u,v,w} R (boundaries P (L-1+k)) := by
    intro k
    induction k with
    | zero => exact boundaries_flat_below P L (L-1+0) hbound (by omega)
    | succ k ih =>
      apply boundary_flat_step P (L-1+(k+1:ℕ)) hP (hH _)
      have he : L-1+((k+1:ℕ):ℤ)-1 = L-1+(k:ℤ) := by omega
      rw [he]
      exact ih
  intro n
  by_cases hn : n < L
  · exact boundaries_flat_below P L n hbound hn
  · have h := hi ((n-(L-1)).toNat)
    have he : L-1+((n-(L-1)).toNat:ℤ) = n := by omega
    rw [he] at h
    exact h


section ConcreteCycleTensorMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

/-- Tensor of explicit cycles, with values in actual coefficient cycles. -/
def tensorExplicitCycles (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{w} R) (n : ℤ) :
    Tensor R (cycles P n) M →ₗ[ℤ] cycles (coefficientComplex P M) n :=
  (tensorMap (cycles P n).subtype (LinearMap.id : M →ₗ[R] M)).codRestrict _ (by
    intro t
    change (tensorMap (P.d n ((ComplexShape.down ℤ).next n)).hom LinearMap.id)
      (tensorMap (cycles P n).subtype LinearMap.id t) = 0
    have h : (tensorMap (P.d n ((ComplexShape.down ℤ).next n)).hom
        (LinearMap.id : M →ₗ[R] M)).comp
        (tensorMap (cycles P n).subtype LinearMap.id) = 0 := by
      apply tensor_hom_ext
      intro z m
      change tmul R ((P.d n ((ComplexShape.down ℤ).next n)).hom z.val) m = 0
      rw [show (P.d n ((ComplexShape.down ℤ).next n)).hom z.val = 0 from z.property]
      simp [tmul]
    exact LinearMap.congr_fun h t)

def explicitCycleClass (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{w} R) (n : ℤ) :=
  (homologyClass (coefficientComplex P M) n).comp (tensorExplicitCycles P M n)

lemma explicitCycleClass_boundary (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{w} R) (n : ℤ) :
    (explicitCycleClass P M n).comp
      (tensorMap (boundaryToCycles P n) (LinearMap.id : M →ₗ[R] M)) = 0 := by
  apply tensor_hom_ext
  intro b m
  obtain ⟨x,hx⟩ := b.property
  change homologyClass (coefficientComplex P M) n
    (tensorExplicitCycles P M n (tmul R (boundaryToCycles P n b) m)) = 0
  rw [P103.Ch10.HomologySequence.class_zero_iff]
  refine ⟨tmul R x m, ?_⟩
  change tmul R ((P.d ((ComplexShape.down ℤ).prev n) n).hom x) m = tmul R b.val m
  rw [hx]

lemma explicitHomologyTensor_surj (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{w} R) (n : ℤ) :
    Function.Surjective (tensorMap (homologyClass P n) (LinearMap.id : M →ₗ[R] M)) := by
  have he : Function.Exact (boundaryToCycles P n) (homologyClass P n) := by
    intro z
    rw [P103.Ch10.HomologySequence.class_zero_iff]
    exact ⟨fun hz => ⟨⟨z.val,hz⟩, Subtype.ext rfl⟩,
      by rintro ⟨b,rfl⟩; exact b.property⟩
  exact (P103.HomTensorExactness.tensor_first_rightExact
    (boundaryToCycles P n) (homologyClass P n) he (cycleBoundaries P n).mkQ_surjective
    (tensorMap (boundaryToCycles P n) (LinearMap.id : M →ₗ[R] M)).toAddMonoidHom
    (by intros; rfl)
    (tensorMap (homologyClass P n) (LinearMap.id : M →ₗ[R] M)).toAddMonoidHom
    (by intros; rfl)).2

lemma explicitHomologyTensor_ker_le (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{w} R) (n : ℤ) :
    LinearMap.ker (tensorMap (homologyClass P n) (LinearMap.id : M →ₗ[R] M)) ≤
      LinearMap.ker (explicitCycleClass P M n) := by
  have he : Function.Exact (boundaryToCycles P n) (homologyClass P n) := by
    intro z
    rw [P103.Ch10.HomologySequence.class_zero_iff]
    exact ⟨fun hz => ⟨⟨z.val,hz⟩, Subtype.ext rfl⟩,
      by rintro ⟨b,rfl⟩; exact b.property⟩
  have ht := (P103.HomTensorExactness.tensor_first_rightExact
    (boundaryToCycles P n) (homologyClass P n) he (cycleBoundaries P n).mkQ_surjective
    (tensorMap (boundaryToCycles P n) (LinearMap.id : M →ₗ[R] M)).toAddMonoidHom
    (by intros; rfl)
    (tensorMap (homologyClass P n) (LinearMap.id : M →ₗ[R] M)).toAddMonoidHom
    (by intros; rfl)).1
  intro t ht0
  obtain ⟨b,rfl⟩ := (ht t).mp ht0
  exact LinearMap.congr_fun (explicitCycleClass_boundary P M n) b

def explicitAlpha (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{w} R) (n : ℤ) :
    Tensor R (Homology P n) M →ₗ[ℤ] Homology (coefficientComplex P M) n :=
  (tensorMap (homologyClass P n) (LinearMap.id : M →ₗ[R] M)).liftOfSurjective
    (explicitHomologyTensor_surj P M n)
    ⟨explicitCycleClass P M n, explicitHomologyTensor_ker_le P M n⟩

lemma explicitAlpha_formula (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{w} R) (n : ℤ) (z : cycles P n) (m : M) :
    explicitAlpha P M n (tmul R (homologyClass P n z) m) =
      homologyClass (coefficientComplex P M) n (tensorExplicitCycles P M n (tmul R z m)) := by
  change explicitAlpha P M n
    (tensorMap (homologyClass P n) (LinearMap.id : M →ₗ[R] M) (tmul R z m)) = _
  exact LinearMap.equivOfSurjective_apply _ _

lemma categoricalHomologyIso_class {S : Type*} [Ring S]
    (P : ChainComplex (ModuleCat.{v} S) ℤ)
    (n : ℤ) (z : P.cycles n) :
    (categoricalHomologyIso P n).hom.hom ((P.homologyπ n).hom z) =
      homologyClass P n ((P.sc n).moduleCatCyclesIso.hom.hom z) := by
  have h : P.homologyπ n ≫ (categoricalHomologyIso P n).hom =
      (P.sc n).moduleCatCyclesIso.hom ≫ ModuleCat.ofHom (homologyClass P n) := by
    dsimp only [categoricalHomologyIso, Iso.trans_hom]
    change (P.sc n).homologyπ ≫ (P.sc n).moduleCatHomologyIso.hom ≫ _ = _
    rw [ShortComplex.π_moduleCatCyclesIso_hom_assoc]
    rfl
  exact congrArg (fun f => f.hom z) h

lemma categoricalCycles_val {S : Type*} [Ring S]
    (P : ChainComplex (ModuleCat.{v} S) ℤ)
    (n : ℤ) (z : P.cycles n) :
    ((P.sc n).moduleCatCyclesIso.hom.hom z).val = (P.iCycles n).hom z := by
  exact congrArg (fun f => f.hom z) ((P.sc n).moduleCatCyclesIso_hom_i)

/-- The concrete cycle-tensor arrow exists for every complex, before exactness. -/
def cycleTensorMap (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (M : ModuleCat.{w} R) (n : ℤ) :
    Tensor R (P.homology n) M →ₗ[ℤ] targetHomology P M n :=
  (ULift.moduleEquiv.symm : Homology (coefficientComplex P M) n ≃ₗ[ℤ]
    ULift.{u} (Homology (coefficientComplex P M) n)).toLinearMap.comp
    ((explicitAlpha P M n).comp
      (tensorMap (categoricalHomologyIso P n).hom.hom (LinearMap.id : M →ₗ[R] M)))

lemma cycleTensorMap_formula (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{w} R) (n : ℤ) (z : P.cycles n) (m : M) :
    cycleTensorMap P M n (tmul R ((P.homologyπ n).hom z) m) = tensorCycleClass P M n z m := by
  change ULift.up (explicitAlpha P M n
    (tmul R ((categoricalHomologyIso P n).hom.hom ((P.homologyπ n).hom z)) m)) = _
  rw [categoricalHomologyIso_class, explicitAlpha_formula]
  apply congrArg ULift.up
  apply congrArg (homologyClass (coefficientComplex P M) n)
  apply Subtype.ext
  change tmul R ((P.sc n).moduleCatCyclesIso.hom.hom z).val m =
    tmul R ((P.iCycles n).hom z) m
  rw [categoricalCycles_val]

lemma tensorCycleClass_natural
    {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {M M' : ModuleCat.{w} R} (f : P ⟶ P') (g : M ⟶ M')
    (n : ℤ) (z : P.cycles n) (m : M) :
    (targetHomologyMap f g n).hom (tensorCycleClass P M n z m) =
      tensorCycleClass P' M' n ((HomologicalComplex.cyclesMap f n).hom z) (g.hom m) := by
  change ULift.up (homologyMap (coefficientComplexMap f g) n
    (homologyClass (coefficientComplex P M) n (tensorCycle P M n z m))) = _
  rw [P103.Ch10.Complexes.homologyMap_apply]
  apply congrArg ULift.up
  apply congrArg (homologyClass (coefficientComplex P' M') n)
  apply Subtype.ext
  change tmul R ((f.f n).hom ((P.iCycles n).hom z)) (g.hom m) =
    tmul R ((P'.iCycles n).hom ((HomologicalComplex.cyclesMap f n).hom z)) (g.hom m)
  exact congrArg (fun x => tmul R x (g.hom m))
    (congrArg (fun k => k.hom z) (HomologicalComplex.cyclesMap_i f n)).symm

lemma cycleTensorMap_natural_of_formula
    {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {M M' : ModuleCat.{w} R} (f : P ⟶ P') (g : M ⟶ M') (n : ℤ)
    (a : Tensor R (P.homology n) M →ₗ[ℤ] targetHomology P M n)
    (a' : Tensor R (P'.homology n) M' →ₗ[ℤ] targetHomology P' M' n)
    (ha : ∀ (z : P.cycles n) m,
      a (tmul R ((P.homologyπ n).hom z) m) = tensorCycleClass P M n z m)
    (ha' : ∀ (z : P'.cycles n) m,
      a' (tmul R ((P'.homologyπ n).hom z) m) = tensorCycleClass P' M' n z m) :
    (targetHomologyMap f g n).hom.comp a =
      a'.comp (tensorMap (HomologicalComplex.homologyMap f n).hom g.hom) := by
  apply tensor_hom_ext
  intro h m
  have hs : Function.Surjective (P.homologyπ n).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨z,rfl⟩ := hs h
  change (targetHomologyMap f g n).hom (a (tmul R ((P.homologyπ n).hom z) m)) =
    a' (tmul R ((HomologicalComplex.homologyMap f n).hom ((P.homologyπ n).hom z)) (g.hom m))
  have hn := congrArg (fun k => k.hom z) (HomologicalComplex.homologyπ_naturality f n)
  change (HomologicalComplex.homologyMap f n).hom ((P.homologyπ n).hom z) =
    (P'.homologyπ n).hom ((HomologicalComplex.cyclesMap f n).hom z) at hn
  rw [ha, hn, ha']
  exact tensorCycleClass_natural f g n z m

/-- Flatness of the previous boundary makes tensoring the cycle inclusion monic. -/
theorem tensorCycleInclusion_injective
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (M : ModuleCat.{w} R) (n : ℤ)
    (hP : FlatTerms.{u,v,w} P)
    (hB : P103.Specs.Ch02.FlatnessTests.RightFlat.{u,v,w} R (boundaries P (n-1))) :
    Function.Injective (tensorMap (cycles P n).subtype (LinearMap.id : M →ₗ[R] M)) := by
  have hs := (basic_exact_sequences R P n).1
  exact (P103.Ch11.UniversalCoefficientsHomology.tensor_shortExact_of_flat
    (ModuleCat.of Rᵐᵒᵖ (cycles P n)) (P.X n) (ModuleCat.of Rᵐᵒᵖ (boundaries P (n-1)))
    (ModuleCat.ofHom (cycles P n).subtype) (ModuleCat.ofHom (boundaryProjection P n))
    hs.1 hs.2.1 hs.2.2 (hP n) hB M).1

/-- No new kernel appears after sending tensored cycles to tensor homology. -/
theorem explicitCycleClass_exact
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (M : ModuleCat.{w} R) (n : ℤ)
    (hinc : Function.Injective
      (tensorMap (cycles P n).subtype (LinearMap.id : M →ₗ[R] M))) :
    Function.Exact
      (tensorMap (boundaryToCycles P n) (LinearMap.id : M →ₗ[R] M))
      (explicitCycleClass P M n) := by
  intro t
  constructor
  · intro ht
    have hb := (P103.Ch10.HomologySequence.class_zero_iff
      (coefficientComplex P M) n (tensorExplicitCycles P M n t)).mp ht
    obtain ⟨y,hy⟩ := hb
    change (tensorMap (P.d ((ComplexShape.down ℤ).prev n) n).hom
      (LinearMap.id : M →ₗ[R] M)) y =
      tensorMap (cycles P n).subtype (LinearMap.id : M →ₗ[R] M) t at hy
    let δ : P.X ((ComplexShape.down ℤ).prev n) →ₗ[Rᵐᵒᵖ] boundaries P n :=
      (P.d ((ComplexShape.down ℤ).prev n) n).hom.rangeRestrict
    refine ⟨tensorMap δ (LinearMap.id : M →ₗ[R] M) y, hinc ?_⟩
    have he : (tensorMap (cycles P n).subtype (LinearMap.id : M →ₗ[R] M)).comp
        ((tensorMap (boundaryToCycles P n) (LinearMap.id : M →ₗ[R] M)).comp
          (tensorMap δ (LinearMap.id : M →ₗ[R] M))) =
        tensorMap (P.d ((ComplexShape.down ℤ).prev n) n).hom (LinearMap.id : M →ₗ[R] M) := by
      apply tensor_hom_ext
      intro x m
      rfl
    exact (LinearMap.congr_fun he y).trans hy
  · rintro ⟨b,rfl⟩
    exact LinearMap.congr_fun (explicitCycleClass_boundary P M n) b

/-- The canonical cycle-tensor arrow is injective whenever the previous
boundary is flat. -/
theorem explicitAlpha_injective
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (M : ModuleCat.{w} R) (n : ℤ)
    (hinc : Function.Injective
      (tensorMap (cycles P n).subtype (LinearMap.id : M →ₗ[R] M))) :
    Function.Injective (explicitAlpha P M n) := by
  apply (injective_iff_map_eq_zero (explicitAlpha P M n)).mpr
  intro x hx
  obtain ⟨t,rfl⟩ := explicitHomologyTensor_surj P M n x
  have ht : explicitCycleClass P M n t = 0 := by
    have he : explicitAlpha P M n
        (tensorMap (homologyClass P n) (LinearMap.id : M →ₗ[R] M) t) =
        explicitCycleClass P M n t := LinearMap.equivOfSurjective_apply _ _
    exact he.symm.trans hx
  obtain ⟨b,hb⟩ := (explicitCycleClass_exact P M n hinc t).mp ht
  rw [← hb]
  have he : (tensorMap (homologyClass P n) (LinearMap.id : M →ₗ[R] M)).comp
      (tensorMap (boundaryToCycles P n) (LinearMap.id : M →ₗ[R] M)) = 0 := by
    apply tensor_hom_ext
    intro b m
    change tmul R (homologyClass P n (boundaryToCycles P n b)) m = 0
    have hb : homologyClass P n (boundaryToCycles P n b) = 0 :=
      (basic_exact_sequences R P n).2.2.1.apply_apply_eq_zero b
    rw [hb]
    simp [tmul]
  exact LinearMap.congr_fun he b


end ConcreteCycleTensorMap

section FiltrationSequence

variable {H E₀ E₁ : ModuleCat.{v} R}
variable (Pm P₀ P₁ : Subobject H) (h₀ : Pm ≤ P₀) (h₁ : P₀ ≤ P₁)

def filtrationZeroIso (hbot : Pm = ⊥) :
    cokernel (Subobject.ofLE Pm P₀ h₀) ≅ (P₀ : ModuleCat.{v} R) := by
  have hz : Subobject.ofLE Pm P₀ h₀ = 0 := by
    apply (cancel_mono P₀.arrow).mp
    rw [Subobject.ofLE_arrow, zero_comp]
    exact (Subobject.mk_eq_bot_iff_zero).mp (by simpa using hbot)
  letI := cokernel.π_of_zero hz
  exact (asIso (cokernel.π (Subobject.ofLE Pm P₀ h₀))).symm

def filtrationLeft (hbot : Pm = ⊥)
    (e₀ : E₀ ≅ cokernel (Subobject.ofLE Pm P₀ h₀)) : E₀ ⟶ H :=
  e₀.hom ≫ (filtrationZeroIso Pm P₀ h₀ hbot).hom ≫ P₀.arrow

def filtrationRight (htop : P₁ = ⊤)
    (e₁ : E₁ ≅ cokernel (Subobject.ofLE P₀ P₁ h₁)) : H ⟶ E₁ := by
  letI : IsIso P₁.arrow := (Subobject.isIso_arrow_iff_eq_top P₁).mpr htop
  exact inv P₁.arrow ≫ cokernel.π (Subobject.ofLE P₀ P₁ h₁) ≫ e₁.inv

set_option backward.isDefEq.respectTransparency false in
theorem filtrationSequence_exact (hbot : Pm = ⊥) (htop : P₁ = ⊤)
    (e₀ : E₀ ≅ cokernel (Subobject.ofLE Pm P₀ h₀))
    (e₁ : E₁ ≅ cokernel (Subobject.ofLE P₀ P₁ h₁)) :
    Function.Injective (filtrationLeft Pm P₀ h₀ hbot e₀).hom ∧
    Function.Exact (filtrationLeft Pm P₀ h₀ hbot e₀).hom
      (filtrationRight P₀ P₁ h₁ htop e₁).hom ∧
    Function.Surjective (filtrationRight P₀ P₁ h₁ htop e₁).hom := by
  letI : IsIso P₁.arrow := (Subobject.isIso_arrow_iff_eq_top P₁).mpr htop
  have hinj : Function.Injective (filtrationLeft Pm P₀ h₀ hbot e₀).hom := by
    apply (ModuleCat.mono_iff_injective _).mp
    dsimp [filtrationLeft]
    infer_instance
  have hsurj : Function.Surjective (filtrationRight P₀ P₁ h₁ htop e₁).hom := by
    apply (ModuleCat.epi_iff_surjective _).mp
    dsimp [filtrationRight]
    infer_instance
  refine ⟨hinj, ?_, hsurj⟩
  have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
    (ShortComplex.mk (Subobject.ofLE P₀ P₁ h₁)
      (cokernel.π (Subobject.ofLE P₀ P₁ h₁)) (by simp))).mp
    (ShortComplex.exact_cokernel (Subobject.ofLE P₀ P₁ h₁))
  intro x
  constructor
  · intro hx
    have hz : (cokernel.π (Subobject.ofLE P₀ P₁ h₁)).hom ((inv P₁.arrow).hom x) = 0 := by
      apply (ModuleCat.mono_iff_injective e₁.inv).mp inferInstance
      change (filtrationRight P₀ P₁ h₁ htop e₁).hom x = e₁.inv.hom 0
      simpa only [map_zero] using hx
    obtain ⟨z,hz⟩ := (hex _).mp hz
    refine ⟨(e₀ ≪≫ filtrationZeroIso Pm P₀ h₀ hbot).inv.hom z, ?_⟩
    change P₀.arrow.hom
      ((e₀ ≪≫ filtrationZeroIso Pm P₀ h₀ hbot).hom.hom
        ((e₀ ≪≫ filtrationZeroIso Pm P₀ h₀ hbot).inv.hom z)) = x
    have hc : (e₀ ≪≫ filtrationZeroIso Pm P₀ h₀ hbot).hom.hom
        ((e₀ ≪≫ filtrationZeroIso Pm P₀ h₀ hbot).inv.hom z) = z := by
      exact congrArg (fun f => f.hom z) (Iso.inv_hom_id (e₀ ≪≫ filtrationZeroIso Pm P₀ h₀ hbot))
    rw [hc]
    rw [← Subobject.ofLE_arrow h₁]
    change P₁.arrow.hom ((Subobject.ofLE P₀ P₁ h₁).hom z) = x
    rw [hz]
    exact congrArg (fun f => f.hom x) (IsIso.inv_hom_id P₁.arrow)
  · rintro ⟨z,rfl⟩
    change e₁.inv.hom ((cokernel.π (Subobject.ofLE P₀ P₁ h₁)).hom
      ((inv P₁.arrow).hom (P₀.arrow.hom
        ((e₀ ≪≫ filtrationZeroIso Pm P₀ h₀ hbot).hom.hom z)))) = 0
    have hc : P₀.arrow ≫ inv P₁.arrow = Subobject.ofLE P₀ P₁ h₁ := by
      rw [← Subobject.ofLE_arrow h₁]
      simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    change e₁.inv.hom ((cokernel.π (Subobject.ofLE P₀ P₁ h₁)).hom
      ((P₀.arrow ≫ inv P₁.arrow).hom
        ((e₀ ≪≫ filtrationZeroIso Pm P₀ h₀ hbot).hom.hom z))) = 0
    rw [hc]
    change e₁.inv.hom
      ((Subobject.ofLE P₀ P₁ h₁ ≫ cokernel.π (Subobject.ofLE P₀ P₁ h₁)).hom
        ((e₀ ≪≫ filtrationZeroIso Pm P₀ h₀ hbot).hom.hom z)) = 0
    rw [cokernel.condition]
    simp


theorem filtrationLeft_range (hbot : Pm = ⊥)
    (e₀ : E₀ ≅ cokernel (Subobject.ofLE Pm P₀ h₀)) :
    LinearMap.range (filtrationLeft Pm P₀ h₀ hbot e₀).hom =
      (ModuleCat.subobjectModule H) P₀ := by
  change LinearMap.range (P₀.arrow.hom.comp
    (e₀ ≪≫ filtrationZeroIso Pm P₀ h₀ hbot).hom.hom) = LinearMap.range P₀.arrow.hom
  apply LinearMap.range_comp_of_range_eq_top
  apply LinearMap.range_eq_top.mpr
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

theorem filtrationLeft_image (hbot : Pm = ⊥)
    (e₀ : E₀ ≅ cokernel (Subobject.ofLE Pm P₀ h₀)) :
    (ModuleCat.subobjectModule H).symm
      (LinearMap.range (filtrationLeft Pm P₀ h₀ hbot e₀).hom) = P₀ := by
  rw [filtrationLeft_range]
  exact (ModuleCat.subobjectModule H).symm_apply_apply P₀

@[reassoc]
theorem filtrationLeft_projection (hbot : Pm = ⊥)
    (e₀ : E₀ ≅ cokernel (Subobject.ofLE Pm P₀ h₀)) :
    cokernel.π (Subobject.ofLE Pm P₀ h₀) ≫ e₀.inv ≫
      filtrationLeft Pm P₀ h₀ hbot e₀ = P₀.arrow := by
  simp [filtrationLeft, filtrationZeroIso]

@[reassoc]
theorem filtrationRight_projection (htop : P₁ = ⊤)
    (e₁ : E₁ ≅ cokernel (Subobject.ofLE P₀ P₁ h₁)) :
    P₁.arrow ≫ filtrationRight P₀ P₁ h₁ htop e₁ ≫ e₁.hom =
      cokernel.π (Subobject.ofLE P₀ P₁ h₁) := by
  letI : IsIso P₁.arrow := (Subobject.isIso_arrow_iff_eq_top P₁).mpr htop
  simp [filtrationRight]


section Naturality
variable {H' F₀ F₁ : ModuleCat.{v} R}
variable (Qm Q₀ Q₁ : Subobject H') (j₀ : Qm ≤ Q₀) (j₁ : Q₀ ≤ Q₁)

/-- Naturality of the left edge obtained from a two-step filtration. -/
theorem filtrationLeft_natural
    (hbot : Pm = ⊥) (qbot : Qm = ⊥)
    (e₀ : E₀ ≅ cokernel (Subobject.ofLE Pm P₀ h₀))
    (e₀' : F₀ ≅ cokernel (Subobject.ofLE Qm Q₀ j₀))
    (h : H ⟶ H') (k₀ : (P₀ : ModuleCat.{v} R) ⟶ (Q₀ : ModuleCat.{v} R))
    (g₀ : cokernel (Subobject.ofLE Pm P₀ h₀) ⟶
      cokernel (Subobject.ofLE Qm Q₀ j₀))
    (f₀ : E₀ ⟶ F₀)
    (hk : k₀ ≫ Q₀.arrow = P₀.arrow ≫ h)
    (hg : cokernel.π (Subobject.ofLE Pm P₀ h₀) ≫ g₀ =
      k₀ ≫ cokernel.π (Subobject.ofLE Qm Q₀ j₀))
    (he : f₀ ≫ e₀'.hom = e₀.hom ≫ g₀) :
    filtrationLeft Pm P₀ h₀ hbot e₀ ≫ h =
      f₀ ≫ filtrationLeft Qm Q₀ j₀ qbot e₀' := by
  have heinv : e₀.inv ≫ f₀ = g₀ ≫ e₀'.inv := by
    apply (cancel_mono e₀'.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.inv_hom_id_assoc] using congrArg (fun t => e₀.inv ≫ t) he
  apply (cancel_epi (cokernel.π (Subobject.ofLE Pm P₀ h₀) ≫ e₀.inv)).mp
  calc
    (cokernel.π (Subobject.ofLE Pm P₀ h₀) ≫ e₀.inv) ≫
        filtrationLeft Pm P₀ h₀ hbot e₀ ≫ h = P₀.arrow ≫ h := by
      simpa only [Category.assoc] using congrArg (fun t => t ≫ h)
        (filtrationLeft_projection Pm P₀ h₀ hbot e₀)
    _ = k₀ ≫ Q₀.arrow := hk.symm
    _ = k₀ ≫ cokernel.π (Subobject.ofLE Qm Q₀ j₀) ≫ e₀'.inv ≫
        filtrationLeft Qm Q₀ j₀ qbot e₀' := by
      rw [filtrationLeft_projection]
    _ = cokernel.π (Subobject.ofLE Pm P₀ h₀) ≫ g₀ ≫ e₀'.inv ≫
        filtrationLeft Qm Q₀ j₀ qbot e₀' := by
      rw [← Category.assoc k₀, ← hg, Category.assoc]
    _ = (cokernel.π (Subobject.ofLE Pm P₀ h₀) ≫ e₀.inv) ≫ f₀ ≫
        filtrationLeft Qm Q₀ j₀ qbot e₀' := by
      simpa only [Category.assoc] using congrArg
        (fun t => cokernel.π (Subobject.ofLE Pm P₀ h₀) ≫ t ≫
          filtrationLeft Qm Q₀ j₀ qbot e₀') heinv.symm

/-- Naturality of the right edge obtained from a two-step filtration. -/
theorem filtrationRight_natural
    (htop : P₁ = ⊤) (qtop : Q₁ = ⊤)
    (e₁ : E₁ ≅ cokernel (Subobject.ofLE P₀ P₁ h₁))
    (e₁' : F₁ ≅ cokernel (Subobject.ofLE Q₀ Q₁ j₁))
    (h : H ⟶ H') (k₁ : (P₁ : ModuleCat.{v} R) ⟶ (Q₁ : ModuleCat.{v} R))
    (g₁ : cokernel (Subobject.ofLE P₀ P₁ h₁) ⟶
      cokernel (Subobject.ofLE Q₀ Q₁ j₁))
    (f₁ : E₁ ⟶ F₁)
    (hk : k₁ ≫ Q₁.arrow = P₁.arrow ≫ h)
    (hg : cokernel.π (Subobject.ofLE P₀ P₁ h₁) ≫ g₁ =
      k₁ ≫ cokernel.π (Subobject.ofLE Q₀ Q₁ j₁))
    (he : f₁ ≫ e₁'.hom = e₁.hom ≫ g₁) :
    filtrationRight P₀ P₁ h₁ htop e₁ ≫ f₁ =
      h ≫ filtrationRight Q₀ Q₁ j₁ qtop e₁' := by
  letI : IsIso P₁.arrow := (Subobject.isIso_arrow_iff_eq_top P₁).mpr htop
  apply (cancel_epi P₁.arrow).mp
  apply (cancel_mono e₁'.hom).mp
  calc
    P₁.arrow ≫ (filtrationRight P₀ P₁ h₁ htop e₁ ≫ f₁) ≫ e₁'.hom =
        P₁.arrow ≫ filtrationRight P₀ P₁ h₁ htop e₁ ≫ e₁.hom ≫ g₁ := by
      simpa only [Category.assoc] using congrArg
        (fun t => P₁.arrow ≫ filtrationRight P₀ P₁ h₁ htop e₁ ≫ t) he
    _ = cokernel.π (Subobject.ofLE P₀ P₁ h₁) ≫ g₁ := by
      simpa only [Category.assoc] using congrArg (fun t => t ≫ g₁)
        (filtrationRight_projection P₀ P₁ h₁ htop e₁)
    _ = k₁ ≫ cokernel.π (Subobject.ofLE Q₀ Q₁ j₁) := hg
    _ = k₁ ≫ Q₁.arrow ≫ filtrationRight Q₀ Q₁ j₁ qtop e₁' ≫ e₁'.hom := by
      rw [filtrationRight_projection]
    _ = P₁.arrow ≫ (h ≫ filtrationRight Q₀ Q₁ j₁ qtop e₁') ≫ e₁'.hom := by
      simpa only [Category.assoc] using congrArg
        (fun t => t ≫ filtrationRight Q₀ Q₁ j₁ qtop e₁' ≫ e₁'.hom) hk
end Naturality


end FiltrationSequence


section StationaryPages
set_option maxHeartbeats 2400000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
namespace Degeneration
open AdvancedHomologicalAlgebra
open FilteredPage PageCohomology FiniteFiltrationConvergence
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K : CochainComplex A ℤ} (F : Filtration K) (D : F03Specs.PageData F)

def shortComplexZeroIso (S : ShortComplex A) (hf : S.f = 0) (hg : S.g = 0) : S.homology ≅ S.X₂ :=
  (S.asIsoHomologyπ hf).symm ≪≫ S.cyclesIsoX₂ hg

@[reassoc]
theorem shortComplexZeroIso_formula (S : ShortComplex A) (hf : S.f = 0) (hg : S.g = 0)
    {T : A} (x : T ⟶ S.X₂) (hx : x ≫ S.g = 0) :
    S.liftCycles x hx ≫ S.homologyπ ≫ (shortComplexZeroIso S hf hg).hom = x := by
  simp [shortComplexZeroIso]

def nextIso (C : PageCohomology.Data F D) (r : ℤ) (hr : 0 ≤ r)
    (hd : ∀ p n, D.differential r hr p n = 0) (p n : ℤ) :
    object F D (r+1) p n ≅ object F D r p n :=
  eqToIso (by unfold object; congr 1 <;> omega) ≪≫
    C.nextIso r hr (p-r) (n-1) ≪≫
    shortComplexZeroIso _ (hd (p-r) (n-1)) (hd _ _) ≪≫
    eqToIso (by unfold shortComplex object; dsimp; congr 1 <;> omega)

@[reassoc]
theorem nextIso_formula (C : PageCohomology.Data F D) (r : ℤ) (hr : 0 ≤ r)
    (hd : ∀ p n, D.differential r hr p n = 0) (p n : ℤ) :
    toPage F (r+1) p n (D.containment (r+1) p n) ≫ (nextIso F D C r hr hd p n).hom =
      nextRepresentative F D r p n := by
  unfold nextIso
  simp only [Iso.trans_hom, eqToIso.hom]
  have h : ((p,n) : ℤ × ℤ) = (p-r+r,n-1+1) := by ext <;> dsimp <;> omega
  have hn := eqToHom_naturality
    (fun i : ℤ × ℤ => toPage F (r+1) i.1 i.2 (D.containment (r+1) i.1 i.2)) h
  dsimp only at hn
  rw [← Category.assoc, hn]
  rw [Category.assoc, ← Category.assoc _ (C.nextIso r hr (p-r) (n-1)).hom, C.nextIso_formula]
  have hh := shortComplexZeroIso_formula (shortComplex F D r hr (p-r) (n-1))
    (hd (p-r) (n-1)) (hd _ _) (nextRepresentative F D r (p-r+r) (n-1+1))
    (C.next_cycle r hr (p-r) (n-1))
  simp only [Category.assoc]
  rw [reassoc_of% hh]
  have hn' := eqToHom_naturality (fun i : ℤ × ℤ => nextRepresentative F D r i.1 i.2) h
  dsimp only at hn'
  rw [← reassoc_of% hn']
  simp

end Degeneration

namespace Degeneration
open AdvancedHomologicalAlgebra
open FilteredPage PageCohomology FiniteFiltrationConvergence
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K : CochainComplex A ℤ} (F : Filtration K) (D : F03Specs.PageData F)

@[reassoc]
theorem nextIso_closed_formula (C : PageCohomology.Data F D) (r : ℤ) (hr : 0 ≤ r)
    (hd : ∀ p n, D.differential r hr p n = 0) (p n : ℤ) :
    closedToPage F D (r+1) p n ≫ (nextIso F D C r hr hd p n).hom =
      closedToPage F D r p n := by
  dsimp only [closedToPage]
  rw [Category.assoc, nextIso_formula]
  dsimp only [nextRepresentative]
  rw [← Category.assoc, Subobject.ofLE_comp_ofLE]


/-- Any later page is canonically identified with the first stationary page,
with compatibility on closed representatives. -/
theorem exists_backward_iso (C : PageCohomology.Data F D) (s r : ℤ)
    (hs : 0 ≤ s) (hsr : s ≤ r)
    (hd : ∀ t (ht : 0 ≤ t), s ≤ t → ∀ p n, D.differential t ht p n = 0)
    (p n : ℤ) :
    ∃ e : object F D r p n ≅ object F D s p n,
      closedToPage F D r p n ≫ e.hom = closedToPage F D s p n := by
  obtain ⟨k,rfl⟩ := Int.exists_add_of_le hsr
  clear hsr
  induction k with
  | zero =>
    have h : s + (↑(0 : ℕ) : ℤ) = s := by omega
    refine ⟨eqToIso (congrArg (fun t => object F D t p n) h), ?_⟩
    have hn := eqToHom_naturality (fun t => closedToPage F D t p n) h
    simpa only [eqToIso.hom, eqToHom_refl, Category.id_comp] using hn
  | succ k ih =>
    rw [Int.natCast_succ, ← add_assoc]
    obtain ⟨e,he⟩ := ih
    refine ⟨nextIso F D C (s+k) (by omega) (hd _ (by omega) (by omega)) p n ≪≫ e, ?_⟩
    rw [Iso.trans_hom, ← Category.assoc, nextIso_closed_formula, he]

/-- Degeneration upgrades the stable representative identification to the
initial stationary page itself. -/
theorem exists_initial_limit (C : PageCohomology.Data F D)
    (conv : DoubleComplexConvergence.Converges F) (s : ℤ) (hs : 0 ≤ s)
    (hd : ∀ t (ht : 0 ≤ t), s ≤ t → ∀ p n, D.differential t ht p n = 0)
    (p n : ℤ) : Nonempty (LimitIso F D s p n) := by
  obtain ⟨R,hR,hstab⟩ := conv.stabilization n
  let r := max R s
  obtain ⟨L⟩ := conv.limit D r p n (by dsimp [r]; omega) (hstab r (le_max_left _ _) p)
  obtain ⟨e,he⟩ := exists_backward_iso F D C s r hs (le_max_right _ _) hd p n
  refine ⟨⟨e.symm ≪≫ L.iso, ?_⟩⟩
  have hform : closedToPage F D s p n ≫ e.inv = closedToPage F D r p n := by
    rw [← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, hform, L.representative_formula]


/-- Closed representatives already cover the first stationary page. -/
theorem initial_closed_epi (C : PageCohomology.Data F D)
    (conv : DoubleComplexConvergence.Converges F) (s : ℤ) (hs : 0 ≤ s)
    (hd : ∀ t (ht : 0 ≤ t), s ≤ t → ∀ p n, D.differential t ht p n = 0)
    (p n : ℤ) : Epi (closedToPage F D s p n) := by
  obtain ⟨R,hR,hstab⟩ := conv.stabilization n
  let r := max R s
  haveI := closedToPage_epi F D r p n (hstab r (le_max_left _ _) p).1
  obtain ⟨e,he⟩ := exists_backward_iso F D C s r hs (le_max_right _ _) hd p n
  rw [← he]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-- A representative-defined comparison with graded cohomology, together
with surjectivity of closed representatives, forces actual stabilization. -/
theorem stabilized_of_limit_of_epi (r p n : ℤ)
    (I : LimitIso F D r p n) (hEpi : Epi (closedToPage F D r p n)) :
    Stabilized F r p n := by
  let Z := FilteredPage.cycles F r p n
  let B := FilteredPage.boundaries F r p n
  let C := stableCycles F p n
  let B' := stableBoundaries F p n
  have hclosed : exactPart F p n ≤ closed F p n :=
    inf_le_inf_left _ (le_kernelSubobject _ _ (imageSubobject_arrow_comp_eq_zero (K.d_comp_d (n-1) n (n+1))))
  have hBC : B' ≤ C := by
    dsimp only [B', C, stableBoundaries, stableCycles]
    simpa only [gradedRepresentative_naturality] using
      imageSubobject_comp_le (Subobject.ofLE _ _ hclosed)
        (gradedRepresentative F p n (closed F p n) inf_le_left)
  have hBB' : B ≤ B' := by
    have h : boundarySource F r p n ≤ exactPart F p n :=
      inf_le_inf_left _ (imageSubobject_comp_le _ _)
    dsimp only [B, B', FilteredPage.boundaries, stableBoundaries]
    simpa only [gradedRepresentative_naturality] using
      imageSubobject_comp_le (Subobject.ofLE _ _ h)
        (gradedRepresentative F p n (exactPart F p n) inf_le_left)
  have hCZ : C ≤ Z := by
    dsimp only [C, Z, stableCycles, FilteredPage.cycles]
    simpa only [gradedRepresentative_naturality] using
      imageSubobject_comp_le (Subobject.ofLE _ _ (closed_le_almost F r p n))
        (gradedRepresentative F p n (almost F r p n) inf_le_left)
  let i : (C : A) ⟶ (Z : A) := Subobject.ofLE _ _ hCZ
  let j : (B : A) ⟶ (Z : A) := Subobject.ofLE _ _ (D.containment r p n)
  let a := factorThruImageSubobject (gradedRepresentative F p n (closed F p n) inf_le_left)
  have hrep : closedToPage F D r p n = a ≫ i ≫ cokernel.π j := by
    have h : Subobject.ofLE _ _ (closed_le_almost F r p n) ≫
          factorThruImageSubobject (gradedRepresentative F p n (almost F r p n) inf_le_left) =
        a ≫ i := by
      apply (cancel_mono Z.arrow).mp
      simp [a, i, Z, C, Category.assoc]
    change Subobject.ofLE _ _ (closed_le_almost F r p n) ≫ (_ ≫ cokernel.π j) = _
    rw [← Category.assoc, h, Category.assoc]
  have hji : j ≫ cokernel.π i = 0 := by
    dsimp only [j, i]
    rw [← Subobject.ofLE_comp_ofLE _ _ _ (hBB'.trans hBC) hCZ, Category.assoc, cokernel.condition, comp_zero]
  let g := cokernel.desc j (cokernel.π i) hji
  have hg : g = 0 := by
    apply (cancel_epi (closedToPage F D r p n)).mp
    rw [hrep]
    simp [g, Category.assoc]
  have hz : cokernel.π i = 0 := by
    rw [← cokernel.π_desc j (cokernel.π i) hji, show cokernel.desc j (cokernel.π i) hji = 0 from hg, comp_zero]
  have : Epi i := Abelian.epi_of_cokernel_π_eq_zero _ hz
  have : IsIso i := isIso_of_mono_of_epi i
  have hZC : Z = C := by
    apply Subobject.eq_of_comm (asIso i).symm
    change inv i ≫ C.arrow = Z.arrow
    rw [← Subobject.ofLE_arrow hCZ]
    change inv i ≫ i ≫ Z.arrow = Z.arrow
    simp
  refine ⟨hZC, le_antisymm hBB' ?_⟩
  let x := Subobject.ofLE _ _ hclosed
  have hx : x ≫ closedToPage F D r p n = 0 := by
    apply (cancel_mono I.iso.hom).mp
    simp only [Category.assoc, I.representative_formula, zero_comp]
    unfold gradedClass
    rw [← Category.assoc, closedClass_zero_of_boundary, zero_comp]
    rw [Subobject.ofLE_arrow]
    exact Subobject.factors_of_le _ inf_le_right (Subobject.factors_self _)
  have hxj : ((x ≫ a) ≫ i) ≫ cokernel.π j = 0 := by
    simpa only [hrep, Category.assoc] using hx
  let b := Abelian.monoLift j ((x ≫ a) ≫ i) hxj
  apply imageSubobject_le _ b
  calc
    b ≫ B.arrow = b ≫ j ≫ Z.arrow := by simp [j]
    _ = gradedRepresentative F p n (exactPart F p n) inf_le_left := by
      rw [← Category.assoc, Abelian.monoLift_comp]
      simp [a, i, x, Z, C, Category.assoc]


section Naturality
variable {X Y : FilteredComplex A}
variable {f : FilteredMap X Y} {D' : F03Specs.PageData X.filtration}
  {E' : F03Specs.PageData Y.filtration}

theorem initial_limit_naturality
    (M : FilteredPageFunctoriality.MapData f D' E')
    (C : PageCohomology.Data X.filtration D')
    (conv : DoubleComplexConvergence.Converges X.filtration)
    (s : ℤ) (hs : 0 ≤ s)
    (hd : ∀ t (ht : 0 ≤ t), s ≤ t → ∀ p n, D'.differential t ht p n = 0)
    (p n : ℤ) (L : LimitIso X.filtration D' s p n)
    (L' : LimitIso Y.filtration E' s p n) :
    M.map s p n ≫ L'.iso.hom = L.iso.hom ≫ gradedCohomologyMap f p n := by
  haveI := initial_closed_epi X.filtration D' C conv s hs hd p n
  apply (cancel_epi (closedToPage X.filtration D' s p n)).1
  rw [← Category.assoc, closedToPage_naturality, Category.assoc,
    L'.representative_formula, ← Category.assoc, L.representative_formula]
  exact (gradedClass_naturality f p n).symm
end Naturality

end Degeneration

open FiniteFiltrationConvergence

def secondLimit (T : CanonicalTheory.{u,v,w} R) (X : Input.{u,v,w} R)
    (hX : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q))
    (D : Realization T X.P X.M X.Q X.L) (p n : ℤ) :
    LimitIso D.tensorPages.filtration D.tensorPages.pages 2 (-p) (-n) :=
  Classical.choice (Degeneration.exists_initial_limit
    D.tensorPages.filtration D.tensorPages.pages D.tensorPages.next
    D.tensorPages.convergence 2 (by omega)
    (fun r hr h => cochain_differentials_zero T X hX D r h) (-p) (-n))

theorem second_stabilized (T : CanonicalTheory.{u,v,w} R) (X : Input.{u,v,w} R)
    (hX : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q))
    (D : Realization T X.P X.M X.Q X.L) (p n : ℤ) :
    Stabilized D.tensorPages.filtration 2 (-p) (-n) :=
  Degeneration.stabilized_of_limit_of_epi _ _ 2 (-p) (-n) (secondLimit T X hX D p n)
    (Degeneration.initial_closed_epi _ _ D.tensorPages.next D.tensorPages.convergence
      2 (by omega) (fun r _ hr => cochain_differentials_zero T X hX D r hr) (-p) (-n))

def secondTargetIso (T : CanonicalTheory.{u,v,w} R) (X : Input.{u,v,w} R)
    (hX : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q))
    (D : Realization T X.P X.M X.Q X.L) (p n : ℤ) :
    PageCohomology.object D.tensorPages.filtration D.tensorPages.pages 2 (-p) (-n) ≅
      D.targetGraded p n :=
  (secondLimit T X hX D p n).iso ≪≫
    transportedGradedIso D.tensorPages.filtration n _ (D.targetIso n) p

variable {T : CanonicalTheory.{u,v,w} R} {X Y : Input.{u,v,w} R}
  {D : Realization T X.P X.M X.Q X.L} {E : Realization T Y.P Y.M Y.Q Y.L}
  {f : Input.Hom X Y}

theorem step_eq_transported (m : NaturalMap T D E f) (p n : ℤ) :
    m.step p n = transportedStepMap m.filtered n (D.targetIso n) (E.targetIso n) p := by
  apply (cancel_mono (E.targetPiece p n).arrow).1
  rw [m.step_arrow, transportedStepMap_arrow _ _ _ _ _ (m.target n)]

theorem graded_eq_transported (m : NaturalMap T D E f) (p n : ℤ) :
    m.graded p n = transportedGradedMap m.filtered n (D.targetIso n) (E.targetIso n) p := by
  apply (cancel_epi (cokernel.π _)).1
  rw [m.graded_projection]
  simp only [transportedGradedMap, cokernel.map, cokernel.π_desc]
  rw [step_eq_transported]

theorem secondTargetIso_natural (m : NaturalMap T D E f)
    (hX : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q))
    (hY : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (Y.P.homology q))
    (p n : ℤ) :
    m.pages.map 2 (-p) (-n) ≫ (secondTargetIso T Y hY E p n).hom =
      (secondTargetIso T X hX D p n).hom ≫ m.graded p n := by
  have hh := Degeneration.initial_limit_naturality m.pages D.tensorPages.next
    D.tensorPages.convergence 2 (by omega)
    (fun r hr h => cochain_differentials_zero T X hX D r h) (-p) (-n)
    (secondLimit T X hX D p n) (secondLimit T Y hY E p n)
  dsimp only [secondTargetIso]
  simp only [Iso.trans_hom]
  rw [← Category.assoc, hh, Category.assoc, transportedGradedIso_naturality,
    ← graded_eq_transported]
  simp only [Category.assoc]


def secondGradedIso (T : CanonicalTheory.{u,v,w} R) (X : Input.{u,v,w} R)
    (hX : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q))
    (D : Realization T X.P X.M X.Q X.L) (p n : ℤ) :
    D.tensorPages.term 2 p (n-p) ≅ D.targetGraded p n :=
  eqToIso (by unfold TensorPages.term PageCohomology.object; congr 1 <;> omega) ≪≫
    secondTargetIso T X hX D p n

theorem secondGradedIso_natural (m : NaturalMap T D E f)
    (hX : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q))
    (hY : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (Y.P.homology q))
    (p n : ℤ) :
    m.page 2 p (n-p) ≫ (secondGradedIso T Y hY E p n).hom =
      (secondGradedIso T X hX D p n).hom ≫ m.graded p n := by
  dsimp only [secondGradedIso, NaturalMap.page]
  simp only [Iso.trans_hom, eqToIso.hom]
  have h : ((-p,-(p+(n-p))) : ℤ × ℤ) = (-p,-n) := by ext <;> dsimp <;> omega
  have hn := eqToHom_naturality (fun i : ℤ × ℤ => m.pages.map 2 i.1 i.2) h
  dsimp only at hn
  rw [← Category.assoc, hn, Category.assoc, secondTargetIso_natural m hX hY]
  simp only [Category.assoc]


end StationaryPages



theorem cycleTensorMap_injective_of_flat_boundary
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (M : ModuleCat.{w} R) (n : ℤ)
    (hP : FlatTerms.{u,v,w} P)
    (hB : RightFlat.{u,v,w} R (boundaries P (n-1))) :
    Function.Injective (cycleTensorMap P M n) := by
  let e := P103.Ch11.FlatResolutions.tensorLinearEquiv
    (categoricalHomologyIso P n).toLinearEquiv (LinearEquiv.refl R M)
  exact (ULift.moduleEquiv.symm : Homology (coefficientComplex P M) n ≃ₗ[ℤ]
    ULift.{u} (Homology (coefficientComplex P M) n)).injective.comp
    ((explicitAlpha_injective P M n (tensorCycleInclusion_injective P M n hP hB)).comp
      e.injective)

theorem cycleTensorMap_injective
    (X : Input.{u,v,w} R)
    (hX : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q)) (n : ℤ) :
    Function.Injective (cycleTensorMap X.P X.M n) :=
  cycleTensorMap_injective_of_flat_boundary X.P X.M n X.flat
    (flat_boundaries_of_flatDimensionOne X.P X.L X.bounded X.flat hX (n-1))

theorem cycleTensorMap_natural
    {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {M N : ModuleCat.{w} R} (f : P ⟶ P') (g : M ⟶ N) (n : ℤ) :
    (targetHomologyMap f g n).hom.comp (cycleTensorMap P M n) =
      (cycleTensorMap P' N n).comp (tensorMap (HomologicalComplex.homologyMap f n).hom g.hom) :=
  cycleTensorMap_natural_of_formula f g n _ _
    (cycleTensorMap_formula P M n) (cycleTensorMap_formula P' N n)



/-- Collapse of the actual finite target filtration. -/
theorem two_column_filtration : Specs.FiltrationCollapse.{u,v,w} := by
  intro R _ T X hX D
  exact ⟨target_filtration_endpoints T X hX D,
    fun p n => ⟨second_stabilized T X hX D p n, ⟨secondLimit T X hX D p n⟩⟩⟩

/-- The concrete left arrow, its cycle formula, monicity, and naturality. -/
theorem cycle_tensor_injection : Specs.CycleTensorInjection.{u,v,w} := by
  intro R _
  exact ⟨cycleTensorMap, cycleTensorMap_formula, cycleTensorMap_injective,
    fun f g n => cycleTensorMap_natural f g n⟩


section FlatCoefficientComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
def flatCycleClassEquiv
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (M : ModuleCat.{w} R)
    (hM : P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R M) (n : ℤ) :
    Tensor R (P.homology n) M ≃ₗ[ℤ] Homology (coefficientComplex P M) n := by
  have := AdvancedHomologicalAlgebra.TorBalance.flat_tensor_preservesHomology hM
  exact (((P.sc n).mapHomologyIso (tensorFunctor M)).symm ≪≫
    categoricalHomologyIso (coefficientComplex P M) n).toLinearEquiv

lemma flatCycleClassEquiv_formula
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (M : ModuleCat.{w} R)
    (hM : P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R M) (n : ℤ)
    (z : P.cycles n) (m : M) :
    flatCycleClassEquiv P M hM n (tmul R ((P.homologyπ n).hom z) m) =
      homologyClass (coefficientComplex P M) n (tensorCycle P M n z m) := by
  have := AdvancedHomologicalAlgebra.TorBalance.flat_tensor_preservesHomology hM
  let H := AdvancedHomologicalAlgebra.TorBalance.exactHomologyComparison (tensorFunctor (R := R) M)
  let y : (coefficientComplex P M).cycles n :=
    (H.cyclesEquivalence (P.sc n)).hom.hom (tmul R z m)
  have hπ := congrArg (fun k => k.hom (tmul R z m)) (H.projection (P.sc n))
  have hi := congrArg (fun k => k.hom (tmul R z m)) (H.inclusion (P.sc n))
  have hy : ((coefficientComplex P M).iCycles n).hom y =
      tmul R ((P.iCycles n).hom z) m := hi
  change (categoricalHomologyIso (coefficientComplex P M) n).hom.hom
    ((H.equivalence (P.sc n)).hom.hom (tmul R ((P.homologyπ n).hom z) m)) = _
  change (H.equivalence (P.sc n)).hom.hom (tmul R ((P.homologyπ n).hom z) m) =
    ((coefficientComplex P M).homologyπ n).hom y at hπ
  rw [hπ, categoricalHomologyIso_class]
  apply congrArg (homologyClass (coefficientComplex P M) n)
  apply Subtype.ext
  exact (categoricalCycles_val (coefficientComplex P M) n y).trans hy

lemma cycleTensorMap_eq_flatCycleClassEquiv
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (M : ModuleCat.{w} R)
    (hM : P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R M) (n : ℤ) :
    cycleTensorMap P M n =
      (ULift.moduleEquiv.symm : Homology (coefficientComplex P M) n ≃ₗ[ℤ]
        ULift.{u} (Homology (coefficientComplex P M) n)).toLinearMap.comp
          (flatCycleClassEquiv P M hM n).toLinearMap := by
  apply tensor_hom_ext
  intro h m
  have hs : Function.Surjective (P.homologyπ n).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨z,rfl⟩ := hs h
  rw [cycleTensorMap_formula]
  change _ = ULift.up (flatCycleClassEquiv P M hM n (tmul R ((P.homologyπ n).hom z) m))
  rw [flatCycleClassEquiv_formula]
  rfl

end FlatCoefficientComparison


section RightEdge
set_option maxHeartbeats 2400000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

def torGradedIso (T : CanonicalTheory.{u,v,w} R) (X : Input.{u,v,w} R)
    (hX : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q))
    (D : Realization T X.P X.M X.Q X.L) (p : ℕ) (n : ℤ) :
    ModuleCat.of ℤ (T.Tor (X.P.homology (n-p)) X.M p) ≅ D.targetGraded p n :=
  (D.secondIso p (n-p)).symm ≪≫ secondGradedIso T X hX D p n

variable {T : CanonicalTheory.{u,v,w} R} {X Y : Input.{u,v,w} R}
  {D : Realization T X.P X.M X.Q X.L} {E : Realization T Y.P Y.M Y.Q Y.L}
  {f : Input.Hom X Y}

theorem torGradedIso_natural (m : NaturalMap T D E f)
    (hX : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q))
    (hY : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (Y.P.homology q))
    (p : ℕ) (n : ℤ) :
    ModuleCat.ofHom (T.torMap p (HomologicalComplex.homologyMap f.right (n-p)) f.coefficient) ≫
        (torGradedIso T Y hY E p n).hom =
      (torGradedIso T X hX D p n).hom ≫ m.graded p n := by
  have hi : ModuleCat.ofHom (T.torMap p (HomologicalComplex.homologyMap f.right (n-p)) f.coefficient) ≫
        (E.secondIso p (n-p)).inv = (D.secondIso p (n-p)).inv ≫ m.page 2 p (n-p) := by
    symm
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
      using congrArg (fun t => (D.secondIso p (n-p)).inv ≫ t ≫ (E.secondIso p (n-p)).inv)
        (m.second p (n-p))
  dsimp only [torGradedIso]
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, hi, Category.assoc, secondGradedIso_natural m hX hY]
  simp only [Category.assoc]

def rightEdge (T : CanonicalTheory.{u,v,w} R) (X : Input.{u,v,w} R)
    (hX : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q))
    (D : Realization T X.P X.M X.Q X.L) (n : ℤ) :
    targetHomology X.P X.M n ⟶ ModuleCat.of ℤ (T.Tor (X.P.homology (n-1)) X.M 1) :=
  filtrationRight (D.targetPiece 0 n) (D.targetPiece 1 n)
    (transportedPiece_increasing _ _ _ _ 1)
    (target_filtration_endpoints T X hX D n).2 (torGradedIso T X hX D 1 n)

/-- The right edge is the actual filtration quotient in the stationary
page's signed Tor coordinate. -/
theorem rightEdge_projection (T : CanonicalTheory.{u,v,w} R) (X : Input.{u,v,w} R)
    (hX : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q))
    (D : Realization T X.P X.M X.Q X.L) (n : ℤ) :
    (D.targetPiece 1 n).arrow ≫ rightEdge T X hX D n =
      cokernel.π (Subobject.ofLE _ _
        (transportedPiece_increasing D.tensorPages.filtration n _ (D.targetIso n) 1)) ≫
      (secondToGraded (X := X) D 1 n (secondLimit T X hX D 1 n)).inv ≫
      (D.secondIso 1 (n-1)).hom := by
  let G := torGradedIso T X hX D 1 n
  have h := filtrationRight_projection (D.targetPiece 0 n) (D.targetPiece 1 n)
    (transportedPiece_increasing _ _ _ _ 1)
    (target_filtration_endpoints T X hX D n).2 G
  have h' := congrArg (fun g => g ≫ G.inv) h
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h'
  exact h'

theorem rightEdge_natural (m : NaturalMap T D E f)
    (hX : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q))
    (hY : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (Y.P.homology q))
    (n : ℤ) :
    rightEdge T X hX D n ≫
        ModuleCat.ofHom (T.torMap 1 (HomologicalComplex.homologyMap f.right (n-1)) f.coefficient) =
      targetHomologyMap f.right f.coefficient n ≫ rightEdge T Y hY E n := by
  exact filtrationRight_natural (D.targetPiece 0 n) (D.targetPiece 1 n)
    (transportedPiece_increasing _ _ _ _ 1) (E.targetPiece 0 n) (E.targetPiece 1 n)
    (transportedPiece_increasing _ _ _ _ 1)
    (target_filtration_endpoints T X hX D n).2 (target_filtration_endpoints T Y hY E n).2
    (torGradedIso T X hX D 1 n) (torGradedIso T Y hY E 1 n)
    (targetHomologyMap f.right f.coefficient n) (m.step 1 n) (m.graded 1 n) _
    (m.step_arrow 1 n) (m.graded_projection 1 n) (torGradedIso_natural m hX hY 1 n)




section GenericProperties
variable {H E₁ : ModuleCat.{v} R}
theorem filtrationRight_properties (P₀ P₁ : Subobject H) (h₁ : P₀ ≤ P₁)
    (htop : P₁ = ⊤) (e₁ : E₁ ≅ cokernel (Subobject.ofLE P₀ P₁ h₁)) :
    Function.Surjective (filtrationRight P₀ P₁ h₁ htop e₁).hom ∧
      LinearMap.ker (filtrationRight P₀ P₁ h₁ htop e₁).hom =
        ModuleCat.subobjectModule H P₀ := by
  let e₀ := (filtrationZeroIso (⊥ : Subobject H) P₀ bot_le rfl).symm
  have hs := filtrationSequence_exact (⊥ : Subobject H) P₀ P₁ bot_le h₁ rfl htop e₀ e₁
  refine ⟨hs.2.2, ?_⟩
  ext x
  change (filtrationRight P₀ P₁ h₁ htop e₁).hom x = 0 ↔ _
  rw [hs.2.1 x, ← filtrationLeft_range (⊥ : Subobject H) P₀ bot_le rfl e₀]
  rfl

end GenericProperties

theorem rightEdge_properties (T : CanonicalTheory.{u,v,w} R) (X : Input.{u,v,w} R)
    (hX : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q))
    (D : Realization T X.P X.M X.Q X.L) (n : ℤ) :
    Function.Surjective (rightEdge T X hX D n).hom ∧
      LinearMap.ker (rightEdge T X hX D n).hom =
        ModuleCat.subobjectModule (targetHomology X.P X.M n) (D.targetPiece 0 n) :=
  filtrationRight_properties (D.targetPiece 0 n) (D.targetPiece 1 n)
    (transportedPiece_increasing D.tensorPages.filtration n _ (D.targetIso n) 1)
    (target_filtration_endpoints T X hX D n).2 (torGradedIso T X hX D 1 n)

/-- The left map can be any prescribed arrow whose actual range is the
zeroth target filtration step; in particular this applies to the cycle map. -/
theorem rightEdge_exact_of_range (T : CanonicalTheory.{u,v,w} R) (X : Input.{u,v,w} R)
    (hX : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q))
    (D : Realization T X.P X.M X.Q X.L) (n : ℤ)
    {B : Type*} [AddCommGroup B] [Module ℤ B] (a : B →ₗ[ℤ] targetHomology X.P X.M n)
    (ha : LinearMap.range a =
      ModuleCat.subobjectModule (targetHomology X.P X.M n) (D.targetPiece 0 n)) :
    Function.Exact a (rightEdge T X hX D n).hom := by
  intro x
  change x ∈ LinearMap.ker (rightEdge T X hX D n).hom ↔ x ∈ LinearMap.range a
  rw [(rightEdge_properties T X hX D n).2, ha]


end RightEdge

namespace TensorEdge
open DoubleTotalization AugmentedDoubleComplexComparison
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
variable {R : Type u} [Ring R]

theorem resolutionTensorAugmentation_zero
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{w} R) (Q : LeftResolution R M) (a : ℤ) :
    sumInjection (tensorCochain P (extendNonnegativeChain Q.complex)) a 0 a (add_zero a) ≫
      (resolutionTensorAugmentation P M Q).f a =
      ModuleCat.ofHom
        ((ULift.moduleEquiv : ULift.{u} (Tensor R (P.X (-a)) M) ≃ₗ[ℤ]
          Tensor R (P.X (-a)) M).symm.toLinearMap.comp
          (tensorMap (LinearMap.id : P.X (-a) →ₗ[Rᵐᵒᵖ] P.X (-a))
            (Q.ε.comp (Q.complex.extendXIso nonnegativeChainEmbedding
              (by rfl : (0 : ℤ) = 0)).hom.hom))) := by
  simp only [resolutionTensorAugmentation, tensorAugmentationMap,
    HomologicalComplex.comp_f]
  simp only [Category.assoc]
  rw [HomologicalComplex₂.ιTotal_map_assoc]
  rw [reassoc_of% (singleTensorTotalIso_zero P (liftedCoefficient M) a)]
  change ModuleCat.ofHom (tensorMap (LinearMap.id : P.X (-a) →ₗ[Rᵐᵒᵖ] P.X (-a))
      ((resolutionAugmentation M Q).f 0).hom) ≫
    ModuleCat.ofHom (tensorMap LinearMap.id
      (HomologicalComplex.singleObjXSelf (ComplexShape.down ℤ) 0 (liftedCoefficient M)).hom.hom) ≫
    ModuleCat.ofHom (tensorLiftRightEquiv (P.X (-a)) M).toLinearMap = _
  rw [resolutionAugmentation_f_zero]

  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro p q
  apply ULift.ext
  change tmul R p
    ((HomologicalComplex.singleObjXSelf (ComplexShape.down ℤ) 0 (liftedCoefficient M)).hom.hom
      ((HomologicalComplex.singleObjXSelf (ComplexShape.down ℤ) 0 (liftedCoefficient M)).inv.hom
        (ULift.up (Q.ε ((Q.complex.extendXIso nonnegativeChainEmbedding
          (by rfl : (0 : ℤ) = 0)).hom.hom q))))).down = _
  have hh := congrArg (fun f => (f.hom
    (ULift.up (Q.ε ((Q.complex.extendXIso nonnegativeChainEmbedding
      (by rfl : (0 : ℤ) = 0)).hom.hom q)))).down)
      (Iso.inv_hom_id (HomologicalComplex.singleObjXSelf (ComplexShape.down ℤ) 0 (liftedCoefficient M)))
  exact congrArg (tmul R p) hh



def reverseCyclesIso (C : ChainComplex (ModuleCat.{v} R) ℤ) (n : ℤ) :
    (reverseChain C).cycles (-n) ≅ C.cycles n :=
  C.restrictionCyclesIso reversal (-n) (-n+1) (by simp)
    (show -(-n) = n by omega) (show -(-n+1) = n-1 by omega) (by simp)

@[reassoc]
theorem reverseHomologyAtNegIso_projection (C : ChainComplex (ModuleCat.{v} R) ℤ) (n : ℤ) :
    (reverseChain C).homologyπ (-n) ≫ (reverseHomologyAtNegIso C n).hom =
      (reverseCyclesIso C n).hom ≫ C.homologyπ n := by
  exact C.homologyπ_restrictionHomologyIso_hom reversal (-n-1) (-n) (-n+1)
    (by simp) (by simp) (show -(-n-1) = n+1 by omega) (show -(-n) = n by omega)
    (show -(-n+1) = n-1 by omega) (by simp) (by simp)

@[reassoc]
theorem reverseCyclesIso_inclusion (C : ChainComplex (ModuleCat.{v} R) ℤ) (n : ℤ) :
    (reverseCyclesIso C n).hom ≫ C.iCycles n =
      (reverseChain C).iCycles (-n) ≫
        (C.restrictionXIso reversal (show -(-n) = n by omega)).hom := by
  exact C.restrictionCyclesIso_hom_iCycles reversal (-n) (-n+1) (by simp)
    (show -(-n) = n by omega) (show -(-n+1) = n-1 by omega) (by simp)

theorem categoricalHomologyIso_class
    {ι : Type*} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{v} R) c) (n : ι) (z : C.cycles n) :
    (categoricalHomologyIso C n).hom.hom ((C.homologyπ n).hom z) =
      homologyClass C n ((C.sc n).moduleCatCyclesIso.hom.hom z) := by
  change ((C.homologyπ n ≫ (categoricalHomologyIso C n).hom).hom z) = _
  dsimp only [categoricalHomologyIso, Iso.trans_hom]
  rw [← Category.assoc]
  dsimp only [HomologicalComplex.homologyπ, HomologicalComplex.homology, HomologicalComplex.cycles]
  rw [ShortComplex.π_moduleCatCyclesIso_hom]
  rfl

theorem categoricalHomologyIso_class_of_val
    {ι : Type*} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{v} R) c) (n : ι) (z : C.cycles n)
    (x : cycles C n) (hx : (C.iCycles n).hom z = x.val) :
    (categoricalHomologyIso C n).hom.hom ((C.homologyπ n).hom z) =
      homologyClass C n x := by
  rw [categoricalHomologyIso_class]
  congr 1
  apply Subtype.ext
  exact (congrArg (fun f => f.hom z)
    (ShortComplex.moduleCatCyclesIso_hom_i (C.sc n))).trans hx

/-- The canonical exact-functor homology isomorphism respects cycle quotients. -/
@[reassoc]
theorem liftedHomologyIso_projection (C : ChainComplex (ModuleCat.{v} ℤ) ℤ) (n : ℤ) :
    ((((ModuleCat.uliftFunctor.{u} ℤ).mapHomologicalComplex (ComplexShape.down ℤ)).obj C).homologyπ n) ≫
      (liftedHomologyIso C n).hom =
      ((C.sc n).mapCyclesIso (ModuleCat.uliftFunctor.{u} ℤ)).hom ≫
        (ModuleCat.uliftFunctor.{u} ℤ).map (C.homologyπ n) := by
  apply (cancel_epi ((C.sc n).mapCyclesIso (ModuleCat.uliftFunctor.{u} ℤ)).inv).mp
  dsimp only [liftedHomologyIso]
  have hp := (AdvancedHomologicalAlgebra.TorBalance.exactHomologyComparison
    (ModuleCat.uliftFunctor.{u} ℤ)).projection (C.sc n)
  change (ModuleCat.uliftFunctor.{u} ℤ).map (C.homologyπ n) ≫
    ((C.sc n).mapHomologyIso (ModuleCat.uliftFunctor.{u} ℤ)).inv =
    ((C.sc n).mapCyclesIso (ModuleCat.uliftFunctor.{u} ℤ)).inv ≫
      ((((ModuleCat.uliftFunctor.{u} ℤ).mapHomologicalComplex (ComplexShape.down ℤ)).obj C).homologyπ n) at hp
  rw [← Category.assoc, ← hp]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]


def coefficientCyclesComparison (C : ChainComplex (ModuleCat.{v} ℤ) ℤ) (n : ℤ) :
    (reverseChain (((ModuleCat.uliftFunctor.{u} ℤ).mapHomologicalComplex
      (ComplexShape.down ℤ)).obj C)).cycles (-n) ⟶
        (ModuleCat.uliftFunctor.{u} ℤ).obj (C.cycles n) :=
  (reverseCyclesIso _ n).hom ≫ ((C.sc n).mapCyclesIso (ModuleCat.uliftFunctor.{u} ℤ)).hom

@[reassoc]
theorem coefficientCyclesComparison_inclusion
    (C : ChainComplex (ModuleCat.{v} ℤ) ℤ) (n : ℤ) :
    coefficientCyclesComparison C n ≫ (ModuleCat.uliftFunctor.{u} ℤ).map (C.iCycles n) =
      (reverseChain (((ModuleCat.uliftFunctor.{u} ℤ).mapHomologicalComplex
        (ComplexShape.down ℤ)).obj C)).iCycles (-n) ≫
        ((((ModuleCat.uliftFunctor.{u} ℤ).mapHomologicalComplex
          (ComplexShape.down ℤ)).obj C).restrictionXIso reversal
            (show -(-n) = n by omega)).hom := by
  dsimp only [coefficientCyclesComparison]
  rw [Category.assoc]
  dsimp only [HomologicalComplex.iCycles, HomologicalComplex.cycles]
  rw [ShortComplex.mapCyclesIso_hom_iCycles]
  exact reverseCyclesIso_inclusion _ n

@[reassoc]
theorem coefficientTargetComparison_projection
    (C : ChainComplex (ModuleCat.{v} ℤ) ℤ) (n : ℤ) :
    (reverseChain (((ModuleCat.uliftFunctor.{u} ℤ).mapHomologicalComplex
      (ComplexShape.down ℤ)).obj C)).homologyπ (-n) ≫
      (coefficientTargetComparison C n).hom =
      coefficientCyclesComparison C n ≫
        (ModuleCat.uliftFunctor.{u} ℤ).map (C.homologyπ n) ≫
        (ModuleCat.uliftFunctor.{u} ℤ).map (categoricalHomologyIso C n).hom := by
  dsimp only [coefficientTargetComparison, coefficientCyclesComparison, Iso.trans_hom,
    Functor.mapIso_hom]
  simp only [Category.assoc]
  rw [reverseHomologyAtNegIso_projection_assoc, liftedHomologyIso_projection_assoc]

theorem coefficientTargetComparison_class
    (C : ChainComplex (ModuleCat.{v} ℤ) ℤ) (n : ℤ)
    (y : (reverseChain (((ModuleCat.uliftFunctor.{u} ℤ).mapHomologicalComplex
      (ComplexShape.down ℤ)).obj C)).cycles (-n))
    (x : cycles C n)
    (hy : (((((ModuleCat.uliftFunctor.{u} ℤ).mapHomologicalComplex
      (ComplexShape.down ℤ)).obj C).restrictionXIso reversal
        (show -(-n) = n by omega)).hom).hom
      (((reverseChain (((ModuleCat.uliftFunctor.{u} ℤ).mapHomologicalComplex
        (ComplexShape.down ℤ)).obj C)).iCycles (-n)).hom y) = ULift.up x.val) :
    (coefficientTargetComparison C n).hom.hom
      (((reverseChain (((ModuleCat.uliftFunctor.{u} ℤ).mapHomologicalComplex
        (ComplexShape.down ℤ)).obj C)).homologyπ (-n)).hom y) =
      ULift.up (homologyClass C n x) := by
  let z : C.cycles n := (C.sc n).moduleCatCyclesIso.inv.hom x
  have hz : (C.iCycles n).hom z = x.val :=
    congrArg (fun f => f.hom x) (ShortComplex.moduleCatCyclesIso_inv_iCycles (C.sc n))
  have hc : (coefficientCyclesComparison C n).hom y = ULift.up z := by
    apply (ModuleCat.mono_iff_injective ((ModuleCat.uliftFunctor.{u} ℤ).map (C.iCycles n))).mp inferInstance
    change ((coefficientCyclesComparison C n ≫
      (ModuleCat.uliftFunctor.{u} ℤ).map (C.iCycles n)).hom y) = ULift.up ((C.iCycles n).hom z)
    rw [coefficientCyclesComparison_inclusion]
    change _ = ULift.up ((C.iCycles n).hom z)
    rw [hz]
    exact hy
  change (((reverseChain (((ModuleCat.uliftFunctor.{u} ℤ).mapHomologicalComplex
    (ComplexShape.down ℤ)).obj C)).homologyπ (-n) ≫
      (coefficientTargetComparison C n).hom).hom y) = _
  rw [coefficientTargetComparison_projection]
  change ULift.up ((categoricalHomologyIso C n).hom.hom
    ((C.homologyπ n).hom ((coefficientCyclesComparison C n).hom y).down)) = _
  rw [hc]
  exact congrArg ULift.up (categoricalHomologyIso_class_of_val C n z x hz)


def rowZeroTensor
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{w} R) (Q : LeftResolution R M)
    (n : ℤ) (z : P.cycles n) (q : (extendNonnegativeChain Q.complex).X 0) :
    ((tensorCochain P (extendNonnegativeChain Q.complex)).X (-n)).X 0 := by
  exact ((coefficientComplex P ((extendNonnegativeChain Q.complex).X 0)).restrictionXIso
    reversal (show -(-n) = n by omega)).inv.hom (tmul R ((P.iCycles n).hom z) q)

theorem indexed_module_cast_apply {I : Type*} (A B : I → ModuleCat.{v} ℤ)
    (f : ∀ i, A i ⟶ B i) {i j : I} (h : i = j) (x : A j) :
    (eqToHom (congrArg B h)).hom
      ((f i).hom ((eqToHom (congrArg A h.symm)).hom x)) = (f j).hom x := by
  cases h
  rfl

theorem resolutionTargetIso_class
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{w} R) (Q : LeftResolution R M) (L : ℤ)
    (hP : BoundedBelow P L) (hflat : FlatTerms.{u,v,w} P)
    (n : ℤ) (z : P.cycles n) (q : (extendNonnegativeChain Q.complex).X 0)
    (y : (sumTotal (tensorCochain P (extendNonnegativeChain Q.complex))).cycles (-n))
    (hy : ((sumTotal (tensorCochain P (extendNonnegativeChain Q.complex))).iCycles (-n)).hom y =
      (sumInjection (tensorCochain P (extendNonnegativeChain Q.complex))
        (-n) 0 (-n) (add_zero _)).hom (rowZeroTensor P M Q n z q)) :
    (resolutionTargetIso P M Q L hP hflat n).hom.hom
      (((sumTotal (tensorCochain P (extendNonnegativeChain Q.complex))).homologyπ (-n)).hom y) =
      AdvancedHomologicalAlgebra.TwoColumnKunneth.tensorCycleClass P M n z
        (Q.ε ((Q.complex.extendXIso nonnegativeChainEmbedding
          (by rfl : (0 : ℤ) = 0)).hom.hom q)) := by
  let C := coefficientComplex P M
  let a := resolutionTensorAugmentation P M Q
  have hc : (resolutionTargetIso P M Q L hP hflat n).hom =
      HomologicalComplex.homologyMap a (-n) ≫ (coefficientTargetComparison C n).hom := rfl
  rw [hc]
  change (coefficientTargetComparison C n).hom.hom
    ((HomologicalComplex.homologyMap a (-n)).hom
      (((sumTotal (tensorCochain P (extendNonnegativeChain Q.complex))).homologyπ (-n)).hom y)) = _
  have hp := congrArg (fun f => f.hom y) (HomologicalComplex.homologyπ_naturality a (-n))
  change (HomologicalComplex.homologyMap a (-n)).hom
      (((sumTotal (tensorCochain P (extendNonnegativeChain Q.complex))).homologyπ (-n)).hom y) =
    ((reverseChain (((ModuleCat.uliftFunctor.{u} ℤ).mapHomologicalComplex
      (ComplexShape.down ℤ)).obj C)).homologyπ (-n)).hom
        ((HomologicalComplex.cyclesMap a (-n)).hom y) at hp
  rw [hp]
  apply coefficientTargetComparison_class C n
    ((HomologicalComplex.cyclesMap a (-n)).hom y)
    (AdvancedHomologicalAlgebra.TwoColumnKunneth.tensorCycle P M n z
      (Q.ε ((Q.complex.extendXIso nonnegativeChainEmbedding
        (by rfl : (0 : ℤ) = 0)).hom.hom q)))
  have hi := congrArg (fun f => f.hom y) (HomologicalComplex.cyclesMap_i a (-n))
  change ((reverseChain (((ModuleCat.uliftFunctor.{u} ℤ).mapHomologicalComplex
      (ComplexShape.down ℤ)).obj C)).iCycles (-n)).hom
      ((HomologicalComplex.cyclesMap a (-n)).hom y) =
    (a.f (-n)).hom (((sumTotal (tensorCochain P (extendNonnegativeChain Q.complex))).iCycles (-n)).hom y) at hi
  rw [hi, hy]
  change (((((ModuleCat.uliftFunctor.{u} ℤ).mapHomologicalComplex
      (ComplexShape.down ℤ)).obj C).restrictionXIso reversal
        (show -(-n) = n by omega)).hom).hom
      (((sumInjection (tensorCochain P (extendNonnegativeChain Q.complex))
        (-n) 0 (-n) (add_zero _)) ≫ a.f (-n)).hom (rowZeroTensor P M Q n z q)) = _
  rw [resolutionTensorAugmentation_zero]
  exact indexed_module_cast_apply
    (fun i => (coefficientComplex P ((extendNonnegativeChain Q.complex).X 0)).X i)
    (fun i => (((ModuleCat.uliftFunctor.{u} ℤ).mapHomologicalComplex
      (ComplexShape.down ℤ)).obj C).X i)
    (fun i => ModuleCat.ofHom
      ((ULift.moduleEquiv : ULift.{u} (Tensor R (P.X i) M) ≃ₗ[ℤ]
        Tensor R (P.X i) M).symm.toLinearMap.comp
        (tensorMap (LinearMap.id : P.X i →ₗ[Rᵐᵒᵖ] P.X i)
          (Q.ε.comp (Q.complex.extendXIso nonnegativeChainEmbedding
            (by rfl : (0 : ℤ) = 0)).hom.hom))))
    (show -(-n) = n by omega) (tmul R ((P.iCycles n).hom z) q)


end TensorEdge


section ZerothRow
open DoubleTotalization FiniteDiagonalFiltrations DoubleComplexFirstPages
namespace RowEdge
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
variable {A : Type u} [Category.{v} A] [Abelian A]
variable (K : Bicomplex A) [K.HasTotal (ComplexShape.up ℤ)]
variable (F : Filtration (sumTotal K)) (hF : HasFiltrationFormula K Prod.snd F)
variable (hz : ∀ i j : ℤ, 0 < j → IsZero ((K.X i).X j))

def rowZeroToStep : K.flip.X 0 ⟶ F.step 0 where
  f n := summandToStep K Prod.snd F hF 0 n 0 n (by omega) (by simp)
  comm' i j hij := by
    simp only [ComplexShape.up_Rel] at hij
    subst j
    change _ = (K.d i (i+1)).f 0 ≫ _
    rw [summandToStep_d K Prod.snd F hF 0 i 0 i (i+1)
      (by omega) rfl (by simp) (by simp) (by simp)]
    have hv : (K.X i).d 0 (0+1) = 0 := (hz i 1 (by omega)).eq_of_tgt _ _
    rw [hv, zero_comp, smul_zero, add_zero]

def rowZeroCoordinate (n : ℤ) : (F.piece 0 n : A) ⟶ (K.X n).X 0 :=
  stepDesc K Prod.snd F hF 0 n (fun i j _ _ => coordinateLeg K n 0 i j)

lemma rowZeroToStep_component_inv (n : ℤ) :
    (rowZeroToStep K F hF hz).f n ≫ rowZeroCoordinate K F hF n = 𝟙 _ := by
  dsimp only [rowZeroToStep, rowZeroCoordinate]
  rw [summandToStep_stepDesc]
  exact coordinateLeg_self K n 0

lemma rowZeroToStep_component_hom (n : ℤ) :
    rowZeroCoordinate K F hF n ≫ (rowZeroToStep K F hF hz).f n = 𝟙 _ := by
  apply step_hom_ext K Prod.snd F hF
  intro i j hij hj
  dsimp only [Prod.snd] at hj
  by_cases hj0 : j = 0
  · subst j
    have hi : i = n := by omega
    subst i
    change (rowZeroToStep K F hF hz).f n ≫ rowZeroCoordinate K F hF n ≫
      (rowZeroToStep K F hF hz).f n = (rowZeroToStep K F hF hz).f n ≫ 𝟙 _
    rw [← Category.assoc, rowZeroToStep_component_inv]
    simp
  · exact (hz i j (by omega)).eq_of_src _ _

instance rowZeroToStep_component_isIso (n : ℤ) :
    IsIso ((rowZeroToStep K F hF hz).f n) :=
  ⟨⟨rowZeroCoordinate K F hF n,
    rowZeroToStep_component_inv K F hF hz n,
    rowZeroToStep_component_hom K F hF hz n⟩⟩

instance rowZeroToStep_isIso : IsIso (rowZeroToStep K F hF hz) := by
  apply HomologicalComplex.Hom.isIso_of_components

/-- If all positive cochain rows vanish, the zeroth row is exactly F⁰. -/
def rowZeroStepIso : K.flip.X 0 ≅ F.step 0 := asIso (rowZeroToStep K F hF hz)

@[reassoc (attr := simp)]
lemma rowZeroToStep_inclusion (n : ℤ) :
    (rowZeroToStep K F hF hz).f n ≫ (F.inclusion 0).f n =
      sumInjection K n 0 n (by omega) := by
  exact summandToStep_arrow K Prod.snd F hF 0 n 0 n (by omega) (by simp)

lemma cohomologyPiece_rowZero (n : ℤ) :
    FiniteFiltrationConvergence.cohomologyPiece F 0 n =
      imageSubobject (HomologicalComplex.homologyMap
        (rowZeroToStep K F hF hz ≫ F.inclusion 0) n) := by
  rw [HomologicalComplex.homologyMap_comp]
  exact (imageSubobject_iso_comp
    (HomologicalComplex.homologyMap (rowZeroToStep K F hF hz) n)
    (HomologicalComplex.homologyMap (F.inclusion 0) n)).symm


lemma map_imageSubobject_iso {B C : A} (f : B ⟶ C) {D : A} (h : C ⟶ D) [IsIso h] :
    (Subobject.map h).obj (imageSubobject f) = imageSubobject (f ≫ h) := by
  rw [← Subobject.mk_arrow (imageSubobject f), Subobject.map_mk]
  rw [← Subobject.mk_arrow (imageSubobject (f ≫ h))]
  apply Subobject.mk_eq_mk_of_comm _ _ (imageSubobjectCompIso f h).symm
  exact imageSubobjectCompIso_inv_arrow f h

lemma transportedPiece_rowZero {H : A} (n : ℤ)
    (e : (sumTotal K).homology (-n) ≅ H) :
    KunnethSpectralSequence.transportedPiece F n H e 0 =
      imageSubobject (HomologicalComplex.homologyMap
        (rowZeroToStep K F hF hz ≫ F.inclusion 0) (-n) ≫ e.hom) := by
  change (Subobject.map e.hom).obj (FiniteFiltrationConvergence.cohomologyPiece F (-0) (-n)) = _
  rw [neg_zero, cohomologyPiece_rowZero K F hF hz (-n), map_imageSubobject_iso]

end RowEdge

namespace TensorEdge
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
open AdvancedHomologicalAlgebra.KunnethSpectralSequence
variable {R : Type u} [Ring R]
variable (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (M : ModuleCat.{w} R)
variable (Q : LeftResolution R M) (S : TensorPages P (extendNonnegativeChain Q.complex))

theorem positive_tensorRows_isZero (i j : ℤ) (hj : 0 < j) :
    IsZero (((tensorCochain P (extendNonnegativeChain Q.complex)).X i).X j) := by
  change IsZero (ModuleCat.of ℤ
    (P103.BalancedTensor.Tensor R (P.X (-i)) ((extendNonnegativeChain Q.complex).X (-j))))
  exact tensor_isZero _ _ (Or.inr (extended_resolution_isZero M Q (-j) (by omega)))

def tensorRowZeroStepIso :
    reverseChain (coefficientComplex P ((extendNonnegativeChain Q.complex).X 0)) ≅
      S.filtration.step 0 :=
  RowEdge.rowZeroStepIso _ S.filtration S.formula
    (positive_tensorRows_isZero P M Q)

lemma tensorRowZeroPiece (n : ℤ) :
    FiniteFiltrationConvergence.cohomologyPiece S.filtration 0 n =
      imageSubobject (HomologicalComplex.homologyMap
        ((tensorRowZeroStepIso P M Q S).hom ≫ S.filtration.inclusion 0) n) :=
  RowEdge.cohomologyPiece_rowZero _ S.filtration S.formula
    (positive_tensorRows_isZero P M Q) n
end TensorEdge

end ZerothRow

namespace TensorEdge

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
variable {R : Type u} [Ring R]

def rowHomologyEquiv (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (N : ModuleCat.{w} R) (hN : P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R N) (n : ℤ) :
    Tensor R (P.homology n) N ≃ₗ[ℤ] (reverseChain (coefficientComplex P N)).homology (-n) :=
  (flatCycleClassEquiv P N hN n).trans
    ((categoricalHomologyIso (coefficientComplex P N) n).toLinearEquiv.symm.trans
      (reverseHomologyAtNegIso (coefficientComplex P N) n).toLinearEquiv.symm)

def rowCycle (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (N : ModuleCat.{w} R) (n : ℤ) (z : P.cycles n) (m : N) :
    (reverseChain (coefficientComplex P N)).cycles (-n) :=
  (reverseCyclesIso (coefficientComplex P N) n).inv.hom
    (((coefficientComplex P N).sc n).moduleCatCyclesIso.inv.hom
      (AdvancedHomologicalAlgebra.TwoColumnKunneth.tensorCycle P N n z m))

lemma rowHomologyEquiv_formula (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (N : ModuleCat.{w} R) (hN : P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R N) (n : ℤ)
    (z : P.cycles n) (m : N) :
    rowHomologyEquiv P N hN n (tmul R ((P.homologyπ n).hom z) m) =
      ((reverseChain (coefficientComplex P N)).homologyπ (-n)).hom (rowCycle P N n z m) := by
  let C := coefficientComplex P N
  let x := AdvancedHomologicalAlgebra.TwoColumnKunneth.tensorCycle P N n z m
  let y : C.cycles n := (C.sc n).moduleCatCyclesIso.inv.hom x
  have hy : (categoricalHomologyIso C n).inv.hom (homologyClass C n x) =
      (C.homologyπ n).hom y := by
    apply (categoricalHomologyIso C n).toLinearEquiv.injective
    change (categoricalHomologyIso C n).toLinearEquiv
      ((categoricalHomologyIso C n).toLinearEquiv.symm _) = _
    rw [LinearEquiv.apply_symm_apply]
    change (homologyClass C n) x =
      (categoricalHomologyIso C n).hom.hom ((C.homologyπ n).hom y)
    rw [AdvancedHomologicalAlgebra.TwoColumnKunneth.categoricalHomologyIso_class]
    apply congrArg (homologyClass C n)
    exact (congrArg (fun f => f.hom x) (Iso.inv_hom_id (C.sc n).moduleCatCyclesIso)).symm
  change (reverseHomologyAtNegIso C n).inv.hom
    ((categoricalHomologyIso C n).inv.hom (flatCycleClassEquiv P N hN n
      (tmul R ((P.homologyπ n).hom z) m))) = _
  rw [flatCycleClassEquiv_formula, hy]
  apply (reverseHomologyAtNegIso C n).toLinearEquiv.injective
  change (reverseHomologyAtNegIso C n).toLinearEquiv
      ((reverseHomologyAtNegIso C n).toLinearEquiv.symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  have hh := congrArg (fun f => f.hom (rowCycle P N n z m)) (reverseHomologyAtNegIso_projection C n)
  change (reverseHomologyAtNegIso C n).hom.hom
      (((reverseChain C).homologyπ (-n)).hom (rowCycle P N n z m)) =
    (C.homologyπ n).hom ((reverseCyclesIso C n).hom.hom (rowCycle P N n z m)) at hh
  change (C.homologyπ n).hom y = (reverseHomologyAtNegIso C n).hom.hom
    (((reverseChain C).homologyπ (-n)).hom (rowCycle P N n z m))
  rw [hh]
  apply congrArg (C.homologyπ n).hom
  exact (congrArg (fun f => f.hom y) (Iso.inv_hom_id (reverseCyclesIso C n))).symm

lemma rowCycle_value (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (N : ModuleCat.{w} R) (n : ℤ) (z : P.cycles n) (m : N) :
    ((reverseChain (coefficientComplex P N)).iCycles (-n)).hom (rowCycle P N n z m) =
      ((coefficientComplex P N).restrictionXIso reversal (show -(-n)=n by omega)).inv.hom
        (tmul R ((P.iCycles n).hom z) m) := by
  let C := coefficientComplex P N
  have hi := C.restrictionCyclesIso_inv_iCycles reversal (-n) (-n+1) (by simp)
    (show -(-n) = n by omega) (show -(-n+1) = n-1 by omega) (by simp)
  change ((reverseCyclesIso C n).inv ≫ (reverseChain C).iCycles (-n)).hom
      ((C.sc n).moduleCatCyclesIso.inv.hom
        (AdvancedHomologicalAlgebra.TwoColumnKunneth.tensorCycle P N n z m)) = _
  have hi' : (reverseCyclesIso C n).inv ≫ (reverseChain C).iCycles (-n) =
      C.iCycles n ≫ (C.restrictionXIso reversal (show -(-n)=n by omega)).inv := hi
  rw [hi']
  change ((C.restrictionXIso reversal _).inv).hom
    ((C.iCycles n).hom ((C.sc n).moduleCatCyclesIso.inv.hom
      (AdvancedHomologicalAlgebra.TwoColumnKunneth.tensorCycle P N n z m))) = _
  congr 1
  exact congrArg (fun f => f.hom
    (AdvancedHomologicalAlgebra.TwoColumnKunneth.tensorCycle P N n z m))
      (ShortComplex.moduleCatCyclesIso_inv_iCycles (C.sc n))

end TensorEdge

section FinalAssembly
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000 in
/-- The geometric image identity supplies the full natural system. -/
def systemOfCycleImage (T : CanonicalTheory.{u,v,w} R)
    (S : KunnethSpectralSequence.System T)
    (hImage : ∀ (X : Input.{u,v,w} R)
      (hX : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q)) (n : ℤ),
      (ModuleCat.subobjectModule (targetHomology X.P X.M n)).symm
        (LinearMap.range (cycleTensorMap X.P X.M n)) = (S.realize X).targetPiece 0 n) :
    TwoColumnKunneth.System T S where
  sequence X hX n := {
    α := cycleTensorMap X.P X.M n
    β := (rightEdge T X hX (S.realize X) n).hom
    injective := cycleTensorMap_injective X hX n
    exact := rightEdge_exact_of_range T X hX (S.realize X) n
      (cycleTensorMap X.P X.M n) (by
        have him := congrArg (ModuleCat.subobjectModule (targetHomology X.P X.M n)) (hImage X hX n)
        simpa only [OrderIso.apply_symm_apply] using him)
    surjective := (rightEdge_properties T X hX (S.realize X) n).1
    cycle_formula := cycleTensorMap_formula X.P X.M n
    image := hImage X hX n
    lower := (target_filtration_endpoints T X hX (S.realize X) n).1
    upper := (target_filtration_endpoints T X hX (S.realize X) n).2
    stable_second := second_stabilized T X hX (S.realize X) 1 n
    projection_formula := ⟨secondLimit T X hX (S.realize X) 1 n,
      rightEdge_projection T X hX (S.realize X) n⟩ }
  natural_left X Y hX hY f g n := cycleTensorMap_natural f g n
  natural_right X Y hX hY f g n := by
    obtain ⟨l,hl⟩ := S.lift_exists X Y f g
    let F : Input.Hom X Y := ⟨f,g,l,hl⟩
    have hn := rightEdge_natural (S.map F) hX hY n
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] using
      (congrArg ModuleCat.Hom.hom hn).symm


end FinalAssembly


namespace TensorEdge
open DoubleTotalization
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
def resolutionZeroAugmentation (M : ModuleCat.{w} R) (Q : LeftResolution R M) :
    (extendNonnegativeChain Q.complex).X 0 →ₗ[R] M :=
  Q.ε.comp (Q.complex.extendXIso nonnegativeChainEmbedding (by rfl : (0 : ℤ)=0)).hom.hom

def rowToTarget
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (M : ModuleCat.{w} R)
    (Q : LeftResolution R M) (L : ℤ) (hP : BoundedBelow P L) (hflat : FlatTerms.{u,v,w} P)
    (S : TensorPages P (extendNonnegativeChain Q.complex)) (n : ℤ) :
    (reverseChain (coefficientComplex P ((extendNonnegativeChain Q.complex).X 0))).homology (-n) →ₗ[ℤ]
      targetHomology P M n :=
  (resolutionTargetIso P M Q L hP hflat n).hom.hom.comp
    (HomologicalComplex.homologyMap
      ((tensorRowZeroStepIso P M Q S).hom ≫ S.filtration.inclusion 0) (-n)).hom

lemma rowToTarget_factor
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (M : ModuleCat.{w} R)
    (Q : LeftResolution R M) (hQ : Q.IsProjective) (L : ℤ)
    (hP : BoundedBelow P L) (hflat : FlatTerms.{u,v,w} P)
    (S : TensorPages P (extendNonnegativeChain Q.complex)) (n : ℤ) :
    (rowToTarget P M Q L hP hflat S n).comp
        (rowHomologyEquiv P ((extendNonnegativeChain Q.complex).X 0)
          (extendedResolution_flat M Q hQ 0) n).toLinearMap =
      (cycleTensorMap P M n).comp (tensorMap (LinearMap.id : P.homology n →ₗ[Rᵐᵒᵖ] P.homology n)
        (resolutionZeroAugmentation M Q)) := by
  apply tensor_hom_ext
  intro h q
  have hs : Function.Surjective (P.homologyπ n).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨z,rfl⟩ := hs h
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  change _ = cycleTensorMap P M n (tmul R ((P.homologyπ n).hom z)
    (resolutionZeroAugmentation M Q q))
  rw [rowHomologyEquiv_formula, cycleTensorMap_formula]
  let f := (tensorRowZeroStepIso P M Q S).hom ≫ S.filtration.inclusion 0
  let y := rowCycle P ((extendNonnegativeChain Q.complex).X 0) n z q
  have hp := congrArg (fun f => f.hom y) (HomologicalComplex.homologyπ_naturality f (-n))
  change (HomologicalComplex.homologyMap f (-n)).hom
      (((reverseChain (coefficientComplex P ((extendNonnegativeChain Q.complex).X 0))).homologyπ (-n)).hom y) =
    ((sumTotal (tensorCochain P (extendNonnegativeChain Q.complex))).homologyπ (-n)).hom
      ((HomologicalComplex.cyclesMap f (-n)).hom y) at hp
  change (resolutionTargetIso P M Q L hP hflat n).hom.hom
    ((HomologicalComplex.homologyMap f (-n)).hom
      (((reverseChain (coefficientComplex P ((extendNonnegativeChain Q.complex).X 0))).homologyπ (-n)).hom y)) = _
  rw [hp]
  apply TensorEdge.resolutionTargetIso_class P M Q L hP hflat n z q
    ((HomologicalComplex.cyclesMap f (-n)).hom y)
  have hi := congrArg (fun f => f.hom y) (HomologicalComplex.cyclesMap_i f (-n))
  change ((sumTotal (tensorCochain P (extendNonnegativeChain Q.complex))).iCycles (-n)).hom
      ((HomologicalComplex.cyclesMap f (-n)).hom y) =
    (f.f (-n)).hom
      (((reverseChain (coefficientComplex P ((extendNonnegativeChain Q.complex).X 0))).iCycles (-n)).hom y) at hi
  rw [hi]
  have hf : f.f (-n) = sumInjection (tensorCochain P (extendNonnegativeChain Q.complex))
      (-n) 0 (-n) (add_zero _) :=
    RowEdge.rowZeroToStep_inclusion _ S.filtration S.formula
      (positive_tensorRows_isZero P M Q) (-n)
  rw [hf, rowCycle_value]
  rfl

lemma imageSubobject_moduleCat {B C : ModuleCat.{v} ℤ} (f : B ⟶ C) :
    (ModuleCat.subobjectModule C) (imageSubobject f) = LinearMap.range f.hom := by
  change LinearMap.range (imageSubobject f).arrow.hom = LinearMap.range f.hom
  have hs : Function.Surjective (factorThruImageSubobject f).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hc := congrArg ModuleCat.Hom.hom (imageSubobject_arrow_comp f)
  change (imageSubobject f).arrow.hom.comp (factorThruImageSubobject f).hom = f.hom at hc
  rw [← hc, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hs)]

lemma resolutionZeroAugmentation_surjective (M : ModuleCat.{w} R) (Q : LeftResolution R M) :
    Function.Surjective (resolutionZeroAugmentation M Q) :=
  Q.surjective.comp
    (Q.complex.extendXIso nonnegativeChainEmbedding (by rfl : (0 : ℤ)=0)).toLinearEquiv.surjective

/-- The concrete cycle-tensor arrow has exactly the actual zeroth target piece. -/
theorem cycleTensorMap_image_realizationData
    (T : P103.Specs.Ch11.ExtTorDefinitions.CanonicalTheory.{u,v,w} R)
    (X : Input.{u,v,w} R) (n : ℤ) :
    (ModuleCat.subobjectModule (targetHomology X.P X.M n)).symm
      (LinearMap.range (cycleTensorMap X.P X.M n)) = (realizationData T X).targetPiece 0 n := by
  let D := realizationData T X
  let S := D.tensorPages
  let N := (extendNonnegativeChain X.Q.complex).X 0
  let e := rowHomologyEquiv X.P N (extendedResolution_flat X.M X.Q X.projective 0) n
  let a := rowToTarget X.P X.M X.Q X.L X.bounded X.flat S n
  let q := tensorMap (LinearMap.id : X.P.homology n →ₗ[Rᵐᵒᵖ] X.P.homology n)
    (resolutionZeroAugmentation X.M X.Q)
  have hq : Function.Surjective q :=
    P103.HomTensorExactness.tensorSecond_surjective (resolutionZeroAugmentation X.M X.Q)
      (resolutionZeroAugmentation_surjective X.M X.Q) q.toAddMonoidHom (by intros; rfl)
  have hf : a.comp e.toLinearMap = (cycleTensorMap X.P X.M n).comp q :=
    rowToTarget_factor X.P X.M X.Q X.projective X.L X.bounded X.flat S n
  have hr : LinearMap.range a = LinearMap.range (cycleTensorMap X.P X.M n) := by
    calc
      LinearMap.range a = LinearMap.range (a.comp e.toLinearMap) :=
        (LinearMap.range_comp_of_range_eq_top a e.range).symm
      _ = LinearMap.range ((cycleTensorMap X.P X.M n).comp q) := congrArg LinearMap.range hf
      _ = LinearMap.range (cycleTensorMap X.P X.M n) :=
        LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hq)
  apply (ModuleCat.subobjectModule (targetHomology X.P X.M n)).injective
  rw [OrderIso.apply_symm_apply]
  change LinearMap.range (cycleTensorMap X.P X.M n) =
    (ModuleCat.subobjectModule (targetHomology X.P X.M n))
      (transportedPiece S.filtration n _ (resolutionTargetIso X.P X.M X.Q X.L X.bounded X.flat n) 0)
  rw [RowEdge.transportedPiece_rowZero _ S.filtration S.formula
    (positive_tensorRows_isZero X.P X.M X.Q) n]
  rw [imageSubobject_moduleCat]
  exact hr.symm

end TensorEdge

/-- HA-B08: the actual finite filtration yields the natural two-column
Künneth exact sequence, with its usual cycle-tensor injection. -/
theorem two_column_kunneth : Specs.FullStatement.{u,v,w} := by
  intro R _ T
  let S := KunnethSpectralSequence.system T
  refine ⟨S, ⟨systemOfCycleImage T S ?_⟩⟩
  intro X hX n
  exact TensorEdge.cycleTensorMap_image_realizationData T X n

section OriginalNaturality
universe v' w'

private theorem original_left_natural
    {T : CanonicalTheory.{u,v,w} R} {T' : CanonicalTheory.{u,v',w'} R}
    {X : Input.{u,v,w} R} {Y : Input.{u,v',w'} R}
    {D : Realization T X.P X.M X.Q X.L} {E : Realization T' Y.P Y.M Y.Q Y.L}
    {f : OriginalInputMap X Y} (F : OriginalNaturalMap D E f) (n : ℤ)
    (A : Sequence T X D n) (B : Sequence T' Y E n) :
    (F.target n).comp A.α =
      B.α.comp (tensorMap (F.pHomology n) f.coefficient) := by
  apply tensor_hom_ext
  intro h m
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (X.P.homologyπ n)).mp inferInstance h
  obtain ⟨z', hz', hπ⟩ := F.pHomology_formula n z
  change F.target n (A.α (tmul R ((X.P.homologyπ n).hom z) m)) =
    B.α (tmul R (F.pHomology n ((X.P.homologyπ n).hom z)) (f.coefficient m))
  rw [A.cycle_formula, hπ, B.cycle_formula]
  unfold tensorCycleClass
  rw [F.target_formula]
  obtain ⟨y, hy, hclass⟩ := F.targetQuotient_formula n (tensorCycle X.P X.M n z m)
  dsimp only at hclass
  rw [hclass]
  apply congrArg ULift.up
  apply congrArg (homologyClass (coefficientComplex Y.P Y.M) n)
  apply Subtype.ext
  rw [hy, F.targetChain_formula]
  change tmul R (f.right.app n ((X.P.iCycles n).hom z)) (f.coefficient m) =
    tmul R ((Y.P.iCycles n).hom z') (f.coefficient m)
  rw [hz']

end OriginalNaturality

section OriginalRightNaturality

open FiniteFiltrationConvergence
universe v' w'
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {T : CanonicalTheory.{u,v,w} R} {T' : CanonicalTheory.{u,v',w'} R}
  {X : Input.{u,v,w} R} {Y : Input.{u,v',w'} R}
  {D : Realization T X.P X.M X.Q X.L} {E : Realization T' Y.P Y.M Y.Q Y.L}
  {f : OriginalInputMap X Y}

set_option maxHeartbeats 350000 in
private theorem original_page_reindex (F : OriginalNaturalMap D E f) {a b : ℤ} (h : a = b) :
    (eqToHom (congrArg (PageCohomology.object E.tensorPages.filtration E.tensorPages.pages
      2 (-1)) h)).hom.comp (F.page 2 (-1) a) =
    (F.page 2 (-1) b).comp
      (eqToHom (congrArg (PageCohomology.object D.tensorPages.filtration D.tensorPages.pages
        2 (-1)) h)).hom := by
  subst b
  simp only [eqToHom_refl, ModuleCat.hom_id, LinearMap.id_comp, LinearMap.comp_id]

set_option maxHeartbeats 350000 in
private theorem original_graded_map_on_second (F : OriginalNaturalMap D E f) (n : ℤ)
    (I : LimitIso D.tensorPages.filtration D.tensorPages.pages 2 (-1) (-n))
    (J : LimitIso E.tensorPages.filtration E.tensorPages.pages 2 (-1) (-n))
    (hI : Stabilized D.tensorPages.filtration 2 (-1) (-n))
    (hJ : Stabilized E.tensorPages.filtration 2 (-1) (-n))
    (z : D.tensorPages.term 2 1 (n-1)) :
    (secondToGraded (X := Y) E 1 n J).hom.hom
        (F.page 2 (-1) (-((1 : ℤ) + (n-1))) z) =
      F.graded 1 n ((secondToGraded (X := X) D 1 n I).hom.hom z) := by
  have h : -((1 : ℤ) + (n-1)) = -n := by omega
  have hr := original_page_reindex F h
  have hl := F.limit_target_natural 2 1 n I J hI hJ
  have hz := LinearMap.congr_fun hr z
  have hw := LinearMap.congr_fun hl
    ((eqToHom (congrArg (PageCohomology.object D.tensorPages.filtration D.tensorPages.pages
        2 (-1)) h)).hom z)
  simp only [secondToGraded, Iso.trans_hom, eqToIso.hom, ModuleCat.hom_comp, LinearMap.comp_apply]
    at hz hw ⊢
  rw [hz]
  exact hw

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency.types true in
private theorem original_right_natural (F : OriginalNaturalMap D E f) (n : ℤ)
    (A : Sequence T X D n) (B : Sequence T' Y E n) :
    B.β.comp (F.target n) = (F.tor (n-1) 1).comp A.β := by
  obtain ⟨I, hA⟩ := A.projection_formula
  obtain ⟨J, hB⟩ := B.projection_formula
  let d := secondToGraded (X := X) D 1 n I
  let e := secondToGraded (X := Y) E 1 n J
  let pD := cokernel.π (Subobject.ofLE _ _
    (transportedPiece_increasing D.tensorPages.filtration n _ (D.targetIso n) 1))
  let pE := cokernel.π (Subobject.ofLE _ _
    (transportedPiece_increasing E.tensorPages.filtration n _ (E.targetIso n) 1))
  have ha (z : (D.targetPiece 1 n : ModuleCat.{max u v w} ℤ)) :
      A.β ((D.targetPiece 1 n).arrow.hom z) =
        (D.secondIso 1 (n-1)).hom.hom (d.inv.hom (pD.hom z)) := by
    exact congrArg (fun k => k.hom z) hA
  have hb (z : (E.targetPiece 1 n : ModuleCat.{max u v' w'} ℤ)) :
      B.β ((E.targetPiece 1 n).arrow.hom z) =
        (E.secondIso 1 (n-1)).hom.hom (e.inv.hom (pE.hom z)) := by
    exact congrArg (fun k => k.hom z) hB
  haveI : IsIso (D.targetPiece 1 n).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).mpr A.upper
  have hsurj := (ModuleCat.epi_iff_surjective (D.targetPiece 1 n).arrow).mp inferInstance
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := hsurj x
  let y := F.step 1 n z
  let s := d.inv.hom (pD.hom z)
  have hs : d.hom.hom s = pD.hom z := by
    exact congrArg (fun k => k.hom (pD.hom z)) d.inv_hom_id
  have hstep : (E.targetPiece 1 n).arrow.hom y =
      F.target n ((D.targetPiece 1 n).arrow.hom z) :=
    LinearMap.congr_fun (F.step_arrow 1 n) z
  have hproj : F.graded 1 n (pD.hom z) = pE.hom y :=
    LinearMap.congr_fun (F.graded_projection 1 n) z
  have htemp : e.hom.hom (F.page 2 (-1) (-((1 : ℤ) + (n-1))) s) = pE.hom y := by
    have hh : e.hom.hom (F.page 2 (-1) (-((1 : ℤ) + (n-1))) s) =
        F.graded 1 n (d.hom.hom s) :=
      original_graded_map_on_second F n I J A.stable_second B.stable_second s
    rw [hh, hs, hproj]
  have hpinv : e.inv.hom (pE.hom y) = F.page 2 (-1) (-((1 : ℤ) + (n-1))) s := by
    rw [← htemp]
    exact congrArg (fun k => k.hom (F.page 2 (-1) (-((1 : ℤ) + (n-1))) s)) e.hom_inv_id
  change B.β (F.target n ((D.targetPiece 1 n).arrow.hom z)) =
    F.tor (n-1) 1 (A.β ((D.targetPiece 1 n).arrow.hom z))
  rw [← hstep, ha, hb, hpinv]
  exact LinearMap.congr_fun (F.second 1 (n-1)) s

end OriginalRightNaturality

section OriginalNaturality
universe v' w'

/-- Both edge maps commute with the original HA-B06 maps, across independent
carrier universes in the two complexes and coefficient modules. -/
theorem original_naturality : Specs.OriginalNaturality.{u,v,w,v',w'} := by
  intro R _ T T' X Y D E f F n A B
  exact ⟨original_left_natural F n A B, original_right_natural F n A B⟩

end OriginalNaturality

namespace IndependentResolution

open KunnethSpectralSequence.IndependentResolution (LimitComparison NaturalMap)
open KunnethSpectralSequence.IndependentResolution
  renaming Input → OriginalInput, Realization → OriginalRealization
open FiniteFiltrationConvergence
universe t v' w' t'

open private limitComparison from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.KunnethSpectralSequence

variable {R : Type u} [Ring R] {T : CanonicalTheory.{u,v,w} R}
  {X : OriginalInput.{u,v,w,t} R}

private theorem second_page_isZero (D : OriginalRealization T X)
    (hX : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q))
    (p q : ℤ) (hp : p < 0 ∨ 1 < p) : IsZero (D.pages.term 2 p q) := by
  rcases hp with hp | hp
  · exact D.support 2 p q (Or.inl hp)
  · letI := higher_tor_vanishes R T (X.P.homology q) (hX q) X.M p.toNat (by omega)
    letI := (D.second.equiv p.toNat q).injective.subsingleton
    have hz := ModuleCat.isZero_of_subsingleton (D.pages.term 2 p.toNat q)
    rwa [Int.toNat_of_nonneg (show 0 ≤ p by omega)] at hz

private theorem page_isZero (D : OriginalRealization T X)
    (hX : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q))
    (r p q : ℤ) (hr : 2 ≤ r) (hp : p < 0 ∨ 1 < p) : IsZero (D.pages.term r p q) :=
  later_pages_isZero D.pages r hr p q (second_page_isZero D hX p q hp)

private theorem page_object_isZero (D : OriginalRealization T X)
    (hX : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q))
    (r : ℤ) (hr : 2 ≤ r) (p n : ℤ) (hp : p < -1 ∨ 0 < p) :
    IsZero (PageCohomology.object D.pages.filtration D.pages.pages r p n) := by
  have hz := page_isZero D hX r (-p) (p-n) hr (by omega)
  simpa only [TensorPages.term, neg_neg, show -(-p+(p-n)) = n by omega] using hz

private theorem page_differential_zero (D : OriginalRealization T X)
    (hX : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q))
    (r : ℤ) (hr₀ : 0 ≤ r) (hr : 2 ≤ r) (p n : ℤ) :
    D.pages.pages.differential r hr₀ p n = 0 := by
  by_cases hp : p < -1 ∨ 0 < p
  · exact (page_object_isZero D hX r hr p n hp).eq_of_src _ _
  · exact (page_object_isZero D hX r hr (p+r) (n+1) (Or.inr (by omega))).eq_of_tgt _ _

/-- The actual row spectral sequence for the given resolution has zero
differentials from the second page and is supported in columns zero and one. -/
theorem _root_.AdvancedHomologicalAlgebra.TwoColumnKunneth.original_resolution_pages :
    Specs.Pages.{u,v,w,t} := by
  intro R _ T X hX D
  refine ⟨page_isZero D hX, fun r hr p q => ?_⟩
  unfold TensorPages.differential homologicalPageDifferential
  rw [page_differential_zero D hX r _ hr, zero_comp]

private theorem stationary_comparison (D : OriginalRealization T X)
    (hX : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q)) (p n : ℤ) :
    Stabilized D.pages.filtration 2 (-p) (-n) ∧ Nonempty (LimitComparison D 2 p n) := by
  have hd := page_differential_zero D hX
  obtain ⟨I⟩ := Degeneration.exists_initial_limit _ _ D.pages.next D.pages.convergence
    2 (by decide) hd (-p) (-n)
  have hepi := Degeneration.initial_closed_epi _ _ D.pages.next D.pages.convergence
    2 (by decide) hd (-p) (-n)
  exact ⟨Degeneration.stabilized_of_limit_of_epi _ _ 2 (-p) (-n) I hepi,
    ⟨limitComparison D 2 p n I⟩⟩

private theorem filtration_endpoints (D : OriginalRealization T X)
    (hX : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q)) (n : ℤ) :
    D.piece (-1) n = ⊥ ∧ D.piece 1 n = ⊤ := by
  apply filtration_endpoints_of_step_eq (fun p => D.piece p n)
    ((KunnethSpectralSequence.original_resolution_convergence R T X D).1 n)
  intro p hp
  obtain ⟨I⟩ := (stationary_comparison D hX p n).2
  have hz := page_isZero D hX 2 p (n-p) (by decide) hp
  have hz' : IsZero (PageCohomology.object D.pages.filtration D.pages.pages 2 (-p) (-n)) := by
    simpa only [TensorPages.term, show p + (n-p) = n by omega] using hz
  letI := ModuleCat.subsingleton_of_isZero hz'
  letI := I.equiv.symm.injective.subsingleton
  apply le_antisymm (D.piece_increasing p n)
  intro x hx
  change (⟨x, hx⟩ : D.piece p n) ∈ D.gradedSubmodule p n
  exact (Submodule.Quotient.mk_eq_zero (D.gradedSubmodule p n)).mp (Subsingleton.elim _ 0)

/-- The stabilized second page identifies the two-step target filtration
by the closed representatives of this particular signed total. -/
theorem _root_.AdvancedHomologicalAlgebra.TwoColumnKunneth.original_resolution_filtration :
    Specs.Filtration.{u,v,w,t} := by
  intro R _ T X hX D
  exact ⟨filtration_endpoints D hX, stationary_comparison D hX⟩

private def originalCycleTensorMap (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{w} R) (n : ℤ) :
    Tensor R (P.homology n) M →ₗ[ℤ] Homology (coefficientComplex P M) n :=
  (ULift.moduleEquiv : targetHomology P M n ≃ₗ[ℤ] Homology (coefficientComplex P M) n).toLinearMap.comp
    (cycleTensorMap P M n)

private theorem originalCycleTensorMap_formula (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{w} R) (n : ℤ) (z : P.cycles n) (m : M) :
    originalCycleTensorMap P M n (tmul R ((P.homologyπ n).hom z) m) =
      homologyClass (coefficientComplex P M) n (tensorCycle P M n z m) := by
  unfold originalCycleTensorMap
  rw [LinearMap.comp_apply, cycleTensorMap_formula]
  rfl

private theorem originalCycleTensorMap_injective
    (hX : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q)) (n : ℤ) :
    Function.Injective (originalCycleTensorMap X.P X.M n) := by
  have hf : FlatTerms.{u,v,w} X.P := fun i => rightFlat_changeUniverse (X.flat i)
  exact (ULift.moduleEquiv : targetHomology X.P X.M n ≃ₗ[ℤ] _).injective.comp
    (cycleTensorMap_injective_of_flat_boundary X.P X.M n hf
      (flat_boundaries_of_flatDimensionOne X.P X.L X.bounded hf hX (n-1)))

section ZerothRow

open DoubleTotalization
open private extended_isZero extended_flat
  from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.KunnethSpectralSequence

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

private def zeroAugmentation (X : OriginalInput.{u,v,w,t} R) : X.extended.X 0 →ₗ[R] X.M :=
  X.Q.ε.comp (X.Q.complex.extendXIso nonnegativeChainEmbedding (i := 0) (i' := 0) rfl).hom.hom

private theorem zeroAugmentation_surjective (X : OriginalInput.{u,v,w,t} R) :
    Function.Surjective (zeroAugmentation X) :=
  X.Q.surjective.comp
    (X.Q.complex.extendXIso nonnegativeChainEmbedding (i := 0) (i' := 0) rfl).toLinearEquiv.surjective

private theorem positive_rows_isZero (X : OriginalInput.{u,v,w,t} R)
    (i j : ℤ) (hj : 0 < j) : IsZero ((X.tensor.X i).X j) :=
  tensor_isZero (X.P.X (-i)) (X.extended.X (-j))
    (Or.inr (extended_isZero X.Q.complex (-j) (by omega)))

private def rowZeroInclusion (D : OriginalRealization T X) :
    reverseChain (coefficientComplex X.P (X.extended.X 0)) ⟶ X.total :=
  RowEdge.rowZeroToStep X.tensor D.pages.filtration D.pages.formula (positive_rows_isZero X) ≫
    D.pages.filtration.inclusion 0

private theorem row_augmentation (D : OriginalRealization T X) (i : ℤ) {n : ℤ}
    (h : -i = n) (x : X.P.X n) (q : X.extended.X 0) :
    (X.coefficient.restrictionXIso reversal h).hom.hom
      (D.augmentation.map.app i ((sumInjection X.tensor i 0 i (add_zero i)).hom
        (((coefficientComplex X.P (X.extended.X 0)).restrictionXIso reversal h).inv.hom
          (tmul R x q)))) =
      tmul R x (zeroAugmentation X q) := by
  subst n
  let e := X.Q.complex.extendXIso nonnegativeChainEmbedding (i := 0) (i' := 0) rfl
  obtain ⟨b,rfl⟩ := e.toLinearEquiv.symm.surjective q
  change D.augmentation.map.app i ((sumInjection X.tensor i 0 i (add_zero i)).hom
    (tmul R x (e.inv.hom b))) = tmul R x (X.Q.ε (e.hom.hom (e.inv.hom b)))
  rw [D.augmentation.zero_component i x b]
  exact congrArg (fun y => tmul R x (X.Q.ε y)) (e.toLinearEquiv.apply_symm_apply b).symm

private theorem rowToTarget_factor (D : OriginalRealization T X) (n : ℤ) :
    ((D.target n).toLinearMap.comp (HomologicalComplex.homologyMap (rowZeroInclusion D) (-n)).hom).comp
      (TensorEdge.rowHomologyEquiv X.P (X.extended.X 0) (extended_flat X 0) n).toLinearMap =
    (originalCycleTensorMap X.P X.M n).comp
      (tensorMap (LinearMap.id : X.P.homology n →ₗ[Rᵐᵒᵖ] X.P.homology n) (zeroAugmentation X)) := by
  apply tensor_hom_ext
  intro h q
  obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective (X.P.homologyπ n)).mp inferInstance h
  change D.target n ((HomologicalComplex.homologyMap (rowZeroInclusion D) (-n)).hom
      (TensorEdge.rowHomologyEquiv X.P (X.extended.X 0) (extended_flat X 0) n
        (tmul R ((X.P.homologyπ n).hom z) q))) =
    originalCycleTensorMap X.P X.M n (tmul R ((X.P.homologyπ n).hom z) (zeroAugmentation X q))
  rw [TensorEdge.rowHomologyEquiv_formula, originalCycleTensorMap_formula]
  let f := rowZeroInclusion D
  let y := TensorEdge.rowCycle X.P (X.extended.X 0) n z q
  let cy := (HomologicalComplex.cyclesMap f (-n)).hom y
  have hp := congrArg (fun g => g.hom y) (HomologicalComplex.homologyπ_naturality f (-n))
  change (HomologicalComplex.homologyMap f (-n)).hom
      (((reverseChain (coefficientComplex X.P (X.extended.X 0))).homologyπ (-n)).hom y) =
    (X.total.homologyπ (-n)).hom cy at hp
  rw [hp]
  obtain ⟨b,hb,hclass⟩ := D.target_formula n cy
  rw [hclass]
  apply congrArg (homologyClass X.coefficient n)
  apply Subtype.ext
  rw [hb]
  have hi := congrArg (fun g => g.hom y) (HomologicalComplex.cyclesMap_i f (-n))
  change (X.total.iCycles (-n)).hom cy = (f.f (-n)).hom
    (((reverseChain (coefficientComplex X.P (X.extended.X 0))).iCycles (-n)).hom y) at hi
  have hf : f.f (-n) = sumInjection X.tensor (-n) 0 (-n) (add_zero _) :=
    RowEdge.rowZeroToStep_inclusion X.tensor D.pages.filtration D.pages.formula
      (positive_rows_isZero X) (-n)
  rw [hi, hf]
  dsimp only [y]
  rw [TensorEdge.rowCycle_value]
  exact row_augmentation D (-n) (neg_neg n) ((X.P.iCycles n).hom z) q

/-- The augmentation sends the homology image of the zeroth resolution row
onto the image of cycles tensored with the original coefficient module. -/
private theorem originalCycleTensorMap_range (D : OriginalRealization T X) (n : ℤ) :
    LinearMap.range (originalCycleTensorMap X.P X.M n) = D.piece 0 n := by
  let a := (D.target n).toLinearMap.comp (HomologicalComplex.homologyMap (rowZeroInclusion D) (-n)).hom
  let e := TensorEdge.rowHomologyEquiv X.P (X.extended.X 0) (extended_flat X 0) n
  let q := tensorMap (LinearMap.id : X.P.homology n →ₗ[Rᵐᵒᵖ] X.P.homology n) (zeroAugmentation X)
  have hq : Function.Surjective q :=
    P103.HomTensorExactness.tensorSecond_surjective (zeroAugmentation X)
      (zeroAugmentation_surjective X) q.toAddMonoidHom (by intros; rfl)
  have hr : LinearMap.range a = LinearMap.range (originalCycleTensorMap X.P X.M n) := by
    calc
      LinearMap.range a = LinearMap.range (a.comp e.toLinearMap) :=
        (LinearMap.range_comp_of_range_eq_top a e.range).symm
      _ = LinearMap.range ((originalCycleTensorMap X.P X.M n).comp q) :=
        congrArg LinearMap.range (rowToTarget_factor D n)
      _ = LinearMap.range (originalCycleTensorMap X.P X.M n) :=
        LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hq)
  change LinearMap.range (originalCycleTensorMap X.P X.M n) =
    ((ModuleCat.subobjectModule _) (cohomologyPiece D.pages.filtration (-0) (-n))).map
      (D.target n).toLinearMap
  rw [neg_zero, RowEdge.cohomologyPiece_rowZero X.tensor D.pages.filtration D.pages.formula
    (positive_rows_isZero X), TensorEdge.imageSubobject_moduleCat, ← LinearMap.range_comp]
  exact hr.symm

end ZerothRow

private def upperEquiv (D : OriginalRealization T X) (n : ℤ) (h : D.piece 1 n = ⊤) :
    D.piece 1 n ≃ₗ[ℤ] Homology X.coefficient n :=
  LinearEquiv.ofBijective (D.piece 1 n).subtype
    ⟨Subtype.val_injective, fun x => ⟨⟨x, h ▸ Submodule.mem_top⟩, rfl⟩⟩

/-- The cycle edge and the signed Tor edge for the augmentation-induced
filtration of the given resolution. -/
theorem _root_.AdvancedHomologicalAlgebra.TwoColumnKunneth.original_resolution_sequence :
    Specs.ExactSequence.{u,v,w,t} := by
  intro R _ T X hX D n
  obtain ⟨hbot, htop⟩ := filtration_endpoints D hX n
  obtain ⟨hstable, ⟨I⟩⟩ := stationary_comparison D hX 1 n
  let α := originalCycleTensorMap X.P X.M n
  let e := upperEquiv D n htop
  let τ := I.equiv.symm.trans (secondTorEquiv D n)
  let π := (D.gradedSubmodule 1 n).mkQ
  let β := τ.toLinearMap.comp (π.comp e.symm.toLinearMap)
  have hα : LinearMap.range α = D.piece 0 n := originalCycleTensorMap_range D n
  refine ⟨⟨α, β, originalCycleTensorMap_injective hX n, ?_,
    τ.surjective.comp ((D.gradedSubmodule 1 n).mkQ_surjective.comp e.symm.surjective),
    originalCycleTensorMap_formula X.P X.M n, hα, hbot, htop, hstable, I, ?_⟩⟩
  · intro x
    change τ (π (e.symm x)) = 0 ↔ x ∈ LinearMap.range α
    rw [hα, ← map_zero τ, τ.injective.eq_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change (e.symm x).val ∈ D.piece (1-1) n ↔ x ∈ D.piece 0 n
    change e (e.symm x) ∈ D.piece (1-1) n ↔ x ∈ D.piece 0 n
    rw [e.apply_symm_apply]
    norm_num
  · ext x
    change τ (π (e.symm (e x))) = τ (π x)
    rw [e.symm_apply_apply]

section Naturality

variable {T' : CanonicalTheory.{u,v',w'} R} {Y : OriginalInput.{u,v',w',t'} R}
    {D : OriginalRealization T X} {E : OriginalRealization T' Y}
    {f : KunnethSpectralSequence.IndependentResolution.Input.Hom X Y}

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

private theorem original_cycle_edge_natural (F : NaturalMap D E f) (n : ℤ)
    (A : Sequence T X D n) (B : Sequence T' Y E n) :
    (F.coefficient.homologyMap n).comp A.α =
      B.α.comp (tensorMap (F.right_homology n) f.coefficient) := by
  apply tensor_hom_ext
  intro h m
  obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective (X.P.homologyπ n)).mp inferInstance h
  obtain ⟨z', hz', hπ⟩ := F.right_homology_formula n z
  change F.coefficient.homologyMap n (A.α (tmul R ((X.P.homologyπ n).hom z) m)) =
    B.α (tmul R (F.right_homology n ((X.P.homologyπ n).hom z)) (f.coefficient m))
  rw [A.cycle_formula, hπ, B.cycle_formula]
  obtain ⟨y,hy,hclass⟩ := F.coefficient.homologyMap_induces n (tensorCycle X.P X.M n z m)
  change F.coefficient.homologyMap n
      (homologyClass X.coefficient n (tensorCycle X.P X.M n z m)) =
    homologyClass Y.coefficient n y at hclass
  rw [hclass]
  apply congrArg (homologyClass Y.coefficient n)
  apply Subtype.ext
  rw [hy, F.coefficient_formula]
  change tmul R (f.right.app n ((X.P.iCycles n).hom z)) (f.coefficient m) =
    tmul R ((Y.P.iCycles n).hom z') (f.coefficient m)
  rw [hz']

private theorem second_natural_at (F : NaturalMap D E f) (p : ℕ) (a q n : ℤ)
    (ha : (p : ℤ) = a) (h : a+q = n) :
    let d := eqToIso (show PageCohomology.object D.pages.filtration D.pages.pages 2 (-a) (-n) =
      D.pages.term 2 p q by unfold TensorPages.term; rw [← h, ← ha])
    let e := eqToIso (show PageCohomology.object E.pages.filtration E.pages.pages 2 (-a) (-n) =
      E.pages.term 2 p q by unfold TensorPages.term; rw [← h, ← ha])
    ((e.toLinearEquiv.trans (E.second.equiv p q)).toLinearMap).comp (F.page 2 (-a) (-n)) =
      (F.tor q p).comp ((d.toLinearEquiv.trans (D.second.equiv p q)).toLinearMap) := by
  subst a n
  simpa only [LinearEquiv.coe_trans, Iso.toLinearMap_toLinearEquiv, eqToIso_refl,
    Iso.refl_hom, ModuleCat.hom_id, LinearMap.comp_id] using F.second p q

private theorem original_tor_edge_natural (F : NaturalMap D E f) (n : ℤ)
    (A : Sequence T X D n) (B : Sequence T' Y E n) :
    B.β.comp (F.coefficient.homologyMap n) = (F.tor (n-1) 1).comp A.β := by
  have hs : (secondTorEquiv E n).toLinearMap.comp (F.page 2 (-1) (-n)) =
      (F.tor (n-1) 1).comp (secondTorEquiv D n).toLinearMap :=
    second_natural_at F 1 1 (n-1) n Int.natCast_one (by omega)
  have hl := F.limit_natural 2 1 n A.limit B.limit A.stable_second B.stable_second
  apply LinearMap.ext
  intro x
  let z : D.piece 1 n := ⟨x, A.upper ▸ Submodule.mem_top⟩
  let y := F.step 1 n z
  let s := A.limit.equiv.symm ((D.gradedSubmodule 1 n).mkQ z)
  have hstep : y.val = F.coefficient.homologyMap n x :=
    LinearMap.congr_fun (F.step_formula 1 n) z
  have hproj : F.graded 1 n ((D.gradedSubmodule 1 n).mkQ z) = (E.gradedSubmodule 1 n).mkQ y :=
    LinearMap.congr_fun (F.graded_formula 1 n) z
  have hpinv : B.limit.equiv.symm ((E.gradedSubmodule 1 n).mkQ y) = F.page 2 (-1) (-n) s := by
    apply B.limit.equiv.injective
    rw [LinearEquiv.apply_symm_apply]
    have h := LinearMap.congr_fun hl s
    change B.limit.equiv (F.page 2 (-1) (-n) s) = F.graded 1 n (A.limit.equiv s) at h
    rw [h, show A.limit.equiv s = (D.gradedSubmodule 1 n).mkQ z from A.limit.equiv.apply_symm_apply _, hproj]
  have hA : A.β x = secondTorEquiv D n s := LinearMap.congr_fun A.projection_formula z
  have hB : B.β y.val = secondTorEquiv E n
      (B.limit.equiv.symm ((E.gradedSubmodule 1 n).mkQ y)) :=
    LinearMap.congr_fun B.projection_formula y
  change B.β (F.coefficient.homologyMap n x) = F.tor (n-1) 1 (A.β x)
  rw [← hstep, hB, hpinv, hA]
  exact LinearMap.congr_fun hs s

/-- Both edges are natural for the actual maps between the original inputs
and the given resolutions, with independent term and coefficient levels. -/
theorem _root_.AdvancedHomologicalAlgebra.TwoColumnKunneth.original_resolution_naturality :
    Specs.Naturality.{u,v,w,t,v',w',t'} := by
  intro R _ T T' X Y D E f F n A B
  exact ⟨original_cycle_edge_natural F n A B, original_tor_edge_natural F n A B⟩

end Naturality

end IndependentResolution

end AdvancedHomologicalAlgebra.TwoColumnKunneth
