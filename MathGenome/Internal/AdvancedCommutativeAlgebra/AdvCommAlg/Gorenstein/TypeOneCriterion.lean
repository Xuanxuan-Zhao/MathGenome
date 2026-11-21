import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.GorensteinExtProfile
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.RegularParameters
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.TypeOneCriterion
import Mathlib.RingTheory.SimpleModule.Rank

/-! The equivalences of GC-06. The converse is proved by induction on the
finite depth, preserving simplicity of the first surviving Ext under a
regular principal quotient. No canonical module is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
universe u
open CategoryTheory CategoryTheory.Abelian

namespace AdvCommAlg.Gorenstein.TypeOneCriterion
open RegularReduction ExtProfile

/-- A type-one first surviving Ext stays simple after a regular quotient.
Using simple modules avoids choosing an identification of the two residue fields. -/
lemma simple_ext_quotient (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (x : R) (hm : x ∈ IsLocalRing.maximalIdeal R) (hx : IsSMulRegular R x) (n : ℕ)
    (hs : IsSimpleModule R (Depth.ResidueExt (ModuleCat.of R R) (n + 1))) :
    letI := quotientLocalRing x hm
    IsSimpleModule (R ⧸ Ideal.span {x})
      (Depth.ResidueExt (ModuleCat.of (R ⧸ Ideal.span {x}) (R ⧸ Ideal.span {x})) n) := by
  let Q := R ⧸ Ideal.span {x}
  letI := quotientLocalRing x hm
  let Y := ModuleCat.of Q (IsLocalRing.ResidueField Q)
  let X := (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).obj Y
  letI : Module R Y := Module.compHom Y (Ideal.Quotient.mk (Ideal.span {x}))
  letI : IsScalarTower R Q Y := IsScalarTower.of_compHom R Q Y
  haveI : IsSimpleModule Q Y :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp inferInstance)
  haveI : IsSimpleModule R X :=
    (isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective
      (R := R) (S := Q) (M := Y) Ideal.Quotient.mk_surjective).mpr inferInstance
  obtain ⟨eX⟩ := simpleModule_residue_equiv (R := R) X
  haveI : IsSimpleModule R (Ext X (ModuleCat.of R R) (n + 1)) :=
    (firstArgumentExtEquiv eX (ModuleCat.of R R) (n + 1)).isSimpleModule_iff.mpr hs
  letI : Module R (Ext Y (ModuleCat.of Q Q) n) :=
    Module.compHom _ (Ideal.Quotient.mk (Ideal.span {x}))
  letI : IsScalarTower R Q (Ext Y (ModuleCat.of Q Q) n) :=
    IsScalarTower.of_compHom R Q _
  haveI : IsSimpleModule R (Ext Y (ModuleCat.of Q Q) n) :=
    (principalExtEquiv x hx Y n).isSimpleModule_iff.mpr inferInstance
  exact (isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective
    (R := R) (S := Q) (M := Ext Y (ModuleCat.of Q Q) n)
    Ideal.Quotient.mk_surjective).mp inferInstance

/-- Induction formulation of the converse: depth and dimension coincide,
and the first surviving residue-field Ext is simple. -/
lemma gorenstein_of_dimension_depth_simple_ext (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
      ringKrullDim R = (n : WithBot ℕ∞) → Depth.depth R R = (n : ℕ∞) →
      IsSimpleModule R (Depth.ResidueExt (ModuleCat.of R R) n) → LocalGorenstein R := by
  induction n with
  | zero =>
    intro R _ _ _ hdim hd hs
    have hlen : IsFiniteLength R R :=
      (CohenMacaulay.dimension_zero_iff_finiteLength R R).mp
        (by simpa [CohenMacaulay.dimension, Module.supportDim_self_eq_ringKrullDim] using hdim)
    haveI : IsArtinianRing R := (isFiniteLength_iff_isNoetherian_isArtinian.mp hlen).2
    obtain ⟨s, _⟩ := hom_socle_equiv R R
    let e : Depth.ResidueExt (ModuleCat.of R R) 0 ≃ₗ[R] socle R R :=
      Ext.linearEquiv₀.trans
        (ModuleCat.homLinearEquiv.trans (s.restrictScalars R))
    haveI : IsSimpleModule R (socle R R) := e.isSimpleModule_iff.mp hs
    haveI : IsSimpleModule (IsLocalRing.ResidueField R) (socle R R) :=
      (isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective
        (R := R) (S := IsLocalRing.ResidueField R) (M := socle R R)
        IsLocalRing.residue_surjective).mp inferInstance
    haveI : Module.Injective R R := selfInjective_of_socle_finrank_one
      (isSimpleModule_iff_finrank_eq_one.mp inferInstance)
    have hinj := Module.injective_object_of_injective_module R R
    exact (finiteInjectiveDimension_iff_exists_bound R R).mpr
      ⟨0, (injective_iff_hasInjectiveDimensionLE_zero _).mp hinj⟩
  | succ n ih =>
    intro R _ _ _ hdim hd hs
    have hne : Depth.depth R R ≠ 0 := by rw [hd]; simp
    obtain ⟨x, hm, hx⟩ : ∃ x : R, x ∈ IsLocalRing.maximalIdeal R ∧ IsSMulRegular R x := by
      by_contra! h
      exact hne ((Depth.grade_zero_iff_no_regular _ R
        (Depth.maximalIdeal_smul_ne_top R (ModuleCat.of R R))).mpr h)
    let Q := R ⧸ Ideal.span {x}
    letI := quotientLocalRing x hm
    have hdQ : Depth.depth Q Q = (n : ℕ∞) := by
      have h := depth_principalQuotient x hm hx
      rw [hd] at h
      exact h.trans (by norm_cast)
    have hdimQ : ringKrullDim Q = (n : WithBot ℕ∞) := by
      obtain ⟨d, hd'⟩ := CohenMacaulay.exists_nat_dimension (R := Q) Q
      have hdQ' : ringKrullDim Q = (d : WithBot ℕ∞) := by
        simpa [CohenMacaulay.dimension, Module.supportDim_self_eq_ringKrullDim] using hd'
      have h := Depth.supportDim_quotSMulTop_add_one R x hm hx
      rw [Module.supportDim_eq_of_equiv (principalQuotientEquiv x),
        Module.supportDim_quotient_eq_ringKrullDim,
        Module.supportDim_self_eq_ringKrullDim, hdQ', hdim] at h
      have he : d + 1 = n + 1 := by exact_mod_cast h
      simpa [show d = n by omega] using hdQ'
    exact (localGorenstein_quotient_iff R x hm hx).mpr
      (ih Q hdimQ hdQ (simple_ext_quotient R x hm hx n hs))

end AdvCommAlg.Gorenstein.TypeOneCriterion

namespace AdvCommAlg.Gorenstein
variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- A Cohen–Macaulay local ring of type one has finite self-injective dimension. -/
theorem localGorenstein_of_cohenMacaulay_type_one
    (hCM : CohenMacaulay.LocalCohenMacaulay R R) (ht : ringType R = 1) :
    LocalGorenstein R := by
  let n := Depth.depthDegree R (ModuleCat.of R R)
  have hd : Depth.depth R R = (n : ℕ∞) := (Depth.depth_finite R (ModuleCat.of R R)).2.symm
  have hdim : ringKrullDim R = (n : WithBot ℕ∞) := by
    have h := (CohenMacaulay.localCohenMacaulay_self_iff R).mp hCM
    rw [← Depth.depth_eq_libraryDepth (ModuleCat.of R R), hd] at h
    exact h.symm
  haveI : IsSimpleModule (IsLocalRing.ResidueField R)
      (Depth.ResidueExt (ModuleCat.of R R) n) := isSimpleModule_iff_finrank_eq_one.mpr ht
  have hs : IsSimpleModule R (Depth.ResidueExt (ModuleCat.of R R) n) :=
    (isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective
      (R := R) (S := IsLocalRing.ResidueField R)
      (M := Depth.ResidueExt (ModuleCat.of R R) n) IsLocalRing.residue_surjective).mpr inferInstance
  exact TypeOneCriterion.gorenstein_of_dimension_depth_simple_ext n R hdim hd hs

/-- GC-06: Gorenstein is equivalent to Cohen–Macaulay of type one. -/
theorem localGorenstein_iff_cohenMacaulay_type_one :
    LocalGorenstein R ↔ CohenMacaulay.LocalCohenMacaulay R R ∧ ringType R = 1 :=
  ⟨fun h => ⟨localGorenstein_cohenMacaulay R h, localGorenstein_type_one R h⟩,
    fun h => localGorenstein_of_cohenMacaulay_type_one R h.1 h.2⟩

/-- GC-06: eventual residue-field Ext vanishing detects the Gorenstein condition. -/
theorem localGorenstein_iff_eventually_ext_vanishing :
    LocalGorenstein R ↔ ∃ n : ℕ, ∀ i : ℕ, n < i →
      Subsingleton (Depth.ResidueExt (ModuleCat.of R R) i) := by
  rw [LocalGorenstein, finiteInjectiveDimension_iff_exists_bound]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (InjectiveDimensionTest.injectiveDimension_le_iff_residue_ext R
      (ModuleCat.of R R) n).mp ((injectiveDimension_le_iff _ n).mpr hn)⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, (injectiveDimension_le_iff _ n).mp
      ((InjectiveDimensionTest.injectiveDimension_le_iff_residue_ext R
        (ModuleCat.of R R) n).mpr hn)⟩

/-- The second and third conditions in GC-06 are equivalent as well. -/
theorem cohenMacaulay_type_one_iff_eventually_ext_vanishing :
    (CohenMacaulay.LocalCohenMacaulay R R ∧ ringType R = 1) ↔
      ∃ n : ℕ, ∀ i : ℕ, n < i →
        Subsingleton (Depth.ResidueExt (ModuleCat.of R R) i) :=
  (localGorenstein_iff_cohenMacaulay_type_one R).symm.trans
    (localGorenstein_iff_eventually_ext_vanishing R)

end AdvCommAlg.Gorenstein
