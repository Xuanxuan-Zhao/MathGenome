import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.RegularReduction
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.DepthZeroInjectivity
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.SelfInjectiveArtinian
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.SocleCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.RegularQuotient
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.SupportAndParameters
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.GorensteinExtProfile

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
universe u
open CategoryTheory CategoryTheory.Abelian
open scoped Pointwise

namespace AdvCommAlg.Gorenstein.ExtProfile
open RegularReduction ConcentratedChangeOfRings

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- The quotient by the scalar image xR is the principal ring quotient. -/
def principalQuotientEquiv (x : R) :
    QuotSMulTop x R ≃ₗ[R] (R ⧸ Ideal.span {x}) :=
  Submodule.quotEquivOfEq _ _ (by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top])

lemma depth_equiv {S : Type u} [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    {M N : Type u} [AddCommGroup M] [Module S M] [Module.Finite S M]
    [AddCommGroup N] [Module S N] [Module.Finite S N] (e : M ≃ₗ[S] N) :
    Depth.depth S M = Depth.depth S N := by
  rw [Depth.depth_eq_libraryDepth (ModuleCat.of S M),
    Depth.depth_eq_libraryDepth (ModuleCat.of S N)]
  exact IsLocalRing.depth_eq_of_iso e.toModuleIso

lemma depth_principalQuotient (x : R) (hm : x ∈ IsLocalRing.maximalIdeal R)
    (hx : IsSMulRegular R x) :
    letI := quotientLocalRing x hm
    Depth.depth (R ⧸ Ideal.span {x}) (R ⧸ Ideal.span {x}) = Depth.depth R R - 1 := by
  letI := quotientLocalRing x hm
  have hreg : RingTheory.Sequence.IsRegular R [x] :=
    ⟨(RingTheory.Sequence.isWeaklyRegular_singleton_iff R x).mpr hx,
      (ne_top_of_le_ne_top (Depth.maximalIdeal_smul_ne_top R (ModuleCat.of R R))
        (Submodule.smul_mono_left (Ideal.span_le.mpr (by simpa using hm)))).symm⟩
  have h := Depth.grade_quotient_regular R (IsLocalRing.maximalIdeal R)
    (Depth.maximalIdeal_smul_ne_top R (ModuleCat.of R R)) [x] hreg (by simpa using hm)
  simp only [List.length_singleton, Nat.cast_one] at h
  have he : Depth.depth R (R ⧸ (Ideal.span {x} • (⊤ : Submodule R R))) =
      Depth.depth R (R ⧸ Ideal.span {x}) :=
    depth_equiv ((quotientRegularModuleEquiv (Ideal.span {x})).restrictScalars R)
  change Depth.depth R (R ⧸ (Ideal.ofList [x] • (⊤ : Submodule R R))) = _ at h
  rw [Ideal.ofList_singleton] at h
  rw [he] at h
  rw [Depth.depth_eq_grade, ← IsLocalRing.map_maximalIdeal_of_surjective
    (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective]
  exact (Depth.grade_map_of_surjective (R := R) (S := R ⧸ Ideal.span {x})
    (R ⧸ Ideal.span {x}) Ideal.Quotient.mk_surjective _).trans h

/-- The natural quotient Ext comparison is linear over the original ring. -/
def principalExtEquiv (x : R) (hx : IsSMulRegular R x)
    (M : ModuleCat.{u} (R ⧸ Ideal.span {x})) (i : ℕ) :
    letI : Module R (Ext M (ModuleCat.of (R ⧸ Ideal.span {x}) (R ⧸ Ideal.span {x})) i) :=
      Module.compHom _ (Ideal.Quotient.mk (Ideal.span {x}))
    Ext M (ModuleCat.of (R ⧸ Ideal.span {x}) (R ⧸ Ideal.span {x})) i ≃ₗ[R]
      Ext ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).obj M)
        (ModuleCat.of R R) (i + 1) := by
  letI : Module R (Ext M (ModuleCat.of (R ⧸ Ideal.span {x}) (R ⧸ Ideal.span {x})) i) :=
    Module.compHom _ (Ideal.Quotient.mk (Ideal.span {x}))
  let e := Classical.choice (RegularQuotientExt.comparison R x (ModuleCat.of R R) hx hx i)
  let a := coefficientExtLinearEquiv
    (quotientRegularModuleEquiv (Ideal.span {x})).symm.toModuleIso M i
  let b : Ext M (ModuleCat.of (R ⧸ Ideal.span {x})
      (Depth.Rees.quotientModule (Ideal.span {x}) (ModuleCat.of R R))) i ≃ₗ[R ⧸ Ideal.span {x}]
      FirstExt (Ideal.Quotient.mk (Ideal.span {x})) M (ModuleCat.of R R) (i + 1) :=
    (e.app (Opposite.op M)).toLinearEquiv
  refine
    { toAddEquiv := ((a.toAddEquiv.trans b.toAddEquiv).trans
        (firstExtAddEquiv _ M (ModuleCat.of R R) (i + 1)))
      map_smul' := ?_ }
  intro r z
  change firstExtAddEquiv _ M (ModuleCat.of R R) (i + 1)
    (b (a ((Ideal.Quotient.mk (Ideal.span {x}) r) • z))) = _
  rw [a.map_smul]
  erw [b.map_smul]
  exact firstExt_smul_of_base (Ideal.Quotient.mk (Ideal.span {x})) M
    (ModuleCat.of R R) (i + 1) r (b (a z))

/-- Change the first Ext argument along a module isomorphism. -/
def firstArgumentExtEquiv {A B : ModuleCat.{u} R} (e : A ≃ₗ[R] B)
    (N : ModuleCat.{u} R) (i : ℕ) : Ext A N i ≃ₗ[R] Ext B N i :=
  (((linearExtFunctor R (ModuleCat.{u} R) i).mapIso e.symm.toModuleIso.op).app N).toLinearEquiv

lemma simple_torsion (X : ModuleCat.{u} R) [IsSimpleModule R X]
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R) :
    Module.IsTorsionBySet R X I := by
  obtain ⟨e⟩ := simpleModule_residue_equiv (R := R) X
  intro y a
  apply e.injective
  rw [e.map_smul, e.map_zero]
  change IsLocalRing.residue R a.val * e y = 0
  rw [(IsLocalRing.residue_eq_zero_iff _).mpr (hI a.property), zero_mul]

lemma simple_ext_zero_equiv [IsArtinianRing R] (hinj : Injective (ModuleCat.of R R))
    (X : ModuleCat.{u} R) [IsSimpleModule R X] :
    Nonempty (Ext X (ModuleCat.of R R) 0 ≃ₗ[R] X) := by
  haveI := hinj
  have hmod := Module.injective_module_of_injective_object R R
  have hdim := socle_finrank_one_of_selfInjective (R := R) hmod
  obtain ⟨s, _⟩ := hom_socle_equiv R R
  obtain ⟨t⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hdim
  obtain ⟨eX⟩ := simpleModule_residue_equiv (R := R) X
  let e0 : Depth.ResidueExt (ModuleCat.of R R) 0 ≃ₗ[R] Depth.ResidueHom R R :=
    Ext.linearEquiv₀.trans (ModuleCat.homLinearEquiv (R := R) (S := R))
  exact ⟨(firstArgumentExtEquiv (A := X)
    (B := ModuleCat.of R (IsLocalRing.ResidueField R)) eX (ModuleCat.of R R) 0).trans
      (e0.trans ((s.restrictScalars R).trans ((t.symm.restrictScalars R).trans eX.symm)))⟩

/-- Induction on the finite depth, uniformly for all simple first arguments.
This formulation avoids choosing identifications between successive residue fields. -/
theorem depth_profile (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
      LocalGorenstein R → Depth.depth R R = (n : ℕ∞) →
      ringKrullDim R = (n : WithBot ℕ∞) ∧
      HasInjectiveDimensionLE (ModuleCat.of R R) n ∧
      ∀ (X : ModuleCat.{u} R) [IsSimpleModule R X],
        Nonempty (Ext X (ModuleCat.of R R) n ≃ₗ[R] X) := by
  induction n with
  | zero =>
    intro R _ _ _ hG hd
    have hinj := DepthZeroInjectivity.injective_of_depth_zero_of_finite_injectiveDimension
      R hd (ModuleCat.of R R) hG
    haveI : IsArtinianRing R := isArtinianRing_of_selfInjective R hinj
    refine ⟨?_, (injective_iff_hasInjectiveDimensionLE_zero _).mp hinj, ?_⟩
    · have hlen : IsFiniteLength R R :=
        isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
      have hz := (CohenMacaulay.dimension_zero_iff_finiteLength R R).mpr hlen
      simpa [CohenMacaulay.dimension, Module.supportDim_self_eq_ringKrullDim] using hz
    · intro X _
      exact simple_ext_zero_equiv hinj X
  | succ n ih =>
    intro R _ _ _ hG hd
    have hne : Depth.depth R R ≠ 0 := by rw [hd]; simp
    obtain ⟨x, hm, hx⟩ : ∃ x : R, x ∈ IsLocalRing.maximalIdeal R ∧ IsSMulRegular R x := by
      by_contra! h
      exact hne ((Depth.grade_zero_iff_no_regular _ R
        (Depth.maximalIdeal_smul_ne_top R (ModuleCat.of R R))).mpr h)
    let Q := R ⧸ Ideal.span {x}
    letI := quotientLocalRing x hm
    have hGQ : LocalGorenstein Q := (localGorenstein_quotient_iff R x hm hx).mp hG
    have hdQ : Depth.depth Q Q = (n : ℕ∞) := by
      have h := depth_principalQuotient x hm hx
      rw [hd] at h
      exact h.trans (by norm_cast)
    obtain ⟨hdimQ, hboundQ, hsimpleQ⟩ := ih Q hGQ hdQ
    haveI := hboundQ
    refine ⟨?_, injectiveDimension_bound_of_quotient x hm hx n, ?_⟩
    · have h := Depth.supportDim_quotSMulTop_add_one R x hm hx
      rw [Module.supportDim_eq_of_equiv (principalQuotientEquiv x),
        Module.supportDim_quotient_eq_ringKrullDim,
        Module.supportDim_self_eq_ringKrullDim, hdimQ] at h
      simpa only [Nat.cast_add, Nat.cast_one] using h.symm
    · intro X _
      have htor := simple_torsion X (Ideal.span {x}) (Ideal.span_le.mpr (by simpa using hm))
      letI : Module Q X := htor.module
      letI : IsScalarTower R Q X := htor.isScalarTower
      haveI : IsSimpleModule Q X :=
        (isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective
          (R := R) (S := Q) (M := X) Ideal.Quotient.mk_surjective).mp inferInstance
      let Y := ModuleCat.of Q X
      obtain ⟨e⟩ := hsimpleQ Y
      letI : Module R (Ext Y (ModuleCat.of Q Q) n) :=
        Module.compHom _ (Ideal.Quotient.mk (Ideal.span {x}))
      letI : IsScalarTower R Q (Ext Y (ModuleCat.of Q Q) n) :=
        IsScalarTower.of_compHom R Q _
      let f : X ≃ₗ[R]
          ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).obj Y) :=
        { toAddEquiv := AddEquiv.refl _
          map_smul' := fun r z => (algebraMap_smul Q r z).symm }
      exact ⟨(firstArgumentExtEquiv f (ModuleCat.of R R) (n + 1)).trans
        ((principalExtEquiv x hx Y n).symm.trans (e.restrictScalars R))⟩

/-- Specialize the uniform simple-module result to the residue field and
its canonical descended scalar structure. -/
lemma residue_profile (hG : LocalGorenstein R) :
    ringKrullDim R = (Depth.depthDegree R (ModuleCat.of R R) : WithBot ℕ∞) ∧
    HasInjectiveDimensionLE (ModuleCat.of R R) (Depth.depthDegree R (ModuleCat.of R R)) ∧
    Nonempty (Depth.ResidueExt (ModuleCat.of R R) (Depth.depthDegree R (ModuleCat.of R R))
      ≃ₗ[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R) := by
  obtain ⟨hdim, hb, hs⟩ := depth_profile (Depth.depthDegree R (ModuleCat.of R R))
    R hG (Depth.depth_finite R (ModuleCat.of R R)).2.symm
  haveI : IsSimpleModule R (IsLocalRing.ResidueField R) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp inferInstance)
  obtain ⟨e⟩ := hs (ModuleCat.of R (IsLocalRing.ResidueField R))
  exact ⟨hdim, hb, ⟨Depth.residueLinearEquiv R e⟩⟩

end AdvCommAlg.Gorenstein.ExtProfile

namespace AdvCommAlg.Gorenstein

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- GC-06: finite self-injective dimension implies Cohen–Macaulayness. -/
theorem localGorenstein_cohenMacaulay (hG : LocalGorenstein R) :
    CohenMacaulay.LocalCohenMacaulay R R := by
  have hdim := (ExtProfile.residue_profile hG).1
  apply (CohenMacaulay.localCohenMacaulay_self_iff R).mpr
  rw [← Depth.depth_eq_libraryDepth (ModuleCat.of R R),
    ← (Depth.depth_finite R (ModuleCat.of R R)).2, hdim]
  norm_cast

/-- GC-06: the self-injective dimension is exactly the Krull dimension. -/
theorem localGorenstein_injectiveDimension (hG : LocalGorenstein R) :
    injectiveDimension (ModuleCat.of R R) = ringKrullDim R := by
  obtain ⟨hdim, hb, ⟨e⟩⟩ := ExtProfile.residue_profile hG
  haveI := hb
  have hn : Nontrivial (Depth.ResidueExt (ModuleCat.of R R)
      (Depth.depthDegree R (ModuleCat.of R R))) := e.symm.injective.nontrivial
  have heq := (InjectiveDimensionTest.injectiveDimension_eq_iff_residue_ext R
    (ModuleCat.of R R) (Depth.depthDegree R (ModuleCat.of R R))).mpr
      ⟨hn, fun i hi => HasInjectiveDimensionLT.subsingleton (ModuleCat.of R R)
        (Depth.depthDegree R (ModuleCat.of R R) + 1) i hi
        (ModuleCat.of R (IsLocalRing.ResidueField R))⟩
  exact heq.trans hdim.symm

/-- GC-06: all residue-field Ext groups outside the dimension vanish. -/
theorem localGorenstein_ext_vanishing (hG : LocalGorenstein R)
    (d : ℕ) (hd : ringKrullDim R = (d : WithBot ℕ∞))
    (i : ℕ) (hi : i ≠ d) : Subsingleton (Depth.ResidueExt (ModuleCat.of R R) i) := by
  obtain ⟨hdim, hb, _⟩ := ExtProfile.residue_profile hG
  have hn : Depth.depthDegree R (ModuleCat.of R R) = d := by
    exact_mod_cast hdim.symm.trans hd
  rw [hn] at hb
  haveI : HasInjectiveDimensionLE (ModuleCat.of R R) d := hb
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · have hg : Depth.grade (Module.annihilator R (ModuleCat.of R (IsLocalRing.ResidueField R)))
        (ModuleCat.of R R) = (d : ℕ∞) := by
      change Depth.grade (Module.annihilator R (R ⧸ IsLocalRing.maximalIdeal R)) R = _
      rw [Ideal.annihilator_quotient]
      exact ((Depth.depth_finite R (ModuleCat.of R R)).2.symm).trans (congrArg _ hn)
    exact ((Depth.grade_eq_nat_iff (ModuleCat.of R (IsLocalRing.ResidueField R))
      (ModuleCat.of R R) d).mp hg).2 i hlt
  · exact HasInjectiveDimensionLT.subsingleton (ModuleCat.of R R) (d + 1) i hgt
      (ModuleCat.of R (IsLocalRing.ResidueField R))

/-- GC-06: top residue-field Ext is one copy of k, as a k-vector space. -/
theorem localGorenstein_ext_equiv (hG : LocalGorenstein R)
    (d : ℕ) (hd : ringKrullDim R = (d : WithBot ℕ∞)) :
    Nonempty (Depth.ResidueExt (ModuleCat.of R R) d ≃ₗ[IsLocalRing.ResidueField R]
      IsLocalRing.ResidueField R) := by
  obtain ⟨hdim, _, he⟩ := ExtProfile.residue_profile hG
  have hn : Depth.depthDegree R (ModuleCat.of R R) = d := by
    exact_mod_cast hdim.symm.trans hd
  exact hn ▸ he

/-- GC-06: a Gorenstein local ring has type one. -/
theorem localGorenstein_type_one (hG : LocalGorenstein R) : ringType R = 1 := by
  obtain ⟨_, _, ⟨e⟩⟩ := ExtProfile.residue_profile hG
  change Module.finrank (IsLocalRing.ResidueField R)
    (Depth.ResidueExt (ModuleCat.of R R) (Depth.depthDegree R (ModuleCat.of R R))) = 1
  simpa using e.finrank_eq

end AdvCommAlg.Gorenstein
