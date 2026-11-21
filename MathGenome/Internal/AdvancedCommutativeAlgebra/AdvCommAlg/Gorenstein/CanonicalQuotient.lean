import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.CanonicalQuotient
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.CohenMacaulayExtDual

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Abelian

namespace AdvCommAlg.Gorenstein.CanonicalQuotient
open ConcentratedChangeOfRings
variable {S R : Type u} [CommRing S] [CommRing R]
  [IsNoetherianRing S] [IsNoetherianRing R] [IsLocalRing S] [IsLocalRing R]
  [Algebra S R]

def sourceEquiv :
    ((ModuleCat.restrictScalars (algebraMap S R)).obj (ModuleCat.of R R)) ≃ₗ[S] R where
  toAddEquiv := AddEquiv.refl _
  map_smul' a m := by
    exact (@Algebra.smul_def S R _ _ _ a m).symm

instance source_nontrivial : Nontrivial
    ((ModuleCat.restrictScalars (algebraMap S R)).obj (ModuleCat.of R R)) :=
  (sourceEquiv (S := S) (R := R)).toEquiv.nontrivial

lemma source_finite (hf : Function.Surjective (algebraMap S R)) :
    Module.Finite S ((ModuleCat.restrictScalars (algebraMap S R)).obj
      (ModuleCat.of R R)) := by
  haveI : Module.Finite S R := CohenMacaulay.finite_restrictScalars_of_surjective R hf
  exact Module.Finite.equiv (sourceEquiv (S := S) (R := R)).symm

lemma source_cm (hf : Function.Surjective (algebraMap S R))
    (hR : CohenMacaulay.LocalCohenMacaulay R R) :
    letI := source_finite hf
    CohenMacaulay.LocalCohenMacaulay S
      ((ModuleCat.restrictScalars (algebraMap S R)).obj (ModuleCat.of R R)) := by
  haveI := source_finite hf
  haveI : Module.Finite S R := CohenMacaulay.finite_restrictScalars_of_surjective R hf
  exact CMExtDual.localCM_of_equiv sourceEquiv
    ((CohenMacaulay.localCohenMacaulay_of_surjective_iff R hf).mpr hR)

lemma source_dimension (hf : Function.Surjective (algebraMap S R)) :
    Module.supportDim S
      ((ModuleCat.restrictScalars (algebraMap S R)).obj (ModuleCat.of R R)) =
        ringKrullDim R := by
  haveI := source_finite hf
  haveI : Module.Finite S R := CohenMacaulay.finite_restrictScalars_of_surjective R hf
  exact (Module.supportDim_eq_of_equiv (sourceEquiv (S := S) (R := R))).trans
    ((CohenMacaulay.dimension_of_surjective R hf).trans
      (Module.supportDim_self_eq_ringKrullDim R))

lemma concentration (hf : Function.Surjective (algebraMap S R))
    (hG : LocalGorenstein S) (hR : CohenMacaulay.LocalCohenMacaulay R R)
    (s d : ℕ) (hs : ringKrullDim S = (s : WithBot ℕ∞))
    (hd : ringKrullDim R = (d : WithBot ℕ∞)) :
    Concentrated (algebraMap S R) (ModuleCat.of S S) (s - d) := by
  haveI := source_finite hf
  exact cohenMacaulay_ext_vanishing S hG _ (source_cm hf hR) s d hs
    ((source_dimension hf).trans hd)

/-- The new target action restricts to the ordinary source action on Ext. -/
def baseEquiv (M : ModuleCat.{u} R) (n : ℕ) :
    letI : Module S (FirstExt (algebraMap S R) M (ModuleCat.of S S) n) :=
      Module.compHom _ (algebraMap S R)
    FirstExt (algebraMap S R) M (ModuleCat.of S S) n ≃ₗ[S]
      Ext ((ModuleCat.restrictScalars (algebraMap S R)).obj M) (ModuleCat.of S S) n := by
  letI : Module S (FirstExt (algebraMap S R) M (ModuleCat.of S S) n) :=
    Module.compHom _ (algebraMap S R)
  exact
    { toAddEquiv := firstExtAddEquiv _ _ _ _
      map_smul' := fun a x => firstExt_smul_of_base _ _ _ _ a x }

/-- Finiteness and the maximal CM property descend with the prescribed action. -/
lemma omega_cm (hf : Function.Surjective (algebraMap S R))
    (hG : LocalGorenstein S) (hR : CohenMacaulay.LocalCohenMacaulay R R)
    (s d : ℕ) (hs : ringKrullDim S = (s : WithBot ℕ∞))
    (hd : ringKrullDim R = (d : WithBot ℕ∞)) :
    ∃ hfin : Module.Finite R (omega S R s d),
      letI := hfin
      Nontrivial (omega S R s d) ∧
        CohenMacaulay.MaximalCohenMacaulay R (omega S R s d) := by
  haveI := source_finite hf
  let W := omega S R s d
  letI : Module S W := Module.compHom _ (algebraMap S R)
  letI : IsScalarTower S R W := IsScalarTower.of_compHom S R W
  let e : W ≃ₗ[S] Ext
      ((ModuleCat.restrictScalars (algebraMap S R)).obj (ModuleCat.of R R))
      (ModuleCat.of S S) (s - d) := baseEquiv (S := S) (ModuleCat.of R R) (s - d)
  obtain ⟨_, hfin, hnt, hCM, hdim⟩ := cohenMacaulay_ext_dual S hG _
    (source_cm hf hR) s d hs ((source_dimension hf).trans hd)
  haveI := hfin
  haveI := hnt
  haveI : Module.Finite S W := Module.Finite.equiv e.symm
  haveI : Nontrivial W := e.toEquiv.nontrivial
  haveI : Module.Finite R W := Module.Finite.of_restrictScalars_finite S R W
  have hCMW : CohenMacaulay.LocalCohenMacaulay S W :=
    CMExtDual.localCM_of_equiv e hCM
  have hdepth : (Depth.depth R W : WithBot ℕ∞) = ringKrullDim R := by
    rw [← CohenMacaulay.depth_of_surjective W hf]
    exact ((CohenMacaulay.localCohenMacaulay_iff_sourceDepth S W).mp hCMW).trans
      ((Module.supportDim_eq_of_equiv e).trans (hdim.trans hd.symm))
  exact ⟨inferInstance, inferInstance,
    (CohenMacaulay.maximalCohenMacaulay_iff_sourceDepth R W).mpr hdepth⟩

/-- The residue field of R remains simple over a surjective source ring. -/
lemma residue_simple (hf : Function.Surjective (algebraMap S R)) :
    IsSimpleModule S ((ModuleCat.restrictScalars (algebraMap S R)).obj
      (ModuleCat.of R (IsLocalRing.ResidueField R))) := by
  let X := (ModuleCat.restrictScalars (algebraMap S R)).obj
    (ModuleCat.of R (IsLocalRing.ResidueField R))
  letI : IsScalarTower S R X := IsScalarTower.of_compHom S R X
  haveI : IsSimpleModule R X :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp inferInstance)
  exact (isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective
    (R := S) (S := R) (M := X) hf).mpr inferInstance

/-- The Gorenstein Ext profile applies to the target residue field over S. -/
lemma residue_source_vanishing (hf : Function.Surjective (algebraMap S R))
    (hG : LocalGorenstein S) (s : ℕ) (hs : ringKrullDim S = (s : WithBot ℕ∞))
    (j : ℕ) (hj : j ≠ s) :
    Subsingleton (Ext ((ModuleCat.restrictScalars (algebraMap S R)).obj
      (ModuleCat.of R (IsLocalRing.ResidueField R))) (ModuleCat.of S S) j) := by
  haveI := residue_simple hf
  obtain ⟨e⟩ := simpleModule_residue_equiv (R := S)
    ((ModuleCat.restrictScalars (algebraMap S R)).obj
      (ModuleCat.of R (IsLocalRing.ResidueField R)))
  haveI := localGorenstein_ext_vanishing S hG s hs j hj
  exact (ExtProfile.firstArgumentExtEquiv
    (B := ModuleCat.of S (IsLocalRing.ResidueField S)) e
    (ModuleCat.of S S) j).injective.subsingleton

lemma residue_vanishing (hf : Function.Surjective (algebraMap S R))
    (hG : LocalGorenstein S) (hR : CohenMacaulay.LocalCohenMacaulay R R)
    (s d : ℕ) (hs : ringKrullDim S = (s : WithBot ℕ∞))
    (hd : ringKrullDim R = (d : WithBot ℕ∞)) (hds : d ≤ s)
    (i : ℕ) (hi : i ≠ d) : Subsingleton (Depth.ResidueExt (omega S R s d) i) := by
  obtain ⟨e⟩ := comparison S R (algebraMap S R) (ModuleCat.of S S) (s - d)
    (concentration hf hG hR s d hs hd) i
  let f : Depth.ResidueExt (omega S R s d) i ≃ₗ[R]
      FirstExt (algebraMap S R) (ModuleCat.of R (IsLocalRing.ResidueField R))
        (ModuleCat.of S S) (i + (s - d)) :=
    (e.app (Opposite.op (ModuleCat.of R (IsLocalRing.ResidueField R)))).toLinearEquiv
  haveI := residue_source_vanishing hf hG s hs (i + (s - d)) (by omega)
  haveI : Subsingleton (FirstExt (algebraMap S R)
      (ModuleCat.of R (IsLocalRing.ResidueField R)) (ModuleCat.of S S) (i + (s - d))) :=
    (firstExtAddEquiv _ _ _ _).injective.subsingleton
  exact f.injective.subsingleton

lemma residue_equiv (hf : Function.Surjective (algebraMap S R))
    (hG : LocalGorenstein S) (hR : CohenMacaulay.LocalCohenMacaulay R R)
    (s d : ℕ) (hs : ringKrullDim S = (s : WithBot ℕ∞))
    (hd : ringKrullDim R = (d : WithBot ℕ∞)) (hds : d ≤ s) :
    Nonempty (Depth.ResidueExt (omega S R s d) d ≃ₗ[IsLocalRing.ResidueField R]
      IsLocalRing.ResidueField R) := by
  let X := (ModuleCat.restrictScalars (algebraMap S R)).obj
    (ModuleCat.of R (IsLocalRing.ResidueField R))
  haveI := residue_simple hf
  have hdepth : Depth.depth S S = (s : ℕ∞) := by
    have h := (CohenMacaulay.localCohenMacaulay_iff_sourceDepth S S).mp
      (localGorenstein_cohenMacaulay S hG)
    rw [CohenMacaulay.dimension, Module.supportDim_self_eq_ringKrullDim, hs] at h
    exact_mod_cast h
  obtain ⟨g⟩ := (ExtProfile.depth_profile s S hG hdepth).2.2 X
  have hshift : d + (s - d) = s := by omega
  obtain ⟨e⟩ := comparison S R (algebraMap S R) (ModuleCat.of S S) (s - d)
    (concentration hf hG hR s d hs hd) d
  let f := (e.app (Opposite.op (ModuleCat.of R (IsLocalRing.ResidueField R)))).toLinearEquiv
  have ht : Nonempty (FirstExt (algebraMap S R)
      (ModuleCat.of R (IsLocalRing.ResidueField R)) (ModuleCat.of S S)
      (d + (s - d)) ≃ₗ[R] IsLocalRing.ResidueField R) := by
    rw [hshift]
    letI : Module S (FirstExt (algebraMap S R)
        (ModuleCat.of R (IsLocalRing.ResidueField R)) (ModuleCat.of S S) s) :=
      Module.compHom _ (algebraMap S R)
    let a := (baseEquiv (S := S) (ModuleCat.of R (IsLocalRing.ResidueField R)) s).trans g
    refine ⟨{ toAddEquiv := a.toAddEquiv, map_smul' := ?_ }⟩
    intro r z
    obtain ⟨t, rfl⟩ := hf r
    exact a.map_smul t z
  obtain ⟨t⟩ := ht
  exact ⟨Depth.residueLinearEquiv R (f.trans t)⟩

end AdvCommAlg.Gorenstein.CanonicalQuotient

namespace AdvCommAlg.Gorenstein
open CanonicalQuotient ConcentratedChangeOfRings

theorem canonicalQuotient_dimension_le : CanonicalQuotientSpecs.dimensionLeType.{u} := by
  intro S R _ _ _ _ _ _ _ hf hG hR s d hs hd
  haveI := source_finite hf
  exact cohenMacaulay_dimension_le S hG _ (source_cm hf hR) s d hs
    ((source_dimension hf).trans hd)

theorem canonicalQuotient_comparison : CanonicalQuotientSpecs.comparisonType.{u} := by
  intro S R _ _ _ _ _ _ _ hf hG hR s d hs hd i
  exact comparison S R (algebraMap S R) (ModuleCat.of S S) (s - d)
    (concentration hf hG hR s d hs hd) i

theorem canonicalQuotient_properties : CanonicalQuotientSpecs.propertiesType.{u} := by
  intro S R _ _ _ _ _ _ _ hf hG hR s d hs hd
  have hds := canonicalQuotient_dimension_le S R hf hG hR s d hs hd
  obtain ⟨hfin, hnt, hmcm⟩ := omega_cm hf hG hR s d hs hd
  haveI := hfin
  haveI := hnt
  have hv := residue_vanishing hf hG hR s d hs hd hds
  obtain ⟨e⟩ := residue_equiv hf hG hR s d hs hd hds
  haveI : Nontrivial (Depth.ResidueExt (omega S R s d) d) := e.toEquiv.nontrivial
  have hinj : injectiveDimension (omega S R s d) = (d : WithBot ℕ∞) :=
    (InjectiveDimensionTest.injectiveDimension_eq_iff_residue_ext R
      (omega S R s d) d).mpr ⟨inferInstance, fun i hi => hv i (by omega)⟩
  have hfinite : FiniteInjectiveDimension R (omega S R s d) := by
    change injectiveDimension (omega S R s d) ≠ ⊤
    rw [hinj]
    exact fun h => ENat.natCast_ne_top d (WithBot.coe_injective h)
  have hdegree : Depth.depthDegree R (omega S R s d) = d := by
    have hdep := (CohenMacaulay.maximalCohenMacaulay_iff_sourceDepth R
      (omega S R s d)).mp hmcm
    rw [hd, ← (Depth.depth_finite R (omega S R s d)).2] at hdep
    exact_mod_cast hdep
  have htype : Depth.moduleType R (omega S R s d) = 1 := by
    unfold Depth.moduleType
    rw [hdegree]
    simpa using e.finrank_eq
  exact ⟨hfin, ⟨hR, hnt, hmcm, htype, hfinite⟩, hinj, hv, ⟨e⟩⟩

end AdvCommAlg.Gorenstein
