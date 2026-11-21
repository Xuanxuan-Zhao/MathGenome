import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.RegularFiniteProjectiveDimension
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.Syzygies
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.MaximalModulesOverRegularRings
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.AuslanderBuchsbaum

/-! CM-12: finite free resolutions over regular local rings.
The syzygies of a minimal finite free resolution form a tower to which the
CM syzygy bound applies. Its (dimension minus depth) syzygy is free (including
when it is zero), giving the projective dimension bound. Minimality then
makes every term above that bound vanish. Auslander–Buchsbaum gives equality
for the residue field, whose depth is zero.
-/

universe u
open CategoryTheory CategoryTheory.Abelian
namespace AdvCommAlg.CohenMacaulay

variable (R : Type u) [CommRing R] [IsRegularLocalRing R]

/-- The successive cokernels in an augmented minimal free resolution give
successive finite free surjections with their actual kernels. -/
private noncomputable def resolutionTower (M : ModuleCat.{u} R)
    (P : ProjectiveResolution M) (hP : IsMinimalFreeResolution P) :
    FiniteFreeSyzygies R where
  K := resolutionSyzygy P
  F := P.complex.X
  finiteK := minimalFreeResolution_syzygy_finite M P hP
  finiteF := hP.finite
  freeF := hP.free
  i n := (syzygyShortComplex P n).f
  p n := (syzygyShortComplex P n).g
  w n := (syzygyShortComplex P n).zero
  shortExact n := syzygyShortComplex_shortExact P n

/-- The sharper bound does not assume finite projective dimension. -/
theorem regularLocal_projectiveDimension_le_sub_depth (M : ModuleCat.{u} R)
    [Module.Finite R M] [Nontrivial M] (d e : ℕ)
    (hd : ringKrullDim R = (d : WithBot ℕ∞)) (he : Depth.depth R M = (e : ℕ∞)) :
    projectiveDimension M ≤ ((d - e : ℕ) : WithBot ℕ∞) := by
  obtain ⟨P, hP⟩ := exists_minimalFreeResolution M
  let T := resolutionTower R M P hP
  have hK0 : Nontrivial (T.K 0) := by
    exact (resolutionSyzygyZeroIso P).symm.toLinearEquiv.injective.nontrivial
  let := hK0
  letI : Module.Finite R (resolutionSyzygy P 0) := T.finiteK 0
  have he0 : Depth.depth R (T.K 0) = (e : ℕ∞) :=
    (Depth.depth_eq_of_iso (resolutionSyzygyZeroIso P)).trans he
  have hMCM := (syzygy_bound T d e (regularLocal_cohenMacaulay R) hd he0).2.2
  have hfree : Module.Free R (T.K (d - e)) := by
    cases subsingleton_or_nontrivial (T.K (d - e)) with
    | inl hz => let := hz; infer_instance
    | inr hn =>
      let := hn
      exact free_of_maximalCohenMacaulay R (T.K (d - e)) hMCM
  let := hfree
  have hp : Projective (resolutionSyzygy P (d - e)) := by
    change Projective (T.K (d - e))
    infer_instance
  have hlt : HasProjectiveDimensionLT (resolutionSyzygy P (d - e)) 1 :=
    projective_iff_hasProjectiveDimensionLT_one.mp hp
  exact (projectiveDimension_le_iff M (d - e)).mpr
    (hasProjectiveDimensionLT_of_syzygy M P (d - e) 1 hlt)

/-- An actual augmented finite free resolution, of length at most `d-e`. -/
theorem regularLocal_exists_finiteFreeResolution (M : ModuleCat.{u} R)
    [Module.Finite R M] [Nontrivial M] (d e : ℕ)
    (hd : ringKrullDim R = (d : WithBot ℕ∞)) (he : Depth.depth R M = (e : ℕ∞)) :
    ∃ P : ProjectiveResolution M,
      (∀ i, Module.Finite R (P.complex.X i)) ∧
      (∀ i, Module.Free R (P.complex.X i)) ∧
      (∀ i : ℕ, d - e < i → Subsingleton (P.complex.X i)) := by
  obtain ⟨P, hP⟩ := exists_minimalFreeResolution M
  exact ⟨P, hP.finite, hP.free, minimalFreeResolution_vanishes_above M P hP (d - e)
    (regularLocal_projectiveDimension_le_sub_depth R M d e hd he)⟩

/-- The uniform bound includes the zero module. -/
theorem regularLocal_projectiveDimension_le (M : ModuleCat.{u} R)
    [Module.Finite R M] (d : ℕ) (hd : ringKrullDim R = (d : WithBot ℕ∞)) :
    projectiveDimension M ≤ (d : WithBot ℕ∞) := by
  cases subsingleton_or_nontrivial M with
  | inl hz =>
    rw [(projectiveDimension_eq_bot_iff M).mpr (ModuleCat.isZero_iff_subsingleton.mpr hz)]
    exact bot_le
  | inr hn =>
    let := hn
    obtain ⟨e, he⟩ := Depth.exists_depth_eq_nat M
    exact (regularLocal_projectiveDimension_le_sub_depth R M d e hd he).trans
      (by exact_mod_cast Nat.sub_le d e)

/-- The residue field attains the dimension bound, also when `d=0`. -/
theorem regularLocal_residueField_projectiveDimension (d : ℕ)
    (hd : ringKrullDim R = (d : WithBot ℕ∞)) :
    projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) = (d : WithBot ℕ∞) := by
  let k := ModuleCat.of R (IsLocalRing.ResidueField R)
  have hb : projectiveDimension k ≤ (d : WithBot ℕ∞) :=
    regularLocal_projectiveDimension_le R k d hd
  have hne : projectiveDimension k ≠ ⊥ := by
    intro hz
    have : Subsingleton k := ModuleCat.subsingleton_of_isZero
      ((projectiveDimension_eq_bot_iff k).mp hz)
    exact not_subsingleton k this
  obtain ⟨p, hp⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← hp] at hb
  obtain ⟨n, hn, _⟩ := ENat.le_natCast_iff.mp (WithBot.coe_le_coe.mp hb)
  have hpd : projectiveDimension k = (n : WithBot ℕ∞) := by simpa [hn] using hp.symm
  have hk : Depth.depth R k = 0 := by
    rw [Depth.depth_eq_residueDepth]
    exact (ModuleCat.depth_eq_zero_iff_nontrivial_linearMap k k).mpr inferInstance
  have hAB := Depth.auslanderBuchsbaum k n hpd
  have hR := depth_self_eq_dimension d (regularLocal_cohenMacaulay R) hd
  rw [hk, add_zero, hR] at hAB
  have hnd : n = d := by exact_mod_cast hAB
  simpa only [hnd] using hpd

end AdvCommAlg.CohenMacaulay
