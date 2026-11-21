import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Homological.MinimalFreeResolution
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Homological.ExtProjectivityTest
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.LocalRing.Module

/-! Proof of paper.tex, Proposition DP-12 (3067–3107).
Lift residue-field bases to finite free covers and iterate on the kernels.
Minimality makes the tensor complex have zero differentials. For the finite
bound, a projective syzygy splits the next inclusion; reduction and Nakayama
force the next syzygy, and hence the corresponding free term, to vanish. -/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AdvCommAlg

theorem finite_projective_free {R : Type u} [CommRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] [Module.Projective R M] :
    Module.Free R M :=
  Module.free_of_flat_of_isLocalRing

section Covers

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Lifting a residue-field basis gives a finite free surjection with minimal kernel. -/
theorem exists_minimalFreeCover (M : ModuleCat.{u} R) [Module.Finite R M] :
    ∃ (F : ModuleCat.{u} R) (_ : Module.Finite R F) (_ : Module.Free R F)
      (f : F ⟶ M), Function.Surjective f.hom ∧
        LinearMap.ker f.hom ≤ IsLocalRing.maximalIdeal R • (⊤ : Submodule R F) := by
  classical
  let k := IsLocalRing.ResidueField R
  let b := Module.Free.chooseBasis k (k ⊗[R] M)
  obtain ⟨v, hv⟩ := (TensorProduct.mk_surjective R M k Ideal.Quotient.mk_surjective).comp_left b
  let ι := Module.Free.ChooseBasisIndex k (k ⊗[R] M)
  have : Finite ι := Module.Finite.finite_basis b
  let : Fintype ι := Fintype.ofFinite ι
  let f : (ι →₀ R) →ₗ[R] M := Finsupp.linearCombination R v
  have hs : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact IsLocalRing.span_eq_top_of_tmul_eq_basis v b (congr_fun hv)
  have hks : Function.Surjective (f.baseChange k) := f.lTensor_surjective k hs
  have hki : Function.Injective (f.baseChange k) := by
    rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero (R := k),
      ← Nat.add_right_inj (n := Module.finrank k (LinearMap.range (f.baseChange k))),
      LinearMap.finrank_range_add_finrank_ker,
      LinearMap.range_eq_top.mpr hks, finrank_top]
    simp only [Module.finrank_tensorProduct, Module.finrank_self,
      Module.finrank_finsupp_self, one_mul, add_zero]
    exact (Module.finrank_eq_card_basis b).symm
  refine ⟨ModuleCat.of R (ι →₀ R), inferInstance, inferInstance, ModuleCat.ofHom f, hs, ?_⟩
  intro x hx
  rw [← LinearMap.ker_tensorProductMk]
  change (1 : k) ⊗ₜ[R] x = 0
  apply hki
  simpa using congrArg (fun y : M => (1 : k) ⊗ₜ[R] y) hx

end Covers

section Construction

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

private structure FiniteModuleData (R : Type u) [CommRing R] where
  X : ModuleCat.{u} R
  finite : Module.Finite R X

attribute [instance] FiniteModuleData.finite

private structure FreeCoverData (M : ModuleCat.{u} R) where
  F : ModuleCat.{u} R
  finite : Module.Finite R F
  free : Module.Free R F
  π : F ⟶ M
  surjective : Function.Surjective π.hom
  minimal : LinearMap.ker π.hom ≤ IsLocalRing.maximalIdeal R • (⊤ : Submodule R F)

attribute [instance] FreeCoverData.finite FreeCoverData.free

private noncomputable def freeCover (M : ModuleCat.{u} R) [Module.Finite R M] :
    FreeCoverData M := Classical.choice (by
  obtain ⟨F, hfin, hfree, f, hs, hm⟩ := exists_minimalFreeCover M
  exact ⟨⟨F, hfin, hfree, f, hs, hm⟩⟩)

private noncomputable def minimalStage (M : ModuleCat.{u} R) [Module.Finite R M] :
    ℕ → FiniteModuleData R
  | 0 => ⟨M, inferInstance⟩
  | n + 1 => ⟨ModuleCat.of R (LinearMap.ker (freeCover (minimalStage M n).X).π.hom),
      inferInstance⟩

variable (M : ModuleCat.{u} R) [Module.Finite R M]

private noncomputable abbrev stageCover (n : ℕ) := freeCover (minimalStage M n).X

private noncomputable def minimalDifferential (n : ℕ) :
    (stageCover M (n + 1)).F ⟶ (stageCover M n).F :=
  (stageCover M (n + 1)).π ≫
    ModuleCat.ofHom (LinearMap.ker (stageCover M n).π.hom).subtype

private lemma minimalDifferential_comp (n : ℕ) :
    minimalDifferential M (n + 1) ≫ minimalDifferential M n = 0 := by
  have h : ModuleCat.ofHom (LinearMap.ker (stageCover M (n + 1)).π.hom).subtype ≫
      (stageCover M (n + 1)).π = 0 := by
    ext x
    exact x.property
  unfold minimalDifferential
  rw [Category.assoc, ← Category.assoc _ (stageCover M (n + 1)).π, h,
    zero_comp, comp_zero]

private noncomputable def minimalComplex : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (fun n => (stageCover M n).F) (minimalDifferential M)
    (minimalDifferential_comp M)

private lemma minimalComplex_d (n : ℕ) :
    (minimalComplex M).d (n + 1) n = minimalDifferential M n := by
  unfold minimalComplex
  exact ChainComplex.of_d (fun n => (stageCover M n).F) (minimalDifferential M) n

private lemma minimalDifferential_range (n : ℕ) :
    LinearMap.range (minimalDifferential M n).hom =
      LinearMap.ker (stageCover M n).π.hom := by
  change LinearMap.range ((LinearMap.ker (stageCover M n).π.hom).subtype.comp
    (stageCover M (n + 1)).π.hom) = _
  rw [LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (stageCover M (n + 1)).surjective), Submodule.range_subtype]

private lemma minimalComplex_exactAt (n : ℕ) : (minimalComplex M).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
  rw [minimalComplex_d M n, minimalComplex_d M (n + 1)]
  change LinearMap.range (minimalDifferential M (n + 1)).hom =
    LinearMap.ker (minimalDifferential M n).hom
  rw [minimalDifferential_range]
  change _ = LinearMap.ker ((LinearMap.ker (stageCover M n).π.hom).subtype.comp
    (stageCover M (n + 1)).π.hom)
  rw [LinearMap.ker_comp_of_ker_eq_bot _ (Submodule.ker_subtype _)]

private lemma minimalComplex_d_comp_augmentation :
    (minimalComplex M).d 1 0 ≫ (stageCover M 0).π = 0 := by
  rw [minimalComplex_d]
  simp only [minimalDifferential, Category.assoc]
  have h : ModuleCat.ofHom (LinearMap.ker (stageCover M 0).π.hom).subtype ≫
      (stageCover M 0).π = 0 := by
    ext x
    exact x.property
  rw [h, comp_zero]

private noncomputable def constructedResolution : ProjectiveResolution M where
  complex := minimalComplex M
  projective n := by
    change Projective (stageCover M n).F
    infer_instance
  π := (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨(stageCover M 0).π, minimalComplex_d_comp_augmentation M⟩
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · dsimp
        refine ⟨?_, ?_⟩
        · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
          change LinearMap.range ((minimalComplex M).d 1 0).hom =
            LinearMap.ker (stageCover M 0).π.hom
          rw [minimalComplex_d]
          exact minimalDifferential_range M 0
        · exact (ModuleCat.epi_iff_surjective _).mpr (stageCover M 0).surjective
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact minimalComplex_exactAt M n
      · exact ChainComplex.exactAt_succ_single_obj _ n⟩

theorem exists_minimalFreeResolution :
    ∃ P : ProjectiveResolution M, IsMinimalFreeResolution P := by
  refine ⟨constructedResolution M, ?_⟩
  refine ⟨fun i => (stageCover M i).finite, fun i => (stageCover M i).free, ?_⟩
  intro i
  change LinearMap.range ((minimalComplex M).d (i + 1) i).hom ≤ _
  rw [minimalComplex_d, minimalDifferential_range]
  exact (stageCover M i).minimal

end Construction

section Tensor

variable {R : Type u} [CommRing R] [IsLocalRing R]
    {M N : ModuleCat.{u} R}

lemma residueTensor_map_eq_zero (f : M ⟶ N)
    (hf : LinearMap.range f.hom ≤
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R N)) :
    ((tensoringLeft (ModuleCat.{u} R)).obj
      (ModuleCat.of R (IsLocalRing.ResidueField R))).map f = 0 := by
  apply ModuleCat.hom_ext
  change f.hom.lTensor (IsLocalRing.ResidueField R) = 0
  ext a m
  change a ⊗ₜ[R] f.hom m = 0
  have h : (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] f.hom m = 0 := by
    change f.hom m ∈ LinearMap.ker (TensorProduct.mk R
      (R ⧸ IsLocalRing.maximalIdeal R) N 1)
    rw [LinearMap.ker_tensorProductMk]
    exact hf ⟨m, rfl⟩
  rw [TensorProduct.tmul_eq_smul_one_tmul, h, smul_zero]

end Tensor

section Tor

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] (P : ProjectiveResolution M)
    (hP : IsMinimalFreeResolution P)

include hP

omit [IsNoetherianRing R] [Module.Finite R M] in
lemma minimalFreeResolution_tensor_d (i j : ℕ) :
    ((tensoringLeft (ModuleCat.{u} R)).obj
      (ModuleCat.of R (IsLocalRing.ResidueField R))).map (P.complex.d i j) = 0 := by
  by_cases hij : i = j + 1
  · subst i
    exact residueTensor_map_eq_zero _ (hP.minimal j)
  · rw [P.complex.shape i j (by simpa [eq_comm] using hij)]
    exact Functor.map_zero _ _ _

theorem minimalFreeResolution_torIso (i : ℕ) :
    Nonempty (ModuleCat.of R (IsLocalRing.ResidueField R ⊗[R] P.complex.X i) ≅
      ((CategoryTheory.Tor (ModuleCat.{u} R) i).obj
        (ModuleCat.of R (IsLocalRing.ResidueField R))).obj M) := by
  let F := (tensoringLeft (ModuleCat.{u} R)).obj
    (ModuleCat.of R (IsLocalRing.ResidueField R))
  let C := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  have hf : (C.sc i).f = 0 := minimalFreeResolution_tensor_d M P hP _ _
  have hg : (C.sc i).g = 0 := minimalFreeResolution_tensor_d M P hP _ _
  exact ⟨((ShortComplex.HomologyData.ofZeros (C.sc i) hf hg).left.homologyIso).symm ≪≫
    (P.isoLeftDerivedObj F i).symm⟩

end Tor

section Termination

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- A finite split submodule contained in the maximal ideal times its ambient
module vanishes: its reduction is both a zero map and a split injection. -/
lemma subsingleton_of_minimal_splitMono {T F : ModuleCat.{u} R} [Module.Finite R T]
    (f : T ⟶ F) (r : F ⟶ T) (hr : f ≫ r = 𝟙 T)
    (hf : LinearMap.range f.hom ≤ IsLocalRing.maximalIdeal R • (⊤ : Submodule R F)) :
    Subsingleton T := by
  let G := (tensoringLeft (ModuleCat.{u} R)).obj
    (ModuleCat.of R (IsLocalRing.ResidueField R))
  have hz : IsZero (G.obj T) := by
    rw [IsZero.iff_id_eq_zero]
    calc
      𝟙 (G.obj T) = G.map f ≫ G.map r := by rw [← G.map_comp, hr, G.map_id]
      _ = 0 := by rw [residueTensor_map_eq_zero f hf, zero_comp]
  exact (IsLocalRing.subsingleton_tensorProduct (R := R)).mp
    (ModuleCat.subsingleton_of_isZero hz)

variable (M : ModuleCat.{u} R) (P : ProjectiveResolution M)
    (hP : IsMinimalFreeResolution P)

include hP

lemma minimalFreeResolution_syzygy_finite (i : ℕ) :
    Module.Finite R (resolutionSyzygy P i) := by
  have := hP.finite i
  exact Module.Finite.of_surjective (P.complex.pOpcycles i).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

lemma minimalFreeResolution_syzygy_inclusion (i : ℕ) :
    LinearMap.range (P.complex.fromOpcycles (i + 1) i).hom ≤
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R (P.complex.X i)) := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, rfl⟩ := ((ModuleCat.epi_iff_surjective
    (P.complex.pOpcycles (i + 1))).mp inferInstance) x
  have h := congrArg (fun f => f.hom y) (P.complex.p_fromOpcycles (i + 1) i)
  change (P.complex.fromOpcycles (i + 1) i).hom
    ((P.complex.pOpcycles (i + 1)).hom y) ∈ _
  rw [show (P.complex.fromOpcycles (i + 1) i).hom
    ((P.complex.pOpcycles (i + 1)).hom y) = (P.complex.d (i + 1) i).hom y from h]
  exact hP.minimal i ⟨y, rfl⟩

lemma minimalFreeResolution_syzygy_succ_zero (i : ℕ)
    [Projective (resolutionSyzygy P i)] : Subsingleton (resolutionSyzygy P (i + 1)) := by
  have := minimalFreeResolution_syzygy_finite M P hP (i + 1)
  have : Projective (syzygyShortComplex P i).X₃ := by
    change Projective (resolutionSyzygy P i)
    infer_instance
  let s := (syzygyShortComplex_shortExact P i).splittingOfProjective
  exact subsingleton_of_minimal_splitMono (syzygyShortComplex P i).f s.r s.f_r
    (minimalFreeResolution_syzygy_inclusion M P hP i)

lemma minimalFreeResolution_term_zero_of_syzygy_zero (i : ℕ)
    (hi : Subsingleton (resolutionSyzygy P i)) : Subsingleton (P.complex.X i) := by
  have := hP.finite i
  have hz : IsZero (syzygyShortComplex P i).X₃ :=
    (ModuleCat.isZero_iff_subsingleton).mpr hi
  have : IsIso (syzygyShortComplex P i).f :=
    (syzygyShortComplex_shortExact P i).isIso_f_iff.mpr hz
  have hsurj := (ModuleCat.epi_iff_surjective (syzygyShortComplex P i).f).mp inferInstance
  have hrange : LinearMap.range (P.complex.fromOpcycles (i + 1) i).hom = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have htop : (⊤ : Submodule R (P.complex.X i)) ≤ IsLocalRing.maximalIdeal R • ⊤ := by
    exact hrange ▸ minimalFreeResolution_syzygy_inclusion M P hP i
  have hbot : (⊤ : Submodule R (P.complex.X i)) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ Module.Finite.fg_top htop
      (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top])
  exact subsingleton_of_forall_eq 0 (fun x => by
    have hx : x ∈ (⊤ : Submodule R (P.complex.X i)) := trivial
    rw [hbot] at hx
    exact hx)

lemma minimalFreeResolution_vanishes_above (e : ℕ)
    (he : projectiveDimension M ≤ (e : WithBot ℕ∞)) :
    ∀ i : ℕ, e < i → Subsingleton (P.complex.X i) := by
  intro i hi
  cases i with
  | zero => omega
  | succ b =>
    have hb : projectiveDimension M ≤ (b : WithBot ℕ∞) :=
      he.trans (by exact_mod_cast (show e ≤ b by omega))
    have hp : HasProjectiveDimensionLE M (b + 0) :=
      (projectiveDimension_le_iff M b).mp hb
    have : HasProjectiveDimensionLE (resolutionSyzygy P b) 0 :=
      syzygy_hasProjectiveDimensionLE P b 0 hp
    have : Projective (resolutionSyzygy P b) :=
      (projective_iff_hasProjectiveDimensionLE_zero _).mpr this
    exact minimalFreeResolution_term_zero_of_syzygy_zero M P hP (b + 1)
      (minimalFreeResolution_syzygy_succ_zero M P hP b)

omit hP [IsLocalRing R] in
/-- A bound on a syzygy gives the corresponding bound on the resolved module.
In particular a zero bth syzygy gives projective dimension strictly below b. -/
lemma hasProjectiveDimensionLT_of_syzygy (b n : ℕ)
    (h : HasProjectiveDimensionLT (resolutionSyzygy P b) n) :
    HasProjectiveDimensionLT M (b + n) := by
  induction b generalizing n with
  | zero =>
    have := h
    simpa only [Nat.zero_add] using
      hasProjectiveDimensionLT_of_iso (resolutionSyzygyZeroIso P) n
  | succ b ih =>
    have hp : Projective (syzygyShortComplex P b).X₂ := by
      dsimp [syzygyShortComplex]
      infer_instance
    have h₂ : HasProjectiveDimensionLT (syzygyShortComplex P b).X₂ (n + 1) :=
      hasProjectiveDimensionLT_of_ge _ 1 (n + 1) (by omega)
    have h' : HasProjectiveDimensionLT (resolutionSyzygy P b) (n + 1) :=
      (syzygyShortComplex_shortExact P b).hasProjectiveDimensionLT_X₃ n h h₂
    simpa only [Nat.succ_add, Nat.add_succ] using ih (n + 1) h'

lemma minimalFreeResolution_lastNonzero_of_projectiveDimension
    (e : ℕ) (he : projectiveDimension M = (e : WithBot ℕ∞)) :
    (∀ i : ℕ, e < i → Subsingleton (P.complex.X i)) ∧ Nontrivial (P.complex.X e) := by
  refine ⟨minimalFreeResolution_vanishes_above M P hP e he.le, ?_⟩
  by_contra h
  have hs : Subsingleton (P.complex.X e) := not_nontrivial_iff_subsingleton.mp h
  have hz : IsZero (resolutionSyzygy P e) :=
    IsZero.of_epi (P.complex.pOpcycles e) (ModuleCat.isZero_iff_subsingleton.mpr hs)
  have hp : HasProjectiveDimensionLT M e := by
    simpa only [Nat.add_zero] using
      hasProjectiveDimensionLT_of_syzygy M P e 0 hz.hasProjectiveDimensionLT_zero
  have hlt : projectiveDimension M < (e : WithBot ℕ∞) :=
    projectiveDimension_lt_iff.mpr hp
  rw [he] at hlt
  exact (lt_irrefl _ hlt)

end Termination

theorem minimalFreeResolution_lastNonzero :
    Specs.AdvCommAlg.minimalFreeResolution_lastNonzero := by
  intro R _ _ _ M _ _ P hP e he
  exact minimalFreeResolution_lastNonzero_of_projectiveDimension M P hP e he

end AdvCommAlg
