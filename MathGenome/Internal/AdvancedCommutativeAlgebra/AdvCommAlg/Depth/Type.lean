import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.FirstSurvivingExt
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.Type
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! Type and the socle comparison (DP-05). The finite-dimensionality proof
uses the first-surviving-Ext comparison and the finite quotient socle. -/
universe u
open CategoryTheory CategoryTheory.Abelian
open scoped Pointwise
namespace AdvCommAlg.Depth

noncomputable def depthDegree (R : Type u) [CommRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) : ℕ := (depth R M).toNat

noncomputable def moduleType (R : Type u) [CommRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) : ℕ :=
  Module.finrank (IsLocalRing.ResidueField R) (ResidueExt M (depthDegree R M))

variable (R : Type u) [CommRing R] [IsLocalRing R]

lemma maximalIdeal_smul_ne_top (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M] :
    IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
  (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
    (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator R M))).symm

lemma exists_maximalRegular [IsNoetherianRing R] (M : ModuleCat.{u} R)
    [Module.Finite R M] [Nontrivial M] :
    ∃ xs : List R, MaximalRegular (IsLocalRing.maximalIdeal R) M xs := by
  simpa using exists_maximalRegular_extension (IsLocalRing.maximalIdeal R) M
    (maximalIdeal_smul_ne_top R M) [] (RingTheory.Sequence.IsRegular.nil R M) (by simp)

theorem depth_finite [IsNoetherianRing R] (M : ModuleCat.{u} R)
    [Module.Finite R M] [Nontrivial M] :
    depth R M ≠ ⊤ ∧ (depthDegree R M : ℕ∞) = depth R M := by
  obtain ⟨xs, hxs⟩ := exists_maximalRegular R M
  have hlen := maximalRegular_length_eq_grade _ M (maximalIdeal_smul_ne_top R M) xs hxs
  have hfin : depth R M ≠ ⊤ := by
    rw [depth_eq_grade, ← hlen]
    simp
  exact ⟨hfin, ENat.natCast_toNat hfin⟩

theorem maximalRegular_length_eq_depthDegree [IsNoetherianRing R] (M : ModuleCat.{u} R)
    [Module.Finite R M] [Nontrivial M] (xs : List R)
    (hxs : MaximalRegular (IsLocalRing.maximalIdeal R) M xs) :
    xs.length = depthDegree R M := by
  have hlen := maximalRegular_length_eq_grade _ M (maximalIdeal_smul_ne_top R M) xs hxs
  have ht := congrArg ENat.toNat hlen
  simpa [depthDegree, depth_eq_grade] using ht

/-- An R-linear equivalence between descended residue-field modules is k-linear. -/
def residueLinearEquiv {U V : Type u} [AddCommGroup U] [AddCommGroup V]
    [Module R U] [Module R V]
    [Module (IsLocalRing.ResidueField R) U] [Module (IsLocalRing.ResidueField R) V]
    [IsScalarTower R (IsLocalRing.ResidueField R) U]
    [IsScalarTower R (IsLocalRing.ResidueField R) V] (e : U ≃ₗ[R] V) :
    U ≃ₗ[IsLocalRing.ResidueField R] V :=
  { e.toAddEquiv with
    map_smul' := by
      intro a x
      obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective (R := R) a
      change e ((algebraMap R (IsLocalRing.ResidueField R) r) • x) =
        (algebraMap R (IsLocalRing.ResidueField R) r) • e x
      simp only [algebraMap_smul, e.map_smul] }

/-- Evaluation at 1 takes a map from k to the maximal-ideal annihilator. -/
noncomputable def socleEvaluation (U : Type u) [AddCommGroup U] [Module R U] :
    ResidueHom R U →ₗ[IsLocalRing.ResidueField R] Socle R U where
  toFun f := ⟨f 1, (Submodule.mem_torsionBySet_iff _ _).mpr (by
    intro a
    rw [← f.map_smul]
    have hz : a.val • (1 : IsLocalRing.ResidueField R) = 0 := by
      change IsLocalRing.residue R a.val * 1 = 0
      rw [(IsLocalRing.residue_eq_zero_iff _).mpr a.property, zero_mul]
    rw [hz, f.map_zero])⟩
  map_add' _ _ := rfl
  map_smul' := by
    intro a f
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective (R := R) a
    apply Subtype.ext
    rfl

lemma socleEvaluation_bijective (U : Type u) [AddCommGroup U] [Module R U] :
    Function.Bijective (socleEvaluation R U) := by
  constructor
  · intro f g h
    have he : f 1 = g 1 := congrArg Subtype.val h
    ext z
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective (R := R) z
    have hr : IsLocalRing.residue R r = r • (1 : IsLocalRing.ResidueField R) := by
      change IsLocalRing.residue R r = IsLocalRing.residue R r * 1
      simp
    rw [hr, f.map_smul, g.map_smul, he]
  · intro y
    let f : IsLocalRing.ResidueField R →ₗ[R] U :=
      (IsLocalRing.maximalIdeal R).liftQ (LinearMap.toSpanSingleton R U y.val) (by
        intro r hr
        exact (Submodule.mem_torsionBySet_iff _ _).mp y.property ⟨r, hr⟩)
    refine ⟨f, ?_⟩
    apply Subtype.ext
    change (1 : R) • y.val = y.val
    exact one_smul R y.val

theorem homSocleEquiv (U : Type u) [AddCommGroup U] [Module R U] :
    ∃ e : ResidueHom R U ≃ₗ[IsLocalRing.ResidueField R] Socle R U,
      ∀ f, (e f).val = f 1 := by
  exact ⟨LinearEquiv.ofBijective (socleEvaluation R U) (socleEvaluation_bijective R U),
    fun _ => rfl⟩

theorem typeComparison [IsNoetherianRing R] (M : ModuleCat.{u} R)
    [Module.Finite R M] [Nontrivial M] (xs : List R)
    (hxs : MaximalRegular (IsLocalRing.maximalIdeal R) M xs) :
    ∃ e : ResidueExt M (depthDegree R M) ≃ₗ[IsLocalRing.ResidueField R]
      ResidueHom R (FirstSurvivingExt.Quotient M xs),
    ∃ s : ResidueHom R (FirstSurvivingExt.Quotient M xs) ≃ₗ[IsLocalRing.ResidueField R]
      Socle R (FirstSurvivingExt.Quotient M xs), ∀ f, (s f).val = f 1 := by
  have hlen := maximalRegular_length_eq_depthDegree R M xs hxs
  obtain ⟨e, _⟩ := FirstSurvivingExt.comparison
    (ModuleCat.of R (IsLocalRing.ResidueField R)) M xs hxs.1 (by
      intro a ha
      rw [show Module.annihilator R (ModuleCat.of R (IsLocalRing.ResidueField R)) =
        IsLocalRing.maximalIdeal R from Ideal.annihilator_quotient]
      exact hxs.2.1 a ha)
  have e' : ResidueExt M (depthDegree R M) ≃ₗ[R]
      ResidueHom R (FirstSurvivingExt.Quotient M xs) := hlen ▸ e
  exact ⟨residueLinearEquiv R e', homSocleEquiv R _⟩

lemma socle_finite [IsNoetherianRing R] (U : Type u) [AddCommGroup U] [Module R U]
    [Module.Finite R U] : FiniteDimensional (IsLocalRing.ResidueField R) (Socle R U) := by
  have : Module.Finite R (Socle R U) := inferInstance
  exact Module.Finite.of_restrictScalars_finite R _ _

theorem typeExt_finite [IsNoetherianRing R] (M : ModuleCat.{u} R)
    [Module.Finite R M] [Nontrivial M] :
    FiniteDimensional (IsLocalRing.ResidueField R) (ResidueExt M (depthDegree R M)) := by
  obtain ⟨xs, hxs⟩ := exists_maximalRegular R M
  obtain ⟨e, s, _⟩ := typeComparison R M xs hxs
  have := socle_finite R (FirstSurvivingExt.Quotient M xs)
  exact Module.Finite.equiv (e.trans s).symm

theorem moduleType_eq_socle [IsNoetherianRing R] (M : ModuleCat.{u} R)
    [Module.Finite R M] [Nontrivial M] (xs : List R)
    (hxs : MaximalRegular (IsLocalRing.maximalIdeal R) M xs) :
    moduleType R M = Module.finrank (IsLocalRing.ResidueField R)
      (Socle R (FirstSurvivingExt.Quotient M xs)) := by
  obtain ⟨e, s, _⟩ := typeComparison R M xs hxs
  exact (e.trans s).finrank_eq

theorem socle_dimension_independent [IsNoetherianRing R] (M : ModuleCat.{u} R)
    [Module.Finite R M] [Nontrivial M] (xs ys : List R)
    (hxs : MaximalRegular (IsLocalRing.maximalIdeal R) M xs)
    (hys : MaximalRegular (IsLocalRing.maximalIdeal R) M ys) :
    Module.finrank (IsLocalRing.ResidueField R) (Socle R (FirstSurvivingExt.Quotient M xs)) =
    Module.finrank (IsLocalRing.ResidueField R) (Socle R (FirstSurvivingExt.Quotient M ys)) :=
  (moduleType_eq_socle R M xs hxs).symm.trans (moduleType_eq_socle R M ys hys)

end AdvCommAlg.Depth
