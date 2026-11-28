import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Invariants.FiniteAveraging
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Invariants.CanonicalProjection
import MathGenome.Internal.AlgebraCore.P103.Ch08.Maschke

open scoped BigOperators MonoidAlgebra

universe u v w z t

namespace RepTheorySurvey.Invariants.GroupRepresentation

/-- The averaging endomorphism of a representation of a finite group. -/
noncomputable abbrev finiteAverage := @Specs.finiteAverage

theorem finiteAverage_apply {k : Type u} {G : Type v} {V : Type w}
    [Field k] [Group G] [Fintype G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (x : V) :
    finiteAverage ρ x = (Fintype.card G : k)⁻¹ • ∑ g : G, ρ g x := by
  let s := @Finset.univ G (Fintype.ofFinite G)
  have hs : s = Finset.univ := Finset.eq_univ_of_forall (fun g ↦
    @Finset.mem_univ G (Fintype.ofFinite G) g)
  change ((Nat.card G : k)⁻¹ • ∑ g ∈ s, ρ g) x = _
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, hs, Fintype.card_eq_nat_card]

theorem finiteAverage_natural {k : Type u} {G : Type v} {V : Type w} {W : Type z}
    [Field k] [Group G] [Finite G] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    (ρ : Representation k G V) (σ : Representation k G W)
    (f : V →ₗ[k] W) (hf : ρ.IsIntertwiningMap σ f) (x : V) :
    finiteAverage σ (f x) = f (finiteAverage ρ x) := by
  let : Fintype G := Fintype.ofFinite G
  rw [finiteAverage_apply σ, finiteAverage_apply ρ, map_smul, map_sum]
  exact congrArg _ (Finset.sum_congr rfl fun g _ ↦ (hf.isIntertwining g x).symm)

theorem finiteAverage_isProj {k : Type u} {G : Type v} {V : Type w}
    [Field k] [Group G] [Finite G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (hcard : (Nat.card G : k) ≠ 0) :
    LinearMap.IsProj ρ.invariants (finiteAverage ρ) := by
  let : Fintype G := Fintype.ofFinite G
  let : Invertible (Fintype.card G : k) :=
    invertibleOfNonzero (by simpa only [Fintype.card_eq_nat_card] using hcard)
  have heq : finiteAverage ρ = ρ.averageMap := by
    ext x
    rw [finiteAverage_apply ρ]
    simp [GroupAlgebra.average, map_sum, invOf_eq_inv]
  rw [heq]
  exact ρ.isProj_averageMap

theorem finiteGroup_linearlyReductive : Specs.FiniteGroupLinearlyReductive.{u,v,w} := by
  intro k G _ _ _ hcard V _ _ _ ρ
  let _ := P103.Ch08.Maschke.semisimple ρ hcard
  let R := MonoidAlgebra k G
  -- The independent family from Maschke remains independent over the ground field.
  obtain ⟨s, hind, hsup, hsimple⟩ :=
    IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top R ρ.asModule
  let pieces : s → Submodule R ρ.asModule := Subtype.val
  have hpieces : iSupIndep pieces := (sSupIndep_iff s).mp hind
  let E := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  let parts : s → Subrepresentation ρ := fun i ↦ E.symm (pieces i)
  have hatom (i : s) : IsAtom (parts i) :=
    (E.symm.isAtom_iff _).mpr (isSimpleModule_iff_isAtom.mp (hsimple i i.property))
  have hpartInd : iSupIndep (fun i ↦ (parts i).toSubmodule) := by
    change iSupIndep (fun i ↦ (pieces i).restrictScalars k)
    intro i
    simp_rw [← Submodule.restrictScalars_iSup]
    exact (Submodule.disjoint_restrictScalars_iff k).mpr (hpieces i)
  have hpartSup : ⨆ i, (parts i).toSubmodule = ⊤ := by
    change (⨆ i, (pieces i).restrictScalars k) = ⊤
    rw [← Submodule.restrictScalars_iSup, Submodule.restrictScalars_eq_top_iff]
    exact (sSup_eq_iSup' s).symm.trans hsup
  have : Finite s := WellFoundedGT.finite_of_iSupIndep hpartInd fun i h ↦
    (hatom i).1 (Subrepresentation.toSubmodule_injective h)
  let e := Finite.equivFin s
  refine ⟨_, parts ∘ e.symm, fun i ↦ hatom (e.symm i),
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_⟩
  · exact hpartInd.comp e.symm.injective
  · exact (e.symm.surjective.iSup_comp (fun i ↦ (parts i).toSubmodule)).trans hpartSup

theorem finiteAverage_canonical : Specs.FiniteAverageCanonical.{u,v,w} := by
  intro k G V _ _ _ _ _ ρ hcard
  have hred : LinearlyReductive.{u,v,w} k G := finiteGroup_linearlyReductive hcard
  have havg := finiteAverage_isProj ρ hcard
  obtain ⟨P, hP, huniq⟩ := canonicalProjection hred ρ (locallyFinite_of_finite ρ)
  refine ⟨P, ?_, hP, huniq⟩
  intro x
  -- The target action is trivial, so averaging there fixes every vector.
  have hnat := finiteAverage_natural ρ (Representation.trivial k G ρ.invariants) P hP.1 x
  have hfix : finiteAverage (Representation.trivial k G ρ.invariants) (P x) = P x :=
    (finiteAverage_isProj _ hcard).2 _ (by intro g; rfl)
  let y : ρ.invariants := ⟨finiteAverage ρ x, havg.1 x⟩
  have heq : P x = P (y : V) := hfix.symm.trans hnat
  rw [heq, hP.2.1]

theorem finiteInvariants_exact : Specs.FiniteInvariantsExact.{u,v,w,z,t} := by
  intro k G U V W _ _ _ _ _ _ _ _ _ hcard τ ρ σ f g hf hg
  refine ⟨?_, ?_, ?_⟩
  · intro hex y
    constructor
    · intro hy
      have hy' : g (y : V) = 0 := congrArg Subtype.val hy
      obtain ⟨x, hx⟩ := (hex (y : V)).mp hy'
      refine ⟨⟨finiteAverage τ x, (finiteAverage_isProj τ hcard).1 x⟩, Subtype.ext ?_⟩
      change f (finiteAverage τ x) = (y : V)
      rw [← finiteAverage_natural τ ρ f hf, hx]
      exact (finiteAverage_isProj ρ hcard).2 _ y.property
    · rintro ⟨x, rfl⟩
      exact Subtype.ext (hex.apply_apply_eq_zero (x : U))
  · intro hinj x y h
    exact Subtype.ext (hinj (congrArg Subtype.val h))
  · intro hsurj y
    obtain ⟨x, hx⟩ := hsurj (y : W)
    refine ⟨⟨finiteAverage ρ x, (finiteAverage_isProj ρ hcard).1 x⟩, Subtype.ext ?_⟩
    change g (finiteAverage ρ x) = (y : W)
    rw [← finiteAverage_natural ρ σ g hg, hx]
    exact (finiteAverage_isProj σ hcard).2 _ y.property

theorem finiteAverage_reynolds : Specs.FiniteAverageReynolds.{u,v,w} := by
  intro k G A _ _ _ _ _ ρ hcard
  have hred : LinearlyReductive.{u,v,w} k G := finiteGroup_linearlyReductive hcard
  obtain ⟨R, hformula, hR, _⟩ := finiteAverage_canonical (GroupAlgebraAction.toRepresentation ρ) hcard
  exact ⟨R, canonicalProjection_reynolds hred ρ (locallyFinite_of_finite _) R hR, hformula⟩

theorem finiteAverage_preservesGrading : Specs.FiniteAveragePreservesGrading.{u,v,w,z} := by
  intro k G V ι _ _ _ _ _ ρ grade hgrade i x hx
  let : Fintype G := Fintype.ofFinite G
  rw [finiteAverage_apply]
  exact (grade i).smul_mem _ ((grade i).sum_mem fun g _ ↦ hgrade g i x hx)

end RepTheorySurvey.Invariants.GroupRepresentation
