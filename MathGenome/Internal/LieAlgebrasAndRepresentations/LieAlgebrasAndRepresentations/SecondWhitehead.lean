import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SecondWhitehead
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CompleteReducibility
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SecondWhiteheadTrivial
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.AbelianExtensions

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
universe u v w w' z
namespace LieAlgebrasAndRepresentations.SecondWhitehead
open AdvancedHomologicalAlgebra.CE
open LieModule.Cohomology AbelianExtensions SimpleCoefficientVanishing
open P103.Specs.Ch10.Complexes
variable (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g]
variable (M : Type w) [AddCommGroup M] [Module k M]
  [LieRingModule g M] [LieModule k g M]

/-- Push a two-cochain along a linear coefficient map. -/
def mapTwo {N : Type w'} [AddCommGroup N] [Module k N]
    (f : M →ₗ[k] N) (c : twoCochain k g M) : twoCochain k g N :=
  ⟨{ toFun := fun x => f.comp (c x)
     map_add' := by intro x y; ext z; simp
     map_smul' := by intro r x; ext z; simp }, by intro x; simp⟩

@[simp] lemma mapTwo_apply {N : Type w'} [AddCommGroup N] [Module k N]
    (f : M →ₗ[k] N) (c : twoCochain k g M) (x y : g) :
    mapTwo k g M f c x y = f (c x y) := rfl

lemma mapTwo_cycle {N : Type w'} [AddCommGroup N] [Module k N]
    [LieRingModule g N] [LieModule k g N] (f : M →ₗ⁅k,g⁆ N)
    (c : twoCocycle k g M) :
    d₂₃ k g N (mapTwo k g M f.toLinearMap c.val) = 0 := by
  ext x y z
  have h := congrArg (fun a : g →ₗ[k] g →ₗ[k] g →ₗ[k] M => f (a x y z)) c.property
  change ⁅x, f (c.val y z)⁆ - ⁅y, f (c.val x z)⁆ + ⁅z, f (c.val x y)⁆ -
    f (c.val ⁅x,y⁆ z) + f (c.val ⁅x,z⁆ y) - f (c.val ⁅y,z⁆ x) = 0
  simpa only [d₂₃_apply, map_sub, map_add, f.map_lie, map_zero,
    LinearMap.zero_apply] using h

lemma mapTwo_d {N : Type w'} [AddCommGroup N] [Module k N]
    [LieRingModule g N] [LieModule k g N] (f : M →ₗ⁅k,g⁆ N) (b : g →ₗ[k] M) :
    mapTwo k g M f.toLinearMap (d₁₂ k g M b) = d₁₂ k g N (f.toLinearMap.comp b) := by
  ext x y
  simp [d₁₂_apply_apply, f.map_lie]

attribute [local instance] CentralActionHomotopy.coefficientModule

lemma canonical_formula [FiniteDimensional k g] :
    HasLieCEFormula (cochainData k g M (boundaryData k g)).differential := by
  intro n f x
  rw [(cochainData k g M (boundaryData k g)).formula n f x]
  simp only [cochainActionSum, FirstWhitehead.inclusion_smul]

lemma exact_of_ce_vanishes [FiniteDimensional k g]
    (h : Subsingleton (Homology (ceCochain k g M) 2))
    (c : twoCocycle k g M) : ∃ b : g →ₗ[k] M, d₁₂ k g M b = c.val := by
  let δ := (cochainData k g M (boundaryData k g)).differential
  let ω := cochainExterior c.val
  have hc : δ 2 ω = 0 :=
    (exterior_cycle_iff δ (canonical_formula k g M) c.val).mpr c.property
  let z : cycles (ceCochain k g M) 2 := ⟨ω, by
    apply (P103.Ch10.HomologySequence.cycle_iff _
      (show (ComplexShape.up ℕ).Rel 2 3 from rfl) _).mpr
    exact hc⟩
  have hz0 : z ∈ cycleBoundaries (ceCochain k g M) 2 :=
    (Submodule.Quotient.mk_eq_zero _).mp (h.elim (Submodule.Quotient.mk z) 0)
  have hz : z.val ∈ boundaries (ceCochain k g M) 2 := hz0
  obtain ⟨f, hf⟩ := (P103.Ch10.HomologySequence.boundary_iff _
    (show (ComplexShape.up ℕ).Rel 1 2 from rfl) _).mp hz
  change δ 1 f = ω at hf
  obtain ⟨b, hb⟩ := exterior_coboundary_surj δ (canonical_formula k g M) f
  refine ⟨b, (twoCochainExteriorEquiv (k := k) (g := g) (M := M)).injective ?_⟩
  exact hb.trans hf
section Scalar
local instance scalarLieRingModule : LieRingModule g k :=
  inferInstanceAs (LieRingModule g (TrivialLieModule k g k))
local instance scalarLieModule : LieModule k g k :=
  inferInstanceAs (LieModule k g (TrivialLieModule k g k))
local instance scalarTrivial : LieModule.IsTrivial g k := ⟨fun _ _ => rfl⟩

/-- Scalar exactness transferred from the canonical trivial-coefficient complex. -/
lemma scalar_exact [CharZero k] [FiniteDimensional k g]
    (hg : Specs.LieAlgebrasAndRepresentations.SolvableRadical.IsSemisimple_value k g)
    (c : twoCocycle k g k) : ∃ b : g →ₗ[k] k, d₁₂ k g k b = c.val := by
  letI : Module (U k g) k := Ext.trivialModule k g
  letI : IsScalarTower k (U k g) k :=
    IsScalarTower.of_algebraMap_smul fun r x => by
      change Shared.Lie.augmentation k g (algebraMap k (U k g) r) * x = r • x
      simp
  let δ := SecondWhiteheadTrivial.differential k g
  have hδ : HasLieCEFormula δ := by
    intro n f x
    change (SecondWhiteheadTrivial.cochains k g).differential n f _ = _
    rw [(SecondWhiteheadTrivial.cochains k g).formula n f x,
      SecondWhiteheadTrivial.actionSum_zero]
    simp [trivial_lie_zero]
  have hc := (exterior_cycle_iff δ hδ c.val).mpr c.property
  obtain ⟨ℓ, hℓ⟩ := SecondWhiteheadTrivial.cocycleExact k g hg (cochainExterior c.val) hc
  obtain ⟨b, hb⟩ := exterior_coboundary_surj δ hδ ℓ
  refine ⟨b, (twoCochainExteriorEquiv (k := k) (g := g) (M := k)).injective ?_⟩
  exact hb.trans hℓ

/-- For any finite trivial module, apply scalar exactness to each coordinate.
This includes the zero module and uses no algebraic closure hypothesis. -/
lemma exact_of_trivial [CharZero k] [FiniteDimensional k g]
    [FiniteDimensional k M] [LieModule.IsTrivial g M]
    (hg : Specs.LieAlgebrasAndRepresentations.SolvableRadical.IsSemisimple_value k g)
    (c : twoCocycle k g M) : ∃ b : g →ₗ[k] M, d₁₂ k g M b = c.val := by
  classical
  let B := Module.finBasis k M
  let f (i : Fin (Module.finrank k M)) : M →ₗ⁅k,g⁆ k :=
    { B.coord i with map_lie' := by intro x m; simp [trivial_lie_zero] }
  have h (i : Fin (Module.finrank k M)) :=
    scalar_exact k g hg ⟨mapTwo k g M (f i).toLinearMap c.val, mapTwo_cycle k g M (f i) c⟩
  choose b hb using h
  refine ⟨∑ i, (b i).smulRight (B i), ?_⟩
  ext x y
  change d₁₂ k g M (∑ i, (b i).smulRight (B i)) x y = c.val x y
  rw [d₁₂_apply_apply_ofTrivial]
  simp only [LinearMap.sum_apply, LinearMap.smulRight_apply]
  rw [← Finset.sum_neg_distrib]
  have he (i) : -(b i ⁅x,y⁆) = B.repr (c.val x y) i := by
    have hi := congrArg (fun a : twoCochain k g k => a x y) (hb i)
    simpa [d₁₂_apply_apply_ofTrivial, f, trivial_lie_zero] using hi
  simp_rw [← neg_smul, he]
  exact B.sum_repr _
end Scalar

/-- Restriction of a two-cochain whose values lie in an invariant subspace. -/
def restrictTwo (S : LieSubmodule k g M) (c : twoCochain k g M)
    (hc : ∀ x y, c x y ∈ S) : twoCochain k g S :=
  ⟨{ toFun := fun x => (c x).codRestrict S.toSubmodule (hc x)
     map_add' := by intro x y; ext z; simp
     map_smul' := by intro r x; ext z; simp }, by
    intro x; apply Subtype.ext; exact c.property x⟩

lemma restrictTwo_cycle (S : LieSubmodule k g M) (c : twoCochain k g M)
    (hc : ∀ x y, c x y ∈ S) (hz : d₂₃ k g M c = 0) :
    d₂₃ k g S (restrictTwo k g M S c hc) = 0 := by
  ext x y z
  change d₂₃ k g M c x y z = 0
  exact congrArg (fun a : g →ₗ[k] g →ₗ[k] g →ₗ[k] M => a x y z) hz

variable [CharZero k] [FiniteDimensional k g]

lemma exact_of_irreducible [FiniteDimensional k M] [LieModule.IsIrreducible k g M]
    (hg : Specs.LieAlgebrasAndRepresentations.SolvableRadical.IsSemisimple_value k g)
    (c : twoCocycle k g M) : ∃ b : g →ₗ[k] M, d₁₂ k g M b = c.val := by
  classical
  by_cases ht : LieModule.IsTrivial g M
  · letI := ht
    exact exact_of_trivial k g M hg c
  · exact exact_of_ce_vanishes k g M
      (SimpleCoefficientVanishing.cohomology_vanishes k g M hg ht 2) c

/-- A composition-series proof on actual cocycles. Lift a primitive from the
quotient, subtract its coboundary, and solve the remaining submodule cocycle. -/
lemma exact_of_finrank
    (hg : Specs.LieAlgebrasAndRepresentations.SolvableRadical.IsSemisimple_value k g)
    (n : ℕ) :
    ∀ (N : Type w) [AddCommGroup N] [Module k N] [FiniteDimensional k N]
      [LieRingModule g N] [LieModule k g N],
      Module.finrank k N = n → ∀ c : twoCocycle k g N,
        ∃ b : g →ₗ[k] N, d₁₂ k g N b = c.val := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro N _ _ _ _ _ hn c
    by_cases hz : Subsingleton N
    · letI := hz
      exact ⟨0, Subsingleton.elim _ _⟩
    haveI : Nontrivial N := not_subsingleton_iff_nontrivial.mp hz
    by_cases hs : LieModule.IsIrreducible k g N
    · letI := hs
      exact exact_of_irreducible k g N hg c
    have hex : ∃ S : LieSubmodule k g N, S ≠ ⊥ ∧ S ≠ ⊤ := by
      by_contra! h
      apply hs
      exact LieModule.IsIrreducible.mk (fun S hS => h S hS)
    obtain ⟨S, hS0, hS1⟩ := hex
    have hdimS : Module.finrank k S < n := by
      rw [← hn]
      exact Submodule.finrank_lt (by
        intro he
        apply hS1
        exact LieSubmodule.toSubmodule_injective he)
    haveI : Nontrivial S := (LieSubmodule.nontrivial_iff_ne_bot k g N).mpr hS0
    have hdimQ : Module.finrank k (N ⧸ S) < n := by
      have hsum : Module.finrank k (N ⧸ S) + Module.finrank k S = n := by
        simpa only [hn] using! (Submodule.finrank_quotient_add_finrank S.toSubmodule)
      have hpos : 0 < Module.finrank k S := Module.finrank_pos
      omega
    let π := LieSubmodule.Quotient.mk' S
    let cq : twoCocycle k g (N ⧸ S) :=
      ⟨mapTwo k g N π.toLinearMap c.val, mapTwo_cycle k g N π c⟩
    obtain ⟨bq, hbq⟩ := ih _ hdimQ (N ⧸ S) rfl cq
    obtain ⟨s, hs⟩ := CompleteReducibility.quotient_section k g N hg S
    let b := s.toLinearMap.comp bq
    have hsb (x : g) : π (b x) = bq x :=
      congrArg (fun a : (N ⧸ S) →ₗ⁅k,g⁆ (N ⧸ S) => a (bq x)) hs
    let r := c.val - d₁₂ k g N b
    have hr (x y : g) : r x y ∈ S := by
      apply (LieSubmodule.Quotient.mk_eq_zero S).mp
      change π (c.val x y - d₁₂ k g N b x y) = 0
      rw [map_sub, d₁₂_apply_apply, map_sub, map_sub, π.map_lie, π.map_lie, hsb, hsb, hsb]
      exact sub_eq_zero.mpr (congrArg (fun a : twoCochain k g (N ⧸ S) => a x y) hbq).symm
    have hrz : d₂₃ k g N r = 0 := by
      ext x y z
      have he : d₂₃ k g N r x y z =
          d₂₃ k g N c.val x y z - d₂₃ k g N (d₁₂ k g N b) x y z := by
        simp only [d₂₃_apply]
        change ⁅x, c.val y z - d₁₂ k g N b y z⁆ -
          ⁅y, c.val x z - d₁₂ k g N b x z⁆ +
          ⁅z, c.val x y - d₁₂ k g N b x y⁆ -
          (c.val ⁅x,y⁆ z - d₁₂ k g N b ⁅x,y⁆ z) +
          (c.val ⁅x,z⁆ y - d₁₂ k g N b ⁅x,z⁆ y) -
          (c.val ⁅y,z⁆ x - d₁₂ k g N b ⁅y,z⁆ x) = _
        simp only [lie_sub]
        abel
      rw [he, c.property]
      have hd := LinearMap.congr_fun (d₂₃_comp_d₁₂ k g N) b
      rw [show d₂₃ k g N (d₁₂ k g N b) = 0 from hd]
      simp
    let cr : twoCocycle k g S :=
      ⟨restrictTwo k g N S r hr, restrictTwo_cycle k g N S r hr hrz⟩
    obtain ⟨bs, hbs⟩ := ih _ hdimS S rfl cr
    refine ⟨b + S.incl.toLinearMap.comp bs, ?_⟩
    rw [map_add, ← mapTwo_d k g S S.incl bs, hbs]
    ext x y
    change d₁₂ k g N b x y + (c.val x y - d₁₂ k g N b x y) = c.val x y
    abel

variable [FiniteDimensional k M]

/-- Every degree-two cocycle for a finite-dimensional coefficient module
is a coboundary. -/
theorem cocycleExact :
    Specs.LieAlgebrasAndRepresentations.SecondWhitehead.cocycleExactType.{u,v,w} := by
  intro k g M _ _ _ _ _ _ _ _ _ _ hg c
  exact exact_of_finrank k g hg (Module.finrank k M) M rfl c

/-- Vanishing in every exterior CE model with the canonical formula. -/
theorem canonicalVanishing :
    Specs.LieAlgebrasAndRepresentations.SecondWhitehead.canonicalVanishingType.{u,v,w} := by
  intro k g M _ _ _ _ _ _ _ _ _ _ hg δ hδ
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply top_unique
  intro z _
  let e := cocycleExteriorEquiv δ hδ
  let c := e.symm z
  obtain ⟨b, hb⟩ := cocycleExact k g M hg c
  change z.val ∈ LinearMap.range (δ 1)
  refine ⟨b.comp (exteriorPower.oneEquiv k g).toLinearMap, ?_⟩
  rw [← exterior_coboundary δ hδ, hb]
  exact congrArg Subtype.val (e.apply_symm_apply z)

/-- Whitehead's second lemma for the actual canonical CE quotient cohomology. -/
theorem secondWhitehead :
    Specs.LieAlgebrasAndRepresentations.SecondWhitehead.secondWhiteheadType.{u,v,w} := by
  intro k g M _ _ _ _ _ _ _ _ _ _ hg
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply top_unique
  intro z _
  let δ := (cochainData k g M (boundaryData k g)).differential
  have hz : δ 2 z.val = 0 :=
    (P103.Ch10.HomologySequence.cycle_iff _
      (show (ComplexShape.up ℕ).Rel 2 3 from rfl) _).mp z.property
  let e := cocycleExteriorEquiv δ (canonical_formula k g M)
  let c := e.symm ⟨z.val, hz⟩
  obtain ⟨b, hb⟩ := cocycleExact k g M hg c
  change z.val ∈ boundaries (ceCochain k g M) 2
  apply (P103.Ch10.HomologySequence.boundary_iff _
    (show (ComplexShape.up ℕ).Rel 1 2 from rfl) _).mpr
  refine ⟨b.comp (exteriorPower.oneEquiv k g).toLinearMap, ?_⟩
  change δ 1 _ = z.val
  rw [← exterior_coboundary δ (canonical_formula k g M), hb]
  exact congrArg Subtype.val (e.apply_symm_apply ⟨z.val, hz⟩)

/-- Every abelian extension with the specified kernel action has a Lie section. -/
theorem extensionSplits :
    Specs.LieAlgebrasAndRepresentations.SecondWhitehead.extensionSplitsType.{u,v,w,z} := by
  intro k g M _ _ _ _ _ _ _ _ _ _ hg E
  have hlow : Subsingleton (LowH2 (k := k) (g := g) (M := M)) := by
    apply Submodule.Quotient.subsingleton_iff.mpr
    apply top_unique
    intro c _
    obtain ⟨b, hb⟩ := cocycleExact k g M hg c
    refine ⟨b, ?_⟩
    exact Subtype.ext hb
  exact (extensionClass_zero_iff E).mpr (hlow.elim _ 0)

end LieAlgebrasAndRepresentations.SecondWhitehead
