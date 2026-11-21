import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.HighestWeightData
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RealRootSpace
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleRoots
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootDecomposition
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootWeightLattices
import Batteries.Tactic.OpenPrivate

noncomputable section
namespace LieAlgebrasAndRepresentations.HighestWeight
open Module
open Specs.LieAlgebrasAndRepresentations.HighestWeightData (
  positiveRootCone_value integralRootLattice_value integralWeights_value dominantWeights_value
  weightLE_value weightSpace_value realization_value)

abbrev positiveRootCone := @positiveRootCone_value
abbrev integralRootLattice := @integralRootLattice_value
abbrev integralWeights := @integralWeights_value
abbrev dominantWeights := @dominantWeights_value
abbrev weightLE := @weightLE_value
abbrev weightSpace := @weightSpace_value
abbrev realization := @realization_value

universe u v w
variable {H : Type u} [AddCommGroup H] [Module ℂ H] {ι : Type v}

@[simp] theorem mem_integralWeights (h : ι → H) (χ : Module.Dual ℂ H) :
    χ ∈ integralWeights h ↔ ∀ i, ∃ z : ℤ, χ (h i) = (z : ℂ) := Iff.rfl

@[simp] theorem mem_dominantWeights (h : ι → H) (χ : Module.Dual ℂ H) :
    χ ∈ dominantWeights h ↔ ∀ i, ∃ n : ℕ, χ (h i) = (n : ℂ) := Iff.rfl

theorem dominant_iff : Specs.LieAlgebrasAndRepresentations.HighestWeightData.dominant_iff_type := by
  intro H _ _ ι h χ
  constructor
  · intro hn
    constructor
    · intro i
      obtain ⟨n, hn⟩ := hn i
      exact ⟨n, by simpa using hn⟩
    · intro i
      obtain ⟨n, hn⟩ := hn i
      simp [hn]
  · rintro ⟨hz, hp⟩ i
    obtain ⟨z, hz⟩ := hz i
    have hzp : 0 ≤ z := by
      have hi := hp i
      simpa [hz] using hi
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hzp
    exact ⟨n, by simpa using hz⟩

/-- The natural-number span is exactly the finite nonnegative sums. -/
theorem mem_positiveRootCone_iff [Fintype ι]
    (α : ι → Module.Dual ℂ H) (χ : Module.Dual ℂ H) :
    χ ∈ positiveRootCone α ↔ ∃ n : ι → ℕ, ∑ i, n i • α i = χ :=
  Submodule.mem_span_range_iff_exists_fun ℕ

private theorem cone_basis_coordinates (a : Basis ι ℂ (Module.Dual ℂ H))
    (χ : Module.Dual ℂ H) (hχ : χ ∈ positiveRootCone a) :
    ∀ i, ∃ n : ℕ, a.repr χ i = (n : ℂ) := by
  change χ ∈ Submodule.span ℕ (Set.range a) at hχ
  induction hχ using Submodule.span_induction with
  | mem χ hχ =>
    obtain ⟨j, rfl⟩ := hχ
    intro i
    classical
    by_cases hi : j = i
    · subst j
      exact ⟨1, by simp⟩
    · exact ⟨0, by simp [hi]⟩
  | zero => intro i; exact ⟨0, by simp⟩
  | add χ ψ hχ hψ ihχ ihψ =>
    intro i
    obtain ⟨n, hn⟩ := ihχ i
    obtain ⟨m, hm⟩ := ihψ i
    exact ⟨n + m, by simp [hn, hm]⟩
  | smul n χ hχ ih =>
    intro i
    obtain ⟨m, hm⟩ := ih i
    exact ⟨n * m, by simp [hm, nsmul_eq_mul]⟩

/-- With a simple-root basis the relation is antisymmetric. -/
theorem weightLE_antisymm (a : Basis ι ℂ (Module.Dual ℂ H))
    {χ μ : Module.Dual ℂ H} (h₁ : weightLE a χ μ) (h₂ : weightLE a μ χ) : χ = μ := by
  apply a.repr.injective
  ext i
  obtain ⟨n, hn⟩ := cone_basis_coordinates a (μ - χ) h₁ i
  obtain ⟨m, hm⟩ := cone_basis_coordinates a (χ - μ) h₂ i
  have hn' := congrArg Complex.re hn
  have hm' := congrArg Complex.re hm
  simp only [map_sub, Finsupp.sub_apply, Complex.sub_re, Complex.natCast_re] at hn' hm'
  have hn0 : n = 0 := by
    have hp : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    have hnz : (n : ℝ) = 0 := by linarith
    exact_mod_cast hnz
  have hz : a.repr μ i - a.repr χ i = 0 := by simpa [hn0] using hn
  exact (sub_eq_zero.mp hz).symm

/-- The source's order is a reflexive and transitive relation. -/
theorem weightLE_refl (α : ι → Module.Dual ℂ H) (χ : Module.Dual ℂ H) :
    weightLE α χ χ := by simp [weightLE_value]

theorem weightLE_trans (α : ι → Module.Dual ℂ H) {χ μ ν : Module.Dual ℂ H}
    (h₁ : weightLE α χ μ) (h₂ : weightLE α μ ν) : weightLE α χ ν := by
  have hh := (positiveRootCone α).add_mem h₁ h₂
  simpa only [weightLE_value, sub_add_sub_cancel'] using hh

theorem mem_weightSpace : Specs.LieAlgebrasAndRepresentations.HighestWeightData.mem_weightSpace_type := by
  intro L _ _ V _ _ _ _ H μ v
  change v ∈ LieModule.weightSpace V (μ : H → ℂ) ↔ _
  simpa only [LieSubalgebra.coe_bracket_of_module] using LieModule.mem_weightSpace (μ : H → ℂ) v

/-- The module Leibniz identity shifts an ordinary weight by the acting root. -/
theorem root_action : Specs.LieAlgebrasAndRepresentations.HighestWeightData.root_action_type := by
  intro L _ _ V _ _ _ _ H α μ x v hx hv
  rw [LieAlgebrasAndRepresentations.mem_rootSpace] at hx
  rw [mem_weightSpace] at hv ⊢
  intro h
  rw [leibniz_lie, hv h, hx h, lie_smul, smul_lie, LinearMap.add_apply, add_smul]
  exact add_comm _ _

variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[simp] theorem realization_apply_coroot (b : Basis ι ℝ E) (c : Basis ι ℂ H)
    (x : E) (i : ι) :
    realization b c x (c i) = (inner ℝ x (coroot (b i)) : ℂ) := by
  exact c.constr_basis ℂ _ i

/-- The comparison is uniquely characterized by its simple-coroot evaluations. -/
theorem realization_unique (b : Basis ι ℝ E) (c : Basis ι ℂ H)
    (x : E) (χ : Module.Dual ℂ H)
    (hχ : ∀ i, χ (c i) = (inner ℝ x (coroot (b i)) : ℂ)) :
    χ = realization b c x := by
  apply c.ext
  intro i
  simpa using hχ i

theorem realization_integral_iff (b : Basis ι ℝ E) (c : Basis ι ℂ H) (x : E) :
    realization b c x ∈ integralWeights c ↔ x ∈ weightLattice b := by
  rw [mem_integralWeights, weightLattice_mem_iff]
  apply forall_congr'
  intro i
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, by simpa using congrArg Complex.re hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, by simp [hz]⟩

theorem realization_injective [Finite ι] [DecidableEq ι]
    (b : Basis ι ℝ E) (c : Basis ι ℂ H) : Function.Injective (realization b c) := by
  intro x y hxy
  apply (fundamentalWeights b).repr.injective
  ext i
  rw [fundamentalWeights_repr, fundamentalWeights_repr]
  have hi := congrArg (fun χ : Module.Dual ℂ H => (χ (c i)).re) hxy
  simpa using hi

/-- Every integral complex weight is the extension of a real integral weight. -/
theorem integralWeights_realization [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ E) (c : Basis ι ℂ H) (χ : Module.Dual ℂ H)
    (hχ : χ ∈ integralWeights c) :
    ∃ x ∈ weightLattice b, realization b c x = χ := by
  let x := (fundamentalWeights b).equivFun.symm (fun i => (χ (c i)).re)
  have he : realization b c x = χ := by
    apply c.ext
    intro i
    rw [realization_apply_coroot, ← fundamentalWeights_repr]
    change (((fundamentalWeights b).equivFun x i : ℝ) : ℂ) = χ (c i)
    rw [LinearEquiv.apply_symm_apply]
    obtain ⟨z, hz⟩ := hχ i
    simp [hz]
  exact ⟨x, (realization_integral_iff b c x).mp (he.symm ▸ hχ), he⟩

/-- Equality of the two actual integral lattices under complex extension. -/
theorem realization_weightLattice [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ E) (c : Basis ι ℂ H) :
    (weightLattice b).map ((realization b c).restrictScalars ℤ) = integralWeights c := by
  ext χ
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (realization_integral_iff b c x).mpr hx
  · intro hχ
    obtain ⟨x, hx, he⟩ := integralWeights_realization b c χ hχ
    exact ⟨x, hx, he⟩

/-- Root lattices agree whenever the given simple roots have the normalized
Cartan pairings with the given simple coroots. -/
theorem realization_rootLattice (b : Basis ι ℝ E) (c : Basis ι ℂ H)
    (α : ι → Module.Dual ℂ H)
    (hα : ∀ i j, α i (c j) = (inner ℝ (b i) (coroot (b j)) : ℂ)) :
    (rootLattice b).map ((realization b c).restrictScalars ℤ) = integralRootLattice α := by
  have he : ∀ i, realization b c (b i) = α i := fun i =>
    (realization_unique b c (b i) (α i) (hα i)).symm
  change (Submodule.span ℤ (Set.range b)).map ((realization b c).restrictScalars ℤ) =
    Submodule.span ℤ (Set.range α)
  rw [Submodule.map_span]
  congr 1
  ext χ
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (he i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨b i, ⟨i, rfl⟩, he i⟩

/-- The same extension identifies the nonnegative root cones. -/
theorem realization_positiveRootCone (b : Basis ι ℝ E) (c : Basis ι ℂ H)
    (α : ι → Module.Dual ℂ H)
    (hα : ∀ i j, α i (c j) = (inner ℝ (b i) (coroot (b j)) : ℂ)) :
    (Submodule.span ℕ (Set.range b)).map ((realization b c).restrictScalars ℕ) =
      positiveRootCone α := by
  have he : ∀ i, realization b c (b i) = α i := fun i =>
    (realization_unique b c (b i) (α i) (hα i)).symm
  change (Submodule.span ℕ (Set.range b)).map ((realization b c).restrictScalars ℕ) =
    Submodule.span ℕ (Set.range α)
  rw [Submodule.map_span]
  congr 1
  ext χ
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (he i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨b i, ⟨i, rfl⟩, he i⟩


/-- Dominance agrees with the closed simple chamber in the real root space. -/
theorem realization_dominant_iff [Finite ι] [DecidableEq ι]
    (R : Set E) (v : E) (b : Basis ι ℝ E) (hb : IsSimpleBasis R v b)
    (c : Basis ι ℂ H) (x : E) :
    realization b c x ∈ dominantWeights c ↔
      x ∈ weightLattice b ∧ x ∈ closedSimpleChamber R v := by
  rw [dominant_iff, realization_integral_iff, closedSimpleChamber_iff_coords b hb]
  simp only [realization_apply_coroot, Complex.ofReal_re, fundamentalWeights_repr]

/-- Equality of the dominant integral sets, including on chamber walls. -/
theorem realization_dominant_image [Fintype ι] [DecidableEq ι]
    (R : Set E) (v : E) (b : Basis ι ℝ E) (hb : IsSimpleBasis R v b)
    (c : Basis ι ℂ H) :
    realization b c '' {x | x ∈ weightLattice b ∧ x ∈ closedSimpleChamber R v} =
      (dominantWeights c : Set (Module.Dual ℂ H)) := by
  ext χ
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (realization_dominant_iff R v b hb c x).mpr hx
  · intro hχ
    obtain ⟨x, hx, he⟩ := integralWeights_realization b c χ ((dominant_iff c χ).mp hχ).1
    refine ⟨x, ?_, he⟩
    exact (realization_dominant_iff R v b hb c x).mp (he.symm ▸ hχ)

/-- In rank zero the positive root cone contains only zero. -/
theorem positiveRootCone_empty [IsEmpty ι] (α : ι → Module.Dual ℂ H) :
    positiveRootCone α = ⊥ := by
  simp [positiveRootCone_value]

/-- Integrality and dominance have no inequalities to check in rank zero. -/
theorem integralWeights_empty [IsEmpty ι] (h : ι → H) : integralWeights h = ⊤ := by
  ext χ
  simp [integralWeights_value]

theorem dominantWeights_empty [IsEmpty ι] (h : ι → H) : dominantWeights h = ⊤ := by
  ext χ
  simp [dominantWeights_value]

theorem weightLE_empty [IsEmpty ι] (α : ι → Module.Dual ℂ H)
    (μ χ : Module.Dual ℂ H) : weightLE α μ χ ↔ μ = χ := by
  simp only [weightLE_value, positiveRootCone_empty, Submodule.mem_bot, sub_eq_zero, eq_comm]

end LieAlgebrasAndRepresentations.HighestWeight

namespace LieAlgebrasAndRepresentations.HighestWeight

open Module
open Specs.LieAlgebrasAndRepresentations.RealRootSpace
open private complex_extension_bijective from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RealRootSpace

universe u v

theorem root_set_empty_of_subsingleton_cartan :
    Specs.LieAlgebrasAndRepresentations.HighestWeightData.root_set_empty_of_subsingleton_cartan_type := by
  intro L _ _ H _
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro α hα
  apply hα.1
  ext h
  simp [Subsingleton.elim h 0]

section Cartan

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
variable {H : LieSubalgebra ℂ L}

private theorem extension_restrict (d : Realization H) (x : E H) (u : realCartan H) :
    d.j x u = (x u : ℂ) := by
  simpa using d.extension_formula x u 0

private theorem cartan_lattice_comparison_of_realization (d : Realization H) :
    Specs.LieAlgebrasAndRepresentations.HighestWeightData.CartanLatticeComparison.{u, v} d := by
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  intro v hv ι s
  classical
  obtain ⟨b₀, hb₀⟩ := simpleRoots_basis (realRoots H) d.root_system v hv
  let b := b₀.reindex s.symm
  have hb (i : ι) : b i = (s i : E H) := by
    rw [Basis.reindex_apply, Equiv.symm_symm, hb₀]
  have hs : IsSimpleBasis (realRoots H) v b := by
    change Set.range b = simpleRoots (realRoots H) v
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      rw [hb i]
      exact (s i).property
    · intro hx
      obtain ⟨i, hi⟩ := s.surjective ⟨x, hx⟩
      exact ⟨i, (hb i).trans (congrArg Subtype.val hi)⟩
  let α : ι → Module.Dual ℂ H := fun i => d.j (s i : E H)
  let h : ι → H := fun i => killingCoroot H (α i)
  have hα (i : ι) : α i ∈ rootSet H ∧ rootRestriction H (α i) = b i := by
    have hi := (s i).property
    have hmem : (s i : E H) ∈ realRoots H := hi.1.1
    obtain ⟨β, hβ, he⟩ := hmem
    have hj : α i = β := by
      change d.j (s i : E H) = β
      rw [← he]
      exact d.extension_root β hβ
    exact ⟨hj ▸ hβ, hj.symm ▸ (he.trans (hb i).symm)⟩
  -- Transport the real coroot basis through the Killing Riesz map and extend scalars.
  let f := extendScalars (S := ℂ) (realCartan H).subtype
  have hf : Function.Bijective f := by
    apply complex_extension_bijective
    exact d.cartan_sum
  let c := (((simpleCorootBasis b).map d.q).baseChange ℂ).map (LinearEquiv.ofBijective f hf)
  have hc (i : ι) : c i = h i := by
    change f ((((simpleCorootBasis b).map d.q).baseChange ℂ) i) = h i
    rw [Basis.baseChange_apply, extendScalars_tmul, one_smul, Basis.map_apply,
      simpleCorootBasis_apply, ← (hα i).2]
    exact d.riesz_coroot (α i) (hα i).1
  have hc_fun : (c : ι → H) = h := funext hc
  let a := (b.baseChange ℂ).map d.complexification
  have ha (i : ι) : a i = α i := by
    rw [Basis.map_apply, Basis.baseChange_apply, d.complexification_tmul, one_smul, hb]
  have hp (x : E H) (i : ι) : d.j x (h i) = (inner ℝ x (coroot (b i)) : ℂ) := by
    rw [← (hα i).2]
    exact d.coroot_evaluation x (α i) (hα i).1
  have he : d.j = realization b c := by
    ext x : 1
    exact realization_unique b c x _ (fun i => by rw [hc, hp])
  have hpair (i k : ι) : α i (c k) = (inner ℝ (b i) (coroot (b k)) : ℂ) := by
    change d.j (s i : E H) (c k) = _
    rw [hc, ← hb i, hp]
  letI : Fintype ι := FiniteDimensional.fintypeBasisIndex c
  have hi : ∀ χ ∈ integralWeights h, ∃ x ∈ weightLattice b, d.j x = χ ∧
      ∀ u : realCartan H, χ u = (x u : ℂ) := by
    intro χ hχ
    rw [← hc_fun] at hχ
    obtain ⟨x, hx, h_eq⟩ := integralWeights_realization b c χ hχ
    have h_eq' : d.j x = χ := by rwa [he]
    exact ⟨x, hx, h_eq', fun u => h_eq' ▸ extension_restrict d x u⟩
  have hzero : IsEmpty ι → Subsingleton H :=
    fun hι => ⟨fun u v => c.repr.injective (Subsingleton.elim (c.repr u) (c.repr v))⟩
  refine ⟨b, c, a, hs, fun i => ⟨hb i, ha i, hc i, (hα i).1, (hα i).2⟩, hp,
    ?_, ?_, ?_, ?_, ?_, hi, ?_, ?_, ?_⟩
  · rw [he]
    exact realization_injective b c
  · conv_lhs => rw [he]
    exact realization_rootLattice b c α hpair
  · conv_lhs => rw [he]
    exact realization_positiveRootCone b c α hpair
  · change (weightLattice b).map (d.j.restrictScalars ℤ) = integralWeights h
    rw [← hc_fun, he]
    exact realization_weightLattice b c
  · change d.j '' {x | x ∈ weightLattice b ∧ x ∈ closedSimpleChamber (realRoots H) v} =
      (dominantWeights h : Set (Module.Dual ℂ H))
    rw [← hc_fun, he]
    exact realization_dominant_image (realRoots H) v b hs c
  · change ∀ μ χ, weightLE α μ χ → weightLE α χ μ → μ = χ
    rw [← show (a : ι → Module.Dual ℂ H) = α from funext ha]
    exact fun _ _ => weightLE_antisymm a
  · constructor
    · intro hz
      letI := hzero hz
      exact root_set_empty_of_subsingleton_cartan H
    · intro hz
      exact ⟨fun i => by simpa only [hz, Set.mem_empty_iff_false] using (hα i).1⟩
  · intro hz
    letI := hzero hz
    haveI : Subsingleton (Module.Dual ℂ H) :=
      ⟨fun x y => LinearMap.ext fun u => by simp [Subsingleton.elim u 0]⟩
    exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _,
      Subsingleton.elim _ _⟩

/-- The natural extension identifies the real root and weight lattices and
their nonnegative parts with the lattices in the complex Cartan dual. -/
theorem cartan_lattice_comparison :
    Specs.LieAlgebrasAndRepresentations.HighestWeightData.cartan_lattice_comparison_type.{u, v} := by
  intro L _ _ _ hss H _
  let d := RealRootSpace.realization hss H
  exact ⟨d, cartan_lattice_comparison_of_realization d⟩

end Cartan

end LieAlgebrasAndRepresentations.HighestWeight
