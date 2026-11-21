import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SecondWhiteheadTrivial
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ChevalleyEilenbergExt
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.KillingCriterion
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.InnerDerivations
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

/-! LA-I04: second Whitehead lemma for trivial coefficients.
An exterior cocycle defines a bilinear form. Killing duality produces a
linear endomorphism, and the cocycle identity proves its derivation identity
by pairing with every vector. Innerness then supplies the primitive -B(a,-).
Exactness is proved in the canonical CE complex before passing to its quotient
and comparing with Ext on the same free resolution.
-/

noncomputable section
universe u v
namespace LieAlgebrasAndRepresentations.SecondWhiteheadTrivial
open AdvancedHomologicalAlgebra.CE
variable (k : Type u) (g : Type v) [Field k] [CharZero k]
  [LieRing g] [LieAlgebra k g] [FiniteDimensional k g]

/-- Evaluation of an exterior two-cochain on two vectors. -/
def pair (ω : W k g 2 →ₗ[k] k) (x y : g) : k := ω (wedge k g 2 ![x,y])

omit [CharZero k] [FiniteDimensional k g] in
lemma pair_skew (ω : W k g 2 →ₗ[k] k) (x y : g) :
    pair k g ω y x = -pair k g ω x y := by
  have h := (wedge k g 2).map_swap ![x,y] (show (0 : Fin 2) ≠ 1 by decide)
  have he : ![x,y] ∘ Equiv.swap (0 : Fin 2) 1 = ![y,x] := by
    funext i; fin_cases i <;> rfl
  rw [he] at h
  simp only [pair, h, map_neg]

omit [CharZero k] [FiniteDimensional k g] in
lemma pair_add_left (ω : W k g 2 →ₗ[k] k) (x y z : g) :
    pair k g ω (x+y) z = pair k g ω x z + pair k g ω y z := by
  simp only [pair, AlternatingMap.map_vecCons_add, map_add]

omit [CharZero k] [FiniteDimensional k g] in
lemma pair_smul_left (ω : W k g 2 →ₗ[k] k) (r : k) (x y : g) :
    pair k g ω (r • x) y = r • pair k g ω x y := by
  simp only [pair, AlternatingMap.map_vecCons_smul, map_smul]

/-- The bilinear form corresponding to an exterior two-cochain. -/
def form (ω : W k g 2 →ₗ[k] k) : LinearMap.BilinForm k g :=
  LinearMap.mk₂ k (pair k g ω) (pair_add_left k g ω) (pair_smul_left k g ω)
    (fun x y z => by rw [pair_skew k g ω (y+z) x, pair_add_left,
      pair_skew k g ω x y, pair_skew k g ω x z]; abel)
    (fun r x y => by rw [pair_skew k g ω (r • y) x, pair_smul_left,
      pair_skew k g ω x y]; simp)

local instance : Module (U k g) k := Ext.trivialModule k g
local instance : IsScalarTower k (U k g) k :=
  IsScalarTower.of_algebraMap_smul fun r x => by
    change Shared.Lie.augmentation k g (algebraMap k (U k g) r) * x = r • x
    simp

omit [CharZero k] [FiniteDimensional k g] in
lemma actionSum_zero (n : ℕ) (f : W k g n →ₗ[k] k) (x : Fin (n+1) → g) :
    cochainActionSum k g k n f x = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  change (-1 : ℤ) ^ (i : ℕ) •
    (Shared.Lie.augmentation k g (Shared.Lie.inclusion k g (x i)) * _) = 0
  rw [(Shared.Lie.augmentation_properties k g).1]
  simp

omit [CharZero k] in
lemma differential_one (ℓ : W k g 1 →ₗ[k] k) (x y : g) :
    differential k g 1 ℓ (wedge k g 2 ![x,y]) =
      -ℓ (wedge k g 1 ![⁅x,y⁆]) := by
  rw [(cochains k g).formula 1 ℓ ![x,y], actionSum_zero, zero_add]
  have h : Finset.Ici (0 : Fin 1) = {0} := by decide
  simp [cochainBracketSum, h]

omit [CharZero k] in
lemma differential_two (ω : W k g 2 →ₗ[k] k) (x y z : g) :
    differential k g 2 ω (wedge k g 3 ![x,y,z]) =
      -pair k g ω ⁅x,y⁆ z + pair k g ω ⁅x,z⁆ y - pair k g ω ⁅y,z⁆ x := by
  rw [(cochains k g).formula 2 ω ![x,y,z], actionSum_zero, zero_add]
  have h0 : Finset.Ici (0 : Fin 2) = {0,1} := by decide
  have h1 : Finset.Ici (1 : Fin 2) = {1} := by decide
  have hr2 (a b : g) : Fin.removeNth (1 : Fin 2) ![a,b] = ![a] := by
    funext i; fin_cases i; rfl
  have hr3 : Fin.removeNth (1 : Fin 3) ![x,y,z] = ![x,z] := by
    funext i; fin_cases i <;> rfl
  simp [cochainBracketSum, Fin.sum_univ_succ, h0, h1, pair, hr2, hr3, pow_succ]
  abel

/-- The Killing-dual endomorphism of a cocycle is a derivation. -/
lemma cocycle_derivation (h : IsSemisimple k g) (ω : W k g 2 →ₗ[k] k)
    (hc : differential k g 2 ω = 0) :
    ∃ D : LieDerivation k g g, ∀ x y, killingForm k g (D x) y = pair k g ω x y := by
  let hn := (semisimple_iff_killingForm_nondegenerate k g).mp h
  let D : g →ₗ[k] g := ((killingForm k g).toDual hn).symm.toLinearMap.comp (form k g ω)
  have hD (x y : g) : killingForm k g (D x) y = pair k g ω x y := by
    exact LinearMap.BilinForm.apply_toDual_symm_apply (hB := hn) (form k g ω x) y
  have hd (x y : g) : D ⁅x,y⁆ = ⁅D x,y⁆ + ⁅x,D y⁆ := by
    apply sub_eq_zero.mp
    apply hn.1
    intro z
    have hc' := LinearMap.congr_fun hc (wedge k g 3 ![x,y,z])
    rw [differential_two] at hc'
    change -pair k g ω ⁅x,y⁆ z + pair k g ω ⁅x,z⁆ y - pair k g ω ⁅y,z⁆ x = 0 at hc'
    have h1 : killingForm k g ⁅D x,y⁆ z = -pair k g ω ⁅y,z⁆ x := by
      rw [killingForm_invariant, hD, pair_skew k g ω ⁅y,z⁆ x]
    have h2 : killingForm k g ⁅x,D y⁆ z = pair k g ω ⁅x,z⁆ y := by
      rw [← lie_skew x (D y)]
      simp only [map_neg, LinearMap.neg_apply]
      rw [killingForm_invariant, hD, pair_skew k g ω ⁅x,z⁆ y]
      simp
    simp only [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply]
    rw [hD, h1, h2]
    linear_combination -hc'
  refine ⟨⟨D, ?_⟩, hD⟩
  intro x y
  rw [hd, ← lie_skew (D x) y]
  abel

/-- Every two-cocycle is the coboundary of the Killing functional -B(a,-). -/
theorem cocycleExact : Specs.LieAlgebrasAndRepresentations.SecondWhiteheadTrivial.cocycleExactType.{u,v} := by
  intro k g _ _ _ _ _ h ω hc
  obtain ⟨D, hD⟩ := cocycle_derivation k g h ω hc
  obtain ⟨a, ha, _⟩ := derivation_inner_unique k g h D
  let ℓ : W k g 1 →ₗ[k] k :=
    (-killingForm k g a).comp (exteriorPower.oneEquiv k g).toLinearMap
  refine ⟨ℓ, exteriorPower.linearMap_ext (AlternatingMap.ext fun x => ?_)⟩
  change differential k g 1 ℓ (wedge k g 2 x) = ω (wedge k g 2 x)
  have hx : x = ![x 0,x 1] := by funext i; fin_cases i <;> rfl
  rw [hx, differential_one]
  change -(-killingForm k g a ((exteriorPower.oneEquiv k g) (wedge k g 1 ![⁅x 0,x 1⁆]))) = _
  rw [exteriorPower.oneEquiv_ιMulti, neg_neg]
  change killingForm k g a ⁅x 0,x 1⁆ = _
  rw [← killingForm_invariant]
  have ha' : ⁅a,x 0⁆ = D (x 0) := by
    simpa only [adjoint_apply] using congrArg (fun d : LieDerivation k g g => d (x 0)) ha
  rw [ha']
  exact hD _ _

/-- The second cohomology of the canonical CE complex with trivial coefficients vanishes. -/
theorem secondWhitehead : Specs.LieAlgebrasAndRepresentations.SecondWhiteheadTrivial.secondWhiteheadType.{u,v} := by
  intro k g _ _ _ _ _ h
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply top_unique
  intro z _
  obtain ⟨ℓ, hℓ⟩ := cocycleExact k g h z.val (by
    have hz := z.property
    change ((complex k g).d 2 ((ComplexShape.up ℕ).next 2)).hom z.val = 0 at hz
    rw [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 2 3 by rfl)] at hz
    simpa [complex, Ext.cochain, CochainComplex.of.d] using hz)
  change z.val ∈ P103.Specs.Ch10.Complexes.boundaries (complex k g) 2
  change ∃ a, ((complex k g).d ((ComplexShape.up ℕ).prev 2) 2).hom a = z.val
  rw [(ComplexShape.up ℕ).prev_eq' (show (ComplexShape.up ℕ).Rel 1 2 by rfl)]
  refine ⟨ℓ, ?_⟩
  simpa [complex, Ext.cochain, CochainComplex.of.d] using hℓ

/-- Vanishing of Ext in degree two, computed using the same augmented CE resolution. -/
theorem secondWhiteheadExt (h : IsSemisimple k g) :
    let D := boundaryData k g
    let he := (Ext.free_resolution k g D).1
    Subsingleton (P103.Specs.Ch11.ExtTorDefinitions.ExtWith
      (Ext.resolution k g D.differential D.augmented he) k 2) := by
  intro D he
  obtain ⟨_, _, comparison⟩ := Ext.cohomology k g D he k (cochains k g)
  obtain ⟨e, _⟩ := comparison 2
  have : Subsingleton (H2 k g) := secondWhitehead k g h
  exact e.symm.injective.subsingleton

end LieAlgebrasAndRepresentations.SecondWhiteheadTrivial
