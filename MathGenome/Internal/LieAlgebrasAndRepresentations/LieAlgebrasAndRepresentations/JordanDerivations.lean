import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.JordanDerivations
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.LinearJordan
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ActionsDerivationsSemidirect

open scoped TensorProduct

universe u v w

namespace LieAlgebrasAndRepresentations

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type u} [Field k] {G : Type v} [LieRing G] [LieAlgebra k G]

/-- The shifted derivation identity distributes the eigenvalue between the inputs. -/
theorem shifted_derivation_bracket (D : LieDerivation k G G) (a b : k) (x y : G) :
    (D.toLinearMap - (a + b) • 1) ⁅x, y⁆ =
      ⁅(D.toLinearMap - a • 1) x, y⁆ + ⁅x, (D.toLinearMap - b • 1) y⁆ := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    sub_lie, lie_sub, smul_lie, lie_smul]
  change D ⁅x, y⁆ - (a + b) • ⁅x, y⁆ =
    (⁅D x, y⁆ - a • ⁅x, y⁆) + (⁅x, D y⁆ - b • ⁅x, y⁆)
  rw [D.apply_lie_eq_add, add_smul]
  abel

/-- A power of the shifted derivation kills a bracket of generalized eigenvectors. -/
theorem shifted_derivation_pow_bracket (D : LieDerivation k G G) (a b : k)
    (p q : ℕ) (x y : G)
    (hx : ((D.toLinearMap - a • 1) ^ p) x = 0)
    (hy : ((D.toLinearMap - b • 1) ^ q) y = 0) :
    ((D.toLinearMap - (a + b) • 1) ^ (p + q)) ⁅x, y⁆ = 0 := by
  induction p generalizing x y q with
  | zero =>
    simp only [pow_zero, Module.End.one_apply] at hx
    simp [hx]
  | succ p ihp =>
    induction q generalizing x y with
    | zero =>
      simp only [pow_zero, Module.End.one_apply] at hy
      simp [hy]
    | succ q ihq =>
      have hx' : ((D.toLinearMap - a • 1) ^ p) ((D.toLinearMap - a • 1) x) = 0 := by
        simpa only [pow_succ, Module.End.mul_apply] using hx
      have hy' : ((D.toLinearMap - b • 1) ^ q) ((D.toLinearMap - b • 1) y) = 0 := by
        simpa only [pow_succ, Module.End.mul_apply] using hy
      rw [show p.succ + q.succ = (p + q.succ) + 1 by omega,
        pow_succ, Module.End.mul_apply, shifted_derivation_bracket, map_add,
        ihp q.succ _ y hx' hy]
      have h := ihq x ((D.toLinearMap - b • 1) y) hx hy'
      simpa only [Nat.succ_add, Nat.add_succ, zero_add] using h

/-- LA-B03: generalized eigenspaces have additive bracket weights. -/
theorem generalized_eigenspace_bracket :
    Specs.LieAlgebrasAndRepresentations.JordanDerivations.generalized_eigenspace_bracket_type := by
  intro k _ G _ _ D a b x y hx hy
  obtain ⟨p, hp⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hx
  obtain ⟨q, hq⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hy
  exact (Module.End.mem_maxGenEigenspace _ _ _).mpr
    ⟨p + q, shifted_derivation_pow_bracket D a b p q x y hp hq⟩

/-- The Leibniz rule is preserved and reflected by scalar extension. -/
theorem derivation_baseChange_iff :
    Specs.LieAlgebrasAndRepresentations.JordanDerivations.derivation_baseChange_iff_type := by
  intro k _ K _ _ G _ _ f
  constructor
  · intro h x y
    apply Module.Flat.tensorProduct_mk_injective (R := k) (S := K) (M := G)
    change (1 : K) ⊗ₜ[k] f ⁅x, y⁆ = 1 ⊗ₜ[k] (⁅f x, y⁆ + ⁅x, f y⁆)
    simpa only [LinearMap.baseChange_tmul, LieAlgebra.ExtendScalars.bracket_tmul,
      one_mul, TensorProduct.tmul_add] using h (1 ⊗ₜ[k] x) (1 ⊗ₜ[k] y)
  · intro h x y
    refine x.inductionOn (fun a x => ?_) (fun x z hx hz => ?_)
    · refine y.inductionOn (fun b y => ?_) (fun y z hy hz => ?_)
      · simp only [LinearMap.baseChange_tmul, LieAlgebra.ExtendScalars.bracket_tmul,
          h, TensorProduct.tmul_add]
      · simp only [lie_add, map_add, hy, hz]
        abel
    · simp only [add_lie, map_add, hx, hz]
      abel

/-- Over a field where the generalized eigenspaces span, the semisimple part
of a derivation satisfies Leibniz. This formulation also works for the zero space. -/
theorem semisimple_part_derivation_of_split
    (D : LieDerivation k G G) (s n : Module.End k G)
    (he : D.toLinearMap = s + n) (hc : Commute s n)
    (hs : s.IsSemisimple) (hn : IsNilpotent n)
    (hspan : (⨆ a : k, Module.End.maxGenEigenspace D.toLinearMap a) = ⊤) :
    ∀ x y, s ⁅x, y⁆ = ⁅s x, y⁆ + ⁅x, s y⁆ := by
  have hDs : Commute D.toLinearMap s := by
    rw [he]
    exact (Commute.refl s).add_left hc.symm
  have hscalar {a : k} {x : G}
      (hx : x ∈ Module.End.maxGenEigenspace D.toLinearMap a) : s x = a • x := by
    apply Module.End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil
      hx hDs hs.isFinitelySemisimple
    simpa only [he, add_sub_cancel_left] using hn
  intro x
  have hx : x ∈ ⨆ a : k, Module.End.maxGenEigenspace D.toLinearMap a := by
    rw [hspan]; trivial
  refine Submodule.iSup_induction _ (motive := fun x => ∀ y, s ⁅x, y⁆ = ⁅s x, y⁆ + ⁅x, s y⁆) hx ?_ ?_ ?_
  · intro a x hx y
    have hy : y ∈ ⨆ b : k, Module.End.maxGenEigenspace D.toLinearMap b := by
      rw [hspan]; trivial
    refine Submodule.iSup_induction _ (motive := fun y => s ⁅x, y⁆ = ⁅s x, y⁆ + ⁅x, s y⁆) hy ?_ ?_ ?_
    · intro b y hy
      rw [hscalar (generalized_eigenspace_bracket D a b x y hx hy),
        hscalar hx, hscalar hy, smul_lie, lie_smul, add_smul]
    · simp
    · intro y z hy hz
      simp only [lie_add, map_add, hy, hz]
      abel
  · intro y
    simp
  · intro x z hx hz y
    simp only [add_lie, map_add, hx y, hz y]
    abel

/-- LA-B03: descend Leibniz for the semisimple part, then subtract it from D. -/
theorem jordan_components_are_derivations :
    Specs.LieAlgebrasAndRepresentations.JordanDerivations.jordan_components_are_derivations_type := by
  intro k _ _ G _ _ _ D s n hdec
  rcases hdec with ⟨he, hc, hs, hn⟩
  let K := AlgebraicClosure k
  let φ := Module.End.baseChangeHom k K G
  have hD : ∀ x y, D.toLinearMap ⁅x, y⁆ = ⁅D x, y⁆ + ⁅x, D y⁆ := by
    intro x y
    exact (D.apply_lie_eq_add x y).trans (add_comm _ _)
  have hDK := (derivation_baseChange_iff (K := K) D.toLinearMap).mpr hD
  let DK : LieDerivation K (K ⊗[k] G) (K ⊗[k] G) :=
    { D.toLinearMap.baseChange K with
      leibniz' := by
        intro x y
        rw [hDK, ← lie_skew y (D.toLinearMap.baseChange K x)]
        abel }
  have heK : DK.toLinearMap = φ s + φ n := by
    change φ D.toLinearMap = φ s + φ n
    rw [he, map_add]
  have hsK : (φ s).IsSemisimple := hs
  have hsDK := semisimple_part_derivation_of_split DK (φ s) (φ n) heK
    (hc.map φ) hsK (hn.map φ) (Module.End.iSup_maxGenEigenspace_eq_top _)
  have hsD : ∀ x y, s ⁅x, y⁆ = ⁅s x, y⁆ + ⁅x, s y⁆ :=
    (derivation_baseChange_iff (K := K) s).mp hsDK
  have hs_mem : s ∈ derivations_subalgebra k G := (derivation_membership s).mpr hsD
  have hD_mem : D.toLinearMap ∈ derivations_subalgebra k G :=
    (derivation_membership D.toLinearMap).mpr hD
  have hn_eq : n = D.toLinearMap - s := by rw [he]; abel
  exact ⟨hs_mem, hn_eq ▸ (derivations_subalgebra k G).sub_mem hD_mem hs_mem⟩

/-- The complete polynomial decomposition with both parts bundled as derivations. -/
theorem jordan_decomposition_derivations :
    Specs.LieAlgebrasAndRepresentations.JordanDerivations.jordan_decomposition_derivations_type := by
  intro k _ _ G _ _ _ D
  obtain ⟨s, n, hdec, hpoly, hstable, huniq⟩ := linear_jordan_decomposition D.toLinearMap
  obtain ⟨hs, hn⟩ := jordan_components_are_derivations D s n hdec
  obtain ⟨S, hS⟩ := hs
  obtain ⟨N, hN⟩ := hn
  have hS' : S.toLinearMap = s := hS
  have hN' : N.toLinearMap = n := hN
  refine ⟨S, N, ?_⟩
  change IsJordanDecomposition D.toLinearMap S.toLinearMap N.toLinearMap ∧ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hS', hN'] using hdec
  · simpa only [hS', hN'] using hpoly
  · intro W hW
    obtain ⟨hsW, hnW⟩ := hstable W hW
    constructor
    · intro x hx
      change S.toLinearMap x ∈ W
      rw [hS']
      exact hsW x hx
    · intro x hx
      change N.toLinearMap x ∈ W
      rw [hN']
      exact hnW x hx
  · simpa only [hS', hN'] using huniq

end LieAlgebrasAndRepresentations
