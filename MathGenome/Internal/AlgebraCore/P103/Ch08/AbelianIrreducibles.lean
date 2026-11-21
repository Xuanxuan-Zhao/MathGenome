import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.AbelianIrreducibles
import MathGenome.Internal.AlgebraCore.P103.Ch08.SplitFourierTransform
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

noncomputable section
open scoped MonoidAlgebra
namespace P103.Ch08.AbelianIrreducibles

variable {k G V : Type*} [Field k] [CommGroup G] [AddCommGroup V] [Module k V]

/-- Scalar group operators preserve every line, so irreducibility forces a
nonzero line to be the whole representation. -/
theorem finrank_eq_one_of_scalar_actions (ρ : Representation k G V)
    (hρ : Irreducible k G V ρ)
    (hs : ∀ g, ∃ c : k, ∀ v, ρ g v = c • v) : Module.finrank k V = 1 := by
  have : Nontrivial V := hρ.1
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let U : Subrepresentation ρ :=
    { toSubmodule := k ∙ v
      apply_mem_toSubmodule := by
        intro g w hw
        obtain ⟨c, hc⟩ := hs g
        rw [hc]
        exact (k ∙ v).smul_mem c hw }
  have hU : U = ⊤ := (hρ.2 U).resolve_left (by
    intro he
    have hm : v ∈ U := Submodule.mem_span_singleton_self v
    rw [he] at hm
    exact hv ((Submodule.mem_bot k).mp hm))
  apply finrank_eq_one v hv
  intro w
  have hw : w ∈ U := hU ▸ (show w ∈ (⊤ : Subrepresentation ρ) from trivial)
  exact Submodule.mem_span_singleton.mp hw

/-- Splitting supplies scalar algebra endomorphisms on any simple module,
by transporting from a simple regular constituent. -/
theorem splitField : Specs.splitFieldType := by
  intro k G V _ _ _ _ _ ρ hn hs hρ
  have := SplitFourierTransform.simple_asModule ρ hρ
  have : NeZero (Nat.card G : k) := ⟨hn⟩
  obtain ⟨S, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule k[G] ρ.asModule
  have : IsSimpleModule k[G] S := IsSimpleModule.congr e.symm
  have hscalar := SplitFourierTransform.scalar_end_of_equiv e (hs S inferInstance).2
  refine ⟨SplitFourierTransform.finite_dimensional ρ hρ,
    finrank_eq_one_of_scalar_actions ρ hρ ?_⟩
  intro g
  obtain ⟨c, hc⟩ := hscalar (Module.toModuleEnd k[G] ρ.asModule (MonoidAlgebra.single g (1 : k)))
  refine ⟨c, fun v => ?_⟩
  have hv := LinearMap.congr_fun hc (ρ.asModuleEquiv.symm v)
  have hv' := congrArg ρ.asModuleEquiv hv
  change c • v = ρ.asAlgebraHom (MonoidAlgebra.single g 1) v at hv'
  simpa using hv'.symm

/-- An eigenspace of a group operator is invariant for an abelian group. -/
theorem scalar_of_hasEigenvalue (ρ : Representation k G V)
    (hρ : Irreducible k G V ρ) (g : G) {c : k}
    (hc : Module.End.HasEigenvalue (ρ g) c) : ∀ v, ρ g v = c • v := by
  let U : Subrepresentation ρ :=
    { toSubmodule := Module.End.eigenspace (ρ g) c
      apply_mem_toSubmodule := by
        intro h v hv
        apply Module.End.mem_eigenspace_iff.mpr
        rw [← Module.End.mul_apply, ← map_mul, mul_comm g h, map_mul,
          Module.End.mul_apply, Module.End.mem_eigenspace_iff.mp hv, map_smul] }
  have hU : U = ⊤ := (hρ.2 U).resolve_left (by
    intro he
    exact hc (congrArg Subrepresentation.toSubmodule he))
  intro v
  apply Module.End.mem_eigenspace_iff.mp
  change v ∈ U
  rw [hU]
  trivial

/-- The split annihilating polynomial yields an eigenvalue; its eigenspace
is the whole irreducible representation. Finite dimension is derived first. -/
theorem rootsOfUnity : Specs.rootsOfUnityType := by
  intro k G V _ _ _ _ _ ρ hn hs hρ
  have : FiniteDimensional k V := SplitFourierTransform.finite_dimensional ρ hρ
  have : Nontrivial V := hρ.1
  refine ⟨inferInstance, finrank_eq_one_of_scalar_actions ρ hρ ?_⟩
  intro g
  have hp : Polynomial.aeval (ρ g)
      (Polynomial.X ^ Monoid.exponent G - 1 : Polynomial k) = 0 := by
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one]
    rw [← map_pow, Monoid.pow_exponent_eq_one, map_one, sub_self]
  have hd := minpoly.dvd k (ρ g) hp
  have hnonzero : (Polynomial.X ^ Monoid.exponent G - 1 : Polynomial k) ≠ 0 := by
    exact Polynomial.X_pow_sub_C_ne_zero
      (Monoid.ExponentExists.of_finite (G := G)).exponent_pos 1
  have hsplit := hs.of_dvd hnonzero hd
  obtain ⟨c, hc⟩ := hsplit.exists_eval_eq_zero
    (ne_of_gt (minpoly.degree_pos (Algebra.IsIntegral.isIntegral (ρ g))))
  exact ⟨c, scalar_of_hasEigenvalue ρ hρ g
    (Module.End.hasEigenvalue_of_isRoot hc)⟩

end P103.Ch08.AbelianIrreducibles
