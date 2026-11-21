import MathGenome.Internal.Specs.D05.M14.Polar
import MathGenome.Internal.D05.M13.Unitary
import MathGenome.Internal.D05.M14.PositiveRoot
import MathGenome.Internal.D05.M14.Svd
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

noncomputable section

namespace D05.M14.Polar

open Module.End
open scoped ComplexOrder

/-- A diagonal positive factor in a full singular basis, and the isometric
equivalence carrying that basis to the full output basis. -/
theorem exists_polar : Specs.D05.M14.Polar.exists_polar := by
  intro F V _ _ _ _ T
  classical
  obtain ⟨d⟩ := D05.M14.Svd.exists_svd T
  let P := d.domainBasis.toBasis.constr F
    (fun i => (T.singularValues i : F) • d.domainBasis i)
  let u := d.domainBasis.equiv d.codomainBasis (Equiv.refl _)
  have hP : ∀ i, P (d.domainBasis i) =
      (T.singularValues i : F) • d.domainBasis i := by
    intro i
    exact d.domainBasis.toBasis.constr_basis F _ i
  have hp : _root_.D05.positiveSemidefinite P := by
    apply (D05.M14.Positive.positiveSemidefinite_iff_mathlib P).mpr
    apply (LinearMap.posSemidef_toMatrix_iff d.domainBasis).mp
    have hm : P.toMatrix d.domainBasis.toBasis d.domainBasis.toBasis =
        Matrix.diagonal (fun i : Fin (Module.finrank F V) => (T.singularValues i : F)) := by
      ext i j
      by_cases hij : i = j <;>
        simp [LinearMap.toMatrix_apply, hP, hij, RCLike.real_smul_eq_coe_mul]
    rw [hm, Matrix.posSemidef_diagonal_iff]
    intro i
    exact RCLike.ofReal_nonneg.mpr (T.singularValues_nonneg i)
  have hu : _root_.D05.IsUnitaryMap u.toLinearMap :=
    ⟨fun x y => u.inner_map_map y x, u.surjective⟩
  have hfac : u.toLinearMap * P = T := by
    apply d.domainBasis.toBasis.ext
    intro i
    change u (P (d.domainBasis i)) = T (d.domainBasis i)
    rw [hP, map_smul]
    simp only [u, OrthonormalBasis.equiv_apply_basis, Equiv.refl_apply]
    by_cases hi : i.val < Module.finrank F (LinearMap.range T)
    · exact (d.positive_action ⟨i.val, hi⟩).symm
    · rw [(D05.M14.SingularValues.zero_iff T i.val).mpr (Nat.le_of_not_lt hi),
        RCLike.ofReal_zero, zero_smul, d.zero_action i (Nat.le_of_not_lt hi)]
  refine ⟨P, u.toLinearMap, hp, ?_, hu, hfac⟩
  have ha : LinearMap.adjoint P = P := hp.1.symm
  have hu' := (D05.M13.Unitary.unitary_iff_adjoint_identities u.toLinearMap).mp hu
  change P * P = (LinearMap.adjoint T) * T
  rw [← hfac]
  change P.comp P = ((u.toLinearMap.comp P).adjoint).comp (u.toLinearMap.comp P)
  rw [LinearMap.adjoint_comp, ha]
  ext x
  change P (P x) = P ((LinearMap.adjoint u.toLinearMap) (u (P x)))
  rw [show (LinearMap.adjoint u.toLinearMap) (u (P x)) = P x from
    DFunLike.congr_fun hu'.1 (P x)]

theorem factor_for_positive_root : Specs.D05.M14.Polar.factor_for_positive_root := by
  intro F V _ _ _ _ T P hp hsq
  obtain ⟨Q, U, hq, hqsq, hu, hfac⟩ := exists_polar T
  have hg : _root_.D05.positiveSemidefinite ((LinearMap.adjoint T) * T) :=
    (D05.M14.Positive.positiveSemidefinite_iff_mathlib _).mpr
      T.isPositive_adjoint_comp_self
  have he : P = Q := D05.M14.PositiveRoot.Uniqueness.positive_roots_unique
    _ P Q hg hp hq hsq hqsq
  exact ⟨U, hu, by simpa only [he] using hfac⟩

/-- Bijectivity of a product with a unitary left factor forces bijectivity
of its right factor; this argument also applies on the zero space. -/
theorem right_factor_bijective {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T P U : Module.End F V)
    (hT : Function.Bijective T) (hu : _root_.D05.IsUnitaryMap U)
    (hfac : U * P = T) : Function.Bijective P := by
  have hi := D05.M13.Unitary.isometry_injective U hu.1
  constructor
  · intro x y hxy
    apply hT.1
    rw [← hfac]
    exact congrArg U hxy
  · intro y
    obtain ⟨x, hx⟩ := hT.2 (U y)
    refine ⟨x, hi ?_⟩
    exact (DFunLike.congr_fun hfac x).trans hx

theorem unitary_factor_unique : Specs.D05.M14.Polar.unitary_factor_unique := by
  intro F V _ _ _ _ T P hT _ _ U₁ U₂ hu₁ _ h₁ h₂
  have hs := (right_factor_bijective T P U₁ hT hu₁ h₁).2
  ext y
  obtain ⟨x, rfl⟩ := hs y
  exact (DFunLike.congr_fun h₁ x).trans (DFunLike.congr_fun h₂ x).symm

theorem existsUnique_unitary_factor :
    Specs.D05.M14.Polar.existsUnique_unitary_factor := by
  intro F V _ _ _ _ T P hT hp hsq
  obtain ⟨U, hu, hfac⟩ := factor_for_positive_root T P hp hsq
  exact ⟨U, ⟨hu, hfac⟩, fun U' hU' =>
    unitary_factor_unique T P hT hp hsq U' U hU'.1 hu hU'.2 hfac⟩

theorem invertible_formula : Specs.D05.M14.Polar.invertible_formula := by
  intro F V _ _ _ _ T P U hT hu hfac
  let e := LinearEquiv.ofBijective P (right_factor_bijective T P U hT hu hfac)
  refine ⟨e, rfl, ?_⟩
  ext x
  change U x = T (e.symm x)
  rw [← hfac]
  change U x = U (e (e.symm x))
  rw [e.apply_symm_apply]

/-- Reflection fixes every output of P. If P is not onto, it changes a vector
outside its image, so composing any completion with it gives a different one. -/
theorem singular_nonunique : Specs.D05.M14.Polar.singular_nonunique := by
  intro F V _ _ _ _ T P hT hp hsq
  classical
  obtain ⟨U, hu, hfac⟩ := factor_for_positive_root T P hp hsq
  obtain ⟨u, rfl⟩ := (D05.M13.Unitary.unitary_iff_linearIsometryEquiv U).mp hu
  have hn : ¬ Function.Surjective P := by
    intro hs
    apply hT
    have hsT : Function.Surjective T := by
      rw [← hfac]
      exact u.surjective.comp hs
    exact ⟨(LinearMap.injective_iff_surjective).mpr hsT, hsT⟩
  obtain ⟨x, hx⟩ := not_forall.mp hn
  let r := (LinearMap.range P).reflection
  let v := r.trans u
  refine ⟨u.toLinearMap, v.toLinearMap, hu,
    ⟨fun x y => v.inner_map_map y x, v.surjective⟩, hfac, ?_, ?_⟩
  · ext y
    change u (r (P y)) = T y
    rw [Submodule.reflection_mem_subspace_eq_self (LinearMap.mem_range_self P y)]
    exact DFunLike.congr_fun hfac y
  · intro he
    have hr : r x = x := u.injective (DFunLike.congr_fun he x).symm
    exact hx ((Submodule.reflection_eq_self_iff x).mp hr)

theorem zero_space : Specs.D05.M14.Polar.zero_space := by
  intro F V _ _ _ _ _ T P
  have hT : Function.Bijective T :=
    ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  refine ⟨hT, 1, ?_, fun U _ => Subsingleton.elim _ _⟩
  exact ⟨⟨fun x y => rfl, fun y => ⟨y, rfl⟩⟩,
    Subsingleton.elim _ _⟩

end D05.M14.Polar
