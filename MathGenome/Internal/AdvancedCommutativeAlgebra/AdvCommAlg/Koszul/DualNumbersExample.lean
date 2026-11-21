import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.DualNumbersExample
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.NullHomotopy

open CategoryTheory
open scoped TensorProduct
noncomputable section
universe u v
namespace AdvCommAlg.Koszul

theorem singleton_differential {R : Type u} [CommRing R] (a : R)
    (z : (⋀[R]^1 (Fin 1 → R)) ⊗[R] R) :
    singletonZeroEquiv a (coefficientDifferential R [a] 0 z) =
      a * singletonOneEquiv a z := by
  induction z using TensorProduct.inductionOn with
  | tmul b r =>
    change singletonZeroEquiv a (coefficientDifferential R [a] 0 (b ⊗ₜ[R] r)) = _
    have hd := degreeZeroBoundary_tmul R [a] b r
    change singletonZeroEquiv a (coefficientDifferential R [a] 0 (b ⊗ₜ[R] r)) = _ at hd
    rw [hd]
    change listForm [a] (exteriorPower.oneEquiv R (Fin 1 → R) b) * r =
      a * (exteriorPower.oneEquiv R (Fin 1 → R) b 0 * r)
    rw [listForm_sum]
    simp [mul_comm, mul_left_comm]
  | add z w hz hw =>
    rw [(coefficientDifferential R [a] 0).map_add, (singletonZeroEquiv a).map_add,
      (singletonOneEquiv a).map_add, mul_add, hz, hw]

theorem singleton_description : Specs.AdvCommAlg.Koszul.singletonDescription.{u} := by
  intro R _ a
  exact ⟨singleton_differential a, fun q hq => coefficientComplex_vanish R [a] q (by simpa)⟩

theorem containsUnit_contractible : Specs.AdvCommAlg.Koszul.containsUnitContractible.{u,v} := by
  intro R _ M _ _ x hx
  obtain ⟨a, ha, hu⟩ := hx
  apply unitIdeal_contractible M x
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ha) hu

theorem dual_nonzero : Specs.AdvCommAlg.Koszul.dualNonzero.{u} := by
  intro k _
  have he : (DualNumber.eps : DualNumber k) ≠ 0 := by
    intro h
    have := congrArg TrivSqZeroExt.snd h
    simp at this
  refine ⟨he, ?_⟩
  intro h
  have hm : (DualNumber.eps : DualNumber k) ∈ (Ideal.span {DualNumber.eps} : Ideal (DualNumber k)) :=
    Ideal.subset_span (Set.mem_singleton _)
  rw [h] at hm
  exact he hm

/-- With no incoming boundary, singleton H₁ is the kernel of its sole differential. -/
def singletonHomologyOneKernelEquiv {R : Type u} [CommRing R] (a : R) :
    homology R [a] 1 ≃ₗ[R] LinearMap.ker (coefficientDifferential R [a] 0) := by
  let C := coefficientComplex R [a]
  let S := C.sc 1
  have hp : (ComplexShape.down ℕ).prev 1 = 2 := ComplexShape.prev_eq' _ rfl
  have hn : (ComplexShape.down ℕ).next 1 = 0 := ComplexShape.next_eq' _ rfl
  have hf : S.f = 0 := by
    let hi : Subsingleton (C.X ((ComplexShape.down ℕ).prev 1)) := by
      rw [hp]
      exact coefficientComplex_vanish R [a] 2 (by simp)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    have hz : z = 0 := @Subsingleton.elim (C.X ((ComplexShape.down ℕ).prev 1)) hi z 0
    rw [hz]
    exact map_zero _
  let L := ShortComplex.LeftHomologyData.ofIsLimitKernelFork S hf
    (ModuleCat.kernelCone S.g) (ModuleCat.kernelIsLimit S.g)
  have hL : L.H = ModuleCat.of R (LinearMap.ker (C.d 1 0).hom) := by
    dsimp [L, S, C, HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
      HomologicalComplex.shortComplexFunctor']
    rw [hn]
    rfl
  exact (L.homologyIso ≪≫ eqToIso hL).toLinearEquiv

/-- The standard degree-one coordinate carries cycles to elements killed by a. -/
def singletonCyclesEquiv {R : Type u} [CommRing R] (a : R) :
    LinearMap.ker (coefficientDifferential R [a] 0) ≃ₗ[R]
      LinearMap.ker (LinearMap.mulLeft R a) := by
  apply (singletonOneEquiv a).ofSubmodules
  ext r
  constructor
  · rintro ⟨z, hz, rfl⟩
    change a * singletonOneEquiv a z = 0
    rw [← singleton_differential a z]
    rw [LinearMap.mem_ker.mp hz, map_zero]
  · intro hr
    refine ⟨(singletonOneEquiv a).symm r, ?_, (singletonOneEquiv a).apply_symm_apply r⟩
    apply LinearMap.mem_ker.mpr
    apply (singletonZeroEquiv a).injective
    have hh := singleton_differential a ((singletonOneEquiv a).symm r)
    rw [hh, LinearEquiv.apply_symm_apply, map_zero]
    exact hr

/-- Multiplication by ε kills exactly the ideal (ε). -/
theorem dual_kernel (k : Type u) [Field k] :
    LinearMap.ker (LinearMap.mulLeft (DualNumber k) DualNumber.eps) =
      (Ideal.span {DualNumber.eps} : Ideal (DualNumber k)) := by
  ext z
  rw [LinearMap.mem_ker, LinearMap.mulLeft_apply, Ideal.mem_span_singleton,
    ← DualNumber.fst_eq_zero_iff_eps_dvd]
  constructor
  · intro h
    have hs := congrArg TrivSqZeroExt.snd h
    simpa using hs
  · intro h
    ext <;> simp [h]

theorem dual_homology_one : Specs.AdvCommAlg.Koszul.dualHomologyOne.{u} := by
  intro k _
  exact ⟨((singletonHomologyOneKernelEquiv (DualNumber.eps : DualNumber k)).trans
    (singletonCyclesEquiv DualNumber.eps)).trans
      (LinearEquiv.ofEq _ _ (dual_kernel k))⟩

/-- The augmentation to the residue field, retaining the dual-number scalar action. -/
def dualResidueMap (k : Type u) [Field k] : DualNumber k →ₗ[DualNumber k] dualResidue k where
  toFun := TrivSqZeroExt.fst
  map_add' := TrivSqZeroExt.fst_add
  map_smul' r z := by
    change (r * z).fst = r.fst * z.fst
    rfl

theorem dualResidueMap_ker (k : Type u) [Field k] :
    LinearMap.ker (dualResidueMap k) = listSubmodule (DualNumber k) [DualNumber.eps] := by
  have hi : listSubmodule (DualNumber k) [(DualNumber.eps : DualNumber k)] =
      (Ideal.span {DualNumber.eps} : Ideal (DualNumber k)) := by
    simp [listSubmodule, listIdeal]
  rw [hi]
  ext z
  change z.fst = 0 ↔ _
  rw [Ideal.mem_span_singleton, DualNumber.fst_eq_zero_iff_eps_dvd]

theorem dual_homology_zero : Specs.AdvCommAlg.Koszul.dualHomologyZero.{u} := by
  intro k _
  have hs : Function.Surjective (dualResidueMap k) := by
    intro r
    exact ⟨TrivSqZeroExt.inl r, rfl⟩
  exact ⟨(homologyZeroEquiv (DualNumber k) [DualNumber.eps]).trans
    ((Submodule.Quotient.equiv _ _ (LinearEquiv.refl (DualNumber k) (DualNumber k))
      (by simpa using (dualResidueMap_ker k).symm)).trans
        ((dualResidueMap k).quotKerEquivOfSurjective hs))⟩

/-- The concrete dual numbers realize exactly the polynomial quotient in RK-13. -/
theorem dual_presentation : Specs.AdvCommAlg.Koszul.dualPresentation.{u} := by
  intro k _
  let I : Ideal (Polynomial k) := Ideal.span {Polynomial.X ^ 2}
  let t : dualPolynomialQuotient k := Ideal.Quotient.mk I Polynomial.X
  have ht : t * t = 0 := by
    change Ideal.Quotient.mk I Polynomial.X * Ideal.Quotient.mk I Polynomial.X = 0
    rw [← map_mul, ← pow_two]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have heval : ∀ p ∈ I, Polynomial.aeval (DualNumber.eps : DualNumber k) p = 0 := by
    change I ≤ RingHom.ker (Polynomial.aeval (DualNumber.eps : DualNumber k)).toRingHom
    apply Ideal.span_le.mpr
    rintro p (rfl : p = Polynomial.X ^ 2)
    simp
  let f : dualPolynomialQuotient k →ₐ[k] DualNumber k :=
    Ideal.Quotient.liftₐ I (Polynomial.aeval DualNumber.eps) heval
  let g : DualNumber k →ₐ[k] dualPolynomialQuotient k :=
    DualNumber.lift ⟨(Algebra.ofId k _, t), ht, fun _ => Commute.all _ _⟩
  have hf : f t = DualNumber.eps := by
    change Polynomial.aeval (DualNumber.eps : DualNumber k) Polynomial.X = _
    exact Polynomial.aeval_X _
  have hg : g DualNumber.eps = t := DualNumber.lift_apply_eps _
  have hfg : f.comp g = AlgHom.id k (DualNumber k) := by
    apply DualNumber.algHom_ext
    change f (g DualNumber.eps) = DualNumber.eps
    rw [hg, hf]
  have hgf : g.comp f = AlgHom.id k (dualPolynomialQuotient k) := by
    apply Ideal.Quotient.algHom_ext
    apply Polynomial.algHom_ext
    change g (f t) = t
    rw [hf, hg]
  exact ⟨AlgEquiv.ofAlgHom f g hfg hgf, hf⟩

end AdvCommAlg.Koszul
