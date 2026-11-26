import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.IsolatedTorSupport
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.RegularFiniteProjectiveDimension
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.RingTheory.Finiteness.Small

noncomputable section

open CategoryTheory
open scoped BigOperators TensorProduct
open CommutativeAlgebraNotes.Intersection.IsolatedTorSupport
  (Tor torLeftEquiv torRightEquiv torSymmetryEquiv tor_finite_length_of_tensor)
open P103.Specs.Ch10.Comparison (LeftResolution)
open P103.Specs.Ch10.Complexes (Homology cycles)
open P103.Specs.Ch12.TorBaseChange (coefficientComplex commutativeTor)

namespace CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler

universe u v w

variable {R : Type u} [CommRing R]

/-- The alternating length of canonical Tor through the given degree, inclusive. -/
abbrev cutoffEuler (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) (d : ℕ) : ℤ :=
  Specs.cutoffEuler M N d

/-- The natural-number dimension of a regular local ring. -/
abbrev regularLocalDimension (R : Type u) [CommRing R] [IsRegularLocalRing R] : ℕ :=
  Specs.regularLocalDimension R

theorem ringKrullDim_eq_regularLocalDimension (R : Type u) [CommRing R]
    [IsRegularLocalRing R] :
    ringKrullDim R = (regularLocalDimension R : WithBot ℕ∞) :=
  (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm

/-- The isolated-intersection Euler characteristic over a regular local ring. -/
abbrev intersectionEuler [IsRegularLocalRing R]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) : ℤ :=
  Specs.intersectionEuler M N

theorem intersectionEuler_eq_cutoff [IsRegularLocalRing R]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) (d : ℕ)
    (hd : ringKrullDim R = (d : WithBot ℕ∞)) :
    intersectionEuler M N = cutoffEuler M N d := by
  have h : regularLocalDimension R = d := by
    exact_mod_cast (ringKrullDim_eq_regularLocalDimension R).symm.trans hd
  change cutoffEuler M N (regularLocalDimension R) = cutoffEuler M N d
  rw [h]

theorem tor_finite_length [IsRegularLocalRing R]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) [Module.Finite R M] [Module.Finite R N]
    (h : IsFiniteLength R (M ⊗[R] N)) (i : ℕ) : IsFiniteLength R (Tor M N i) :=
  tor_finite_length_of_tensor M N h i

/-- Retain the complex of a categorical resolution and transport its augmentation
to the given linearly equivalent module. -/
private def leftResolutionOfEquiv (M : ModuleCat.{v} R)
    (A : ModuleCat.{max u v} R) (P : ProjectiveResolution A) (e : A ≃ₗ[R] M) :
    LeftResolution R M where
  complex := P.complex
  ε := e.toLinearMap.comp (P.π.f 0).hom
  surjective := e.surjective.comp ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  exact_zero := P.exact₀.moduleCat_range_eq_ker.trans (e.ker_comp (P.π.f 0).hom).symm
  exact_succ n := (P.exact_succ n).moduleCat_range_eq_ker

private theorem homology_subsingleton_of_term (C : ChainComplex (ModuleCat R) ℕ)
    (i : ℕ) [Subsingleton (C.X i)] : Subsingleton (Homology C i) := by
  have : Subsingleton (cycles C i) := Subtype.coe_injective.subsingleton
  infer_instance

/-- Over a regular local ring of dimension `d`, a finite first argument
forces all Tor groups in degrees above `d` to vanish. -/
theorem tor_vanishes_above [IsRegularLocalRing R]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) [Module.Finite R M] (d : ℕ)
    (hd : ringKrullDim R = (d : WithBot ℕ∞)) (i : ℕ) (hi : d < i) :
    Subsingleton (Tor M N i) := by
  cases subsingleton_or_nontrivial M with
  | inl hM =>
    let := hM
    let Q := P103.Ch11.ExtTorDefinitions.resolutionFamily R N
    have hterm : Subsingleton ((coefficientComplex (S := R) Q.val.complex M).X i) :=
      inferInstanceAs (Subsingleton (M ⊗[R] Q.val.complex.X i))
    have : Subsingleton (commutativeTor Q.val M i) := homology_subsingleton_of_term _ i
    exact (torRightEquiv M N Q.val Q.property i).injective.subsingleton
  | inr hM =>
    let : Small.{u} M := Module.Finite.small.{u} R M
    let A : ModuleCat.{u} R := ModuleCat.of R (Shrink.{u} M)
    let e : A ≃ₗ[R] M := Shrink.linearEquiv R M
    let : Nontrivial A := e.symm.injective.nontrivial
    let : Module.Finite R A := Module.Finite.equiv e.symm
    obtain ⟨depth, hdepth⟩ := AdvCommAlg.Depth.exists_depth_eq_nat A
    obtain ⟨P, _, _, hP⟩ :=
      AdvCommAlg.CohenMacaulay.regularLocal_exists_finiteFreeResolution R A d depth hd hdepth
    let F : ModuleCat.{u} R ⥤ ModuleCat.{max u v} R := ModuleCat.uliftFunctor.{v, u} R
    let P' := F.mapProjectiveResolution P
    let Q := leftResolutionOfEquiv M (F.obj A) P' (ULift.moduleEquiv.trans e)
    have hQ : Q.IsProjective := by
      intro j
      change Module.Projective R (P'.complex.X j)
      infer_instance
    have : Subsingleton (P.complex.X i) := hP i ((Nat.sub_le d depth).trans_lt hi)
    have : Subsingleton (Q.complex.X i) :=
      inferInstanceAs (Subsingleton (ULift.{v} (P.complex.X i)))
    have hterm : Subsingleton ((coefficientComplex (S := R) Q.complex N).X i) :=
      inferInstanceAs (Subsingleton (N ⊗[R] Q.complex.X i))
    have : Subsingleton (commutativeTor Q N i) := homology_subsingleton_of_term _ i
    exact (torLeftEquiv M N Q hQ i).injective.subsingleton

theorem cutoffEuler_symm (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) (d : ℕ) :
    cutoffEuler M N d = cutoffEuler N M d := by
  unfold cutoffEuler Specs.cutoffEuler
  apply Finset.sum_congr rfl
  intro i _
  rw [(torSymmetryEquiv M N i).length_eq]

theorem cutoffEuler_eq_of_vanishes_above (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (d d' : ℕ) (hle : d ≤ d') (h : ∀ i : ℕ, d < i → Subsingleton (Tor M N i)) :
    cutoffEuler M N d' = cutoffEuler M N d := by
  unfold cutoffEuler Specs.cutoffEuler
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hle))
  intro i _ hi
  have := h i (by simpa only [Finset.mem_range, Nat.lt_succ_iff, not_le] using hi)
  rw [Module.length_eq_zero]
  simp

theorem intersectionEuler_symm [IsRegularLocalRing R]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R M] [Module.Finite R N] (_h : IsFiniteLength R (M ⊗[R] N)) :
    intersectionEuler M N = intersectionEuler N M :=
  cutoffEuler_symm M N (regularLocalDimension R)

end CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler
