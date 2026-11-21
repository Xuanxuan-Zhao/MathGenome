import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.MinimalZeroMultiplicityLocus
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootDecomposition
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.Sl2Model
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RegularSemisimple
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Algebra.Module.Submodule.Union

/-!
LA-D06, source lines 1799–1878 and 1987–1991. The polynomial locus topology is reused from
LA-D06-PolynomialLocus. Barnes's minimal-Engel argument proves semisimplicity
and the centralizer assertions. Root decomposition and the strict inverse
function theorem then prove equality of toral dimensions. Inner exponentials
are constructed from convergent operator series; their bracket preservation
is proved by a zero-derivative argument, without a Lie-group integration theorem.
-/

universe u
namespace LieAlgebrasAndRepresentations
namespace RegularSemisimple
attribute [local instance 100] LieRing.ofAssociativeRing
open Specs.LieAlgebrasAndRepresentations.MinimalZeroMultiplicityLocus
open Specs.LieAlgebrasAndRepresentations.RegularSemisimple

open private cartan_toral self_centralizing_maximal from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.MaximalTori

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

theorem density : Specs.LieAlgebrasAndRepresentations.RegularSemisimple.density_type.{u} :=
  LieAlgebrasAndRepresentations.MinimalZeroMultiplicityLocus.topology

/-- Bridge from the least attained zero multiplicity to Mathlib's polynomial rank. -/
theorem minimum_eq_rank : minimalZeroMultiplicity L = LieAlgebra.rank ℂ L := by
  apply le_antisymm
  · obtain ⟨x, hx⟩ := LieAlgebra.exists_isRegular ℂ L
    have he := (LieAlgebra.isRegular_iff_natTrailingDegree_charpoly_eq_rank ℂ x).mp hx
    simpa only [zeroMultiplicity, Polynomial.rootMultiplicity_eq_natTrailingDegree', he] using
      (MinimalZeroMultiplicityLocus.minimum L).2 x
  · obtain ⟨x, hx⟩ := (MinimalZeroMultiplicityLocus.minimum L).1
    have he := LieAlgebra.rank_le_natTrailingDegree_charpoly_ad ℂ x
    simpa only [zeroMultiplicity, Polynomial.rootMultiplicity_eq_natTrailingDegree'] using
      he.trans_eq (by simpa only [zeroMultiplicity, Polynomial.rootMultiplicity_eq_natTrailingDegree'] using hx)

theorem mem_locus_iff_isRegular (x : L) :
    x ∈ minimalMultiplicityLocus L ↔ LieAlgebra.IsRegular ℂ x := by
  rw [LieAlgebra.isRegular_iff_natTrailingDegree_charpoly_eq_rank]
  change zeroMultiplicity L x = minimalZeroMultiplicity L ↔ _
  rw [minimum_eq_rank]
  exact (show zeroMultiplicity L x = (LieAlgebra.ad ℂ L x).charpoly.natTrailingDegree from
    Polynomial.rootMultiplicity_eq_natTrailingDegree' ) ▸ Iff.rfl

/-- The minimal Engel subalgebra is Cartan. This specializes Barnes's lemma
already proved in Mathlib; no semisimplicity is assumed in this step. -/
theorem engel_isCartan_of_regular (x : L) (hx : LieAlgebra.IsRegular ℂ x) :
    (LieSubalgebra.engel ℂ x).IsCartanSubalgebra := by
  refine ⟨?_, LieSubalgebra.normalizer_engel _ _⟩
  apply LieSubalgebra.isNilpotent_of_forall_le_engel
  intro y hy
  set Ex : {LieSubalgebra.engel ℂ z | z ∈ LieSubalgebra.engel ℂ x} :=
    ⟨LieSubalgebra.engel ℂ x, x, LieSubalgebra.self_mem_engel _ _, rfl⟩
  suffices IsBot Ex from @this ⟨LieSubalgebra.engel ℂ y, y, hy, rfl⟩
  apply LieAlgebra.engel_isBot_of_isMin
    (Cardinal.natCast_le_aleph0.trans (Cardinal.infinite_iff.mp (inferInstance : Infinite ℂ)))
    (LieSubalgebra.engel ℂ x) Ex le_rfl
  rintro ⟨_, z, hz, rfl⟩ hzx
  have hdim : Module.finrank ℂ (LieSubalgebra.engel ℂ x) ≤
      Module.finrank ℂ (LieSubalgebra.engel ℂ z) := by
    rw [(LieAlgebra.isRegular_iff_finrank_engel_eq_rank ℂ x).mp hx]
    exact LieAlgebra.rank_le_finrank_engel ℂ z
  have he : LieSubalgebra.engel ℂ z = LieSubalgebra.engel ℂ x := by
    apply LieSubalgebra.toSubmodule_injective
    exact Submodule.eq_of_le_of_finrank_le hzx hdim
  exact he.ge

theorem regular_semisimple :
    Specs.LieAlgebrasAndRepresentations.RegularSemisimple.regular_semisimple_type := by
  intro L _ _ _ hss x hx
  letI : LieAlgebra.HasTrivialRadical ℂ L := ⟨hss⟩
  letI := engel_isCartan_of_regular x ((mem_locus_iff_isRegular x).mp hx)
  exact LieAlgebra.IsKilling.isSemisimple_ad_of_mem_isCartanSubalgebra
    (K := ℂ) (H := LieSubalgebra.engel ℂ x) (LieSubalgebra.self_mem_engel ℂ x)

/-- For a semisimple adjoint, generalized zero vectors are actual zero vectors. -/
theorem centralizer_eq_engel (x : L) (hx : (LieAlgebra.ad ℂ L x).IsSemisimple) :
    elementCentralizer x = LieSubalgebra.engel ℂ x := by
  apply LieSubalgebra.toSubmodule_injective
  change LinearMap.ker (LieAlgebra.ad ℂ L x) =
    (LieAlgebra.ad ℂ L x).maxGenEigenspace 0
  rw [hx.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace,
    Module.End.eigenspace_zero]

theorem regular_centralizer :
    Specs.LieAlgebrasAndRepresentations.RegularSemisimple.regular_centralizer_type := by
  intro L _ _ _ hss x hx
  letI : LieAlgebra.HasTrivialRadical ℂ L := ⟨hss⟩
  have hr := (mem_locus_iff_isRegular x).mp hx
  letI := engel_isCartan_of_regular x hr
  have he := centralizer_eq_engel x (regular_semisimple L hss x hx)
  have ht : IsToral (elementCentralizer x) := by
    rw [he]
    exact cartan_toral _
  have hc : toralCentralizer (elementCentralizer x) = elementCentralizer x := by
    apply le_antisymm
    · intro y hy
      exact hy ⟨x, lie_self x⟩
    · intro y hy z
      letI := ht.1
      exact congrArg Subtype.val (trivial_lie_zero (elementCentralizer x)
        (elementCentralizer x) z ⟨y, hy⟩)
  have hm := self_centralizing_maximal (elementCentralizer x) ht hc
  refine ⟨hm, ?_, lie_self x, ?_⟩
  · rw [he, (LieAlgebra.isRegular_iff_finrank_engel_eq_rank ℂ x).mp hr, minimum_eq_rank]
  · intro H hH hxH
    have hle : H ≤ elementCentralizer x := by
      intro y hy
      letI := hH.1.1
      exact congrArg Subtype.val (trivial_lie_zero H H ⟨x, hxH⟩ ⟨y, hy⟩)
    exact le_antisymm hle (hH.2 ht hle)

/-- For a semisimple operator its kernel and range are disjoint. -/
theorem semisimple_disjoint_ker_range (f : Module.End ℂ L) (hf : f.IsSemisimple) :
    Disjoint (LinearMap.ker f) (LinearMap.range f) := by
  rw [Submodule.disjoint_def]
  intro x hx hxR
  obtain ⟨y, rfl⟩ := hxR
  have hy : y ∈ f.maxGenEigenspace 0 := by
    rw [Module.End.mem_maxGenEigenspace]
    refine ⟨2, ?_⟩
    simpa only [zero_smul, sub_zero, pow_two, Module.End.mul_apply] using (LinearMap.mem_ker.mp hx)
  rw [hf.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace,
    Module.End.eigenspace_zero] at hy
  exact hy

/-- The root hyperplane condition makes the range of ad h complementary to H. -/
theorem rootRegular_sup_range (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H) (h : H)
    (hh : h ∈ rootRegular H) :
    H.toSubmodule ⊔ LinearMap.range (LieAlgebra.ad ℂ L (h : L)) = ⊤ := by
  apply top_unique
  rw [← iSup_rootSpace_eq_top H hH.1]
  refine iSup_le fun α => ?_
  by_cases hα : α = 0
  · subst α
    rw [rootSpace_zero hss H hH]
    exact le_sup_left
  · by_cases ha : rootSpace H α = ⊥
    · simp [ha]
    · intro x hx
      apply Submodule.mem_sup_right
      have hn := hh α ⟨hα, ha⟩
      refine ⟨(α h)⁻¹ • x, ?_⟩
      change ⁅(h : L), (α h)⁻¹ • x⁆ = x
      rw [lie_smul, (mem_rootSpace H α x).mp hx h, smul_smul, inv_mul_cancel₀ hn, one_smul]

/-- Centralizers inside a maximal torus are exactly the zero-root summand
when no root vanishes. -/
theorem centralizer_eq_torus_of_rootRegular (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H) (h : H)
    (hh : h ∈ rootRegular H) : elementCentralizer (h : L) = H := by
  let f := LieAlgebra.ad ℂ L (h : L)
  have hle : H.toSubmodule ≤ LinearMap.ker f := by
    intro x hx
    letI := hH.1.1
    exact congrArg Subtype.val (trivial_lie_zero H H h ⟨x, hx⟩)
  have hd := semisimple_disjoint_ker_range f (hH.1.2 h)
  have hs := rootRegular_sup_range hss H hH h hh
  apply LieSubalgebra.toSubmodule_injective
  change LinearMap.ker f = H.toSubmodule
  have he : (H.toSubmodule ⊔ LinearMap.range f) ⊓ LinearMap.ker f = H.toSubmodule := by
    rw [sup_inf_assoc_of_le _ hle, hd.symm.eq_bot, sup_bot_eq]
  rwa [hs, top_inf_eq] at he

/-- Conversely, a vanishing root produces a nonzero centralizing root vector. -/
theorem rootRegular_of_centralizer_eq_torus
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H) (h : H)
    (hc : elementCentralizer (h : L) = H) : h ∈ rootRegular H := by
  intro α hα he
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hα.2
  have hxc : x ∈ elementCentralizer (h : L) := by
    change ⁅(h : L), x⁆ = 0
    rw [(mem_rootSpace H α x).mp hx h, he, zero_smul]
  rw [hc] at hxc
  have ha : ∀ z : H, α z = 0 := by
    intro z
    have hz := (mem_rootSpace H α x).mp hx z
    have hab : ⁅(z : L), x⁆ = 0 := by
      letI := hH.1.1
      exact congrArg Subtype.val (trivial_lie_zero H H z ⟨x, hxc⟩)
    rw [hab, eq_comm, smul_eq_zero] at hz
    exact hz.resolve_right hx0
  exact hα.1 (LinearMap.ext ha)

/-- The linear map occurring in the local conjugation differential. -/
def conjugationLinear (H : LieSubalgebra ℂ L) (M : Submodule ℂ L) (h : H) :
    (M × H) →ₗ[ℂ] L :=
  (((LieAlgebra.ad ℂ L).toLinearMap.flip (h : L)).comp M.subtype).coprod H.toSubmodule.subtype

@[simp] theorem conjugationLinear_apply
    (H : LieSubalgebra ℂ L) (M : Submodule ℂ L) (h : H) (p : M × H) :
    conjugationLinear H M h p = ⁅(p.1 : L), (h : L)⁆ + (p.2 : L) := rfl

/-- An arbitrary linear complement gives the same invertible differential. -/
theorem conjugationLinear_bijective (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H) (M : Submodule ℂ L)
    (hM : IsCompl M H.toSubmodule) (h : H) (hh : h ∈ rootRegular H) :
    Function.Bijective (conjugationLinear H M h) := by
  have hc := centralizer_eq_torus_of_rootRegular hss H hH h hh
  have hd := semisimple_disjoint_ker_range (LieAlgebra.ad ℂ L (h : L)) (hH.1.2 h)
  have hi : Function.Injective (conjugationLinear H M h) := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro p hp
    have he : ⁅(p.1 : L), (h : L)⁆ + (p.2 : L) = 0 := hp
    have hbH : ⁅(p.1 : L), (h : L)⁆ ∈ H := by
      rw [eq_neg_of_add_eq_zero_left he]
      exact H.neg_mem p.2.property
    have hb : ⁅(p.1 : L), (h : L)⁆ = 0 := by
      apply Submodule.disjoint_def.mp hd
      · change ⁅(h : L), ⁅(p.1 : L), (h : L)⁆⁆ = 0
        letI := hH.1.1
        exact congrArg Subtype.val (trivial_lie_zero H H h ⟨_, hbH⟩)
      · exact ⟨-(p.1 : L), by simp only [LieAlgebra.ad_apply, lie_neg, lie_skew]⟩
    have hpH : (p.1 : L) ∈ H := hc.le (show (p.1 : L) ∈ elementCentralizer (h : L) from by
      change ⁅(h : L), (p.1 : L)⁆ = 0
      rw [← lie_skew (h : L) (p.1 : L), hb, neg_zero])
    have hp1 : p.1 = 0 := Subtype.ext
      (Submodule.disjoint_def.mp hM.disjoint (p.1 : L) p.1.property hpH)
    have hp2 : p.2 = 0 := Subtype.ext (show (p.2 : L) = 0 from by simpa only [hb, zero_add] using he)
    exact Prod.ext hp1 hp2
  have hdim : Module.finrank ℂ (M × H) = Module.finrank ℂ L := by
    rw [Module.finrank_prod]
    exact Submodule.finrank_add_eq_of_isCompl hM
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi⟩

section Analytic

/-- Strict differentiability is used, so the inverse function theorem applies
without an unproved continuity-of-derivative hypothesis. -/
theorem conjugation_hasStrictFDerivAt (H : LieSubalgebra ℂ L)
    (M : Submodule ℂ L) (h : H) :
    letI : NormedAddCommGroup L := algebraNorm
    letI : NormedSpace ℂ L :=
      NormedSpace.induced ℂ L (Fin (Module.finrank ℂ L) → ℂ) (Module.finBasis ℂ L).equivFun
    HasStrictFDerivAt (conjugationMap H M)
      (conjugationLinear H M h).toContinuousLinearMap (0, h) := by
  letI : NormedAddCommGroup L := algebraNorm
  letI : NormedSpace ℂ L :=
    NormedSpace.induced ℂ L (Fin (Module.finrank ℂ L) → ℂ) (Module.finBasis ℂ L).equivFun
  letI : NormedAddCommGroup H := H.toSubmodule.normedAddCommGroup
  letI : NormedSpace ℂ H := SubmoduleClass.toNormedSpace H.toSubmodule
  let A : L →L[ℂ] (L →L[ℂ] L) := LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap.comp (LieAlgebra.ad ℂ L).toLinearMap)
  let Y : (M × H) →L[ℂ] (L →L[ℂ] L) :=
    A.comp (M.subtypeL.comp (ContinuousLinearMap.fst ℂ M H))
  let Z : (M × H) →L[ℂ] L :=
    H.toSubmodule.subtypeL.comp (ContinuousLinearMap.snd ℂ M H)
  have hY0 : Y (0, h) = 0 := by simp [Y]
  have he : HasStrictFDerivAt (fun p : M × H => NormedSpace.exp (Y p))
      Y (0, h) := by
    have hExp : HasStrictFDerivAt NormedSpace.exp
        (1 : (L →L[ℂ] L) →L[ℂ] (L →L[ℂ] L)) (Y (0, h)) := by
      rw [hY0]
      exact hasStrictFDerivAt_exp_zero
    have he := hExp.comp (0, h) Y.hasStrictFDerivAt
    simpa only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp] using he
  have hd := he.clm_apply (Z.hasStrictFDerivAt (x := (0, h)))
  convert hd using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro p
    simp only [hY0, NormedSpace.exp_zero, add_apply,
      ContinuousLinearMap.comp_apply, one_apply_eq_self,
      ContinuousLinearMap.flip_apply]
    change ⁅(p.1 : L), (h : L)⁆ + (p.2 : L) = (p.2 : L) + ⁅(p.1 : L), (h : L)⁆
    exact add_comm _ _

/-- A convergent exponential of an inner derivation preserves the bracket.
The proof differentiates exp(-t ad y)[exp(t ad y)x, exp(t ad y)z];
the derivation identity makes its derivative zero. -/
theorem exp_ad_map_lie (y x z : L) :
    letI : NormedAddCommGroup L := algebraNorm
    letI : NormedSpace ℂ L :=
      NormedSpace.induced ℂ L (Fin (Module.finrank ℂ L) → ℂ) (Module.finBasis ℂ L).equivFun
    let D := LinearMap.toContinuousLinearMap (LieAlgebra.ad ℂ L y)
    (NormedSpace.exp D) ⁅x, z⁆ = ⁅(NormedSpace.exp D) x, (NormedSpace.exp D) z⁆ := by
  letI : NormedAddCommGroup L := algebraNorm
  letI : NormedSpace ℂ L :=
    NormedSpace.induced ℂ L (Fin (Module.finrank ℂ L) → ℂ) (Module.finBasis ℂ L).equivFun
  letI : Algebra ℚ (L →L[ℂ] L) := RestrictScalars.algebra ℚ ℂ _
  letI : NormedAlgebra ℚ (L →L[ℂ] L) := NormedAlgebra.restrictScalars ℚ ℂ _
  let D := LinearMap.toContinuousLinearMap (LieAlgebra.ad ℂ L y)
  let E (t : ℂ) := NormedSpace.exp (t • D)
  let N (t : ℂ) := NormedSpace.exp (t • (-D))
  let B : L →L[ℂ] (L →L[ℂ] L) := LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap.comp (LieAlgebra.ad ℂ L).toLinearMap)
  have hE (t : ℂ) : HasDerivAt E (D * E t) t := hasDerivAt_exp_smul_const' D t
  have hN (t : ℂ) : HasDerivAt N (N t * (-D)) t := hasDerivAt_exp_smul_const (-D) t
  have hu (v : L) (t : ℂ) : HasDerivAt (fun s => E s v) (D (E t v)) t := by
    simpa only [ContinuousLinearMap.mul_apply, zero_add, map_zero, add_zero] using
      (hE t).clm_apply (hasDerivAt_const t v)
  let F (t : ℂ) := N t ⁅E t x, E t z⁆
  have hF (t : ℂ) : HasDerivAt F 0 t := by
    have hB := (B.hasFDerivAt.comp_hasDerivAt t (hu x t)).clm_apply (hu z t)
    change HasDerivAt (fun s => ⁅E s x, E s z⁆)
      (⁅D (E t x), E t z⁆ + ⁅E t x, D (E t z)⁆) t at hB
    have hd := (hN t).clm_apply hB
    have hdz : D ⁅E t x, E t z⁆ =
        ⁅D (E t x), E t z⁆ + ⁅E t x, D (E t z)⁆ := leibniz_lie y _ _
    have hz : (N t * (-D)) ⁅E t x, E t z⁆ +
        N t (⁅D (E t x), E t z⁆ + ⁅E t x, D (E t z)⁆) = 0 := by
      rw [← hdz, ContinuousLinearMap.mul_apply]
      simp
    rw [hz] at hd
    exact hd
  have hconst : F 1 = F 0 := is_const_of_deriv_eq_zero
    (fun t => (hF t).differentiableAt) (fun t => (hF t).deriv) 1 0
  have hc : (NormedSpace.exp (-D)) ⁅(NormedSpace.exp D) x, (NormedSpace.exp D) z⁆ =
      ⁅x, z⁆ := by simpa [F, E, N] using hconst
  apply_fun (NormedSpace.exp D) at hc
  have hinv := NormedSpace.exp_add_of_commute (Commute.refl D).neg_right
  rw [add_neg_cancel, NormedSpace.exp_zero] at hinv
  have hinv' (v : L) : (NormedSpace.exp D) ((NormedSpace.exp (-D)) v) = v := by
    change (NormedSpace.exp D * NormedSpace.exp (-D)) v = v
    rw [← hinv]
    rfl
  rw [hinv'] at hc
  exact hc.symm

/-- Convergent inner exponential, with inverse exp(-ad y). -/
noncomputable def expAdEquiv (y : L) : L ≃ₗ⁅ℂ⁆ L := by
  letI : NormedAddCommGroup L := algebraNorm
  letI : NormedSpace ℂ L :=
    NormedSpace.induced ℂ L (Fin (Module.finrank ℂ L) → ℂ) (Module.finBasis ℂ L).equivFun
  letI : Algebra ℚ (L →L[ℂ] L) := RestrictScalars.algebra ℚ ℂ _
  letI : NormedAlgebra ℚ (L →L[ℂ] L) := NormedAlgebra.restrictScalars ℚ ℂ _
  let D := LinearMap.toContinuousLinearMap (LieAlgebra.ad ℂ L y)
  have hl := NormedSpace.exp_add_of_commute (Commute.refl D).neg_left
  have hr := NormedSpace.exp_add_of_commute (Commute.refl D).neg_right
  rw [neg_add_cancel, NormedSpace.exp_zero] at hl
  rw [add_neg_cancel, NormedSpace.exp_zero] at hr
  exact
    { toLinearMap := (NormedSpace.exp D).toLinearMap
      map_lie' := by intro a b; exact exp_ad_map_lie y a b
      invFun := (NormedSpace.exp (-D) : L →L[ℂ] L)
      left_inv := fun x => by
        change (NormedSpace.exp (-D) * NormedSpace.exp D) x = x
        rw [← hl]
        rfl
      right_inv := fun x => by
        change (NormedSpace.exp D * NormedSpace.exp (-D)) x = x
        rw [← hr]
        rfl }

/-- Algebraic zero multiplicity is invariant under a Lie automorphism. -/
theorem zeroMultiplicity_lieEquiv (e : L ≃ₗ⁅ℂ⁆ L) (x : L) :
    zeroMultiplicity L (e x) = zeroMultiplicity L x := by
  have he : LieAlgebra.ad ℂ L (e x) = e.toLinearEquiv.conj (LieAlgebra.ad ℂ L x) := by
    ext z
    obtain ⟨z, rfl⟩ := e.surjective z
    change ⁅e x, e z⁆ = e ⁅x, e.symm (e z)⁆
    rw [e.symm_apply_apply]
    exact (e.map_lie x z).symm
  unfold zeroMultiplicity
  rw [he, LinearEquiv.charpoly_conj]

/-- For semisimple elements algebraic and geometric zero multiplicities agree. -/
theorem zeroMultiplicity_eq_finrank_centralizer (x : L)
    (hs : (LieAlgebra.ad ℂ L x).IsSemisimple) :
    zeroMultiplicity L x = Module.finrank ℂ (elementCentralizer x) := by
  rw [centralizer_eq_engel x hs, LieAlgebra.finrank_engel]
  exact Polynomial.rootMultiplicity_eq_natTrailingDegree'

/-- A finite collection of nonzero roots has a common nonvanishing point,
including when the root set is empty. -/
theorem rootRegular_nonempty (H : LieSubalgebra ℂ L) (hH : IsToral H) :
    (rootRegular H).Nonempty := by
  classical
  letI : Finite (rootSet H) := (rootSet_finite H hH).to_subtype
  obtain ⟨h, hh⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists
    (fun α : rootSet H => α.val) (fun α => by
      by_contra! hn
      exact α.property.1 (LinearMap.ext hn))
  exact ⟨h, fun α hα => hh ⟨α, hα⟩⟩

/-- The local chart is obtained from Mathlib's Banach inverse function theorem.
Completeness follows from finite dimensionality over ℂ. -/
theorem local_conjugation :
    Specs.LieAlgebrasAndRepresentations.RegularSemisimple.local_conjugation_type := by
  intro L _ _ _
  letI : NormedAddCommGroup L := algebraNorm
  letI : NormedSpace ℂ L :=
    NormedSpace.induced ℂ L (Fin (Module.finrank ℂ L) → ℂ) (Module.finBasis ℂ L).equivFun
  intro hss H hH M hM h hh
  letI : NormedAddCommGroup H := H.toSubmodule.normedAddCommGroup
  letI : NormedSpace ℂ H := SubmoduleClass.toNormedSpace H.toSubmodule
  let e := (LinearEquiv.ofBijective (conjugationLinear H M h)
    (conjugationLinear_bijective hss H hH M hM h hh)).toContinuousLinearEquiv
  have he : HasStrictFDerivAt (conjugationMap H M) (e : (M × H) →L[ℂ] L) (0, h) :=
    conjugation_hasStrictFDerivAt H M h
  refine ⟨e, fun p => rfl, he, he.toOpenPartialHomeomorph (conjugationMap H M), rfl, ?_⟩
  exact he.mem_toOpenPartialHomeomorph_source
/-- The root hyperplane complement is open in the ordinary topology on H. -/
theorem rootRegular_isOpen (H : LieSubalgebra ℂ L) (hH : IsToral H) :
    letI : NormedAddCommGroup L := algebraNorm
    letI : NormedSpace ℂ L :=
      NormedSpace.induced ℂ L (Fin (Module.finrank ℂ L) → ℂ) (Module.finBasis ℂ L).equivFun
    IsOpen (rootRegular H) := by
  letI : NormedAddCommGroup L := algebraNorm
  letI : NormedSpace ℂ L :=
    NormedSpace.induced ℂ L (Fin (Module.finrank ℂ L) → ℂ) (Module.finBasis ℂ L).equivFun
  letI : NormedAddCommGroup H := H.toSubmodule.normedAddCommGroup
  letI : NormedSpace ℂ H := SubmoduleClass.toNormedSpace H.toSubmodule
  letI : Finite (rootSet H) := (rootSet_finite H hH).to_subtype
  have he : rootRegular H = ⋂ α : rootSet H, {h : H | α.val h ≠ 0} := by
    ext h
    simp only [rootRegular, Set.mem_setOf_eq, Set.mem_iInter]
    exact ⟨fun hh α => hh α.val α.property, fun hh α hα => hh ⟨α, hα⟩⟩
  rw [he]
  exact isOpen_iInter_of_finite fun α =>
    (α.val.continuous_of_finiteDimensional).isOpen_preimage _ isOpen_ne

/-- The local conjugation chart meets the dense minimum-multiplicity locus.
Multiplicity is constant along inner conjugation, so every maximal torus
has the minimum zero multiplicity as its dimension. -/
theorem toral_rank :
    Specs.LieAlgebrasAndRepresentations.RegularSemisimple.toral_rank_type := by
  intro L _ _ _ hss H hH
  letI : NormedAddCommGroup L := algebraNorm
  letI : NormedSpace ℂ L :=
    NormedSpace.induced ℂ L (Fin (Module.finrank ℂ L) → ℂ) (Module.finBasis ℂ L).equivFun
  letI : NormedAddCommGroup H := H.toSubmodule.normedAddCommGroup
  letI : NormedSpace ℂ H := SubmoduleClass.toNormedSpace H.toSubmodule
  obtain ⟨M, hM⟩ := H.toSubmodule.exists_isCompl
  obtain ⟨h, hh⟩ := rootRegular_nonempty H hH.1
  obtain ⟨e, he, hd, φ, hφ, hs⟩ := local_conjugation L hss H hH M hM.symm h hh
  let V : Set (M × H) := {p | p.2 ∈ rootRegular H}
  have hV : IsOpen V := (rootRegular_isOpen H hH.1).preimage continuous_snd
  have hU := φ.isOpen_image_source_inter hV
  have hn : (φ '' (φ.source ∩ V)).Nonempty :=
    ⟨φ (0, h), ⟨(0, h), ⟨hs, hh⟩, rfl⟩⟩
  obtain ⟨x, hxU, hx⟩ := (MinimalZeroMultiplicityLocus.topology L).2.1.inter_open_nonempty
    _ hU hn
  obtain ⟨p, hp, rfl⟩ := hxU
  have hmult : zeroMultiplicity L (φ p) = zeroMultiplicity L (p.2 : L) := by
    rw [hφ]
    change zeroMultiplicity L (expAdEquiv (p.1 : L) (p.2 : L)) = _
    exact zeroMultiplicity_lieEquiv _ _
  have hnz := zeroMultiplicity_eq_finrank_centralizer (p.2 : L) (hH.1.2 p.2)
  rw [centralizer_eq_torus_of_rootRegular hss H hH p.2 hp.2] at hnz
  exact hnz.symm.trans (hmult.symm.trans hx)

/-- Restriction of the minimal-multiplicity locus to a maximal torus is
exactly the complement of the root hyperplanes. -/
theorem toral_regular :
    Specs.LieAlgebrasAndRepresentations.RegularSemisimple.toral_regular_type := by
  intro L _ _ _ hss H hH
  ext h
  constructor
  · intro hh
    have hc := (regular_centralizer L hss (h : L) hh).2.2.2 H hH h.property
    exact rootRegular_of_centralizer_eq_torus H hH h hc.symm
  · intro hh
    change zeroMultiplicity L (h : L) = minimalZeroMultiplicity L
    rw [zeroMultiplicity_eq_finrank_centralizer (h : L) (hH.1.2 h),
      centralizer_eq_torus_of_rootRegular hss H hH h hh, toral_rank L hss H hH]

end Analytic

/-- Kernel dimensions cannot decrease below their value on a dense locus:
rank is lower semicontinuous for finite-dimensional linear maps. -/
theorem centralizer_lower_bound :
    Specs.LieAlgebrasAndRepresentations.RegularSemisimple.centralizer_lower_bound_type := by
  intro L _ _ _ hss y
  letI : NormedAddCommGroup L := algebraNorm
  letI : NormedSpace ℂ L :=
    NormedSpace.induced ℂ L (Fin (Module.finrank ℂ L) → ℂ) (Module.finBasis ℂ L).equivFun
  let A : L →L[ℂ] (L →L[ℂ] L) := LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap.comp (LieAlgebra.ad ℂ L).toLinearMap)
  have hA (x : L) : (A x).toLinearMap = LieAlgebra.ad ℂ L x := rfl
  by_contra! hy
  let n := Module.finrank ℂ L - minimalZeroMultiplicity L + 1
  have ho : IsOpen {x : L | (n : Cardinal) ≤ (A x).toLinearMap.rank} :=
    (isOpen_setOfPred_nat_le_rank (𝕜 := ℂ) (E := L) (F := L) n).preimage A.continuous
  have hdim (x : L) := (LieAlgebra.ad ℂ L x).finrank_range_add_finrank_ker
  have hrle : minimalZeroMultiplicity L ≤ Module.finrank ℂ L := by
    rw [minimum_eq_rank]
    exact LieAlgebra.rank_le_finrank ℂ L
  have hyU : y ∈ {x : L | (n : Cardinal) ≤ (A x).toLinearMap.rank} := by
    change (n : Cardinal) ≤ (A y).toLinearMap.rank
    rw [hA, LinearMap.rank, ← Module.finrank_eq_rank]
    norm_cast
    have he : Module.finrank ℂ (LinearMap.ker (LieAlgebra.ad ℂ L y)) =
        Module.finrank ℂ (elementCentralizer y) := rfl
    dsimp [n]
    have := hdim y
    omega
  obtain ⟨x, hxU, hx⟩ := (MinimalZeroMultiplicityLocus.topology L).2.1.inter_open_nonempty
    _ ho ⟨y, hyU⟩
  have hxrank : n ≤ Module.finrank ℂ (LieAlgebra.ad ℂ L x).range := by
    change (n : Cardinal) ≤ (A x).toLinearMap.rank at hxU
    rw [hA, LinearMap.rank, ← Module.finrank_eq_rank] at hxU
    exact_mod_cast hxU
  have hxc := (regular_centralizer L hss x hx).2.1
  have he : Module.finrank ℂ (LinearMap.ker (LieAlgebra.ad ℂ L x)) =
      Module.finrank ℂ (elementCentralizer x) := rfl
  have := hdim x
  dsimp [n] at hxrank
  omega

/-- The upper root vector in the trace-zero matrix model has minimum ordinary
centralizer dimension and lies outside the minimum algebraic-multiplicity locus. -/
theorem centralizer_minimum_boundary :
    Specs.LieAlgebrasAndRepresentations.RegularSemisimple.centralizer_minimum_boundary_type := by
  classical
  change Module.finrank ℂ (elementCentralizer (sl2_e ℂ)) = 1 ∧
    (∀ x : sl2 ℂ, Module.finrank ℂ (elementCentralizer (sl2_e ℂ)) ≤
      Module.finrank ℂ (elementCentralizer x)) ∧
    minimalZeroMultiplicity (sl2 ℂ) = 1 ∧
    zeroMultiplicity (sl2 ℂ) (sl2_e ℂ) = 3 ∧
    sl2_e ℂ ∉ minimalMultiplicityLocus (sl2 ℂ)
  obtain ⟨b, he, hf, hh⟩ := sl2_basis ℂ
  obtain ⟨hhe, hhf, hef⟩ := sl2_relations ℂ
  have heh : ⁅sl2_e ℂ, sl2_h ℂ⁆ = (-2 : ℂ) • sl2_e ℂ := by
    rw [← lie_skew, hhe, neg_smul]
  have e0 : LieAlgebra.ad ℂ (sl2 ℂ) (sl2_e ℂ) (b 0) = 0 := by
    simp [he]
  have e1 : LieAlgebra.ad ℂ (sl2 ℂ) (sl2_e ℂ) (b 1) = b 2 := by
    rw [hf, hh, LieAlgebra.ad_apply, hef]
  have e2 : LieAlgebra.ad ℂ (sl2 ℂ) (sl2_e ℂ) (b 2) = (-2 : ℂ) • b 0 := by
    rw [hh, he, LieAlgebra.ad_apply, heh]
  have h0 : LieAlgebra.ad ℂ (sl2 ℂ) (sl2_h ℂ) (b 0) = (2 : ℂ) • b 0 := by
    rw [he, LieAlgebra.ad_apply, hhe]
  have h1 : LieAlgebra.ad ℂ (sl2 ℂ) (sl2_h ℂ) (b 1) = (-2 : ℂ) • b 1 := by
    rw [hf, LieAlgebra.ad_apply, hhf]
  have h2 : LieAlgebra.ad ℂ (sl2 ℂ) (sl2_h ℂ) (b 2) = 0 := by
    simp [hh]
  have eMatrix : LinearMap.toMatrix b b (LieAlgebra.ad ℂ (sl2 ℂ) (sl2_e ℂ)) =
      !![0, 0, -2; 0, 0, 0; 0, 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [LinearMap.toMatrix_apply, e0, e1, e2, Module.Basis.repr_self_apply]
  have hMatrix : LinearMap.toMatrix b b (LieAlgebra.ad ℂ (sl2 ℂ) (sl2_h ℂ)) =
      Matrix.diagonal ![2, -2, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [LinearMap.toMatrix_apply, h0, h1, h2, Module.Basis.repr_self_apply,
        Matrix.diagonal_apply]
  have hspan : (elementCentralizer (sl2_e ℂ)).toSubmodule = ℂ ∙ sl2_e ℂ := by
    apply le_antisymm
    · intro x hx
      change LieAlgebra.ad ℂ (sl2 ℂ) (sl2_e ℂ) x = 0 at hx
      have hc := LinearMap.toMatrix_mulVec_repr b b
        (LieAlgebra.ad ℂ (sl2 ℂ) (sl2_e ℂ)) x
      rw [hx, map_zero, eMatrix] at hc
      have hc₁ : b.repr x 1 = 0 := by
        simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using congrFun hc (2 : Fin 3)
      have hc₂ : b.repr x 2 = 0 := by
        simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using congrFun hc (0 : Fin 3)
      refine Submodule.mem_span_singleton.mpr ⟨b.repr x 0, ?_⟩
      simpa only [Fin.sum_univ_three, hc₁, hc₂, zero_smul, add_zero, he] using b.sum_repr x
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr (lie_self (sl2_e ℂ))
  have he_ne : sl2_e ℂ ≠ 0 := he ▸ b.ne_zero 0
  have hdim : Module.finrank ℂ (elementCentralizer (sl2_e ℂ)) = 1 := by
    change Module.finrank ℂ ((elementCentralizer (sl2_e ℂ)).toSubmodule) = 1
    rw [hspan, finrank_span_singleton he_ne]
  have hpos (x : sl2 ℂ) : 1 ≤ Module.finrank ℂ (elementCentralizer x) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    by_cases hx : x = 0
    · subst x
      exact ⟨⟨sl2_e ℂ, zero_lie _⟩, fun hz => he_ne (congrArg Subtype.val hz)⟩
    · exact ⟨⟨x, lie_self x⟩, fun hz => hx (congrArg Subtype.val hz)⟩
  have hmult (x : sl2 ℂ) : 1 ≤ zeroMultiplicity (sl2 ℂ) x := by
    let f := LieAlgebra.ad ℂ (sl2 ℂ) x
    have hle : LinearMap.ker f ≤ f.maxGenEigenspace 0 := by
      rw [← Module.End.eigenspace_zero]
      exact Module.End.eigenspace_le_maxGenEigenspace
    have hd := Submodule.finrank_mono hle
    rw [LinearMap.finrank_maxGenEigenspace_eq] at hd
    exact (hpos x).trans hd
  have eMult : zeroMultiplicity (sl2 ℂ) (sl2_e ℂ) = 3 := by
    unfold zeroMultiplicity
    rw [← LinearMap.charpoly_toMatrix _ b, eMatrix]
    have hp : (!![0, 0, -2; 0, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) ℂ).charpoly =
        Polynomial.X ^ 3 := by
      rw [Matrix.charpoly, Matrix.det_fin_three]
      simp [pow_succ]
    rw [hp]
    simpa using Polynomial.rootMultiplicity_X_sub_C_pow (R := ℂ) 0 3
  have hMult : zeroMultiplicity (sl2 ℂ) (sl2_h ℂ) = 1 := by
    unfold zeroMultiplicity
    rw [← LinearMap.charpoly_toMatrix _ b, hMatrix, Matrix.charpoly_diagonal]
    simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two]
    let p : Polynomial ℂ := (Polynomial.X - Polynomial.C 2) *
      (Polynomial.X - Polynomial.C (-2))
    have hp : ¬ p.IsRoot 0 := by norm_num [p, Polynomial.IsRoot]
    have hp0 : p ≠ 0 := by
      intro hz
      exact hp (by simp [hz])
    change (p * (Polynomial.X - Polynomial.C 0)).rootMultiplicity 0 = 1
    rw [← pow_one (Polynomial.X - Polynomial.C (0 : ℂ)),
      Polynomial.rootMultiplicity_mul_X_sub_C_pow hp0,
      Polynomial.rootMultiplicity_eq_zero hp, zero_add]
  obtain ⟨x, hx⟩ := (MinimalZeroMultiplicityLocus.minimum (sl2 ℂ)).1
  have hmin : minimalZeroMultiplicity (sl2 ℂ) = 1 :=
    le_antisymm ((MinimalZeroMultiplicityLocus.minimum (sl2 ℂ)).2 (sl2_h ℂ) |>.trans_eq hMult)
      ((hmult x).trans_eq hx)
  refine ⟨hdim, fun x => hdim.symm ▸ hpos x, hmin, eMult, ?_⟩
  change zeroMultiplicity (sl2 ℂ) (sl2_e ℂ) ≠ minimalZeroMultiplicity (sl2 ℂ)
  rw [eMult, hmin]
  decide

end RegularSemisimple
end LieAlgebrasAndRepresentations
