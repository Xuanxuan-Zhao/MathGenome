import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleIdealDecomposition
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.Enveloping
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ModuleCasimir
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-! LA-C02: the module-dependent Casimir over arbitrary characteristic-zero
fields. The trace-dual contraction is proved directly with finite sums, without
PBW or complete reducibility. -/

noncomputable section
open scoped Classical
universe u v w t
namespace LieAlgebrasAndRepresentations.ModuleCasimir
open _root_.Shared.Lie
attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type u) (G : Type v) (M : Type w)
  [Field k] [CharZero k] [LieRing G] [LieAlgebra k G] [FiniteDimensional k G]
  [AddCommGroup M] [Module k M] [FiniteDimensional k M]
  [LieRingModule G M] [LieModule k G M]

theorem support_isCompl (hg : IsSemisimple k G) :
    IsCompl (LieModule.toEnd k G M).ker (support k G M) :=
  ideal_isCompl_killingCompl k G hg _

/-- Restriction of the Killing form to any ideal of a semisimple algebra is
nondegenerate; its value is the Killing form of the ideal itself. -/
theorem ideal_isKilling (hg : IsSemisimple k G) (I : LieIdeal k G) :
    LieAlgebra.IsKilling k I := by
  have hcompl := ideal_isCompl_killingCompl k G hg I
  have hi : (_root_.killingForm k I).Nondegenerate := by
    apply (LieModule.traceForm_isSymm k I I).isRefl.nondegenerate_iff_separatingLeft.mpr
    intro x hx
    apply Subtype.ext
    have hm : (x : G) ∈ I ⊓ I.killingCompl := by
      refine ⟨x.property, ?_⟩
      change (x : G) ∈ I.killingCompl
      rw [LieIdeal.mem_killingCompl]
      intro y hy
      change killingForm k G y (x : G) = 0
      rw [← killingForm_restrict_ideal k G I ⟨y, hy⟩ x]
      exact (LieModule.traceForm_comm k I I _ _).trans (hx ⟨y, hy⟩)
    rw [hcompl.disjoint.eq_bot] at hm
    exact hm
  haveI : LieAlgebra.HasTrivialRadical k I :=
    ⟨(killingForm_nondegenerate_iff_radical_eq_bot k I).mp hi⟩
  infer_instance

/-- Restrict the representation to its supporting ideal. -/
def supportMap : support k G M →ₗ⁅k⁆ image k G M :=
  (LieModule.toEnd k G M).rangeRestrict.comp (support k G M).incl

theorem supportMap_bijective (hg : IsSemisimple k G) :
    Function.Bijective (supportMap k G M) := by
  have hc := support_isCompl k G M hg
  constructor
  · apply (supportMap k G M).ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro x hx
    apply Subtype.ext
    have hxk : (x : G) ∈ (LieModule.toEnd k G M).ker := by
      rw [LieHom.mem_ker]
      exact congrArg Subtype.val ((supportMap k G M).mem_ker.mp hx)
    have hh : (x : G) ∈ (LieModule.toEnd k G M).ker ⊓ support k G M :=
      ⟨hxk, x.property⟩
    rw [hc.disjoint.eq_bot] at hh
    exact hh
  · rintro ⟨y, z, rfl⟩
    have hz : z ∈ (LieModule.toEnd k G M).ker ⊔ support k G M := by
      rw [hc.codisjoint.eq_top]; exact LieSubmodule.mem_top _
    rw [LieSubmodule.mem_sup] at hz
    obtain ⟨a, ha, b, hb, hab⟩ := hz
    refine ⟨⟨b, hb⟩, Subtype.ext ?_⟩
    change LieModule.toEnd k G M b = LieModule.toEnd k G M z
    rw [← hab, map_add, (LieModule.toEnd k G M).mem_ker.mp ha, zero_add]

noncomputable def supportEquivImage (hg : IsSemisimple k G) :
    support k G M ≃ₗ⁅k⁆ image k G M :=
  LieEquiv.ofBijective (supportMap k G M) (supportMap_bijective k G M hg)

/-- Cartan's matrix criterion applied to the radical of the trace form. -/
theorem traceForm_nondegenerate_of_semisimple_subalgebra
    (A : LieSubalgebra k (Module.End k M)) [LieAlgebra.HasTrivialRadical k A] :
    (LieModule.traceForm k A M).Nondegenerate := by
  let B := LieModule.traceForm k A M
  let J : LieIdeal k A := LieAlgebra.InvariantForm.orthogonal B
    (LieModule.traceForm_lieInvariant k A M) ⊤
  let f : J →ₗ⁅k⁆ Module.End k M := A.incl.comp J.incl
  have hf : Function.Injective f := (Subtype.val_injective).comp J.incl_injective
  haveI : LieAlgebra.IsSolvable f.range := by
    apply solvable_of_trace_orthogonal f.range
    rintro ⟨x, hx⟩ _ ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    change B x y = 0
    rw [LieModule.traceForm_comm]
    exact (LieAlgebra.InvariantForm.mem_orthogonal B
      (LieModule.traceForm_lieInvariant k A M) ⊤ x).mp x.property y
      (LieSubmodule.mem_top _)
  haveI : LieAlgebra.IsSolvable J :=
    (f.equivRangeOfInjective hf).injective.lieAlgebra_isSolvable
  have hJ : J = ⊥ := LieAlgebra.HasTrivialRadical.eq_bot_of_isSolvable J
  apply (LieModule.traceForm_isSymm k A M).isRefl.nondegenerate_iff_separatingLeft.mpr
  intro x hx
  have hxJ : x ∈ J := by
    rw [LieAlgebra.InvariantForm.mem_orthogonal]
    intro y _
    exact (LieModule.traceForm_comm k A M _ _).trans (hx y)
  simpa only [hJ, LieSubmodule.mem_bot] using hxJ

theorem image_traceForm_nondegenerate (hg : IsSemisimple k G) :
    (LieModule.traceForm k (image k G M) M).Nondegenerate := by
  haveI := ideal_isKilling k G hg (support k G M)
  haveI := (supportEquivImage k G M hg).isKilling
  exact traceForm_nondegenerate_of_semisimple_subalgebra k M (image k G M)

theorem support_traceForm_nondegenerate (hg : IsSemisimple k G) :
    (LieModule.traceForm k (support k G M) M).Nondegenerate := by
  have hB := image_traceForm_nondegenerate k G M hg
  let e := supportEquivImage k G M hg
  apply (LieModule.traceForm_isSymm k (support k G M) M).isRefl.nondegenerate_iff_separatingLeft.mpr
  intro x hx
  apply e.injective
  change e x = e 0
  rw [map_zero]
  apply hB.1 (e x)
  intro y
  obtain ⟨z, rfl⟩ := e.surjective y
  exact hx z

theorem dualBasis_pairing {V : Type*} [AddCommGroup V] [Module k V]
    (B : LinearMap.BilinForm k V) (hB : B.Nondegenerate)
    {ι : Type t} [Fintype ι] (b : Module.Basis ι k V) (i : ι) (z : V) :
    B (B.dualBasis hB b i) z = b.repr z i := by
  classical
  conv_lhs => rw [← b.sum_repr z]
  simp only [map_sum, map_smul, B.apply_dualBasis_left, smul_eq_mul]
  simp

/-- Change of a trace-dual basis preserves its contraction with any bilinear map. -/
theorem dual_basis_contraction {V : Type*} [AddCommGroup V] [Module k V]
    (B : LinearMap.BilinForm k V) (hB : B.Nondegenerate)
    {ι κ : Type t} [Fintype ι] [Fintype κ]
    (b : Module.Basis ι k V) (c : Module.Basis κ k V)
    {W : Type*} [AddCommGroup W] [Module k W]
    (f : V →ₗ[k] V →ₗ[k] W) :
    ∑ i, f (b i) (B.dualBasis hB b i) =
      ∑ j, f (c j) (B.dualBasis hB c j) := by
  classical
  haveI := b.finiteDimensional_of_finite
  let d := B.dualBasis hB b
  have hd (j : κ) : ∑ i, c.repr (b i) j • d i = B.dualBasis hB c j := by
    apply (B.toDual hB).injective
    apply b.ext
    intro l
    change B (∑ i, c.repr (b i) j • d i) (b l) = B (B.dualBasis hB c j) (b l)
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, d, B.apply_dualBasis_left]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simpa using (dualBasis_pairing k B hB c j (b l)).symm
  calc
    ∑ i, f (b i) (B.dualBasis hB b i) =
        ∑ i, ∑ j, c.repr (b i) j • f (c j) (d i) := by
      apply Finset.sum_congr rfl
      intro i _
      conv_lhs => rw [← c.sum_repr (b i)]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
      rfl
    _ = ∑ j, ∑ i, c.repr (b i) j • f (c j) (d i) := Finset.sum_comm
    _ = ∑ j, f (c j) (B.dualBasis hB c j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← hd j]
      simp

/-- The bilinear multiplication map on an ideal, followed by the canonical
inclusion in the enveloping algebra. -/
def envelopingProduct (I : LieIdeal k G) : I →ₗ[k] I →ₗ[k] U k G :=
  { toFun := fun x =>
      { toFun := fun y => inclusion k G (x : G) * inclusion k G (y : G)
        map_add' := by intros; simp [mul_add]
        map_smul' := by intros; simp [Algebra.mul_smul_comm] }
    map_add' := by intros; ext; simp [add_mul]
    map_smul' := by intros; ext; simp [Algebra.smul_mul_assoc] }

theorem casimir_basis_independent (I : LieIdeal k G)
    (hB : (LieModule.traceForm k I M).Nondegenerate)
    {ι κ : Type t} [Fintype ι] [Fintype κ]
    (b : Module.Basis ι k I) (c : Module.Basis κ k I) :
    casimirSum k G M I hB b = casimirSum k G M I hB c := by
  exact dual_basis_contraction k (LieModule.traceForm k I M) hB b c (envelopingProduct k G I)

/-- The dual contraction of a skew-adjoint linear map is zero. This is the
finite-sum form of invariance of the inverse tensor of a bilinear form. -/
theorem skew_contraction {V : Type*} [AddCommGroup V] [Module k V]
    (B : LinearMap.BilinForm k V) (hB : B.Nondegenerate)
    {ι : Type t} [Fintype ι] (b : Module.Basis ι k V)
    (D : V →ₗ[k] V) (hD : ∀ y z, B (D y) z = -B y (D z))
    {W : Type*} [AddCommGroup W] [Module k W]
    (f : V →ₗ[k] V →ₗ[k] W) :
    (∑ i, f (D (b i)) (B.dualBasis hB b i)) +
      (∑ i, f (b i) (D (B.dualBasis hB b i))) = 0 := by
  classical
  let d := B.dualBasis hB b
  have hd (i : ι) : D (d i) = -∑ j, b.repr (D (b j)) i • d j := by
    apply d.repr.injective
    ext l
    change d.repr (D (d i)) l = d.repr (-∑ j, b.repr (D (b j)) i • d j) l
    rw [LinearMap.BilinForm.dualBasis_repr_apply, hD, dualBasis_pairing]
    simp [map_sum, map_smul, d, smul_eq_mul, Finsupp.single_apply]
  have h₁ : (∑ i, f (D (b i)) (d i)) =
      ∑ i, ∑ j, b.repr (D (b i)) j • f (b j) (d i) := by
    apply Finset.sum_congr rfl
    intro i _
    conv_lhs => rw [← b.sum_repr (D (b i))]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  have h₂ : (∑ i, f (b i) (D (d i))) =
      -∑ i, ∑ j, b.repr (D (b j)) i • f (b i) (d j) := by
    simp only [hd, map_neg, map_sum, map_smul, Finset.sum_neg_distrib]
  change (∑ i, f (D (b i)) (d i)) + (∑ i, f (b i) (D (d i))) = 0
  rw [h₁, h₂, Finset.sum_comm]
  exact add_neg_cancel _

theorem casimir_commutes_generator (I : LieIdeal k G)
    (hB : (LieModule.traceForm k I M).Nondegenerate)
    {ι : Type t} [Fintype ι] (b : Module.Basis ι k I) (x : G) :
    inclusion k G x * casimirSum k G M I hB b =
      casimirSum k G M I hB b * inclusion k G x := by
  classical
  let B := LieModule.traceForm k I M
  let D := LieModule.toEnd k G I x
  have hD : ∀ y z, B (D y) z = - B y (D z) := by
    intro y z
    change LieModule.traceForm k G M ⁅x, (y : G)⁆ (z : G) =
      -LieModule.traceForm k G M (y : G) ⁅x, (z : G)⁆
    exact LieModule.traceForm_apply_lie_apply' k G M x y z
  have hh := skew_contraction k B hB b D hD (envelopingProduct k G I)
  have hlie (y : I) : inclusion k G (D y : G) =
      inclusion k G x * inclusion k G (y : G) -
        inclusion k G (y : G) * inclusion k G x := by
    change inclusion k G ⁅x, (y : G)⁆ = _
    exact (inclusion k G).map_lie x y
  change (∑ i, inclusion k G (D (b i) : G) *
      inclusion k G (B.dualBasis hB b i : G)) +
    (∑ i, inclusion k G (b i : G) *
      inclusion k G (D (B.dualBasis hB b i) : G)) = 0 at hh
  simp only [hlie, sub_mul, mul_sub, mul_assoc] at hh
  rw [← Finset.sum_add_distrib] at hh
  simp only [sub_add_sub_cancel] at hh
  simpa only [casimirSum, Finset.mul_sum, Finset.sum_mul, mul_assoc,
    Finset.sum_sub_distrib, sub_eq_zero] using hh

theorem casimir_central (I : LieIdeal k G)
    (hB : (LieModule.traceForm k I M).Nondegenerate)
    {ι : Type t} [Fintype ι] (b : Module.Basis ι k I) :
    casimirSum k G M I hB b ∈ Subalgebra.center k (U k G) := by
  rw [Subalgebra.mem_center_iff]
  intro a
  induction a using enveloping_induction k G with
  | scalar r => exact Algebra.commutes r _
  | generator x => exact casimir_commutes_generator k G M I hB b x
  | mul a b ha hb => rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  | add a b ha hb => simp only [add_mul, mul_add, ha, hb]

theorem casimir_augmentation (I : LieIdeal k G)
    (hB : (LieModule.traceForm k I M).Nondegenerate)
    {ι : Type t} [Fintype ι] (b : Module.Basis ι k I) :
    augmentation k G (casimirSum k G M I hB b) = 0 := by
  classical
  simp [casimirSum, augmentation, inclusion, UniversalEnvelopingAlgebra.lift_ι_apply]

theorem casimir_trace (I : LieIdeal k G)
    (hB : (LieModule.traceForm k I M).Nondegenerate)
    {ι : Type t} [Fintype ι] (b : Module.Basis ι k I) :
    LinearMap.trace k M (action k G M (casimirSum k G M I hB b)) =
      (Module.finrank k I : k) := by
  classical
  have he (x : G) : action k G M (inclusion k G x) = LieModule.toEnd k G M x :=
    UniversalEnvelopingAlgebra.lift_ι_apply k _ x
  simp only [casimirSum, map_sum, map_mul, he]
  change ∑ i, LieModule.traceForm k I M (b i)
    ((LieModule.traceForm k I M).dualBasis hB b i) = _
  simp only [LinearMap.BilinForm.apply_dualBasis_right _
    ⟨LieModule.traceForm_comm k I M⟩, if_true, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  exact congrArg Nat.cast (Module.finrank_eq_card_basis b).symm

/-- Every central element acts by a morphism of the original Lie module. -/
def centralAction (C : U k G) (hC : C ∈ Subalgebra.center k (U k G)) :
    M →ₗ⁅k,G⁆ M where
  __ := (action k G M C : Module.End k M)
  map_lie' {x m} := by
    change action k G M C ⁅x, m⁆ = ⁅x, action k G M C m⁆
    have he (x : G) : action k G M (inclusion k G x) = LieModule.toEnd k G M x :=
      UniversalEnvelopingAlgebra.lift_ι_apply k _ x
    have h := congrArg (fun a => action k G M a m)
      ((Subalgebra.mem_center_iff.mp hC) (inclusion k G x))
    simpa only [map_mul, he, Module.End.mul_apply, LieModule.toEnd_apply_apply] using h.symm

/-- Schur's kernel argument over an arbitrary field. Finite dimension supplies
surjectivity from injectivity, with no algebraic closure hypothesis. -/
theorem bijective_of_irreducible [LieModule.IsIrreducible k G M]
    (f : M →ₗ⁅k,G⁆ M) (hf : f ≠ 0) : Function.Bijective f := by
  have hk : f.ker = ⊥ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top f.ker with hk | hk
    · exact hk
    · exfalso
      apply hf
      ext m
      exact LieModuleHom.mem_ker.mp (hk ▸ LieSubmodule.mem_top m)
  have hi := f.ker_eq_bot.mp hk
  exact ⟨hi, (LinearMap.injective_iff_surjective (f := (f : Module.End k M))).mp hi⟩

theorem image_finrank_ne_zero (hM : ¬ LieModule.IsTrivial G M) :
    Module.finrank k (image k G M) ≠ 0 := by
  intro h
  haveI : Subsingleton (image k G M) := Module.finrank_zero_iff.mp h
  apply hM
  constructor
  intro x m
  have hh : (LieModule.toEnd k G M).rangeRestrict x = 0 := Subsingleton.elim _ _
  exact congrArg (fun f : image k G M => (f : Module.End k M) m) hh

theorem module_casimir [LieModule.IsIrreducible k G M]
    (hg : IsSemisimple k G) (hM : ¬ LieModule.IsTrivial G M) :
    ∃ hB : (LieModule.traceForm k (support k G M) M).Nondegenerate,
      ∀ {ι : Type t} [Fintype ι] (b : Module.Basis ι k (support k G M)),
        CasimirProperties k G M (casimirSum k G M (support k G M) hB b) := by
  refine ⟨support_traceForm_nondegenerate k G M hg, ?_⟩
  intro ι _ b
  let C := casimirSum k G M (support k G M) (support_traceForm_nondegenerate k G M hg) b
  have hc : C ∈ Subalgebra.center k (U k G) := casimir_central k G M _ _ b
  have ht : LinearMap.trace k M (action k G M C) =
      (Module.finrank k (image k G M) : k) := by
    rw [← (supportEquivImage k G M hg).toLinearEquiv.finrank_eq]
    exact casimir_trace k G M _ _ b
  refine ⟨hc, casimir_augmentation k G M _ _ b, ht, ?_⟩
  apply bijective_of_irreducible k G M (centralAction k G M C hc)
  intro hz
  have hzero : action k G M C = 0 := congrArg LieModuleHom.toLinearMap hz
  have hn : (Module.finrank k (image k G M) : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (image_finrank_ne_zero k G M hM)
  apply hn
  rw [← ht, hzero, map_zero]

theorem exists_module_casimir [LieModule.IsIrreducible k G M]
    (hg : IsSemisimple k G) (hM : ¬ LieModule.IsTrivial G M) :
    ∃ C : U k G, CasimirProperties k G M C := by
  obtain ⟨hB, h⟩ := module_casimir.{u,v,w,0} k G M hg hM
  exact ⟨_, h (Module.finBasis k (support k G M))⟩

/-- Schur's scalar argument is used only after assuming algebraic closure. -/
theorem scalar_of_irreducible [IsAlgClosed k] [LieModule.IsIrreducible k G M]
    (f : M →ₗ⁅k,G⁆ M) : ∃ c : k, (f : Module.End k M) = c • LinearMap.id := by
  haveI := LieModule.nontrivial_of_isIrreducible k G M
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (f : Module.End k M)
  obtain ⟨m, hm⟩ := hc.exists_hasEigenvector
  let q : M →ₗ⁅k,G⁆ M := f - c • LieModuleHom.id
  have hqm : q m = 0 := by
    change f m - c • m = 0
    exact sub_eq_zero.mpr hm.apply_eq_smul
  have hq : q = 0 := by
    by_contra hq
    have hi := (bijective_of_irreducible k G M q hq).injective
    exact hm.2 (hi (hqm.trans (map_zero q).symm))
  have hh := congrArg LieModuleHom.toLinearMap hq
  change (f : Module.End k M) - c • LinearMap.id = 0 at hh
  exact ⟨c, sub_eq_zero.mp hh⟩

theorem module_casimir_scalar [IsAlgClosed k] [LieModule.IsIrreducible k G M]
    (hg : IsSemisimple k G) (hM : ¬ LieModule.IsTrivial G M)
    (hB : (LieModule.traceForm k (support k G M) M).Nondegenerate)
    {ι : Type t} [Fintype ι] (b : Module.Basis ι k (support k G M)) :
    let c : k := (Module.finrank k (image k G M) : k) / (Module.finrank k M : k)
    c ≠ 0 ∧ action k G M (casimirSum k G M (support k G M) hB b) =
      c • (LinearMap.id : Module.End k M) := by
  haveI := LieModule.nontrivial_of_isIrreducible k G M
  let C := casimirSum k G M (support k G M) hB b
  have hC : C ∈ Subalgebra.center k (U k G) := casimir_central k G M _ _ b
  obtain ⟨c, hc⟩ := scalar_of_irreducible k G M (centralAction k G M C hC)
  change action k G M C = c • LinearMap.id at hc
  have ht : LinearMap.trace k M (action k G M C) =
      (Module.finrank k (image k G M) : k) := by
    rw [← (supportEquivImage k G M hg).toLinearEquiv.finrank_eq]
    exact casimir_trace k G M _ _ b
  rw [hc, map_smul, LinearMap.trace_id] at ht
  have hd : (Module.finrank k M : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt Module.finrank_pos)
  have he : c = (Module.finrank k (image k G M) : k) / (Module.finrank k M : k) :=
    (eq_div_iff hd).mpr ht
  refine ⟨div_ne_zero (Nat.cast_ne_zero.mpr (image_finrank_ne_zero k G M hM)) hd, ?_⟩
  rw [← he]
  exact hc

end LieAlgebrasAndRepresentations.ModuleCasimir
