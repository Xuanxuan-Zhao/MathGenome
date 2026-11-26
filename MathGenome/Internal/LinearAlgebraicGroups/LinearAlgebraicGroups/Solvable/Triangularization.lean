import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.Triangularization
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.WeightDecomposition
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.CentralSeries
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SchemeDerivedGroup
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite WithConv
open scoped TensorProduct CategoryTheory.MonObj

universe u v

namespace LinearAlgebraicGroups.Triangularization

noncomputable section

open _root_.LinearAlgebraicGroups.Specs Specs.Triangularization Specs.Unipotent
open RationalRepresentations

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k]

private lemma stable_line {A : HopfAlgebraCategory k} {V : Type u}
    [AddCommGroup V] [Module k V] (ρ : RightComodule k A V) (v : V) (a : A)
    (h : ρ.coaction v = v ⊗ₜ[k] a) :
    ρ.IsSubcomodule (k ∙ v) := by
  intro x
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp x.property
  let w : (k ∙ v : Submodule k V) := ⟨v, Submodule.mem_span_singleton_self v⟩
  refine ⟨(c • w) ⊗ₜ[k] a, ?_⟩
  rw [LinearMap.rTensor_tmul]
  change (c • v) ⊗ₜ[k] a = ρ.coaction (x : V)
  rw [← hc, map_smul, h, TensorProduct.smul_tmul']

private lemma eigenvector_of_stable_line {A : HopfAlgebraCategory k} {V : Type u}
    [AddCommGroup V] [Module k V] (ρ : RightComodule k A V)
    (W : Submodule k V) (hW : ρ.IsSubcomodule W) (hd : Module.finrank k W = 1) :
    ∃ v : V, v ≠ 0 ∧ ∃ a : A, ρ.coaction v = v ⊗ₜ[k] a := by
  letI : FiniteDimensional k W := Module.finite_of_finrank_pos (by omega)
  obtain ⟨σ, hσ⟩ := (ρ.isSubcomodule_iff_exists_coaction W).mp hW
  let b := ((Module.finBasis k W).reindex (finCongr hd)).reindex Equiv.ulift.symm
  let j : Index.{u} 1 := ⟨0⟩
  refine ⟨b j, fun hv ↦ b.ne_zero j (Subtype.ext hv), coefficients A b σ j j, ?_⟩
  have h := DFunLike.congr_fun hσ (b j)
  change W.subtype.rTensor A (σ.coaction (b j)) = ρ.coaction (b j) at h
  rw [coaction_apply_basis A b σ, Finset.sum_eq_single j, LinearMap.rTensor_tmul] at h
  · exact h.symm
  · intro i _ hi
    exact (hi (Subsingleton.elim _ _)).elim
  · exact fun hj ↦ (hj (Finset.mem_univ _)).elim

private lemma has_simple_subcomodule {A : HopfAlgebraCategory k} {V : Type u}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (ρ : RightComodule k A V) :
    ∃ (W : Submodule k V) (σ : RightComodule k A W),
      IsSimple σ ∧ ρ.IsSubcomodule W := by
  classical
  let P (d : ℕ) := ∃ W : Submodule k V, ρ.IsSubcomodule W ∧ W ≠ ⊥ ∧ Module.finrank k W = d
  have hex : ∃ d, P d := by
    refine ⟨_, ⊤, ?_, top_ne_bot, rfl⟩
    intro x
    exact LinearMap.rTensor_surjective A (show Function.Surjective
      (⊤ : Submodule k V).subtype from fun v ↦ ⟨⟨v, Submodule.mem_top⟩, rfl⟩) _
  obtain ⟨W, hW, hnW, hd⟩ := Nat.find_spec hex
  obtain ⟨σ, hσ⟩ := (ρ.isSubcomodule_iff_exists_coaction W).mp hW
  refine ⟨W, σ, ⟨Submodule.nontrivial_iff_ne_bot.mpr hnW, ?_⟩, hW⟩
  intro S hS
  by_contra! hs
  obtain ⟨τ, hτ⟩ := (σ.isSubcomodule_iff_exists_coaction S).mp hS
  let L := S.map W.subtype
  let e : S ≃ₗ[k] L := S.equivMapOfInjective W.subtype W.subtype_injective
  have hL : ρ.IsSubcomodule L := by
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    refine ⟨e.toLinearMap.rTensor A (τ.coaction z), ?_⟩
    change L.subtype.rTensor A (e.toLinearMap.rTensor A (τ.coaction z)) =
      ρ.coaction (W.subtype (S.subtype z))
    rw [← LinearMap.rTensor_comp_apply]
    change (W.subtype.comp S.subtype).rTensor A (τ.coaction z) = _
    rw [LinearMap.rTensor_comp_apply]
    rw [show S.subtype.rTensor A (τ.coaction z) = σ.coaction (S.subtype z) from
      DFunLike.congr_fun hτ z]
    exact DFunLike.congr_fun hσ (S.subtype z)
  have hne : L ≠ ⊥ := by
    letI : Nontrivial S := Submodule.nontrivial_iff_ne_bot.mpr hs.1
    letI : Nontrivial L := e.injective.nontrivial
    exact Submodule.nontrivial_iff_ne_bot.mp inferInstance
  have hdim : Module.finrank k L < Module.finrank k W := by
    rw [← e.finrank_eq]
    exact Submodule.finrank_lt hs.2
  have hmin := Nat.find_min' hex ⟨L, hL, hne, rfl⟩
  omega

private def HasEigenvectors (A : HopfAlgebraCategory k) : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (ρ : RightComodule k A V), ∃ v : V, v ≠ 0 ∧ ∃ a : A, ρ.coaction v = v ⊗ₜ[k] a

private theorem simple_iff_eigenvectors (A : HopfAlgebraCategory k) :
    SimpleRepresentationsAreLines A ↔ HasEigenvectors A := by
  constructor
  · intro h V _ _ _ _ ρ
    obtain ⟨W, σ, hs, hW⟩ := has_simple_subcomodule ρ
    exact eigenvector_of_stable_line ρ W hW (h W σ hs)
  · intro h V _ _ _ ρ hs
    letI : Nontrivial V := hs.1
    obtain ⟨v, hv, a, ha⟩ := h V ρ
    rcases hs.2 (k ∙ v) (stable_line ρ v a ha) with he | he
    · exact (hv ((Submodule.eq_bot_iff _).mp he v (Submodule.mem_span_singleton_self v))).elim
    · rw [← finrank_top (R := k) (M := V), ← he]
      exact finrank_span_singleton hv

/-- Preservation of a basis flag is equivalent to triangularity of the coaction matrix. -/
theorem upperTriangular_iff_invariant_prefixes {A : HopfAlgebraCategory k}
    {n : ℕ} {V : Type u} [AddCommGroup V] [Module k V]
    (b : Module.Basis (Index.{u} n) k V) (ρ : RightComodule k A V) :
    (coefficients A b ρ).IsUpperTriangular ↔
      ∀ j : Fin (n + 1), ρ.IsSubcomodule (Submodule.span k (b '' {i | i.down.val < j.val})) := by
  classical
  constructor
  · intro hb j
    let W := Submodule.span k (b '' {i | i.down.val < j.val})
    have hW : W ≤ Submodule.comap ρ.coaction (LinearMap.range (W.subtype.rTensor A)) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, hi, rfl⟩
      change ρ.coaction (b i) ∈ LinearMap.range (W.subtype.rTensor A)
      rw [coaction_apply_basis A b ρ]
      apply Submodule.sum_mem
      intro l _
      by_cases hl : l.down.val < j.val
      · let w : W := ⟨b l, Submodule.subset_span ⟨l, hl, rfl⟩⟩
        exact ⟨w ⊗ₜ[k] coefficients A b ρ l i, LinearMap.rTensor_tmul A W.subtype _ w⟩
      · have hli : i < l := Nat.lt_of_lt_of_le hi (Nat.le_of_not_gt hl)
        rw [hb hli, TensorProduct.tmul_zero]
        exact Submodule.zero_mem _
    intro x
    exact hW x.property
  · intro h i j hij
    change j < i at hij
    let t : Fin (n + 1) := ⟨j.down.val + 1, Nat.succ_lt_succ j.down.isLt⟩
    let W := Submodule.span k (b '' {l | l.down.val < t.val})
    have hzero : W ≤ LinearMap.ker (b.coord i) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨l, hl, rfl⟩
      change l.down.val < t.val at hl
      have hli : l ≠ i := by
        intro he
        subst l
        exact Nat.not_lt_of_ge (Nat.succ_le_of_lt (show j.down.val < i.down.val from hij)) hl
      simp [Module.Basis.coord_apply, hli]
    have hw : b j ∈ W := Submodule.subset_span ⟨j, Nat.lt_succ_self _, rfl⟩
    obtain ⟨z, hz⟩ := h t ⟨b j, hw⟩
    have hmap : (tensorCoordinate b i).comp (W.subtype.rTensor A) = 0 := by
      apply TensorProduct.ext'
      intro w a
      change b.coord i (w : V) • a = 0
      rw [LinearMap.mem_ker.mp (hzero w.property), zero_smul]
    change tensorCoordinate b i (ρ.coaction (b j)) = 0
    change W.subtype.rTensor A z = ρ.coaction (b j) at hz
    rw [← hz]
    exact DFunLike.congr_fun hmap z

private theorem eigenvectors_of_flags {A : HopfAlgebraCategory k}
    (h : HasInvariantFullFlags A) : HasEigenvectors A := by
  intro V _ _ _ _ ρ
  obtain ⟨b, hb⟩ := h V ρ
  have htri := (upperTriangular_iff_invariant_prefixes b ρ).mpr hb
  have hp : 0 < Module.finrank k V := Module.finrank_pos
  let j : Index.{u} (Module.finrank k V) := ⟨⟨0, hp⟩⟩
  refine ⟨b j, b.ne_zero j, coefficients A b ρ j j, ?_⟩
  rw [coaction_apply_basis A b ρ, Finset.sum_eq_single j]
  · intro i _ hi
    have hj : j < i := lt_of_le_of_ne (Nat.zero_le i.down.val) (Ne.symm hi)
    rw [htri hj, TensorProduct.tmul_zero]
  · simp

open private Unipotent.quotientCoaction from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.Criteria

private abbrev basisTensorCoordinate {Idx : Type v} {V : Type u}
    [AddCommGroup V] [Module k V] {A : HopfAlgebraCategory k}
    (b : Module.Basis Idx k V) (i : Idx) : V ⊗[k] A →ₗ[k] A :=
  (TensorProduct.lid k A).toLinearMap.comp ((b.coord i).rTensor A)

private theorem finBasis_of_eigenvectors {A : HopfAlgebraCategory k} (h : HasEigenvectors A) (n : ℕ) :
    ∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V],
      Module.finrank k V = n → ∀ ρ : RightComodule k A V,
        ∃ b : Module.Basis (Fin n) k V, Matrix.IsUpperTriangular (fun i j ↦ basisTensorCoordinate b i (ρ.coaction (b j)) : Matrix (Fin n) (Fin n) A) := by
  induction n with
  | zero =>
    intro V _ _ _ hn ρ
    exact ⟨(Module.finBasis k V).reindex (finCongr hn), fun {i} ↦ Fin.elim0 i⟩
  | succ n ih =>
    intro V _ _ _ hn ρ
    letI := Module.nontrivial_of_finrank_pos (R := k) (M := V) (by omega)
    obtain ⟨v, hv, a, ha⟩ := h V ρ
    obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one k hv
    let W := LinearMap.ker l
    let inc : W →ₗ[k] V := W.subtype
    let p : V →ₗ[k] W :=
      (LinearMap.id - (LinearMap.toSpanSingleton k V v).comp l).codRestrict W (fun x ↦ by
        change l (x - l x • v) = 0
        simp [hl])
    have hp (x : V) : inc (p x) = x - l x • v := rfl
    have hp_inc (w : W) : p (inc w) = w := by
      apply Subtype.ext
      change inc (p (inc w)) = inc w
      rw [hp, show l (inc w) = 0 from w.property, zero_smul, sub_zero]
    have hp_v : p v = 0 := by
      apply Subtype.ext
      change inc (p v) = 0
      rw [hp, hl, one_smul, sub_self]
    let f : W →ₗ[k] W ⊗[k] A := (p.rTensor A).comp (ρ.coaction.comp inc)
    have hf : f.comp p = (p.rTensor A).comp ρ.coaction := by
      ext x
      change p.rTensor A (ρ.coaction (inc (p x))) = p.rTensor A (ρ.coaction x)
      rw [hp, map_sub, map_smul, ha, map_sub, map_smul, LinearMap.rTensor_tmul, hp_v]
      simp
    let σ := Unipotent.quotientCoaction A ρ p (fun w ↦ ⟨inc w, hp_inc w⟩) f hf
    have hrange : LinearMap.range l = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro c
      exact ⟨c • v, by simp [hl]⟩
    have hdim := l.finrank_range_add_finrank_ker
    rw [hrange, finrank_top, Module.finrank_self, hn] at hdim
    have hnW : Module.finrank k W = n := by change Module.finrank k (LinearMap.ker l) = n; omega
    obtain ⟨b, hb⟩ := ih W hnW σ
    have hli (c : k) (x : V) (hx : x ∈ W) (hcx : c • v + x = 0) : c = 0 := by
      simpa [hl, show l x = 0 from hx] using congrArg l hcx
    have hsp (x : V) : ∃ c : k, x + c • v ∈ W := by
      refine ⟨-l x, ?_⟩
      change l (x + (-l x) • v) = 0
      simp [hl]
    let B := Module.Basis.mkFinCons v b hli hsp
    have hB : (B : Fin (n + 1) → V) = Fin.cons v (inc ∘ b) :=
      Module.Basis.coe_mkFinCons v b hli hsp
    have hcoord (i : Fin n) :
        basisTensorCoordinate (A := A) B i.succ = (basisTensorCoordinate b i).comp (p.rTensor A) := by
      apply TensorProduct.ext'
      intro x c
      change B.coord i.succ x • c = b.coord i (p x) • c
      congr 1
      have hc : B.coord i.succ = (b.coord i).comp p := by
        apply B.ext
        intro j
        simp only [LinearMap.comp_apply, Module.Basis.coord_apply, Module.Basis.repr_self]
        rw [hB]
        cases j using Fin.cases with
        | zero => simp [hp_v]
        | succ j =>
          simp only [Fin.cons_succ, Function.comp_apply, hp_inc, Module.Basis.repr_self]
          simp [Finsupp.single_apply]
      exact DFunLike.congr_fun hc x
    refine ⟨B, ?_⟩
    intro i j hij
    change j < i at hij
    cases i using Fin.cases with
    | zero => exact (Fin.not_lt_zero _ hij).elim
    | succ i =>
      change basisTensorCoordinate B i.succ (ρ.coaction (B j)) = 0
      rw [hcoord, LinearMap.comp_apply, hB]
      cases j using Fin.cases with
      | zero => simp [ha, hp_v]
      | succ j =>
        change basisTensorCoordinate b i (σ.coaction (b j)) = 0
        exact hb (Fin.succ_lt_succ_iff.mp hij)

private theorem flags_of_eigenvectors {A : HopfAlgebraCategory k}
    (h : HasEigenvectors A) : HasInvariantFullFlags A := by
  intro V _ _ _ ρ
  obtain ⟨b, hb⟩ := finBasis_of_eigenvectors h (Module.finrank k V) V rfl ρ
  let B := b.reindex Equiv.ulift.symm
  refine ⟨B, (upperTriangular_iff_invariant_prefixes B ρ).mp ?_⟩
  intro i j hij
  have hc : tensorCoordinate (C := A) B i = basisTensorCoordinate b i.down := by
    apply TensorProduct.ext'
    intro x a
    change B.coord i x • a = b.coord i.down x • a
    simp [B, Module.Basis.coord_apply]
  change tensorCoordinate B i (ρ.coaction (B j)) = 0
  rw [hc]
  simpa [B, Module.Basis.reindex_apply, coefficients] using hb (show j.down < i.down from hij)

theorem simpleRepresentationsIffInvariantFullFlags {A : HopfAlgebraCategory k} :
    SimpleRepresentationsAreLines A ↔ HasInvariantFullFlags A :=
  (simple_iff_eigenvectors A).trans ⟨flags_of_eigenvectors, eigenvectors_of_flags⟩

section UpperTriangularGroup

open Specs.StandardGroups

open private
  StandardGroups.Representation StandardGroups.Representation.mk
  StandardGroups.Representation.hopf
  StandardGroups.Representation.convolutionIso StandardGroups.spectrumPointsIso
  StandardGroups.glEvaluation StandardGroups.glEvaluation_entry
  StandardGroups.glCoordinates_ext StandardGroups.evaluatedGeneralLinear
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups

variable (k) (n : ℕ)

private def lowerEntryIdeal : Ideal (GLCoordinates k (Index.{u} n)) :=
  Ideal.span (Set.range (fun p : StrictUpper n ↦ universalMatrix k (Index.{u} n) p.1.2 p.1.1))

private abbrev UpperCoordinates := GLCoordinates k (Index.{u} n) ⧸ lowerEntryIdeal k n

private abbrev quotientCoordinates := Ideal.Quotient.mkₐ k (lowerEntryIdeal k n)

private def evaluatedUpperTriangular (R : TestAlgebra k)
    (f : UpperCoordinates k n →ₐ[k] R) : (upperTriangularPoints k n).obj R :=
  ⟨StandardGroups.evaluatedGeneralLinear (f.comp (quotientCoordinates k n)), by
    intro i j hij
    change j < i at hij
    change f (quotientCoordinates k n (universalMatrix k (Index.{u} n) i j)) = 0
    rw [show quotientCoordinates k n (universalMatrix k (Index.{u} n) i j) = 0 from
      Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span ⟨⟨(j, i), hij⟩, rfl⟩), map_zero]⟩

private def upperEvaluation (R : TestAlgebra k)
    (g : (upperTriangularPoints k n).obj R) : UpperCoordinates k n →ₐ[k] R :=
  Ideal.Quotient.liftₐ (lowerEntryIdeal k n) (StandardGroups.glEvaluation g.val) (by
    change lowerEntryIdeal k n ≤ RingHom.ker (StandardGroups.glEvaluation g.val).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨p, rfl⟩
    change StandardGroups.glEvaluation g.val (universalMatrix k (Index.{u} n) p.1.2 p.1.1) = 0
    rw [StandardGroups.glEvaluation_entry]
    exact g.property p.property)

private lemma upperEvaluation_entry (R : TestAlgebra k)
    (g : (upperTriangularPoints k n).obj R) (i j : Index.{u} n) :
    upperEvaluation k n R g (quotientCoordinates k n (universalMatrix k (Index.{u} n) i j)) =
      g.val.val i j :=
  StandardGroups.glEvaluation_entry g.val i j

private def upperTriangularRepresentation :
    StandardGroups.Representation (UpperCoordinates k n) (upperTriangularPoints k n) := by
  refine StandardGroups.Representation.mk (fun R ↦ ?_) ?_
  · exact
      { toFun := evaluatedUpperTriangular k n R
        invFun := upperEvaluation k n R
        left_inv := fun f ↦ by
          apply Ideal.Quotient.algHom_ext k
          apply StandardGroups.glCoordinates_ext
          exact upperEvaluation_entry k n R (evaluatedUpperTriangular k n R f)
        right_inv := fun g ↦ Subtype.ext (Matrix.GeneralLinearGroup.ext (upperEvaluation_entry k n R g)) }
  · intro R S a f
    exact Subtype.ext (Matrix.GeneralLinearGroup.ext fun _ _ ↦ rfl)

/-- The affine algebraic group of invertible upper triangular matrices. -/
def upperTriangularGroup : AffineAlgebraicGroup k :=
  letI := StandardGroups.Representation.hopf (upperTriangularRepresentation k n)
  spectrum k (UpperCoordinates k n)

/-- The upper triangular group represents the matrix functor over every test algebra. -/
def upperTriangularGroupPointsIso :
    (groupPointsFunctor k).obj (upperTriangularGroup k n).val ≅ upperTriangularPoints k n :=
  letI := StandardGroups.Representation.hopf (upperTriangularRepresentation k n)
  StandardGroups.spectrumPointsIso
    (StandardGroups.Representation.convolutionIso (upperTriangularRepresentation k n))

theorem upperTriangularRepresentability : UpperTriangularRepresentability.{u} :=
  fun k _ n ↦ ⟨upperTriangularGroup k n, ⟨upperTriangularGroupPointsIso k n⟩⟩

private abbrev upperHopfAlgebra : HopfAlgebraCategory k :=
  letI := StandardGroups.Representation.hopf (upperTriangularRepresentation k n)
  CommHopfAlgCat.of k (UpperCoordinates k n)

end UpperTriangularGroup

open private StandardGroups.Representation.convolutionIso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups

open private
  Unipotent.onPoints Unipotent.onPoints_comp Unipotent.onPoints_natural
  Unipotent.scheme_hom_spec Unipotent.closed_of_comp
  Unipotent.kernel_of_closed_factor Unipotent.kernel_points
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.CentralSeries


open private surjective_of_coefficients from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.FaithfulLinearization

private theorem embeds_of_flags {G : AffineAlgebraicGroup k} {A : HopfAlgebraCategory k}
    (e : specGroup A ≅ G.val) (h : HasInvariantFullFlags A) :
    EmbedsUpperTriangular G := by
  classical
  letI : IsIso e.hom.hom.hom.left := by
    change IsIso (((Grp.forget (SchemeOver k)) ⋙ Over.forget _).map e.hom)
    infer_instance
  haveI : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  have hf := locallyOfFiniteType_comp e.hom.hom.hom.left G.val.X.hom
  have heq : e.hom.hom.hom.left ≫ G.val.X.hom = (specGroup A).X.hom := Over.w e.hom.hom.hom
  letI : Algebra.FiniteType k A := (hopfSpec_locallyOfFiniteType_iff k A).mp (heq ▸ hf)
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType k A).out
  let ρ : RightComodule k A A := RightComodule.regular
  obtain ⟨W₀, hsW⟩ := ρ.exists_finiteSubcomodule_containing (s : Set A) s.finite_toSet
  let W := W₀.val
  letI : FiniteDimensional k W := W₀.property.2
  obtain ⟨σ, hσ⟩ := (ρ.isSubcomodule_iff_exists_coaction W).mp W₀.property.1
  obtain ⟨b, hb⟩ := h W σ
  have htri := (upperTriangular_iff_invariant_prefixes b σ).mpr hb
  let n := Module.finrank k W
  let T := upperTriangularGroup k n
  let eT := upperTriangularGroupPointsIso k n
  let GA : AffineAlgebraicGroup k := Specs.StandardGroups.spectrum k A
  let eA := hopfSpecPointIso A
  let m := matrixPointHom A (coefficients A b σ) (coefficients_isCoactionMatrix A b σ)
  let mT : convolutionPoints A ⟶ upperTriangularPoints k n :=
    { app := fun R ↦ letI := convolutionGroup A R; GrpCat.ofHom <| (m.app R).hom.codRestrict
        (upperTriangular (Index.{u} n) R) (fun g ↦ by
          change (g.ofConv.mapMatrix (coefficients A b σ)).IsUpperTriangular
          exact htri.map g.ofConv)
      naturality := by
        intro R S a
        apply GrpCat.ext
        intro x
        exact Subtype.ext (congrArg (fun t ↦ t x) (m.naturality a)) }
  let α := eA.inv ≫ mT ≫ eT.inv
  let f : GA.val ⟶ T.val := (AffineAlgebraicGroup.groupHomEquiv GA T).symm α
  let R := CommAlgCat.of k A
  let p := eA.hom.app R (toConv (AlgHom.id k A))
  let y := mT.app R (toConv (AlgHom.id k A))
  let q := upperEvaluation k n R y
  have hq (i j : Index.{u} n) : coefficients A b σ i j ∈ q.range := by
    refine ⟨quotientCoordinates k n (Specs.StandardGroups.universalMatrix k (Index.{u} n) i j), ?_⟩
    change q _ = _
    exact upperEvaluation_entry k n R y i j
  have hy : Unipotent.onPoints f R p = (hopfSpecPointIso (upperHopfAlgebra k n)).hom.app R (toConv q) := by
    apply (eT.app R).groupIsoToMulEquiv.injective
    change eT.hom.app R (Unipotent.onPoints f R p) =
      eT.hom.app R ((hopfSpecPointIso (upperHopfAlgebra k n)).hom.app R (toConv q))
    calc
      _ = y := by
        rw [show Unipotent.onPoints f R p = α.app R p from
          Unipotent.scheme_hom_spec (G := GA) (H := T) α R p]
        change eT.hom.app R (eT.inv.app R (mT.app R (eA.inv.app R p))) = y
        rw [show eA.inv.app R p = toConv (AlgHom.id k A) from
          (eA.app R).groupIsoToMulEquiv.symm_apply_apply _]
        exact (eT.app R).groupIsoToMulEquiv.apply_symm_apply _
      _ = evaluatedUpperTriangular k n R q :=
        Subtype.ext (Matrix.GeneralLinearGroup.ext (fun i j ↦
          (upperEvaluation_entry k n R y i j).symm))
      _ = _ := by
        let c := StandardGroups.Representation.convolutionIso (upperTriangularRepresentation k n)
        let d := hopfSpecPointIso (upperHopfAlgebra k n)
        change evaluatedUpperTriangular k n R q = c.hom.app R (d.inv.app R (d.hom.app R (toConv q)))
        rw [show d.inv.app R (d.hom.app R (toConv q)) = toConv q from
          (d.app R).groupIsoToMulEquiv.symm_apply_apply _]
        rfl
  have hleft := congrArg (fun z : Points T.val.X R ↦ z.left) hy
  change Spec.map (CommRingCat.ofHom (AlgHom.id k A).toRingHom) ≫ f.hom.hom.left =
     Spec.map (CommRingCat.ofHom q.toRingHom) at hleft
  rw [show CommRingCat.ofHom (AlgHom.id k A).toRingHom = 𝟙 _ from rfl, Spec.map_id,
    Category.id_comp] at hleft
  have hclosed : IsClosedImmersion f.hom.hom.left := by
    rw [hleft]
    exact IsClosedImmersion.spec_of_surjective _
      (surjective_of_coefficients A s hs W hsW b σ hσ q hq)
  refine ⟨n, T, ⟨eT⟩, e.inv ≫ f, ?_⟩
  letI : IsClosedImmersion f.hom.hom.left := hclosed
  letI : IsIso e.inv.hom.hom.left := by
    change IsIso (((Grp.forget (SchemeOver k)) ⋙ Over.forget _).map e.inv)
    infer_instance
  change IsClosedImmersion (e.inv.hom.hom.left ≫ f.hom.hom.left)
  exact IsClosedImmersion.comp _ _

open private Unipotent.GPoints Unipotent.onPoints_injective Unipotent.factor_through_closed
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.CentralSeries
open private schemeKernel_exists groupPresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private SchemeDerivedGroup.kernel_normal
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SchemeDerivedGroup

private def diagonalUnit {Idx : Type u} {R : Type v} [Fintype Idx] [LinearOrder Idx] [DecidableEq Idx] [CommRing R]
    (g : upperTriangular Idx R) (i : Idx) : Rˣ where
  val := g.val.val i i
  inv := g.val.inv i i
  val_inv := by
    calc
      _ = (g.val.val * g.val.inv) i i :=
        (IsUpperUnitriangular.mul_apply_diag g.property g⁻¹.property i).symm
      _ = 1 := by rw [g.val.val_inv, Matrix.one_apply_eq]
  inv_val := by
    calc
      _ = (g.val.inv * g.val.val) i i :=
        (IsUpperUnitriangular.mul_apply_diag g⁻¹.property g.property i).symm
      _ = 1 := by rw [g.val.inv_val, Matrix.one_apply_eq]

private def diagonalHom (k : Type u) [Field k] (n : ℕ) :
    upperTriangularPoints k n ⟶ Specs.StandardGroups.multiplicativePowerPoints k (Index.{u} n) where
  app R := GrpCat.ofHom
    { toFun := diagonalUnit
      map_one' := by
        funext i
        apply Units.ext
        exact Matrix.one_apply_eq i
      map_mul' := fun g h ↦ by
        funext i
        apply Units.ext
        change (g.val.val * h.val.val) i i = g.val.val i i * h.val.val i i
        exact IsUpperUnitriangular.mul_apply_diag g.property h.property i }
  naturality R S a := by
    apply GrpCat.ext
    intro g
    funext i
    apply Units.ext
    rfl

private lemma diagonal_eq_one_iff {n : ℕ} (R : TestAlgebra k)
    (g : (upperTriangularPoints k n).obj R) :
    (diagonalHom k n).app R g = 1 ↔ IsUpperUnitriangular g.val.val := by
  constructor
  · intro h
    exact ⟨g.property, fun i ↦ congrArg (fun f : Index.{u} n → Rˣ ↦ (f i : R)) h⟩
  · intro h
    funext i
    exact Units.ext (h.2 i)

private def diagonalMap {n : ℕ} {T : AffineAlgebraicGroup k}
    (e : (groupPointsFunctor k).obj T.val ≅ upperTriangularPoints k n) :
    T.val ⟶ (StandardGroups.multiplicativePowerGroup k (Index.{u} n)).val :=
  (AffineAlgebraicGroup.groupHomEquiv _ _).symm
    (e.hom ≫ diagonalHom k n ≫ (StandardGroups.multiplicativePowerGroupPointsIso k _).inv)

private lemma diagonalMap_eq_one_iff {n : ℕ} {T : AffineAlgebraicGroup k}
    (e : (groupPointsFunctor k).obj T.val ≅ upperTriangularPoints k n)
    (R : TestAlgebra k) (x : Unipotent.GPoints T.val R) :
    Unipotent.onPoints (diagonalMap e) R x = 1 ↔
      IsUpperUnitriangular (e.hom.app R x).val.val := by
  let c := StandardGroups.multiplicativePowerGroupPointsIso k (Index.{u} n)
  rw [show Unipotent.onPoints (diagonalMap e) R x =
      c.inv.app R ((diagonalHom k n).app R (e.hom.app R x)) from Unipotent.scheme_hom_spec _ R x]
  rw [← map_one (c.inv.app R).hom]
  exact ((c.app R).groupIsoToMulEquiv.symm.injective.eq_iff).trans (diagonal_eq_one_iff R _)

private def kernelDiagonalPointsIso {n : ℕ} {T : AffineAlgebraicGroup k}
    (e : (groupPointsFunctor k).obj T.val ≅ upperTriangularPoints k n)
    (N : ClosedSubgroup T.val) (hN : IsSchemeKernel (diagonalMap e) N) :
    (groupPointsFunctor k).obj N.group ≅ Specs.Unipotent.unitriangularPoints k n := by
  let β : (groupPointsFunctor k).obj N.group ⟶ Specs.Unipotent.unitriangularPoints k n :=
    { app R := GrpCat.ofHom <|
        (((upperTriangular (Index.{u} n) R).subtype.comp (e.hom.app R).hom).comp
          (Unipotent.onPoints N.inclusion R)).codRestrict _
          (fun x ↦ (diagonalMap_eq_one_iff e R _).mp
            ((Unipotent.kernel_points (diagonalMap e) N hN R _).mpr ⟨x, rfl⟩))
      naturality R S a := by
        apply GrpCat.ext
        intro x
        apply Subtype.ext
        change (e.hom.app S (Unipotent.onPoints N.inclusion S
            (((groupPointsFunctor k).obj N.group).map a x))).val =
          ((upperTriangularPoints k n).map a (e.hom.app R (Unipotent.onPoints N.inclusion R x))).val
        rw [Unipotent.onPoints_natural]
        exact congrArg (fun t ↦ (t (Unipotent.onPoints N.inclusion R x)).val) (e.hom.naturality a) }
  refine NatIso.ofComponents (fun R ↦ (MulEquiv.ofBijective (β.app R).hom ⟨?_, ?_⟩).toGrpIso)
    (fun a ↦ β.naturality a)
  · intro x y h
    apply Unipotent.onPoints_injective N.inclusion N.isClosedImmersion R
    apply (e.app R).groupIsoToMulEquiv.injective
    apply Subtype.ext
    exact congrArg (fun g : UnitriangularMatrix n R ↦ g.val) h
  · intro g
    let t : (upperTriangularPoints k n).obj R := ⟨g.val, g.property.1⟩
    let x := e.inv.app R t
    have hx : e.hom.app R x = t := (e.app R).groupIsoToMulEquiv.apply_symm_apply t
    have hk : Unipotent.onPoints (diagonalMap e) R x = 1 := (diagonalMap_eq_one_iff e R x).mpr
      (by rw [hx]; exact g.property)
    obtain ⟨y, hy⟩ := (Unipotent.kernel_points (diagonalMap e) N hN R x).mp hk
    refine ⟨y, Subtype.ext ?_⟩
    change (e.hom.app R (Unipotent.onPoints N.inclusion R y)).val = g.val
    rw [hy, hx]

private theorem unipotent_iff_embeds (G : AffineAlgebraicGroup k) :
    IsUnipotent G ↔ EmbedsUnitriangular G := by
  obtain ⟨A, _, ⟨e⟩⟩ := groupPresentation G
  have h := Unipotent.unipotenceCriteria G A e
  exact h.1.trans (h.2.1.trans h.2.2.1)

private theorem extension_of_embedding {G : AffineAlgebraicGroup k}
    (h : EmbedsUpperTriangular G) : HasUnipotentKernelAndDiagonalizableQuotient G := by
  obtain ⟨n, T, ⟨e⟩, f, hf⟩ := h
  let D := StandardGroups.multiplicativePowerGroup k (Index.{u} n)
  let g : T.val ⟶ D.val := diagonalMap e
  haveI : IsAffine D.val.X.left := D.property.1
  obtain ⟨K, hK⟩ := schemeKernel_exists g
  obtain ⟨Q, q, i, N, hfact, _, hN, hsheaf⟩ := schemeImageQuotient G D (f ≫ g)
  have hkernel := Unipotent.kernel_of_closed_factor (f ≫ g) q i hfact.1 hfact.2.2.2.2.2 N hN
  have hdiag : ∃ (M : Type u) (_ : CommGroup M) (_ : Group.FG M),
      Nonempty (Q.val ≅ (Specs.DiagonalizableGroups.diagonalGroup k M).val) := by
    let M := Multiplicative (Index.{u} n → ℤ)
    obtain ⟨d⟩ := DiagonalizableGroups.diagonalIntegerPowers k (Index.{u} n)
    have hclosed := hfact.2.2.2.2.2
    haveI : IsClosedImmersion i.hom.hom.left := hclosed
    haveI : IsIso d.inv.hom.hom.left := by
      change IsIso (((Grp.forget (SchemeOver k)) ⋙ Over.forget _).map d.inv)
      infer_instance
    have hi : IsClosedImmersion (i ≫ d.inv).hom.hom.left := by
      change IsClosedImmersion (i.hom.hom.left ≫ d.inv.hom.hom.left)
      infer_instance
    obtain ⟨J, ⟨eQ, _⟩, _⟩ :=
      (DiagonalizableGroups.diagonalClosedSubgroups k M Q.val (i ≫ d.inv)).mp hi
    exact ⟨M ⧸ J, inferInstance, inferInstance, ⟨eQ⟩⟩
  have hfN : IsClosedImmersion (N.inclusion ≫ f).hom.hom.left := by
    haveI : IsClosedImmersion f.hom.hom.left := hf
    haveI : IsClosedImmersion N.inclusion.hom.hom.left := N.isClosedImmersion
    change IsClosedImmersion (N.inclusion.hom.hom.left ≫ f.hom.hom.left)
    infer_instance
  obtain ⟨j, hj⟩ := Unipotent.factor_through_closed
    (A := closedSubgroupAlgebraicGroup N) (B := closedSubgroupAlgebraicGroup K)
    (C := T) (N.inclusion ≫ f) K.inclusion K.isClosedImmersion (fun R x ↦ by
      apply (Unipotent.kernel_points g K hK R _).mp
      rw [← Unipotent.onPoints_comp, Category.assoc]
      exact (Unipotent.kernel_points (f ≫ g) N hN R _).mpr ⟨x, rfl⟩)
  have hjclosed : IsClosedImmersion j.hom.hom.left :=
    Unipotent.closed_of_comp j K.inclusion (hj ▸ hfN) K.isClosedImmersion
  exact ⟨N, Q, q, SchemeDerivedGroup.kernel_normal hkernel,
    (unipotent_iff_embeds _).mpr ⟨n, _, ⟨kernelDiagonalPointsIso e K hK⟩, j, hjclosed⟩,
    ⟨hkernel, hfact.2.1, hfact.2.2.1, hfact.2.2.2.1, hsheaf⟩, hdiag⟩

open private Unipotent.restrictCoaction Unipotent.faithfullyFlat_of_presentation
  Unipotent.kernel_presentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.ExactOperations
open private WeightDecomposition.sum_projections WeightDecomposition.projection_mem
  WeightDecomposition.weightProjection from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.WeightDecomposition

private theorem eigenvectors_of_extension {G : AffineAlgebraicGroup k} {B : HopfAlgebraCategory k}
    (eG : specGroup B ≅ G.val) (h : HasUnipotentKernelAndDiagonalizableQuotient G) :
    HasEigenvectors B := by
  obtain ⟨N, Q, p, _, hU, hQ, M, _, _, ⟨d⟩⟩ := h
  let A := Specs.DiagonalizableGroups.groupAlgebra k M
  let eQ : specGroup A ≅ Q.val := d.symm
  let ff := hopfSpec.fullyFaithful (R := CommRingCat.of k)
  let a : A ⟶ B := (ff.preimage (eG.hom ≫ p ≫ eQ.inv)).unop
  have ha : specGroupMap a ≫ eQ.hom = eG.hom ≫ p := by
    rw [show specGroupMap a = eG.hom ≫ p ≫ eQ.inv from ff.map_preimage _]
    simp
  letI : (kernelIdeal a).IsHopfIdeal k := hopfKernelIdeal k a
  let D := hopfQuotient B (kernelIdeal a)
  let q := hopfQuotientMap B (kernelIdeal a)
  have eN : specGroup D ≅ (closedSubgroupAlgebraicGroup N).val :=
    Unipotent.kernel_presentation p N hQ.1 a eG eQ ha
  have hN := (Unipotent.unipotenceCriteria (closedSubgroupAlgebraicGroup N) D eN).1.mp hU
  have hff := Unipotent.faithfullyFlat_of_presentation p a eG eQ ha hQ.2.1 hQ.2.2.1
  intro V _ _ _ _ ρ
  obtain ⟨v, hv, hmem⟩ := hN V (Unipotent.restrictCoaction q ρ)
  let W := kernelInvariants a ρ
  let w : W := ⟨v, hmem⟩
  have hw : w ≠ 0 := fun h ↦ hv (congrArg Subtype.val h)
  obtain ⟨σ, hσ⟩ := Unipotent.quotientActionOnKernelInvariants a hff ρ
  classical
  obtain ⟨m, hm⟩ : ∃ m : M, WeightDecomposition.weightProjection σ m w ≠ 0 := by
    by_contra! hzero
    obtain ⟨s, hs⟩ := WeightDecomposition.sum_projections σ w
    exact hw (by simpa [hzero] using hs.symm)
  let z := WeightDecomposition.weightProjection σ m w
  have hz := WeightDecomposition.mem_weightSpace.mp (WeightDecomposition.projection_mem σ m w)
  refine ⟨z.val, fun h ↦ hm (Subtype.ext h), a.hom (MonoidAlgebra.of k M m), ?_⟩
  have he := DFunLike.congr_fun hσ z
  change W.subtype.rTensor B ((a.hom.toLinearMap.lTensor W) (σ.coaction z)) =
    ρ.coaction z.val at he
  rw [show σ.coaction z = _ from hz, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul] at he
  exact he.symm

/-- The four equivalent triangularization criteria over an arbitrary field. -/
theorem triangularization : FourEquivalentConditions.{u} := by
  intro k _ G A e
  have h₁ := simpleRepresentationsIffInvariantFullFlags (A := A)
  have h₂ := embeds_of_flags e
  have h₃ := extension_of_embedding (G := G)
  have h₄ := eigenvectors_of_extension e
  exact ⟨h₁, ⟨h₂, fun h ↦ flags_of_eigenvectors (h₄ (h₃ h))⟩,
    ⟨h₃, fun h ↦ h₂ (flags_of_eigenvectors (h₄ h))⟩⟩

open private
  Unipotent.closed_surjective_points_iso Unipotent.scheme_kernel_of_points
  Unipotent.terminalIso Unipotent.stage Unipotent.Stage Unipotent.StageLink
  Unipotent.Stage.group Unipotent.Stage.inclusion
  Unipotent.Stage.closed Unipotent.Stage.range_eq Unipotent.Stage.before
  Unipotent.nextStage Unipotent.StageStep.next Unipotent.StageStep.link Unipotent.StageLink.inclusion
  Unipotent.StageLink.closed Unipotent.StageLink.commutes
  Unipotent.stageCoordinate Unipotent.pointMatrix Unipotent.before_all_eq_one
  Unipotent.before_succ Unipotent.nextEntry Unipotent.rank_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.CentralSeries

open private quotientRepresentsImage from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient

private theorem quotient_of_surjective_points {G Q : AffineAlgebraicGroup k}
    (p : G.val ⟶ Q.val) (N : ClosedSubgroup G.val) (hN : IsSchemeKernel p N)
    (hp : ∀ R, Function.Surjective (Unipotent.onPoints p R)) :
    Specs.SchemeDerivedGroup.RepresentsQuotient N p := by
  obtain ⟨I, q, i, hfac, _, _⟩ := schemeImageFactorization G Q p
  have hi : IsIso i :=
    Unipotent.closed_surjective_points_iso (A := I) (B := Q) i hfac.2.2.2.2.2 (fun R x ↦ by
      obtain ⟨y, hy⟩ := hp R x
      refine ⟨Unipotent.onPoints q R y, ?_⟩
      rw [← Unipotent.onPoints_comp, hfac.1, hy])
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  letI : IsIso (F.map i) := Functor.map_isIso _ _
  have hcomp : q.hom.hom.left ≫ i.hom.hom.left = p.hom.hom.left :=
    congrArg F.map hfac.1
  have hfac' : IsImageFactorization p p (𝟙 Q.val) := by
    letI : Flat q.hom.hom.left := hfac.2.1
    letI : Surjective q.hom.hom.left := hfac.2.2.1
    letI : LocallyOfFinitePresentation q.hom.hom.left := hfac.2.2.2.1
    letI : IsAffineHom q.hom.hom.left := hfac.2.2.2.2.1
    letI : IsIso i.hom.hom.left := inferInstanceAs (IsIso (F.map i))
    refine ⟨Category.comp_id _, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hcomp]; infer_instance
    · rw [← hcomp]; infer_instance
    · rw [← hcomp]; infer_instance
    · rw [← hcomp]; infer_instance
    · change IsClosedImmersion (𝟙 Q.val.X.left)
      infer_instance
  exact quotientRepresentsImage hfac' hN

private lemma stage_pointMatrix_id {n : ℕ} {H : AffineAlgebraicGroup k}
    (e : (groupPointsFunctor k).obj H.val ≅ Specs.Unipotent.unitriangularPoints k n)
    (R : TestAlgebra k) (x : Unipotent.GPoints H.val R) :
    Unipotent.pointMatrix (𝟙 H.val) e R x = e.hom.app R x := by
  simp [Unipotent.pointMatrix, Unipotent.onPoints]
  rfl

private lemma exists_entry_value {n : ℕ} (R : TestAlgebra k) (p : StrictUpper.{u} n) (r : R) :
    ∃ g : UnitriangularMatrix n R,
      InCoordinateFlag (coordinateRank p) g ∧ Unipotent.nextEntry (coordinateRank p) g = r := by
  classical
  let M : Matrix (Index.{u} n) (Index.{u} n) R := fun i j ↦
    if (i, j) = p.val then r else (1 : Matrix _ _ _) i j
  have hM : IsUpperUnitriangular M := by
    constructor
    · intro i j hij
      change j < i at hij
      have hp : (i, j) ≠ p.val := by
        intro h
        have h' : (i, j).1 < (i, j).2 := h ▸ p.property
        exact (not_lt_of_gt hij) h'
      simp [M, hp, Matrix.one_apply_ne hij.ne']
    · intro i
      have hp : (i, i) ≠ p.val := by
        intro h
        have h' : (i, i).1 < (i, i).2 := h ▸ p.property
        exact lt_irrefl _ h'
      simp [M, hp]
  have hd : M.det = 1 := by rw [Matrix.det_of_isUpperTriangular hM.1]; simp [hM.2]
  let g : UnitriangularMatrix n R :=
    ⟨Matrix.GeneralLinearGroup.mk'' M (hd ▸ isUnit_one), hM⟩
  refine ⟨g, ?_, ?_⟩
  · intro q hq
    have hpair : q.val ≠ p.val := fun h ↦ hq.ne (congrArg coordinateRank (Subtype.ext h))
    change M q.val.1 q.val.2 = 0
    simp [M, hpair, Matrix.one_apply_ne q.property.ne]
  · unfold Unipotent.nextEntry
    let h : ∃ q : StrictUpper.{u} n, coordinateRank q = coordinateRank p := ⟨p, rfl⟩
    rw [dite_eq_left h]
    have he : h.choose = p := Unipotent.rank_injective h.choose_spec
    change M h.choose.val.1 h.choose.val.2 = r
    rw [he]
    simp [M]

private theorem unitriangular_split_step {n : ℕ} {H : AffineAlgebraicGroup k}
    {e : (groupPointsFunctor k).obj H.val ≅ Specs.Unipotent.unitriangularPoints k n} {s : ℕ}
    (X : Unipotent.Stage (𝟙 H.val) e s) (Y : Unipotent.Stage (𝟙 H.val) e (s + 1))
    (link : Unipotent.StageLink X Y)
    (ih : ∀ L : AffineAlgebraicGroup k, (L.val ≅ (Unipotent.Stage.group Y).val) →
      Specs.SchemeDerivedGroup.IsSplitSolvable L.val)
    (L : AffineAlgebraicGroup k) (i : L.val ≅ (Unipotent.Stage.group X).val) :
    Specs.SchemeDerivedGroup.IsSplitSolvable L.val := by
  classical
  let j : (Unipotent.Stage.group Y).val ⟶ L.val := (Unipotent.StageLink.inclusion link) ≫ i.inv
  have hj : IsClosedImmersion j.hom.hom.left := by
    letI : IsClosedImmersion (Unipotent.StageLink.inclusion link).hom.hom.left := (Unipotent.StageLink.closed link)
    letI : IsIso i.inv.hom.hom.left := by
      change IsIso (((Grp.forget (SchemeOver k)) ⋙ Over.forget _).map i.inv)
      infer_instance
    change IsClosedImmersion ((Unipotent.StageLink.inclusion link).hom.hom.left ≫ i.inv.hom.hom.left)
    exact IsClosedImmersion.comp _ _
  let inc : L.val ⟶ H.val := i.hom ≫ (Unipotent.Stage.inclusion X)
  have hjcomp : j ≫ inc = (Unipotent.Stage.inclusion Y) := by
    dsimp only [j, inc]
    rw [Category.assoc, Iso.inv_hom_id_assoc]
    exact Unipotent.StageLink.commutes link
  have hinc : IsClosedImmersion inc.hom.hom.left := by
    letI : IsClosedImmersion (Unipotent.Stage.inclusion X).hom.hom.left := (Unipotent.Stage.closed X)
    letI : IsIso i.hom.hom.hom.left := by
      change IsIso (((Grp.forget (SchemeOver k)) ⋙ Over.forget _).map i.hom)
      infer_instance
    change IsClosedImmersion (i.hom.hom.hom.left ≫ (Unipotent.Stage.inclusion X).hom.hom.left)
    exact IsClosedImmersion.comp _ _
  have hstep (R : TestAlgebra k) (x : Unipotent.GPoints L.val R) :
      Unipotent.nextEntry s (Unipotent.pointMatrix (𝟙 H.val) e R (Unipotent.onPoints inc R x)) = 0 ↔
        ∃ y : Unipotent.GPoints (Unipotent.Stage.group Y).val R, Unipotent.onPoints j R y = x := by
    have hx : InCoordinateFlag s (Unipotent.pointMatrix (𝟙 H.val) e R (Unipotent.onPoints inc R x)) :=
      Unipotent.Stage.before X R (Unipotent.onPoints i.hom R x)
    constructor
    · intro hz
      obtain ⟨y, hy⟩ := (Unipotent.Stage.range_eq Y R _).mp ((Unipotent.before_succ s _).mpr ⟨hx, hz⟩)
      refine ⟨y, Unipotent.onPoints_injective inc hinc R ?_⟩
      rw [← Unipotent.onPoints_comp, hjcomp, hy]
    · rintro ⟨y, rfl⟩
      rw [← Unipotent.onPoints_comp, hjcomp]
      exact ((Unipotent.before_succ s _).mp (Unipotent.Stage.before Y R y)).2
  by_cases hr : ∃ p : StrictUpper.{u} n, coordinateRank p = s
  · let A := StandardGroups.additiveGroup k
    let c := StandardGroups.additiveGroupPointsIso k
    let α := (groupPointsFunctor k).map i.hom ≫ Unipotent.stageCoordinate X ≫ c.inv
    let q : L.val ⟶ A.val := (AffineAlgebraicGroup.groupHomEquiv L A).symm α
    have hvalue (R : TestAlgebra k) (x : Unipotent.GPoints L.val R) :
        (c.app R).groupIsoToMulEquiv (Unipotent.onPoints q R x) =
          Multiplicative.ofAdd (Unipotent.nextEntry s (Unipotent.pointMatrix (𝟙 H.val) e R (Unipotent.onPoints inc R x))) := by
      rw [show Unipotent.onPoints q R x = α.app R x from
        Unipotent.scheme_hom_spec (G := L) (H := A) α R x]
      exact (c.app R).groupIsoToMulEquiv.apply_symm_apply _
    have hk (R : TestAlgebra k) (x : Unipotent.GPoints L.val R) :
        Unipotent.onPoints q R x = 1 ↔ ∃ y : Unipotent.GPoints (Unipotent.Stage.group Y).val R, Unipotent.onPoints j R y = x := by
      rw [← hstep R x, ← (c.app R).groupIsoToMulEquiv.injective.eq_iff, map_one, hvalue]
      rfl
    have hker := Unipotent.scheme_kernel_of_points (A := L) (B := (Unipotent.Stage.group Y)) (C := A) q j hj hk
    refine Specs.SchemeDerivedGroup.IsSplitSolvable.step ⟨_, j, hj⟩ (SchemeDerivedGroup.kernel_normal hker)
      (ih (Unipotent.Stage.group Y) (Iso.refl _)) A q (quotient_of_surjective_points q _ hker ?_) (Or.inl ⟨c⟩)
    intro R r
    obtain ⟨p, rfl⟩ := hr
    obtain ⟨g, hg, hgval⟩ := exists_entry_value R p (Multiplicative.toAdd (c.hom.app R r))
    let x := e.inv.app R g
    have he : Unipotent.pointMatrix (𝟙 H.val) e R x = g := by
      rw [stage_pointMatrix_id]
      exact (e.app R).groupIsoToMulEquiv.apply_symm_apply _
    obtain ⟨y, hy⟩ := (Unipotent.Stage.range_eq X R x).mp (by rwa [he])
    let z := Unipotent.onPoints i.inv R y
    have hz : Unipotent.onPoints inc R z = x := by
      change Unipotent.onPoints (i.inv ≫ i.hom ≫ (Unipotent.Stage.inclusion X)) R y = x
      simpa using hy
    refine ⟨z, (c.app R).groupIsoToMulEquiv.injective ?_⟩
    rw [hvalue, hz, he, hgval]
    rfl
  · have hjiso := Unipotent.closed_surjective_points_iso (A := (Unipotent.Stage.group Y)) (B := L) j hj (fun R x ↦
      (hstep R x).mp (by simp [Unipotent.nextEntry, hr]))
    exact ih L (@asIso _ _ _ _ j hjiso).symm

private theorem unitriangular_split_solvable {n : ℕ} (H : AffineAlgebraicGroup k)
    (e : (groupPointsFunctor k).obj H.val ≅ Specs.Unipotent.unitriangularPoints k n) :
    Specs.SchemeDerivedGroup.IsSplitSolvable H.val := by
  classical
  let S := Unipotent.stage (f := 𝟙 H.val) (e := e)
  let length := n * (n + 1)
  have go (s : ℕ) (hs : s ≤ length) : ∀ (L : AffineAlgebraicGroup k),
      (L.val ≅ (Unipotent.Stage.group (S s)).val) → Specs.SchemeDerivedGroup.IsSplitSolvable L.val := by
    induction hs using Nat.decreasingInduction with
    | self =>
      intro L i
      apply Specs.SchemeDerivedGroup.IsSplitSolvable.trivial
      refine ⟨i ≪≫ Unipotent.terminalIso (Unipotent.Stage.group (S length)) (fun R y ↦ ?_)⟩
      apply Unipotent.onPoints_injective (Unipotent.Stage.inclusion (S length)) (Unipotent.Stage.closed (S length)) R
      apply (e.app R).groupIsoToMulEquiv.injective
      rw [(Unipotent.onPoints (Unipotent.Stage.inclusion (S length)) R).map_one,
        (e.app R).groupIsoToMulEquiv.map_one]
      change e.hom.app R (Unipotent.onPoints (Unipotent.Stage.inclusion (S length)) R y) =
        (1 : UnitriangularMatrix n R)
      rw [← stage_pointMatrix_id e R]
      exact Unipotent.before_all_eq_one _ (Unipotent.Stage.before (S length) R y)
    | of_succ s hs ih =>
      exact unitriangular_split_step (S s) (Unipotent.StageStep.next (Unipotent.nextStage (S s)))
        (Unipotent.StageStep.link (Unipotent.nextStage (S s))) ih
  exact go 0 (Nat.zero_le _) H (Iso.refl _)

private def unitCoordinate (k : Type u) [Field k] {Idx : Type u} (i : Idx) :
    Specs.StandardGroups.multiplicativePowerPoints k Idx ⟶ Specs.StandardGroups.multiplicativePoints k where
  app R := GrpCat.ofHom (Pi.evalMonoidHom _ i)
  naturality R S a := by apply GrpCat.ext; intro x; rfl

private theorem split_solvable_of_unit_coordinates {Idx : Type u} [DecidableEq Idx] (I : Finset Idx) :
    ∀ (G : AffineAlgebraicGroup k)
      (α : (groupPointsFunctor k).obj G.val ⟶ Specs.StandardGroups.multiplicativePowerPoints k Idx),
      (∀ (R : TestAlgebra k) (v : Idx → Rˣ), ∃ x : Unipotent.GPoints G.val R,
        ∀ i ∈ I, α.app R x i = v i) →
      (∀ (L : AffineAlgebraicGroup k) (j : L.val ⟶ G.val), IsClosedImmersion j.hom.hom.left →
        (∀ (R : TestAlgebra k) (x : Unipotent.GPoints G.val R),
          (∀ i ∈ I, α.app R x i = 1) ↔ ∃ y : Unipotent.GPoints L.val R, Unipotent.onPoints j R y = x) →
        Specs.SchemeDerivedGroup.IsSplitSolvable L.val) →
      Specs.SchemeDerivedGroup.IsSplitSolvable G.val := by
  induction I using Finset.induction_on with
  | empty =>
    intro G α _ h
    apply h G (𝟙 G.val)
    · change IsClosedImmersion (𝟙 G.val.X.left); infer_instance
    · intro R x
      simp only [Finset.notMem_empty, false_implies, implies_true, true_iff]
      exact ⟨x, rfl⟩
  | @insert i I hi ih =>
    intro G α hs hbase
    let M := StandardGroups.multiplicativeGroup k
    let e := StandardGroups.multiplicativeGroupPointsIso k
    let β := α ≫ unitCoordinate k i ≫ e.inv
    let q : G.val ⟶ M.val := (AffineAlgebraicGroup.groupHomEquiv G M).symm β
    have hval (R : TestAlgebra k) (x : Unipotent.GPoints G.val R) :
        (e.app R).groupIsoToMulEquiv (Unipotent.onPoints q R x) = α.app R x i := by
      rw [Unipotent.scheme_hom_spec β]
      exact (e.app R).groupIsoToMulEquiv.apply_symm_apply _
    haveI : IsAffine M.val.X.left := M.property.1
    obtain ⟨N, hN⟩ := schemeKernel_exists q
    let K := closedSubgroupAlgebraicGroup N
    let γ := (groupPointsFunctor k).map N.inclusion ≫ α
    have hker (R : TestAlgebra k) (x : Unipotent.GPoints G.val R) :
        α.app R x i = 1 ↔ ∃ y : Unipotent.GPoints K.val R, Unipotent.onPoints N.inclusion R y = x := by
      rw [← hval R x]
      change (e.app R).groupIsoToMulEquiv (Unipotent.onPoints q R x) =
        (1 : (Specs.StandardGroups.multiplicativePoints k).obj R) ↔ _
      rw [← (e.app R).groupIsoToMulEquiv.map_one, (e.app R).groupIsoToMulEquiv.injective.eq_iff]
      exact Unipotent.kernel_points q N hN R x
    have hsplit : Specs.SchemeDerivedGroup.IsSplitSolvable K.val := by
      apply ih K γ
      · intro R v
        obtain ⟨x, hx⟩ := hs R (Function.update v i 1)
        have hxi : α.app R x i = 1 := by
          simpa using hx i (Finset.mem_insert_self i I)
        obtain ⟨y, hy⟩ := (hker R x).mp hxi
        refine ⟨y, fun j hj ↦ ?_⟩
        change α.app R (Unipotent.onPoints N.inclusion R y) j = v j
        have hji : j ≠ i := by
          intro he
          subst j
          exact hi hj
        rw [hy, hx j (Finset.mem_insert_of_mem hj), Function.update_of_ne hji]
      · intro L j hj hL
        have hj' : IsClosedImmersion (j ≫ N.inclusion).hom.hom.left := by
          letI : IsClosedImmersion j.hom.hom.left := hj
          letI : IsClosedImmersion N.inclusion.hom.hom.left := N.isClosedImmersion
          change IsClosedImmersion (j.hom.hom.left ≫ N.inclusion.hom.hom.left)
          exact @IsClosedImmersion.comp _ _ _ _ _ hj N.isClosedImmersion
        apply hbase L (j ≫ N.inclusion) hj'
        intro R x
        constructor
        · intro hx
          obtain ⟨y, hy⟩ := (hker R x).mp (hx i (Finset.mem_insert_self i I))
          obtain ⟨z, hz⟩ := (hL R y).mp (fun j hj ↦ by
            change α.app R (Unipotent.onPoints N.inclusion R y) j = 1
            rw [hy]
            exact hx j (Finset.mem_insert_of_mem hj))
          exact ⟨z, (Unipotent.onPoints_comp j N.inclusion R z).trans
            ((congrArg (Unipotent.onPoints N.inclusion R) hz).trans hy)⟩
        · rintro ⟨z, rfl⟩
          rw [Unipotent.onPoints_comp]
          intro a ha
          rcases Finset.mem_insert.mp ha with rfl | ha
          · exact (hker R _).mpr ⟨_, rfl⟩
          · exact (hL R (Unipotent.onPoints j R z)).mpr ⟨z, rfl⟩ a ha
    refine Specs.SchemeDerivedGroup.IsSplitSolvable.step N (SchemeDerivedGroup.kernel_normal hN) hsplit M q
      (quotient_of_surjective_points q N hN ?_) (Or.inr ⟨e⟩)
    intro R y
    obtain ⟨x, hx⟩ := hs R (fun _ ↦ e.hom.app R y)
    exact ⟨x, (e.app R).groupIsoToMulEquiv.injective
      ((hval R x).trans (hx i (Finset.mem_insert_self i I)))⟩

private lemma diagonal_surjective {n : ℕ} (R : TestAlgebra k) :
    Function.Surjective ((diagonalHom k n).app R).hom := by
  intro v
  let m : Matrix (Index.{u} n) (Index.{u} n) R := Matrix.diagonal (fun i ↦ (v i : R))
  have h : IsUnit m.det := by
    rw [Matrix.det_diagonal]
    exact IsUnit.prod_iff.mpr (fun i _ ↦ (v i).isUnit)
  let g : (upperTriangularPoints k n).obj R :=
    ⟨Matrix.GeneralLinearGroup.mk'' m h, fun i j hij ↦ Matrix.diagonal_apply_ne _ hij.ne'⟩
  exact ⟨g, funext fun i ↦ Units.ext (Matrix.diagonal_apply_eq _ _)⟩

/-- The diagonal coordinates and the strictly upper entries give a split solvable series. -/
theorem upperTriangularSplitSolvable : UpperTriangularSplitSolvable.{u} := by
  intro k _ n T e
  apply split_solvable_of_unit_coordinates
    (Finset.univ : Finset (Index.{u} n)) T (e.hom ≫ diagonalHom k n)
  · intro R v
    obtain ⟨g, hg⟩ := diagonal_surjective R (n := n) v
    refine ⟨e.inv.app R g, fun i _ ↦ ?_⟩
    change (diagonalHom k n).app R (e.hom.app R (e.inv.app R g)) i = v i
    rw [show e.hom.app R (e.inv.app R g) = g from
      (e.app R).groupIsoToMulEquiv.apply_symm_apply g, hg]
  · intro L j hj hL
    let D := StandardGroups.multiplicativePowerGroup k (Index.{u} n)
    let p : T.val ⟶ D.val := diagonalMap e
    have hk (R : TestAlgebra k) (x : Unipotent.GPoints T.val R) :
        Unipotent.onPoints p R x = 1 ↔ ∃ y : Unipotent.GPoints L.val R, Unipotent.onPoints j R y = x := by
      rw [diagonalMap_eq_one_iff e]
      rw [← diagonal_eq_one_iff]
      have he : (diagonalHom k n).app R (e.hom.app R x) = 1 ↔
          ∀ i, (diagonalHom k n).app R (e.hom.app R x) i = 1 :=
        ⟨fun h i ↦ congrFun h i, funext⟩
      rw [he]
      constructor
      · intro h
        exact (hL R x).mp (fun i _ ↦ h i)
      · intro h i
        exact (hL R x).mpr h i (Finset.mem_univ i)
    have h := Unipotent.scheme_kernel_of_points p j hj hk
    exact unitriangular_split_solvable L (kernelDiagonalPointsIso e ⟨_, j, hj⟩ h)

end

end LinearAlgebraicGroups.Triangularization
