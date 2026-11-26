import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.Criteria
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.FaithfulLinearization
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite WithConv
open scoped TensorProduct

universe u
noncomputable section

namespace LinearAlgebraicGroups
namespace Unipotent

open Specs.Unipotent
open Specs.StandardGroups
open RationalRepresentations

abbrev unitriangularPoints : UnitriangularPointsType.{u} := Specs.Unipotent.unitriangularPoints

abbrev IsUnipotent : IsUnipotentType.{u} := @Specs.Unipotent.IsUnipotent

open private
  StandardGroups.Representation
  StandardGroups.Representation.mk
  StandardGroups.Representation.equiv
  StandardGroups.Representation.hopf
  StandardGroups.Representation.represents
  StandardGroups.Representation.convolutionIso
  StandardGroups.Representation.operations
  StandardGroups.Representation.delta
  StandardGroups.Representation.equiv_mul
  StandardGroups.Representation.equiv_epsilon
  StandardGroups.Representation.epsilon
  StandardGroups.spectrumPointsIso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups

variable {k : Type u} [Field k]

private lemma coordinateMatrix_isUnitriangular (n : ℕ) :
    IsUpperUnitriangular (coordinateMatrix k n) := by
  constructor
  · intro i j h
    change j < i at h
    simp [coordinateMatrix, not_lt_of_gt h, ne_of_gt h]
  · simp [coordinateMatrix]

private lemma unitriangular_det {ι R : Type*}
    [Fintype ι] [LinearOrder ι] [DecidableEq ι] [CommRing R]
    {M : Matrix ι ι R} (h : IsUpperUnitriangular M) : M.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular h.1]
  simp [h.2]

private def evaluateUnitriangular {n : ℕ} (R : TestAlgebra k) (f : Coordinates k n →ₐ[k] R) :
    (unitriangularPoints k n).obj R := by
  let M := f.mapMatrix (coordinateMatrix k n)
  have h : IsUpperUnitriangular M :=
    ⟨(coordinateMatrix_isUnitriangular (k := k) n).1.map f,
      fun i ↦ by change f (coordinateMatrix k n i i) = 1; simp [coordinateMatrix]⟩
  exact ⟨Matrix.GeneralLinearGroup.mk'' M (unitriangular_det h ▸ isUnit_one), h⟩

private def unitriangularRepresentation (k : Type u) [Field k] (n : ℕ) :
    StandardGroups.Representation (Coordinates k n) (unitriangularPoints k n) := by
  refine StandardGroups.Representation.mk (fun R ↦ ?_) ?_
  · exact
      { toFun := evaluateUnitriangular R
        invFun := fun g ↦ MvPolynomial.aeval (fun p : StrictUpper n ↦ g.val.val p.val.1 p.val.2)
        left_inv := fun f ↦ by
          apply MvPolynomial.algHom_ext
          intro p
          rw [MvPolynomial.aeval_X]
          change f (coordinateMatrix k n p.val.1 p.val.2) = _
          rw [coordinateMatrix, dite_eq_left p.property]
        right_inv := fun g ↦ by
          apply Subtype.ext
          apply Matrix.GeneralLinearGroup.ext
          intro i j
          change MvPolynomial.aeval (fun p : StrictUpper n ↦ g.val.val p.val.1 p.val.2)
            (coordinateMatrix k n i j) = _
          rcases lt_trichotomy i j with h | rfl | h
          · rw [coordinateMatrix, dite_eq_left h, MvPolynomial.aeval_X]
          · simpa [coordinateMatrix] using (g.property.2 i).symm
          · simp [coordinateMatrix, not_lt_of_gt h, ne_of_gt h, g.property.1 h] }
  · intro R S a f
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rfl

/-- The scheme representing the unitriangular point functor. -/
def unitriangularGroup (k : Type u) [Field k] (n : ℕ) : Specs.AffineAlgebraicGroup k :=
  letI := StandardGroups.Representation.hopf (unitriangularRepresentation k n)
  spectrum k (Coordinates k n)

theorem unitriangularGroupSpecification : UnitriangularGroup.{u} := by
  intro k _ n
  let P := unitriangularRepresentation k n
  exact ⟨StandardGroups.Representation.operations P, StandardGroups.Representation.represents P _ (fun _ _ ↦ rfl)⟩

/-- On points, this is the group of upper unitriangular matrices over the test ring. -/
def unitriangularGroupPointsIso (k : Type u) [Field k] (n : ℕ) :
    (groupPointsFunctor k).obj (unitriangularGroup k n).val ≅ unitriangularPoints k n :=
  letI := StandardGroups.Representation.hopf (unitriangularRepresentation k n)
  StandardGroups.spectrumPointsIso (StandardGroups.Representation.convolutionIso (unitriangularRepresentation k n))

private def unitriangularHopfAlgebra (k : Type u) [Field k] (n : ℕ) : HopfAlgebraCategory k :=
  letI := StandardGroups.Representation.hopf (unitriangularRepresentation k n)
  CommHopfAlgCat.of k (Coordinates k n)

private lemma unitriangular_comul (n : ℕ) (i j : Index.{u} n) :
    Coalgebra.comul (R := k) (A := unitriangularHopfAlgebra k n) (coordinateMatrix k n i j) =
      ∑ l : Index.{u} n, coordinateMatrix k n i l ⊗ₜ[k] coordinateMatrix k n l j := by
  let P := unitriangularRepresentation k n
  let A := Coordinates k n
  let f : A →ₐ[k] A ⊗[k] A := Algebra.TensorProduct.includeLeft
  let g : A →ₐ[k] A ⊗[k] A := Algebra.TensorProduct.includeRight
  have h := StandardGroups.Representation.equiv_mul P f g
  have he := congrArg (fun m : (unitriangularPoints k n).obj (CommAlgCat.of k (A ⊗[k] A)) ↦
    m.val.val i j) h
  change StandardGroups.Representation.delta P (coordinateMatrix k n i j) =
    (f.mapMatrix (coordinateMatrix k n) * g.mapMatrix (coordinateMatrix k n)) i j at he
  have he' := he
  rw [Matrix.mul_apply] at he'
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, f, g,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at he'
  have hdef : (StandardGroups.Representation.operations P).delta =
      StandardGroups.Representation.delta P := rfl
  exact (congrArg (fun f : A →ₐ[k] A ⊗[k] A ↦ f (coordinateMatrix k n i j)) hdef).trans he'

private lemma invariant_iff_coaction (A : HopfAlgebraCategory k)
    {V : Type u} [AddCommGroup V] [Module k V] (ρ : RightComodule k A V) (v : V) :
    v ∈ invariants A ρ ↔ ρ.coaction v = v ⊗ₜ[k] (1 : A) := by
  change ρ.coaction v - v ⊗ₜ[k] (1 : A) = 0 ↔ _
  exact sub_eq_zero

private lemma exists_tensor_filtration {A : HopfAlgebraCategory k}
    (C : ℕ → Submodule k A) (hC : Monotone C) (hEx : ∀ x : A, ∃ r, x ∈ C r)
    {V : Type u} [AddCommGroup V] [Module k V] (t : V ⊗[k] A) :
    ∃ r, (C r).mkQ.lTensor V t = 0 := by
  induction t using TensorProduct.inductionOn with
  | tmul v a =>
    obtain ⟨r, hr⟩ := hEx a
    exact ⟨r, by simp [(Submodule.Quotient.mk_eq_zero _).mpr hr]⟩
  | add x y hx hy =>
    obtain ⟨r, hr⟩ := hx
    obtain ⟨s, hs⟩ := hy
    refine ⟨max r s, ?_⟩
    have mono (i j : ℕ) (hij : i ≤ j) (z : V ⊗[k] A) (hz : (C i).mkQ.lTensor V z = 0) :
        (C j).mkQ.lTensor V z = 0 := by
      have hz' : z ∈ LinearMap.ker ((C i).mkQ.lTensor V) := hz
      rw [lTensor_mkQ] at hz'
      obtain ⟨w, rfl⟩ := hz'
      have hzero : ((C j).mkQ).comp (C i).subtype = 0 := by
        ext a
        exact (Submodule.Quotient.mk_eq_zero _).mpr (hC hij a.property)
      rw [← LinearMap.lTensor_comp_apply, hzero, LinearMap.lTensor_zero, LinearMap.zero_apply]
    rw [map_add, mono r _ (le_max_left _ _) _ hr, mono s _ (le_max_right _ _) _ hs, add_zero]

private lemma tensorFiltration_killed {A : HopfAlgebraCategory k}
    (C : ℕ → Submodule k A) (hC : Monotone C) (r : ℕ) {t : A ⊗[k] A}
    (ht : t ∈ tensorFiltration C (r + 1)) :
    TensorProduct.map (C r).mkQ (C r).mkQ t = 0 := by
  change t ∈ LinearMap.ker (TensorProduct.map (C r).mkQ (C r).mkQ)
  apply (show tensorFiltration C (r + 1) ≤ _ from ?_) ht
  apply iSup_le
  intro i
  rintro _ ⟨x, rfl⟩
  rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← TensorProduct.map_comp]
  rcases le_or_gt (i : ℕ) r with hi | hi
  · have hz : (C r).mkQ.comp (C (i : ℕ)).subtype = 0 := by
      ext a
      exact (Submodule.Quotient.mk_eq_zero _).mpr (hC hi a.property)
    rw [hz, TensorProduct.map_zero_left, LinearMap.zero_apply]
  · have hj : r + 1 - (i : ℕ) ≤ r := by omega
    have hz : (C r).mkQ.comp (C (r + 1 - (i : ℕ))).subtype = 0 := by
      ext a
      exact (Submodule.Quotient.mk_eq_zero _).mpr (hC hj a.property)
    rw [hz, TensorProduct.map_zero_right, LinearMap.zero_apply]

private lemma invariant_of_degree_zero (A : HopfAlgebraCategory k)
    {V : Type u} [AddCommGroup V] [Module k V] (ρ : RightComodule k A V) (v : V)
    (h : (Submodule.span k ({1} : Set A)).mkQ.lTensor V (ρ.coaction v) = 0) :
    v ∈ invariants A ρ := by
  let S := Submodule.span k ({1} : Set A)
  have hm : ρ.coaction v ∈ LinearMap.ker (S.mkQ.lTensor V) := h
  rw [lTensor_mkQ] at hm
  obtain ⟨t, ht⟩ := hm
  have he : ∃ w : V, S.subtype.lTensor V t = w ⊗ₜ[k] (1 : A) := by
    clear ht
    induction t using TensorProduct.inductionOn with
    | tmul x a =>
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp a.property
      exact ⟨c • x, by rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, ← hc,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul']⟩
    | add x y hx hy =>
      obtain ⟨w, hw⟩ := hx
      obtain ⟨z, hz⟩ := hy
      exact ⟨w + z, by rw [map_add, hw, hz, TensorProduct.add_tmul]⟩
  obtain ⟨w, hw⟩ := he
  have hρ := ht.symm.trans hw
  have hv := ρ.counit v
  rw [hρ] at hv
  have hwv : w = v := by simpa using hv
  exact (invariant_iff_coaction A ρ v).mpr (hwv ▸ hρ)

theorem hasInvariantVectors_of_filtration {A : HopfAlgebraCategory k}
    (h : HasCoalgebraFiltration A) : HasInvariantVectors A := by
  intro V _ _ _ _ ρ
  obtain ⟨C, hC, hex, h0, hΔ⟩ := h
  by_contra! hinv
  have inject (r : ℕ) :
      Function.Injective (((C r).mkQ.lTensor V).comp ρ.coaction) := by
    induction r with
    | zero =>
      apply LinearMap.ker_eq_bot.mp
      apply (Submodule.eq_bot_iff _).mpr
      intro v hv
      change (C 0).mkQ.lTensor V (ρ.coaction v) = 0 at hv
      rw [h0] at hv
      by_contra hn
      exact hinv v hn (invariant_of_degree_zero A ρ v hv)
    | succ r ih =>
      apply LinearMap.ker_eq_bot.mp
      apply (Submodule.eq_bot_iff _).mpr
      intro v hv
      change (C (r + 1)).mkQ.lTensor V (ρ.coaction v) = 0 at hv
      have hm : ρ.coaction v ∈ LinearMap.ker ((C (r + 1)).mkQ.lTensor V) := hv
      rw [lTensor_mkQ] at hm
      let Q := A ⧸ C r
      let q : A →ₗ[k] Q := (C r).mkQ
      let F : V →ₗ[k] V ⊗[k] Q := (q.lTensor V).comp ρ.coaction
      let D := TensorProduct.map q q
      have hkill : D.comp ((Coalgebra.comul (R := k)).comp (C (r + 1)).subtype) = 0 := by
        ext a
        exact tensorFiltration_killed C hC r (hΔ _ _ a.property)
      obtain ⟨w, hw⟩ := hm
      have hright : D.lTensor V ((Coalgebra.comul (R := k)).lTensor V (ρ.coaction v)) = 0 := by
        rw [← hw, ← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply,
          LinearMap.comp_assoc, hkill, LinearMap.lTensor_zero, LinearMap.zero_apply]
      have hcomm :
          (TensorProduct.assoc k V Q Q).toLinearMap.comp (TensorProduct.map F q) =
            (D.lTensor V).comp ((TensorProduct.assoc k V A A).toLinearMap.comp
              (ρ.coaction.rTensor A)) := by
        apply TensorProduct.ext'
        intro x a
        change TensorProduct.assoc k V Q Q ((q.lTensor V (ρ.coaction x)) ⊗ₜ[k] q a) =
          D.lTensor V (TensorProduct.assoc k V A A (ρ.coaction x ⊗ₜ[k] a))
        generalize ρ.coaction x = t
        induction t using TensorProduct.inductionOn with
        | tmul y b =>
          simp [D, LinearMap.lTensor_tmul,
            TensorProduct.assoc_tmul, TensorProduct.map_tmul]
        | add x y hx hy =>
          simpa only [map_add, TensorProduct.add_tmul] using congrArg₂ (· + ·) hx hy
      have hz := DFunLike.congr_fun hcomm (ρ.coaction v)
      change TensorProduct.assoc k V Q Q (TensorProduct.map F q (ρ.coaction v)) =
        D.lTensor V (TensorProduct.assoc k V A A (ρ.coaction.rTensor A (ρ.coaction v))) at hz
      rw [ρ.coassoc, hright] at hz
      have hcomp : TensorProduct.map F q = (F.rTensor Q).comp (q.lTensor V) := by
        apply TensorProduct.ext'
        intro x a
        rfl
      rw [hcomp, LinearMap.comp_apply] at hz
      have hF : Function.Injective F := ih
      have hf := Module.Flat.rTensor_preserves_injective_linearMap (M := Q) F hF
      have hzero : F.rTensor Q (F v) = 0 :=
        (TensorProduct.assoc k V Q Q).injective (hz.trans (map_zero _).symm)
      exact hF ((hf (hzero.trans (map_zero _).symm)).trans (map_zero F).symm)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨r, hr⟩ := exists_tensor_filtration C hC hex (ρ.coaction v)
  exact hv (inject r (hr.trans (map_zero _).symm))

section Flags

variable (A : HopfAlgebraCategory k)
variable {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

private def quotientCoaction (ρ : RightComodule k A V) (p : V →ₗ[k] W)
    (hp : Function.Surjective p) (f : W →ₗ[k] W ⊗[k] A)
    (hf : f.comp p = (p.rTensor A).comp ρ.coaction) : RightComodule k A W where
  coaction := f
  coassoc w := by
    obtain ⟨v, rfl⟩ := hp w
    have hv : f (p v) = p.rTensor A (ρ.coaction v) := DFunLike.congr_fun hf v
    have hassoc :
        (TensorProduct.assoc k W A A).toLinearMap.comp ((p.rTensor A).rTensor A) =
          (p.rTensor (A ⊗[k] A)).comp (TensorProduct.assoc k V A A).toLinearMap := by
      apply TensorProduct.ext_threefold
      intro x a b
      rfl
    calc
      _ = TensorProduct.assoc k W A A (((f.comp p).rTensor A) (ρ.coaction v)) := by
        rw [hv, LinearMap.rTensor_comp_apply]
      _ = p.rTensor (A ⊗[k] A)
          (TensorProduct.assoc k V A A (ρ.coaction.rTensor A (ρ.coaction v))) := by
        rw [hf, LinearMap.rTensor_comp_apply]
        exact DFunLike.congr_fun hassoc (ρ.coaction.rTensor A (ρ.coaction v))
      _ = _ := by
        rw [ρ.coassoc, hv]
        let Δ : A →ₗ[k] A ⊗[k] A := Coalgebra.comul
        have he : (p.rTensor (A ⊗[k] A)).comp (Δ.lTensor V) =
            (Δ.lTensor W).comp (p.rTensor A) := by
          apply TensorProduct.ext'
          intro x a
          rfl
        exact DFunLike.congr_fun he (ρ.coaction v)
  counit w := by
    obtain ⟨v, rfl⟩ := hp w
    have hv : f (p v) = p.rTensor A (ρ.coaction v) := DFunLike.congr_fun hf v
    let β (X : Type u) [AddCommGroup X] [Module k X] :=
      (TensorProduct.rid k X).toLinearMap.comp
        ((Coalgebra.counit (R := k) (A := A)).lTensor X)
    have he : (β W).comp (p.rTensor A) = p.comp (β V) := by
      apply TensorProduct.ext'
      intro x a
      simp only [β, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
        LinearEquiv.coe_coe, TensorProduct.rid_tmul, map_smul]
    change β W (f (p v)) = _
    rw [hv]
    exact (DFunLike.congr_fun he (ρ.coaction v)).trans (congrArg p (ρ.counit v))

private def IsTriangularBasis {n : ℕ} (ρ : RightComodule k A V)
    (b : Module.Basis (Fin n) k V) : Prop :=
  ∀ j, ∃ c : Fin n → A, (∀ i, j ≤ i → c i = 0) ∧
    ρ.coaction (b j) = b j ⊗ₜ[k] 1 + ∑ i, b i ⊗ₜ[k] c i

private lemma triangularBasis_of_invariants (h : HasInvariantVectors A) (n : ℕ) :
    ∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V],
    Module.finrank k V = n → ∀ ρ : RightComodule k A V,
      ∃ b : Module.Basis (Fin n) k V, IsTriangularBasis A ρ b := by
  induction n with
  | zero =>
    intro V _ _ _ hn ρ
    exact ⟨(Module.finBasis k V).reindex (finCongr hn), fun j ↦ Fin.elim0 j⟩
  | succ n ih =>
    intro V _ _ _ hn ρ
    let := Module.nontrivial_of_finrank_pos (R := k) (M := V) (by omega)
    obtain ⟨v, hv, hvfix⟩ := h V ρ
    have hρv := (invariant_iff_coaction A ρ v).mp hvfix
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
      rw [hp, map_sub, map_smul, hρv, map_sub, map_smul, LinearMap.rTensor_tmul, hp_v]
      simp
    let σ := quotientCoaction A ρ p (fun w ↦ ⟨inc w, hp_inc w⟩) f hf
    have hrange : LinearMap.range l = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro a
      exact ⟨a • v, by simp [hl]⟩
    have hdim := l.finrank_range_add_finrank_ker
    rw [hrange, finrank_top, Module.finrank_self, hn] at hdim
    have hnW : Module.finrank k W = n := by change Module.finrank k (LinearMap.ker l) = n; omega
    obtain ⟨b, hb⟩ := ih W hnW σ
    have hli (a : k) (x : V) (hx : x ∈ W) (hax : a • v + x = 0) : a = 0 := by
      have hu := congrArg l hax
      simpa [hl, show l x = 0 from hx] using hu
    have hsp (x : V) : ∃ a : k, x + a • v ∈ W := by
      refine ⟨-l x, ?_⟩
      change l (x + (-l x) • v) = 0
      simp [hl]
    let B := Module.Basis.mkFinCons v b hli hsp
    have hB : (B : Fin (n + 1) → V) = Fin.cons v (inc ∘ b) :=
      Module.Basis.coe_mkFinCons v b hli hsp
    have splitTensor (t : V ⊗[k] A) :
        t = v ⊗ₜ[k] (TensorProduct.lid k A (l.rTensor A t)) +
            inc.rTensor A (p.rTensor A t) := by
      induction t using TensorProduct.inductionOn with
      | tmul x a =>
        simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, hp]
        rw [← TensorProduct.smul_tmul (l x) v a, ← TensorProduct.add_tmul, add_comm, sub_add_cancel]
      | add x y hx hy =>
        simp only [map_add, TensorProduct.tmul_add]
        rw [add_add_add_comm, ← hx, ← hy]
    refine ⟨B, ?_⟩
    intro j
    refine Fin.cases ?_ (fun j ↦ ?_) j
    · refine ⟨0, by simp, ?_⟩
      simpa [hB] using hρv
    · obtain ⟨c, hc, hσ⟩ := hb j
      let d := TensorProduct.lid k A (l.rTensor A (ρ.coaction (inc (b j))))
      refine ⟨Fin.cons d c, ?_, ?_⟩
      · intro i hi
        cases i using Fin.cases with
        | zero => exact ((Fin.succ_pos j).not_ge hi).elim
        | succ i => exact hc i (Fin.succ_le_succ_iff.mp hi)
      · have hproj : p.rTensor A (ρ.coaction (inc (b j))) = σ.coaction (b j) := rfl
        rw [hB, Fin.cons_succ, Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
        calc
          _ = v ⊗ₜ[k] d + inc.rTensor A (p.rTensor A (ρ.coaction (inc (b j)))) :=
            splitTensor _
          _ = _ := by
            rw [hproj, hσ]
            simp only [map_add, map_sum, LinearMap.rTensor_tmul]
            ac_rfl

private lemma triangularBasis_isUnitriangular {n : ℕ} (ρ : RightComodule k A V)
    (b : Module.Basis (Fin n) k V) (h : IsTriangularBasis A ρ b) :
    IsUpperUnitriangular (coefficients A (b.reindex Equiv.ulift.symm) ρ) := by
  classical
  let B : Module.Basis (Index.{u} n) k V := b.reindex Equiv.ulift.symm
  change IsUpperUnitriangular (coefficients A B ρ)
  have hB (x : Index.{u} n) : B x = b x.down := by simp [B, Module.Basis.reindex_apply]
  have happly (i j : Index.{u} n) :
      ∃ c : Fin n → A, (∀ x, j.down ≤ x → c x = 0) ∧
        coefficients A B ρ i j = (if i = j then 1 else 0) + c i.down := by
    obtain ⟨c, hc, hr⟩ := h j.down
    refine ⟨c, hc, ?_⟩
    have hcoord (x : Fin n) (a : A) :
        tensorCoordinate B i (b x ⊗ₜ[k] a) = (if ULift.up x = i then a else 0) := by
      change B.coord i (b x) • a = _
      rw [(hB (ULift.up x)).symm, Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_apply]
      split <;> simp_all
    change tensorCoordinate B i (ρ.coaction (B j)) = _
    rw [hB, hr, map_add, map_sum, hcoord]
    simp only [hcoord]
    rw [Finset.sum_eq_single i.down]
    · simp [eq_comm]
    · intro x _ hx
      exact ite_eq_right (fun hEq ↦ hx (congrArg ULift.down hEq))
    · simp
  refine ⟨fun {i j} hj ↦ ?_, fun i ↦ ?_⟩
  · change j < i at hj
    obtain ⟨c, hc, he⟩ := happly i j
    rw [he, hc i.down (le_of_lt hj), ite_eq_right (ne_of_gt hj), add_zero]
  · obtain ⟨c, hc, he⟩ := happly i i
    rw [he, hc i.down le_rfl, ite_eq_left rfl, add_zero]

theorem hasFullFlags_of_invariants (h : HasInvariantVectors A) : HasFullFlags A := by
  intro V _ _ _ _ ρ
  obtain ⟨b, hb⟩ := triangularBasis_of_invariants A h (Module.finrank k V) V rfl ρ
  exact ⟨b.reindex Equiv.ulift.symm, triangularBasis_isUnitriangular A ρ b hb⟩

theorem hasInvariantVectors_of_flags (h : HasFullFlags A) : HasInvariantVectors A := by
  intro V _ _ _ _ ρ
  obtain ⟨b, hb⟩ := h V ρ
  let j : Index.{u} (Module.finrank k V) := ⟨⟨0, Module.finrank_pos⟩⟩
  refine ⟨b j, b.ne_zero j, (invariant_iff_coaction A ρ _).mpr ?_⟩
  rw [coaction_apply_basis A b ρ, Finset.sum_eq_single j, hb.2]
  · intro i _ hi
    have hji : j < i := lt_of_le_of_ne (Nat.zero_le i.down.val) (Ne.symm hi)
    rw [hb.1 hji, TensorProduct.tmul_zero]
  · simp

end Flags


theorem fullFlagComparison : FullFlagComparison.{u} := by
  intro k _ A
  constructor
  · intro h V _ _ _ _ ρ
    obtain ⟨b, hb⟩ := triangularBasis_of_invariants A (hasInvariantVectors_of_flags A h)
      (Module.finrank k V) V rfl ρ
    refine ⟨b, fun j ↦ ?_⟩
    let f := ((b.flag j.castSucc).mkQ.rTensor A).comp (invariantDifference A ρ)
    have hf : b.flag j.succ ≤ LinearMap.ker f := by
      apply (b.flag_le_iff).2
      intro i hi
      obtain ⟨c, hc, he⟩ := hb i
      change ((b.flag j.castSucc).mkQ.rTensor A)
        (ρ.coaction (b i) - b i ⊗ₜ[k] (1 : A)) = 0
      rw [he, add_sub_cancel_left, map_sum]
      apply Finset.sum_eq_zero
      intro l _
      rw [LinearMap.rTensor_tmul]
      by_cases hl : i ≤ l
      · rw [hc l hl, TensorProduct.tmul_zero]
      · have hli : l < i := lt_of_not_ge hl
        have hji : i.val ≤ j.val := Nat.le_of_lt_succ hi
        have hlj : l.castSucc < j.castSucc := Nat.lt_of_lt_of_le hli hji
        rw [show (b.flag j.castSucc).mkQ (b l) = 0 from
          (Submodule.Quotient.mk_eq_zero _).2 (b.self_mem_flag hlj), TensorProduct.zero_tmul]
    exact fun v hv ↦ hf hv
  · intro h
    apply hasFullFlags_of_invariants
    intro V _ _ _ _ ρ
    obtain ⟨b, hb⟩ := h V ρ
    let j : Fin (Module.finrank k V) := ⟨0, Module.finrank_pos⟩
    have hmem : b j ∈ b.flag j.succ :=
      b.self_mem_flag (show j.castSucc < j.succ from Fin.castSucc_lt_succ)
    let t := invariantDifference A ρ (b j)
    have hz : t ∈ LinearMap.ker ((b.flag j.castSucc).mkQ.rTensor A) := hb j (b j) hmem
    have hj : j.castSucc = 0 := rfl
    rw [rTensor_mkQ, hj, b.flag_zero] at hz
    obtain ⟨y, hy⟩ := hz
    have hb0 : ((⊥ : Submodule k V).subtype : _ →ₗ[k] V) = 0 := by
      ext x
      exact x.property
    rw [hb0, LinearMap.rTensor_zero, LinearMap.zero_apply] at hy
    exact ⟨b j, b.ne_zero j, hy.symm⟩

private theorem unitriangular_counit (n : ℕ) (p : StrictUpper.{u} n) :
    Coalgebra.counit (R := k) (A := unitriangularHopfAlgebra k n) (MvPolynomial.X p) = 0 := by
  let P := unitriangularRepresentation k n
  have h := StandardGroups.Representation.equiv_epsilon P (AlgHom.id k k)
  rw [AlgHom.id_comp] at h
  have hh := congrArg (fun g : (unitriangularPoints k n).obj (CommAlgCat.of k k) ↦
    g.val.val p.val.1 p.val.2) h
  change StandardGroups.Representation.epsilon P (coordinateMatrix k n p.val.1 p.val.2) =
    (1 : Matrix (Index n) (Index n) k) p.val.1 p.val.2 at hh
  rw [coordinateMatrix, dite_eq_left p.property, Matrix.one_apply_ne p.property.ne] at hh
  exact hh

private lemma matrix_eq_coordinateMatrix_of_unitriangular
    {A : HopfAlgebraCategory k} {n : ℕ} {M : Matrix (Index.{u} n) (Index.{u} n) A}
    (hM : IsUpperUnitriangular M) :
    (MvPolynomial.aeval (fun p : StrictUpper n ↦ M p.val.1 p.val.2)).mapMatrix (coordinateMatrix k n) =
      M := by
  ext i j
  change MvPolynomial.aeval (fun p : StrictUpper n ↦ M p.val.1 p.val.2) (coordinateMatrix k n i j) =
    M i j
  rcases lt_trichotomy i j with h | rfl | h
  · rw [coordinateMatrix, dite_eq_left h, MvPolynomial.aeval_X]
  · simp [coordinateMatrix, hM.2]
  · simp [coordinateMatrix, not_lt_of_gt h, ne_of_gt h, hM.1 h]

private def hopfMapOfUnitriangularMatrix {A : HopfAlgebraCategory k} {n : ℕ}
    {M : Matrix (Index.{u} n) (Index.{u} n) A}
    (hM : IsUpperUnitriangular M) (h : IsCoactionMatrix A M) :
    unitriangularHopfAlgebra k n ⟶ A := by
  let B := unitriangularHopfAlgebra k n
  let f : B →ₐ[k] A := MvPolynomial.aeval (fun p : StrictUpper n ↦ M p.val.1 p.val.2)
  have hM' (i j : Index.{u} n) : f (coordinateMatrix k n i j) = M i j :=
    congrArg (fun M : Matrix (Index.{u} n) (Index.{u} n) A ↦ M i j)
      (matrix_eq_coordinateMatrix_of_unitriangular hM)
  apply CommHopfAlgCat.ofHom
  refine BialgHom.ofAlgHom f ?_ ?_
  · apply MvPolynomial.algHom_ext
    intro p
    change Coalgebra.counit (R := k) (f (MvPolynomial.X p)) =
      Coalgebra.counit (R := k) (A := B) (MvPolynomial.X p)
    rw [unitriangular_counit, show f (MvPolynomial.X p) = M p.val.1 p.val.2 from
      MvPolynomial.aeval_X _ _, h.counit, Matrix.one_apply_ne p.property.ne]
  · apply MvPolynomial.algHom_ext
    intro p
    have hp : MvPolynomial.X p = coordinateMatrix k n p.val.1 p.val.2 := by
      rw [coordinateMatrix, dite_eq_left p.property]
    change Algebra.TensorProduct.map f f
      (Coalgebra.comul (R := k) (A := B) (MvPolynomial.X p)) = Coalgebra.comul (f (MvPolynomial.X p))
    rw [hp, unitriangular_comul, hM' p.val.1 p.val.2, h.comul]
    let g := Algebra.TensorProduct.map f f
    calc
      _ = ∑ l : Index.{u} n, g ((coordinateMatrix k n p.val.1 l : B) ⊗ₜ[k]
          (coordinateMatrix k n l p.val.2 : B)) := map_sum g _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro l _
        exact (Algebra.TensorProduct.map_tmul f f
          (coordinateMatrix k n p.val.1 l : B) (coordinateMatrix k n l p.val.2 : B)).trans
            (congrArg₂ (fun a b : A ↦ a ⊗ₜ[k] b) (hM' p.val.1 l) (hM' l p.val.2))

open private surjective_of_coefficients from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.FaithfulLinearization

private theorem embeds_of_flags {G : Specs.AffineAlgebraicGroup k}
    {A : HopfAlgebraCategory k} (e : specGroup A ≅ G.val) (h : HasFullFlags A) :
    EmbedsUnitriangular G := by
  classical
  have he : IsIso e.hom.hom.hom.left := by
    change IsIso (((Grp.forget (SchemeOver k)) ⋙ Over.forget _).map e.hom)
    infer_instance
  have hft : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  have hf := locallyOfFiniteType_comp e.hom.hom.hom.left G.val.X.hom
  have heq : e.hom.hom.hom.left ≫ G.val.X.hom = (specGroup A).X.hom := Over.w e.hom.hom.hom
  let : Algebra.FiniteType k A := (hopfSpec_locallyOfFiniteType_iff k A).mp (heq ▸ hf)
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType k A).out
  let ρ : RightComodule k A A := RightComodule.regular
  obtain ⟨W₀, hsW⟩ := ρ.exists_finiteSubcomodule_containing
    ((insert (1 : A) s : Finset A) : Set A) (insert 1 s).finite_toSet
  let W := W₀.val
  let : FiniteDimensional k W := W₀.property.2
  let : Nontrivial A := (Bialgebra.algebraMap_injective (R := k) A).nontrivial
  let : Nontrivial W := ⟨⟨⟨1, hsW (Finset.mem_insert_self _ _)⟩, 0,
    fun h ↦ one_ne_zero (congrArg Subtype.val h)⟩⟩
  obtain ⟨σ, hσ⟩ := (ρ.isSubcomodule_iff_exists_coaction W).mp W₀.property.1
  obtain ⟨b, hb⟩ := h W σ
  let n := Module.finrank k W
  let q := hopfMapOfUnitriangularMatrix hb (coefficients_isCoactionMatrix A b σ)
  have hq (i j : Index.{u} n) : coefficients A b σ i j ∈ q.hom.toAlgHom.range :=
    ⟨coordinateMatrix k n i j, congrArg (fun M : Matrix (Index.{u} n) (Index.{u} n) A ↦ M i j)
      (matrix_eq_coordinateMatrix_of_unitriangular hb)⟩
  have hsurj : Function.Surjective q.hom :=
    surjective_of_coefficients A s hs W (fun _ hx ↦ hsW (Finset.mem_insert_of_mem hx)) b σ
      hσ q.hom.toAlgHom hq
  refine ⟨n, unitriangularGroup k n, ⟨unitriangularGroupPointsIso k n⟩,
    e.inv ≫ specGroupMap q, ?_⟩
  change IsClosedImmersion (e.inv.hom.hom.left ≫ (specGroupMap q).hom.hom.left)
  have : IsClosedImmersion (specGroupMap q).hom.hom.left :=
    (hopfMapClosedImmersion k q).mpr hsurj
  have : IsIso e.inv.hom.hom.left := by
    change IsIso (((Grp.forget (SchemeOver k)) ⋙ Over.forget _).map e.inv)
    infer_instance
  infer_instance

private def groupIsoOfPoints {G H : Specs.AffineAlgebraicGroup k}
    (e : (groupPointsFunctor k).obj G.val ≅ (groupPointsFunctor k).obj H.val) :
    G.val ≅ H.val := by
  let hG := groupHomComparison k G.val H.val G.property.1
  let hH := groupHomComparison k H.val G.val H.property.1
  let f := Classical.choose (hG.2 e.hom)
  let g := Classical.choose (hH.2 e.inv)
  have hf : (groupPointsFunctor k).map f = e.hom := Classical.choose_spec (hG.2 e.hom)
  have hg : (groupPointsFunctor k).map g = e.inv := Classical.choose_spec (hH.2 e.inv)
  refine ⟨f, g, ?_, ?_⟩
  · apply (groupHomComparison k G.val G.val G.property.1).1
    change (groupPointsFunctor k).map (f ≫ g) = (groupPointsFunctor k).map (𝟙 G.val)
    rw [Functor.map_comp, (groupPointsFunctor k).map_id G.val, hf, hg, e.hom_inv_id]
  · apply (groupHomComparison k H.val H.val H.property.1).1
    change (groupPointsFunctor k).map (g ≫ f) = (groupPointsFunctor k).map (𝟙 H.val)
    rw [Functor.map_comp, (groupPointsFunctor k).map_id H.val, hf, hg, e.inv_hom_id]

private theorem exists_surjective_of_embedding {G : Specs.AffineAlgebraicGroup k}
    {A : HopfAlgebraCategory k} (e : specGroup A ≅ G.val) (h : EmbedsUnitriangular G) :
    ∃ n, ∃ q : unitriangularHopfAlgebra k n ⟶ A, Function.Surjective q.hom := by
  obtain ⟨n, N, ⟨eN⟩, f, hf⟩ := h
  let i := groupIsoOfPoints (eN ≪≫ (unitriangularGroupPointsIso k n).symm)
  let a : specGroup A ⟶ specGroup (unitriangularHopfAlgebra k n) := e.hom ≫ f ≫ i.hom
  let p := (hopfSpec.fullyFaithful (R := CommRingCat.of k)).preimage a
  have hp : specGroupMap p.unop = a := (hopfSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage a
  refine ⟨n, p.unop, (hopfMapClosedImmersion k p.unop).mp ?_⟩
  rw [hp]
  change IsClosedImmersion (e.hom.hom.hom.left ≫ f.hom.hom.left ≫ i.hom.hom.hom.left)
  have : IsIso e.hom.hom.hom.left := by
    change IsIso (((Grp.forget (SchemeOver k)) ⋙ Over.forget _).map e.hom)
    infer_instance
  have : IsIso i.hom.hom.hom.left := by
    change IsIso (((Grp.forget (SchemeOver k)) ⋙ Over.forget _).map i.hom)
    infer_instance
  infer_instance

section WeightedFiltration

open scoped Pointwise

variable {A : HopfAlgebraCategory k}

private lemma tmul_mem_tensorFiltration {C : ℕ → Submodule k A} {r i j : ℕ}
    (hC : Monotone C) (hij : i + j ≤ r) {a b : A} (ha : a ∈ C i) (hb : b ∈ C j) :
    a ⊗ₜ[k] b ∈ tensorFiltration C r := by
  let m : Fin (r + 1) := ⟨i, by omega⟩
  apply (le_iSup _ m : _ ≤ tensorFiltration C r)
  exact ⟨(⟨a, ha⟩ : C i) ⊗ₜ[k] (⟨b, hC (show j ≤ r - i by omega) hb⟩ : C (r - i)), rfl⟩

private lemma tensorFiltration_mono {C : ℕ → Submodule k A} (hC : Monotone C) :
    Monotone (tensorFiltration C) := by
  intro r s hrs
  apply iSup_le
  intro i
  rw [TensorProduct.range_map_eq_span_tmul]
  apply Submodule.span_le.mpr
  rintro _ ⟨a, b, rfl⟩
  exact tmul_mem_tensorFiltration hC (by have := i.isLt; omega) a.property b.property

private lemma mul_mem_tensorFiltration {C : ℕ → Submodule k A}
    (hC : Monotone C)
    (hmul : ∀ i j, C i * C j ≤ C (i + j))
    {r s : ℕ} {x y : A ⊗[k] A}
    (hx : x ∈ tensorFiltration C r) (hy : y ∈ tensorFiltration C s) :
    x * y ∈ tensorFiltration C (r + s) := by
  apply (show tensorFiltration C r * tensorFiltration C s ≤ _ from ?_)
    (Submodule.mul_mem_mul hx hy)
  unfold tensorFiltration
  rw [Submodule.iSup_mul]
  apply iSup_le
  intro i
  rw [Submodule.mul_iSup]
  apply iSup_le
  intro j
  rw [TensorProduct.range_map_eq_span_tmul, TensorProduct.range_map_eq_span_tmul,
    Submodule.span_mul_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨_, ⟨a, b, rfl⟩, _, ⟨c, d, rfl⟩, rfl⟩
  change ((a.val ⊗ₜ[k] b.val) * (c.val ⊗ₜ[k] d.val)) ∈ tensorFiltration C (r + s)
  rw [Algebra.TensorProduct.tmul_mul_tmul]
  exact tmul_mem_tensorFiltration hC
    (by have := i.isLt; have := j.isLt; omega)
    (hmul _ _ (Submodule.mul_mem_mul a.property c.property))
    (hmul _ _ (Submodule.mul_mem_mul b.property d.property))

private def weight {n : ℕ} (p : StrictUpper.{u} n) : ℕ :=
  p.val.2.down.val - p.val.1.down.val

private def wordWeight {n : ℕ} (w : List (StrictUpper.{u} n)) : ℕ :=
  (w.map weight).sum

private def wordValue {n : ℕ} (x : StrictUpper.{u} n → A) (w : List (StrictUpper.{u} n)) : A :=
  (w.map x).prod

private def weightedFiltration {n : ℕ} (x : StrictUpper.{u} n → A) (r : ℕ) : Submodule k A :=
  Submodule.span k {a | ∃ w, wordWeight w ≤ r ∧ wordValue x w = a}

private lemma weightedFiltration_mono {n : ℕ} (x : StrictUpper.{u} n → A) :
    Monotone (weightedFiltration x) := by
  intro r s hrs
  apply Submodule.span_mono
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w, hw.trans hrs, rfl⟩

private lemma weightedFiltration_one {n : ℕ} (x : StrictUpper.{u} n → A) :
    (1 : A) ∈ weightedFiltration x 0 :=
  Submodule.subset_span ⟨[], le_rfl, rfl⟩

private lemma weightedFiltration_zero {n : ℕ} (x : StrictUpper.{u} n → A) :
    weightedFiltration x 0 = Submodule.span k {1} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    cases w with
    | nil => exact Submodule.mem_span_singleton_self _
    | cons p w =>
      have hp : 0 < weight p := Nat.sub_pos_of_lt p.property
      simp only [wordWeight, List.map_cons, List.sum_cons] at hw
      omega
  · rw [Submodule.span_singleton_le_iff_mem]
    exact weightedFiltration_one x

private lemma weightedFiltration_mul {n : ℕ} (x : StrictUpper.{u} n → A) (r s : ℕ) :
    weightedFiltration x r * weightedFiltration x s ≤ weightedFiltration x (r + s) := by
  unfold weightedFiltration
  rw [Submodule.span_mul_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨_, ⟨l, hl, rfl⟩, _, ⟨m, hm, rfl⟩, rfl⟩
  apply Submodule.subset_span
  exact ⟨l ++ m, by simpa only [wordWeight, List.map_append, List.sum_append] using Nat.add_le_add hl hm,
    by simp only [wordValue, List.map_append, List.prod_append]⟩

private lemma weightedFiltration_var {n : ℕ} (x : StrictUpper.{u} n → A) (p : StrictUpper.{u} n) :
    x p ∈ weightedFiltration x (weight p) :=
  Submodule.subset_span ⟨[p], by simp [wordWeight], by simp [wordValue]⟩

private theorem filtration_of_surjective {n : ℕ} (q : unitriangularHopfAlgebra k n ⟶ A)
    (hq : Function.Surjective q.hom) : HasCoalgebraFiltration A := by
  let f : Coordinates k n →ₐ[k] A := q.hom.toAlgHom
  let x : StrictUpper.{u} n → A := fun p ↦ f (MvPolynomial.X p)
  let C := weightedFiltration x
  let hC := weightedFiltration_mono x
  let hmul := weightedFiltration_mul x
  have h1 := weightedFiltration_one x
  have hx := weightedFiltration_var x
  refine ⟨C, hC, ?_, weightedFiltration_zero x, ?_⟩
  · intro a
    obtain ⟨p, rfl⟩ := hq a
    change ∃ r, f (p : Coordinates k n) ∈ C r
    induction p using MvPolynomial.induction_on with
    | C d =>
      refine ⟨0, ?_⟩
      rw [← MvPolynomial.algebraMap_eq, f.commutes]
      simpa only [Algebra.smul_def, mul_one] using (C 0).smul_mem d h1
    | add a b ha hb =>
      obtain ⟨r, hr⟩ := ha
      obtain ⟨s, hs⟩ := hb
      refine ⟨max r s, ?_⟩
      rw [map_add]
      exact (C _).add_mem (hC (le_max_left _ _) hr) (hC (le_max_right _ _) hs)
    | mul_X a p ha =>
      obtain ⟨r, hr⟩ := ha
      exact ⟨r + weight p, by rw [map_mul]; exact hmul _ _ (Submodule.mul_mem_mul hr (hx p))⟩
  · let M : Matrix (Index.{u} n) (Index.{u} n) A :=
      fun i j ↦ f (coordinateMatrix k n i j)
    have hM : IsUpperUnitriangular M :=
      (coordinateMatrix_isUnitriangular (k := k) n).imp (fun h ↦ h.map f)
        (fun h i ↦ by change f _ = 1; rw [h i, map_one])
    have hm (i j : Index.{u} n) (hij : i < j) :
        M i j = x ⟨(i, j), hij⟩ := by
      change f (coordinateMatrix k n i j) = _
      rw [coordinateMatrix, dite_eq_left hij]
    have hΔM (i j : Index.{u} n) :
        Coalgebra.comul (R := k) (M i j) = ∑ l, M i l ⊗ₜ[k] M l j := by
      change Coalgebra.comul (R := k) (q.hom (coordinateMatrix k n i j)) = _
      let B := unitriangularHopfAlgebra k n
      let g : B ⊗[k] B →ₗ[k] A ⊗[k] A := TensorProduct.map q.hom.toLinearMap q.hom.toLinearMap
      calc
        _ = g (Coalgebra.comul (R := k) (A := B) (coordinateMatrix k n i j)) :=
          (CoalgHomClass.map_comp_comul_apply (R := k) (A := ↑B) (B := ↑A) q.hom (coordinateMatrix k n i j : B)).symm
        _ = g (∑ l : Index.{u} n,
              (coordinateMatrix k n i l : B) ⊗ₜ[k] (coordinateMatrix k n l j : B)) :=
          congrArg g (unitriangular_comul (k := k) n i j)
        _ = ∑ l : Index.{u} n, g ((coordinateMatrix k n i l : B) ⊗ₜ[k]
              (coordinateMatrix k n l j : B)) := map_sum g _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro l _
          exact TensorProduct.map_tmul q.hom.toLinearMap q.hom.toLinearMap
            (coordinateMatrix k n i l : B) (coordinateMatrix k n l j : B)
    have hΔx (p : StrictUpper.{u} n) :
        Coalgebra.comul (R := k) (x p) ∈ tensorFiltration C (weight p) := by
      obtain ⟨⟨i, j⟩, hij⟩ := p
      rw [← hm i j hij, hΔM]
      apply (tensorFiltration C _).sum_mem
      intro l _
      by_cases hil : i ≤ l
      · by_cases hlj : l ≤ j
        · have hmem (a b : Index.{u} n) (hab : a ≤ b) :
              M a b ∈ C (b.down.val - a.down.val) := by
            rcases hab.eq_or_lt with rfl | hab
            · simpa only [hM.2, Nat.sub_self] using h1
            · rw [hm a b hab]
              exact hx ⟨(a, b), hab⟩
          have hil' : i.down.val ≤ l.down.val := hil
          have hlj' : l.down.val ≤ j.down.val := hlj
          exact tmul_mem_tensorFiltration hC
            (show (l.down.val - i.down.val) + (j.down.val - l.down.val) ≤ j.down.val - i.down.val by omega)
            (hmem i l hil) (hmem l j hlj)
        · rw [hM.1 (lt_of_not_ge hlj), TensorProduct.tmul_zero]
          exact (tensorFiltration C _).zero_mem
      · rw [hM.1 (lt_of_not_ge hil), TensorProduct.zero_tmul]
        exact (tensorFiltration C _).zero_mem
    have hΔword (w : List (StrictUpper.{u} n)) :
        Coalgebra.comul (R := k) (wordValue x w) ∈ tensorFiltration C (wordWeight w) := by
      induction w with
      | nil =>
        change Coalgebra.comul (R := k) (1 : A) ∈ tensorFiltration C 0
        rw [Bialgebra.comul_one, Algebra.TensorProduct.one_def]
        exact tmul_mem_tensorFiltration hC (Nat.zero_le 0) h1 h1
      | cons p w ih =>
        change Coalgebra.comul (R := k) (x p * wordValue x w) ∈
          tensorFiltration C (weight p + wordWeight w)
        rw [Bialgebra.comul_mul]
        exact mul_mem_tensorFiltration hC hmul (hΔx p) ih
    intro r a ha
    change a ∈ weightedFiltration x r at ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨w, hw, rfl⟩ := ha
      exact tensorFiltration_mono hC hw (hΔword w)
    | zero => rw [map_zero]; exact (tensorFiltration C r).zero_mem
    | add a b _ _ ha hb => rw [map_add]; exact (tensorFiltration C r).add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact (tensorFiltration C r).smul_mem c ha

end WeightedFiltration

theorem unipotenceCriteria : UnipotenceCriteria.{u} := by
  intro k _ G A e
  have hEF : EmbedsUnitriangular G → HasCoalgebraFiltration A := by
    intro h
    obtain ⟨n, q, hq⟩ := exists_surjective_of_embedding e h
    exact filtration_of_surjective q hq
  have hIF := hasFullFlags_of_invariants A
  have hFI := hasInvariantVectors_of_flags A
  have hFE := embeds_of_flags e
  have hCI := hasInvariantVectors_of_filtration (A := A)
  have hFlag := fullFlagComparison A
  refine ⟨⟨?_, fun h ↦ ⟨A, ⟨e⟩, h⟩⟩, (Iff.intro hIF hFI).trans hFlag,
    hFlag.symm.trans ⟨hFE, fun h ↦ hIF (hCI (hEF h))⟩,
    ⟨hEF, fun h ↦ hFE (hIF (hCI h))⟩⟩
  rintro ⟨B, ⟨i⟩, h⟩
  exact hCI (hEF (embeds_of_flags i (hasFullFlags_of_invariants B h)))

end Unipotent
end LinearAlgebraicGroups
