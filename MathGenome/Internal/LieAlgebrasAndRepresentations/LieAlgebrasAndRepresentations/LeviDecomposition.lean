import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.LeviDecomposition
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SecondWhitehead
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SolvableRadical
import Mathlib.LinearAlgebra.Projection

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace LieAlgebrasAndRepresentations.LeviDecomposition

variable {k : Type u} [Field k] [CharZero k]
variable {H : Type v} [LieRing H] [LieAlgebra k H] [FiniteDimensional k H]
variable {L : Type v} [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]

/-- Whitehead applies to the actual adjoint action on an abelian kernel. -/
theorem section_of_abelian_kernel (f : L →ₗ⁅k⁆ H) (hf : Function.Surjective f)
    (hH : IsSemisimple k H) [IsLieAbelian f.ker] :
    ∃ s : H →ₗ⁅k⁆ L, ∀ x, f (s x) = x := by
  let E := (LieAlgebra.isExtension_of_surjective f hf).extension
  letI := E.ringModuleOf
  letI := E.lieModuleOf
  let F : AbelianExtensions.Extension.{u,v,v,v} k H f.ker :=
    { carrier := L
      instLieRing := inferInstance
      instLieAlgebra := inferInstance
      incl := f.ker.incl.toLinearMap
      proj := f
      injective := Subtype.val_injective
      surjective := hf
      exact := by
        change LinearMap.range f.ker.toSubmodule.subtype = f.ker.toSubmodule
        exact Submodule.range_subtype _
      abelian := by
        intro x y
        exact congrArg (fun a : f.ker => (a : L)) (trivial_lie_zero f.ker f.ker x y)
      action := by
        intro x y
        have h := E.ringModuleOf_bracket_proj y x
        have hh := congrArg (fun z : f.ker => (E.toKer z).val) h
        rw [LieEquiv.apply_symm_apply] at hh
        exact hh.symm }
  exact SecondWhitehead.extensionSplits k H f.ker hH F

/-- A finite-dimensional extension of a semisimple algebra by a solvable
kernel splits. Induction removes a nonzero abelian ideal of that kernel. -/
theorem section_of_solvable_kernel_aux (hH : IsSemisimple k H) (n : ℕ) :
    ∀ (E : Type v) [LieRing E] [LieAlgebra k E] [FiniteDimensional k E],
      Module.finrank k E = n → ∀ f : E →ₗ⁅k⁆ H,
      Function.Surjective f → LieAlgebra.IsSolvable f.ker →
      ∃ s : H →ₗ⁅k⁆ E, ∀ x, f (s x) = x := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E _ _ _ hn f hf hker
    letI := hker
    by_cases hz : f.ker = ⊥
    · haveI : IsLieAbelian f.ker := by rw [hz]; infer_instance
      exact section_of_abelian_kernel f hf hH
    let A := LieAlgebra.derivedAbelianOfIdeal f.ker
    have hA : A ≤ f.ker := by
      dsimp [A, LieAlgebra.derivedAbelianOfIdeal]
      split
      · exact bot_le
      · exact LieAlgebra.derivedSeriesOfIdeal_le_self _ _
    have hA0 : A ≠ ⊥ :=
      fun h => hz ((LieAlgebra.abelian_of_solvable_ideal_eq_bot_iff f.ker).mp h)
    haveI : IsLieAbelian A := LieAlgebra.abelian_derivedAbelianOfIdeal f.ker
    haveI : Nontrivial A := (LieSubmodule.nontrivial_iff_ne_bot k E E).mpr hA0
    obtain ⟨q, hqval, hq, hqker⟩ := quotient_projection A
    let F : (E ⧸ A) →ₗ[k] H := A.toSubmodule.liftQ f.toLinearMap hA
    have hF (x : E) : F (q x) = f x := by rw [hqval]; rfl
    let g : (E ⧸ A) →ₗ⁅k⁆ H :=
      { F with
        map_lie' := by
          intro x y
          obtain ⟨x, rfl⟩ := hq x
          obtain ⟨y, rfl⟩ := hq y
          change F ⁅q x, q y⁆ = ⁅F (q x), F (q y)⁆
          rw [← q.map_lie, hF, hF, hF, f.map_lie] }
    have hfac (x : E) : g (q x) = f x := hF x
    have hg : Function.Surjective g := by
      intro y
      obtain ⟨x, rfl⟩ := hf y
      exact ⟨q x, hfac x⟩
    let T : f.ker →ₗ⁅k⁆ g.ker :=
      { (q.toLinearMap.comp f.ker.incl.toLinearMap).codRestrict g.ker.toSubmodule
          (fun x => by change g (q x) = 0; rw [hfac]; exact x.property) with
        map_lie' := by intro x y; apply Subtype.ext; exact q.map_lie x y }
    have hT : Function.Surjective T := by
      intro y
      obtain ⟨x, hx⟩ := hq y.val
      have hx0 : f x = 0 := by rw [← hfac, hx]; exact y.property
      exact ⟨⟨x, hx0⟩, Subtype.ext hx⟩
    have hgker : LieAlgebra.IsSolvable g.ker := hT.lieAlgebra_isSolvable
    have hdim : Module.finrank k (E ⧸ A) < n := by
      have he : Module.finrank k (E ⧸ A) + Module.finrank k A =
          Module.finrank k E := by
        simpa only using! (Submodule.finrank_quotient_add_finrank A.toSubmodule)
      have hp : 0 < Module.finrank k A := Module.finrank_pos
      rw [hn] at he
      omega
    obtain ⟨s, hs⟩ := ih _ hdim (E ⧸ A) rfl g hg hgker
    let P := s.range.comap q
    let p : P →ₗ⁅k⁆ H := f.comp P.incl
    have hp : Function.Surjective p := by
      intro x
      obtain ⟨y, hy⟩ := hq (s x)
      refine ⟨⟨y, ?_⟩, ?_⟩
      · change q y ∈ s.range
        rw [hy]
        exact s.mem_range_self x
      · change f y = x
        rw [← hfac, hy, hs]
    have hpa (x : p.ker) : (x.val.val : E) ∈ A := by
      have hx : q x.val.val ∈ s.range := x.val.property
      obtain ⟨y, hy⟩ := (s.mem_range _).mp hx
      have hy0 : y = 0 := by
        rw [← hs y, hy, hfac]
        exact x.property
      have hq0 : q x.val.val = 0 := by rw [← hy, hy0, map_zero]
      rw [← hqker]
      exact hq0
    haveI : IsLieAbelian p.ker := by
      refine ⟨?_⟩
      intro x y
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun a : A => (a : E))
        (trivial_lie_zero A A ⟨x.val.val, hpa x⟩ ⟨y.val.val, hpa y⟩)
    obtain ⟨t, ht⟩ := section_of_abelian_kernel p hp hH
    exact ⟨P.incl.comp t, ht⟩

/-- The solvable-kernel splitting theorem, without a dimension parameter. -/
theorem section_of_solvable_kernel (f : L →ₗ⁅k⁆ H) (hf : Function.Surjective f)
    (hH : IsSemisimple k H) (hker : LieAlgebra.IsSolvable f.ker) :
    ∃ s : H →ₗ⁅k⁆ L, ∀ x, f (s x) = x :=
  section_of_solvable_kernel_aux hH (Module.finrank k L) L rfl f hf hker

/-- Semisimplicity in the radical sense is invariant under a Lie equivalence. -/
theorem semisimple_of_equiv (e : L ≃ₗ⁅k⁆ H) (hH : IsSemisimple k H) :
    IsSemisimple k L := by
  apply (semisimple_iff_no_solvable_ideals k L).mpr
  intro I hI
  letI := hI
  let J := I.map e.toLieHom
  let t : I →ₗ⁅k⁆ J :=
    { (e.toLinearMap.comp I.incl.toLinearMap).codRestrict J.toSubmodule
        (fun x => LieIdeal.mem_map x.property) with
      map_lie' := by intro x y; apply Subtype.ext; exact e.map_lie x y }
  have ht : Function.Surjective t := by
    intro y
    obtain ⟨x, hx⟩ := LieIdeal.mem_map_of_surjective e.surjective y.property
    exact ⟨x, Subtype.ext hx⟩
  have hJ : LieAlgebra.IsSolvable J := ht.lieAlgebra_isSolvable
  have hJ0 : J = ⊥ := (semisimple_iff_no_solvable_ideals k H).mp hH J hJ
  exact LieIdeal.bot_of_map_eq_bot e.injective hJ0

/-- Levi's decomposition: the subalgebra is the image of a section of the
canonical radical quotient, and its underlying vector space complements the
radical. The displayed equivalence is that quotient map restricted to it. -/
theorem leviDecomposition :
    Specs.LieAlgebrasAndRepresentations.LeviDecomposition.leviDecompositionType.{u,v} := by
  intro k L _ _ _ _ _
  obtain ⟨q, hqval, hq, hqker⟩ := quotient_projection (radical k L)
  have hker : LieAlgebra.IsSolvable q.ker := by
    rw [hqker]
    exact radical_solvable k L
  obtain ⟨s, hs⟩ := section_of_solvable_kernel q hq (quotient_semisimple k L) hker
  have hsinj : Function.Injective s := by
    intro x y h
    rw [← hs x, ← hs y, h]
  let e := (s.equivRangeOfInjective hsinj).symm
  have he (x : s.range) : e x = q x.val := by
    obtain ⟨y, hy⟩ := (s.mem_range x.val).mp x.property
    have hx : x = s.equivRangeOfInjective hsinj y := Subtype.ext hy.symm
    rw [hx, LieEquiv.symm_apply_apply]
    exact (hs y).symm
  refine ⟨s.range, semisimple_of_equiv e (quotient_semisimple k L), ?_, e, ?_⟩
  · let p : L →ₗ[k] s.range := s.rangeRestrict.toLinearMap.comp q.toLinearMap
    have hp (x : s.range) : p x.val = x := by
      apply Subtype.ext
      obtain ⟨y, hy⟩ := (s.mem_range x.val).mp x.property
      change s (q x.val) = x.val
      rw [← hy, hs]
    have hc := LinearMap.isCompl_of_proj hp
    have hk : LinearMap.ker p = (radical k L).toSubmodule := by
      ext x
      change s.rangeRestrict (q x) = 0 ↔ x ∈ radical k L
      rw [Subtype.ext_iff]
      change s (q x) = 0 ↔ x ∈ radical k L
      rw [← map_zero s, hsinj.eq_iff]
      change x ∈ q.ker ↔ _
      rw [hqker]
    rw [hk] at hc
    exact hc
  · intro x
    exact (he x).trans (hqval x.val)

end LieAlgebrasAndRepresentations.LeviDecomposition
