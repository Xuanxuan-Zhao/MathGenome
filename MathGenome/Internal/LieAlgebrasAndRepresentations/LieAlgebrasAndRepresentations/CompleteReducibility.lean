import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.CompleteReducibility
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.FirstWhitehead
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.TensorDualHom
import Mathlib.Algebra.Lie.DirectSum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Order.CompactlyGenerated.Basic

open scoped Classical DirectSum
noncomputable section
set_option maxRecDepth 4096
universe u v w
namespace LieAlgebrasAndRepresentations.CompleteReducibility

variable (k : Type u) (g : Type v) (V : Type w)
  [Field k] [CharZero k] [LieRing g] [LieAlgebra k g] [FiniteDimensional k g]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [LieRingModule g V] [LieModule k g V]

/-- Correct a vector-space section of the quotient by its inner equivariance defect.
The coefficient module is the canonical Hom module Hom(V/W,W). -/
lemma quotient_section
    (hg : Specs.LieAlgebrasAndRepresentations.SolvableRadical.IsSemisimple_value k g)
    (W : LieSubmodule k g V) :
    ∃ s : (V ⧸ W) →ₗ⁅k,g⁆ V,
      (LieSubmodule.Quotient.mk' W).comp s = LieModuleHom.id := by
  let p := LieSubmodule.Quotient.mk' W
  obtain ⟨s, hs⟩ := p.toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (LieSubmodule.Quotient.surjective_mk' W))
  have hs' (q : V ⧸ W) : p (s q) = q := LinearMap.congr_fun hs q
  have hdef (x : g) (q : V ⧸ W) : ⁅x,s⁆ q ∈ W := by
    apply (LieSubmodule.Quotient.mk_eq_zero W).mp
    change p (⁅x,s q⁆ - s ⁅x,q⁆) = 0
    rw [map_sub, p.map_lie, hs', hs', sub_self]
  let a : g →ₗ[k] ((V ⧸ W) →ₗ[k] W) :=
    { toFun := fun x => (⁅x,s⁆).codRestrict W.toSubmodule (hdef x)
      map_add' := by intro x y; ext q; simp [add_lie]
      map_smul' := by intro c x; ext q; simp [smul_lie] }
  have ha : ∀ x y, a ⁅x,y⁆ = ⁅x,a y⁆ - ⁅y,a x⁆ := by
    intro x y
    ext q
    have h := congrArg (fun f : (V ⧸ W) →ₗ[k] V => f q) (lie_lie x y s)
    change ⁅⁅x,y⁆,s⁆ q =
      (⁅x,(a y) q⁆ : W).val - ((a y) ⁅x,q⁆).val -
        ((⁅y,(a x) q⁆ : W).val - ((a x) ⁅y,q⁆).val)
    exact h
  obtain ⟨t, ht⟩ := FirstWhitehead.cocycle_inner k g ((V ⧸ W) →ₗ[k] W) hg a ha
  let r : (V ⧸ W) →ₗ[k] V := s - W.toSubmodule.subtype.comp t
  have hr (x : g) (q : V ⧸ W) : r ⁅x,q⁆ = ⁅x,r q⁆ := by
    have h := congrArg (fun f : (V ⧸ W) →ₗ[k] W => (f q).val) (ht x)
    change ⁅x,s q⁆ - s ⁅x,q⁆ = ⁅x,(t q).val⁆ - (t ⁅x,q⁆).val at h
    change s ⁅x,q⁆ - (t ⁅x,q⁆).val = ⁅x,s q - (t q).val⁆
    rw [lie_sub]
    rw [sub_eq_sub_iff_add_eq_add] at h ⊢
    exact (add_comm _ _).trans h.symm
  refine ⟨{ r with map_lie' := fun {x q} => hr x q }, ?_⟩
  ext q
  change p (s q - (t q).val) = q
  rw [map_sub, hs']
  have hz : p (t q).val = 0 := (LieSubmodule.Quotient.mk_eq_zero W).mpr (t q).property
  rw [hz, sub_zero]

/-- Weyl complete reducibility, with no algebraic-closure assumption. -/
theorem invariant_complement :
    Specs.LieAlgebrasAndRepresentations.CompleteReducibility.invariant_complement_type.{u,v,w} := by
  intro k g V _ _ _ _ _ _ _ _ _ _ hg W
  obtain ⟨s, hs⟩ := quotient_section k g V hg W
  let p := LieSubmodule.Quotient.mk' W
  have hs' (q : V ⧸ W) : p (s q) = q :=
    congrArg (fun f : (V ⧸ W) →ₗ⁅k,g⁆ (V ⧸ W) => f q) hs
  refine ⟨s.range, ?_⟩
  rw [isCompl_iff, disjoint_iff, codisjoint_iff]
  constructor
  · apply (LieSubmodule.eq_bot_iff _).mpr
    intro v hv
    obtain ⟨q, hq⟩ := hv.2
    have hz : p v = 0 := (LieSubmodule.Quotient.mk_eq_zero W).mpr hv.1
    rw [← hq, hs'] at hz
    rw [← hq, hz, map_zero]
  · apply top_unique
    intro v _
    apply (LieSubmodule.mem_sup _ _ _).mpr
    refine ⟨v - s (p v), ?_, s (p v), ⟨p v, rfl⟩, sub_add_cancel _ _⟩
    apply (LieSubmodule.Quotient.mk_eq_zero W).mp
    change p (v - s (p v)) = 0
    rw [map_sub, hs', sub_self]

omit [CharZero k] [LieAlgebra k g] [FiniteDimensional k g]
  [FiniteDimensional k V] [LieModule k g V] in
/-- An atom of the invariant-subspace lattice is a simple Lie module. -/
lemma irreducible_of_atom (W : LieSubmodule k g V) (hW : IsAtom W) :
    LieModule.IsIrreducible k g W := by
  have : Nontrivial W := (LieSubmodule.nontrivial_iff_ne_bot k g V).mpr hW.ne_bot
  apply LieModule.IsIrreducible.mk
  intro N hN
  by_contra hn
  have hlt : N.map W.incl < W :=
    LieSubmodule.map_incl_lt_iff_lt_top.mpr (lt_top_iff_ne_top.mpr hn)
  have hz : N.map W.incl = ⊥ := hW.2 _ hlt
  apply hN
  apply LieSubmodule.map_injective_of_injective (f := W.incl) Subtype.coe_injective
  rw [hz, LieSubmodule.map_bot]

/-- A complemented finite-length submodule lattice has an independent spanning
family of atoms; finite dimension makes that family finite. -/
theorem finite_simple_decomposition :
    Specs.LieAlgebrasAndRepresentations.CompleteReducibility.finite_simple_decomposition_type.{u,v,w} := by
  intro k g V _ _ _ _ _ _ _ _ _ _ hg
  let : ComplementedLattice (LieSubmodule k g V) :=
    ⟨invariant_complement k g V hg⟩
  let : IsCompactlyGenerated (LieSubmodule k g V) := IsCompactlyGenerated.of_wellFoundedGT
  obtain ⟨S, hind, hsup, hatom⟩ := exists_sSupIndep_of_sSup_atoms_eq_top
    (sSup_atoms_eq_top (α := LieSubmodule k g V))
  refine ⟨S, WellFoundedGT.finite_of_sSupIndep hind, ?_, ?_⟩
  · exact fun W hW => irreducible_of_atom k g V W (hatom hW)
  · apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · exact LieSubmodule.iSupIndep_toSubmodule.mpr ((sSupIndep_iff _).mp hind)
    · rw [LieSubmodule.iSup_toSubmodule_eq_top]
      simpa only [sSup_eq_iSup, iSup_subtype] using hsup

/-- The canonical sum of the inclusions is an equivalence of Lie modules.
The family of simple summands is empty when the ambient module is zero. -/
theorem finite_simple_decomposition_equivariant
    (hg : Specs.LieAlgebrasAndRepresentations.SolvableRadical.IsSemisimple_value k g) :
    ∃ S : Set (LieSubmodule k g V), S.Finite ∧
      (∀ W ∈ S, LieModule.IsIrreducible k g W) ∧
      (Subsingleton V → S = ∅) ∧
      ∃ e : (⨁ W : S, W.val) ≃ₗ⁅k,g⁆ V,
        ∀ (W : S) (m : W.val), e (DirectSum.of (fun W : S => W.val) W m) = m.val := by
  obtain ⟨S, hfinite, hsimple, hinternal⟩ := finite_simple_decomposition k g V hg
  refine ⟨S, hfinite, hsimple, ?_, ?_⟩
  · intro hV
    letI : Subsingleton V := hV
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro W hW
    exact (not_nontrivial_iff_subsingleton.mpr inferInstance) (hsimple W hW).toNontrivial
  · let sum : (⨁ W : S, W.val) →ₗ[k] V :=
      DirectSum.coeLinearMap (fun W : S => W.val.toSubmodule)
    have hsum (W : S) (m : W.val) :
        sum (DirectSum.lieModuleOf k S g (fun W : S => W.val) W m) = m.val :=
      DirectSum.coeLinearMap_lof (fun W : S => W.val.toSubmodule) W m
    have hLie (x : g) (m : ⨁ W : S, W.val) : sum ⁅x,m⁆ = ⁅x,sum m⁆ := by
      induction m using DirectSum.induction_on with
      | zero => simp
      | of W m =>
        let incl := DirectSum.lieModuleOf k S g (fun W : S => W.val) W
        change sum ⁅x, incl m⁆ = ⁅x, sum (incl m)⁆
        rw [← incl.map_lie]
        exact (hsum W ⁅x,m⁆).trans (congrArg (fun v : V => ⁅x,v⁆) (hsum W m)).symm
      | add m n hm hn => rw [lie_add, map_add, hm, hn, map_add, lie_add]
    let equiv := LinearEquiv.ofBijective sum hinternal
    exact ⟨{ equiv with map_lie' := fun {x m} => hLie x m }, hsum⟩

end LieAlgebrasAndRepresentations.CompleteReducibility
