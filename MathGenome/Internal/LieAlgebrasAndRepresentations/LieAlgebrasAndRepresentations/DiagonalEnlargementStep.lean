import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.JordanDerivations
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Pi
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.DiagonalEnlargementStep
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.Nilradical
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CompleteReducibility
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

noncomputable section
universe u v w z uS uT uB
namespace LieAlgebrasAndRepresentations.DiagonalEnlargementStep

open Module
open scoped DirectSum

/-- B08 applied with rad(A)=A. -/
theorem derivation_image :
    Specs.LieAlgebrasAndRepresentations.DiagonalEnlargementStep.derivation_image_type := by
  intro k A _ _ _ _ _ _ D x
  apply derivation_radical_mem_nilradical k A D x
  change x ∈ LieAlgebra.radical k A
  rw [LieAlgebra.radical_eq_top_of_isSolvable]
  trivial

/-- Choose the functional on the quotient, so annihilation of the nilradical
is part of the construction rather than an additional assumption. -/
theorem normalized_character :
    Specs.LieAlgebrasAndRepresentations.DiagonalEnlargementStep.normalized_character_type := by
  intro k A _ _ _ _ _ _ d hd
  let N := (nilradical k A).toSubmodule
  have hd' : N.mkQ d ≠ 0 := by
    intro h
    exact hd ((Submodule.Quotient.mk_eq_zero N).mp h)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one k hd'
  let χ : A →ₗ[k] k := f.comp N.mkQ
  have hN : ∀ x ∈ nilradical k A, χ x = 0 := by
    intro x hx
    change f (N.mkQ x) = 0
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).mpr hx, map_zero]
  refine ⟨χ, hf, hN, ?_, ?_⟩
  · intro x y
    apply hN
    have h := derivation_image k A (LieDerivation.ad k A x) y
    have he : (LieDerivation.ad k A x) y = ⁅x, y⁆ := by
      change -⁅y, x⁆ = ⁅x, y⁆
      exact lie_skew x y
    rw [he] at h
    exact h
  · intro D x
    exact hN (D x) (derivation_image k A D x)

/-- The nilradical criterion absorbs each generator; closure under linear
combinations is then inherited from the nilradical itself. -/
theorem nilpotent_span :
    Specs.LieAlgebrasAndRepresentations.DiagonalEnlargementStep.nilpotent_span_type := by
  intro k A _ _ _ _ _ _ P y M hP hy hM
  have hmem (x : A) (hx : IsNilpotent (LieAlgebra.ad k A x)) :
      x ∈ nilradical k A := by
    apply (mem_nilradical_iff k A x).mpr
    refine ⟨?_, hx⟩
    change x ∈ LieAlgebra.radical k A
    rw [LieAlgebra.radical_eq_top_of_isSolvable]
    trivial
  have hle : M.toSubmodule ≤ (nilradical k A).toSubmodule := by
    apply hM.trans
    apply sup_le
    · exact fun x hx => hmem x (hP x hx)
    · apply Submodule.span_le.mpr
      intro x hx
      have hxy := Set.mem_singleton_iff.mp hx
      exact hxy.symm ▸ hmem _ hy
  let f : M →ₗ⁅k⁆ nilradical k A :=
    { M.toSubmodule.subtype.codRestrict (nilradical k A).toSubmodule
        (fun x => hle x.property) with
      map_lie' := by intro x y; rfl }
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : nilradical k A => (z : A)) h
  letI := nilradical_nilpotent k A
  exact hf.lieAlgebra_isNilpotent

theorem nilpotent_ideal_plus_line :
    Specs.LieAlgebrasAndRepresentations.DiagonalEnlargementStep.nilpotent_ideal_plus_line_type := by
  intro k A _ _ _ _ _ _ I y M hI hy hM
  letI := hI
  apply nilpotent_span k A I.toSubmodule y M
  · intro x hx
    exact isNilpotent_ad_of_mem_nilpotent_ideal I ⟨x, hx⟩
  · exact hy
  · exact hM.le

/-- Once the new nilradical contains one more independent direction, the
quotient dimension decreases. No separate positivity premise is needed. -/
theorem quotient_dimension_drop :
    Specs.LieAlgebrasAndRepresentations.DiagonalEnlargementStep.quotient_dimension_drop_type := by
  intro k _ V W _ _ _ _ _ _ P Q R y hVW hPQ hy hle
  have hsup := Submodule.finrank_sup_span_singleton hy
  have hmono := Submodule.finrank_mono hle
  have hR := R.finrank_quotient_add_finrank
  have hP := P.finrank_quotient_add_finrank
  omega

/-- This gives the source formula ker χ + k(d-α), its complement, and its
dimension before any Lie brackets are considered. -/
theorem graph_complement :
    Specs.LieAlgebrasAndRepresentations.DiagonalEnlargementStep.graph_complement_type := by
  intro k _ V H _ _ _ _ _ χ α d hd
  let f := Specs.LieAlgebrasAndRepresentations.DiagonalEnlargementStep.tiltedGraphMap χ α
  have hf (x : V) : f x = (x, -(χ x • α)) := rfl
  have hinj : Function.Injective f := by
    intro x y h
    exact congrArg Prod.fst h
  refine ⟨?_, ?_, (LinearEquiv.ofInjective f hinj).finrank_eq.symm⟩
  · apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      apply Submodule.mem_sup.mpr
      refine ⟨(x - χ x • d, 0), ?_, χ x • (d, -α), ?_, ?_⟩
      · exact ⟨x - χ x • d, by simp [LinearMap.mem_ker, hd], rfl⟩
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
      · rw [hf]
        ext <;> simp
    · apply sup_le
      · rintro _ ⟨x, hx, rfl⟩
        refine ⟨x, ?_⟩
        have hx' : χ x = 0 := hx
        change f x = (x, 0)
        simp only [hf, hx', zero_smul, neg_zero]
      · apply Submodule.span_le.mpr
        intro z hz
        have hz' : z = (d, -α) := Set.mem_singleton_iff.mp hz
        rw [hz']
        refine ⟨d, ?_⟩
        change f d = (d, -α)
        simp only [hf, hd, one_smul]
  · constructor
    · apply Submodule.disjoint_def.mpr
      intro z hz hz'
      obtain ⟨x, rfl⟩ := hz
      obtain ⟨h, hh⟩ := hz'
      have hx : x = 0 := (congrArg Prod.fst hh).symm
      rw [hx, map_zero]
    · apply codisjoint_iff.mpr
      apply top_unique
      intro z _
      apply Submodule.mem_sup.mpr
      refine ⟨f z.1, ⟨z.1, rfl⟩, (0, z.2 + χ z.1 • α), ?_, ?_⟩
      · exact ⟨z.2 + χ z.1 • α, rfl⟩
      · rw [hf]
        ext <;> simp

/-- Bracketing any ambient element with a vector of the graph lands in
ker χ in the old algebra, and hence in the graph. -/
theorem graph_ideal :
    Specs.LieAlgebrasAndRepresentations.DiagonalEnlargementStep.graph_ideal_type := by
  intro k _ A H _ _ _ _ θ χ α hcentral hchar haction
  refine ⟨{ carrier := {z | z.right = -(χ z.left • α)}
            zero_mem' := by
              change (0 : H) = -(χ (0 : A) • α)
              simp
            add_mem' := ?_
            smul_mem' := ?_
            lie_mem := ?_ }, fun _ => Iff.rfl⟩
  · intro x y hx hy
    change x.right + y.right = -(χ (x.left + y.left) • α)
    rw [hx, hy, map_add, add_smul]
    abel
  · intro c x hx
    change c • x.right = -(χ (c • x.left) • α)
    rw [hx, map_smul]
    simp only [smul_neg, smul_smul, smul_eq_mul]
  · intro x y hy
    change ⁅x.right, y.right⁆ =
      -(χ (⁅x.left, y.left⁆ + θ x.right y.left - θ y.right x.left) • α)
    rw [hy, lie_neg, lie_smul, hcentral, smul_zero, neg_zero,
      map_sub, map_add, hchar, haction, haction]
    simp

/-- The finite spectrum generates a finite type torsion-free ℤ-module,
which is free over the PID ℤ. This is the actual eigenvalue subgroup. -/
theorem eigenvalue_lattice :
    Specs.LieAlgebrasAndRepresentations.DiagonalEnlargementStep.eigenvalue_lattice_type := by
  intro B _ _ _ D
  classical
  let Γ := Specs.LieAlgebrasAndRepresentations.DiagonalEnlargementStep.eigenvalueGroup D
  letI : Finite {β : ℂ | D.HasEigenvalue β} := D.finite_hasEigenvalue.to_subtype
  haveI : AddGroup.FG Γ := AddGroup.closure_finite_fg _
  haveI : Module.Finite ℤ Γ := Module.Finite.iff_addGroup_fg.mpr inferInstance
  obtain ⟨m, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := Γ)
  exact ⟨m, ⟨b⟩⟩

section FixedVector

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A zero central-weight space surjects onto the nilradical quotient.
Weyl's theorem on that space then lifts a nonzero quotient vector. -/
theorem fixed_vector :
    Specs.LieAlgebrasAndRepresentations.DiagonalEnlargementStep.fixed_vector_type := by
  intro S T B _ _ _ _ _ _ _ _ _ _ _ θ r bT hS hw hq
  classical
  let ρ : S →ₗ⁅ℂ⁆ Module.End ℂ B :=
    ((LieDerivation.toLinearMapLieHom ℂ B).comp θ).comp (LieHom.inl ℂ S T)
  letI : LieRingModule S B := LieRingModule.compLieHom B ρ
  letI : LieModule ℂ S B := LieModule.compLieHom B ρ
  let N := (nilradical ℂ B).toSubmodule
  have hact (s : S) (x : B) : ⁅s, x⁆ = θ (s, 0) x := rfl
  let Z : LieSubmodule ℂ S B :=
    { carrier := {x | ∀ t : T, θ (0, t) x = 0}
      zero_mem' := by intro t; exact map_zero _
      add_mem' := by intro x y hx hy t; rw [map_add, hx t, hy t, add_zero]
      smul_mem' := by intro c x hx t; rw [map_smul, hx t, smul_zero]
      lie_mem := by
        intro s x hx t
        change θ (0, t) (θ (s, 0) x) = 0
        have h := congrArg (fun E : LieDerivation ℂ B B => E x)
          (θ.map_lie (0, t) (s, 0))
        have hz : ⁅((0 : S), t), (s, (0 : T))⁆ = (0 : S × T) := by ext <;> simp
        rw [hz, map_zero] at h
        change 0 = θ (0, t) (θ (s, 0) x) - θ (s, 0) (θ (0, t) x) at h
        simpa only [hx t, map_zero, sub_zero] using h.symm }
  let W : LieSubmodule ℂ S Z :=
    { toSubmodule := N.comap Z.toSubmodule.subtype
      lie_mem := by
        intro s x hx
        exact derivation_image ℂ B (θ (s, 0)) x.val }
  obtain ⟨n, c, w, hw⟩ := hw
  have heig (i : Fin n) (j : Fin r) :
      θ (0, bT j) (c i) = (w i j : ℂ) • c i := hw i j
  have hbasis (i : Fin n) (hi : c i ∉ N) : c i ∈ Z := by
    have hweight (j : Fin r) : w i j = 0 := by
      by_contra hj
      have hnonzero : (w i j : ℂ) ≠ 0 := by exact_mod_cast hj
      have hmem := derivation_image ℂ B (θ (0, bT j)) (c i)
      rw [heig i j] at hmem
      exact hi ((Submodule.smul_mem_iff N hnonzero).mp hmem)
    intro t
    change (Specs.LieAlgebrasAndRepresentations.DiagonalEnlargementStep.centerAction θ t) (c i) = 0
    rw [← bT.sum_repr t]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    have heig' (j : Fin r) :
        (Specs.LieAlgebrasAndRepresentations.DiagonalEnlargementStep.centerAction θ (bT j))
          (c i) = (w i j : ℂ) • c i := heig i j
    simp only [heig', hweight, Int.cast_zero, zero_smul, smul_zero, Finset.sum_const_zero]
  have hex : ∃ i : Fin n, c i ∉ N := by
    by_contra h
    have hc : ∀ i, c i ∈ N := by simpa using h
    have htop : N = ⊤ := by
      apply top_unique
      intro x _
      rw [← c.sum_repr x]
      exact N.sum_mem fun i _ => N.smul_mem _ (hc i)
    have hz := N.finrank_quotient_add_finrank
    have hNdim : Module.finrank ℂ N = Module.finrank ℂ B := by rw [htop]; simp
    change 0 < Module.finrank ℂ (B ⧸ N) at hq
    omega
  obtain ⟨i, hi⟩ := hex
  let z : Z := ⟨c i, hbasis i hi⟩
  let p := LieSubmodule.Quotient.mk' W
  have hz : p z ≠ 0 := by
    intro hz
    exact hi ((LieSubmodule.Quotient.mk_eq_zero W).mp hz)
  obtain ⟨s, hs⟩ := CompleteReducibility.quotient_section ℂ S Z hS W
  have hs' : p (s (p z)) = p z :=
    congrArg (fun f : (Z ⧸ W) →ₗ⁅ℂ,S⁆ (Z ⧸ W) => f (p z)) hs
  have htriv (a : S) : ⁅a, p z⁆ = 0 := by
    rw [← p.map_lie]
    apply (LieSubmodule.Quotient.mk_eq_zero W).mpr
    exact derivation_image ℂ B (θ (a, 0)) z.val
  refine ⟨(s (p z)).val, ?_, ?_⟩
  · rintro ⟨a, t⟩
    have hfixed : θ (a, 0) (s (p z)).val = 0 := by
      have h := s.map_lie a (p z)
      rw [htriv, map_zero] at h
      exact congrArg (fun x : Z => x.val) h.symm
    have hcentral := (s (p z)).property t
    have hsum : (a, t) = (a, 0) + (0, t) := by simp
    rw [hsum, map_add, LieDerivation.add_apply, hfixed, hcentral, add_zero]
  · intro hmem
    have hzero : p (s (p z)) = 0 :=
      (LieSubmodule.Quotient.mk_eq_zero W).mpr hmem
    exact hz (hs'.symm.trans hzero)

end FixedVector


section ProductExtension

attribute [local instance 100] LieRing.ofAssociativeRing
variable {k : Type u} [Field k]
variable {A : Type v} [LieRing A] [LieAlgebra k A]
variable {H : Type w} [LieRing H] [LieAlgebra k H]
variable {U : Type z} [LieRing U] [LieAlgebra k U]

/-- Commuting actions extend to the direct product. -/
def productAction (θ : H →ₗ⁅k⁆ LieDerivation k A A)
    (τ : U →ₗ⁅k⁆ LieDerivation k A A)
    (hc : ∀ h u, ⁅θ h, τ u⁆ = 0) :
    H × U →ₗ⁅k⁆ LieDerivation k A A :=
  { θ.toLinearMap.coprod τ.toLinearMap with
    map_lie' := by
      intro x y
      change θ ⁅x.1, y.1⁆ + τ ⁅x.2, y.2⁆ = ⁅θ x.1 + τ x.2, θ y.1 + τ y.2⁆
      rw [θ.map_lie, τ.map_lie, add_lie, lie_add, lie_add, hc, ← lie_skew (τ x.2) (θ y.1), hc]
      simp }

@[simp] theorem productAction_apply (θ : H →ₗ⁅k⁆ LieDerivation k A A)
    (τ : U →ₗ⁅k⁆ LieDerivation k A A) (hc : ∀ h u, ⁅θ h, τ u⁆ = 0)
    (h : H) (u : U) : productAction θ τ hc (h,u) = θ h + τ u := rfl

/-- Adjoining a commuting factor retains the old semidirect algebra faithfully. -/
def semidirectEmbedding (θ : H →ₗ⁅k⁆ LieDerivation k A A)
    (Θ : H × U →ₗ⁅k⁆ LieDerivation k A A)
    (hΘ : ∀ h, Θ (h, 0) = θ h) :
    (A ⋊⁅θ⁆ H) →ₗ⁅k⁆ (A ⋊⁅Θ⁆ (H × U)) where
  toFun x := ⟨x.left, (x.right, 0)⟩
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp
  map_lie' := by
    intro x y
    ext
    · change ⁅x.left, y.left⁆ + θ x.right y.left - θ y.right x.left =
        ⁅x.left, y.left⁆ + Θ (x.right, 0) y.left - Θ (y.right, 0) x.left
      rw [hΘ, hΘ]
    · rfl
    · exact (lie_zero (0 : U)).symm

theorem semidirectEmbedding_injective (θ : H →ₗ⁅k⁆ LieDerivation k A A)
    (Θ : H × U →ₗ⁅k⁆ LieDerivation k A A)
    (hΘ : ∀ h, Θ (h, 0) = θ h) :
    Function.Injective (semidirectEmbedding θ Θ hΘ) := by
  intro x y h
  have hl := congrArg (fun z : A ⋊⁅Θ⁆ (H × U) => z.left) h
  have hr := congrArg (fun z : A ⋊⁅Θ⁆ (H × U) => z.right.1) h
  exact LieAlgebra.SemiDirectSum.ext hl hr

/-- An action fixing d commutes with its adjoint. -/
theorem commute_ad_of_fixed (θ : H →ₗ⁅k⁆ LieDerivation k A A)
    (d : A) (hd : ∀ h, θ h d = 0) (h : H) :
    Commute (LieDerivation.ad k A d).toLinearMap (θ h).toLinearMap := by
  ext x
  change -⁅θ h x, d⁆ = θ h (-⁅x, d⁆)
  rw [map_neg, (θ h).apply_lie_eq_add, hd, lie_zero, zero_add]

end ProductExtension

section GraphAssembly

variable {k : Type u} [Field k]
variable {A : Type v} [LieRing A] [LieAlgebra k A]
variable {H : Type w} [LieRing H] [LieAlgebra k H]

/-- The ambient adjoint action restricts to an ideal. -/
def idealAdjoint (I : LieIdeal k A) : A →ₗ⁅k⁆ LieDerivation k I I where
  toFun a :=
    { toFun x := ⟨⁅a, x.val⁆, I.lie_mem x.property⟩
      map_add' := by intro x y; apply Subtype.ext; exact lie_add a x.val y.val
      map_smul' := by intro c x; apply Subtype.ext; exact lie_smul c a x.val
      leibniz' := by
        intro x y
        apply Subtype.ext
        change ⁅a, ⁅x.val, y.val⁆⁆ = ⁅x.val, ⁅a, y.val⁆⁆ - ⁅y.val, ⁅a, x.val⁆⁆
        rw [leibniz_lie, ← lie_skew y.val ⁅a, x.val⁆]
        abel }
  map_add' := by intro a b; ext x; exact add_lie a b x.val
  map_smul' := by intro c a; ext x; exact smul_lie c a x.val
  map_lie' := by
    intro a b
    ext x
    change ⁅⁅a, b⁆, x.val⁆ = ⁅a, ⁅b, x.val⁆⁆ - ⁅b, ⁅a, x.val⁆⁆
    rw [leibniz_lie, add_sub_cancel_right]

variable (θ : H →ₗ⁅k⁆ LieDerivation k A A)
variable (χ : A →ₗ[k] k) (α : H)
variable (I : LieIdeal k (A ⋊⁅θ⁆ H))
variable (hI : ∀ z : A ⋊⁅θ⁆ H, z ∈ I ↔ z.right = -(χ z.left • α))

/-- Restrict the original external factor's adjoint action to the graph ideal. -/
def graphAction : H →ₗ⁅k⁆ LieDerivation k I I :=
  (idealAdjoint I).comp (LieAlgebra.SemiDirectSum.inr θ)

/-- The sum map from the graph's semidirect product into the ambient algebra. -/
def graphSplittingHom : (I ⋊⁅graphAction θ I⁆ H) →ₗ⁅k⁆ (A ⋊⁅θ⁆ H) where
  toFun z := z.left.val + LieAlgebra.SemiDirectSum.inr θ z.right
  map_add' := by
    intro x y
    change (x.left.val + y.left.val) + LieAlgebra.SemiDirectSum.inr θ (x.right + y.right) = _
    rw [map_add]
    abel
  map_smul' := by
    intro c x
    change c • x.left.val + LieAlgebra.SemiDirectSum.inr θ (c • x.right) = _
    simp only [map_smul, smul_add, RingHom.id_apply]
  map_lie' := by
    intro x y
    change ⁅x.left.val, y.left.val⁆ +
      ⁅LieAlgebra.SemiDirectSum.inr θ x.right, y.left.val⁆ -
      ⁅LieAlgebra.SemiDirectSum.inr θ y.right, x.left.val⁆ +
      LieAlgebra.SemiDirectSum.inr θ ⁅x.right, y.right⁆ = _
    rw [LieHom.map_lie, add_lie, lie_add, lie_add,
      ← lie_skew (x.left.val) (LieAlgebra.SemiDirectSum.inr θ y.right)]
    abel

include χ α hI in
theorem graphSplittingHom_bijective :
    Function.Bijective (graphSplittingHom θ I) := by
  constructor
  · intro x y h
    have hleft : x.left.val.left = y.left.val.left :=
      by simpa only [graphSplittingHom, LieHom.coe_mk, LieAlgebra.SemiDirectSum.add_eq_mk,
        LieAlgebra.SemiDirectSum.inr_eq_mk, add_zero] using
        congrArg LieAlgebra.SemiDirectSum.left h
    have hgraph : x.left = y.left := by
      apply Subtype.ext
      apply LieAlgebra.SemiDirectSum.ext hleft
      rw [(hI x.left.val).mp x.left.property, (hI y.left.val).mp y.left.property, hleft]
    have hright : x.right = y.right := by
      have h' := congrArg LieAlgebra.SemiDirectSum.right h
      change x.left.val.right + x.right = y.left.val.right + y.right at h'
      rw [hgraph] at h'
      exact add_left_cancel h'
    exact LieAlgebra.SemiDirectSum.ext hgraph hright
  · intro z
    let x : I := ⟨⟨z.left, -(χ z.left • α)⟩, (hI _).mpr rfl⟩
    refine ⟨⟨x, z.right + χ z.left • α⟩, ?_⟩
    apply LieAlgebra.SemiDirectSum.ext
    · exact add_zero _
    · change -(χ z.left • α) + (z.right + χ z.left • α) = z.right
      abel

/-- The graph complement yields the canonical Lie algebra splitting. -/
def graphSplitting : (I ⋊⁅graphAction θ I⁆ H) ≃ₗ⁅k⁆ (A ⋊⁅θ⁆ H) :=
  LieEquiv.ofBijective (graphSplittingHom θ I) (graphSplittingHom_bijective θ χ α I hI)


include χ α hI in
/-- A graph ideal over a solvable algebra is solvable: its derived algebra
embeds back into the original solvable algebra. -/
theorem graph_solvable [LieAlgebra.IsSolvable A] : LieAlgebra.IsSolvable I := by
  let J := LieAlgebra.derivedSeries k I 1
  let p : I →ₗ⁅k⁆ H := (LieAlgebra.SemiDirectSum.projr θ).comp I.incl
  have hJ : J ≤ p.ker := by
    change J.toSubmodule ≤ p.ker.toSubmodule
    change (LieAlgebra.derivedSeries k I 1).toSubmodule ≤ p.ker.toSubmodule
    have hseries : (LieAlgebra.derivedSeries k I 1).toLieSubalgebra.toSubmodule =
        Submodule.span k {⁅x, y⁆ | (x : I) (y : I)} :=
      LieAlgebra.coe_derivedSeries_one_eq k I
    change (LieAlgebra.derivedSeries k I 1).toSubmodule = _ at hseries
    rw [hseries]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, y, rfl⟩
    change ⁅x.val.right, y.val.right⁆ = 0
    rw [(hI x.val).mp x.property, (hI y.val).mp y.property]
    simp only [neg_lie, lie_neg, smul_lie, lie_smul, lie_self, smul_zero, neg_zero]
  have hright (x : J) : x.val.val.right = 0 := hJ x.property
  let f : J →ₗ⁅k⁆ A :=
    { toFun x := x.val.val.left
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl
      map_lie' := by
        intro x y
        change ⁅x.val.val.left, y.val.val.left⁆ + θ x.val.val.right y.val.val.left -
          θ y.val.val.right x.val.val.left = _
        simp only [hright, map_zero, LieDerivation.zero_apply, add_zero, sub_zero] }
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact LieAlgebra.SemiDirectSum.ext h ((hright x).trans (hright y).symm)
  haveI : LieAlgebra.IsSolvable J := hf.lieAlgebra_isSolvable
  obtain ⟨n, hn⟩ := LieAlgebra.IsSolvable.solvable k J
  apply LieAlgebra.IsSolvable.mk (R := k) (k := n + 1)
  change LieAlgebra.derivedSeriesOfIdeal k I (n + 1) ⊤ = ⊥
  rw [LieAlgebra.derivedSeriesOfIdeal_add]
  exact (J.derivedSeries_eq_bot_iff n).mp hn


/-- An invariant old ideal annihilated by the character lifts into the graph. -/
def graphIdealLift (N : LieIdeal k A) (hχN : ∀ x ∈ N, χ x = 0)
    (hθN : ∀ h x, x ∈ N → θ h x ∈ N) : LieIdeal k I where
  carrier := {x | x.val.left ∈ N}
  zero_mem' := N.zero_mem
  add_mem' := fun hx hy => N.add_mem hx hy
  smul_mem' := fun c _ hx => N.smul_mem c hx
  lie_mem := by
    intro x y hy
    have hyright : y.val.right = 0 := by
      rw [(hI y.val).mp y.property, hχN _ hy, zero_smul, neg_zero]
    change ⁅x.val.left, y.val.left⁆ + θ x.val.right y.val.left - θ y.val.right x.val.left ∈ N
    rw [hyright, map_zero, LieDerivation.zero_apply, sub_zero]
    exact N.add_mem (N.lie_mem hy) (hθN _ _ hy)

/-- The lifted ideal is isomorphic to the old ideal as a Lie algebra;
its left projection suffices for transfer of nilpotence. -/
def graphIdealLiftHom (N : LieIdeal k A) (hχN : ∀ x ∈ N, χ x = 0)
    (hθN : ∀ h x, x ∈ N → θ h x ∈ N) :
    (graphIdealLift θ χ α I hI N hχN hθN) →ₗ⁅k⁆ N where
  toFun x := ⟨x.val.val.left, x.property⟩
  map_add' := by intro x y; rfl
  map_smul' := by intro c x; rfl
  map_lie' := by
    intro x y
    apply Subtype.ext
    have hxright : x.val.val.right = 0 := by
      rw [(hI x.val.val).mp x.val.property, hχN _ x.property, zero_smul, neg_zero]
    have hyright : y.val.val.right = 0 := by
      rw [(hI y.val.val).mp y.val.property, hχN _ y.property, zero_smul, neg_zero]
    change ⁅x.val.val.left, y.val.val.left⁆ + θ x.val.val.right y.val.val.left -
      θ y.val.val.right x.val.val.left = _
    simp only [hxright, hyright, map_zero, LieDerivation.zero_apply, add_zero, sub_zero]
    rfl

include hI in
theorem graphIdealLiftHom_injective (N : LieIdeal k A) (hχN : ∀ x ∈ N, χ x = 0)
    (hθN : ∀ h x, x ∈ N → θ h x ∈ N) :
    Function.Injective (graphIdealLiftHom θ χ α I hI N hχN hθN) := by
  intro x y h
  have hleft : x.val.val.left = y.val.val.left := congrArg Subtype.val h
  apply Subtype.ext
  apply Subtype.ext
  apply LieAlgebra.SemiDirectSum.ext hleft
  rw [(hI x.val.val).mp x.val.property, (hI y.val.val).mp y.val.property, hleft]

include hI in
theorem graphIdealLift_nilpotent (N : LieIdeal k A) (hχN : ∀ x ∈ N, χ x = 0)
    (hθN : ∀ h x, x ∈ N → θ h x ∈ N) [LieRing.IsNilpotent N] :
    LieRing.IsNilpotent (graphIdealLift θ χ α I hI N hχN hθN) :=
  (graphIdealLiftHom_injective θ χ α I hI N hχN hθN).lieAlgebra_isNilpotent


/-- Nilpotence descends through an injective intertwiner. -/
theorem isNilpotent_of_intertwiner {V W : Type*}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (f : V →ₗ[k] W) (hf : Function.Injective f)
    (D : Module.End k V) (E : Module.End k W)
    (h : ∀ x, f (D x) = E (f x)) (hE : IsNilpotent E) : IsNilpotent D := by
  have hpow (n : ℕ) (x : V) : f ((D^n) x) = (E^n) (f x) := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [pow_succ', Module.End.mul_apply, h, ih]
  obtain ⟨n, hn⟩ := hE
  refine ⟨n, ?_⟩
  ext x
  apply hf
  simpa only [hn, LinearMap.zero_apply, map_zero] using hpow n x

/-- The new generator inside the graph ideal. -/
def graphVector (d : A) (hd : χ d = 1) : I :=
  ⟨⟨d, -α⟩, (hI _).mpr (by simp only [hd, one_smul])⟩

include hI in
theorem graph_ad_nilpotent (d : A) (hd : χ d = 1) (hαd : θ α d = 0)
    (hN : IsNilpotent (LieAlgebra.ad k A d - (θ α).toLinearMap)) :
    IsNilpotent (LieAlgebra.ad k I (graphVector θ χ α I hI d hd)) := by
  let f : I →ₗ[k] A := (LieAlgebra.SemiDirectSum.projl θ).comp I.incl.toLinearMap
  have hf : Function.Injective f := by
    intro x y h
    change x.val.left = y.val.left at h
    apply Subtype.ext
    apply LieAlgebra.SemiDirectSum.ext h
    change x.val.right = y.val.right
    rw [(hI x.val).mp x.property, (hI y.val).mp y.property]
    exact congrArg (fun a => -(χ a • α)) h
  apply isNilpotent_of_intertwiner f hf _ _ _ hN
  intro x
  change ⁅d, x.val.left⁆ + θ (-α) x.val.left - θ x.val.right d =
    ⁅d, x.val.left⁆ - θ α x.val.left
  rw [(hI x.val).mp x.property, map_neg, map_neg, map_smul,
    LieDerivation.neg_apply, LieDerivation.neg_apply, LieDerivation.smul_apply, hαd]
  simp only [smul_zero, neg_zero, sub_zero, sub_eq_add_neg, add_zero]


/-- Any subspace obtained by adjoining one vector to the lifted old ideal is
an ideal once all brackets and derivation images are in the old ideal. -/
def graphSumIdeal (N : LieIdeal k A) (hχN : ∀ x ∈ N, χ x = 0)
    (hθN : ∀ h x, x ∈ N → θ h x ∈ N) (y : I)
    (hbr : ∀ a b : A, ⁅a, b⁆ ∈ N) (hθall : ∀ h a, θ h a ∈ N) : LieIdeal k I :=
  { toSubmodule := (graphIdealLift θ χ α I hI N hχN hθN).toSubmodule ⊔
      Submodule.span k {y}
    lie_mem := by
      intro x z _
      apply (show (graphIdealLift θ χ α I hI N hχN hθN).toSubmodule ≤
        (graphIdealLift θ χ α I hI N hχN hθN).toSubmodule ⊔ Submodule.span k {y}
        from le_sup_left)
      change ⁅x.val.left, z.val.left⁆ + θ x.val.right z.val.left - θ z.val.right x.val.left ∈ N
      exact N.sub_mem (N.add_mem (hbr _ _) (hθall _ _)) (hθall _ _) }

include hI in
theorem graphIdealLift_space (N : LieIdeal k A) (hχN : ∀ x ∈ N, χ x = 0)
    (hθN : ∀ h x, x ∈ N → θ h x ∈ N) :
    (graphIdealLift θ χ α I hI N hχN hθN).toSubmodule.map I.incl.toLinearMap =
      N.toSubmodule.map (LieAlgebra.SemiDirectSum.inl θ).toLinearMap := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.val.left, hx, ?_⟩
    change (⟨x.val.left, 0⟩ : A ⋊⁅θ⁆ H) = x.val
    apply LieAlgebra.SemiDirectSum.ext
    · rfl
    · change 0 = x.val.right
      rw [(hI x.val).mp x.property, hχN _ hx, zero_smul, neg_zero]
  · rintro ⟨a, ha, rfl⟩
    have hain : LieAlgebra.SemiDirectSum.inl θ a ∈ I := by
      apply (hI _).mpr
      change 0 = -(χ a • α)
      rw [hχN _ ha, zero_smul, neg_zero]
    exact ⟨⟨LieAlgebra.SemiDirectSum.inl θ a, hain⟩, ha, rfl⟩

include hI in
theorem graphSumIdeal_space (N : LieIdeal k A) (hχN : ∀ x ∈ N, χ x = 0)
    (hθN : ∀ h x, x ∈ N → θ h x ∈ N) (y : I)
    (hbr : ∀ a b : A, ⁅a, b⁆ ∈ N) (hθall : ∀ h a, θ h a ∈ N) :
    (graphSumIdeal θ χ α I hI N hχN hθN y hbr hθall).toSubmodule.map I.incl.toLinearMap =
      N.toSubmodule.map (LieAlgebra.SemiDirectSum.inl θ).toLinearMap ⊔
        Submodule.span k {y.val} := by
  change ((graphIdealLift θ χ α I hI N hχN hθN).toSubmodule ⊔
    Submodule.span k {y}).map I.incl.toLinearMap = _
  rw [Submodule.map_sup, graphIdealLift_space θ χ α I hI N hχN hθN,
    Submodule.map_span, Set.image_singleton]
  rfl

end GraphAssembly

section GraphEquivalence

variable {k : Type u} [Field k]
variable {A : Type v} [LieRing A] [LieAlgebra k A]
variable {H : Type w} [LieRing H] [LieAlgebra k H]

def graphEquiv (θ : H →ₗ⁅k⁆ LieDerivation k A A)
    (χ : A →ₗ[k] k) (α : H) (I : LieIdeal k (A ⋊⁅θ⁆ H))
    (hI : ∀ z : A ⋊⁅θ⁆ H, z ∈ I ↔ z.right = -(χ z.left • α)) : A ≃ₗ[k] I where
  toFun x := ⟨⟨x, -(χ x • α)⟩, (hI _).mpr rfl⟩
  invFun x := x.val.left
  left_inv x := rfl
  right_inv x := by
    apply Subtype.ext
    apply LieAlgebra.SemiDirectSum.ext
    · rfl
    · exact ((hI x.val).mp x.property).symm
  map_add' x y := by
    apply Subtype.ext
    apply LieAlgebra.SemiDirectSum.ext
    · rfl
    · change -(χ (x+y) • α) = -(χ x • α) + -(χ y • α)
      simp [add_smul, add_comm]
  map_smul' c x := by
    apply Subtype.ext
    apply LieAlgebra.SemiDirectSum.ext
    · rfl
    · change -(χ (c • x) • α) = c • -(χ x • α)
      simp [smul_smul]

theorem graphEquiv_equivariant
    (θ : H →ₗ⁅k⁆ LieDerivation k A A)
    (χ : A →ₗ[k] k) (α : H) (I : LieIdeal k (A ⋊⁅θ⁆ H))
    (hI : ∀ z : A ⋊⁅θ⁆ H, z ∈ I ↔ z.right = -(χ z.left • α))
    (hcentral : ∀ h : H, ⁅h, α⁆ = 0)
    (hχ : ∀ h x, χ (θ h x) = 0)
    (σ : H →ₗ⁅k⁆ LieDerivation k I I)
    (hσ : ∀ h x, (σ h x : A ⋊⁅θ⁆ H) =
      ⁅LieAlgebra.SemiDirectSum.inr θ h, (x : A ⋊⁅θ⁆ H)⁆)
    (h : H) (x : A) :
    σ h (graphEquiv θ χ α I hI x) = graphEquiv θ χ α I hI (θ h x) := by
  apply Subtype.ext
  rw [hσ]
  apply LieAlgebra.SemiDirectSum.ext
  · change ⁅(0 : A), x⁆ + θ h x - θ (-(χ x • α)) 0 = θ h x
    simp
  · change ⁅h, -(χ x • α)⁆ = -(χ (θ h x) • α)
    rw [hχ, zero_smul, neg_zero, lie_neg, lie_smul, hcentral, smul_zero, neg_zero]



end GraphEquivalence

section WeightTransport

open Specs.LieAlgebrasAndRepresentations.DiagonalEnlargementStep
variable {ι T V W : Type*}
variable [AddCommGroup T] [Module ℂ T]
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem integer_weights_transport (b : Basis ι ℂ T)
    (ρ : T →ₗ[ℂ] Module.End ℂ V) (σ : T →ₗ[ℂ] Module.End ℂ W)
    (e : V ≃ₗ[ℂ] W) (he : ∀ t x, σ t (e x) = e (ρ t x))
    (hw : HasIntegerWeights b ρ) : HasIntegerWeights b σ := by
  obtain ⟨n, c, w, hw⟩ := hw
  refine ⟨n, c.map e, w, ?_⟩
  intro i j
  change σ (b j) (e (c i)) = (w i j : ℂ) • e (c i)
  rw [he, hw, map_smul]

end WeightTransport

section IntegralTorus

open Specs.LieAlgebrasAndRepresentations.DiagonalEnlargementStep
attribute [local instance 100] LieRing.ofAssociativeRing
variable {B : Type u} [LieRing B] [LieAlgebra ℂ B] [FiniteDimensional ℂ B]

private theorem spectral_span (D : LieDerivation ℂ B B) :
    (⨆ β : eigenvalueGroup D.toLinearMap,
      Module.End.maxGenEigenspace D.toLinearMap (β : ℂ)) = ⊤ := by
  apply top_unique
  rw [← Module.End.iSup_maxGenEigenspace_eq_top D.toLinearMap]
  apply iSup_le
  intro β
  by_cases hβ : Module.End.HasEigenvalue D.toLinearMap β
  · exact le_iSup (fun γ : eigenvalueGroup D.toLinearMap =>
      Module.End.maxGenEigenspace D.toLinearMap (γ : ℂ)) ⟨β, AddSubgroup.subset_closure hβ⟩
  · have hz : Module.End.maxGenEigenspace D.toLinearMap β = ⊥ := by
      rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank D.toLinearMap]
      apply not_ne_iff.mp
      intro hn
      apply hβ
      apply Module.End.hasEigenvalue_of_hasGenEigenvalue
      exact hn
    rw [hz]
    exact bot_le

private def spectralEquiv (D : LieDerivation ℂ B B) :
    (⨁ β : eigenvalueGroup D.toLinearMap, Module.End.maxGenEigenspace D.toLinearMap (β : ℂ)) ≃ₗ[ℂ] B :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap _) <|
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      ((Module.End.independent_genEigenspace D.toLinearMap ⊤).comp Subtype.val_injective)
      (spectral_span D)

private def scalarEnd (D : LieDerivation ℂ B B)
    (f : eigenvalueGroup D.toLinearMap → ℂ) : Module.End ℂ B :=
  (DirectSum.toModule ℂ _ B (fun β => f β • (Module.End.maxGenEigenspace D.toLinearMap (β : ℂ)).subtype)).comp
    (spectralEquiv D).symm.toLinearMap

private theorem scalarEnd_apply (D : LieDerivation ℂ B B)
    (f : eigenvalueGroup D.toLinearMap → ℂ)
    (β : eigenvalueGroup D.toLinearMap) (x : B)
    (hx : x ∈ Module.End.maxGenEigenspace D.toLinearMap (β : ℂ)) :
    scalarEnd D f x = f β • x := by
  have hx' : (spectralEquiv D) (DirectSum.lof ℂ _ _ β ⟨x, hx⟩) = x := by
    exact DirectSum.coeLinearMap_lof _ β ⟨x, hx⟩
  rw [← hx', scalarEnd, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply, DirectSum.toModule_lof]
  simp only [hx', LinearMap.smul_apply]
  rfl


private theorem spectral_induction (D : LieDerivation ℂ B B) (p : B → Prop)
    (h : ∀ β : eigenvalueGroup D.toLinearMap, ∀ x ∈ Module.End.maxGenEigenspace D.toLinearMap (β : ℂ), p x)
    (hz : p 0) (ha : ∀ x y, p x → p y → p (x+y)) (x : B) : p x := by
  have hx : x ∈ ⨆ β : eigenvalueGroup D.toLinearMap,
      Module.End.maxGenEigenspace D.toLinearMap (β : ℂ) := by rw [spectral_span D]; trivial
  exact Submodule.iSup_induction _ (motive := p) hx h hz ha

private def scalarDerivation (D : LieDerivation ℂ B B)
    (f : eigenvalueGroup D.toLinearMap →+ ℂ) : LieDerivation ℂ B B :=
  { scalarEnd D f with
    leibniz' := by
      intro x y
      suffices ∀ x y, scalarEnd D f ⁅x, y⁆ =
          ⁅scalarEnd D f x, y⁆ + ⁅x, scalarEnd D f y⁆ by
        rw [this, ← lie_skew y (scalarEnd D f x)]
        abel
      intro x
      apply spectral_induction D
        (fun x => ∀ y, scalarEnd D f ⁅x, y⁆ =
          ⁅scalarEnd D f x, y⁆ + ⁅x, scalarEnd D f y⁆)
      · intro β x hx y
        apply spectral_induction D
          (fun y => scalarEnd D f ⁅x, y⁆ =
            ⁅scalarEnd D f x, y⁆ + ⁅x, scalarEnd D f y⁆)
        · intro γ y hy
          have hxy := generalized_eigenspace_bracket D (β : ℂ) (γ : ℂ) x y hx hy
          rw [scalarEnd_apply D f (β + γ) ⁅x,y⁆ hxy,
            scalarEnd_apply D f β x hx, scalarEnd_apply D f γ y hy,
            f.map_add, smul_lie, lie_smul, add_smul]
        · simp
        · intro y z hy hz
          simp only [lie_add, map_add, hy, hz]
          abel
      · intro y
        simp
      · intro x z hx hz y
        simp only [add_lie, map_add, hx y, hz y]
        abel }

private theorem scalarDerivation_apply (D : LieDerivation ℂ B B)
    (f : eigenvalueGroup D.toLinearMap →+ ℂ)
    (β : eigenvalueGroup D.toLinearMap) (x : B)
    (hx : x ∈ Module.End.maxGenEigenspace D.toLinearMap (β : ℂ)) :
    scalarDerivation D f x = f β • x := scalarEnd_apply D f β x hx

private def coordinateCharacter (D : LieDerivation ℂ B B) {m : ℕ}
    (b : Basis (Fin m) ℤ (eigenvalueGroup D.toLinearMap)) (z : Torus m) :
    eigenvalueGroup D.toLinearMap →+ ℂ where
  toFun β := ∑ j, (b.repr β j : ℂ) * z j
  map_zero' := by simp
  map_add' β γ := by simp [map_add, add_mul, Finset.sum_add_distrib]

private theorem coordinateCharacter_single (D : LieDerivation ℂ B B) {m : ℕ}
    (b : Basis (Fin m) ℤ (eigenvalueGroup D.toLinearMap))
    (β : eigenvalueGroup D.toLinearMap) (j : Fin m) :
    coordinateCharacter D b (Pi.single j 1) β = (b.repr β j : ℂ) := by
  classical
  simp [coordinateCharacter, Pi.single_apply, mul_ite]

private def coordinateAction (D : LieDerivation ℂ B B) {m : ℕ}
    (b : Basis (Fin m) ℤ (eigenvalueGroup D.toLinearMap)) :
    Torus m →ₗ⁅ℂ⁆ LieDerivation ℂ B B where
  toFun z := scalarDerivation D (coordinateCharacter D b z)
  map_add' z w := by
    ext x
    apply spectral_induction D (fun x => scalarDerivation D (coordinateCharacter D b (z+w)) x =
      (scalarDerivation D (coordinateCharacter D b z) + scalarDerivation D (coordinateCharacter D b w)) x)
    · intro β x hx
      simp only [LieDerivation.add_apply, scalarDerivation_apply D _ β x hx]
      simp [coordinateCharacter, mul_add, Finset.sum_add_distrib, add_smul]
    · simp
    · intro x y hx hy
      simp only [map_add, LieDerivation.add_apply] at *
      rw [hx, hy]
  map_smul' c z := by
    ext x
    apply spectral_induction D (fun x => scalarDerivation D (coordinateCharacter D b (c • z)) x =
      (c • scalarDerivation D (coordinateCharacter D b z)) x)
    · intro β x hx
      simp only [LieDerivation.smul_apply, scalarDerivation_apply D _ β x hx]
      rw [smul_smul]
      congr 1
      change (∑ j, (b.repr β j : ℂ) * (c * z j)) = c * (∑ j, (b.repr β j : ℂ) * z j)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ac_rfl
    · simp
    · intro x y hx hy
      simp only [map_add, LieDerivation.smul_apply] at *
      rw [hx, hy]
  map_lie' := by
    intro z w
    ext x
    have hz : ⁅z,w⁆ = (0 : Torus m) := by ext j; simp [Ring.lie_def, mul_comm]
    rw [hz]
    change scalarDerivation D (coordinateCharacter D b 0) x =
      scalarDerivation D (coordinateCharacter D b z) (scalarDerivation D (coordinateCharacter D b w) x) -
        scalarDerivation D (coordinateCharacter D b w) (scalarDerivation D (coordinateCharacter D b z) x)
    apply spectral_induction D
      (fun x => scalarDerivation D (coordinateCharacter D b 0) x =
        scalarDerivation D (coordinateCharacter D b z) (scalarDerivation D (coordinateCharacter D b w) x) -
          scalarDerivation D (coordinateCharacter D b w) (scalarDerivation D (coordinateCharacter D b z) x))
    · intro β x hx
      simp only [scalarDerivation_apply D _ β x hx, map_smul]
      simp [coordinateCharacter, smul_smul, mul_comm]
    · simp
    · intro x y hx hy
      simp only [map_add]
      rw [hx, hy]
      abel

private theorem coordinateAction_apply (D : LieDerivation ℂ B B) {m : ℕ}
    (b : Basis (Fin m) ℤ (eigenvalueGroup D.toLinearMap)) (z : Torus m)
    (β : eigenvalueGroup D.toLinearMap) (x : B)
    (hx : x ∈ Module.End.maxGenEigenspace D.toLinearMap (β : ℂ)) :
    coordinateAction D b z x = coordinateCharacter D b z β • x := scalarDerivation_apply D _ β x hx

private theorem coordinateAction_centralizer (D : LieDerivation ℂ B B) {m : ℕ}
    (b : Basis (Fin m) ℤ (eigenvalueGroup D.toLinearMap))
    (E : LieDerivation ℂ B B) (h : Commute D.toLinearMap E.toLinearMap) (z : Torus m) :
    ⁅E, coordinateAction D b z⁆ = 0 := by
  ext x
  change E (coordinateAction D b z x) - coordinateAction D b z (E x) = 0
  apply spectral_induction D
    (fun x => E (coordinateAction D b z x) - coordinateAction D b z (E x) = 0)
  · intro β x hx
    have hEx := Module.End.mapsTo_maxGenEigenspace_of_comm h (β : ℂ) hx
    rw [coordinateAction_apply D b z β x hx, map_smul,
      coordinateAction_apply D b z β (E x) hEx, sub_self]
  · simp
  · intro x y hx hy
    simp only [map_add]
    rw [add_sub_add_comm, hx, hy, add_zero]

private theorem coordinateAction_kills_kernel (D : LieDerivation ℂ B B) {m : ℕ}
    (b : Basis (Fin m) ℤ (eigenvalueGroup D.toLinearMap))
    (x : B) (hx : D x = 0) (z : Torus m) : coordinateAction D b z x = 0 := by
  have hx' : x ∈ Module.End.maxGenEigenspace D.toLinearMap 0 := by
    apply (Module.End.mem_maxGenEigenspace _ _ _).mpr
    exact ⟨1, by simpa using hx⟩
  rw [coordinateAction_apply D b z 0 x hx']
  simp

private theorem coordinateCharacter_basis (D : LieDerivation ℂ B B) {m : ℕ}
    (b : Basis (Fin m) ℤ (eigenvalueGroup D.toLinearMap))
    (β : eigenvalueGroup D.toLinearMap) :
    coordinateCharacter D b (fun j => (b j : ℂ)) β = (β : ℂ) := by
  change (∑ j, (b.repr β j : ℂ) * (b j : ℂ)) = (β : ℂ)
  have h := congrArg (eigenvalueGroup D.toLinearMap).subtype (b.sum_repr β)
  change (eigenvalueGroup D.toLinearMap).subtype (∑ j, b.repr β j • b j) = (β : ℂ) at h
  rw [map_sum] at h
  simpa only [map_zsmul, zsmul_eq_mul, AddSubgroup.subtype_apply] using h

private theorem coordinateAction_jordan (D : LieDerivation ℂ B B) {m : ℕ}
    (b : Basis (Fin m) ℤ (eigenvalueGroup D.toLinearMap)) :
    ∃ N : Module.End ℂ B, IsJordanDecomposition D.toLinearMap
      (coordinateAction D b (fun j => (b j : ℂ))).toLinearMap N := by
  obtain ⟨s, n, hdec, hpoly, hstable, huniq⟩ := linear_jordan_decomposition D.toLinearMap
  rcases hdec with ⟨he, hc, hs, hn⟩
  have hDs : Commute D.toLinearMap s := by
    rw [he]
    exact (Commute.refl s).add_left hc.symm
  have hss : s.IsSemisimple := (absolutely_semisimple_iff s).mp hs
  have hscalar (β : eigenvalueGroup D.toLinearMap) (x : B)
      (hx : x ∈ Module.End.maxGenEigenspace D.toLinearMap (β : ℂ)) : s x = (β : ℂ) • x := by
    apply Module.End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil hx hDs hss.isFinitelySemisimple
    simpa only [he, add_sub_cancel_left] using hn
  have haction : (coordinateAction D b (fun j => (b j : ℂ))).toLinearMap = s := by
    ext x
    apply spectral_induction D (fun x => coordinateAction D b (fun j => (b j : ℂ)) x = s x)
    · intro β x hx
      rw [coordinateAction_apply D b _ β x hx, coordinateCharacter_basis D b β, hscalar β x hx]
    · simp
    · intro x y hx hy
      simp only [map_add]
      rw [hx, hy]
  exact ⟨n, haction.symm ▸ ⟨he, hc, hs, hn⟩⟩

/-- Integer-coordinate derivations on the actual spectral lattice. -/
theorem exists_integral_torus (D : LieDerivation ℂ B B) : Nonempty (IntegralTorusData D) := by
  classical
  let Γ := eigenvalueGroup D.toLinearMap
  letI : Finite {β : ℂ | Module.End.HasEigenvalue D.toLinearMap β} :=
    (Module.End.finite_hasEigenvalue D.toLinearMap).to_subtype
  haveI : AddGroup.FG Γ := AddGroup.closure_finite_fg _
  haveI : Module.Finite ℤ Γ := Module.Finite.iff_addGroup_fg.mpr inferInstance
  obtain ⟨m, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := Γ)
  exact ⟨{
    rank := m
    basis := b
    action := coordinateAction D b
    on_generalized_eigenspace := by
      intro β hβ x hx j
      rw [coordinateAction_apply D b _ ⟨β,hβ⟩ x hx, coordinateCharacter_single D b ⟨β,hβ⟩ j]
    centralizer := coordinateAction_centralizer D b
    kills_kernel := coordinateAction_kills_kernel D b
    jordan := coordinateAction_jordan D b
  }⟩


/-- The new torus has an integral eigenbasis on the original Lie algebra. -/
theorem integral_torus_has_integer_weights (D : LieDerivation ℂ B B)
    (t : IntegralTorusData D) :
    HasIntegerWeights (Pi.basisFun ℂ (Fin t.rank))
      (((LieDerivation.toLinearMapLieHom ℂ B).comp t.action).toLinearMap) := by
  classical
  let A : eigenvalueGroup D.toLinearMap → Submodule ℂ B :=
    fun β => Module.End.maxGenEigenspace D.toLinearMap (β : ℂ)
  have hi : DirectSum.IsInternal A :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      ((Module.End.independent_genEigenspace D.toLinearMap ⊤).comp Subtype.val_injective)
      (spectral_span D)
  let J := Σ β : eigenvalueGroup D.toLinearMap, Fin (Module.finrank ℂ (A β))
  let cb : Basis J ℂ B := hi.collectedBasis (fun β => Module.finBasis ℂ (A β))
  letI : Fintype J := cb.fintypeIndexOfRankLtAleph0 (Module.rank_lt_aleph0 ℂ B)
  let n := Fintype.card J
  let e : J ≃ Fin n := Fintype.equivFin J
  let c : Basis (Fin n) ℂ B := cb.reindex e
  let w : Fin n → Fin t.rank → ℤ := fun i j => t.basis.repr (e.symm i).1 j
  refine ⟨n,c,w,?_⟩
  intro i j
  have hm := hi.collectedBasis_mem (fun β => Module.finBasis ℂ (A β)) (e.symm i)
  have hm' : c i ∈ A (e.symm i).1 := by
    simpa only [c, Basis.reindex_apply] using hm
  have h := t.on_generalized_eigenspace ((e.symm i).1 : ℂ) (e.symm i).1.property (c i) hm' j
  simp only [Pi.basisFun_apply]
  change t.action (Pi.single j 1) (c i) = (t.basis.repr (e.symm i).1 j : ℂ) • c i
  exact h

end IntegralTorus

section SimultaneousWeights

attribute [local instance 100] LieRing.ofAssociativeRing
variable {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

private theorem semisimple_of_eigenbasis {ι : Type v} (c : Basis ι ℂ V)
    (f : Module.End ℂ V) (w : ι → ℂ) (hw : ∀ i, f (c i) = w i • c i) : f.IsSemisimple := by
  obtain ⟨s,n,⟨he,hc,hs,hn⟩,-,-,-⟩ := linear_jordan_decomposition f
  have hDs : Commute f s := by
    rw [he]
    exact (Commute.refl s).add_left hc.symm
  have hss : s.IsSemisimple := (absolutely_semisimple_iff s).mp hs
  have hsf : s = f := by
    apply c.ext
    intro i
    rw [hw]
    apply Module.End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil
      (Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr (hw i))) hDs hss.isFinitelySemisimple
    simpa only [he, add_sub_cancel_left] using hn
  exact hsf ▸ hss

/-- Coordinates of an endomorphism in an eigenbasis. -/
theorem repr_apply_of_eigenbasis {ι : Type*} (c : Basis ι ℂ V)
    (F : Module.End ℂ V) (eig : ι → ℂ) (h : ∀ i, F (c i) = eig i • c i)
    (x : V) (i : ι) : c.repr (F x) i = eig i * c.repr x i := by
  classical
  have heq : (c.coord i).comp F = eig i • c.coord i := by
    apply c.ext
    intro j
    by_cases hij : j = i
    · subst j; simp [h]
    · simp [h, hij, Ne.symm hij]
  exact congrArg (fun f : V →ₗ[ℂ] ℂ => f x) heq

/-- A nonzero eigenvector of an integer diagonal operator has integer eigenvalue. -/
theorem eigenvalue_eq_int_of_eigenbasis {ι : Type*}
    (c : Basis ι ℂ V) (F : Module.End ℂ V) (w : ι → ℤ)
    (h : ∀ i, F (c i) = (w i : ℂ) • c i) (β : ℂ) (x : V)
    (hx : x ≠ 0) (heig : F x = β • x) : ∃ z : ℤ, β = (z : ℂ) := by
  classical
  have hex : ∃ i, c.repr x i ≠ 0 := by
    by_contra hn
    simp only [not_exists, not_not] at hn
    apply hx
    apply c.repr.injective
    ext i
    simp only [hn, map_zero, Finsupp.zero_apply]
  obtain ⟨i, hi⟩ := hex
  refine ⟨w i, ?_⟩
  have he := congrArg (fun y : V => c.repr y i) heig
  rw [repr_apply_of_eigenbasis c F (fun i => (w i : ℂ)) h,
    map_smul, Finsupp.smul_apply, smul_eq_mul] at he
  exact (mul_right_cancel₀ hi he).symm

private theorem simultaneous_integer_basis {I : Type v} (F : I → Module.End ℂ V)
    (hc : ∀ i j, Commute (F i) (F j))
    (hs : ∀ j, (F j).IsSemisimple)
    (hint : ∀ j (μ : ℂ) x, x ≠ 0 → F j x = μ • x → ∃ z : ℤ, μ = (z : ℂ)) :
    ∃ n : ℕ, ∃ c : Basis (Fin n) ℂ V, ∃ w : Fin n → I → ℤ,
      ∀ i j, F j (c i) = (w i j : ℂ) • c i := by
  classical
  let A : (I → ℂ) → Submodule ℂ V := fun χ => ⨅ j, Module.End.eigenspace (F j) (χ j)
  have heq (j : I) (μ : ℂ) :
      Module.End.maxGenEigenspace (F j) μ = Module.End.eigenspace (F j) μ :=
    (hs j).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  have hmaps : ∀ i j μ, Set.MapsTo (F i)
      (Module.End.maxGenEigenspace (F j) μ) (Module.End.maxGenEigenspace (F j) μ) :=
    fun i j => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i)
  have hspan : iSup A = ⊤ := by
    simpa only [heq] using Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo
      F hmaps (fun j => Module.End.iSup_maxGenEigenspace_eq_top (F j))
  have hind : iSupIndep A := by
    simpa only [heq] using Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo F hmaps
  have hi : DirectSum.IsInternal A :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind hspan
  let cb := hi.collectedBasis (fun χ => Module.finBasis ℂ (A χ))
  let J := Σ χ : I → ℂ, Fin (Module.finrank ℂ (A χ))
  letI : Fintype J := cb.fintypeIndexOfRankLtAleph0 (Module.rank_lt_aleph0 ℂ V)
  let n := Fintype.card J
  let e : J ≃ Fin n := Fintype.equivFin J
  let c : Basis (Fin n) ℂ V := cb.reindex e
  have hmem (i : Fin n) (j : I) : c i ∈ Module.End.eigenspace (F j) ((e.symm i).1 j) := by
    have hm := hi.collectedBasis_mem (fun χ => Module.finBasis ℂ (A χ)) (e.symm i)
    have hm' : cb (e.symm i) ∈ A (e.symm i).1 := hm
    have hh := (show ∀ j, cb (e.symm i) ∈ Module.End.eigenspace (F j) ((e.symm i).1 j) from by simpa only [A, Submodule.mem_iInf] using hm') j
    simpa only [c, Basis.reindex_apply] using hh
  have hex (i : Fin n) (j : I) : ∃ z : ℤ, (e.symm i).1 j = (z : ℂ) :=
    hint j _ (c i) (c.ne_zero i) (Module.End.mem_eigenspace_iff.mp (hmem i j))
  choose w hw using hex
  refine ⟨n,c,w,?_⟩
  intro i j
  rw [← hw i j]
  exact Module.End.mem_eigenspace_iff.mp (hmem i j)

end SimultaneousWeights

section ProductWeights

open Specs.LieAlgebrasAndRepresentations.DiagonalEnlargementStep
variable {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Two diagonal operators with a common eigenbasis commute. -/
theorem commute_of_eigenbasis {ι : Type*} (c : Basis ι ℂ V)
    (F G : Module.End ℂ V) (f g : ι → ℂ)
    (hF : ∀ i, F (c i) = f i • c i) (hG : ∀ i, G (c i) = g i • c i) :
    Commute F G := by
  apply c.ext
  intro i
  change F (G (c i)) = G (F (c i))
  rw [hF, hG, map_smul, map_smul, hF, hG, smul_smul, smul_smul, mul_comm]

/-- Commuting integer diagonal actions have an integer joint eigenbasis. -/
theorem integer_weights_coprod {T : Type v} {U : Type w}
    [AddCommGroup T] [Module ℂ T] [AddCommGroup U] [Module ℂ U]
    {r m : ℕ} (bT : Basis (Fin r) ℂ T) (bU : Basis (Fin m) ℂ U)
    (ρ : T →ₗ[ℂ] Module.End ℂ V) (τ : U →ₗ[ℂ] Module.End ℂ V)
    (hρ : HasIntegerWeights bT ρ) (hτ : HasIntegerWeights bU τ)
    (hcross : ∀ i j, Commute (ρ (bT i)) (τ (bU j))) :
    HasIntegerWeights (bT.prod bU) (ρ.coprod τ) := by
  classical
  obtain ⟨nT, cT, wT, hcT⟩ := hρ
  obtain ⟨nU, cU, wU, hcU⟩ := hτ
  let F : Fin r ⊕ Fin m → Module.End ℂ V := Sum.elim (fun j => ρ (bT j)) (fun j => τ (bU j))
  have hcomm : ∀ i j, Commute (F i) (F j) := by
    intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact commute_of_eigenbasis cT _ _ (fun a => (wT a i : ℂ))
        (fun a => (wT a j : ℂ)) (fun a => hcT a i) (fun a => hcT a j)
    · exact hcross i j
    · exact (hcross j i).symm
    · exact commute_of_eigenbasis cU _ _ (fun a => (wU a i : ℂ))
        (fun a => (wU a j : ℂ)) (fun a => hcU a i) (fun a => hcU a j)
  have hsemisimple : ∀ j, (F j).IsSemisimple := by
    intro j
    rcases j with j | j
    · exact semisimple_of_eigenbasis cT _ (fun a => (wT a j : ℂ)) (fun a => hcT a j)
    · exact semisimple_of_eigenbasis cU _ (fun a => (wU a j : ℂ)) (fun a => hcU a j)
  have hint : ∀ j (μ : ℂ) x, x ≠ 0 → F j x = μ • x → ∃ z : ℤ, μ = (z : ℂ) := by
    intro j μ x hx he
    rcases j with j | j
    · exact eigenvalue_eq_int_of_eigenbasis cT _ (fun a => wT a j) (fun a => hcT a j) μ x hx he
    · exact eigenvalue_eq_int_of_eigenbasis cU _ (fun a => wU a j) (fun a => hcU a j) μ x hx he
  obtain ⟨n, c, weights, hc⟩ := simultaneous_integer_basis F hcomm hsemisimple hint
  refine ⟨n, c, weights, ?_⟩
  intro i j
  rcases j with j | j
  · simpa [F, Basis.prod_apply] using hc i (Sum.inl j)
  · simpa [F, Basis.prod_apply] using hc i (Sum.inr j)

end ProductWeights

section TorusBridges

open Specs.LieAlgebrasAndRepresentations.DiagonalEnlargementStep
attribute [local instance 100] LieRing.ofAssociativeRing
variable {B : Type u} [LieRing B] [LieAlgebra ℂ B]
theorem ad_commute_of_derivation_kills (d : B) (E : LieDerivation ℂ B B) (h : E d = 0) :
    Commute (LieDerivation.ad ℂ B d).toLinearMap E.toLinearMap := by
  apply LinearMap.ext
  intro x
  change -⁅E x,d⁆ = E (-⁅x,d⁆)
  rw [map_neg, E.apply_lie_eq_add, h, lie_zero, zero_add]

theorem integral_torus_commute (D : LieDerivation ℂ B B) (t : IntegralTorusData D)
    (E : LieDerivation ℂ B B) (h : Commute D.toLinearMap E.toLinearMap) (z : Torus t.rank) :
    Commute E.toLinearMap (t.action z).toLinearMap := by
  apply LinearMap.ext
  intro x
  have hz := congrArg (fun E : LieDerivation ℂ B B => E x) (t.centralizer E h z)
  change E (t.action z x) - t.action z (E x) = 0 at hz
  exact sub_eq_zero.mp hz
end TorusBridges

section GraphComplement

variable {k : Type u} [Field k]
variable {A : Type v} [LieRing A] [LieAlgebra k A]
variable {H : Type w} [LieRing H] [LieAlgebra k H]

/-- The graph formula and complement, in actual semidirect-product coordinates. -/
theorem graph_space_and_complement
    (θ : H →ₗ⁅k⁆ LieDerivation k A A) (χ : A →ₗ[k] k) (α : H)
    (I : LieIdeal k (A ⋊⁅θ⁆ H))
    (hI : ∀ z : A ⋊⁅θ⁆ H, z ∈ I ↔ z.right = -(χ z.left • α))
    (d : A) (hd : χ d = 1) :
    I.toSubmodule = (LinearMap.ker χ).map (LieAlgebra.SemiDirectSum.inl θ).toLinearMap ⊔
      Submodule.span k {(⟨d, -α⟩ : A ⋊⁅θ⁆ H)} ∧
    IsCompl I.toSubmodule (LieAlgebra.SemiDirectSum.inr θ).range.toSubmodule := by
  constructor
  · apply le_antisymm
    · intro z hz
      apply Submodule.mem_sup.mpr
      refine ⟨LieAlgebra.SemiDirectSum.inl θ (z.left - χ z.left • d), ?_,
        χ z.left • (⟨d, -α⟩ : A ⋊⁅θ⁆ H), ?_, ?_⟩
      · refine ⟨z.left - χ z.left • d, ?_, rfl⟩
        simp [LinearMap.mem_ker, hd]
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
      · have hzright := (hI z).mp hz
        apply LieAlgebra.SemiDirectSum.ext
        · change z.left - χ z.left • d + χ z.left • d = z.left
          abel
        · change 0 + χ z.left • -α = z.right
          simp only [zero_add, smul_neg]
          exact hzright.symm
    · apply sup_le
      · rintro _ ⟨x, hx, rfl⟩
        apply (hI _).mpr
        change 0 = -(χ x • α)
        have hx' : χ x = 0 := hx
        simp only [hx', zero_smul, neg_zero]
      · apply Submodule.span_le.mpr
        intro z hz
        have hz' : z = (⟨d, -α⟩ : A ⋊⁅θ⁆ H) := Set.mem_singleton_iff.mp hz
        rw [hz']
        apply (hI _).mpr
        change -α = -(χ d • α)
        simp only [hd, one_smul]
  · constructor
    · apply Submodule.disjoint_def.mpr
      intro z hz hz'
      obtain ⟨h, hh⟩ := hz'
      have hzleft : z.left = 0 := (congrArg LieAlgebra.SemiDirectSum.left hh).symm
      apply LieAlgebra.SemiDirectSum.ext
      · exact hzleft
      · change z.right = 0
        rw [(hI z).mp hz, hzleft, map_zero, zero_smul, neg_zero]
    · apply codisjoint_iff.mpr
      apply top_unique
      intro z _
      apply Submodule.mem_sup.mpr
      refine ⟨⟨z.left, -(χ z.left • α)⟩, (hI _).mpr rfl,
        LieAlgebra.SemiDirectSum.inr θ (z.right + χ z.left • α), ?_, ?_⟩
      · exact ⟨z.right + χ z.left • α, rfl⟩
      · apply LieAlgebra.SemiDirectSum.ext
        · change z.left + 0 = z.left
          exact add_zero _
        · change -(χ z.left • α) + (z.right + χ z.left • α) = z.right
          abel

end GraphComplement


section NilpotentGraph
variable {k : Type u} [Field k]
variable {A : Type v} [LieRing A] [LieAlgebra k A]
variable {H : Type w} [LieRing H] [LieAlgebra k H]
variable (θ : H →ₗ⁅k⁆ LieDerivation k A A)
variable (χ : A →ₗ[k] k) (α : H)
variable (I : LieIdeal k (A ⋊⁅θ⁆ H))
variable (hI : ∀ z : A ⋊⁅θ⁆ H, z ∈ I ↔ z.right = -(χ z.left • α))
include hI in
/-- The old ideal is the image under the graph's linear equivalence. -/
theorem graphIdealLift_eq_map (N : LieIdeal k A) (hχN : ∀ x ∈ N, χ x = 0)
    (hθN : ∀ h x, x ∈ N → θ h x ∈ N) :
    (graphIdealLift θ χ α I hI N hχN hθN).toSubmodule =
      N.toSubmodule.map (graphEquiv θ χ α I hI).toLinearMap := by
  ext x
  constructor
  · intro hx
    refine ⟨x.val.left, hx, ?_⟩
    apply Subtype.ext
    apply LieAlgebra.SemiDirectSum.ext
    · rfl
    · exact ((hI x.val).mp x.property).symm
  · rintro ⟨a, ha, rfl⟩
    exact ha

include hI in
theorem graphIdealLift_finrank (N : LieIdeal k A) (hχN : ∀ x ∈ N, χ x = 0)
    (hθN : ∀ h x, x ∈ N → θ h x ∈ N) :
    Module.finrank k (graphIdealLift θ χ α I hI N hχN hθN) = Module.finrank k N := by
  change Module.finrank k (graphIdealLift θ χ α I hI N hχN hθN).toSubmodule = _
  rw [graphIdealLift_eq_map θ χ α I hI N hχN hθN]
  exact (graphEquiv θ χ α I hI).finrank_map_eq N.toSubmodule

include hI in
/-- A new nilpotent-adjoint direction adjoined to the old nilpotent ideal
is nilpotent inside the solvable replacement. -/
theorem graphSumIdeal_nilpotent [CharZero k] [FiniteDimensional k A]
    [LieAlgebra.IsSolvable I]
    (N : LieIdeal k A) (hχN : ∀ x ∈ N, χ x = 0)
    (hθN : ∀ h x, x ∈ N → θ h x ∈ N) [LieRing.IsNilpotent N]
    (y : I) (hbr : ∀ a b : A, ⁅a, b⁆ ∈ N) (hθall : ∀ h a, θ h a ∈ N)
    (hy : IsNilpotent (LieAlgebra.ad k I y)) :
    LieRing.IsNilpotent (graphSumIdeal θ χ α I hI N hχN hθN y hbr hθall) := by
  haveI : FiniteDimensional k I := (graphEquiv θ χ α I hI).finiteDimensional
  have hN := graphIdealLift_nilpotent θ χ α I hI N hχN hθN
  exact nilpotent_ideal_plus_line k I _ y
    (graphSumIdeal θ χ α I hI N hχN hθN y hbr hθall).toLieSubalgebra hN hy rfl

include hI in
theorem graph_nilradical_dimension_drop [CharZero k] [FiniteDimensional k A]
    [LieAlgebra.IsSolvable I]
    (N : LieIdeal k A) (hχN : ∀ x ∈ N, χ x = 0)
    (hθN : ∀ h x, x ∈ N → θ h x ∈ N) [LieRing.IsNilpotent N]
    (d : A) (hd : χ d = 1) (hdN : d ∉ N)
    (hbr : ∀ a b : A, ⁅a, b⁆ ∈ N) (hθall : ∀ h a, θ h a ∈ N)
    (hy : IsNilpotent (LieAlgebra.ad k I (graphVector θ χ α I hI d hd))) :
    Module.finrank k (I ⧸ nilradical k I) < Module.finrank k (A ⧸ N) := by
  let y := graphVector θ χ α I hI d hd
  let P := graphIdealLift θ χ α I hI N hχN hθN
  let M := graphSumIdeal θ χ α I hI N hχN hθN y hbr hθall
  haveI : FiniteDimensional k I := (graphEquiv θ χ α I hI).finiteDimensional
  have hM : LieRing.IsNilpotent M :=
    graphSumIdeal_nilpotent θ χ α I hI N hχN hθN y hbr hθall hy
  have hle : P.toSubmodule ⊔ Submodule.span k {y} ≤ (nilradical k I).toSubmodule :=
    nilpotent_ideal_le_nilradical M hM
  have hyP : y ∉ P.toSubmodule := hdN
  exact quotient_dimension_drop k A I N.toSubmodule P.toSubmodule
    (nilradical k I).toSubmodule y (graphEquiv θ χ α I hI).finrank_eq.symm
    (graphIdealLift_finrank θ χ α I hI N hχN hθN) hyP hle

include hI in
theorem graphSumIdeal_direct (N : LieIdeal k A) (hχN : ∀ x ∈ N, χ x = 0)
    (hθN : ∀ h x, x ∈ N → θ h x ∈ N)
    (d : A) (hd : χ d = 1) (hdN : d ∉ N) :
    Disjoint ((graphIdealLift θ χ α I hI N hχN hθN).toSubmodule.map I.incl.toLinearMap)
      (Submodule.span k {(graphVector θ χ α I hI d hd).val}) := by
  apply Submodule.disjoint_span_singleton_of_notMem
  rintro ⟨x, hx, heq⟩
  have hh : x.val.left = d := congrArg LieAlgebra.SemiDirectSum.left heq
  exact hdN (hh ▸ hx)


end NilpotentGraph

section Setup

open Specs.LieAlgebrasAndRepresentations
open Specs.LieAlgebrasAndRepresentations.DiagonalEnlargementStep
attribute [local instance 100] LieRing.ofAssociativeRing
variable {S : Type uS} {T : Type uT} {B : Type uB}
    [LieRing S] [LieAlgebra ℂ S] [FiniteDimensional ℂ S]
    [LieRing T] [LieAlgebra ℂ T] [FiniteDimensional ℂ T] [IsLieAbelian T]
    [LieRing B] [LieAlgebra ℂ B] [FiniteDimensional ℂ B] [LieAlgebra.IsSolvable B]

/-- The spectral and character setup, before constructing the graph ideal. -/
structure EnlargementSetup (θ : (S × T) →ₗ⁅ℂ⁆ LieDerivation ℂ B B)
    {r : ℕ} (bT : Basis (Fin r) ℂ T) where
  d : B
  fixed : ∀ x : S × T, θ x d = 0
  outside_nilradical : d ∉ Nilradical.nilradical_value ℂ B
  character : B →ₗ[ℂ] ℂ
  character_d : character d = 1
  character_nilradical : ∀ x ∈ Nilradical.nilradical_value ℂ B, character x = 0
  character_bracket : ∀ x y : B, character ⁅x,y⁆ = 0
  character_derivation : ∀ (E : LieDerivation ℂ B B) (x : B), character (E x) = 0
  torus : IntegralTorusData (LieDerivation.ad ℂ B d)
  commutes : ∀ x z, ⁅θ x, torus.action z⁆ = 0
  kills_d : ∀ z, torus.action z d = 0
  extendedAction : ((S × T) × Torus torus.rank) →ₗ⁅ℂ⁆ LieDerivation ℂ B B
  extends_old : ∀ x, extendedAction (x,0) = θ x
  extends_torus : ∀ z, extendedAction (0,z) = torus.action z
  fixed_extended : ∀ x, extendedAction x d = 0
  nilpotent_difference : IsNilpotent
    (LieAlgebra.ad ℂ B d - (extendedAction (0, torusElement torus)).toLinearMap)
  integer_weights : HasIntegerWeights (bT.prod (Pi.basisFun ℂ (Fin torus.rank)))
    (enlargedCenterAction extendedAction)

/-- Choose the invariant vector and character, then adjoin its spectral torus. -/
theorem exists_enlargement_setup (θ : (S × T) →ₗ⁅ℂ⁆ LieDerivation ℂ B B)
    {r : ℕ} (bT : Basis (Fin r) ℂ T)
    (hS : SolvableRadical.IsSemisimple_value ℂ S)
    (hw : HasIntegerWeights bT (centerAction θ))
    (hq : 0 < Module.finrank ℂ (B ⧸ Nilradical.nilradical_value ℂ B)) :
    Nonempty (EnlargementSetup θ bT) := by
  classical
  obtain ⟨d,hfixed,hd⟩ := fixed_vector S T B θ r bT hS hw hq
  obtain ⟨χ,hχd,hχN,hχbr,hχDer⟩ := normalized_character ℂ B d hd
  obtain ⟨t⟩ := exists_integral_torus (LieDerivation.ad ℂ B d)
  have hcomm (x : S × T) (z : Torus t.rank) : ⁅θ x,t.action z⁆ = 0 :=
    t.centralizer (θ x) (commute_ad_of_fixed θ d hfixed x) z
  let Θ := productAction θ t.action hcomm
  have hΘold (x : S × T) : Θ (x,0) = θ x := by
    change θ x + t.action 0 = θ x
    simp
  have hΘtorus (z : Torus t.rank) : Θ (0,z) = t.action z := by
    change θ 0 + t.action z = t.action z
    simp
  have hDd : (LieDerivation.ad ℂ B d) d = 0 := by
    change -⁅d,d⁆ = 0
    simp
  have htd (z : Torus t.rank) : t.action z d = 0 := t.kills_kernel d hDd z
  have hΘd (x : (S × T) × Torus t.rank) : Θ x d = 0 := by
    change θ x.1 d + t.action x.2 d = 0
    rw [hfixed, htd, add_zero]
  have hn : IsNilpotent (LieAlgebra.ad ℂ B d - (Θ (0,torusElement t)).toLinearMap) := by
    obtain ⟨N,he,hc,hs,hn⟩ := t.jordan
    rw [hΘtorus]
    have hn' : IsNilpotent ((LieDerivation.ad ℂ B d).toLinearMap -
        (t.action (torusElement t)).toLinearMap) := by
      have he' : (LieDerivation.ad ℂ B d).toLinearMap -
          (t.action (torusElement t)).toLinearMap = N :=
        sub_eq_iff_eq_add.mpr (he.trans (add_comm _ _))
      exact he'.symm ▸ hn
    simpa only [LieDerivation.coe_ad_apply_eq_ad_apply] using hn'
  let τ : Torus t.rank →ₗ[ℂ] Module.End ℂ B :=
    ((LieDerivation.toLinearMapLieHom ℂ B).comp t.action).toLinearMap
  have hwτ : HasIntegerWeights (Pi.basisFun ℂ (Fin t.rank)) τ :=
    integral_torus_has_integer_weights (LieDerivation.ad ℂ B d) t
  have hcross (i : Fin r) (j : Fin t.rank) :
      Commute (centerAction θ (bT i)) (τ (Pi.basisFun ℂ (Fin t.rank) j)) := by
    change Commute (θ (0,bT i)).toLinearMap
      (t.action (Pi.basisFun ℂ (Fin t.rank) j)).toLinearMap
    exact integral_torus_commute (LieDerivation.ad ℂ B d) t (θ (0,bT i))
      (commute_ad_of_fixed θ d hfixed (0,bT i)) _
  have hwjoint := integer_weights_coprod bT (Pi.basisFun ℂ (Fin t.rank))
    (centerAction θ) τ hw hwτ hcross
  have hext : enlargedCenterAction Θ = (centerAction θ).coprod τ := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    rfl
  refine ⟨{
    d := d
    fixed := hfixed
    outside_nilradical := hd
    character := χ
    character_d := hχd
    character_nilradical := hχN
    character_bracket := hχbr
    character_derivation := hχDer
    torus := t
    commutes := hcomm
    kills_d := htd
    extendedAction := Θ
    extends_old := hΘold
    extends_torus := hΘtorus
    fixed_extended := hΘd
    nilpotent_difference := hn
    integer_weights := hext.symm ▸ hwjoint
  }⟩


end Setup


section Enlargement

open Specs.LieAlgebrasAndRepresentations
open Specs.LieAlgebrasAndRepresentations.DiagonalEnlargementStep
attribute [local instance 100] LieRing.ofAssociativeRing

/-- The diagonal enlargement decreases the dimension of the nilradical quotient. -/
theorem enlargement_step : enlargement_step_type := by
  intro S T B _ _ _ _ _ _ _ _ _ _ _ θ r bT hS hw hq
  classical
  obtain ⟨e⟩ := exists_enlargement_setup θ bT hS hw hq
  let Θ := e.extendedAction
  let χ := e.character
  let α : (S × T) × Torus e.torus.rank := (0, torusElement e.torus)
  have hcentral : ∀ h : (S × T) × Torus e.torus.rank, ⁅h, α⁆ = 0 := by
    rintro ⟨h, z⟩
    ext <;> simp [α, Ring.lie_def, mul_comm]
  have hχact : ∀ h x, χ (Θ h x) = 0 := fun h x => e.character_derivation (Θ h) x
  obtain ⟨I, hI⟩ := graph_ideal ℂ B ((S × T) × Torus e.torus.rank)
    Θ χ α hcentral e.character_bracket hχact
  letI : LieAlgebra.IsSolvable I := graph_solvable Θ χ α I hI
  let N := nilradical ℂ B
  letI : LieRing.IsNilpotent N := nilradical_nilpotent ℂ B
  have hχN : ∀ x ∈ N, χ x = 0 := e.character_nilradical
  have hθall : ∀ h x, Θ h x ∈ N := fun h x => derivation_image ℂ B (Θ h) x
  have hθN : ∀ h x, x ∈ N → Θ h x ∈ N := fun h x _ => hθall h x
  have hbr : ∀ a b : B, ⁅a, b⁆ ∈ N := by
    intro a b
    have he : (LieDerivation.ad ℂ B a) b = ⁅a, b⁆ := by
      change -⁅b, a⁆ = ⁅a, b⁆
      exact lie_skew a b
    exact he ▸ derivation_image ℂ B (LieDerivation.ad ℂ B a) b
  let y := graphVector Θ χ α I hI e.d e.character_d
  have hyval : y.val = tiltedVector Θ e.d (torusElement e.torus) := by
    apply LieAlgebra.SemiDirectSum.ext
    · rfl
    · change -(0, torusElement e.torus) = (0, -torusElement e.torus)
      simp
  have hyad : IsNilpotent (LieAlgebra.ad ℂ I y) :=
    graph_ad_nilpotent Θ χ α I hI e.d e.character_d
      (e.fixed_extended α) e.nilpotent_difference
  let M := graphSumIdeal Θ χ α I hI N hχN hθN y hbr hθall
  have hMnil : LieRing.IsNilpotent M :=
    graphSumIdeal_nilpotent Θ χ α I hI N hχN hθN y hbr hθall hyad
  have hMspace : M.toSubmodule.map I.incl.toLinearMap =
      N.toSubmodule.map (LieAlgebra.SemiDirectSum.inl Θ).toLinearMap ⊔
        Submodule.span ℂ {tiltedVector Θ e.d (torusElement e.torus)} := by
    rw [← hyval]
    exact graphSumIdeal_space Θ χ α I hI N hχN hθN y hbr hθall
  have hdir : Disjoint (N.toSubmodule.map (LieAlgebra.SemiDirectSum.inl Θ).toLinearMap)
      (Submodule.span ℂ {tiltedVector Θ e.d (torusElement e.torus)}) := by
    rw [← hyval]
    rw [← graphIdealLift_space Θ χ α I hI N hχN hθN]
    exact graphSumIdeal_direct Θ χ α I hI N hχN hθN e.d e.character_d e.outside_nilradical
  obtain ⟨hspace, hcompl⟩ := graph_space_and_complement Θ χ α I hI e.d e.character_d
  have hspace' : I.toSubmodule = (LinearMap.ker χ).map
      (LieAlgebra.SemiDirectSum.inl Θ).toLinearMap ⊔
        Submodule.span ℂ {tiltedVector Θ e.d (torusElement e.torus)} := by
    rw [← hyval]
    exact hspace
  have hweights : HasIntegerWeights (bT.prod (Pi.basisFun ℂ (Fin e.torus.rank)))
      (enlargedCenterAction (graphAction Θ I)) := by
    apply integer_weights_transport _ (enlargedCenterAction Θ) _
      (graphEquiv Θ χ α I hI) _ e.integer_weights
    intro t x
    change graphAction Θ I ((0, t.1), t.2) (graphEquiv Θ χ α I hI x) =
      graphEquiv Θ χ α I hI (Θ ((0, t.1), t.2) x)
    exact graphEquiv_equivariant Θ χ α I hI hcentral hχact (graphAction Θ I)
      (fun _ _ => rfl) _ _
  refine ⟨{
    d := e.d
    fixed := e.fixed
    outside_nilradical := e.outside_nilradical
    character := χ
    character_d := e.character_d
    character_nilradical := hχN
    character_bracket := e.character_bracket
    torus := e.torus
    extendedAction := Θ
    extends_old := e.extends_old
    extends_torus := e.extends_torus
    replacement := I
    replacement_space := hspace'
    replacement_solvable := inferInstance
    complement := hcompl
    newAction := graphAction Θ I
    splitting := graphSplitting Θ χ α I hI
    splitting_apply := fun _ _ => rfl
    oldEmbedding := semidirectEmbedding θ Θ e.extends_old
    oldEmbedding_apply := fun _ => rfl
    oldEmbedding_injective := semidirectEmbedding_injective θ Θ e.extends_old
    nilpotentSum := M
    nilpotentSum_space := hMspace
    nilpotentSum_nilpotent := hMnil
    nilpotentSum_direct := hdir
    integer_weights := hweights
    dimension_drop := graph_nilradical_dimension_drop Θ χ α I hI N hχN hθN
      e.d e.character_d e.outside_nilradical hbr hθall hyad
  }⟩


end Enlargement

end LieAlgebrasAndRepresentations.DiagonalEnlargementStep
