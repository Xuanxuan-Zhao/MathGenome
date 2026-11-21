import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.AbstractJordan
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.Engel
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.KillingCriterion
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.MaximalTori
import Mathlib.Algebra.Lie.CartanExists
import Mathlib.Algebra.Lie.Weights.Killing

universe u
namespace LieAlgebrasAndRepresentations

attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

def IsToral (H : LieSubalgebra ℂ L) : Prop :=
  Specs.LieAlgebrasAndRepresentations.MaximalTori.IsToral_value H

def IsMaximalToral (H : LieSubalgebra ℂ L) : Prop :=
  Maximal IsToral H

def toralCentralizer (H : LieSubalgebra ℂ L) : LieSubalgebra ℂ L :=
  Specs.LieAlgebrasAndRepresentations.MaximalTori.toralCentralizer_value H

@[simp] theorem mem_toralCentralizer (H : LieSubalgebra ℂ L) (x : L) :
    x ∈ toralCentralizer H ↔ ∀ h : H, ⁅(h : L), x⁆ = 0 := Iff.rfl

private theorem toral_lie {H : LieSubalgebra ℂ L} (hH : IsToral H) (x y : H) :
    ⁅(x : L), (y : L)⁆ = 0 := by
  letI := hH.1
  exact congrArg Subtype.val (trivial_lie_zero H H x y)

theorem toral_bot (L : Type u) [LieRing L] [LieAlgebra ℂ L] :
    IsToral (⊥ : LieSubalgebra ℂ L) := by
  refine ⟨⟨fun x y => Subtype.ext (by
    change ⁅(x : L), (y : L)⁆ = 0
    rw [show (x : L) = 0 from x.property, zero_lie])⟩, fun x => ?_⟩
  have hx : (x : L) = 0 := x.property
  rw [hx, map_zero]
  exact Module.End.isSemisimple_zero

private theorem toral_le_centralizer {H : LieSubalgebra ℂ L} (hH : IsToral H) :
    H ≤ toralCentralizer H := by
  intro x hx h
  exact toral_lie hH h ⟨x, hx⟩

private theorem cartan_toral [FiniteDimensional ℂ L] [LieAlgebra.IsKilling ℂ L]
    (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] : IsToral H :=
  ⟨inferInstance, fun x =>
    LieAlgebra.IsKilling.isSemisimple_ad_of_mem_isCartanSubalgebra (K := ℂ) (L := L)
      (H := H) x.property⟩

private theorem cartan_centralizer (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (hH : IsToral H) : toralCentralizer H = H := by
  refine le_antisymm ?_ (toral_le_centralizer hH)
  intro x hx
  have hn : x ∈ H.normalizer := (H.mem_normalizer_iff x).mpr fun y hy => by
    rw [← lie_skew x y, hx ⟨y, hy⟩, neg_zero]
    exact H.zero_mem
  rwa [LieSubalgebra.IsCartanSubalgebra.self_normalizing] at hn

private theorem self_centralizing_maximal (H : LieSubalgebra ℂ L)
    (hH : IsToral H) (hc : toralCentralizer H = H) : IsMaximalToral H := by
  refine ⟨hH, ?_⟩
  intro K hK hHK x hx
  rw [← hc]
  intro h
  exact toral_lie hK ⟨h, hHK h.property⟩ ⟨x, hx⟩

theorem exists_maximal_toral (L : Type u) [LieRing L] [LieAlgebra ℂ L]
    [FiniteDimensional ℂ L] (hss : IsSemisimple ℂ L) :
    ∃ H : LieSubalgebra ℂ L, IsMaximalToral H := by
  haveI : LieAlgebra.HasTrivialRadical ℂ L := ⟨hss⟩
  obtain ⟨x, hx⟩ := LieAlgebra.exists_isCartanSubalgebra_engel (K := ℂ) (L := L)
  letI := hx
  let H := LieSubalgebra.engel ℂ x
  have ht : IsToral H := cartan_toral H
  exact ⟨H, self_centralizing_maximal H ht (cartan_centralizer H ht)⟩

/-- Adding a commuting semisimple element to a torus still gives a torus. -/
private theorem semisimple_mem_of_maximal_toral [FiniteDimensional ℂ L]
    {H : LieSubalgebra ℂ L} (hH : IsMaximalToral H) {s : L}
    (hs : (LieAlgebra.ad ℂ L s).IsSemisimple)
    (hc : s ∈ toralCentralizer H) : s ∈ H := by
  let W : Submodule ℂ L := H.toSubmodule ⊔ Submodule.span ℂ {s}
  have hw (x : L) (hx : x ∈ W) : ∃ h : H, ∃ a : ℂ, x = (h : L) + a • s := by
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    exact ⟨⟨y, hy⟩, a, rfl⟩
  have hbr (x y : L) (hx : x ∈ W) (hy : y ∈ W) : ⁅x, y⁆ = 0 := by
    obtain ⟨h, a, rfl⟩ := hw x hx
    obtain ⟨k, b, rfl⟩ := hw y hy
    have hh := toral_lie hH.1 h k
    have hk : ⁅s, (k : L)⁆ = 0 := by rw [← lie_skew s (k : L), hc k, neg_zero]
    simp [add_lie, lie_add, smul_lie, lie_smul, hh, hc h, hk]
  let K : LieSubalgebra ℂ L :=
    { toSubmodule := W
      lie_mem' := fun {x y} hx hy => by rw [hbr x y hx hy]; exact W.zero_mem }
  have hK : IsToral K := by
    refine ⟨⟨fun x y => Subtype.ext (hbr x y x.property y.property)⟩, ?_⟩
    intro x
    obtain ⟨h, a, he⟩ := hw x x.property
    change (LieAlgebra.ad ℂ L (x : L)).IsSemisimple
    rw [he, map_add, map_smul]
    apply Module.End.IsSemisimple.add_of_commute
    · rw [commute_iff_lie_eq, lie_smul, ← LieHom.map_lie, hc h, map_zero, smul_zero]
    · exact hH.1.2 h
    · exact Module.End.IsSemisimple_smul _ hs
  have hHK : H ≤ K := fun _ hx => Submodule.mem_sup_left hx
  have hKH : K ≤ H := hH.2 hK hHK
  exact hKH (Submodule.mem_sup_right (Submodule.mem_span_singleton_self s))

/-- A torus has no generalized zero weights beyond its actual centralizer. -/
private theorem zeroRoot_eq_centralizer [FiniteDimensional ℂ L]
    (H : LieSubalgebra ℂ L) (hH : IsToral H) :
    letI : IsLieAbelian H := hH.1
    LieAlgebra.zeroRootSubalgebra ℂ L H = toralCentralizer H := by
  letI : IsLieAbelian H := hH.1
  ext x
  constructor
  · intro hx h
    have hh : x ∈ (LieAlgebra.ad ℂ L (h : L)).maxGenEigenspace 0 :=
      LieModule.genWeightSpace_le_genWeightSpaceOf L h 0 hx
    rw [(hH.2 h).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at hh
    simpa only [Module.End.mem_eigenspace_iff, LieAlgebra.ad_apply, zero_smul] using hh
  · intro hx
    apply (LieAlgebra.mem_zeroRootSubalgebra ℂ L H x).mpr
    intro h
    exact ⟨1, by simpa using hx h⟩

/-- The centralizer of a maximal torus is Cartan: Jordan parts and Engel
show nilpotence, while the zero-root subalgebra is self-normalizing. -/
private theorem maximal_toral_centralizer_cartan [FiniteDimensional ℂ L]
    (hss : IsSemisimple ℂ L) (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H) :
    (toralCentralizer H).IsCartanSubalgebra := by
  letI : IsLieAbelian H := hH.1.1
  let C := toralCentralizer H
  have hHC : H ≤ C := toral_le_centralizer hH.1
  have hn : LieRing.IsNilpotent C := (engel_criterion ℂ C).mpr fun x => by
    obtain ⟨s, n, hd, _⟩ := abstract_jordan_decomposition ℂ L hss (x : L)
    have hsC : s ∈ C := by
      intro h
      have hx : ⁅(x : L), (h : L)⁆ = 0 := by
        rw [← lie_skew (x : L) (h : L), x.property h, neg_zero]
      have hh := (abstract_jordan_centralizer ℂ L hss (x : L) s n hd h hx).1
      rw [← lie_skew (h : L) s, hh, neg_zero]
    have hsH : s ∈ H := semisimple_mem_of_maximal_toral hH
      ((absolutely_semisimple_iff (LieAlgebra.ad ℂ L s)).mp hd.2.2.1) hsC
    have hnC : n ∈ C := by
      have hn : n = (x : L) - s := by rw [hd.1, add_sub_cancel_left]
      rw [hn]
      exact C.sub_mem x.property hsC
    have hnmap : IsNilpotent ((LieAlgebra.ad ℂ L n).restrict
        (fun y hy => C.lie_mem hnC hy)) :=
      Module.End.isNilpotent.restrict _ hd.2.2.2
    have heq : LieAlgebra.ad ℂ C x = (LieAlgebra.ad ℂ L n).restrict
        (fun y hy => C.lie_mem hnC hy) := by
      ext y
      change ⁅(x : L), (y : L)⁆ = ⁅n, (y : L)⁆
      have hh : ⁅s, (y : L)⁆ = 0 := y.property ⟨s, hsH⟩
      rw [hd.1, add_lie, hh, zero_add]
    rw [heq]
    exact hnmap
  haveI := hn
  refine ⟨hn, ?_⟩
  have he := zeroRoot_eq_centralizer H hH.1
  rw [← he]
  exact LieAlgebra.zeroRootSubalgebra_normalizer_eq_self ℂ L H

theorem maximal_toral_centralizer [FiniteDimensional ℂ L]
    (hss : IsSemisimple ℂ L) (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H) :
    toralCentralizer H = H := by
  haveI : LieAlgebra.HasTrivialRadical ℂ L := ⟨hss⟩
  haveI := maximal_toral_centralizer_cartan hss H hH
  exact le_antisymm (hH.2 (cartan_toral (toralCentralizer H))
    (toral_le_centralizer hH.1)) (toral_le_centralizer hH.1)

theorem maximal_toral_ne_bot [FiniteDimensional ℂ L] [Nontrivial L]
    (hss : IsSemisimple ℂ L) (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H) :
    H ≠ ⊥ := by
  intro he
  obtain ⟨x, hx⟩ := exists_ne (0 : L)
  have hm : x ∈ toralCentralizer H := by
    rw [he]
    intro h
    rw [show (h : L) = 0 from h.property, zero_lie]
  rw [maximal_toral_centralizer hss H hH, he] at hm
  exact hx hm

theorem zero_algebra_toral (L : Type u) [LieRing L] [LieAlgebra ℂ L] [Subsingleton L] :
    IsMaximalToral (⊥ : LieSubalgebra ℂ L) ∧
      toralCentralizer (⊥ : LieSubalgebra ℂ L) = ⊥ := by
  refine ⟨⟨toral_bot L, ?_⟩, ?_⟩
  · intro K _ _ x _
    exact Subsingleton.elim x 0
  · apply le_antisymm _ bot_le
    intro x _
    exact Subsingleton.elim x 0

private theorem toral_genWeightSpace_eq_weightSpace [FiniteDimensional ℂ L]
    (H : LieSubalgebra ℂ L) (hH : IsToral H) :
    letI : IsLieAbelian H := hH.1
    ∀ χ : H → ℂ, LieModule.genWeightSpace L χ = LieModule.weightSpace L χ := by
  letI : IsLieAbelian H := hH.1
  intro χ
  refine le_antisymm ?_ (LieModule.weightSpace_le_genWeightSpace L χ)
  intro v hv
  apply (LieModule.mem_weightSpace χ v).mpr
  intro h
  have hv' : v ∈ (LieAlgebra.ad ℂ L (h : L)).maxGenEigenspace (χ h) :=
    LieModule.genWeightSpace_le_genWeightSpaceOf L h χ hv
  rw [(hH.2 h).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at hv'
  exact Module.End.mem_eigenspace_iff.mp hv'

/-- Collect bases of the joint eigenspaces, then reindex by a finite interval. -/
theorem toral_simultaneously_diagonalizable [FiniteDimensional ℂ L]
    (H : LieSubalgebra ℂ L) (hH : IsToral H) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ L),
      ∀ (h : H) (i : Fin n), ∃ a : ℂ, ⁅(h : L), b i⁆ = a • b i := by
  classical
  letI : IsLieAbelian H := hH.1
  let W (χ : H → ℂ) := (LieModule.weightSpace L χ).toSubmodule
  have he := toral_genWeightSpace_eq_weightSpace H hH
  have hsup : (⨆ χ, W χ) = ⊤ := by
    apply LieSubmodule.iSup_toSubmodule_eq_top.mpr
    simpa only [he] using LieModule.iSup_genWeightSpace_eq_top ℂ H L
  have hind : iSupIndep W := by
    apply LieSubmodule.iSupIndep_toSubmodule.mpr
    simpa only [he] using LieModule.iSupIndep_genWeightSpace ℂ H L
  have hd := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind hsup
  let B := hd.collectedBasis fun χ => Module.Basis.ofVectorSpace ℂ (W χ)
  let I := Σ χ : H → ℂ, Module.Basis.ofVectorSpaceIndex ℂ (W χ)
  letI : Fintype I := FiniteDimensional.fintypeBasisIndex B
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  refine ⟨Fintype.card I, B.reindex e, fun h i => ?_⟩
  refine ⟨(e.symm i).1 h, ?_⟩
  have hb : B (e.symm i) ∈ LieModule.weightSpace L (e.symm i).1 :=
    hd.collectedBasis_mem _ (e.symm i)
  simpa only [Module.Basis.reindex_apply, LieSubalgebra.coe_bracket_of_module] using (LieModule.mem_weightSpace _ _).mp hb h

end LieAlgebrasAndRepresentations
