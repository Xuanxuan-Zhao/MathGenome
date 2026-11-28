import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Invariants.ReductiveFiniteGeneration
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Invariants.CanonicalProjection
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Invariants.FilteredReynolds
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Invariants.TorusProjection
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.CompleteReducibility
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite LinearAlgebraicGroups
open LinearAlgebraicGroups.Specs.GeometricRadicals (IsReductive IsSplitTorus)
open LinearAlgebraicGroups.RationalRepresentations (IsSemisimple invariants)
open scoped TensorProduct

universe u

namespace RepTheorySurvey.Invariants

open RationalActionComparison (KPoints HasRegularOrbits)

noncomputable section

set_option linter.style.haveILetI false

open private kernel_isSubcomodule from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.CompleteReducibility
open private Deviations.stable_inf RationalRepresentation.stable_iff from
  MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Invariants.CanonicalProjection

private theorem independent_cons {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
    {n : ℕ} (U : Submodule k V) (S : Fin n → Submodule k V)
    (hS : iSupIndep S) (hd : Disjoint U (⨆ i, S i)) : iSupIndep (Fin.cons U S) := by
  rw [iSupIndep_def]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · apply hd.mono_right
    refine iSup_le (fun j => iSup_le (fun hj => ?_))
    revert hj
    refine Fin.cases (fun h => (h rfl).elim) (fun j _ => ?_) j
    exact le_iSup S j
  · change Disjoint (S j) _
    let B := ⨆ (i) (_ : i ≠ j), S i
    have hB : B ≤ ⨆ i, S i := iSup_le fun i => iSup_le fun _ => le_iSup S i
    have hSB : S j ⊔ B ≤ ⨆ i, S i := sup_le (le_iSup S j) hB
    have hh := (hS j).disjoint_sup_right_of_disjoint_sup_left ((hd.mono_right hSB).symm)
    apply hh.mono_right
    refine iSup_le (fun i => iSup_le (fun hi => ?_))
    revert hi
    refine Fin.cases (fun _ => le_sup_right) (fun i hi => ?_) i
    exact (le_iSup₂ (f := fun i (_ : i ≠ j) => S i) i
      (fun h => hi (congrArg Fin.succ h))).trans le_sup_left

/-- Splittings of subcomodule inclusions yield an internal sum of simple comodules. -/
private theorem simple_sum_of_retractions {k V : Type u} [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {H : HopfAlgebraCategory k} (ρ : RightComodule k H V) (h : IsSemisimple H ρ) :
    ∃ (n : ℕ) (S : Fin n → Submodule k V),
      (∀ i, Specs.rationalIsSimpleSubcomodule ρ (S i)) ∧ DirectSum.IsInternal S := by
  classical
  let r (S T : Submodule k V) := Module.finrank k S < Module.finrank k T
  have hw : WellFounded r := (measure (fun S : Submodule k V => Module.finrank k S)).wf
  have decompose (W : Submodule k V) (hW : ρ.IsSubcomodule W) :
      ∃ (n : ℕ) (S : Fin n → Submodule k V),
        (∀ i, Specs.rationalIsSimpleSubcomodule ρ (S i)) ∧
          iSupIndep S ∧ (⨆ i, S i) = W := by
    induction W using hw.induction with
    | h W ih =>
      by_cases hW₀ : W = ⊥
      · subst W
        exact ⟨0, Fin.elim0, (fun i => Fin.elim0 i), iSupIndep_subsingleton _, iSup_of_empty _⟩
      let candidates := {U : Submodule k V | U ≤ W ∧ ρ.IsSubcomodule U ∧ U ≠ ⊥}
      obtain ⟨U, ⟨hUW, hU, hU₀⟩, hmin⟩ :=
        hw.has_min candidates ⟨W, le_rfl, hW, hW₀⟩
      have hs : Specs.rationalIsSimpleSubcomodule ρ U := by
        refine ⟨hU, hU₀, fun B hBU hB => ?_⟩
        by_cases hB₀ : B = ⊥
        · exact Or.inl hB₀
        · right
          exact eq_of_le_of_not_lt hBU (fun hlt =>
            hmin B ⟨hBU.trans hUW, hB, hB₀⟩ (Submodule.finrank_lt_finrank_of_lt hlt))
      obtain ⟨σ, hσ⟩ := (RightComodule.isSubcomodule_iff_exists_coaction ρ U).mp hU
      obtain ⟨p, hp, hpU⟩ := h U σ hσ
      let C := LinearMap.ker p
      have hC : ρ.IsSubcomodule C := kernel_isSubcomodule ρ σ p hp
      have hI : ρ.IsSubcomodule (W ⊓ C) :=
        (RationalRepresentation.stable_iff ρ _).mp (Deviations.stable_inf
          ((RationalRepresentation.stable_iff ρ W).mpr hW)
          ((RationalRepresentation.stable_iff ρ C).mpr hC))
      have hcomp : IsCompl U C := LinearMap.isCompl_of_proj (DFunLike.congr_fun hpU)
      have hlt : W ⊓ C < W := by
        refine lt_of_le_of_ne inf_le_left (fun hEq => hU₀ ?_)
        have hWC : W ≤ C := hEq ▸ inf_le_right
        have hD := (hcomp.disjoint.mono_right hWC).eq_bot
        rwa [inf_eq_left.mpr hUW] at hD
      obtain ⟨n, S, hSimple, hInd, hSum⟩ :=
        ih (W ⊓ C) (Submodule.finrank_lt_finrank_of_lt hlt) hI
      have hd : Disjoint U (⨆ i, S i) := by
        rw [hSum]
        exact hcomp.disjoint.mono_right inf_le_right
      let T : Fin (n + 1) → Submodule k V := Fin.cons U S
      have hT : (⨆ i, T i) = U ⊔ ⨆ i, S i := by
        apply le_antisymm
        · apply iSup_le
          exact Fin.cases le_sup_left (fun i => (le_iSup S i).trans le_sup_right)
        · exact sup_le (le_iSup T 0) (iSup_le (fun i => le_iSup T i.succ))
      refine ⟨n + 1, T, Fin.cases hs hSimple, independent_cons U S hInd hd, ?_⟩
      rw [hT, hSum, inf_comm W C, ← sup_inf_assoc_of_le C hUW, hcomp.sup_eq_top, top_inf_eq]
  have htop : ρ.IsSubcomodule ⊤ :=
    (RationalRepresentation.stable_iff ρ ⊤).mp (fun _ _ _ => Submodule.mem_top)
  obtain ⟨n, S, hs, hi, hsum⟩ := decompose ⊤ htop
  exact ⟨n, S, hs, (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr ⟨hi, hsum⟩⟩

private theorem finiteType_of_linearlyReductive {k A : Type u} [Field k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] {H : HopfAlgebraCategory k}
    (h : Specs.rationalLinearlyReductive H) (ρ : RationalAlgebraAction H A) :
    Algebra.FiniteType k ρ.fixedSubalgebra := by
  let d := ρ.toRightComodule
  obtain ⟨P, hP, _⟩ := RationalRepresentation.canonicalProjection h d
  refine ρ.filtered_finite_generation P
    (RationalRepresentation.canonicalProjection_reynolds h ρ P hP) ?_
  intro W hW hdim x hx
  letI : FiniteDimensional k W := hdim
  obtain ⟨σ, hσ⟩ := (RightComodule.isSubcomodule_iff_exists_coaction d W).mp hW
  obtain ⟨Q, hQ, _⟩ := RationalRepresentation.canonicalProjection h σ
  exact (RationalRepresentation.canonicalProjection_restriction h d W σ hσ P Q hP hQ
    ⟨x, hx⟩).symm ▸ (Q ⟨x, hx⟩ : W).property

/-- Hilbert finite generation for rational actions of connected reductive groups
over algebraically closed fields of characteristic zero. -/
theorem reductive_finite_generation : Specs.ReductiveFiniteGeneration.{u} := by
  intro k A _ _ _ _ _ _ G _ hG ρ hρ
  let G' : AffineGroupCategory k := ⟨G.val, G.property.1⟩
  letI : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  letI : QuasiCompact G.val.X.hom := G.property.2.2
  letI : Smooth G.val.X.hom := hG.1
  let H := GlobalFunctions.globalHopf G.val
  let a := GlobalFunctions.groupUnit G.val
  have ha := GlobalFunctions.groupUnit_underlying G.val
  obtain ⟨e, _⟩ := GlobalFunctions.affineCompatibility G' H a ha
  let s : specGroup H.hopf ≅ G.val :=
    (hopfSpec (CommRingCat.of k)).mapIso e.symm.op ≪≫
      (affineGroupInclusion k).mapIso (coordinateHopfSpecIso G')
  have hss :=
    (LinearAlgebraicGroups.Representation.CompleteReducibility.characteristicZeroCompleteReducibility
      G H.hopf s).1.mp hG
  have hl : Specs.rationalLinearlyReductive H.hopf := by
    intro V _ _ _ d
    exact simple_sum_of_retractions d (hss V d)
  obtain ⟨E, hE⟩ := RationalActionComparison.algebraComparison (A := A) G.val H a ha
  let d : RationalAlgebraAction H.hopf A := E.symm ⟨ρ, hρ⟩
  have hf := (hE d).2
  rw [show E d = ⟨ρ, hρ⟩ from E.apply_symm_apply _] at hf
  rw [hf]
  exact finiteType_of_linearlyReductive hl d

open LinearAlgebraicGroups.Specs.StandardGroups (multiplicativePowerGroup)
open Specs.TorusWeights (coordinates)
open GlobalFunctions (pull)
open private transportCoaction invariants_transportCoaction from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.ExactInvariants

private theorem tensorAlgMap_toLinearMap {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {H B : HopfAlgebraCategory k} (f : H →ₐc[k] B) :
    (Algebra.TensorProduct.map (AlgHom.id k A) f.toAlgHom).toLinearMap =
      f.toLinearMap.lTensor A := by
  apply TensorProduct.ext'
  intro x a
  rfl

private def transportAlgebraAction {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {H B : HopfAlgebraCategory k} (f : H →ₐc[k] B) (ρ : RationalAlgebraAction H A) :
    RationalAlgebraAction B A where
  coaction := (Algebra.TensorProduct.map (AlgHom.id k A) f.toAlgHom).comp ρ.coaction
  coassoc x := by
    let l := ((Algebra.TensorProduct.map (AlgHom.id k A) f.toAlgHom).comp ρ.coaction).toLinearMap
    change TensorProduct.assoc k A B B ((l.rTensor B) (l x)) =
      (Coalgebra.comul (R := k) (A := B)).lTensor A (l x)
    dsimp only [l]
    rw [AlgHom.comp_toLinearMap, tensorAlgMap_toLinearMap]
    exact (transportCoaction f ρ.toRightComodule).coassoc x
  counit x := by
    let l := ((Algebra.TensorProduct.map (AlgHom.id k A) f.toAlgHom).comp ρ.coaction).toLinearMap
    change TensorProduct.rid k A ((Coalgebra.counit (R := k) (A := B)).lTensor A (l x)) = x
    dsimp only [l]
    rw [AlgHom.comp_toLinearMap, tensorAlgMap_toLinearMap]
    exact (transportCoaction f ρ.toRightComodule).counit x

private theorem transport_fixedSubalgebra {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {H B : HopfAlgebraCategory k} (e : H ≅ B) (ρ : RationalAlgebraAction H A) :
    (transportAlgebraAction e.hom.hom ρ).fixedSubalgebra = ρ.fixedSubalgebra := by
  have hd : (transportAlgebraAction e.hom.hom ρ).toRightComodule =
      transportCoaction e.hom.hom ρ.toRightComodule := by
    have hc : (transportAlgebraAction e.hom.hom ρ).toRightComodule.coaction =
        (transportCoaction e.hom.hom ρ.toRightComodule).coaction := by
      change ((Algebra.TensorProduct.map (AlgHom.id k A) e.hom.hom.toAlgHom).comp
        ρ.coaction).toLinearMap = _
      rw [AlgHom.comp_toLinearMap, tensorAlgMap_toLinearMap]
      rfl
    generalize (transportAlgebraAction e.hom.hom ρ).toRightComodule = d at hc ⊢
    generalize transportCoaction e.hom.hom ρ.toRightComodule = d' at hc ⊢
    cases d
    cases d'
    cases hc
    rfl
  ext x
  change x ∈ invariants B (transportAlgebraAction e.hom.hom ρ).toRightComodule ↔
    x ∈ invariants H ρ.toRightComodule
  rw [hd, invariants_transportCoaction e]

private theorem standard_torus_finite_generation {k A ι : Type u} [Field k] [IsAlgClosed k]
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [Fintype ι]
    (ρ : GroupAlgebraAction k (KPoints (multiplicativePowerGroup k ι).val) A)
    (hρ : HasRegularOrbits ρ.toRepresentation) :
    Algebra.FiniteType k ρ.fixedSubalgebra := by
  let D := multiplicativePowerGroup k ι
  let T := D.val
  let B := coordinates k (Multiplicative (ι → ℤ))
  letI : LocallyOfFiniteType T.X.hom := D.property.2.1
  letI : QuasiCompact T.X.hom := D.property.2.2
  have hred : IsReduced T.X.left := by
    change IsReduced (Spec (CommRingCat.of (AddMonoidAlgebra k (ι → ℤ))))
    infer_instance
  letI : Smooth T.X.hom := smoothOfReducedOverPerfectField k T hred
  obtain ⟨H, a, _, e, ha, _, _⟩ := TorusProjection.pointInvariants k ι
  obtain ⟨E, hE⟩ := RationalActionComparison.algebraComparison (A := A) T H a ha
  let d : RationalAlgebraAction H.hopf A := E.symm ⟨ρ, hρ⟩
  have hf := (hE d).2
  rw [show E d = ⟨ρ, hρ⟩ from E.apply_symm_apply _] at hf
  let b : RationalAlgebraAction B A := transportAlgebraAction e.inv.hom d
  have hb : b.fixedSubalgebra = d.fixedSubalgebra := transport_fixedSubalgebra e.symm d
  rw [show ρ.fixedSubalgebra = d.fixedSubalgebra from hf, ← hb]
  obtain ⟨R, hR, hReynolds⟩ := TorusProjection.reynolds b
  refine b.filtered_finite_generation R hReynolds (fun W hW _ x hx => ?_)
  have hval := DFunLike.congr_fun hR x
  change (R x : A) = TorusProjection.zeroComponent b.toRightComodule x at hval
  rw [hval]
  exact TorusProjection.stableSubspaces b.toRightComodule W hW hx

/-- Hilbert finite generation for rational actions of split tori in any characteristic. -/
theorem split_torus_finite_generation : Specs.SplitTorusFiniteGeneration.{u} := by
  intro k A _ _ _ _ _ T hT ρ hρ
  change GroupAlgebraAction k (KPoints T) A at ρ
  obtain ⟨n, ⟨s⟩⟩ := hT
  let D := (multiplicativePowerGroup k (ULift.{u} (Fin n))).val
  let e : KPoints D ≅ KPoints T :=
    ((groupPointsFunctor k).mapIso s.symm).app (CommAlgCat.of k k)
  let σ : GroupAlgebraAction k (KPoints D) A := ρ.comp e.hom.hom
  have hσ : HasRegularOrbits σ.toRepresentation := by
    intro x
    obtain ⟨m, f, w, h⟩ := hρ x
    refine ⟨m, fun j => pull s.inv.hom.hom (f j), w, fun g => ?_⟩
    change ρ.toRepresentation (e.hom g) x = _
    rw [h]
    congr 1
  have hsurj : Function.Surjective e.hom := e.groupIsoToMulEquiv.surjective
  have hfix : σ.fixedSubalgebra = ρ.fixedSubalgebra := by
    ext x
    change (∀ g : KPoints D, ρ.toRepresentation (e.hom g) x = x) ↔
      ∀ g : KPoints T, ρ.toRepresentation g x = x
    exact ⟨fun h g => let ⟨a, ha⟩ := hsurj g; ha ▸ h a, fun h g => h (e.hom g)⟩
  change Algebra.FiniteType k ρ.fixedSubalgebra
  rw [← hfix]
  exact standard_torus_finite_generation σ hσ

end

end RepTheorySurvey.Invariants
