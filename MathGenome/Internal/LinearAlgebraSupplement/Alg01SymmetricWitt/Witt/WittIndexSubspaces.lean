import MathGenome.Internal.LinearAlgebraSupplement.Alg01SymmetricWitt.Witt.Decomposition
import MathGenome.Internal.LinearAlgebraSupplement.Alg01SymmetricWitt.Witt.IsotropicExtension
import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Witt.WittIndexSubspaces
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace Alg01SymmetricWitt.Witt.WittIndexSubspaces

open Coordinates (hyperbolicSum firstCoordinates totallyIsotropic
  mem_firstCoordinates firstCoordinates_totallyIsotropic)
open Decomposition (isWittIndex_iff wittDecomposition)
open QuadraticMap (IsometryEquiv)

universe u v w

variable {k : Type u} [Field k]
variable {V : Type v} [AddCommGroup V] [Module k V]

private theorem finrank_firstCoordinates (r : ℕ) :
    Module.finrank k (firstCoordinates k r) = r := by
  let e : firstCoordinates k r ≃ₗ[k] (Fin r → k) :=
    { toFun := fun x i => (x.val i).1
      invFun := fun a => ⟨fun i => (a i, 0), mem_firstCoordinates.mpr (fun _ => rfl)⟩
      left_inv := fun x => Subtype.ext (funext fun i =>
        Prod.ext rfl ((mem_firstCoordinates.mp x.property i).symm))
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact e.finrank_eq.trans (Module.finrank_fin_fun k)

private theorem totallyIsotropic_map_firstCoordinates
    {C : Type w} [AddCommGroup C] [Module k C]
    {q : QuadraticForm k V} {qC : QuadraticForm k C} {r : ℕ}
    (e : ((hyperbolicSum k r).prod qC).IsometryEquiv q)
    (L : Submodule k C) (hL : totallyIsotropic qC L) :
    totallyIsotropic q (((firstCoordinates k r).prod L).map e.toLinearEquiv.toLinearMap) := by
  rintro _ ⟨⟨x, c⟩, h, rfl⟩
  obtain ⟨hx, hc⟩ := Submodule.mem_prod.mp h
  change q (e (x, c)) = 0
  rw [e.map_app, QuadraticMap.prod_apply, firstCoordinates_totallyIsotropic r x hx,
    hL c hc, add_zero]

private theorem anisotropic_complement_of_maximal
    {C : Type w} [AddCommGroup C] [Module k C]
    {q : QuadraticForm k V} {qC : QuadraticForm k C} {m : ℕ}
    (T : Submodule k V) (e : ((hyperbolicSum k m).prod qC).IsometryEquiv q)
    (hmem : ∀ x c, e (x, c) ∈ T ↔ x ∈ firstCoordinates k m ∧ c = 0)
    (hmax : ∀ S : Submodule k V, T ≤ S → totallyIsotropic q S → S = T) :
    qC.Anisotropic := by
  intro c hc
  let L : Submodule k C := k ∙ c
  let S := ((firstCoordinates k m).prod L).map e.toLinearEquiv.toLinearMap
  have hL : totallyIsotropic qC L := by
    intro y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [qC.map_smul, hc, smul_zero]
  have hTS : T ≤ S := by
    intro t ht
    obtain ⟨⟨x, y⟩, rfl⟩ := e.surjective t
    obtain ⟨hx, rfl⟩ := (hmem x y).mp ht
    exact ⟨(x, 0), Submodule.mem_prod.mpr ⟨hx, L.zero_mem⟩, rfl⟩
  have hS : S = T := hmax S hTS (totallyIsotropic_map_firstCoordinates e L hL)
  have h : e (0, c) ∈ S :=
    ⟨(0, c), Submodule.mem_prod.mpr ⟨Submodule.zero_mem _, Submodule.mem_span_singleton_self c⟩,
      rfl⟩
  exact ((hmem 0 c).mp (hS ▸ h)).2

open private splitHyperbolicSum from MathGenome.Internal.LinearAlgebraSupplement.Alg01SymmetricWitt.Witt.DecompositionUniqueness in
/-- The largest dimension of a totally isotropic subspace equals the Witt index.
An inclusion-maximal totally isotropic subspace has that dimension. -/
theorem wittIndexSubspaces :
    Specs.Alg01SymmetricWitt.Witt.WittIndexSubspaces.wittIndexSubspaces.{u,v} := by
  intro k V _ _ _ _ _ q hq r hr
  constructor
  · intro T hT
    let m := Module.finrank k T
    obtain ⟨C, e, hC, he, hmem⟩ := IsotropicExtension.isotropicExtension q hq T hT
    let qC := q.comp C.subtype
    refine ⟨⟨C, e, hC, he, hmem⟩, ?_, ?_⟩
    · obtain ⟨s, A, hA, _, ⟨d⟩, _⟩ := wittDecomposition.{u,v,v} qC hC
      let qA := qC.comp A.subtype
      let Hm := hyperbolicSum k m
      let rest := (hyperbolicSum k s).prod qA
      let decompose := e.symm.trans ((IsometryEquiv.refl Hm).prod d)
      let combine := (IsometryEquiv.prodComm Hm rest).trans (splitHyperbolicSum qA m s).symm
      have hcount : r = m + s :=
        (isWittIndex_iff q qA (m + s) r hq hA ⟨decompose.trans combine⟩).mp hr
      exact hcount ▸ Nat.le_add_right m s
    · intro hmax
      have hAnis : qC.Anisotropic := anisotropic_complement_of_maximal T e hmem hmax
      exact ((isWittIndex_iff q qC m r hq hAnis ⟨e.symm⟩).mp hr).symm
  · obtain ⟨A, _, ⟨e⟩⟩ := hr
    let L : Submodule k A := ⊥
    let S := (firstCoordinates k r).prod L
    have hL : totallyIsotropic (q.comp A.subtype) L := by
      intro x hx
      change x ∈ (⊥ : Submodule k A) at hx
      rw [Submodule.mem_bot] at hx
      rw [hx, map_zero]
    refine ⟨S.map e.symm.toLinearEquiv.toLinearMap,
      totallyIsotropic_map_firstCoordinates e.symm L hL, ?_⟩
    rw [e.symm.toLinearEquiv.finrank_map_eq, ((firstCoordinates k r).prodEquiv L).finrank_eq,
      Module.finrank_prod, finrank_firstCoordinates, finrank_bot, add_zero]

end Alg01SymmetricWitt.Witt.WittIndexSubspaces
