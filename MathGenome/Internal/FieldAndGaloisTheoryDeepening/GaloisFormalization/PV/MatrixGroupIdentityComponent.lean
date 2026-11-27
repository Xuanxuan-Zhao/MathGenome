import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.MatrixGroupCoordinates
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.MatrixGroupIdentityComponent
import Mathlib.Topology.Connected.Clopen

/-!
# Identity component of a matrix group

The topology on a subgroup is induced by the algebraic Zariski topology on
the general linear group. A fixed translation and inversion are continuous
because they have polynomial coordinate formulas.
-/

namespace GaloisFormalization.PV.MatrixGroupIdentityComponent

open MatrixGroupCoordinates
open scoped MatrixGroupCoordinates.Specs Pointwise

universe u

variable {C : Type u} [Field C] {n : ℕ}

private theorem continuous_of_coordinate_substitution
    {f : GL (Fin n) C → GL (Fin n) C}
    (v : CoordinateVariable n → CoordinatePolynomial C n)
    (hv : ∀ g i, evalAt (C := C) g (v i) = evalAt (C := C) (f g) (MvPolynomial.X i)) :
    Continuous f := by
  have heval (g : GL (Fin n) C) :
      (evalAt (C := C) g).comp (MvPolynomial.aeval v) = evalAt (C := C) (f g) := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa only [AlgHom.comp_apply, MvPolynomial.aeval_X] using hv g i
  apply continuous_iff_isClosed.mpr
  intro S hS
  obtain ⟨s, rfl⟩ := (isClosed_iff_zeroLocus S).mp hS
  apply (isClosed_iff_zeroLocus _).mpr
  refine ⟨MvPolynomial.aeval v '' s, ?_⟩
  ext g
  change (∀ p ∈ s, evalAt (C := C) (f g) p = 0) ↔
    (∀ q ∈ MvPolynomial.aeval v '' s, evalAt (C := C) g q = 0)
  constructor
  · rintro hg _ ⟨p, hp, rfl⟩
    exact (DFunLike.congr_fun (heval g) p).trans (hg p hp)
  · intro hg p hp
    exact (DFunLike.congr_fun (heval g) p).symm.trans (hg _ ⟨p, hp, rfl⟩)

private theorem continuous_ambient_mul_left (a : GL (Fin n) C) :
    Continuous (fun g => a * g) := by
  classical
  apply continuous_of_coordinate_substitution
    (Sum.elim (fun ij => ∑ k : Fin n, MvPolynomial.C (a ij.1 k) *
      MvPolynomial.X (Sum.inl (k, ij.2)))
      (fun _ => MvPolynomial.C (inverseDeterminant a) * MvPolynomial.X (Sum.inr ())))
  intro g i
  rcases i with ⟨i, j⟩ | ⟨⟨⟩⟩
  · simp [Matrix.mul_apply]
  · simp [MatrixGroupCoordinates.Specs.inverseDeterminant, mul_comm]

private theorem continuous_ambient_mul_right (a : GL (Fin n) C) :
    Continuous (fun g => g * a) := by
  classical
  apply continuous_of_coordinate_substitution
    (Sum.elim (fun ij => ∑ k : Fin n, MvPolynomial.X (Sum.inl (ij.1, k)) *
      MvPolynomial.C (a k ij.2))
      (fun _ => MvPolynomial.X (Sum.inr ()) * MvPolynomial.C (inverseDeterminant a)))
  intro g i
  rcases i with ⟨i, j⟩ | ⟨⟨⟩⟩
  · simp [Matrix.mul_apply]
  · simp [MatrixGroupCoordinates.Specs.inverseDeterminant, mul_comm]

private theorem continuous_ambient_inv :
    Continuous (fun g : GL (Fin n) C => g⁻¹) := by
  classical
  let X : Matrix (Fin n) (Fin n) (CoordinatePolynomial C n) :=
    Matrix.of fun i j => MvPolynomial.X (Sum.inl (i, j))
  apply continuous_of_coordinate_substitution
    (Sum.elim (fun ij => MvPolynomial.X (Sum.inr ()) * X.adjugate ij.1 ij.2)
      (fun _ => X.det))
  intro g i
  have hX : (evalAt (C := C) g).mapMatrix X = g.val := by
    ext i j
    exact evalAt_entry g i j
  rcases i with ⟨i, j⟩ | ⟨⟨⟩⟩
  · simp only [Sum.elim_inl, map_mul, evalAt_entry, evalAt_inverseDeterminant]
    have hadj : evalAt (C := C) g (X.adjugate i j) = g.val.adjugate i j := by
      change ((evalAt (C := C) g).mapMatrix X.adjugate) i j = _
      rw [AlgHom.map_adjugate, hX]
    rw [hadj]
    change _ = ((g⁻¹ : GL (Fin n) C).val) i j
    rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def]
    change _ = (Ring.inverse g.val.det) * g.val.adjugate i j
    rw [← Matrix.GeneralLinearGroup.val_det_apply, Ring.inverse_unit]
    rfl
  · simp only [Sum.elim_inr, AlgHom.map_det, hX, evalAt_inverseDeterminant]
    simp [MatrixGroupCoordinates.Specs.inverseDeterminant]

variable {G : Subgroup (GL (Fin n) C)}

theorem continuous_mul_left (g : G) : Continuous (fun x : G => g * x) :=
  ((continuous_ambient_mul_left g.val).comp continuous_subtype_val).subtype_mk _

theorem continuous_mul_right (g : G) : Continuous (fun x : G => x * g) :=
  ((continuous_ambient_mul_right g.val).comp continuous_subtype_val).subtype_mk _

theorem continuous_inv : Continuous (fun x : G => x⁻¹) :=
  (continuous_ambient_inv.comp continuous_subtype_val).subtype_mk _

theorem continuous_conj (g : G) : Continuous (fun x : G => g * x * g⁻¹) :=
  (continuous_mul_right g⁻¹).comp (continuous_mul_left g)

abbrev identityComponent := @Specs.identityComponent

private theorem mem_connectedComponent_mul_iff (g x : G) :
    x ∈ connectedComponent g ↔ g⁻¹ * x ∈ connectedComponent (1 : G) := by
  constructor
  · intro hx
    simpa only [inv_mul_cancel] using
      (continuous_mul_left g⁻¹).mapsTo_connectedComponent g hx
  · intro hx
    simpa only [mul_one, mul_inv_cancel_left] using
      (continuous_mul_left g).mapsTo_connectedComponent (1 : G) hx

theorem identityComponent_carrier (G : Subgroup (GL (Fin n) C)) :
    (identityComponent G : Set G) = connectedComponent (1 : G) := by
  let H : Subgroup G :=
    { carrier := connectedComponent (1 : G)
      one_mem' := mem_connectedComponent
      mul_mem' := fun {x y} hx hy => by
        have hm := (continuous_mul_left x).mapsTo_connectedComponent (1 : G) hy
        simpa only [mul_one, ← connectedComponent_eq hx] using hm
      inv_mem' := fun {x} hx => by
        simpa only [inv_one] using (continuous_inv (G := G)).mapsTo_connectedComponent (1 : G) hx }
  exact congrArg (fun K : Subgroup G => (K : Set G))
    (Subgroup.closure_eq_of_le (K := H) Set.Subset.rfl Subgroup.subset_closure)

theorem identityComponent_closed (G : Subgroup (GL (Fin n) C)) :
    IsClosed (identityComponent G : Set G) := by
  rw [identityComponent_carrier]
  exact isClosed_connectedComponent

instance identityComponent_normal (G : Subgroup (GL (Fin n) C)) :
    (identityComponent G).Normal where
  conj_mem x hx g := by
    change x ∈ (identityComponent G : Set G) at hx
    change g * x * g⁻¹ ∈ (identityComponent G : Set G)
    rw [identityComponent_carrier] at hx ⊢
    simpa only [mul_one, mul_inv_cancel] using
      (continuous_conj g).mapsTo_connectedComponent (1 : G) hx

private theorem leftCoset_eq_connectedComponent (g : G) :
    g • (identityComponent G : Set G) = connectedComponent g := by
  ext x
  rw [mem_leftCoset_iff, identityComponent_carrier]
  exact (mem_connectedComponent_mul_iff g x).symm

theorem identityComponent_cosets (G : Subgroup (GL (Fin n) C)) (g : G) :
    g • (identityComponent G : Set G) = connectedComponent g ∧
      MulOpposite.op g • (identityComponent G : Set G) = connectedComponent g :=
  ⟨leftCoset_eq_connectedComponent g,
    (eq_cosets_of_normal (identityComponent G) (identityComponent_normal G) g).symm.trans
      (leftCoset_eq_connectedComponent g)⟩

instance identityComponent_finiteIndex (G : Subgroup (GL (Fin n) C)) :
    (identityComponent G).FiniteIndex := by
  let : TopologicalSpace.NoetherianSpace (GL (Fin n) C) := zariski_noetherian
  let : TopologicalSpace.NoetherianSpace G :=
    Topology.IsInducing.subtypeVal.noetherianSpace
  let : Finite (irreducibleComponents G) :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype
  let point (Z : irreducibleComponents G) : G := Z.2.1.nonempty.choose
  let f (Z : irreducibleComponents G) : G ⧸ identityComponent G := QuotientGroup.mk (point Z)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    let Z : irreducibleComponents G :=
      ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
    have hpoint : point Z ∈ irreducibleComponent x := Z.2.1.nonempty.choose_spec
    refine ⟨Z, ?_⟩
    change QuotientGroup.mk (point Z) = QuotientGroup.mk x
    rw [eq_comm, QuotientGroup.eq, ← SetLike.mem_coe, ← mem_leftCoset_iff,
      leftCoset_eq_connectedComponent]
    exact irreducibleComponent_subset_connectedComponent hpoint
  let := Finite.of_surjective f hf
  exact Subgroup.finiteIndex_of_finite_quotient

theorem closed_finiteIndex_clopen (H : Subgroup G) [H.FiniteIndex]
    (hH : IsClosed (H : Set G)) : IsClopen (H : Set G) := by
  refine ⟨hH, isClosed_compl_iff.mp ?_⟩
  have hcoset (x : G) (q : G ⧸ H) :
      x ∈ q.out • (H : Set G) ↔ (QuotientGroup.mk x : G ⧸ H) = q := by
    rw [mem_leftCoset_iff]
    change q.out⁻¹ * x ∈ H ↔ _
    rw [← QuotientGroup.eq, QuotientGroup.out_eq', eq_comm]
  have hone (x : G) : (QuotientGroup.mk x : G ⧸ H) = QuotientGroup.mk (1 : G) ↔ x ∈ H := by
    rw [eq_comm, QuotientGroup.eq, inv_one, one_mul]
  have hcover : (H : Set G)ᶜ =
      ⋃ q : {q : G ⧸ H // q ≠ QuotientGroup.mk (1 : G)}, q.1.out • (H : Set G) := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, hcoset]
    constructor
    · intro hx
      exact ⟨⟨QuotientGroup.mk x, fun h => hx ((hone x).mp h)⟩, rfl⟩
    · rintro ⟨q, hq⟩ hx
      exact q.2 (hq.symm.trans ((hone x).mpr hx))
  rw [hcover]
  apply isClosed_iUnion_of_finite
  intro q
  convert hH.preimage (continuous_mul_left q.1.out⁻¹) using 1
  ext x
  exact mem_leftCoset_iff _

theorem identityComponent_le_of_closed_finiteIndex (H : Subgroup G) [H.FiniteIndex]
    (hH : IsClosed (H : Set G)) : identityComponent G ≤ H := by
  change (identityComponent G : Set G) ⊆ (H : Set G)
  rw [identityComponent_carrier]
  exact (closed_finiteIndex_clopen H hH).connectedComponent_subset H.one_mem

end GaloisFormalization.PV.MatrixGroupIdentityComponent
