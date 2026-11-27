import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.LineStabilizerRepresentation
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.ClosedSubgroupRepresentations
import Batteries.Tactic.OpenPrivate

namespace GaloisFormalization.PV.ClosedSubgroupRepresentations

universe u

/-- The line-stabilizer conclusion for closed subgroups. -/
theorem exists_lineStabilizerRepresentation :
    Specs.ExistsLineStabilizerRepresentation.{u} :=
  LineStabilizerRepresentation.exists_lineStabilizerRepresentation

open MatrixGroupCoordinates
open scoped MatrixGroupCoordinates.Specs

open private regular_inverse regular_representation_of_entries from
  MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.LineStabilizerRepresentation

noncomputable section

variable {C : Type u} [Field C] {n : ℕ} {G : Subgroup (GL (Fin n) C)}

private abbrev RegularMatrix {ι κ : Type*} (M : G → Matrix ι κ C) : Prop :=
  IsRegularMatrix (S := (G : Set (GL (Fin n) C))) M

private theorem regular_matrix_const {ι κ : Type*} (M : Matrix ι κ C) :
    RegularMatrix (fun _ : G => M) :=
  fun i j => ⟨MvPolynomial.C (M i j), fun g => by
    simp [MatrixGroupCoordinates.Specs.evalAt]⟩

private theorem regular_matrix_mul {ι κ η : Type*} [Fintype κ]
    {A : G → Matrix ι κ C} {B : G → Matrix κ η C}
    (hA : RegularMatrix A) (hB : RegularMatrix B) :
    RegularMatrix (fun g => A g * B g) := by
  classical
  choose p hp using hA
  choose q hq using hB
  exact fun i j => ⟨∑ k, p i k * q k j, fun g => by
    simp only [map_sum, map_mul, hp, hq, Matrix.mul_apply]⟩

section Restriction

variable {V : Type*} [AddCommGroup V] [Module C V]

private def restrictAction (r : G →* Module.End C V) (U : Submodule C V)
    (hU : ∀ g (v : V), v ∈ U → r g v ∈ U) : G →* Module.End C U where
  toFun g := (r g).restrict (hU g)
  map_one' := by
    ext v
    change r 1 (v : V) = v
    simp
  map_mul' g h := by
    ext v
    change r (g * h) (v : V) = r g (r h (v : V))
    rw [map_mul, Module.End.mul_apply]

private theorem regular_restrictAction {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (b : Module.Basis ι C V) (r : G →* Module.End C V)
    (hr : RegularMatrix fun g => LinearMap.toMatrix b b (r g))
    (U : Submodule C V) (hU : ∀ g (v : V), v ∈ U → r g v ∈ U)
    (d : Module.Basis κ C U) :
    RegularMatrix fun g => LinearMap.toMatrix d d (restrictAction r U hU g) := by
  classical
  obtain ⟨p, hp⟩ := LinearMap.exists_extend (LinearMap.id : U →ₗ[C] U)
  have he (g : G) : restrictAction r U hU g = p.comp ((r g).comp U.subtype) := by
    apply LinearMap.ext
    intro v
    exact (LinearMap.congr_fun hp (restrictAction r U hU g v)).symm
  simp only [he, LinearMap.toMatrix_comp d b b,
    LinearMap.toMatrix_comp d b d]
  exact regular_matrix_mul (regular_matrix_const _) (regular_matrix_mul hr (regular_matrix_const _))

end Restriction

section Centralizer

variable {V : Type*} [AddCommGroup V] [Module C V]

private def conjugationAction (r : G →* Module.End C V) :
    G →* Module.End C (Module.End C V) where
  toFun g := LinearMap.mulLeftRight C (r g, r g⁻¹)
  map_one' := by
    apply LinearMap.ext
    intro T
    change r 1 * T * r (1 : G)⁻¹ = T
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro T
    change r (g * h) * T * r (g * h)⁻¹ = r g * (r h * T * r h⁻¹) * r g⁻¹
    simp [mul_assoc]

private theorem conjugationAction_apply (r : G →* Module.End C V)
    (g : G) (T : Module.End C V) :
    conjugationAction r g T = r g * T * r g⁻¹ := rfl

private abbrev actionCentralizer (r : G →* Module.End C V) (H : Subgroup G) :
    Submodule C (Module.End C V) :=
  (Subalgebra.centralizer C (r '' (H : Set G))).toSubmodule

private theorem mem_actionCentralizer (r : G →* Module.End C V) (H : Subgroup G)
    (T : Module.End C V) :
    T ∈ actionCentralizer r H ↔ ∀ h ∈ H, r h * T = T * r h := by
  change T ∈ Subalgebra.centralizer C (r '' (H : Set G)) ↔ _
  rw [Subalgebra.mem_centralizer_iff]
  simp only [Set.forall_mem_image, SetLike.mem_coe]

private theorem conjugation_preserves_centralizer (r : G →* Module.End C V)
    (H : Subgroup G) (hN : H.Normal) (g : G) (T : Module.End C V)
    (hT : T ∈ actionCentralizer r H) : conjugationAction r g T ∈ actionCentralizer r H := by
  rw [mem_actionCentralizer] at hT ⊢
  intro h hh
  let k := g⁻¹ * h * g
  have hk : k ∈ H := hN.conj_mem' h hh g
  have hleft : r h * r g = r g * r k := by
    rw [← map_mul, ← map_mul]
    congr 1
    simp [k, mul_assoc]
  have hright : r k * r g⁻¹ = r g⁻¹ * r h := by
    rw [← map_mul, ← map_mul]
    congr 1
    simp [k, mul_assoc]
  rw [conjugationAction_apply]
  calc
    r h * (r g * T * r g⁻¹) = r g * (r k * T) * r g⁻¹ := by
      simpa only [mul_assoc] using congrArg (fun L : Module.End C V => L * (T * r g⁻¹)) hleft
    _ = (r g * T) * (r k * r g⁻¹) := by simp only [hT k hk, mul_assoc]
    _ = (r g * T * r g⁻¹) * r h := by simp only [hright, mul_assoc]

private theorem regular_conjugationAction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι C V) (r : G →* Module.End C V)
    (hr : RegularMatrix fun g => LinearMap.toMatrix b b (r g)) :
    RegularMatrix fun g => LinearMap.toMatrix b.end b.end (conjugationAction r g) := by
  have hi : RegularMatrix fun g => LinearMap.toMatrix b b (r g⁻¹) :=
    fun i j => regular_inverse G (hr i j)
  have hrepr (M : Matrix ι ι C) (i : ι × ι) :
      (Matrix.stdBasis C ι ι).repr M i = M i.1 i.2 := rfl
  intro i j
  simpa only [LinearMap.toMatrix_apply, Module.Basis.linearMap_repr_apply, hrepr,
    conjugationAction_apply, LinearMap.toMatrix_mul] using
      (regular_matrix_mul (regular_matrix_mul hr
        (regular_matrix_const (LinearMap.toMatrix b b (b.end j)))) hi i.1 i.2)

end Centralizer

private theorem action_injective {V : Type*} [AddCommGroup V] [Module C V]
    (r : G →* Module.End C V) (g : G) : Function.Injective (r g) := by
  apply Function.LeftInverse.injective (g := r g⁻¹)
  intro v
  change (r g⁻¹ * r g) v = v
  rw [← map_mul, inv_mul_cancel, map_one]
  rfl

private theorem kernel_representation_of_eigenbasis
    {V : Type*} [AddCommGroup V] [Module C V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι C V) (R : G →* Module.End C V)
    (hRreg : RegularMatrix fun g => LinearMap.toMatrix b b (R g))
    (H : Subgroup G) (hN : H.Normal) (i : ι)
    (heig : ∀ h ∈ H, ∀ j, ∃ a : C, R h (b j) = a • b j)
    (hline : ∀ (g : G) (a : C), R g (b i) = a • b i → g ∈ H) :
    ∃ (k : ℕ) (σ : G →* GL (Fin k) C), IsRegularRepresentation σ ∧ σ.ker = H := by
  classical
  let P := b.end (i, i)
  let E := actionCentralizer R H
  have hP : P ∈ E := by
    apply (mem_actionCentralizer R H P).2
    intro h hh
    choose a ha using heig h hh
    apply sub_eq_zero.mp
    simpa only [Ring.lie_def, sub_self, zero_smul] using
      b.lie_end_of_apply_eq_smul a (R h) ha i i
  have hPr : P = (b.coord i).smulRight (b i) := by
    apply b.ext
    intro j
    change (b.end (i, i)) (b j) = (b.coord i).smulRight (b i) (b j)
    rw [Module.Basis.end_apply_apply, LinearMap.smulRight_apply, Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_apply]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  have hPi : P (b i) = b i := by
    simp [P, Module.Basis.end_apply_apply]
  let T := restrictAction (conjugationAction R) E (conjugation_preserves_centralizer R H hN)
  have hker (g : G) : T g = 1 ↔ g ∈ H := by
    constructor
    · intro hg
      let p : E := ⟨P, hP⟩
      have hfix : R g * P * R g⁻¹ = P := by
        have he : T g p = p := by rw [hg]; rfl
        exact congrArg Subtype.val he
      have hinv : R g⁻¹ * R g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
      have hcomm : R g * P = P * R g := calc
        R g * P = (R g * P * R g⁻¹) * R g := by rw [mul_assoc (R g * P), hinv, mul_one]
        _ = P * R g := by rw [hfix]
      have hv : R g (P (b i)) = P (R g (b i)) := LinearMap.congr_fun hcomm (b i)
      rw [hPi, hPr, LinearMap.smulRight_apply] at hv
      exact hline g _ hv
    · intro hg
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change R g * (x : Module.End C V) * R g⁻¹ = (x : Module.End C V)
      rw [(mem_actionCentralizer R H _).mp x.property g hg, mul_assoc,
        ← map_mul, mul_inv_cancel, map_one, mul_one]
  let : FiniteDimensional C (Module.End C V) := b.end.finiteDimensional_of_finite
  let : Module.Free C E := Module.Free.of_divisionRing C E
  let d := Module.finBasis C E
  have hTreg : RegularMatrix fun g => LinearMap.toMatrix d d (T g) :=
    regular_restrictAction b.end (conjugationAction R) (regular_conjugationAction b R hRreg)
      E (conjugation_preserves_centralizer R H hN) d
  let σ := ((LinearMap.toMatrixAlgEquiv d).toAlgHom.toMonoidHom.comp T).toHomUnits
  refine ⟨_, σ, regular_representation_of_entries G σ hTreg, ?_⟩
  ext g
  rw [MonoidHom.mem_ker, ← hker]
  constructor
  · intro h
    apply (LinearMap.toMatrixAlgEquiv d).injective
    have hv := congrArg Units.val h
    change LinearMap.toMatrixAlgEquiv d (T g) = 1 at hv
    rwa [map_one]
  · intro h
    apply Units.ext
    change LinearMap.toMatrixAlgEquiv d (T g) = 1
    rw [h, map_one]

/-- The centralizer on the span of a line's orbit gives a kernel representation
when the stabilizer of the line is normal. -/
theorem exists_kernelRepresentation : Specs.ExistsKernelRepresentation.{u} := by
  classical
  intro C _ _ _ n G hG H hH hN
  obtain ⟨m, ρ, w, hρ, hw, hstab⟩ := exists_lineStabilizerRepresentation G hG H hH
  let r : G →* Module.End C (Fin m → C) :=
    Matrix.toLinAlgEquiv'.toAlgHom.toMonoidHom.comp (Units.coeHom _ |>.comp ρ)
  have hline (g : G) : (∃ a : Cˣ, (a : C) • w = r g w) ↔ g ∈ H := by
    rw [← hstab g, Submodule.map_span, Set.image_singleton]
    change (∃ a : Cˣ, (a : C) • w = r g w) ↔
      Submodule.span C {r g w} = Submodule.span C {w}
    exact Submodule.span_singleton_eq_span_singleton.symm.trans eq_comm
  have hr : RegularMatrix fun g => LinearMap.toMatrix (Pi.basisFun C (Fin m))
      (Pi.basisFun C (Fin m)) (r g) := by
    have he (g : G) : LinearMap.toMatrix (Pi.basisFun C (Fin m))
        (Pi.basisFun C (Fin m)) (r g) = (ρ g).val := by
      change LinearMap.toMatrixAlgEquiv' (Matrix.toLinAlgEquiv' (ρ g).val) = _
      exact LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv' _
    simp only [he]
    exact hρ.1
  let U := Submodule.span C (Set.range fun g : G => r g w)
  have hU (g : G) : ∀ v ∈ U, r g v ∈ U := by
    have hle : U ≤ U.comap (r g) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      change r g (r k w) ∈ U
      rw [← Module.End.mul_apply, ← map_mul]
      exact Submodule.subset_span (Set.mem_range_self (g * k))
    exact fun _ hv => hle hv
  let R := restrictAction r U hU
  let orbit (g : G) : U := ⟨r g w, Submodule.subset_span (Set.mem_range_self g)⟩
  have hsp : Submodule.span C (Set.range orbit) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff U
      (fun g => Submodule.subset_span (Set.mem_range_self g))).2 rfl
  let u := orbit 1
  have hu : (u : Fin m → C) = w := by
    change r 1 w = w
    simp
  have hune : u ≠ 0 := by
    intro h
    exact hw (hu.symm.trans (congrArg Subtype.val h))
  have hli : LinearIndepOn C id ({u} : Set U) := (linearIndepOn_singleton_iff C).mpr hune
  have hsub : ({u} : Set U) ⊆ Set.range orbit := Set.singleton_subset_iff.mpr
    (Set.mem_range_self 1)
  let b := Module.Basis.extendLe hli hsub hsp.ge
  let : Fintype (hli.extend hsub) := FiniteDimensional.fintypeBasisIndex b
  obtain ⟨i, hi⟩ : u ∈ Set.range b :=
    Module.Basis.subset_extendLe hli hsub hsp.ge (Set.mem_singleton u)
  have heig (h : G) (hh : h ∈ H) (j : hli.extend hsub) :
      ∃ a : C, R h (b j) = a • b j := by
    obtain ⟨k, hk⟩ := Module.Basis.extendLe_subset hli hsub hsp.ge (Set.mem_range_self j)
    have hkH : k⁻¹ * h * k ∈ H := hN.conj_mem' h hh k
    obtain ⟨a, ha⟩ := (hline _).mpr hkH
    refine ⟨(a : C), ?_⟩
    change orbit k = b j at hk
    rw [← hk]
    apply Subtype.ext
    change r h (r k w) = (a : C) • r k w
    have hmul : h * k = k * (k⁻¹ * h * k) := by simp [mul_assoc]
    rw [← Module.End.mul_apply, ← map_mul, hmul, map_mul, Module.End.mul_apply, ← ha, map_smul]
  have hRreg : RegularMatrix fun g => LinearMap.toMatrix b b (R g) :=
    regular_restrictAction _ r hr U hU b
  apply kernel_representation_of_eigenbasis b R hRreg H hN i heig
  intro g a hg
  rw [hi] at hg
  have hv : r g w = a • w := by
    have he : r g (u : Fin m → C) = a • (u : Fin m → C) := congrArg Subtype.val hg
    exact hu ▸ he
  have ha : a ≠ 0 := by
    intro hz
    exact hw ((action_injective r g) (by simpa [hz] using hv))
  exact (hline g).mp ⟨Units.mk0 a ha, hv.symm⟩

end

end GaloisFormalization.PV.ClosedSubgroupRepresentations
