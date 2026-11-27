import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.FiniteSemilinearDescent
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.OperatorGaloisCorrespondence
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.TorsorSpecialization
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.DescendedRepresentationMatrix
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Flat.Basic

namespace GaloisFormalization.PV

open scoped Matrix TensorProduct
open Matrix (GeneralLinearGroup)
open MatrixGroupCoordinates (CoordinateRing evalCoordinate coordinate_ext regular_iff_coordinate)
open Algebra.TensorProduct (includeLeft includeRight)

noncomputable section

open private mapGL_injective from MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.PicardVessiotTorsor

private theorem mapGL_comp {A B D : Type*} [CommRing A] [CommRing B] [CommRing D]
    {m : ℕ} (f : A →+* B) (g : B →+* D) (X : GL (Fin m) A) :
    GeneralLinearGroup.map g (GeneralLinearGroup.map f X) =
      GeneralLinearGroup.map (g.comp f) X := rfl

private theorem gl_mem_range {A B : Type*} [CommRing A] [CommRing B] {m : ℕ}
    (f : A →+* B) (hf : Function.Injective f) (X : GL (Fin m) B)
    (h : ∀ i j, X i j ∈ Set.range f) (hi : ∀ i j, X⁻¹ i j ∈ Set.range f) :
    ∃ Y : GL (Fin m) A, GeneralLinearGroup.map f Y = X := by
  choose a ha using h
  choose b hb using hi
  let F : Matrix (Fin m) (Fin m) A →+* Matrix (Fin m) (Fin m) B := f.mapMatrix
  have hF : Function.Injective F := fun _ _ h => Matrix.ext fun i j =>
    hf (congrArg (fun M : Matrix (Fin m) (Fin m) B => M i j) h)
  let M : Matrix (Fin m) (Fin m) A := a
  let N : Matrix (Fin m) (Fin m) A := b
  have ha' : F M = X.val := Matrix.ext ha
  have hb' : F N = X.inv := Matrix.ext hb
  refine ⟨⟨M, N, hF ?_, hF ?_⟩, Units.ext ha'⟩
  · rw [map_mul, map_one, ha', hb', X.val_inv]
  · rw [map_mul, map_one, ha', hb', X.inv_val]

/-- A regular representation is the evaluation of an invertible coordinate matrix. -/
private theorem regular_representation_matrix {C : Type*} [Field C] {n m : ℕ}
    (G : Subgroup (GL (Fin n) C)) (ρ : G →* GL (Fin m) C)
    (hρ : MatrixGroupCoordinates.Specs.IsRegularRepresentation ρ) :
    ∃ P : GL (Fin m) (CoordinateRing (G : Set (GL (Fin n) C))),
      ∀ x : G, GeneralLinearGroup.map (evalCoordinate x).toRingHom P = ρ x := by
  classical
  let S : Set (GL (Fin n) C) := G
  let D := CoordinateRing S
  obtain ⟨he, hd⟩ := hρ
  choose p hp using fun i j => (regular_iff_coordinate S (fun x => (ρ x) i j)).mp (he i j)
  obtain ⟨d, hd⟩ := (regular_iff_coordinate S _).mp hd
  let M : Matrix (Fin m) (Fin m) D := p
  have hM (x : G) : (evalCoordinate x).toRingHom.mapMatrix M = (ρ x).val :=
    Matrix.ext fun i j => hp i j x
  have hu : M.det * d = 1 := by
    apply coordinate_ext S
    intro x
    rw [map_mul, map_one, (evalCoordinate x).map_det]
    change ((evalCoordinate x).toRingHom.mapMatrix M).det * evalCoordinate x d = 1
    rw [hM x, hd]
    exact (GeneralLinearGroup.det (ρ x)).val_inv
  let P := GeneralLinearGroup.mk'' M (IsUnit.of_mul_eq_one d hu)
  exact ⟨P, fun x => Units.ext (hM x)⟩

/-- Invariants for an action on the first tensor factor can be read off
coefficient by coefficient in a basis of the second factor. -/
private theorem tensor_fixed_left {K A B I : Type*} [Field K]
    [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (act : I → A →ₐ[K] A)
    (hfix : ∀ a : A, (∀ i, act i a = a) → a ∈ Set.range (algebraMap K A))
    (z : A ⊗[K] B)
    (hz : ∀ i, Algebra.TensorProduct.map (act i) (AlgHom.id K B) z = z) :
    ∃ b : B, (includeRight : B →ₐ[K] A ⊗[K] B) b = z := by
  classical
  let b := Module.Free.chooseBasis K B
  let repr := TensorProduct.equivFinsuppOfBasisRight (M := A) b
  have hcoeff (i : I) (x : A ⊗[K] B) (j : Module.Free.ChooseBasisIndex K B) :
      repr (Algebra.TensorProduct.map (act i) (AlgHom.id K B) x) j =
        act i (repr x j) := by
    induction x using TensorProduct.inductionOn with
    | tmul a c =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, repr,
        TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, map_smul]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  choose k hk using fun j => hfix (repr z j) (fun i => (hcoeff i z j).symm.trans (by rw [hz]))
  let v := (repr z).sum fun j _ => k j • b j
  refine ⟨v, ?_⟩
  calc
    (includeRight : B →ₐ[K] A ⊗[K] B) v =
        (repr z).sum (fun j a => a ⊗ₜ[K] b j) := by
      unfold v Finsupp.sum
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      change (1 : A) ⊗ₜ[K] (k j • b j) = repr z j ⊗ₜ[K] b j
      rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, hk]
    _ = z := by
      rw [← TensorProduct.equivFinsuppOfBasisRight_symm_apply]
      exact repr.symm_apply_apply z

private theorem tensor_fixed_right {K A B I : Type*} [Field K]
    [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (act : I → B →ₐ[K] B)
    (hfix : ∀ b : B, (∀ i, act i b = b) → b ∈ Set.range (algebraMap K B))
    (z : A ⊗[K] B)
    (hz : ∀ i, Algebra.TensorProduct.map (AlgHom.id K A) (act i) z = z) :
    ∃ a : A, (includeLeft : A →ₐ[K] A ⊗[K] B) a = z := by
  let s := Algebra.TensorProduct.comm K A B
  have hs i : Algebra.TensorProduct.map (act i) (AlgHom.id K A) (s z) = s z := by
    rw [← Algebra.TensorProduct.comm_comp_map_apply, hz]
  obtain ⟨a, ha⟩ := tensor_fixed_left act hfix (s z) hs
  exact ⟨a, s.injective ha⟩

set_option maxHeartbeats 600000 in
private theorem gl_descent {K L R I : Type*} [Field K] [Field L] [CommRing R]
    [Algebra K L] [Algebra K R] [FiniteDimensional K L] [IsGalois K L] {m : ℕ}
    (inj : Function.Injective (algebraMap K R))
    (act : I → R →ₐ[K] R) (ρ : I → GL (Fin m) K)
    (hfix : ∀ r : R, (∀ g, act g r = r) → r ∈ Set.range (algebraMap K R))
    (X : GL (Fin m) (L ⊗[K] R))
    (hX : ∀ g, GeneralLinearGroup.map
      (Algebra.TensorProduct.map (AlgHom.id K L) (act g)).toRingHom X =
        X * GeneralLinearGroup.map (algebraMap K (L ⊗[K] R)) (ρ g)) :
    ∃ W : GL (Fin m) R, ∀ g,
      GeneralLinearGroup.map (act g).toRingHom W =
        W * GeneralLinearGroup.map (algebraMap K R) (ρ g) := by
  let S := L ⊗[K] R
  let l : L →ₐ[K] S := includeLeft
  let r : R →ₐ[K] S := includeRight
  let leftAct (γ : Gal(L/K)) : S →ₐ[K] S :=
    Algebra.TensorProduct.map γ.toAlgHom (AlgHom.id K R)
  let rightAct (g : I) : S →ₐ[K] S :=
    Algebra.TensorProduct.map (AlgHom.id K L) (act g)
  let leftGL (γ : Gal(L/K)) := GeneralLinearGroup.map (n := Fin m) (leftAct γ).toRingHom
  let rightGL (g : I) := GeneralLinearGroup.map (n := Fin m) (rightAct g).toRingHom
  let leftIn := GeneralLinearGroup.map (n := Fin m) l.toRingHom
  let rightIn := GeneralLinearGroup.map (n := Fin m) r.toRingHom
  let c (g : I) := GeneralLinearGroup.map (n := Fin m) (algebraMap K S) (ρ g)
  have hinL : Function.Injective l :=
    Algebra.TensorProduct.includeLeft_injective inj
  have hinR : Function.Injective r :=
    Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective
  have hc (γ : Gal(L/K)) (g : I) : leftGL γ (c g) = c g := by
    apply GeneralLinearGroup.ext
    intro i j
    exact (leftAct γ).commutes (ρ g i j)
  have hcomm (g : I) (γ : Gal(L/K)) (U : GL (Fin m) S) :
      rightGL g (leftGL γ U) = leftGL γ (rightGL g U) := by
    have h : (rightAct g).comp (leftAct γ) = (leftAct γ).comp (rightAct g) := by
      dsimp only [rightAct, leftAct]
      rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp]
      simp only [AlgHom.id_comp, AlgHom.comp_id]
    exact congrArg (fun f : S →ₐ[K] S => GeneralLinearGroup.map f.toRingHom U) h
  have hmul (γ η : Gal(L/K)) (U : GL (Fin m) S) :
      leftGL (γ * η) U = leftGL γ (leftGL η U) := by
    apply GeneralLinearGroup.ext
    intro i j
    change leftAct (γ * η) (U i j) = leftAct γ (leftAct η (U i j))
    generalize U i j = z
    induction z using TensorProduct.inductionOn with
    | tmul x y => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hleft (γ : Gal(L/K)) (U : GL (Fin m) L) :
      leftGL γ (leftIn U) = leftIn (GeneralLinearGroup.map γ.toRingEquiv.toRingHom U) := by
    apply GeneralLinearGroup.ext
    intro i j
    change (leftAct γ) (l (U i j)) = l (γ (U i j))
    change (leftAct γ) (U i j ⊗ₜ[K] (1 : R)) = γ (U i j) ⊗ₜ[K] (1 : R)
    rfl
  have hX' (g : I) : rightGL g X = X * c g := hX g
  -- The two actions commute, so X * γ(X)⁻¹ is fixed by the right action.
  -- The fixed ring on this tensor product identifies the ratio with a matrix over L.
  let D (γ : Gal(L/K)) := X * (leftGL γ X)⁻¹
  have hD (γ : Gal(L/K)) (g : I) : rightGL g (D γ) = D γ := by
    change rightGL g (X * (leftGL γ X)⁻¹) = X * (leftGL γ X)⁻¹
    rw [map_mul, map_inv, hcomm, hX', map_mul, hc, mul_inv_rev, ← mul_assoc,
      mul_inv_cancel_right]
  have liftD (γ : Gal(L/K)) : ∃ a : GL (Fin m) L, leftIn a = D γ := by
    apply gl_mem_range l.toRingHom hinL
    · intro i j
      exact tensor_fixed_right act hfix (D γ i j) fun g =>
        congrArg (fun U : GL (Fin m) S => U i j) (hD γ g)
    · intro i j
      exact tensor_fixed_right act hfix ((D γ)⁻¹ i j) fun g =>
        congrArg (fun U : GL (Fin m) S => U i j)
          (by rw [map_inv, hD] : rightGL g (D γ)⁻¹ = (D γ)⁻¹)
  choose a ha using liftD
  have hXγ (γ : Gal(L/K)) : leftIn (a γ) * leftGL γ X = X := by
    rw [ha γ]
    exact inv_mul_cancel_right _ _
  have ha_mul (γ η : Gal(L/K)) :
      a (γ * η) = a γ * GeneralLinearGroup.map γ.toRingEquiv.toRingHom (a η) := by
    apply mapGL_injective l.toRingHom hinL
    apply mul_right_cancel (b := leftGL (γ * η) X)
    change leftIn (a (γ * η)) * _ =
      leftIn (a γ * GeneralLinearGroup.map γ.toRingEquiv.toRingHom (a η)) * _
    rw [hXγ, map_mul, ← hleft, mul_assoc, hmul, ← map_mul, hXγ, hXγ]
  obtain ⟨B, hB⟩ := finiteSemilinearDescent K L m a ha_mul
  let Z := leftIn B * X
  have hZ (γ : Gal(L/K)) : leftGL γ Z = Z := by
    change leftGL γ (leftIn B * X) = leftIn B * X
    rw [map_mul, hleft, hB, map_mul, mul_assoc, hXγ]
  have hfixL (x : L) (hx : ∀ γ : Gal(L/K), γ x = x) :
      x ∈ Set.range (algebraMap K L) := (IsGalois.mem_range_algebraMap_iff_fixed x).mpr hx
  have liftZ : ∃ W : GL (Fin m) R, rightIn W = Z := by
    apply gl_mem_range r.toRingHom hinR
    · intro i j
      exact tensor_fixed_left (fun γ : Gal(L/K) => γ.toAlgHom) hfixL (Z i j) fun γ =>
        congrArg (fun U : GL (Fin m) S => U i j) (hZ γ)
    · intro i j
      exact tensor_fixed_left (fun γ : Gal(L/K) => γ.toAlgHom) hfixL (Z⁻¹ i j) fun γ =>
        congrArg (fun U : GL (Fin m) S => U i j)
          (by rw [map_inv, hZ] : leftGL γ Z⁻¹ = Z⁻¹)
  obtain ⟨W, hW⟩ := liftZ
  refine ⟨W, fun g => mapGL_injective r.toRingHom hinR ?_⟩
  have hright (U : GL (Fin m) R) :
      rightIn (GeneralLinearGroup.map (act g).toRingHom U) = rightGL g (rightIn U) := by
    apply GeneralLinearGroup.ext
    intro i j
    change (1 : L) ⊗ₜ[K] act g (U i j) = rightAct g (1 ⊗ₜ[K] U i j)
    rfl
  have hrightL (U : GL (Fin m) L) : rightGL g (leftIn U) = leftIn U := by
    apply GeneralLinearGroup.ext
    intro i j
    change Algebra.TensorProduct.map (AlgHom.id K L) (act g) (U i j ⊗ₜ[K] (1 : R)) =
      U i j ⊗ₜ[K] (1 : R)
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
  have hrightC : rightIn (GeneralLinearGroup.map (algebraMap K R) (ρ g)) = c g := by
    apply GeneralLinearGroup.ext
    intro i j
    exact r.commutes _
  change rightIn (GeneralLinearGroup.map (act g).toRingHom W) = rightIn (W * _)
  rw [hright, map_mul, hW, hrightC]
  change rightGL g (leftIn B * X) = (leftIn B * X) * c g
  rw [map_mul, hrightL, hX', mul_assoc]

set_option maxHeartbeats 500000 in
/-- The right translation rule over the constant field transports the
representation matrix to an equivariant matrix over the split torsor. -/
private theorem equivariant_matrix_of_specialization
    {kind : OperatorKind} {K R L : Type*}
    [Field K] [CommRing R] [Algebra K R] [Field L] [Algebra K L] {n m : ℕ}
    (δ : Specs.operatorField kind K) (E : Specs.operator kind R)
    (Y : GL (Fin n) R) (point : R →ₐ[K] L)
    (hs : Specs.isTorsorSpecialization δ E Y point)
    (ρ : Specs.matrixGaloisGroup δ E Y →* GL (Fin m) (Specs.constantSubfield δ))
    (hρ : MatrixGroupCoordinates.Specs.IsRegularRepresentation ρ) :
    ∃ X : GL (Fin m) (L ⊗[K] R), ∀ g,
      GeneralLinearGroup.map (Algebra.TensorProduct.map (AlgHom.id K L)
        (Specs.matrixAutomorphism δ E Y g).val.toAlgHom).toRingHom X =
        X * GeneralLinearGroup.map (algebraMap K (L ⊗[K] R))
          (GeneralLinearGroup.map (Specs.constantSubfield δ).subtype (ρ g)) := by
  let C := Specs.constantSubfield δ
  let G := Specs.matrixGaloisGroup δ E Y
  let D := CoordinateRing (G : Set (GL (Fin n) C))
  let : Algebra C L := Algebra.compHom L (Specs.constantSubfield δ).subtype
  let : CommRing D := inferInstanceAs (CommRing (CoordinateRing (G : Set (GL (Fin n) C))))
  let : Algebra C D := inferInstanceAs (Algebra C (CoordinateRing (G : Set (GL (Fin n) C))))
  let V := L ⊗[C] D
  let : CommRing V := Algebra.TensorProduct.instCommRing
  let : Algebra L V := Algebra.TensorProduct.leftAlgebra
  let : Algebra C V := Algebra.TensorProduct.leftAlgebra
  let S := L ⊗[K] R
  rcases hs with ⟨e, translate, _, htranslate, he⟩
  obtain ⟨P, hP⟩ := regular_representation_matrix G ρ hρ
  let ι : D →ₐ[C] V := includeRight
  let p : D →+* S := e.toRingHom.comp ι.toRingHom
  let act (g : G) : S →ₐ[K] S :=
    Algebra.TensorProduct.map (AlgHom.id K L) (Specs.matrixAutomorphism δ E Y g).val.toAlgHom
  refine ⟨GeneralLinearGroup.map p P, ?_⟩
  intro g
  have htrans : GeneralLinearGroup.map (translate g).toRingHom P =
      P * GeneralLinearGroup.map (algebraMap C D) (ρ g) := by
    apply GeneralLinearGroup.ext
    intro i j
    apply coordinate_ext (G : Set (GL (Fin n) C))
    intro x
    have h₁ : GeneralLinearGroup.map (evalCoordinate x).toRingHom
        (GeneralLinearGroup.map (translate g).toRingHom P) = ρ (x * g) := by
      rw [← hP (x * g)]
      exact GeneralLinearGroup.ext fun i j => htranslate g x (P i j)
    have h₂ : GeneralLinearGroup.map (evalCoordinate x).toRingHom
        (GeneralLinearGroup.map (algebraMap C D) (ρ g)) = ρ g :=
      GeneralLinearGroup.ext fun i j => (evalCoordinate x).commutes (ρ g i j)
    have h₃ : GeneralLinearGroup.map (evalCoordinate x).toRingHom
        (P * GeneralLinearGroup.map (algebraMap C D) (ρ g)) = ρ x * ρ g := by
      rw [map_mul, hP x, h₂]
    exact congrArg (fun M : GL (Fin m) C => M i j)
      (h₁.trans ((map_mul ρ x g).trans h₃.symm))
  have htransport : (act g).toRingHom.comp p = p.comp (translate g).toRingHom := by
    apply RingHom.ext
    intro b
    exact (he g 1 b).symm
  have hconstant : p.comp (algebraMap C D) =
      (algebraMap K S).comp (Specs.constantSubfield δ).subtype := by
    apply RingHom.ext
    intro c
    calc
      p (algebraMap C D c) = e (ι (algebraMap C D c)) := rfl
      _ = e (algebraMap C V c) := congrArg e (ι.commutes c)
      _ = e (algebraMap L V (algebraMap C L c)) := rfl
      _ = algebraMap L S (algebraMap C L c) := e.commutes _
      _ = algebraMap K S (c : K) := rfl
  change GeneralLinearGroup.map (act g).toRingHom (GeneralLinearGroup.map p P) = _
  rw [mapGL_comp, htransport, ← mapGL_comp, htrans, map_mul, mapGL_comp, hconstant,
    ← mapGL_comp]

private theorem map_operator_mul_constants {kind : OperatorKind} {K R : Type*}
    [Field K] [CommRing R] [Algebra K R] {m : ℕ}
    (δ : Specs.operatorField kind K) (E : Specs.operator kind R)
    (hE : Specs.isAlgebra δ E)
    (W : Matrix (Fin m) (Fin m) R)
    (B : Matrix (Fin m) (Fin m) (Specs.constantSubfield δ)) :
    let B' := B.map ((algebraMap K R).comp (Specs.constantSubfield δ).subtype)
    (W * B').map (Specs.apply E) = W.map (Specs.apply E) * B' := by
  intro B'
  cases kind with
  | differential =>
    let d := Specs.toDerivation E
    have hB (i j : Fin m) : d (B' i j) = 0 := by
      change Specs.apply E (algebraMap K R ((B i j : Specs.constantSubfield δ) : K)) = 0
      rw [← hE]
      have h := (B i j).property
      change Specs.apply δ (B i j : K) = 0 at h
      rw [h, map_zero]
    apply Matrix.ext
    intro i j
    change d (∑ k, W i k * B' k j) = ∑ k, d (W i k) * B' k j
    simp only [map_sum, Derivation.leibniz, hB, smul_eq_mul, mul_zero, zero_add]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  | difference =>
    let σ := Specs.toRingEquiv E
    have hB : σ.toRingHom.mapMatrix B' = B' := by
      apply Matrix.ext
      intro i j
      change Specs.apply E (algebraMap K R ((B i j : Specs.constantSubfield δ) : K)) =
        algebraMap K R ((B i j : Specs.constantSubfield δ) : K)
      rw [← hE]
      exact congrArg (algebraMap K R) (B i j).property
    change σ.toRingHom.mapMatrix (W * B') = σ.toRingHom.mapMatrix W * B'
    rw [map_mul, hB]

set_option maxHeartbeats 600000 in
private theorem fundamental_of_equivariant
    {kind : OperatorKind} {K R I : Type*} [Field K] [CommRing R] [Algebra K R] {m : ℕ}
    (δ : Specs.operatorField kind K) (E : Specs.operator kind R)
    (hE : Specs.isExtension δ E) (act : I → R →ₐ[K] R)
    (hcomm : ∀ g, Specs.commutes E E (act g))
    (hfix : ∀ r : R, (∀ g, act g r = r) → r ∈ Set.range (algebraMap K R))
    (ρ : I → GL (Fin m) (Specs.constantSubfield δ))
    (W : GL (Fin m) R)
    (hW : ∀ g, GeneralLinearGroup.map (act g).toRingHom W =
      W * GeneralLinearGroup.map
        ((algebraMap K R).comp (Specs.constantSubfield δ).subtype) (ρ g)) :
    ∃ Aρ : Specs.linearSystem kind K m, Specs.isFundamental Aρ E W := by
  let U := W.val.map (Specs.apply E)
  let M := U * W.inv
  have hU : M * W.val = U := by
    change (U * W.inv) * W.val = U
    rw [mul_assoc, W.inv_val, mul_one]
  have hM (g : I) : (act g).toRingHom.mapMatrix M = M := by
    let F : Matrix (Fin m) (Fin m) R →+* Matrix (Fin m) (Fin m) R :=
      (act g).toRingHom.mapMatrix
    let Bg := GeneralLinearGroup.map
      ((algebraMap K R).comp (Specs.constantSubfield δ).subtype) (ρ g)
    have hval : F W.val = W.val * Bg.val :=
      congrArg Units.val (hW g)
    have hUcomm : F U = U * Bg.val := by
      calc
        F U = (F W.val).map (Specs.apply E) := Matrix.ext fun i j => hcomm g _
        _ = U * Bg.val := by
          rw [hval]
          exact map_operator_mul_constants δ E hE.1 W.val (ρ g).val
    apply ((GeneralLinearGroup.map (act g).toRingHom W).isUnit).mul_right_cancel
    change F M * F W.val = M * F W.val
    rw [← map_mul, hU, hUcomm, hval, ← mul_assoc, hU]
  have hentries (i j : Fin m) : M i j ∈ Set.range (algebraMap K R) := by
    apply hfix
    intro g
    exact congrArg (fun A : Matrix (Fin m) (Fin m) R => A i j) (hM g)
  cases kind with
  | differential =>
    choose a ha using hentries
    let Aρ : Matrix (Fin m) (Fin m) K := a
    refine ⟨Aρ, ?_⟩
    have ham : Aρ.map (algebraMap K R) = M := Matrix.ext ha
    change U = Aρ.map (algebraMap K R) * W.val
    rw [ham, hU]
  | difference =>
    let σ := Specs.toRingEquiv E
    let Z := GeneralLinearGroup.map σ.toRingHom W * W⁻¹
    have hf (g : I) : GeneralLinearGroup.map (act g).toRingHom Z = Z := Units.ext (hM g)
    obtain ⟨Aρ, hAρ⟩ := gl_mem_range (algebraMap K R) hE.2 Z hentries (by
      intro i j
      apply hfix
      intro g
      exact congrArg (fun X : GL (Fin m) R => X i j)
        (by rw [map_inv, hf] : GeneralLinearGroup.map (act g).toRingHom Z⁻¹ = Z⁻¹))
    refine ⟨Aρ, ?_⟩
    change U = Aρ.val.map (algebraMap K R) * W.val
    rw [show Aρ.val.map (algebraMap K R) = M from congrArg Units.val hAρ, hU]

set_option maxHeartbeats 600000 in
/-- Every finite-dimensional regular representation of the concrete Galois
group has a covariant fundamental matrix in the Picard–Vessiot ring. -/
theorem descendedRepresentationMatrix.{u, v} : Specs.descendedRepresentationMatrix.{u, v} := by
  intro kind K R _ _ _ n δ A E T Y hbase hpv hY m ρ hρ
  let G := Specs.matrixGaloisGroup δ E Y
  let act (g : G) := (Specs.matrixAutomorphism δ E Y g).val.toAlgHom
  let Q := Specs.totalQuotientRing R
  have hQ := (operatorGaloisCorrespondence δ A E T Y hbase hpv hY).2.2.2
  have hfix (r : R) (hr : ∀ g, act g r = r) : r ∈ Set.range (algebraMap K R) := by
    have hmem : algebraMap R Q r ∈ Specs.matrixFixedSubalgebra δ E Y (Set.univ : Set G) := by
      intro g _
      change IsFractionRing.ringEquivOfRingEquiv
        (Specs.matrixAutomorphism δ E Y g).val.toRingEquiv (algebraMap R Q r) =
        algebraMap R Q r
      rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
      exact congrArg (algebraMap R Q) (hr g)
    rw [hQ] at hmem
    obtain ⟨k, hk⟩ := Algebra.mem_bot.mp hmem
    exact ⟨k, hpv.2.2 ((IsScalarTower.algebraMap_apply K R Q k).symm.trans hk)⟩
  obtain ⟨_, _, _, _, _, L, _, _, hfinite, hgalois, _, hs⟩ :=
    torsorSpecializationAtResidue δ A E Y hbase hpv.1 hY
  let : FiniteDimensional K L := hfinite
  let : IsGalois K L := hgalois
  obtain ⟨X, hX⟩ := equivariant_matrix_of_specialization δ E Y _ hs ρ hρ
  obtain ⟨W, hW⟩ := gl_descent (L := L) hpv.1.1.2 act
    (fun g => GeneralLinearGroup.map (Specs.constantSubfield δ).subtype (ρ g))
    hfix X hX
  have hW' (g : G) : GeneralLinearGroup.map (act g).toRingHom W =
      W * GeneralLinearGroup.map
        ((algebraMap K R).comp (Specs.constantSubfield δ).subtype) (ρ g) := hW g
  obtain ⟨Aρ, hAρ⟩ := fundamental_of_equivariant δ E hpv.1.1 act
    (fun g => (Specs.matrixAutomorphism δ E Y g).property) hfix ρ W hW'
  exact ⟨W, Aρ, hAρ, hW'⟩

end

end GaloisFormalization.PV
