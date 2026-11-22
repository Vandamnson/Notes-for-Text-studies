import OAI.RepresentationTheory.FoulkesHowe.Stabilization
import OAI.RepresentationTheory.FoulkesHowe.FoulkesDiagonal

/-!
Additional interface checks for the unchanged Foulkes--Howe solution.
This file lives outside the original repository.
-/

set_option autoImplicit false

noncomputable section
open scoped BigOperators Pointwise Classical
open OAI.Problem346

namespace FoulkesHoweVerification

universe u v

/-- The custom symmetric power is the span of products of degree-one generators. -/
theorem symPowSubmodule_eq_power
    (W : Type u) [AddCommGroup W] [Module ℂ W] (n : ℕ) :
    symPowSubmodule n W =
      (Submodule.span ℂ (Set.range (SymmetricAlgebra.ι ℂ W))) ^ n := by
  classical
  rw [Submodule.span_pow]
  unfold symPowSubmodule
  congr 1
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact Set.mem_pow_iff_prod.mpr
      ⟨fun i => SymmetricAlgebra.ι ℂ W (w i), fun i => ⟨w i, rfl⟩, rfl⟩
  · intro hz
    obtain ⟨f, hf, hp⟩ := Set.mem_pow_iff_prod.mp hz
    choose w hw using hf
    refine ⟨w, ?_⟩
    simpa only [symMonomialRaw, hw] using hp

/-- Every ordinary homogeneous polynomial gives an element of the corresponding
    homogeneous symmetric algebra, with no multilinear-representability assumption. -/
theorem homogeneous_preimage_mem
    {W : Type u} [AddCommGroup W] [Module ℂ W]
    {κ : Type v} (e : Module.Basis κ ℂ W)
    {n : ℕ} (p : MvPolynomial κ ℂ) (hp : p.IsHomogeneous n) :
    (SymmetricAlgebra.equivMvPolynomial e).symm p ∈ symPowSubmodule n W := by
  let A := (SymmetricAlgebra.equivMvPolynomial e).symm
  have h1 : Submodule.map A.toLinearMap (MvPolynomial.homogeneousSubmodule κ ℂ 1) ≤
      Submodule.span ℂ (Set.range (SymmetricAlgebra.ι ℂ W)) := by
    rw [MvPolynomial.homogeneousSubmodule_one_eq_span_X, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    apply Submodule.subset_span
    exact ⟨e i, (SymmetricAlgebra.equivMvPolynomial_symm_X e i).symm⟩
  have hn : Submodule.map A.toLinearMap (MvPolynomial.homogeneousSubmodule κ ℂ n) ≤
      symPowSubmodule n W := by
    rw [symPowSubmodule_eq_power, ← MvPolynomial.homogeneousSubmodule_one_pow]
    change Submodule.map A.toAlgHom.toLinearMap
      (MvPolynomial.homogeneousSubmodule κ ℂ 1 ^ n) ≤ _
    rw [Submodule.map_pow]
    exact pow_le_pow_left' h1 n
  exact hn (Submodule.mem_map.mpr ⟨p, hp, rfl⟩)

/-- The symmetric-algebra realization evaluates as the usual coordinate polynomial. -/
theorem polynomial_evaluation
    {E : Type u} [AddCommGroup E] [Module ℂ E]
    {κ : Type v} [Fintype κ] (e : Module.Basis κ ℂ E)
    (p : MvPolynomial κ ℂ) (x : E) :
    SymmetricAlgebra.lift (Module.Dual.eval ℂ E x)
      ((SymmetricAlgebra.equivMvPolynomial e.dualBasis).symm p) =
      MvPolynomial.eval (fun i => e.repr x i) p := by
  have h : (SymmetricAlgebra.lift (Module.Dual.eval ℂ E x)).comp
      (SymmetricAlgebra.equivMvPolynomial e.dualBasis).symm.toAlgHom =
      MvPolynomial.aeval (fun i => e.repr x i) := by
    ext i
    simp
  exact congrArg (fun f : MvPolynomial κ ℂ →ₐ[ℂ] ℂ => f p) h

/-- Literal homogeneous-coordinate-polynomial version of the vanishing assertion.
    The basis is arbitrary, and the conclusion is equality of polynomials. -/
theorem homogeneous_polynomial_vanishing
    (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a b : ℕ) (ha : 2 ≤ a) (hab : a * (a - 1) ≤ b)
    {κ : Type v} [Fintype κ] (e : Module.Basis κ ℂ (SymPow b V))
    (p : MvPolynomial κ ℂ) (hp : p.IsHomogeneous a)
    (hvan : ∀ u : Fin b → V,
      MvPolynomial.eval (fun i => e.repr (symMonomial b V u) i) p = 0) :
    p = 0 := by
  let E := SymPow b V
  let q : SymPow a (Module.Dual ℂ E) :=
    ⟨(SymmetricAlgebra.equivMvPolynomial e.dualBasis).symm p,
      homogeneous_preimage_mem e.dualBasis p hp⟩
  let L := PairingConstruction.dualMap E a q
  have hb : 1 ≤ b := by
    have hpred : 1 ≤ a - 1 := by omega
    have hprod := Nat.mul_le_mul ha hpred
    omega
  have hT : monomialFunctional a b V L = 0 := by
    apply vanishing_on_products V a b (by omega) hb hab
    · exact monomialFunctional_symmetric a b V L
    · intro u
      change PairingConstruction.dualMap E a q
        (symMonomial a E (fun _ => symMonomial b V u)) = 0
      rw [PairingConstruction.dualMap_pure]
      change SymmetricAlgebra.lift (Module.Dual.eval ℂ E (symMonomial b V u))
        ((SymmetricAlgebra.equivMvPolynomial e.dualBasis).symm p) = 0
      rw [polynomial_evaluation]
      exact hvan u
  have hL : L = 0 := (monomialFunctional_eq_zero_iff a b V L).mp hT
  have hq : q = 0 := (PairingConstruction.dualMap_injective E a)
    (hL.trans (map_zero (PairingConstruction.dualMap E a)).symm)
  apply (SymmetricAlgebra.equivMvPolynomial e.dualBasis).symm.injective
  simpa [q, E] using congrArg Subtype.val hq

/-- The associated polynomial function vanishes identically. -/
theorem homogeneous_polynomial_function_vanishing
    (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a b : ℕ) (ha : 2 ≤ a) (hab : a * (a - 1) ≤ b)
    {κ : Type v} [Fintype κ] (e : Module.Basis κ ℂ (SymPow b V))
    (f : SymPow b V → ℂ)
    (hpoly : ∃ p : MvPolynomial κ ℂ, p.IsHomogeneous a ∧
      ∀ x, f x = MvPolynomial.eval (fun i => e.repr x i) p)
    (hvan : ∀ u : Fin b → V, f (symMonomial b V u) = 0) :
    f = 0 := by
  obtain ⟨p, hp, hf⟩ := hpoly
  have hp0 := homogeneous_polynomial_vanishing V a b ha hab e p hp
    (fun u => (hf (symMonomial b V u)).symm.trans (hvan u))
  funext x
  simp [hf x, hp0]

/-- The exact pure-power formula uniquely determines a linear map on the source. -/
theorem map_unique_of_pure_rule
    (V : Type u) [AddCommGroup V] [Module ℂ V] (a b : ℕ)
    (μ ν : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V))
    (hμ : ∀ u : Fin b → V,
      μ (symMonomial b (SymPow a V) (fun j => symMonomial a V (fun _ => u j))) =
        symMonomial a (SymPow b V) (fun _ => symMonomial b V u))
    (hν : ∀ u : Fin b → V,
      ν (symMonomial b (SymPow a V) (fun j => symMonomial a V (fun _ => u j))) =
        symMonomial a (SymPow b V) (fun _ => symMonomial b V u)) : μ = ν := by
  have h : μ.compMultilinearMap (symMonomialMultilinear b (SymPow a V)) =
      ν.compMultilinearMap (symMonomialMultilinear b (SymPow a V)) := by
    apply MultilinearMap.ext_of_span_eq_top
      (g := fun {_ : Fin b} (x : V) => symMonomial a V (fun _ => x))
      (fun _ => span_purePowers_eq_top a V)
    intro u
    exact (hμ u).trans (hν u).symm
  apply symPow_linearMap_ext b (SymPow a V)
  intro x
  exact DFunLike.congr_fun h x

/-- Surjectivity and uniqueness with the map specified solely by the paper's rule. -/
theorem paper_surjectivity
    (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a b : ℕ) (ha : 2 ≤ a) (hab : a * (a - 1) ≤ b) :
    ∃! μ : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V),
      Function.Surjective μ ∧
      ∀ u : Fin b → V,
        μ (symMonomial b (SymPow a V) (fun j => symMonomial a V (fun _ => u j))) =
          symMonomial a (SymPow b V) (fun _ => symMonomial b V u) := by
  obtain ⟨μ, hμ, hsurj, _⟩ := canonical_foulkes_howe_surjective V a b ha hab
  have hdiag := IsFoulkesMap.map_diagonal a b V μ hμ
  exact ⟨μ, ⟨hsurj, hdiag⟩, fun ν hν => map_unique_of_pure_rule V a b ν μ hν.2 hdiag⟩

#print axioms symPowSubmodule_eq_power
#print axioms homogeneous_preimage_mem
#print axioms polynomial_evaluation
#print axioms homogeneous_polynomial_vanishing
#print axioms homogeneous_polynomial_function_vanishing
#print axioms map_unique_of_pure_rule
#print axioms paper_surjectivity
#check homogeneous_polynomial_vanishing
#check homogeneous_polynomial_function_vanishing
#check paper_surjectivity

end FoulkesHoweVerification
