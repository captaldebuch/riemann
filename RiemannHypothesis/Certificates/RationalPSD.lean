import Mathlib

/-!
# Rational Positive Semidefinite (PSD) Infrastructure

This file isolates the exact rational finite matrix algebra from the specific 
analytic and geometric routes of the Riemann Hypothesis.
By defining the `RationalPSDWitness` interface here, it can be seamlessly reused 
by the Nyman-Beurling approximation distances, Weil kernel positivites, 
and Connes finite trace computations.
-/

namespace RH.Certificates

open scoped BigOperators

/-- A rational matrix is Positive Semidefinite (PSD) if its associated quadratic form is non-negative. -/
def RationalMatrixPSD {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) : Prop :=
  ∀ x : Fin n → ℚ, 0 ≤ ∑ i, x i * (M.mulVec x) i

/-- 
A computable witness of positive-semidefiniteness via an exact LDLᵀ decomposition.
Because L and D are rational, Lean can verify this identity exactly via `norm_num`.
-/
structure RationalPSDWitness (n : ℕ) where
  M : Matrix (Fin n) (Fin n) ℚ
  L : Matrix (Fin n) (Fin n) ℚ
  D : Fin n → ℚ
  diagonal_nonneg : ∀ i, 0 ≤ D i
  ldl_identity : M = L * Matrix.diagonal D * L.transpose

/-- 
The explicit formal theorem that an LDLᵀ decomposition implies PSD.
This proves that the algebraic identity `M = L * D * Lᵀ` translates
exactly into `RationalMatrixPSD`.
-/
theorem psd_from_ldl_witness {n : ℕ} (W : RationalPSDWitness n) :
    RationalMatrixPSD W.M := by
  intro x
  have h0 : (∑ i, x i * (W.M.mulVec x) i) = dotProduct x (W.M.mulVec x) := rfl
  rw [h0]
  rw [W.ldl_identity]
  have h1 : (W.L * (Matrix.diagonal W.D * W.L.transpose)).mulVec x = 
            W.L.mulVec ((Matrix.diagonal W.D * W.L.transpose).mulVec x) := (Matrix.mulVec_mulVec _ _ _).symm
  rw [Matrix.mul_assoc, h1]
  rw [Matrix.dotProduct_mulVec]
  have h2 : (Matrix.diagonal W.D * W.L.transpose).mulVec x = 
            (Matrix.diagonal W.D).mulVec (W.L.transpose.mulVec x) := (Matrix.mulVec_mulVec _ _ _).symm
  rw [h2]
  have h3 : Matrix.vecMul x W.L = W.L.transpose.mulVec x := by
    funext i
    dsimp [Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.transpose]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h3]
  let y := W.L.transpose.mulVec x
  have h4 : dotProduct y ((Matrix.diagonal W.D).mulVec y) = ∑ i : Fin n, W.D i * (y i)^2 := by
    dsimp [dotProduct, Matrix.mulVec, Matrix.diagonal]
    apply Finset.sum_congr rfl
    intro i _
    have h5 : (∑ j : Fin n, (if i = j then W.D i else 0) * y j) = W.D i * y i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hij
        have : (if i = j then W.D i else 0) = 0 := if_neg hij.symm
        rw [this, zero_mul]
      · intro hi
        simp at hi
    rw [h5]
    ring
  rw [h4]
  apply Finset.sum_nonneg
  intro i _
  have hD := W.diagonal_nonneg i
  have hy := sq_nonneg (y i)
  positivity

/--
A certificate mapping a regularized matrix back to an original un-regularized matrix.
Useful when numerical Gram matrix inversion required a small diagonal shift.
-/
structure RegularizedPSDCertificate (n : ℕ) where
  originalMatrix : Matrix (Fin n) (Fin n) ℚ
  epsilon : ℚ
  regularizedMatrix : Matrix (Fin n) (Fin n) ℚ
  regularized_eq : regularizedMatrix = originalMatrix + epsilon • 1
  epsilon_nonneg : 0 ≤ epsilon
  witness : RationalPSDWitness n
  witness_matches : witness.M = regularizedMatrix

end RH.Certificates
