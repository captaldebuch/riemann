import Mathlib

open scoped BigOperators
open Matrix

namespace RH.Certificates

def RationalMatrixPSD {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) : Prop :=
  ∀ x : Fin n → ℚ, 0 ≤ dotProduct x (M.mulVec x)

structure RationalPSDWitness (n : ℕ) where
  M : Matrix (Fin n) (Fin n) ℚ
  L : Matrix (Fin n) (Fin n) ℚ
  D : Fin n → ℚ
  diagonal_nonneg : ∀ i, 0 ≤ D i
  ldl_identity : M = L * Matrix.diagonal D * L.transpose

theorem psd_from_ldl_witness {n : ℕ} (W : RationalPSDWitness n) :
    RationalMatrixPSD W.M := by
  intro x
  rw [W.ldl_identity]
  -- We want to show 0 ≤ dotProduct x ((L * D * Lᵀ).mulVec x)
  have h1 : (W.L * (Matrix.diagonal W.D * W.L.transpose)).mulVec x = 
            W.L.mulVec ((Matrix.diagonal W.D * W.L.transpose).mulVec x) := (Matrix.mulVec_mulVec _ _ _).symm
  rw [Matrix.mul_assoc, h1]
  rw [dotProduct_mulVec]
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

end RH.Certificates
