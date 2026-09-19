import SpectralGraph.Certificate.RankOneUpdate

namespace SpectralGraphTests.RankOneUpdate
open SpectralGraph SpectralGraph.Certificate SpectralGraph.Inertia Matrix

/-- The shifted empty graph Laplacian on three vertices. -/
def base : Matrix (Fin 3) (Fin 3) ℚ := -1
/-- Adding an edge of weight `c` adds `c (e₀-e₁)(e₀-e₁)ᵀ` to its Laplacian. -/
def edge : Fin 3 → ℚ := ![1, -1, 0]
def solution : Fin 3 → ℚ := ![-1, 1, 0]

example : checkRankOneUpdate base base edge solution (1/4) (-2)
    ⟨0, 0, 3⟩ ⟨0, 0, 3⟩ = true := by decide +kernel
example : checkRankOneUpdate base base edge solution (1/2) (-2)
    ⟨0, 0, 3⟩ ⟨0, 1, 2⟩ = true := by decide +kernel
example : checkRankOneUpdate base base edge solution 1 (-2)
    ⟨0, 0, 3⟩ ⟨1, 0, 2⟩ = true := by decide +kernel
example : checkRankOneUpdate base base edge solution (1/2) (-2)
    ⟨0, 0, 3⟩ ⟨1, 0, 2⟩ = false := by decide +kernel
example : checkRankOneUpdate base base edge 0 1 (-2)
    ⟨0, 0, 3⟩ ⟨1, 0, 2⟩ = false := by decide +kernel
example : checkRankOneUpdate base 0 edge solution 1 (-2)
    ⟨0, 0, 3⟩ ⟨1, 0, 2⟩ = false := by decide +kernel
example : checkRankOneUpdate base base edge solution 0 (-2)
    ⟨0, 0, 3⟩ ⟨0, 0, 3⟩ = false := by decide +kernel
example : checkRankOneUpdate (0 : Matrix (Fin 3) (Fin 3) ℚ) 0 0 0 1 0
    ⟨0, 3, 0⟩ ⟨0, 3, 0⟩ = false := by decide +kernel

/-- Certify the base once, then reuse it for every edge weight. -/
theorem base_inertia : matrixInertia (ratCastMatrix base) = ⟨0, 0, 3⟩ := by
  have he : ratCastMatrix base = -(1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [ratCastMatrix, base, hij]
  rw [he, matrixInertia_neg, matrixInertia_one]
  simp

/-- A checked solve detects the exact singular edge weight. -/
theorem edge_at_transition :
    matrixInertia (ratCastMatrix base + (1/2 : ℝ) •
      vecMulVec (fun i ↦ (edge i : ℝ)) (fun i ↦ (edge i : ℝ))) = ⟨0, 1, 2⟩ := by
  simpa using checkRankOneUpdate_sound base base edge solution (1/2) (-2)
    ⟨0, 0, 3⟩ ⟨0, 1, 2⟩ base_inertia (by decide +kernel)

/-- Crossing the transition changes the full signature by two. -/
theorem edge_past_transition :
    matrixInertia (ratCastMatrix base + (1 : ℝ) •
      vecMulVec (fun i ↦ (edge i : ℝ)) (fun i ↦ (edge i : ℝ))) = ⟨1, 0, 2⟩ := by
  simpa using checkRankOneUpdate_sound base base edge solution 1 (-2)
    ⟨0, 0, 3⟩ ⟨1, 0, 2⟩ base_inertia (by decide +kernel)

#print axioms edge_at_transition
#print axioms edge_past_transition
end SpectralGraphTests.RankOneUpdate
