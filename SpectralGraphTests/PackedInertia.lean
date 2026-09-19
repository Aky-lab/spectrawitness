import SpectralGraph.Graph.PackedInertia

open SpectralGraph SpectralGraph.Graph

example : checkPackedInertia 3 #[2, 4, 0] 0 ⟨1, 1, 1⟩ = true := by decide +kernel
example : checkPackedInertia 3 #[2, 5, 2] 1 ⟨1, 0, 2⟩ = true := by decide +kernel
example : checkPackedInertia 3 #[2, 4, 0] (-1) ⟨2, 0, 1⟩ = true := by decide +kernel
example : checkPackedInertia 0 #[] 7 ⟨0, 0, 0⟩ = true := by decide +kernel
example : checkPackedInertia 3 #[2, 4] 0 ⟨1, 1, 1⟩ = false := by decide +kernel
example : checkPackedInertia 3 #[2, 4, 0, 0] 0 ⟨1, 1, 1⟩ = false := by decide +kernel
example : checkPackedInertia 3 #[3, 4, 0] 0 ⟨1, 1, 1⟩ = false := by decide +kernel
example : checkPackedInertia 3 #[10, 4, 0] 0 ⟨1, 1, 1⟩ = false := by decide +kernel
example : checkPackedInertia 3 #[2, 4, 0] 0 ⟨3, 0, 0⟩ = false := by decide +kernel

example : matrixInertia ((graphOfPackedRows 3 #[2, 4, 0]).adjMatrix ℝ -
    (1 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) = ⟨1, 0, 2⟩ := by
  simpa using checkPackedInertia_sound 3 #[2, 4, 0] 1 ⟨1, 0, 2⟩ (by decide +kernel)
