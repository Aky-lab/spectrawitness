import SpectralGraph.Graph.EncodingCheck
import SpectralGraph.Graph.PackedEnumerationFast

/-! Representation invariants of executable graph extension and enumeration.
The extension writes exactly n+1 bounded rows and preserves old stored loop bits.
Consequently a valid packed input stays valid, and both graph generators produce
strictly valid packed encodings without an additional runtime validity assumption. -/
namespace SpectralGraph.Graph

@[simp] theorem extendPackedRows_size {n : Nat} (rows : PackedAdjacencyRows)
    (S : Finset (Fin n)) : (extendPackedRows rows S).size = n + 1 := by
  simp [extendPackedRows]

/-- Masking and writing the new bit ensures every output row is in range,
independently of whether the input data obeyed the storage contract. -/
theorem packedAdjacencyRow_extend_lt {n : Nat} (rows : PackedAdjacencyRows)
    (S : Finset (Fin n)) (i : Fin (n + 1)) :
    packedAdjacencyRow (extendPackedRows rows S) i.val < 2 ^ (n + 1) := by
  have hpow : 2 ^ n < 2 ^ (n + 1) := by
    have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
    rw [Nat.pow_succ]
    omega
  refine Fin.lastCases ?_ (fun u ↦ ?_) i
  · simp
  · rw [Fin.val_castSucc, packedAdjacencyRow_extend_old]
    apply Nat.or_lt_two_pow
    · exact (Nat.mod_lt _ (Nat.two_pow_pos n)).trans hpow
    · split_ifs
      · exact hpow
      · exact Nat.two_pow_pos (n + 1)

/-- Stored loops are the only input defect that survives one-vertex extension.
Dimensions and high bits are rebuilt, while the old diagonal bits are preserved. -/
theorem packedRowsValid_extend_iff {n : Nat} (rows : PackedAdjacencyRows)
    (S : Finset (Fin n)) :
    PackedRowsValid (n + 1) (extendPackedRows rows S) ↔
      ∀ i : Fin n, packedAdjacencyBit rows i.val i.val = false := by
  constructor
  · intro h i
    simpa using (h.2 i.castSucc).2
  · intro h
    refine ⟨extendPackedRows_size rows S, fun i ↦ ⟨packedAdjacencyRow_extend_lt rows S i, ?_⟩⟩
    refine Fin.lastCases ?_ (fun u ↦ ?_) i
    · simp [packedAdjacencyBit]
    · simpa using h u

/-- Valid packed inputs remain valid after adjoining any neighbor selection. -/
theorem PackedRowsValid.extend {n : Nat} {rows : PackedAdjacencyRows}
    (h : PackedRowsValid n rows) (S : Finset (Fin n)) :
    PackedRowsValid (n + 1) (extendPackedRows rows S) :=
  (packedRowsValid_extend_iff rows S).mpr (fun i ↦ (h.2 i).2)

/-- Every candidate generated from valid parent encodings satisfies the strict
storage contract; no connectivity or degree hypothesis is needed for this invariant. -/
theorem packedDegreeExtensionCandidates_valid (n d : Nat)
    (parents : List PackedAdjacencyRows)
    (hparents : ∀ rows ∈ parents, PackedRowsValid n rows)
    {child : PackedAdjacencyRows}
    (hchild : child ∈ packedDegreeExtensionCandidates n d parents) :
    PackedRowsValid (n + 1) child := by
  obtain ⟨rows, hr, S, _, rfl⟩ :=
    (mem_packedDegreeExtensionCandidates n d parents child).mp hchild
  exact (hparents rows hr).extend S

/-- Strict packed-data validity is an invariant of the full reference enumeration. -/
theorem packedConnectedDegreeGraphs_valid (n d : Nat)
    {rows : PackedAdjacencyRows} (hr : rows ∈ packedConnectedDegreeGraphs n d) :
    PackedRowsValid n rows := by
  induction n generalizing rows with
  | zero => simp [packedConnectedDegreeGraphs] at hr
  | succ n ih =>
    cases n with
    | zero =>
      simp only [packedConnectedDegreeGraphs, List.mem_singleton] at hr
      subst rows
      decide
    | succ n =>
      exact packedDegreeExtensionCandidates_valid (n + 1) d _ (fun _ h ↦ ih h) hr

/-- The optimized enumeration inherits strict validity from its exact
output-membership agreement with the reference generator. -/
theorem packedConnectedDegreeGraphsFast_valid (n d : Nat)
    {rows : PackedAdjacencyRows} (hr : rows ∈ packedConnectedDegreeGraphsFast n d) :
    PackedRowsValid n rows :=
  packedConnectedDegreeGraphs_valid n d ((mem_packedConnectedDegreeGraphsFast_iff n d rows).mp hr)

/-- The generic invariant discharges every reference output's Boolean validity
check without requiring a separate concrete evaluation of the census. -/
theorem packedConnectedDegreeGraphs_all_valid (n d : Nat) :
    (packedConnectedDegreeGraphs n d).all (packedRowsValid n) = true := by
  apply List.all_eq_true.mpr
  intro rows hr
  exact (packedRowsValid_eq_true_iff n rows).mpr (packedConnectedDegreeGraphs_valid n d hr)

theorem packedConnectedDegreeGraphsFast_all_valid (n d : Nat) :
    (packedConnectedDegreeGraphsFast n d).all (packedRowsValid n) = true := by
  apply List.all_eq_true.mpr
  intro rows hr
  exact (packedRowsValid_eq_true_iff n rows).mpr (packedConnectedDegreeGraphsFast_valid n d hr)

end SpectralGraph.Graph
