import Submissions.UpperRiscv.MixedContext
import Submissions.UpperRiscv.Payload

namespace OptimalOTS.RiscvMixedProgram
open RiscvZkvm.Rv64
open Riscv2Program (W W_toNat)
open Forest

/-- Cursor in the graph's payload order, including the final cursor at chain 32. -/
def cursor (k : ℕ) : ℕ := if k < 8 then 192*k else 1536+160*(k-8)
/-- Offset in the wire payload; the narrow blocks occur in the order `Payload.wireBlock`. -/
def wireOffset (k : ℕ) : ℕ := if k < 8 then 192*k else 1536+160*Payload.wireBlock (k-8)

theorem cursor_step (k : Fin 32) : cursor (k.val+1) = cursor k + chainBits k := by
  unfold cursor chainBits
  split_ifs <;> omega

theorem cursor_zero : cursor 0 = 0 := rfl
theorem cursor_end : cursor 32 = 5376 := by decide

theorem wireOffset_aligned (k : Fin 32) : wireOffset k % 8 = 0 := by
  unfold wireOffset; split_ifs <;> omega

theorem wireOffset_contained (k : Fin 32) : wireOffset k + chainBits k ≤ 5376 := by
  have := k.isLt
  have := Payload.wireBlock_le (k.val - 8)
  unfold wireOffset chainBits; split_ifs <;> omega

theorem wireSlot_eq (k : Fin 32) : wireSlot k = 0x400040 + wireOffset k / 8 := by
  have := k.isLt
  unfold wireSlot slot physical narrow wireOffset
  simp only [decide_eq_true_eq]
  split_ifs <;> omega

theorem slot_bounds (k : Fin 32) :
    0x400040 ≤ slot k ∧ slot k + 24 ≤ 0x400348 ∧ slot k % 8 = 0 := by
  have := k.isLt
  unfold slot physical narrow
  simp only [decide_eq_true_eq]
  split_ifs <;> omega

theorem output_bounds (k : Fin 32) :
    0x400038 ≤ outAddr k ∧ outAddr k + 32 ≤ 0x400348 ∧ outAddr k % 8 = 0 := by
  have h := slot_bounds k
  unfold outAddr; omega

/-- The state of every chain begins `truncOff k / 8` bytes into its answer buffer. -/
theorem work_eq' : ∀ k : Fin 32, work k = outAddr k + truncOff k / 8 := by
  decide +kernel

theorem work_of_expands {k : ℕ} (h : expands k = true) : work k = slot k := by
  unfold work
  exact if_pos h

theorem work_of_not_expands {k : ℕ} (h : ¬ expands k = true) : work k = wireSlot k := by
  unfold work
  exact if_neg h

theorem work_bounds' : ∀ k : Fin 32, 32 ≤ work k ∧ work k + 24 ≤ 0x78000000 := by
  decide +kernel

theorem unread_disjoint' : ∀ k j : Fin 32, k.val < j.val →
    wireSlot j + chainBits j / 8 ≤ outAddr k ∨ outAddr k + 32 ≤ wireSlot j := by
  decide +kernel

/-- No chain hash overwrites a later, unread wire block. -/
theorem unread_disjoint (k j : Fin 32) (hkj : k.val < j.val) :
    wireSlot j + chainBits j / 8 ≤ outAddr k ∨ outAddr k + 32 ≤ wireSlot j :=
  unread_disjoint' k j hkj

/-- Position of the bytes committed by the root for a completed chain. -/
def rootSliceAddr (k : ℕ) : ℕ := if k < 8 ∨ k = 31 then outAddr k else slot k
def rootSliceBits (k : ℕ) : ℕ := if k = 7 ∨ k = 31 then 256 else 192

/-- Every later hash preserves the committed slice of an earlier chain. -/
theorem completed_disjoint (j k : Fin 32) (hjk : j.val < k.val) :
    rootSliceAddr j + rootSliceBits j / 8 ≤ outAddr k ∨
      outAddr k + 32 ≤ rootSliceAddr j := by
  have := k.isLt; have := j.isLt
  unfold rootSliceAddr rootSliceBits outAddr slot physical narrow
  simp only [decide_eq_true_eq]
  split_ifs <;> omega

theorem payload_index (k : Fin 32) (i : ℕ) (hi : i < chainBits k) :
    Payload.index 5376 (cursor k + i) = wireOffset k + i := by
  have hk := k.isLt
  unfold cursor wireOffset
  by_cases h8 : k.val < 8
  · have hb : chainBits k = 192 := by unfold chainBits; rw [if_pos h8]
    rw [if_pos h8, if_pos h8]
    exact Payload.index_low _ (by omega)
  · have hb : chainBits k = 160 := by unfold chainBits; rw [if_neg h8]
    rw [if_neg h8, if_neg h8]
    exact Payload.index_block (k.val - 8) i (by omega) (by omega)

end OptimalOTS.RiscvMixedProgram
