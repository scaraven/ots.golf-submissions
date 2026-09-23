import Mathlib

/-! The abstract graph numbers chains in execution order. The wire stores the eight wide blocks
in the same order, followed by the 24 narrow blocks of 160 bits in a fixed permuted order: the
`b`-th narrow chain in execution order occupies wire block `wireBlock b`. Block `23`, the top
edge of the wire, belongs to the narrow chain hashed in place (`b = 4`); the others are laid out
so that no chain hash overwrites a block that is still unread. `index` maps a graph-order bit to
its wire bit and `unindex` inverts it; malformed payloads (of any other length) are left
unchanged. -/

namespace OptimalOTS.Payload

/-- Wire block of the `b`-th narrow chain in execution order. -/
def wireBlock (b : ℕ) : ℕ := if b = 4 then 23 else if b < 4 then 22 - b else 23 - b

/-- Execution-order position of the narrow chain stored in wire block `q`. -/
def payloadBlock (q : ℕ) : ℕ := if q = 23 then 4 else if 19 ≤ q then 22 - q else 23 - q

theorem wireBlock_le (b : ℕ) : wireBlock b ≤ 23 := by
  unfold wireBlock
  split_ifs <;> omega

theorem payloadBlock_le (q : ℕ) : payloadBlock q ≤ 23 := by
  unfold payloadBlock
  split_ifs <;> omega

theorem payloadBlock_wireBlock' : ∀ b : Fin 24, payloadBlock (wireBlock b) = b := by
  decide +kernel

theorem wireBlock_payloadBlock' : ∀ q : Fin 24, wireBlock (payloadBlock q) = q := by
  decide +kernel

theorem payloadBlock_wireBlock (b : ℕ) (hb : b < 24) : payloadBlock (wireBlock b) = b :=
  payloadBlock_wireBlock' ⟨b, hb⟩

theorem wireBlock_payloadBlock (q : ℕ) (hq : q < 24) : wireBlock (payloadBlock q) = q :=
  wireBlock_payloadBlock' ⟨q, hq⟩

/-- Graph-order (cursor) bit `i` ↦ the wire bit that holds it. -/
def index (len i : ℕ) : ℕ :=
  if len = 5376 ∧ 1536 ≤ i ∧ i < 5376 then
    1536 + 160 * wireBlock ((i - 1536) / 160) + (i - 1536) % 160
  else i

/-- Wire bit `i` ↦ the graph-order bit it holds. -/
def unindex (len i : ℕ) : ℕ :=
  if len = 5376 ∧ 1536 ≤ i ∧ i < 5376 then
    1536 + 160 * payloadBlock ((i - 1536) / 160) + (i - 1536) % 160
  else i

theorem div_mod_160 (q r : ℕ) (hr : r < 160) :
    (160 * q + r) / 160 = q ∧ (160 * q + r) % 160 = r :=
  ⟨by omega, by omega⟩

/-- Every bit of the narrow region is a block number and an offset inside the block. -/
theorem block_rep (i : ℕ) (h1 : 1536 ≤ i) (h2 : i < 5376) :
    ∃ b r, b < 24 ∧ r < 160 ∧ i = 1536 + 160 * b + r :=
  ⟨(i - 1536) / 160, (i - 1536) % 160, by omega, by omega, by omega⟩

theorem index_block (b r : ℕ) (hb : b < 24) (hr : r < 160) :
    index 5376 (1536 + 160 * b + r) = 1536 + 160 * wireBlock b + r := by
  have hc : 5376 = 5376 ∧ 1536 ≤ 1536 + 160 * b + r ∧ 1536 + 160 * b + r < 5376 :=
    ⟨rfl, by omega, by omega⟩
  have e : 1536 + 160 * b + r - 1536 = 160 * b + r := by omega
  have hd := div_mod_160 b r hr
  unfold index
  rw [if_pos hc, e, hd.1, hd.2]

theorem unindex_block (q r : ℕ) (hq : q < 24) (hr : r < 160) :
    unindex 5376 (1536 + 160 * q + r) = 1536 + 160 * payloadBlock q + r := by
  have hc : 5376 = 5376 ∧ 1536 ≤ 1536 + 160 * q + r ∧ 1536 + 160 * q + r < 5376 :=
    ⟨rfl, by omega, by omega⟩
  have e : 1536 + 160 * q + r - 1536 = 160 * q + r := by omega
  have hd := div_mod_160 q r hr
  unfold unindex
  rw [if_pos hc, e, hd.1, hd.2]

/-- The wide region is not permuted. -/
theorem index_low (i : ℕ) (hi : i < 1536) : index 5376 i = i := by
  have h : ¬ (5376 = 5376 ∧ 1536 ≤ i ∧ i < 5376) := fun ⟨_, h1, _⟩ => by omega
  unfold index
  rw [if_neg h]

theorem index_lt (len i : ℕ) (hi : i < len) : index len i < len := by
  by_cases h : len = 5376 ∧ 1536 ≤ i ∧ i < 5376
  · obtain ⟨rfl, h1, h2⟩ := h
    obtain ⟨b, r, hb, hr, rfl⟩ := block_rep i h1 h2
    rw [index_block b r hb hr]
    have := wireBlock_le b
    omega
  · unfold index
    rw [if_neg h]
    exact hi

theorem unindex_lt (len i : ℕ) (hi : i < len) : unindex len i < len := by
  by_cases h : len = 5376 ∧ 1536 ≤ i ∧ i < 5376
  · obtain ⟨rfl, h1, h2⟩ := h
    obtain ⟨q, r, hq, hr, rfl⟩ := block_rep i h1 h2
    rw [unindex_block q r hq hr]
    have := payloadBlock_le q
    omega
  · unfold unindex
    rw [if_neg h]
    exact hi

theorem unindex_index (len i : ℕ) (hi : i < len) : unindex len (index len i) = i := by
  by_cases h : len = 5376 ∧ 1536 ≤ i ∧ i < 5376
  · obtain ⟨rfl, h1, h2⟩ := h
    obtain ⟨b, r, hb, hr, rfl⟩ := block_rep i h1 h2
    have hw : wireBlock b < 24 := by have := wireBlock_le b; omega
    rw [index_block b r hb hr, unindex_block (wireBlock b) r hw hr, payloadBlock_wireBlock b hb]
  · have e : index len i = i := by
      unfold index
      rw [if_neg h]
    rw [e]
    unfold unindex
    rw [if_neg h]

theorem index_unindex (len i : ℕ) (hi : i < len) : index len (unindex len i) = i := by
  by_cases h : len = 5376 ∧ 1536 ≤ i ∧ i < 5376
  · obtain ⟨rfl, h1, h2⟩ := h
    obtain ⟨q, r, hq, hr, rfl⟩ := block_rep i h1 h2
    have hp : payloadBlock q < 24 := by have := payloadBlock_le q; omega
    rw [unindex_block q r hq hr, index_block (payloadBlock q) r hp hr, wireBlock_payloadBlock q hq]
  · have e : unindex len i = i := by
      unfold unindex
      rw [if_neg h]
    rw [e]
    unfold index
    rw [if_neg h]

/-- Graph-order payload of a wire payload (the decoding direction). -/
def permute (bits : List Bool) : List Bool :=
  List.ofFn fun i : Fin bits.length => bits[index bits.length i.val]'(index_lt _ _ i.isLt)

/-- Wire payload of a graph-order payload (the encoding direction). -/
def unpermute (bits : List Bool) : List Bool :=
  List.ofFn fun i : Fin bits.length => bits[unindex bits.length i.val]'(unindex_lt _ _ i.isLt)

@[simp] theorem length_permute (bits : List Bool) : (permute bits).length = bits.length := by
  simp [permute]

@[simp] theorem length_unpermute (bits : List Bool) : (unpermute bits).length = bits.length := by
  simp [unpermute]

@[simp] theorem getElem_permute (bits : List Bool) (i : ℕ) (hi : i < (permute bits).length) :
    (permute bits)[i] = bits[index bits.length i]'(index_lt _ _ (by simpa using hi)) := by
  simp [permute]

@[simp] theorem getElem_unpermute (bits : List Bool) (i : ℕ) (hi : i < (unpermute bits).length) :
    (unpermute bits)[i] = bits[unindex bits.length i]'(unindex_lt _ _ (by simpa using hi)) := by
  simp [unpermute]

@[simp] theorem permute_unpermute (bits : List Bool) : permute (unpermute bits) = bits := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [getElem_permute, getElem_unpermute, length_unpermute, unindex_index _ _ h2]

@[simp] theorem unpermute_permute (bits : List Bool) : unpermute (permute bits) = bits := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [getElem_unpermute, getElem_permute, length_permute, index_unindex _ _ h2]

theorem unpermute_injective : Function.Injective unpermute :=
  Function.LeftInverse.injective permute_unpermute

end OptimalOTS.Payload
