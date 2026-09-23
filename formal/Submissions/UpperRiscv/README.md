# RISC-V upper bound: 371-cycle in-place edge chain

This candidate extends the 372-cycle dense-dispatch record (PR #27, by alexanderlhicks,
itself building on dhsorens's paired-dispatch construction). It removes one redirect
instruction from every accepted execution: **371 = 40 index + 309 chains + 22 root and
decision**, on every accepting run and as the bound on every run.

## The in-place narrow edge chain

The scheme is a WOTS-style one-time signature: 32 hash chains, 8 with 192-bit states
and 24 with 160-bit states, and one 4-bit digit per chain. Each chain is hashed in the
signature buffer itself. A hash reads the state at `x10` and writes its 256-bit answer
at `x12`; the next state is a slice of that answer, and the final answers of all chains
form the root input `R`. In the 372 record every narrow chain first *expands* its
160-bit wire value, which is packed at a 20-byte stride, into a 24-byte tile: the first
hash reads the packed value and writes the tile, and an `ADDI x10, x12, 8` (the
"redirect") points later hashes at the tile. That costs 24 redirects.

Here one narrow chain skips the expansion. Chain 12 (tile 27, the fine chain of pair 6)
is re-packed to the top edge of the wire, bytes `[652, 672)` after the nonce, and hashed
**in place**: `x10 = 652` and `x12 = 648` (8-byte aligned). Every hash of this chain
writes the block `[648, 680)`, and the next state is answer bytes `[4, 24)`, which is
again `[652, 672)`. This is safe because the block touches only

- `[648, 652)`, the tail of the wire value below it (tile 31, chain 8), which is
  processed earlier and so already consumed; and
- `[672, 680)`, just above the end of the 5504-bit signature. It holds only tile 28's
  spill, which neither `R` nor any unread input needs. The 372 record overwrote the same
  bytes when it expanded tile 27.

The chain's final answer leaves bytes `[8, 32)` at `[656, 680)`, exactly where the record
keeps tile 27's committed slice, so `R` and the root hash are unchanged. The chain needs
no expansion hash and no redirect. Its ladder has 16 hashes like a wide chain and it
still hashes `d + 1` times. The saving is one cycle.

Two layout changes make room for it:

- **Wire re-pack.** Narrow tile `p` stores its wire value at block `p - 8` for
  `p <= 26` (as before), block 23 for `p = 27`, and block `p - 9` for `p >= 28`.
  In execution order, narrow chain `b` is at `Payload.wireBlock b`. No hash overwrites
  a value that has not been read yet; `MixedLayout.unread_disjoint'` checks all 32 x 32
  chain pairs.
- **Group 4 swap.** Pair 6's copy body grows by one instruction, to between 26 and 41
  instructions, so it no longer fits a 40-instruction slot. Row group 4 becomes
  `[10, 14, 6]`: pair 6 takes the 48-instruction slot and pair 14 the middle slot.
  Pair 14's JALR immediate is now +160 rather than +320.

Accounting: 189 chain hashes, 64 pointer instructions, **23** redirects, 32 dispatch
instructions and one width change give 309 cycles for the chains. The index phase (40)
and root and decision (22) are unchanged. The image is still 12338 instructions and 104
data bytes (49456 bytes).

In the proof, `Payload` becomes a non-involutive permutation (`index`/`unindex`,
`permute`/`unpermute`). `Forest.truncOff` gives each chain's state offset in its answer
(64 bits, or 32 for chain 12), and `work k` is the chain's input address. A general
counting lemma `Values.card_filter_extract_le` bounds the security events at either offset.

**Validation status:** the claim has so far been checked **only by our private CI** (a
GitHub Actions build of `Submissions.UpperRiscv.Solution` against the pinned contract,
with an axiom check). The hosted ots.golf verifier has **not** checked it. Before any
Lean was written, a Python emulator of this exact image (`record + in-place edge chain`)
measured 371 = 40/309/22 on every accepted input and at most 371 on rejects. It also
rejected every exhaustive single-bit flip of a valid signature.

Assisted by: Claude Opus 5.5 (Anthropic).

---

## The 372-cycle base construction (text by its authors)

The candidate extends the verified 377-cycle mixed-width construction. It uses
thirty-two four-bit index digits with accepted sum 157, executes 189 chain hashes,
and packs up to three pair bodies into a 128-instruction dispatch row. The signature
still occupies 5504 bits, including a 128-bit nonce, eight 192-bit chain states and
twenty-four 160-bit states.

The coarse digit still selects a row with a 512-byte stride. Bodies start at row
offsets 0, 40 and 80 instructions; the final body may occupy 48 instructions. This
reduces code size enough to use the all-four-bit digit profile with halfword loads
and signed-immediate JALR dispatch. A shared digit mask removes one load, and the
bounded fine/coarse sums permit a single mask after the shifted addition, removing
one AND. REMU 65535 still performs the horizontal sum.

The proved bound is 40 cycles for index processing, 310 for all chain blocks and 22
for the root and decision. The image contains 12338 instructions and 104 data bytes:
49456 bytes. Hash work is 203 compressions; ordinary instructions contribute 169 cycles.

**Validation:** the full exported 372-cycle certificate and image-size theorem pass
the pinned Lean build (8900 jobs), with only the three permitted axioms. Independent
tests cover 6706 transcript cases, seven pinned-machine fixtures and exact image
equality. The PR requests official hosted validation; see `NOTES.md` for the local
production-wrapper infrastructure limitation.

The proof remains in the `Mixed*.lean` modules, with security and availability in the
shared graph/wire modules. `MixedProgram` defines the image; `MixedLanes` proves the
single-mask fold; `MixedCode` locates the packed bodies; `MixedVerifier`, `Candidate`
and `Solution` connect execution to the certified wire algorithm and export the claim.

See `NOTES.md` for layout details, validation and attribution.
Rules: [ots.golf/rules](https://ots.golf/rules).
