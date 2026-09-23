# In-place edge chain: 371-cycle candidate

This extends the 372-cycle dense-dispatch record (PR #27 by alexanderlhicks, which builds
on dhsorens's paired dispatch and the 377/393-cycle optimizations credited below). The
notes of the 372 construction follow unchanged after this section.

Assisted by: Claude Opus 5.5 (Anthropic)

## What changes (372 -> 371)

- **Machine.** Chain 12 (tile 27) is hashed in place at the wire's top edge, `x10 = 652`,
  `x12 = 648`. Its block `[648, 680)` covers the already-consumed tail of tile 31's wire
  value and the 8 bytes above the signature, which hold only tile 28's dead spill. Its next state is answer bytes `[4, 24)`,
  so `truncOff 12 = 32`. `prologue 6` loses its expansion ECALL and redirect, and pair
  6's fine ladder has 16 ECALLs. Only the redirect is saved: 23 redirects instead of 24.
- **Wire order.** Narrow tiles 8-26 keep blocks 0-18, tile 27 moves to block 23 and
  tiles 28-31 move to blocks 19-22 (`Payload.wireBlock`, inverse `Payload.payloadBlock`).
  The payload map is no longer an involution, so the adapter encodes with `unpermute` and
  decodes with `permute`.
- **Packing.** Group 4 is `[10, 14, 6]`: pair 6 (26-41 instructions) takes the
  48-instruction slot, pair 14 (25-40) the middle one, `jumpImm 14 = 160`. Every other
  row, capacity and base constant is unchanged apart from pair 6's base lane. The image
  still has 12338 instructions and 104 data bytes.
- **Root.** Unchanged. Tile 27's retained answer bytes `[8, 32)` land at `[656, 680)`
  exactly as before, so `R`, `rootCat` and the 13-block root hash are untouched.
- **Accounting.** 40 + (189 + 64 + 23 + 32 + 1 = 309) + 22 = 371.

## Proof changes

- `Payload`: `wireBlock`/`payloadBlock` with inverse laws checked by `decide +kernel`
  over `Fin 24`; `index`/`unindex` and `permute`/`unpermute` are mutually inverse.
- `Names.truncOff` and `trunc` at `min (truncOff k) (w - chainBits k)`. `Values` adds
  `card_filter_extract_le`, which bounds 256-bit words with a fixed `c`-bit window at
  any offset. `card_filter_trunc_le'` and `card_filter_rootSlice_le` now go through it.
  No other security file reads the offset.
- `MixedProgram`: `expands`, `work`, the new `wireSlot`, `withinGroup` and
  `groupPairs`. The machine invariants (`HashInv`, `HoldsAt`, `Prepared`, dispatch,
  landing) are stated at `work k`. `MixedLayout.work_eq'` (`work k = outAddr k +
  truncOff k / 8`) and `unread_disjoint'` are kernel checks over all chains.
- `MixedCost`/`MixedPair`/`MixedPhase`: 23 early hashes, per-pair overhead 120, chains 309.

## Validation status

Checked **only by our private CI**: a GitHub Actions build of
`Submissions.UpperRiscv.Solution` against the pinned `.contract`, with policy and axiom
checks. It has **not** been checked by the hosted ots.golf verifier. The Python emulator
of this image (`.work/imb/sim/inplace_variants.py --variant N1` in our working tree, not
part of this root) measured 371 = 40/309/22 on every accepted input and at most 371 on
rejects. It rejected all exhaustive single-bit flips, and replaying byte tags found no
clobbered unread input.

---

# Dense dispatch: 372-cycle candidate

This extends Alexander Hicks's officially verified 377-cycle mixed-width submission
(PR #26, commit 7635add16c45b513b8afe37f6b3b3916e55b0fae), which builds on dhsorens's
paired-dispatch construction and the earlier 393-cycle fold optimization.

Assisted by: GPT-6 (Codex)

## What changes

The 377 image reserves 64 instructions per pair body and packs two bodies into a
128-instruction coarse-digit row. It uses two 5/3-bit digit pairs to keep that image
within the reach of halfword-based dispatch. Here up to three bodies share a row,
so the scheme can use 32 four-bit digits and accepted sum 157 instead of 160.
That removes three chain hashes without reducing the nonce or state widths.

Pair groups are `[0,1,2]`, `[3]`, `[8,4,12]`, `[9,5,13]`, `[10,6,14]`, `[11,7,15]`.
Every group has 16 rows of 128 instructions. Body starts are at offsets 0, 40 and 80
instructions. Pair 3 occupies a row on its own because its continuation changes the
hash-input width. Ordinary wide bodies need at most 38 instructions, pair 3 needs 41,
ordinary narrow bodies need 40, and the final body needs 47. This preserves the
`4*dA + 512*dB` displacement. Pairs 8/12 through 11/15 differ by 320 bytes, allowing
the final dispatch word to reuse the third word's base constants.

The masks are now identical in all four index-answer words, so one load is removed.
For each accumulated 16-bit lane the fine and coarse sums are each at most 60.
After division by four, the shifted addition has alternating seven- and nine-bit
cells: a fine-plus-coarse sum is below 128, and each intervening field is below 512.
Thus `SRLI 7; ADD; AND 0x01fc` replaces the two-mask fold. REMU 65535 then sums the
four lanes. `MixedLanes.fold_fields` factors the arithmetic into small digit and
quotient lemmas to keep proof checking economical.

The 128-bit nonce, 8 wide/24 narrow state split, reverse expansion, and 6272-bit root
input are unchanged. The proved accounting is:

- Index phase: 40 cycles.
- Chains: 189 hashes + 64 pointer instructions + 24 redirects + 32 dispatch
  instructions + one width change = 310 cycles.
- Root hash and decision: 22 cycles.
- Total: 372 cycles; 12338 instructions + 104 data bytes = 49456 bytes.

## Validation status

The Python prototype passes 6170 full-transcript cases, eight honest signing/key
cases and 528 signature mutations (6706 in total). Seven fixtures replay through
the pinned RISC-V loader and instruction/hash semantics. The Lean image exactly
matches the generator. These checks supplement the universal proof.

The complete public 372-cycle certificate and image-size theorem compile with the
pinned Lean toolchain: `lake build Submissions.UpperRiscv.Solution` passes (8900 jobs).
The exported submission, certificate, image-size theorem and machine refinement use
only `propext`, `Classical.choice` and `Quot.sound`. The full proof includes security,
signing availability and exact oracle-computation refinement on every raw input.

The local production verifier was attempted, but stopped before proof checking:
this Linux host lacks the required dedicated filesystem of at most 64 GiB for
`OTS_WORK_DIR`. Its isolation checks were not bypassed. The hosted comparator and
resource-limited verification are requested by this PR; no hosted verdict is claimed
in these submission notes.

## Rejected directions and next work

The earlier 375-cycle nonce-64 variant fails the quantitative security requirement:
a chosen-message collision attack exceeds the permitted bound by at least 7.28x.
This candidate retains the verified construction's 128-bit nonce. An earlier
mixed-state placement also corrupted four unread input bytes; retain the shifted
boundary and both full boundary tops in the root input.

The denser packing was missed by counting every body as a 64-instruction allocation.
It is distinct from dispatching three chain digits together: this still dispatches
two digits, while packing three independent bodies into one coarse-digit row.
Future work could explore dispatch encodings or a stronger availability/freshness
argument. Neither the histogram search nor these layouts establish a global optimum.

The score is not hardware latency or zkVM proving time. REMU may be expensive on a
physical core, and a zkVM must charge real arithmetic, memory and hash-precompile
traces. Fewer hashes and a smaller image are potentially useful across those models,
but no hardware or zkVM wall-time benchmark is claimed.
