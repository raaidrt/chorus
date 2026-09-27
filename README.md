# chess_engine

A chess engine whose rules implementation is formally verified with [Verus](https://github.com/verus-lang/verus).

## Layout

| File | Role | Verified? |
|---|---|---|
| `src/spec.rs` | **The specification**: the FIDE rules as Verus `spec` functions (attacks, check, pseudo-legal and legal moves, castling, en passant, promotion, making a move, checkmate and stalemate, insufficient material, 50/75-move rules, threefold/fivefold repetition). | Trusted: review this |
| `src/types.rs` | Shared data types (`Piece`, `Square`, `Move`, ...). | ✓ |
| `src/position.rs` | Mailbox `Position` and its `View` into `spec::PositionModel`. | ✓ |
| `src/bitboard.rs` | Bitboards (`u64` square sets) and their bit lemmas. | ✓ |
| `src/attacks.rs` | `is_attacked_exec`, `in_check_exec`. | ✓ `== spec` |
| `src/movegen.rs` | `is_legal_exec`, `apply_move_exec`, `legal_moves_exec` (sound, complete, no duplicates). | ✓ `== spec` |
| `src/game.rs` | `Game` history, `outcome()`, `can_claim_draw()`, repetition counting. | ✓ `== spec` |
| `src/fen.rs` | FEN / UCI parsing and printing. | ✗ (I/O glue) |

The board stays a mailbox, but move generation works with bitboards:

* **Pieces.** One pass over the board gives the bitboard of the side to move's pieces and
  its king's square, and whether that king is in check (`scan_exec`).
* **Destinations.** For each piece, `dests` builds the bitboard of exactly its
  pseudo-legal destinations: knight and king steps (plus castling), pawn pushes and
  captures, and each slider ray up to its first blocker. The loops walk both bitboards
  lowest bit first (`trailing_zeros`), so moves come out in the same order as a scan of
  every (from, to) pair, which is what the completeness and no-duplicates proofs follow.
* **King safety.** A move of another piece, from a king that is not in check, can only
  expose the king along the line from the king through the square it leaves. So such a
  move needs no attack test unless it starts on a line through the king, and then only
  that one ray is checked (`lemma_discovered`, `lemma_discovered_ray`). King moves,
  en passant and moves out of check test the king's square on the new board.
* **Attacks.** `is_attacked_exec` looks outward from the square: the eight knight
  squares and the first piece along each of the eight rays (which covers adjacent kings
  and pawns). Before, it scanned all 64 squares for attackers.

Outcome detection stops at the first piece with a legal move, checks en passant with the
two pawns that could capture, and decides insufficient material in one pass. Further
optimizations must prove the same public `ensures` clauses.

Agents (and humans) working on the implementation must follow [`AGENTS.md`](AGENTS.md):
the specification is read-only and every implementation must be proven against it.

## Validating the spec

The executable code is proven equal to the spec, so the perft tests in
`tests/perft.rs` (reference counts from chessprogramming.org, ~20M leaf nodes)
test the **spec itself**. `tests/game.rs` covers end-of-game rules.

## Usage

```sh
cargo verus verify         # verify
cargo test --release       # perft + game tests
cargo bench --bench per_move   # per-move timings, see benches/README.md
```

Verus was installed from the binary release into `/root/verus` (on `PATH` via `~/.bashrc`),
with the Rust toolchain it requires installed through rustup.
