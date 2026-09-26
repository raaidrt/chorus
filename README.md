# chess_engine

A chess engine whose rules implementation is formally verified with [Verus](https://github.com/verus-lang/verus).

## Layout

| File | Role | Verified? |
|---|---|---|
| `src/spec.rs` | **The specification**: the FIDE rules as Verus `spec` functions (attacks, check, pseudo-legal and legal moves, castling, en passant, promotion, making a move, checkmate and stalemate, insufficient material, 50/75-move rules, threefold/fivefold repetition). | Trusted: review this |
| `src/types.rs` | Shared data types (`Piece`, `Square`, `Move`, ...). | ✓ |
| `src/position.rs` | Mailbox `Position` and its `View` into `spec::PositionModel`. | ✓ |
| `src/attacks.rs` | `is_attacked_exec` (ray-based), `in_check_exec`. | ✓ `== spec` |
| `src/movegen.rs` | `is_legal_exec`, `apply_move_exec`, `legal_moves_exec` (sound, complete, no duplicates). | ✓ `== spec` |
| `src/game.rs` | `Game` history, `outcome()`, `can_claim_draw()`, repetition counting. | ✓ `== spec` |
| `src/fen.rs` | FEN / UCI parsing and printing. | ✗ (I/O glue) |

The implementation keeps the simple mailbox board, and the spec's definitions stay the
proof targets. Three things make it fast:

* **Attack detection** starts from the target square. It checks the eight knight squares
  and the first piece along each of the eight lines, instead of trying every square as an attacker.
* **Move generation** tries only the targets a piece could reach: pawn pushes and
  captures, knight and king offsets plus the castling squares, and each slider line up to
  its first blocker. A ghost set of tried squares proves completeness and the absence of duplicates.
* **Legality** uses the king square, found once per position. If the king is not in check
  and does not move, only the line from the king through the vacated square (or through
  the pawn captured en passant) can attack it.

`has_legal_move_exec` stops at the first piece with a legal move. `en_passant_available_exec`
tries only the two pawns that could capture en passant.

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
