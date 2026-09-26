# chess_engine

A chess engine whose rules implementation is formally verified with [Verus](https://github.com/verus-lang/verus).

## Layout

| File | Role | Verified? |
|---|---|---|
| `src/spec.rs` | **The specification**: the FIDE rules as Verus `spec` functions (attacks, check, pseudo-legal and legal moves, castling, en passant, promotion, making a move, checkmate and stalemate, insufficient material, 50/75-move rules, threefold/fivefold repetition). | Trusted: review this |
| `src/types.rs` | Shared data types (`Piece`, `Square`, `Move`, ...). | ✓ |
| `src/position.rs` | Mailbox `Position` and its `View` into `spec::PositionModel`. | ✓ |
| `src/attacks.rs` | `is_attacked_exec`, `in_check_exec`. | ✓ `== spec` |
| `src/movegen.rs` | `is_legal_exec`, `apply_move_exec`, `legal_moves_exec` (sound, complete, no duplicates). | ✓ `== spec` |
| `src/game.rs` | `Game` history, `outcome()`, `can_claim_draw()`, repetition counting. | ✓ `== spec` |
| `src/fen.rs` | FEN / UCI parsing and printing. | ✗ (I/O glue) |

The implementation is deliberately naive (legal move generation tries every
from/to/promotion candidate). It is the reference to optimize against later: any
faster implementation only has to prove the same `ensures` clauses.

## Validating the spec

The executable code is proven equal to the spec, so the perft tests in
`tests/perft.rs` (reference counts from chessprogramming.org, ~20M leaf nodes)
test the **spec itself**. `tests/game.rs` covers end-of-game rules.

## Usage

```sh
cargo verus verify         # verify
cargo test --release       # perft + game tests
```

Verus was installed from the binary release into `/root/verus` (on `PATH` via `~/.bashrc`),
with the Rust toolchain it requires installed through rustup.
