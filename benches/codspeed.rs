//! Benchmarks for CodSpeed (`.github/workflows/codspeed.yml`).
//!
//! The same workloads as `per_move.rs`, written for divan, which CodSpeed instruments:
//! the verified primitives on the perft reference positions, the same primitives swept
//! over every position of the 100-game Lichess sample, and whole-game replays. CodSpeed
//! tracks these on every push and comments on pull requests. `per_move.rs` stays the tool
//! for detailed local analysis (per-ply timings, confidence intervals, A/B reports).
//!
//! `cargo bench --bench codspeed` runs them locally as plain divan wall-time benchmarks;
//! `cargo codspeed build --bench codspeed && cargo codspeed run --bench codspeed` runs them
//! the way CI does.
use chess_engine::game::Game;
use chess_engine::movegen::{apply_move_exec, has_legal_move_exec, is_legal_exec, legal_moves_exec};
use chess_engine::position::Position;
use chess_engine::types::Move;
use divan::{black_box, Bencher};
use std::sync::OnceLock;

mod common;

use common::{game_positions, lichess_games, position, LichessGame, PLY_GAMES};

fn main() {
    divan::main();
}

/// Names of `common::POSITIONS`, as divan needs them in the attribute.
const POSITIONS: [&str; 6] = ["start", "kiwipete", "pos3_endgame", "pos4_promotions", "pos5", "pos6_middlegame"];

/// The Lichess sample and every position it reaches with its legal moves, loaded (and
/// checked) once for all benchmarks.
struct Sample {
    games: Vec<LichessGame>,
    positions: Vec<(Position, Vec<Move>)>,
}

fn sample() -> &'static Sample {
    static SAMPLE: OnceLock<Sample> = OnceLock::new();
    SAMPLE.get_or_init(|| {
        let games = lichess_games();
        let positions = game_positions(&games).into_iter().map(|p| (p, legal_moves_exec(&p))).collect();
        Sample { games, positions }
    })
}

/// Plays a game from the start, doing at every ply what the engine does for one move.
fn replay(moves: &[Move]) {
    let mut g = Game::new();
    for &m in moves {
        black_box(legal_moves_exec(g.current()));
        assert!(g.play(black_box(m)));
        black_box(g.outcome());
    }
}

/// The verified primitives on the perft reference positions (move counts checked).
mod reference {
    use super::*;

    #[divan::bench(args = POSITIONS)]
    fn legal_moves(bencher: Bencher, name: &str) {
        let pos = position(name);
        bencher.bench(|| legal_moves_exec(black_box(&pos)));
    }

    #[divan::bench(args = POSITIONS)]
    fn has_legal_move(bencher: Bencher, name: &str) {
        let pos = position(name);
        bencher.bench(|| has_legal_move_exec(black_box(&pos)));
    }

    /// `is_legal_exec` on every legal move of the position.
    #[divan::bench(args = POSITIONS)]
    fn is_legal(bencher: Bencher, name: &str) {
        let pos = position(name);
        let moves = legal_moves_exec(&pos);
        bencher.bench(|| moves.iter().filter(|&&m| is_legal_exec(black_box(&pos), black_box(m))).count());
    }

    /// `apply_move_exec` on every legal move of the position.
    #[divan::bench(args = POSITIONS)]
    fn apply_move(bencher: Bencher, name: &str) {
        let pos = position(name);
        let moves = legal_moves_exec(&pos);
        bencher.bench(|| {
            for &m in &moves {
                black_box(apply_move_exec(black_box(&pos), black_box(m)));
            }
        });
    }

    #[divan::bench(args = POSITIONS)]
    fn outcome(bencher: Bencher, name: &str) {
        let g = Game::from_position(position(name));
        bencher.bench(|| black_box(&g).outcome());
    }
}

/// The Lichess sample (`benches/data/lichess_games.txt`).
mod lichess {
    use super::*;

    /// `legal_moves_exec` on every position the games reach.
    #[divan::bench(sample_count = 10)]
    fn legal_moves(bencher: Bencher) {
        let s = sample();
        bencher.bench(|| {
            for (p, _) in &s.positions {
                black_box(legal_moves_exec(black_box(p)));
            }
        });
    }

    /// `is_legal_exec` on every legal move of every position the games reach.
    #[divan::bench(sample_count = 10)]
    fn is_legal(bencher: Bencher) {
        let s = sample();
        bencher.bench(|| {
            s.positions.iter().map(|(p, ms)| ms.iter().filter(|&&m| is_legal_exec(black_box(p), black_box(m))).count()).sum::<usize>()
        });
    }

    /// `apply_move_exec` on every legal move of every position the games reach.
    #[divan::bench(sample_count = 10)]
    fn apply_move(bencher: Bencher) {
        let s = sample();
        bencher.bench(|| {
            for (p, ms) in &s.positions {
                for &m in ms {
                    black_box(apply_move_exec(black_box(p), black_box(m)));
                }
            }
        });
    }

    /// All 100 games from the start: legal moves, play and outcome at every ply.
    #[divan::bench(sample_count = 10)]
    fn replay_all(bencher: Bencher) {
        let s = sample();
        bencher.bench(|| {
            for g in &s.games {
                replay(black_box(&g.moves));
            }
        });
    }

    /// One game at a time: the two games `per_move.rs` also times ply by ply.
    #[divan::bench(args = PLY_GAMES)]
    fn replay_game(bencher: Bencher, id: &str) {
        let g = sample().games.iter().find(|g| g.id == id).unwrap();
        bencher.bench(|| replay(black_box(&g.moves)));
    }
}
