//! Workloads shared by `per_move.rs` (the statistical harness) and `codspeed.rs` (CI).
#![allow(dead_code)]

use chess_engine::fen::{move_to_uci, parse_fen, parse_uci_move};
use chess_engine::game::Game;
use chess_engine::movegen::legal_moves_exec;
use chess_engine::position::Position;
use chess_engine::types::{Color, GameOutcome, Move};

/// Perft reference positions (see `tests/perft.rs`) with their known move counts, so a
/// benchmark can never silently time the wrong thing.
pub const POSITIONS: &[(&str, &str, usize)] = &[
    ("start", "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1", 20),
    ("kiwipete", "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1", 48),
    ("pos3_endgame", "8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1", 14),
    ("pos4_promotions", "r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq - 0 1", 6),
    ("pos5", "rnbq1k1r/pp1Pbppp/2p5/8/2B5/8/PPP1NnPP/RNBQK2R w KQ - 1 8", 44),
    ("pos6_middlegame", "r4rk1/1pp1qppp/p1np1n2/2b1p1B1/2B1P1b1/P1NP1N2/1PP1QPPP/R4RK1 w - - 0 10", 46),
];

/// Parses a perft reference position and checks its legal move count.
pub fn position(name: &str) -> Position {
    let &(_, fen, expected) = POSITIONS.iter().find(|p| p.0 == name).expect("unknown position");
    let pos = parse_fen(fen).unwrap();
    assert_eq!(legal_moves_exec(&pos).len(), expected, "legal move count of {name}");
    pos
}

/// 100 rated and casual Lichess games (`scripts/lichess_games.py` explains the sampling).
const LICHESS_GAMES: &str = include_str!("../data/lichess_games.txt");

/// Games that also get per-ply benchmarks: a median-length game (65 plies) that ends in
/// mate, and a long (135-ply) drawn game with an endgame.
pub const PLY_GAMES: &[&str] = &["ILZ77Y8B", "jGiADcVr"];

pub struct LichessGame {
    pub id: &'static str,
    /// Lichess's `victory_status`: `mate`, `resign`, `outoftime` or `draw`.
    pub status: &'static str,
    pub moves: Vec<Move>,
}

/// Loads the sample and replays every game, so a transcription error fails loudly
/// instead of benchmarking a truncated game.
pub fn lichess_games() -> Vec<LichessGame> {
    let games: Vec<LichessGame> = LICHESS_GAMES
        .lines()
        .filter(|l| !l.starts_with('#') && !l.trim().is_empty())
        .map(|l| {
            let mut fields = l.split_whitespace();
            let id = fields.next().unwrap();
            let status = fields.next().unwrap();
            let winner = fields.next().unwrap();
            let moves: Vec<Move> =
                fields.map(|s| parse_uci_move(s).unwrap_or_else(|| panic!("{id}: bad UCI move {s}"))).collect();
            let g = replay(&moves).unwrap_or_else(|k| panic!("{id}: illegal move at ply {}", k + 1));
            if status == "mate" {
                let winner = if winner == "white" { Color::White } else { Color::Black };
                assert_eq!(g.outcome(), Some(GameOutcome::Checkmate { winner }), "{id} should end in mate");
            }
            LichessGame { id, status, moves }
        })
        .collect();
    assert_eq!(games.len(), 100, "games in benches/data/lichess_games.txt");
    games
}

pub fn lichess_game(id: &str) -> LichessGame {
    lichess_games().into_iter().find(|g| g.id == id).unwrap_or_else(|| panic!("no game {id}"))
}

/// Plays `moves` from the initial position; `Err(k)` if the `k`-th (0-based) is illegal.
pub fn replay(moves: &[Move]) -> Result<Game, usize> {
    let mut g = Game::new();
    for (k, &m) in moves.iter().enumerate() {
        if !g.play(m) {
            return Err(k);
        }
    }
    Ok(g)
}

/// Every prefix of a game: `states[k]` is the game after `k` plies.
pub fn game_states(moves: &[Move]) -> Vec<Game> {
    let mut g = Game::new();
    let mut states = vec![clone_game(&g)];
    for (k, &m) in moves.iter().enumerate() {
        assert!(g.play(m), "illegal move {} at ply {k}", move_to_uci(m));
        states.push(clone_game(&g));
    }
    states
}

/// Every position reached in the sample (before each move, and the final one).
pub fn game_positions(games: &[LichessGame]) -> Vec<Position> {
    games.iter().flat_map(|g| game_states(&g.moves).into_iter().map(|s| *s.current())).collect()
}

pub fn clone_game(g: &Game) -> Game {
    Game { history: g.history.clone() }
}
