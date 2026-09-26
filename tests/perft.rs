//! Perft (move path enumeration) against published reference counts.
//!
//! Because `legal_moves_exec` and `apply_move_exec` are *proven* equal to the
//! specification, these tests validate the specification itself: a wrong rule in
//! `spec.rs` would show up as a wrong node count.
//! Reference numbers: https://www.chessprogramming.org/Perft_Results
use chess_engine::fen::*;
use chess_engine::movegen::*;
use chess_engine::position::Position;

fn perft(pos: &Position, depth: u32) -> u64 {
    if depth == 0 {
        return 1;
    }
    let moves = legal_moves_exec(pos);
    if depth == 1 {
        return moves.len() as u64;
    }
    moves.iter().map(|&m| perft(&apply_move_exec(pos, m), depth - 1)).sum()
}

fn check(fen: &str, expected: &[u64]) {
    let pos = parse_fen(fen).unwrap();
    assert_eq!(to_fen(&pos), fen, "FEN round trip");
    for (i, &n) in expected.iter().enumerate() {
        let depth = i as u32 + 1;
        assert_eq!(perft(&pos, depth), n, "perft({depth}) of {fen}");
    }
}

#[test]
fn initial_position_matches_fen() {
    assert_eq!(
        to_fen(&Position::initial()),
        "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"
    );
}

#[test]
fn perft_start() {
    check("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1", &[20, 400, 8902, 197281, 4865609]);
}

#[test]
fn perft_kiwipete() {
    check(
        "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1",
        &[48, 2039, 97862, 4085603],
    );
}

#[test]
fn perft_position3() {
    check("8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1", &[14, 191, 2812, 43238, 674624]);
}

#[test]
fn perft_position4() {
    check(
        "r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq - 0 1",
        &[6, 264, 9467, 422333],
    );
}

#[test]
fn perft_position4_mirrored() {
    check(
        "r2q1rk1/pP1p2pp/Q4n2/bbp1p3/Np6/1B3NBn/pPPP1PPP/R3K2R b KQ - 0 1",
        &[6, 264, 9467, 422333],
    );
}

#[test]
fn perft_position5() {
    check("rnbq1k1r/pp1Pbppp/2p5/8/2B5/8/PPP1NnPP/RNBQK2R w KQ - 1 8", &[44, 1486, 62379, 2103487]);
}

#[test]
fn perft_position6() {
    check(
        "r4rk1/1pp1qppp/p1np1n2/2b1p1B1/2B1P1b1/P1NP1N2/1PP1QPPP/R4RK1 w - - 0 10",
        &[46, 2079, 89890, 3894594],
    );
}
