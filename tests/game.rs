//! End-of-game rules, exercised through the verified `Game` API.
use chess_engine::fen::*;
use chess_engine::game::Game;
use chess_engine::types::*;

fn play_all(g: &mut Game, moves: &str) {
    for mv in moves.split_whitespace() {
        let m = parse_uci_move(mv).unwrap();
        assert!(g.play(m), "illegal move {mv} in {}", to_fen(g.current()));
    }
}

fn game(fen: &str) -> Game {
    Game::from_position(parse_fen(fen).unwrap())
}

#[test]
fn fools_mate() {
    let mut g = Game::new();
    play_all(&mut g, "f2f3 e7e5 g2g4");
    assert_eq!(g.outcome(), None);
    play_all(&mut g, "d8h4");
    assert_eq!(g.outcome(), Some(GameOutcome::Checkmate { winner: Color::Black }));
}

#[test]
fn illegal_moves_are_rejected() {
    let mut g = Game::new();
    for mv in ["e2e5", "e1g1", "a2a1q", "g1g3", "e7e5", "b1d2"] {
        assert!(!g.play(parse_uci_move(mv).unwrap()), "{mv} should be illegal");
    }
    assert_eq!(g.history.len(), 1);
    // promotion must name a piece
    let mut g = game("8/P6k/8/8/8/8/8/K7 w - - 0 1");
    assert!(!g.play(parse_uci_move("a7a8").unwrap()));
    assert!(g.play(parse_uci_move("a7a8n").unwrap()));
}

#[test]
fn stalemate() {
    let g = game("7k/5Q2/6K1/8/8/8/8/8 b - - 0 1");
    assert_eq!(g.outcome(), Some(GameOutcome::Stalemate));
}

#[test]
fn insufficient_material() {
    for (fen, dead) in [
        ("8/8/4k3/8/8/4K3/8/8 w - - 0 1", true),        // K v K
        ("8/8/4k3/8/8/4KN2/8/8 w - - 0 1", true),       // K+N v K
        ("8/8/4k3/8/8/4KB2/8/8 w - - 0 1", true),       // K+B v K
        ("8/8/4kb2/8/8/4K1B1/8/8 w - - 0 1", true),     // bishops on same shade
        ("8/8/4k1b1/8/8/4K1B1/8/8 w - - 0 1", false),   // bishops on opposite shades
        ("8/8/4kn2/8/8/4K1N1/8/8 w - - 0 1", false),    // K+N v K+N
        ("8/8/4k3/8/8/4KNN1/8/8 w - - 0 1", false),     // K+N+N v K
        ("8/8/4k3/8/8/4K3/4P3/8 w - - 0 1", false),     // pawn
    ] {
        let expected = if dead { Some(GameOutcome::InsufficientMaterial) } else { None };
        assert_eq!(game(fen).outcome(), expected, "{fen}");
    }
}

#[test]
fn fifty_and_seventy_five_move_rules() {
    let g = game("8/8/4k3/8/8/4K3/4R3/8 w - - 99 80");
    assert!(!g.can_claim_draw());
    let g = game("8/8/4k3/8/8/4K3/4R3/8 w - - 100 80");
    assert!(g.can_claim_draw());
    assert_eq!(g.outcome(), None);
    let g = game("8/8/4k3/8/8/4K3/4R3/8 w - - 150 100");
    assert_eq!(g.outcome(), Some(GameOutcome::SeventyFiveMoveRule));
    // checkmate on the move that reaches 150 takes precedence
    let mut g = game("k7/8/1K6/8/8/8/8/7R w - - 149 100");
    play_all(&mut g, "h1h8");
    assert_eq!(g.outcome(), Some(GameOutcome::Checkmate { winner: Color::White }));
    // a pawn move resets the clock
    let mut g = game("8/8/4k3/8/8/4K3/P7/8 w - - 120 80");
    play_all(&mut g, "a2a4");
    assert_eq!(g.current().halfmove_clock, 0);
}

#[test]
fn repetition() {
    let mut g = Game::new();
    let cycle = "g1f3 g8f6 f3g1 f6g8";
    play_all(&mut g, cycle);
    assert_eq!(g.repetition_count(), 2);
    assert!(!g.can_claim_draw());
    play_all(&mut g, cycle);
    assert_eq!(g.repetition_count(), 3);
    assert!(g.can_claim_draw());
    assert_eq!(g.outcome(), None);
    play_all(&mut g, cycle);
    play_all(&mut g, cycle);
    assert_eq!(g.repetition_count(), 5);
    assert_eq!(g.outcome(), Some(GameOutcome::FivefoldRepetition));
}

#[test]
fn repetition_ignores_unusable_en_passant_square() {
    // After 1.e4 the ep square e3 is set, but no black pawn can capture on e3, so the
    // position after 1.e4 Nf6 2.Nf3 Ng8 3.Ng1 is "the same" as after 1.e4.
    let mut g = Game::new();
    play_all(&mut g, "e2e4");
    assert!(g.current().ep.is_some());
    play_all(&mut g, "g8f6 g1f3 f6g8 f3g1");
    assert_eq!(g.repetition_count(), 2);
}

#[test]
fn repetition_respects_usable_en_passant_square() {
    // Here black *can* capture en passant right after d2d4, so that position
    // differs from the later one with the same pieces.
    let mut g = game("4k3/8/8/8/4p3/8/3P4/4K3 w - - 0 1");
    play_all(&mut g, "d2d4");
    assert!(g.current().ep.is_some());
    play_all(&mut g, "e8d8 e1d1 d8e8 d1e1");
    assert_eq!(g.repetition_count(), 1);
}

#[test]
fn castling_rights_are_lost() {
    let mut g = game("r3k2r/8/8/8/8/8/8/R3K2R w KQkq - 0 1");
    play_all(&mut g, "a1a8"); // rook captures rook: both queenside rights lost
    let cr = g.current().castling;
    assert!(!cr.white_queenside && !cr.black_queenside && cr.white_kingside && cr.black_kingside);
    play_all(&mut g, "e8e7");
    assert!(!g.current().castling.black_kingside);
    assert!(!g.play(parse_uci_move("e1c1").unwrap()));
    assert!(g.play(parse_uci_move("e1g1").unwrap()));
    assert_eq!(to_fen(g.current()), "R6r/4k3/8/8/8/8/8/5RK1 b - - 2 2");
}

#[test]
fn no_draw_claim_after_checkmate() {
    // Black is mated; the 50-move condition also holds, but checkmate ended the game.
    let g = game("7k/6Q1/6K1/8/8/8/8/8 b - - 120 80");
    assert_eq!(g.outcome(), Some(GameOutcome::Checkmate { winner: Color::White }));
    assert!(!g.can_claim_draw());
}
