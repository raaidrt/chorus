//! Compare candidate pruning against exhaustive legality checks at board edges.
use chess_engine::movegen::{has_legal_move_exec, is_legal_exec, legal_moves_exec};
use chess_engine::position::Position;
use chess_engine::types::{Color, Move, Piece, PieceKind, Square};

#[test]
fn bounded_candidates_match_exhaustive_search() {
    let kinds = [
        PieceKind::Pawn,
        PieceKind::Knight,
        PieceKind::Bishop,
        PieceKind::Rook,
        PieceKind::Queen,
        PieceKind::King,
    ];
    let promotions = [
        None,
        Some(PieceKind::Knight),
        Some(PieceKind::Bishop),
        Some(PieceKind::Rook),
        Some(PieceKind::Queen),
        Some(PieceKind::Pawn),
        Some(PieceKind::King),
    ];
    for color in [Color::White, Color::Black] {
        for kind in kinds {
            for rank in 0..8 {
                for file in [0, 4, 7] {
                    let from = Square { file, rank };
                    let mut pos = Position::initial();
                    pos.board = [None; 64];
                    pos.turn = color;
                    pos.board[rank as usize * 8 + file as usize] = Some(Piece { color, kind });
                    // The API also accepts sparse boards and pawns on the last rank.
                    // Exercise both colors and every rank, including empty move bands.
                    let mut expected = Vec::new();
                    for to_rank in 0..8 {
                        for to_file in 0..8 {
                            for promotion in promotions {
                                let m = Move {
                                    from,
                                    to: Square { file: to_file, rank: to_rank },
                                    promotion,
                                };
                                if is_legal_exec(&pos, m) {
                                    expected.push(m);
                                }
                            }
                        }
                    }
                    assert_eq!(legal_moves_exec(&pos), expected, "{color:?} {kind:?} {from:?}");
                    assert_eq!(has_legal_move_exec(&pos), !expected.is_empty());
                }
            }
        }
    }
}
