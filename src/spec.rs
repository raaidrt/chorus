//! # Formal specification of the rules of chess (FIDE Laws of Chess, articles 2, 3, 5 and 9).
//!
//! Everything in this module is `spec` (mathematical, ghost-only) code. It is the
//! *trusted* part of the engine: the executable code elsewhere in the crate is proven
//! to agree with these definitions, so the definitions here are what must be reviewed
//! for correctness.
//!
//! Conventions:
//! * Files and ranks are integers `0..8` (file 0 = a, rank 0 = the 1st rank).
//! * The board is a sequence of 64 optional pieces indexed by `rank * 8 + file`.
//! * Moves are in pure coordinate (UCI) form: castling is the king moving two files,
//!   en passant is the pawn moving onto the en-passant target square.
use crate::types::*;
use vstd::prelude::*;

verus! {

pub type Board = Seq<Option<Piece>>;

/// Everything needed to determine the legal moves in a position
/// (the same information as a FEN string).
pub struct PositionModel {
    pub board: Board,
    pub turn: Color,
    pub castling: CastlingRights,
    /// The square "behind" a pawn that has just advanced two squares, if any.
    /// (Set after every double push, whether or not a capture is actually possible.)
    pub ep: Option<Square>,
    /// Half-moves since the last capture or pawn move (FIDE 9.3 / 9.6.2).
    pub halfmove_clock: nat,
    pub fullmove_number: nat,
}

// ===========================================================================
// Board geometry
// ===========================================================================

pub open spec fn on_board(f: int, r: int) -> bool {
    0 <= f < 8 && 0 <= r < 8
}

pub open spec fn valid_square(s: Square) -> bool {
    s.file < 8 && s.rank < 8
}

pub open spec fn index_of(f: int, r: int) -> int {
    r * 8 + f
}

pub open spec fn at(b: Board, f: int, r: int) -> Option<Piece> {
    b[index_of(f, r)]
}

pub open spec fn piece_at(b: Board, s: Square) -> Option<Piece> {
    at(b, s.file as int, s.rank as int)
}

pub open spec fn is_empty(b: Board, f: int, r: int) -> bool {
    at(b, f, r) is None
}

pub open spec fn has_color(b: Board, f: int, r: int, c: Color) -> bool {
    at(b, f, r) matches Some(p) && p.color == c
}

pub open spec fn abs(x: int) -> int {
    if x < 0 { -x } else { x }
}

/// Chebyshev (king-move) distance for a displacement.
pub open spec fn distance(df: int, dr: int) -> int {
    if abs(df) >= abs(dr) { abs(df) } else { abs(dr) }
}

/// Coordinate reached from `x` after `k` unit steps in the direction of `sign(d)`.
pub open spec fn step(x: int, d: int, k: int) -> int {
    if d > 0 { x + k } else if d < 0 { x - k } else { x }
}

/// Along a rank or a file.
pub open spec fn is_orthogonal(df: int, dr: int) -> bool {
    (df == 0) != (dr == 0)
}

/// Along a diagonal.
pub open spec fn is_diagonal(df: int, dr: int) -> bool {
    df != 0 && abs(df) == abs(dr)
}

/// All squares strictly between (f1, r1) and (f2, r2) are empty.
/// Only meaningful when the two squares are on a common line (orthogonal or diagonal).
pub open spec fn path_clear(b: Board, f1: int, r1: int, f2: int, r2: int) -> bool {
    forall|k: int|
        0 < k < distance(f2 - f1, r2 - r1) ==> #[trigger] is_empty(
            b,
            step(f1, f2 - f1, k),
            step(r1, r2 - r1, k),
        )
}

// ===========================================================================
// Colors
// ===========================================================================

pub open spec fn opponent(c: Color) -> Color {
    match c {
        Color::White => Color::Black,
        Color::Black => Color::White,
    }
}

/// Rank direction in which pawns of color `c` advance.
pub open spec fn forward(c: Color) -> int {
    match c {
        Color::White => 1,
        Color::Black => -1,
    }
}

/// The rank on which the king and rooks of `c` start.
pub open spec fn back_rank(c: Color) -> int {
    match c {
        Color::White => 0,
        Color::Black => 7,
    }
}

pub open spec fn pawn_start_rank(c: Color) -> int {
    match c {
        Color::White => 1,
        Color::Black => 6,
    }
}

pub open spec fn promotion_rank(c: Color) -> int {
    match c {
        Color::White => 7,
        Color::Black => 0,
    }
}

// ===========================================================================
// Attacks (FIDE 3.2 - 3.8: the squares a piece "attacks")
// ===========================================================================

/// Piece `p` standing on (f1, r1) attacks (f2, r2) on board `b`.
/// Occupancy of the target square is irrelevant; only the path matters.
pub open spec fn attacks(b: Board, p: Piece, f1: int, r1: int, f2: int, r2: int) -> bool {
    let df = f2 - f1;
    let dr = r2 - r1;
    match p.kind {
        PieceKind::Pawn => dr == forward(p.color) && abs(df) == 1,
        PieceKind::Knight => (abs(df) == 1 && abs(dr) == 2) || (abs(df) == 2 && abs(dr) == 1),
        PieceKind::Bishop => is_diagonal(df, dr) && path_clear(b, f1, r1, f2, r2),
        PieceKind::Rook => is_orthogonal(df, dr) && path_clear(b, f1, r1, f2, r2),
        PieceKind::Queen => (is_orthogonal(df, dr) || is_diagonal(df, dr)) && path_clear(
            b,
            f1,
            r1,
            f2,
            r2,
        ),
        PieceKind::King => distance(df, dr) == 1,
    }
}

/// The piece on (f1, r1) belongs to `by` and attacks (f, r).
pub open spec fn attacker_at(b: Board, f1: int, r1: int, f: int, r: int, by: Color) -> bool {
    at(b, f1, r1) matches Some(p) && p.color == by && attacks(b, p, f1, r1, f, r)
}

pub open spec fn is_attacked(b: Board, f: int, r: int, by: Color) -> bool {
    exists|f1: int, r1: int| on_board(f1, r1) && #[trigger] attacker_at(b, f1, r1, f, r, by)
}

pub open spec fn king_of(c: Color) -> Piece {
    Piece { color: c, kind: PieceKind::King }
}

/// A king of color `c` is attacked by the opponent (FIDE 3.9).
pub open spec fn in_check(b: Board, c: Color) -> bool {
    exists|f: int, r: int|
        on_board(f, r) && #[trigger] at(b, f, r) == Some(king_of(c)) && is_attacked(
            b,
            f,
            r,
            opponent(c),
        )
}

// ===========================================================================
// Moves
// ===========================================================================

pub open spec fn moving_piece(pos: PositionModel, m: Move) -> Option<Piece> {
    piece_at(pos.board, m.from)
}

pub open spec fn is_promotion_piece(k: PieceKind) -> bool {
    match k {
        PieceKind::Knight | PieceKind::Bishop | PieceKind::Rook | PieceKind::Queen => true,
        _ => false,
    }
}

/// A pawn reaching the last rank must promote to N/B/R/Q (FIDE 3.7.5);
/// every other move carries no promotion.
pub open spec fn promotion_ok(p: Piece, m: Move) -> bool {
    if p.kind == PieceKind::Pawn && m.to.rank as int == promotion_rank(p.color) {
        m.promotion matches Some(k) && is_promotion_piece(k)
    } else {
        m.promotion is None
    }
}

/// The move is an en-passant capture (a pawn moving diagonally onto the empty ep square).
pub open spec fn is_en_passant(pos: PositionModel, m: Move) -> bool {
    &&& moving_piece(pos, m) matches Some(p) && p.kind == PieceKind::Pawn
    &&& pos.ep == Some(m.to)
    &&& m.from.file != m.to.file
    &&& piece_at(pos.board, m.to) is None
}

/// The move is a castling move (a king moving two files from the e-file).
pub open spec fn is_castling(pos: PositionModel, m: Move) -> bool {
    &&& moving_piece(pos, m) matches Some(p) && p.kind == PieceKind::King
    &&& m.from.file == 4
    &&& m.from.rank == m.to.rank
    &&& abs(m.to.file - m.from.file) == 2
}

pub open spec fn is_capture(pos: PositionModel, m: Move) -> bool {
    piece_at(pos.board, m.to) is Some || is_en_passant(pos, m)
}

pub open spec fn is_double_push(pos: PositionModel, m: Move) -> bool {
    &&& moving_piece(pos, m) matches Some(p) && p.kind == PieceKind::Pawn
    &&& abs(m.to.rank - m.from.rank) == 2
}

/// Pawn moves (FIDE 3.7): single push, double push from the start rank,
/// diagonal capture and en-passant capture.
pub open spec fn pawn_move_ok(pos: PositionModel, m: Move) -> bool {
    let b = pos.board;
    let c = pos.turn;
    let (f1, r1, f2, r2) = (m.from.file as int, m.from.rank as int, m.to.file as int, m.to.rank as int);
    let df = f2 - f1;
    let dr = r2 - r1;
    ||| df == 0 && dr == forward(c) && is_empty(b, f2, r2)
    ||| df == 0 && dr == 2 * forward(c) && r1 == pawn_start_rank(c) && is_empty(
        b,
        f1,
        r1 + forward(c),
    ) && is_empty(b, f2, r2)
    ||| abs(df) == 1 && dr == forward(c) && (has_color(b, f2, r2, opponent(c)) || (pos.ep == Some(
        m.to,
    ) && is_empty(b, f2, r2) && at(b, f2, r1) == Some(
        Piece { color: opponent(c), kind: PieceKind::Pawn },
    )))
}

pub open spec fn has_kingside_right(cr: CastlingRights, c: Color) -> bool {
    match c {
        Color::White => cr.white_kingside,
        Color::Black => cr.black_kingside,
    }
}

pub open spec fn has_queenside_right(cr: CastlingRights, c: Color) -> bool {
    match c {
        Color::White => cr.white_queenside,
        Color::Black => cr.black_queenside,
    }
}

pub open spec fn rook_of(c: Color) -> Piece {
    Piece { color: c, kind: PieceKind::Rook }
}

/// Castling (FIDE 3.8.2): the right has not been lost, the rook is in place,
/// the squares between king and rook are empty, the king is not in check and does
/// not pass over an attacked square. (That the king does not *land* on an attacked
/// square is covered by the general legality condition, but it is repeated here.)
pub open spec fn castle_ok(pos: PositionModel, m: Move) -> bool {
    let b = pos.board;
    let c = pos.turn;
    let r = back_rank(c);
    let opp = opponent(c);
    &&& m.from.file == 4 && m.from.rank as int == r && m.to.rank as int == r
    &&& !in_check(b, c)
    &&& {
        ||| m.to.file == 6 && has_kingside_right(pos.castling, c) && at(b, 7, r) == Some(rook_of(c))
            && is_empty(b, 5, r) && is_empty(b, 6, r) && !is_attacked(b, 5, r, opp)
            && !is_attacked(b, 6, r, opp)
        ||| m.to.file == 2 && has_queenside_right(pos.castling, c) && at(b, 0, r) == Some(
            rook_of(c),
        ) && is_empty(b, 1, r) && is_empty(b, 2, r) && is_empty(b, 3, r) && !is_attacked(
            b,
            3,
            r,
            opp,
        ) && !is_attacked(b, 2, r, opp)
    }
}

/// A move obeying how the pieces move, ignoring whether it leaves the own king in check.
pub open spec fn is_pseudo_legal(pos: PositionModel, m: Move) -> bool {
    let b = pos.board;
    let (f1, r1, f2, r2) = (m.from.file as int, m.from.rank as int, m.to.file as int, m.to.rank as int);
    &&& valid_square(m.from)
    &&& valid_square(m.to)
    &&& moving_piece(pos, m) matches Some(p) && {
        &&& p.color == pos.turn
        &&& promotion_ok(p, m)
        &&& !has_color(b, f2, r2, pos.turn)
        &&& match p.kind {
            PieceKind::Pawn => pawn_move_ok(pos, m),
            PieceKind::King => attacks(b, p, f1, r1, f2, r2) || castle_ok(pos, m),
            _ => attacks(b, p, f1, r1, f2, r2),
        }
    }
}

/// The board after making move `m` (assumed pseudo-legal).
pub open spec fn move_board(pos: PositionModel, m: Move) -> Board {
    let b = pos.board;
    let p = moving_piece(pos, m)->Some_0;
    let placed = match m.promotion {
        Some(k) => Piece { color: p.color, kind: k },
        None => p,
    };
    let (f1, r1, f2, r2) = (m.from.file as int, m.from.rank as int, m.to.file as int, m.to.rank as int);
    let b1 = b.update(index_of(f1, r1), None).update(index_of(f2, r2), Some(placed));
    if is_en_passant(pos, m) {
        // the captured pawn stands beside the moving pawn
        b1.update(index_of(f2, r1), None)
    } else if is_castling(pos, m) {
        if f2 == 6 {
            b1.update(index_of(7, r1), None).update(index_of(5, r1), Some(rook_of(p.color)))
        } else {
            b1.update(index_of(0, r1), None).update(index_of(3, r1), Some(rook_of(p.color)))
        }
    } else {
        b1
    }
}

/// A legal move: pseudo-legal and does not leave the mover's king in check (FIDE 3.9, 3.10).
pub open spec fn is_legal(pos: PositionModel, m: Move) -> bool {
    is_pseudo_legal(pos, m) && !in_check(move_board(pos, m), pos.turn)
}

pub open spec fn legal_moves(pos: PositionModel) -> ISet<Move> {
    ISet::new(|m: Move| is_legal(pos, m))
}

pub open spec fn has_legal_move(pos: PositionModel) -> bool {
    exists|m: Move| is_legal(pos, m)
}

// ===========================================================================
// Making a move
// ===========================================================================

/// The move starts from or lands on (f, r).
pub open spec fn touches(m: Move, f: int, r: int) -> bool {
    (m.from.file == f && m.from.rank == r) || (m.to.file == f && m.to.rank == r)
}

/// Castling rights are lost when the king or the relevant rook moves, or when
/// anything lands on the rook's original square (i.e. the rook is captured).
pub open spec fn update_castling(cr: CastlingRights, m: Move) -> CastlingRights {
    CastlingRights {
        white_kingside: cr.white_kingside && !touches(m, 4, 0) && !touches(m, 7, 0),
        white_queenside: cr.white_queenside && !touches(m, 4, 0) && !touches(m, 0, 0),
        black_kingside: cr.black_kingside && !touches(m, 4, 7) && !touches(m, 7, 7),
        black_queenside: cr.black_queenside && !touches(m, 4, 7) && !touches(m, 0, 7),
    }
}

/// The position after playing the (legal) move `m`.
pub open spec fn apply_move(pos: PositionModel, m: Move) -> PositionModel {
    let pawn_move = moving_piece(pos, m) matches Some(p) && p.kind == PieceKind::Pawn;
    PositionModel {
        board: move_board(pos, m),
        turn: opponent(pos.turn),
        castling: update_castling(pos.castling, m),
        ep: if is_double_push(pos, m) {
            Some(Square { file: m.from.file, rank: ((m.from.rank + m.to.rank) / 2) as u8 })
        } else {
            None
        },
        halfmove_clock: if pawn_move || is_capture(pos, m) {
            0
        } else {
            pos.halfmove_clock + 1
        },
        fullmove_number: if pos.turn == Color::Black {
            pos.fullmove_number + 1
        } else {
            pos.fullmove_number
        },
    }
}

// ===========================================================================
// The initial position (FIDE 2.3)
// ===========================================================================

pub open spec fn back_rank_kind(f: int) -> PieceKind {
    if f == 0 || f == 7 {
        PieceKind::Rook
    } else if f == 1 || f == 6 {
        PieceKind::Knight
    } else if f == 2 || f == 5 {
        PieceKind::Bishop
    } else if f == 3 {
        PieceKind::Queen
    } else {
        PieceKind::King
    }
}

pub open spec fn initial_piece(f: int, r: int) -> Option<Piece> {
    if r == 0 {
        Some(Piece { color: Color::White, kind: back_rank_kind(f) })
    } else if r == 1 {
        Some(Piece { color: Color::White, kind: PieceKind::Pawn })
    } else if r == 6 {
        Some(Piece { color: Color::Black, kind: PieceKind::Pawn })
    } else if r == 7 {
        Some(Piece { color: Color::Black, kind: back_rank_kind(f) })
    } else {
        None
    }
}

pub open spec fn initial_position() -> PositionModel {
    PositionModel {
        board: Seq::new(64, |i: int| initial_piece(i % 8, i / 8)),
        turn: Color::White,
        castling: CastlingRights {
            white_kingside: true,
            white_queenside: true,
            black_kingside: true,
            black_queenside: true,
        },
        ep: None,
        halfmove_clock: 0,
        fullmove_number: 1,
    }
}

// ===========================================================================
// Well-formed positions
// ===========================================================================

pub open spec fn exactly_one_king(b: Board, c: Color) -> bool {
    exists|f: int, r: int|
        on_board(f, r) && #[trigger] at(b, f, r) == Some(king_of(c)) && forall|f2: int, r2: int|
            on_board(f2, r2) && #[trigger] at(b, f2, r2) == Some(king_of(c)) ==> f2 == f && r2
                == r
}

pub open spec fn castling_rights_consistent(pos: PositionModel) -> bool {
    let b = pos.board;
    &&& pos.castling.white_kingside ==> at(b, 4, 0) == Some(king_of(Color::White)) && at(b, 7, 0)
        == Some(rook_of(Color::White))
    &&& pos.castling.white_queenside ==> at(b, 4, 0) == Some(king_of(Color::White)) && at(b, 0, 0)
        == Some(rook_of(Color::White))
    &&& pos.castling.black_kingside ==> at(b, 4, 7) == Some(king_of(Color::Black)) && at(b, 7, 7)
        == Some(rook_of(Color::Black))
    &&& pos.castling.black_queenside ==> at(b, 4, 7) == Some(king_of(Color::Black)) && at(b, 0, 7)
        == Some(rook_of(Color::Black))
}

/// If an ep square is set, the opponent has just double-pushed a pawn over it.
pub open spec fn en_passant_consistent(pos: PositionModel) -> bool {
    let b = pos.board;
    let c = pos.turn;
    pos.ep matches Some(s) ==> {
        let (f, r) = (s.file as int, s.rank as int);
        &&& valid_square(s)
        &&& r == pawn_start_rank(opponent(c)) + forward(opponent(c))
        &&& is_empty(b, f, r)
        // the square the pawn came from is empty...
        &&& is_empty(b, f, r - forward(opponent(c)))
        // ...and the pawn stands on the square it moved to
        &&& at(b, f, r + forward(opponent(c))) == Some(
            Piece { color: opponent(c), kind: PieceKind::Pawn },
        )
    }
}

/// Positions that can arise in a game (a sound over-approximation of reachability).
/// The executable code does not need this; it is the natural invariant for games.
pub open spec fn is_well_formed(pos: PositionModel) -> bool {
    &&& pos.board.len() == 64
    &&& exactly_one_king(pos.board, Color::White)
    &&& exactly_one_king(pos.board, Color::Black)
    &&& forall|f: int|
        0 <= f < 8 ==> !(#[trigger] at(pos.board, f, 0) matches Some(p) && p.kind == PieceKind::Pawn)
    &&& forall|f: int|
        0 <= f < 8 ==> !(#[trigger] at(pos.board, f, 7) matches Some(p) && p.kind == PieceKind::Pawn)
    &&& !in_check(pos.board, opponent(pos.turn))
    &&& castling_rights_consistent(pos)
    &&& en_passant_consistent(pos)
    &&& pos.fullmove_number >= 1
}

// ===========================================================================
// End of the game (FIDE 5 and 9)
// ===========================================================================

/// FIDE 5.1.1
pub open spec fn is_checkmate(pos: PositionModel) -> bool {
    in_check(pos.board, pos.turn) && !has_legal_move(pos)
}

/// FIDE 5.2.1
pub open spec fn is_stalemate(pos: PositionModel) -> bool {
    !in_check(pos.board, pos.turn) && !has_legal_move(pos)
}

pub open spec fn is_minor(k: PieceKind) -> bool {
    k == PieceKind::Knight || k == PieceKind::Bishop
}

pub open spec fn square_shade(f: int, r: int) -> int {
    (f + r) % 2
}

/// There is a knight or bishop on (f, r).
pub open spec fn minor_at(b: Board, f: int, r: int) -> bool {
    at(b, f, r) matches Some(p) && is_minor(p.kind)
}

/// There is a bishop on (f, r).
pub open spec fn bishop_at(b: Board, f: int, r: int) -> bool {
    at(b, f, r) matches Some(p) && p.kind == PieceKind::Bishop
}

/// There is no piece other than a king, knight or bishop on (f, r).
pub open spec fn king_or_minor_or_empty(b: Board, f: int, r: int) -> bool {
    at(b, f, r) matches Some(p) ==> p.kind == PieceKind::King || is_minor(p.kind)
}

/// Material with which no sequence of legal moves can produce checkmate
/// (the standard, material-only instance of a "dead position", FIDE 5.2.2 / 9.6.1):
/// only kings plus either at most one minor piece, or any number of bishops that
/// all stand on squares of the same shade.
pub open spec fn insufficient_material(b: Board) -> bool {
    &&& forall|f: int, r: int| on_board(f, r) ==> #[trigger] king_or_minor_or_empty(b, f, r)
    &&& {
        // at most one minor piece
        ||| forall|f1: int, r1: int, f2: int, r2: int|
            on_board(f1, r1) && on_board(f2, r2) && #[trigger] minor_at(b, f1, r1)
                && #[trigger] minor_at(b, f2, r2) ==> f1 == f2 && r1 == r2
        // or only bishops (no knights), all on squares of the same shade
        ||| forall|f1: int, r1: int, f2: int, r2: int|
            on_board(f1, r1) && on_board(f2, r2) && #[trigger] minor_at(b, f1, r1)
                && #[trigger] minor_at(b, f2, r2) ==> bishop_at(b, f1, r1) && bishop_at(b, f2, r2)
                && square_shade(f1, r1) == square_shade(f2, r2)
    }
}

/// The part of a position that determines whether two positions are "the same"
/// for the repetition rule (FIDE 9.2.3): same player to move, same pieces on the
/// same squares, same castling rights, and the same en-passant possibilities.
pub struct PositionKey {
    pub board: Board,
    pub turn: Color,
    pub castling: CastlingRights,
    pub ep: Option<Square>,
}

/// An en-passant capture is actually (legally) possible.
pub open spec fn en_passant_available(pos: PositionModel) -> bool {
    exists|m: Move| is_legal(pos, m) && is_en_passant(pos, m)
}

pub open spec fn repetition_key(pos: PositionModel) -> PositionKey {
    PositionKey {
        board: pos.board,
        turn: pos.turn,
        castling: pos.castling,
        ep: if en_passant_available(pos) { pos.ep } else { None },
    }
}

/// A game: the sequence of positions from the start position to the current one.
pub struct GameModel {
    pub history: Seq<PositionModel>,
}

pub open spec fn current(g: GameModel) -> PositionModel {
    g.history.last()
}

/// The game consisting of the first `n` positions of `g`.
pub open spec fn game_prefix(g: GameModel, n: int) -> GameModel {
    GameModel { history: g.history.take(n) }
}

/// Each position arises from the previous one by a legal move, and no move is
/// made after the game has ended (FIDE 5.1.1, 5.2.1, 5.2.2, 9.6: these end the
/// game immediately).
pub open spec fn is_valid_game(g: GameModel) -> bool {
    &&& g.history.len() > 0
    &&& is_well_formed(g.history[0])
    &&& forall|i: int|
        0 <= i < g.history.len() - 1 ==> {
            &&& game_outcome(game_prefix(g, i + 1)) is None
            &&& exists|m: Move|
                is_legal(g.history[i], m) && #[trigger] g.history[i + 1] == apply_move(
                    g.history[i],
                    m,
                )
        }
}

/// Number of positions among the first `n` of `h` whose key equals `k`.
pub open spec fn occurrences(h: Seq<PositionModel>, k: PositionKey, n: int) -> nat
    decreases n,
{
    if n <= 0 {
        0
    } else {
        occurrences(h, k, n - 1) + if repetition_key(h[n - 1]) == k {
            1nat
        } else {
            0nat
        }
    }
}

/// How often the current position has occurred in the game (including now).
pub open spec fn repetition_count(g: GameModel) -> nat {
    occurrences(g.history, repetition_key(current(g)), g.history.len() as int)
}

/// Ways the game ends automatically, without a claim.
pub open spec fn game_outcome(g: GameModel) -> Option<GameOutcome> {
    let pos = current(g);
    if is_checkmate(pos) {
        Some(GameOutcome::Checkmate { winner: opponent(pos.turn) })
    } else if is_stalemate(pos) {
        Some(GameOutcome::Stalemate)
    } else if insufficient_material(pos.board) {
        Some(GameOutcome::InsufficientMaterial)
    } else if pos.halfmove_clock >= 150 {
        // FIDE 9.6.2 (a checkmate on the 75th move takes precedence, handled above)
        Some(GameOutcome::SeventyFiveMoveRule)
    } else if repetition_count(g) >= 5 {
        // FIDE 9.6.1
        Some(GameOutcome::FivefoldRepetition)
    } else {
        None
    }
}

/// A player may claim a draw in the current position (FIDE 9.2 and 9.3).
/// No claim is possible once the game has already ended (e.g. the last move gave
/// checkmate, which takes precedence: FIDE 5.1.1, 9.6).
/// (Claims made by announcing a move that would produce the condition are not modelled.)
pub open spec fn can_claim_draw(g: GameModel) -> bool {
    &&& game_outcome(g) is None
    &&& current(g).halfmove_clock >= 100 || repetition_count(g) >= 3
}

} // verus!
