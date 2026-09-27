//! Move legality, making moves, and legal move generation — all proven to match `spec`.
//!
//! Legal move generation visits the pieces of the side to move (a bitboard), computes the
//! bitboard of each one's pseudo-legal destinations (`dests`, proven exact), and keeps the
//! moves that leave the king safe. King safety is decided from the king's square, found
//! once per position (`scan_exec`): a move of another piece, from a king not in check, can
//! only expose the king along the line through its starting square (`lemma_discovered`,
//! `lemma_discovered_ray`), so most moves need no attack test at all.
use crate::attacks::*;
use crate::bitboard::*;
use crate::position::*;
#[cfg(verus_only)]
use crate::spec::*;
use crate::types::*;
use vstd::prelude::*;

verus! {

fn is_promotion_piece_exec(k: PieceKind) -> (r: bool)
    ensures
        r == is_promotion_piece(k),
{
    match k {
        PieceKind::Knight | PieceKind::Bishop | PieceKind::Rook | PieceKind::Queen => true,
        _ => false,
    }
}

fn promotion_ok_exec(p: Piece, m: Move) -> (r: bool)
    ensures
        r == promotion_ok(p, m),
{
    if kind_eq(p.kind, PieceKind::Pawn) && m.to.rank as i32 == promotion_rank_exec(p.color) {
        match m.promotion {
            Some(k) => is_promotion_piece_exec(k),
            None => false,
        }
    } else {
        m.promotion.is_none()
    }
}

fn has_color_exec(b: &[Option<Piece>; 64], f: i32, r: i32, c: Color) -> (res: bool)
    requires
        on_board(f as int, r as int),
    ensures
        res == has_color(b@, f as int, r as int, c),
{
    match get(b, f, r) {
        Some(p) => color_eq(p.color, c),
        None => false,
    }
}

fn is_empty_exec(b: &[Option<Piece>; 64], f: i32, r: i32) -> (res: bool)
    requires
        on_board(f as int, r as int),
    ensures
        res == is_empty(b@, f as int, r as int),
{
    get(b, f, r).is_none()
}

fn pawn_move_ok_exec(pos: &Position, m: Move) -> (res: bool)
    requires
        valid_square(m.from),
        valid_square(m.to),
    ensures
        res == pawn_move_ok(pos@, m),
{
    let b = &pos.board;
    let c = pos.turn;
    let fw = forward_exec(c);
    let opp = opponent_exec(c);
    let (f1, r1, f2, r2) = (m.from.file as i32, m.from.rank as i32, m.to.file as i32, m.to.rank as i32);
    let df = f2 - f1;
    let dr = r2 - r1;
    if df == 0 && dr == fw && is_empty_exec(b, f2, r2) {
        return true;
    }
    if df == 0 && dr == 2 * fw && r1 == pawn_start_rank_exec(c) && is_empty_exec(b, f1, r1 + fw)
        && is_empty_exec(b, f2, r2) {
        return true;
    }
    if abs_exec(df) == 1 && dr == fw {
        if has_color_exec(b, f2, r2, opp) {
            return true;
        }
        if opt_square_eq(pos.ep, Some(m.to)) && is_empty_exec(b, f2, r2) && opt_piece_eq(
            get(b, f2, r1),
            Some(Piece { color: opp, kind: PieceKind::Pawn }),
        ) {
            return true;
        }
    }
    false
}

fn has_kingside_right_exec(cr: CastlingRights, c: Color) -> (r: bool)
    ensures
        r == has_kingside_right(cr, c),
{
    match c {
        Color::White => cr.white_kingside,
        Color::Black => cr.black_kingside,
    }
}

fn has_queenside_right_exec(cr: CastlingRights, c: Color) -> (r: bool)
    ensures
        r == has_queenside_right(cr, c),
{
    match c {
        Color::White => cr.white_queenside,
        Color::Black => cr.black_queenside,
    }
}

fn castle_ok_exec(pos: &Position, m: Move) -> (res: bool)
    requires
        valid_square(m.from),
        valid_square(m.to),
    ensures
        res == castle_ok(pos@, m),
{
    let b = &pos.board;
    let c = pos.turn;
    let r = back_rank_exec(c);
    let opp = opponent_exec(c);
    let rook = Piece { color: c, kind: PieceKind::Rook };
    if !(m.from.file == 4 && m.from.rank as i32 == r && m.to.rank as i32 == r) {
        return false;
    }
    // Reject impossible destinations and absent rights before scanning for check.
    if !((m.to.file == 6 && has_kingside_right_exec(pos.castling, c))
        || (m.to.file == 2 && has_queenside_right_exec(pos.castling, c))) {
        return false;
    }
    if in_check_exec(b, c) {
        return false;
    }
    if m.to.file == 6 && has_kingside_right_exec(pos.castling, c) && opt_piece_eq(
        get(b, 7, r),
        Some(rook),
    ) && is_empty_exec(b, 5, r) && is_empty_exec(b, 6, r) && !is_attacked_exec(b, 5, r, opp)
        && !is_attacked_exec(b, 6, r, opp) {
        return true;
    }
    m.to.file == 2 && has_queenside_right_exec(pos.castling, c) && opt_piece_eq(
        get(b, 0, r),
        Some(rook),
    ) && is_empty_exec(b, 1, r) && is_empty_exec(b, 2, r) && is_empty_exec(b, 3, r)
        && !is_attacked_exec(b, 3, r, opp) && !is_attacked_exec(b, 2, r, opp)
}

pub fn is_pseudo_legal_exec(pos: &Position, m: Move) -> (res: bool)
    ensures
        res == is_pseudo_legal(pos@, m),
{
    if !(m.from.file < 8 && m.from.rank < 8 && m.to.file < 8 && m.to.rank < 8) {
        return false;
    }
    let b = &pos.board;
    let (f1, r1, f2, r2) = (m.from.file as i32, m.from.rank as i32, m.to.file as i32, m.to.rank as i32);
    match get_sq(b, m.from) {
        None => false,
        Some(p) => {
            if !color_eq(p.color, pos.turn) || !promotion_ok_exec(p, m) || has_color_exec(
                b,
                f2,
                r2,
                pos.turn,
            ) {
                return false;
            }
            match p.kind {
                PieceKind::Pawn => pawn_move_ok_exec(pos, m),
                PieceKind::King => attacks_exec(b, p, f1, r1, f2, r2) || castle_ok_exec(pos, m),
                _ => attacks_exec(b, p, f1, r1, f2, r2),
            }
        },
    }
}

pub fn is_en_passant_exec(pos: &Position, m: Move) -> (res: bool)
    requires
        valid_square(m.from),
        valid_square(m.to),
    ensures
        res == is_en_passant(pos@, m),
{
    match get_sq(&pos.board, m.from) {
        Some(p) => kind_eq(p.kind, PieceKind::Pawn) && opt_square_eq(pos.ep, Some(m.to))
            && m.from.file != m.to.file && get_sq(&pos.board, m.to).is_none(),
        None => false,
    }
}

pub fn is_castling_exec(pos: &Position, m: Move) -> (res: bool)
    requires
        valid_square(m.from),
        valid_square(m.to),
    ensures
        res == is_castling(pos@, m),
{
    match get_sq(&pos.board, m.from) {
        Some(p) => kind_eq(p.kind, PieceKind::King) && m.from.file == 4 && m.from.rank
            == m.to.rank && abs_exec(m.to.file as i32 - m.from.file as i32) == 2,
        None => false,
    }
}

/// The board after the move.
pub fn move_board_exec(pos: &Position, m: Move) -> (nb: [Option<Piece>; 64])
    requires
        valid_square(m.from),
        valid_square(m.to),
        moving_piece(pos@, m) is Some,
    ensures
        nb@ == move_board(pos@, m),
{
    let p = get_sq(&pos.board, m.from).unwrap();
    let placed = match m.promotion {
        Some(k) => Piece { color: p.color, kind: k },
        None => p,
    };
    let (f1, r1, f2, r2) = (
        m.from.file as usize,
        m.from.rank as usize,
        m.to.file as usize,
        m.to.rank as usize,
    );
    let ep = is_en_passant_exec(pos, m);
    let castle = is_castling_exec(pos, m);
    let mut b = pos.board;
    b[r1 * 8 + f1] = None;
    b[r2 * 8 + f2] = Some(placed);
    if ep {
        b[r1 * 8 + f2] = None;
    } else if castle {
        let rook = Some(Piece { color: p.color, kind: PieceKind::Rook });
        if f2 == 6 {
            b[r1 * 8 + 7] = None;
            b[r1 * 8 + 5] = rook;
        } else {
            b[r1 * 8 + 0] = None;
            b[r1 * 8 + 3] = rook;
        }
    }
    b
}

pub fn is_legal_exec(pos: &Position, m: Move) -> (res: bool)
    ensures
        res == is_legal(pos@, m),
{
    if !is_pseudo_legal_exec(pos, m) {
        return false;
    }
    let nb = move_board_exec(pos, m);
    !in_check_exec(&nb, pos.turn)
}

fn touches_exec(m: Move, f: u8, r: u8) -> (res: bool)
    ensures
        res == touches(m, f as int, r as int),
{
    (m.from.file == f && m.from.rank == r) || (m.to.file == f && m.to.rank == r)
}

/// The position after the pseudo-legal move `m`, given the board after it.
pub fn position_after_exec(pos: &Position, m: Move, board: [Option<Piece>; 64]) -> (np: Position)
    requires
        is_pseudo_legal(pos@, m),
        board@ == move_board(pos@, m),
        pos.halfmove_clock < u32::MAX,
        pos.fullmove_number < u32::MAX,
    ensures
        np@ == apply_move(pos@, m),
{
    let p = get_sq(&pos.board, m.from).unwrap();
    let pawn_move = kind_eq(p.kind, PieceKind::Pawn);
    // A pawn move resets the clock anyway, so only a capture on `to` matters (en passant is
    // a pawn move).
    let reset = pawn_move || get_sq(&pos.board, m.to).is_some();
    let double_push = pawn_move && abs_exec(m.to.rank as i32 - m.from.rank as i32) == 2;
    let cr = pos.castling;
    let np = Position {
        board,
        turn: opponent_exec(pos.turn),
        castling: CastlingRights {
            white_kingside: cr.white_kingside && !touches_exec(m, 4, 0) && !touches_exec(m, 7, 0),
            white_queenside: cr.white_queenside && !touches_exec(m, 4, 0) && !touches_exec(
                m,
                0,
                0,
            ),
            black_kingside: cr.black_kingside && !touches_exec(m, 4, 7) && !touches_exec(m, 7, 7),
            black_queenside: cr.black_queenside && !touches_exec(m, 4, 7) && !touches_exec(
                m,
                0,
                7,
            ),
        },
        ep: if double_push {
            Some(Square { file: m.from.file, rank: (m.from.rank + m.to.rank) / 2 })
        } else {
            None
        },
        halfmove_clock: if reset {
            0
        } else {
            pos.halfmove_clock + 1
        },
        fullmove_number: if color_eq(pos.turn, Color::Black) {
            pos.fullmove_number + 1
        } else {
            pos.fullmove_number
        },
    };
    assert(np@ == apply_move(pos@, m));
    np
}

/// Play a legal move.
pub fn apply_move_exec(pos: &Position, m: Move) -> (np: Position)
    requires
        is_legal(pos@, m),
        pos.halfmove_clock < u32::MAX,
        pos.fullmove_number < u32::MAX,
    ensures
        np@ == apply_move(pos@, m),
{
    position_after_exec(pos, m, move_board_exec(pos, m))
}

/// If `m` is legal, the position after it.
pub fn try_apply_move_exec(pos: &Position, m: Move) -> (res: Option<Position>)
    requires
        pos.halfmove_clock < u32::MAX,
        pos.fullmove_number < u32::MAX,
    ensures
        res is Some == is_legal(pos@, m),
        res matches Some(np) ==> np@ == apply_move(pos@, m),
{
    if !is_pseudo_legal_exec(pos, m) {
        return None;
    }
    let nb = move_board_exec(pos, m);
    if in_check_exec(&nb, pos.turn) {
        return None;
    }
    Some(position_after_exec(pos, m, nb))
}

// ---------------------------------------------------------------------------
// Legal move generation
// ---------------------------------------------------------------------------

// Destination bitboards: for the piece on a square, a bitboard (see `bitboard`) of exactly
// the squares it can move to, ignoring whether that leaves its king in check.

/// `to` is a destination of the piece `p` on `from`: `is_pseudo_legal` without the
/// conditions on whose piece it is and on the promotion.
pub open spec fn dest_ok(pos: PositionModel, p: Piece, from: Square, to: Square) -> bool {
    let b = pos.board;
    let m = Move { from, to, promotion: None };
    let (f1, r1, f2, r2) = (from.file as int, from.rank as int, to.file as int, to.rank as int);
    &&& !has_color(b, f2, r2, pos.turn)
    &&& match p.kind {
        PieceKind::Pawn => pawn_move_ok(pos, m),
        PieceKind::King => attacks(b, p, f1, r1, f2, r2) || castle_ok(pos, m),
        _ => attacks(b, p, f1, r1, f2, r2),
    }
}

pub proof fn lemma_pseudo_legal_dest(pos: PositionModel, m: Move, p: Piece)
    requires
        valid_square(m.from),
        valid_square(m.to),
        moving_piece(pos, m) == Some(p),
        p.color == pos.turn,
    ensures
        is_pseudo_legal(pos, m) == (promotion_ok(p, m) && dest_ok(pos, p, m.from, m.to)),
{
}

/// The bitboard of `t` is exactly the destinations of `p` on `from`.
pub open spec fn dests_exact(pos: PositionModel, p: Piece, from: Square, t: u64) -> bool {
    forall|to: Square| valid_square(to) ==> (#[trigger] bit(t, sq_index(to)) == dest_ok(pos, p, from, to))
}

/// Adds (f + df, r + dr) if it is on the board and has no piece of the side to move.
fn with_step(pos: &Position, t: u64, f: i32, r: i32, df: i32, dr: i32) -> (y: u64)
    requires
        on_board(f as int, r as int),
        -2 <= df <= 2,
        -2 <= dr <= 2,
    ensures
        forall|j: int| 0 <= j < 64 ==> #[trigger] bit(y, j) == (bit(t, j) || (on_board(f + df, r + dr)
            && !has_color(pos@.board, f + df, r + dr, pos.turn) && j == index_of(f + df, r + dr))),
{
    let g = f + df;
    let h = r + dr;
    if 0 <= g && g < 8 && 0 <= h && h < 8 && !has_color_exec(&pos.board, g, h, pos.turn) {
        with_bit(t, g, h)
    } else {
        t
    }
}

fn knight_dests(pos: &Position, from: Square, Ghost(p): Ghost<Piece>) -> (t: u64)
    requires
        valid_square(from),
        p.kind == PieceKind::Knight,
    ensures
        dests_exact(pos@, p, from, t),
{
    let (f, r) = (from.file as i32, from.rank as i32);
    proof {
        assert forall|j: int| 0 <= j < 64 implies !#[trigger] bit(0u64, j) by {
            lemma_bit_zero(j as u64);
        }
    }
    let t = with_step(pos, 0, f, r, 1, 2);
    let t = with_step(pos, t, f, r, 2, 1);
    let t = with_step(pos, t, f, r, 2, -1);
    let t = with_step(pos, t, f, r, 1, -2);
    let t = with_step(pos, t, f, r, -1, -2);
    let t = with_step(pos, t, f, r, -2, -1);
    let t = with_step(pos, t, f, r, -2, 1);
    let t = with_step(pos, t, f, r, -1, 2);
    proof {
        assert forall|to: Square| valid_square(to) implies (#[trigger] bit(t, sq_index(to)) == dest_ok(
            pos@,
            p,
            from,
            to,
        )) by {
            lemma_index_square(to);
            let (f2, r2) = (to.file as int, to.rank as int);
        }
    }
    t
}

/// Castling destination `(to_file, back rank)` of the king on e1/e8, given whether the side
/// to move is in check.
fn castle_dest_ok(pos: &Position, to_file: u8, checked: bool) -> (res: bool)
    requires
        to_file == 6 || to_file == 2,
        checked == in_check(pos@.board, pos.turn),
    ensures
        res == castle_ok(
            pos@,
            Move {
                from: Square { file: 4, rank: back_rank(pos.turn) as u8 },
                to: Square { file: to_file, rank: back_rank(pos.turn) as u8 },
                promotion: None,
            },
        ),
{
    let b = &pos.board;
    let c = pos.turn;
    let r = back_rank_exec(c);
    let opp = opponent_exec(c);
    let rook = Some(Piece { color: c, kind: PieceKind::Rook });
    if checked {
        return false;
    }
    if to_file == 6 {
        has_kingside_right_exec(pos.castling, c) && opt_piece_eq(get(b, 7, r), rook) && is_empty_exec(
            b,
            5,
            r,
        ) && is_empty_exec(b, 6, r) && !is_attacked_exec(b, 5, r, opp) && !is_attacked_exec(
            b,
            6,
            r,
            opp,
        )
    } else {
        has_queenside_right_exec(pos.castling, c) && opt_piece_eq(get(b, 0, r), rook)
            && is_empty_exec(b, 1, r) && is_empty_exec(b, 2, r) && is_empty_exec(b, 3, r)
            && !is_attacked_exec(b, 3, r, opp) && !is_attacked_exec(b, 2, r, opp)
    }
}

fn king_dests(pos: &Position, from: Square, Ghost(p): Ghost<Piece>, checked: bool) -> (t: u64)
    requires
        valid_square(from),
        p.kind == PieceKind::King,
        checked == in_check(pos@.board, pos.turn),
    ensures
        dests_exact(pos@, p, from, t),
{
    let (f, r) = (from.file as i32, from.rank as i32);
    proof {
        assert forall|j: int| 0 <= j < 64 implies !#[trigger] bit(0u64, j) by {
            lemma_bit_zero(j as u64);
        }
    }
    let t = with_step(pos, 0, f, r, 1, 0);
    let t = with_step(pos, t, f, r, 1, 1);
    let t = with_step(pos, t, f, r, 0, 1);
    let t = with_step(pos, t, f, r, -1, 1);
    let t = with_step(pos, t, f, r, -1, 0);
    let t = with_step(pos, t, f, r, -1, -1);
    let t = with_step(pos, t, f, r, 0, -1);
    let t1 = with_step(pos, t, f, r, 1, -1);
    let mut t2 = t1;
    let home = f == 4 && r == back_rank_exec(pos.turn);
    if home {
        if castle_dest_ok(pos, 6, checked) {
            t2 = with_bit(t2, 6, r);
        }
        if castle_dest_ok(pos, 2, checked) {
            t2 = with_bit(t2, 2, r);
        }
    }
    proof {
        assert forall|to: Square| valid_square(to) implies (#[trigger] bit(t2, sq_index(to)) == dest_ok(
            pos@,
            p,
            from,
            to,
        )) by {
            lemma_index_square(to);
            let m = Move { from, to, promotion: None };
            if home {
                assert(from == Square { file: 4, rank: back_rank(pos.turn) as u8 });
            }
            if castle_ok(pos@, m) {
                assert(home);
            }
        }
    }
    t2
}

/// A diagonal pawn step onto (f2, r2) from rank r1 captures something (possibly en passant).
fn pawn_capture_ok(pos: &Position, f2: i32, r2: i32, r1: i32) -> (res: bool)
    requires
        on_board(f2 as int, r2 as int),
        on_board(f2 as int, r1 as int),
    ensures
        res == (has_color(pos@.board, f2 as int, r2 as int, opponent(pos.turn)) || (pos.ep == Some(
            Square { file: f2 as u8, rank: r2 as u8 },
        ) && is_empty(pos@.board, f2 as int, r2 as int) && at(pos@.board, f2 as int, r1 as int)
            == Some(Piece { color: opponent(pos.turn), kind: PieceKind::Pawn }))),
{
    let b = &pos.board;
    let opp = opponent_exec(pos.turn);
    has_color_exec(b, f2, r2, opp) || (opt_square_eq(
        pos.ep,
        Some(Square { file: f2 as u8, rank: r2 as u8 }),
    ) && is_empty_exec(b, f2, r2) && opt_piece_eq(
        get(b, f2, r1),
        Some(Piece { color: opp, kind: PieceKind::Pawn }),
    ))
}

fn pawn_dests(pos: &Position, from: Square, Ghost(p): Ghost<Piece>) -> (t: u64)
    requires
        valid_square(from),
        p.kind == PieceKind::Pawn,
    ensures
        dests_exact(pos@, p, from, t),
{
    let b = &pos.board;
    let c = pos.turn;
    let fw = forward_exec(c);
    let (f, r) = (from.file as i32, from.rank as i32);
    let r1 = r + fw;
    proof {
        assert forall|j: int| 0 <= j < 64 implies !#[trigger] bit(0u64, j) by {
            lemma_bit_zero(j as u64);
        }
    }
    let mut t: u64 = 0;
    if 0 <= r1 && r1 < 8 {
        if is_empty_exec(b, f, r1) {
            t = with_bit(t, f, r1);
            if r == pawn_start_rank_exec(c) && is_empty_exec(b, f, r1 + fw) {
                t = with_bit(t, f, r1 + fw);
            }
        }
        if f >= 1 && pawn_capture_ok(pos, f - 1, r1, r) {
            t = with_bit(t, f - 1, r1);
        }
        if f <= 6 && pawn_capture_ok(pos, f + 1, r1, r) {
            t = with_bit(t, f + 1, r1);
        }
        proof {
            assert forall|to: Square| valid_square(to) implies (#[trigger] bit(t, sq_index(to))
                == dest_ok(pos@, p, from, to)) by {
                lemma_index_square(to);
                let (f2, r2) = (to.file as int, to.rank as int);
                lemma_index_injective(f2, r2, f as int, r1 as int);
                if 0 <= r1 + fw < 8 {
                    lemma_index_injective(f2, r2, f as int, r1 + fw);
                }
                if f >= 1 {
                    lemma_index_injective(f2, r2, f - 1, r1 as int);
                }
                if f <= 6 {
                    lemma_index_injective(f2, r2, f + 1, r1 as int);
                }
                if f >= 1 && to == (Square { file: (f - 1) as u8, rank: r1 as u8 }) {
                    assert(Some(to) == Some(Square { file: (f - 1) as u8, rank: r1 as u8 }));
                }
                if f <= 6 && to == (Square { file: (f + 1) as u8, rank: r1 as u8 }) {
                    assert(Some(to) == Some(Square { file: (f + 1) as u8, rank: r1 as u8 }));
                }
            }
        }
    }
    t
}

/// The squares of the ray from (f, r) in direction (df, dr).
pub open spec fn in_dir(f: int, r: int, df: int, dr: int, f2: int, r2: int) -> bool {
    &&& (if df > 0 { f2 > f } else if df < 0 { f2 < f } else { f2 == f })
    &&& (if dr > 0 { r2 > r } else if dr < 0 { r2 < r } else { r2 == r })
    &&& (df == 0 || dr == 0 || abs(f2 - f) == abs(r2 - r))
}

pub proof fn lemma_in_dir_step(f: int, r: int, df: int, dr: int, f2: int, r2: int, k: int)
    requires
        unit_dir(df, dr),
        k >= 1,
    ensures
        (in_dir(f, r, df, dr, f2, r2) && distance(f2 - f, r2 - r) == k) <==> (f2 == step(f, df, k)
            && r2 == step(r, dr, k)),
{
}

/// The path from the origin of a ray to its `k`-th square is clear iff the squares before
/// it are empty.
pub proof fn lemma_path_clear_ray(b: Board, f: int, r: int, df: int, dr: int, k: int)
    requires
        unit_dir(df, dr),
        k >= 1,
    ensures
        path_clear(b, f, r, step(f, df, k), step(r, dr, k)) <==> (forall|j: int|
            1 <= j < k ==> #[trigger] is_empty(b, step(f, df, j), step(r, dr, j))),
{
    let (g, h) = (step(f, df, k), step(r, dr, k));
    assert(distance(g - f, h - r) == k);
    assert forall|j: int| 1 <= j < k implies step(f, g - f, j) == step(f, df, j) && step(r, h - r, j)
        == step(r, dr, j) by {}
    if path_clear(b, f, r, g, h) {
        assert forall|j: int| 1 <= j < k implies #[trigger] is_empty(b, step(f, df, j), step(r, dr, j)) by {
            assert(is_empty(b, step(f, g - f, j), step(r, h - r, j)));
        }
    }
    if forall|j: int| 1 <= j < k ==> #[trigger] is_empty(b, step(f, df, j), step(r, dr, j)) {
        assert forall|j: int| 0 < j < distance(g - f, h - r) implies #[trigger] is_empty(
            b,
            step(f, g - f, j),
            step(r, h - r, j),
        ) by {
            assert(is_empty(b, step(f, df, j), step(r, dr, j)));
        }
    }
}

/// Adds the destinations along one ray of a bishop, rook or queen on (f, r).
fn ray_dests(pos: &Position, t: u64, f: i32, r: i32, df: i32, dr: i32) -> (y: u64)
    requires
        on_board(f as int, r as int),
        unit_dir(df as int, dr as int),
    ensures
        forall|to: Square| valid_square(to) ==> #[trigger] bit(y, sq_index(to)) == (bit(t, sq_index(to))
            || (in_dir(f as int, r as int, df as int, dr as int, to.file as int, to.rank as int)
            && path_clear(pos@.board, f as int, r as int, to.file as int, to.rank as int)
            && !has_color(pos@.board, to.file as int, to.rank as int, pos.turn))),
{
    let b = &pos.board;
    let mut y = t;
    let ghost mut k: int = 1;
    let mut g = f + df;
    let mut h = r + dr;
    while 0 <= g && g < 8 && 0 <= h && h < 8
        invariant
            1 <= k <= 8,
            b@ == pos@.board,
            on_board(f as int, r as int),
            unit_dir(df as int, dr as int),
            g == step(f as int, df as int, k as int),
            h == step(r as int, dr as int, k as int),
            forall|j: int|
                1 <= j < k ==> #[trigger] is_empty(
                    b@,
                    step(f as int, df as int, j),
                    step(r as int, dr as int, j),
                ),
            forall|to: Square| valid_square(to) ==> #[trigger] bit(y, sq_index(to)) == (bit(t, sq_index(to))
                || (in_dir(f as int, r as int, df as int, dr as int, to.file as int, to.rank as int)
                && distance(to.file - f, to.rank - r) < k)),
        decreases 8 - k,
    {
        let ghost y0 = y;
        let occupied = get(b, g, h).is_some();
        if !occupied || !has_color_exec(b, g, h, pos.turn) {
            y = with_bit(y, g, h);
        }
        proof {
            assert forall|to: Square| valid_square(to) implies (#[trigger] bit(y, sq_index(to)) == (bit(y0, sq_index(to))
                || (!(occupied && has_color(b@, g as int, h as int, pos.turn))
                    && in_dir(f as int, r as int, df as int, dr as int, to.file as int, to.rank as int)
                    && distance(to.file - f, to.rank - r) == k))) by {
                lemma_index_square(to);
                lemma_index_injective(to.file as int, to.rank as int, g as int, h as int);
                lemma_in_dir_step(f as int, r as int, df as int, dr as int, to.file as int, to.rank as int, k as int);
            }
        }
        if occupied {
            proof {
                assert forall|to: Square| valid_square(to) implies #[trigger] bit(y, sq_index(to)) == (bit(t, sq_index(to))
                    || (in_dir(f as int, r as int, df as int, dr as int, to.file as int, to.rank as int)
                    && path_clear(b@, f as int, r as int, to.file as int, to.rank as int)
                    && !has_color(b@, to.file as int, to.rank as int, pos.turn))) by {
                    let (f2, r2) = (to.file as int, to.rank as int);
                    if in_dir(f as int, r as int, df as int, dr as int, f2, r2) {
                        let d = distance(f2 - f, r2 - r);
                        lemma_in_dir_step(f as int, r as int, df as int, dr as int, f2, r2, d);
                        lemma_path_clear_ray(b@, f as int, r as int, df as int, dr as int, d);
                        if d > k {
                            assert(!is_empty(b@, step(f as int, df as int, k as int), step(r as int, dr as int, k as int)));
                        } else if d < k {
                            assert(is_empty(b@, step(f as int, df as int, d), step(r as int, dr as int, d)));
                        } else {
                            assert(f2 == g && r2 == h);
                            assert(path_clear(b@, f as int, r as int, f2, r2));
                        }
                    }
                }
            }
            return y;
        }
        proof {
            k = k + 1;
        }
        g += df;
        h += dr;
    }
    proof {
        assert forall|to: Square| valid_square(to) implies #[trigger] bit(y, sq_index(to)) == (bit(t, sq_index(to))
            || (in_dir(f as int, r as int, df as int, dr as int, to.file as int, to.rank as int)
            && path_clear(b@, f as int, r as int, to.file as int, to.rank as int)
            && !has_color(b@, to.file as int, to.rank as int, pos.turn))) by {
            let (f2, r2) = (to.file as int, to.rank as int);
            if in_dir(f as int, r as int, df as int, dr as int, f2, r2) {
                let d = distance(f2 - f, r2 - r);
                lemma_in_dir_step(f as int, r as int, df as int, dr as int, f2, r2, d);
                lemma_path_clear_ray(b@, f as int, r as int, df as int, dr as int, d);
                assert(d < k);
                assert(is_empty(b@, step(f as int, df as int, d), step(r as int, dr as int, d)));
            }
        }
    }
    y
}

/// The eight rays from (f, r) partition the orthogonal and diagonal lines through it.
pub proof fn lemma_dirs(f: int, r: int, f2: int, r2: int)
    ensures
        is_orthogonal(f2 - f, r2 - r) <==> (in_dir(f, r, 1, 0, f2, r2) || in_dir(f, r, -1, 0, f2, r2)
            || in_dir(f, r, 0, 1, f2, r2) || in_dir(f, r, 0, -1, f2, r2)),
        is_diagonal(f2 - f, r2 - r) <==> (in_dir(f, r, 1, 1, f2, r2) || in_dir(f, r, 1, -1, f2, r2)
            || in_dir(f, r, -1, 1, f2, r2) || in_dir(f, r, -1, -1, f2, r2)),
{
}

fn slider_dests(pos: &Position, from: Square, p: Piece) -> (t: u64)
    requires
        valid_square(from),
        p.kind == PieceKind::Bishop || p.kind == PieceKind::Rook || p.kind == PieceKind::Queen,
    ensures
        dests_exact(pos@, p, from, t),
{
    let (f, r) = (from.file as i32, from.rank as i32);
    proof {
        assert forall|j: int| 0 <= j < 64 implies !#[trigger] bit(0u64, j) by {
            lemma_bit_zero(j as u64);
        }
    }
    let straight = !kind_eq(p.kind, PieceKind::Bishop);
    let diagonal = !kind_eq(p.kind, PieceKind::Rook);
    let mut t: u64 = 0;
    if straight {
        t = ray_dests(pos, t, f, r, 1, 0);
        t = ray_dests(pos, t, f, r, -1, 0);
        t = ray_dests(pos, t, f, r, 0, 1);
        t = ray_dests(pos, t, f, r, 0, -1);
    }
    if diagonal {
        t = ray_dests(pos, t, f, r, 1, 1);
        t = ray_dests(pos, t, f, r, 1, -1);
        t = ray_dests(pos, t, f, r, -1, 1);
        t = ray_dests(pos, t, f, r, -1, -1);
    }
    proof {
        assert forall|to: Square| valid_square(to) implies (#[trigger] bit(t, sq_index(to)) == dest_ok(
            pos@,
            p,
            from,
            to,
        )) by {
            lemma_index_square(to);
            lemma_dirs(f as int, r as int, to.file as int, to.rank as int);
        }
    }
    t
}

/// The destinations of the piece `p` of the side to move on `from`.
fn dests(pos: &Position, from: Square, p: Piece, checked: bool) -> (t: u64)
    requires
        valid_square(from),
        p.kind == PieceKind::King ==> checked == in_check(pos@.board, pos.turn),
    ensures
        dests_exact(pos@, p, from, t),
{
    match p.kind {
        PieceKind::Pawn => pawn_dests(pos, from, Ghost(p)),
        PieceKind::Knight => knight_dests(pos, from, Ghost(p)),
        PieceKind::King => king_dests(pos, from, Ghost(p), checked),
        _ => slider_dests(pos, from, p),
    }
}


/// Moves whose (from, to) pair has already been enumerated.
pub open spec fn visited(m: Move, i: int, j: int) -> bool {
    sq_index(m.from) < i || (sq_index(m.from) == i && sq_index(m.to) < j)
}

pub proof fn lemma_legal_promotion(pos: PositionModel, m: Move)
    requires
        is_legal(pos, m),
    ensures
        valid_square(m.from),
        valid_square(m.to),
        m.promotion is None || m.promotion == Some(PieceKind::Knight) || m.promotion == Some(
            PieceKind::Bishop,
        ) || m.promotion == Some(PieceKind::Rook) || m.promotion == Some(PieceKind::Queen),
{
}

// ---------------------------------------------------------------------------
// King safety
// ---------------------------------------------------------------------------

/// What move generation knows about the king of the side to move.
pub struct KingInfo {
    /// The side to move has exactly one king, on (f, r).
    pub unique: bool,
    pub f: i32,
    pub r: i32,
    /// The side to move is in check.
    pub checked: bool,
}

pub open spec fn unique_king_at(b: Board, c: Color, kf: int, kr: int) -> bool {
    &&& on_board(kf, kr)
    &&& forall|f: int, r: int|
        on_board(f, r) ==> (#[trigger] at(b, f, r) == Some(king_of(c)) <==> (f == kf && r == kr))
}

pub open spec fn king_info_ok(pos: PositionModel, ki: KingInfo) -> bool {
    &&& ki.checked == in_check(pos.board, pos.turn)
    &&& ki.unique ==> unique_king_at(pos.board, pos.turn, ki.f as int, ki.r as int)
}

pub proof fn lemma_in_check_unique(b: Board, c: Color, kf: int, kr: int)
    requires
        unique_king_at(b, c, kf, kr),
    ensures
        in_check(b, c) == is_attacked(b, kf, kr, opponent(c)),
{
    assert(at(b, kf, kr) == Some(king_of(c)));
}

/// Bit `j` of `own` is set exactly when square `j` holds a piece of the side to move.
pub open spec fn own_pieces(pos: PositionModel, own: u64) -> bool {
    forall|j: int| 0 <= j < 64 ==> #[trigger] bit(own, j) == (pos.board[j] matches Some(p) && p.color == pos.turn)
}

/// One pass over the board: the pieces of the side to move, and its king.
fn scan_exec(pos: &Position) -> (res: (u64, KingInfo))
    ensures
        own_pieces(pos@, res.0),
        king_info_ok(pos@, res.1),
{
    let ghost king = Some(king_of(pos.turn));
    let mut own: u64 = 0;
    let mut kings: u8 = 0;
    let mut k: usize = 0;
    let mut i: usize = 0;
    proof {
        assert forall|j: int| 0 <= j < 64 implies !#[trigger] bit(0u64, j) by {
            lemma_bit_zero(j as u64);
        }
    }
    while i < 64
        invariant
            0 <= i <= 64,
            king == Some(king_of(pos.turn)),
            forall|j: int| 0 <= j < 64 ==> #[trigger] bit(own, j) == (j < i && (pos.board@[j] matches Some(p) && p.color == pos.turn)),
            kings <= 2,
            kings == 0 ==> forall|j: int| 0 <= j < i ==> pos.board@[j] != king,
            kings == 1 ==> k < i && pos.board@[k as int] == king && forall|j: int|
                0 <= j < i && pos.board@[j] == king ==> j == k,
        decreases 64 - i,
    {
        if let Some(p) = pos.board[i] {
            if color_eq(p.color, pos.turn) {
                let ghost own0 = own;
                own = own | (1u64 << (i as u64));
                proof {
                    assert forall|j: int| 0 <= j < 64 implies #[trigger] bit(own, j) == (bit(own0, j) || j == i) by {
                        lemma_bit_or(own0, i as u64, j as u64);
                    }
                }
                if kind_eq(p.kind, PieceKind::King) {
                    if kings == 0 {
                        k = i;
                    }
                    if kings < 2 {
                        kings += 1;
                    }
                }
            }
        }
        i += 1;
    }
    if kings != 1 {
        return (own, KingInfo { unique: false, f: 0, r: 0, checked: in_check_exec(&pos.board, pos.turn) });
    }
    let kf = (k % 8) as i32;
    let kr = (k / 8) as i32;
    proof {
        lemma_square_index(k as int);
        assert forall|f: int, r: int| on_board(f, r) implies (#[trigger] at(pos@.board, f, r) == Some(
            king_of(pos.turn),
        ) <==> (f == kf && r == kr)) by {
            lemma_index_injective(f, r, kf as int, kr as int);
        }
        lemma_in_check_unique(pos@.board, pos.turn, kf as int, kr as int);
    }
    let checked = is_attacked_exec(&pos.board, kf, kr, opponent_exec(pos.turn));
    (own, KingInfo { unique: true, f: kf, r: kr, checked })
}

/// A move of anything but the king leaves the king where it was.
proof fn lemma_king_stays(pos: PositionModel, m: Move, p: Piece, kf: int, kr: int)
    requires
        pos.board.len() == 64,
        is_pseudo_legal(pos, m),
        moving_piece(pos, m) == Some(p),
        p.kind != PieceKind::King,
        unique_king_at(pos.board, pos.turn, kf, kr),
    ensures
        unique_king_at(move_board(pos, m), pos.turn, kf, kr),
{
    let b = pos.board;
    let nb = move_board(pos, m);
    let (f1, r1, f2, r2) = (m.from.file as int, m.from.rank as int, m.to.file as int, m.to.rank as int);
    assert(!is_castling(pos, m));
    if is_en_passant(pos, m) {
        assert(at(b, f2, r1) == Some(Piece { color: opponent(pos.turn), kind: PieceKind::Pawn }));
    }
    assert forall|f: int, r: int| on_board(f, r) implies (#[trigger] at(nb, f, r) == Some(
        king_of(pos.turn),
    ) <==> (f == kf && r == kr)) by {
        lemma_index_injective(f, r, f1, r1);
        lemma_index_injective(f, r, f2, r2);
        lemma_index_injective(f, r, f2, r1);
        assert(at(b, f, r) == Some(king_of(pos.turn)) <==> (f == kf && r == kr));
    }
}

/// A king move (including castling) takes the only king to the destination.
proof fn lemma_king_moves(pos: PositionModel, m: Move, p: Piece, kf: int, kr: int)
    requires
        pos.board.len() == 64,
        is_pseudo_legal(pos, m),
        moving_piece(pos, m) == Some(p),
        p.kind == PieceKind::King,
        unique_king_at(pos.board, pos.turn, kf, kr),
    ensures
        unique_king_at(move_board(pos, m), pos.turn, m.to.file as int, m.to.rank as int),
{
    let b = pos.board;
    let nb = move_board(pos, m);
    let (f1, r1, f2, r2) = (m.from.file as int, m.from.rank as int, m.to.file as int, m.to.rank as int);
    assert(at(b, f1, r1) == Some(king_of(pos.turn)));
    assert(f1 == kf && r1 == kr);
    assert(!is_en_passant(pos, m));
    assert forall|f: int, r: int| on_board(f, r) implies (#[trigger] at(nb, f, r) == Some(
        king_of(pos.turn),
    ) <==> (f == f2 && r == r2)) by {
        lemma_index_injective(f, r, f1, r1);
        lemma_index_injective(f, r, f2, r2);
        lemma_index_injective(f, r, 7, r1);
        lemma_index_injective(f, r, 5, r1);
        lemma_index_injective(f, r, 0, r1);
        lemma_index_injective(f, r, 3, r1);
        assert(at(b, f, r) == Some(king_of(pos.turn)) <==> (f == kf && r == kr));
    }
}

/// (f, r) lies on a rank, file or diagonal through (kf, kr).
pub open spec fn aligned(kf: int, kr: int, f: int, r: int) -> bool {
    f == kf || r == kr || abs(f - kf) == abs(r - kr)
}

/// A move of anything but the king, other than en passant, cannot expose a king that is
/// not in check unless it starts on a line through the king.
proof fn lemma_discovered(pos: PositionModel, m: Move, p: Piece, kf: int, kr: int)
    requires
        pos.board.len() == 64,
        is_pseudo_legal(pos, m),
        moving_piece(pos, m) == Some(p),
        p.kind != PieceKind::King,
        !is_en_passant(pos, m),
        on_board(kf, kr),
        !is_attacked(pos.board, kf, kr, opponent(pos.turn)),
        !aligned(kf, kr, m.from.file as int, m.from.rank as int),
    ensures
        !is_attacked(move_board(pos, m), kf, kr, opponent(pos.turn)),
{
    let b = pos.board;
    let nb = move_board(pos, m);
    let opp = opponent(pos.turn);
    let (f1, r1, f2, r2) = (m.from.file as int, m.from.rank as int, m.to.file as int, m.to.rank as int);
    assert(!is_castling(pos, m));
    assert forall|a: int, c: int| on_board(a, c) implies !#[trigger] attacker_at(nb, a, c, kf, kr, opp) by {
        if attacker_at(nb, a, c, kf, kr, opp) {
            lemma_index_injective(a, c, f1, r1);
            lemma_index_injective(a, c, f2, r2);
            assert(at(nb, a, c) == at(b, a, c));
            let q = at(b, a, c)->Some_0;
            if q.kind == PieceKind::Bishop || q.kind == PieceKind::Rook || q.kind == PieceKind::Queen {
                assert forall|j: int| 0 < j < distance(kf - a, kr - c) implies #[trigger] is_empty(
                    b,
                    step(a, kf - a, j),
                    step(c, kr - c, j),
                ) by {
                    let (sf, sr) = (step(a, kf - a, j), step(c, kr - c, j));
                    assert(is_empty(nb, sf, sr));
                    assert(on_board(sf, sr));
                    lemma_index_injective(sf, sr, f1, r1);
                    lemma_index_injective(sf, sr, f2, r2);
                    if sf == f1 && sr == r1 {
                        assert(aligned(kf, kr, f1, r1));
                    }
                }
            }
            assert(attacker_at(b, a, c, kf, kr, opp));
        }
    }
}

/// The same, when the move starts on a line through the king: only a bishop, rook or queen
/// on the ray from the king through the vacated square can be uncovered.
proof fn lemma_discovered_ray(pos: PositionModel, m: Move, p: Piece, kf: int, kr: int, sf: int, sr: int)
    requires
        pos.board.len() == 64,
        is_pseudo_legal(pos, m),
        moving_piece(pos, m) == Some(p),
        p.kind != PieceKind::King,
        !is_en_passant(pos, m),
        on_board(kf, kr),
        !is_attacked(pos.board, kf, kr, opponent(pos.turn)),
        sf == (if m.from.file as int > kf { 1int } else if (m.from.file as int) < kf { -1int } else { 0int }),
        sr == (if m.from.rank as int > kr { 1int } else if (m.from.rank as int) < kr { -1int } else { 0int }),
        is_attacked(move_board(pos, m), kf, kr, opponent(pos.turn)),
    ensures
        exists|k: int|
            k >= 1 && on_board(step(kf, sf, k), step(kr, sr, k)) && #[trigger] slider_attacker_at(
                move_board(pos, m),
                step(kf, sf, k),
                step(kr, sr, k),
                kf,
                kr,
                opponent(pos.turn),
            ),
{
    let b = pos.board;
    let nb = move_board(pos, m);
    let opp = opponent(pos.turn);
    let (f1, r1, f2, r2) = (m.from.file as int, m.from.rank as int, m.to.file as int, m.to.rank as int);
    assert(!is_castling(pos, m));
    let (a, c) = choose|a: int, c: int| on_board(a, c) && #[trigger] attacker_at(nb, a, c, kf, kr, opp);
    lemma_index_injective(a, c, f1, r1);
    lemma_index_injective(a, c, f2, r2);
    assert(at(nb, a, c) == at(b, a, c));
    let q = at(b, a, c)->Some_0;
    if !attacks(b, q, a, c, kf, kr) {
        assert(q.kind == PieceKind::Bishop || q.kind == PieceKind::Rook || q.kind == PieceKind::Queen);
        let n = distance(kf - a, kr - c);
        assert(!path_clear(b, a, c, kf, kr));
        let j = choose|j: int| 0 < j < n && !#[trigger] is_empty(b, step(a, kf - a, j), step(c, kr - c, j));
        let (sa, sc) = (step(a, kf - a, j), step(c, kr - c, j));
        assert(is_empty(nb, sa, sc));
        assert(on_board(sa, sc));
        lemma_index_injective(sa, sc, f1, r1);
        lemma_index_injective(sa, sc, f2, r2);
        assert(sa == f1 && sc == r1);
        assert(a == step(kf, sf, n) && c == step(kr, sr, n));
        assert(slider_attacker_at(nb, step(kf, sf, n), step(kr, sr, n), kf, kr, opp));
    } else {
        assert(attacker_at(b, a, c, kf, kr, opp));
    }
}

/// Whether the pseudo-legal move `m` of `p` leaves the mover's king out of check.
fn king_safe_exec(pos: &Position, ki: &KingInfo, m: Move, p: Piece) -> (res: bool)
    requires
        is_pseudo_legal(pos@, m),
        moving_piece(pos@, m) == Some(p),
        king_info_ok(pos@, *ki),
    ensures
        res == !in_check(move_board(pos@, m), pos.turn),
{
    let opp = opponent_exec(pos.turn);
    if !ki.unique {
        let nb = move_board_exec(pos, m);
        return !in_check_exec(&nb, pos.turn);
    }
    if kind_eq(p.kind, PieceKind::King) {
        let nb = move_board_exec(pos, m);
        proof {
            lemma_king_moves(pos@, m, p, ki.f as int, ki.r as int);
            lemma_in_check_unique(nb@, pos.turn, m.to.file as int, m.to.rank as int);
        }
        return !is_attacked_exec(&nb, m.to.file as i32, m.to.rank as i32, opp);
    }
    proof {
        lemma_king_stays(pos@, m, p, ki.f as int, ki.r as int);
        lemma_in_check_unique(move_board(pos@, m), pos.turn, ki.f as int, ki.r as int);
        lemma_in_check_unique(pos@.board, pos.turn, ki.f as int, ki.r as int);
    }
    let df = m.from.file as i32 - ki.f;
    let dr = m.from.rank as i32 - ki.r;
    // En passant also vacates the captured pawn's square, so it gets the full test.
    let simple = !ki.checked && !is_en_passant_exec(pos, m);
    if simple && !(df == 0 || dr == 0 || abs_exec(df) == abs_exec(dr)) {
        proof {
            lemma_discovered(pos@, m, p, ki.f as int, ki.r as int);
        }
        return true;
    }
    let nb = move_board_exec(pos, m);
    if simple {
        // Only the line from the king through `from` can have opened.
        let sf: i32 = if df > 0 { 1 } else if df < 0 { -1 } else { 0 };
        let sr: i32 = if dr > 0 { 1 } else if dr < 0 { -1 } else { 0 };
        proof {
            if is_attacked(nb@, ki.f as int, ki.r as int, opponent(pos.turn)) {
                lemma_discovered_ray(pos@, m, p, ki.f as int, ki.r as int, sf as int, sr as int);
            }
        }
        return !ray_attacked_exec(&nb, ki.f, ki.r, sf, sr, opp, false);
    }
    !is_attacked_exec(&nb, ki.f, ki.r, opp)
}

/// Append the pseudo-legal move `m` to `moves` if it is legal.
fn try_push(pos: &Position, ki: &KingInfo, m: Move, p: Piece, moves: &mut Vec<Move>)
    requires
        is_pseudo_legal(pos@, m),
        moving_piece(pos@, m) == Some(p),
        king_info_ok(pos@, *ki),
    ensures
        is_legal(pos@, m) ==> final(moves)@ == old(moves)@.push(m),
        !is_legal(pos@, m) ==> final(moves)@ == old(moves)@,
        forall|x: Move|
            #[trigger] final(moves)@.contains(x) <==> old(moves)@.contains(x) || (x == m
                && is_legal(pos@, m)),
{
    if king_safe_exec(pos, ki, m, p) {
        let ghost prev = moves@;
        moves.push(m);
        assert forall|x: Move| #[trigger] moves@.contains(x) <==> prev.contains(x) || x == m by {
            if moves@.contains(x) {
                let k = choose|k: int| 0 <= k < moves@.len() && moves@[k] == x;
                if k < prev.len() {
                    assert(prev[k] == x);
                }
            }
            if prev.contains(x) {
                let k = choose|k: int| 0 <= k < prev.len() && prev[k] == x;
                assert(moves@[k] == x);
            }
            if x == m {
                assert(moves@[prev.len() as int] == x);
            }
        }
    }
}

/// Enumerate legal moves, optionally stopping after the first nonempty candidate pair.
/// The same traversal proves completeness for full generation and for an empty search.
///
/// For every piece of the side to move, the destination bitboard (`dests`) is walked in
/// increasing square order; each destination is a pseudo-legal move, which is kept if it
/// leaves the king safe (`king_safe_exec`).
// Specialize the traversal for the two callers so full generation has no stop flag branch.
#[inline(always)]
fn collect_legal_moves(pos: &Position, own: u64, ki: &KingInfo, stop_after_first: bool) -> (moves: Vec<Move>)
    requires
        own_pieces(pos@, own),
        king_info_ok(pos@, *ki),
    ensures
        forall|m: Move| #[trigger] moves@.contains(m) ==> is_legal(pos@, m),
        !stop_after_first || moves@.len() == 0 ==>
            forall|m: Move| #[trigger] moves@.contains(m) <==> is_legal(pos@, m),
        moves@.no_duplicates(),
{
    let mut moves: Vec<Move> = Vec::with_capacity(if stop_after_first { 4 } else { 64 });
    let promo_rank = promotion_rank_exec(pos.turn);
    // The squares of the pieces of the side to move, lowest first; the others have no moves.
    let mut rem_from = own;
    let ghost mut lo_from: int = 0;
    while rem_from != 0
        invariant
            own_pieces(pos@, own),
            king_info_ok(pos@, *ki),
            promo_rank == promotion_rank(pos.turn),
            0 <= lo_from <= 64,
            forall|j: int| 0 <= j < 64 ==> #[trigger] bit(rem_from, j) == (bit(own, j) && j >= lo_from),
            forall|m: Move| #[trigger] moves@.contains(m) <==> is_legal(pos@, m) && visited(m, lo_from, 0),
            forall|k: int| 0 <= k < moves@.len() ==> visited(#[trigger] moves@[k], lo_from, 0),
            moves@.no_duplicates(),
        decreases 64 - lo_from,
    {
        proof {
            vstd::std_specs::bits::axiom_u64_trailing_zeros(rem_from);
        }
        let i = rem_from.trailing_zeros() as u8;
        assert(bit(rem_from, i as int));
        let from = Square { file: i % 8, rank: i / 8 };
        proof {
            lemma_square_index(i as int);
            // The squares between `lo_from` and `i` have no piece of the side to move.
            assert forall|m: Move| #[trigger] is_legal(pos@, m) && lo_from <= sq_index(m.from) < i
                implies false by {
                lemma_legal_promotion(pos@, m);
                lemma_index_square(m.from);
                assert(bit(own, sq_index(m.from)));
                assert(bit(rem_from, sq_index(m.from)));
                assert((rem_from >> (sq_index(m.from) as u64)) & 1u64 == 0u64);
            }
            assert forall|m: Move| #[trigger] moves@.contains(m) <==> is_legal(pos@, m) && visited(m, i as int, 0) by {
                if is_legal(pos@, m) {
                    lemma_legal_promotion(pos@, m);
                    lemma_index_square(m.from);
                }
            }
            assert forall|k: int| 0 <= k < moves@.len() implies visited(#[trigger] moves@[k], i as int, 0) by {
                assert(visited(moves@[k], lo_from, 0));
            }
        }
        assert(from == square_of_index(i as int));
        let piece = get_sq(&pos.board, from);
        let p = piece.unwrap();
        let t = dests(pos, from, p, ki.checked);
        let pawn = kind_eq(p.kind, PieceKind::Pawn);
        let mut rem = t;
        let ghost mut lo: int = 0;
        while rem != 0
            invariant
                0 <= i < 64,
                from == square_of_index(i as int),
                sq_index(from) == i,
                valid_square(from),
                piece == piece_at(pos@.board, from),
                p.color == pos.turn,
                piece == Some(p),
                dests_exact(pos@, p, from, t),
                pawn == (p.kind == PieceKind::Pawn),
                own_pieces(pos@, own),
                0 <= lo_from <= i,
                forall|j: int| 0 <= j < 64 ==> #[trigger] bit(rem_from, j) == (bit(own, j) && j >= i),
                king_info_ok(pos@, *ki),
                promo_rank == promotion_rank(pos.turn),
                0 <= lo <= 64,
                forall|j: int| 0 <= j < 64 ==> #[trigger] bit(rem, j) == (bit(t, j) && j >= lo),
                forall|m: Move| #[trigger] moves@.contains(m) <==> is_legal(pos@, m) && visited(m, i as int, lo),
                forall|k: int| 0 <= k < moves@.len() ==> visited(#[trigger] moves@[k], i as int, lo),
                moves@.no_duplicates(),
            decreases 64 - lo,
        {
            let jj = rem.trailing_zeros();
            proof {
                vstd::std_specs::bits::axiom_u64_trailing_zeros(rem);
            }
            let j = jj as u8;
            assert(bit(rem, j as int));
            let to = Square { file: j % 8, rank: j / 8 };
            proof {
                lemma_square_index(j as int);
                // Nothing between `lo` and `j` is a destination.
                assert forall|m: Move| #[trigger] is_legal(pos@, m) && sq_index(m.from) == i && lo <= sq_index(m.to) < j
                    implies false by {
                    lemma_legal_promotion(pos@, m);
                    lemma_index_square(m.from);
                    lemma_index_square(m.to);
                    assert(m.from == from);
                    lemma_pseudo_legal_dest(pos@, m, p);
                    assert(bit(t, sq_index(m.to)));
                    assert(bit(rem, sq_index(m.to)));
                    assert((rem >> (sq_index(m.to) as u64)) & 1u64 == 0u64);
                }
            }
            let ghost old_moves = moves@;
            // `promotion_ok` allows exactly one shape of promotion for a given (from, to):
            // N/B/R/Q for a pawn reaching the last rank, none otherwise. Only try those.
            let promotes = pawn && to.rank as i32 == promo_rank;
            proof {
                assert(dest_ok(pos@, p, from, to));
                assert(moving_piece(pos@, Move { from, to, promotion: None }) == Some(p));
            }
            if promotes {
                proof {
                    lemma_pseudo_legal_dest(pos@, Move { from, to, promotion: Some(PieceKind::Knight) }, p);
                    lemma_pseudo_legal_dest(pos@, Move { from, to, promotion: Some(PieceKind::Bishop) }, p);
                    lemma_pseudo_legal_dest(pos@, Move { from, to, promotion: Some(PieceKind::Rook) }, p);
                    lemma_pseudo_legal_dest(pos@, Move { from, to, promotion: Some(PieceKind::Queen) }, p);
                }
                try_push(pos, ki, Move { from, to, promotion: Some(PieceKind::Knight) }, p, &mut moves);
                try_push(pos, ki, Move { from, to, promotion: Some(PieceKind::Bishop) }, p, &mut moves);
                try_push(pos, ki, Move { from, to, promotion: Some(PieceKind::Rook) }, p, &mut moves);
                try_push(pos, ki, Move { from, to, promotion: Some(PieceKind::Queen) }, p, &mut moves);
            } else {
                proof {
                    lemma_pseudo_legal_dest(pos@, Move { from, to, promotion: None }, p);
                }
                try_push(pos, ki, Move { from, to, promotion: None }, p, &mut moves);
            }
            proof {
                assert forall|m: Move| #[trigger] moves@.contains(m) <==> is_legal(pos@, m) && visited(m, i as int, j + 1) by {
                    if is_legal(pos@, m) {
                        lemma_legal_promotion(pos@, m);
                        lemma_index_square(m.from);
                        lemma_index_square(m.to);
                        if sq_index(m.from) == i && sq_index(m.to) == j {
                            assert(m.from == from);
                            assert(m.to == to);
                            assert(promotion_ok(p, m));
                            assert(m.promotion is Some <==> promotes);
                        }
                    }
                    if moves@.contains(m) && !old_moves.contains(m) {
                        assert(m.from == from && m.to == to);
                    }
                }
                assert forall|k: int| 0 <= k < moves@.len() implies visited(#[trigger] moves@[k], i as int, j + 1) by {
                    if k >= old_moves.len() {
                        assert(moves@[k].from == from && moves@[k].to == to);
                    } else {
                        assert(moves@[k] == old_moves[k]);
                    }
                }
                assert forall|a: int, c: int| 0 <= a < c < moves@.len() implies moves@[a] != moves@[c] by {
                    if c >= old_moves.len() && a < old_moves.len() {
                        assert(visited(old_moves[a], i as int, lo));
                        assert(moves@[c].to == to);
                    }
                }
            }
            let ghost rem0 = rem;
            rem = rem ^ (1u64 << j);
            proof {
                assert forall|k: int| 0 <= k < 64 implies #[trigger] bit(rem, k) == (bit(t, k) && k >= j + 1) by {
                    lemma_bit_xor(rem0, j as u64, k as u64);
                    if lo <= k < j {
                        assert(bit(rem0, k) == bit(t, k));
                        assert((rem0 >> (k as u64)) & 1u64 == 0u64);
                    }
                }
                lo = j + 1;
            }
            if stop_after_first && moves.len() > 0 {
                return moves;
            }
        }
        proof {
            assert forall|j: int| 0 <= j < 64 implies !#[trigger] bit(rem, j) by {
                lemma_bit_zero(j as u64);
            }
            assert forall|m: Move| #[trigger] moves@.contains(m) <==> is_legal(pos@, m) && visited(m, i + 1, 0) by {
                if is_legal(pos@, m) {
                    lemma_legal_promotion(pos@, m);
                    lemma_index_square(m.from);
                    lemma_index_square(m.to);
                    if sq_index(m.from) == i {
                        assert(m.from == from);
                        lemma_pseudo_legal_dest(pos@, m, p);
                        assert(bit(t, sq_index(m.to)));
                        assert(bit(rem, sq_index(m.to)) || sq_index(m.to) < lo);
                    }
                }
            }
            assert forall|k: int| 0 <= k < moves@.len() implies visited(#[trigger] moves@[k], i + 1, 0) by {
                assert(visited(moves@[k], i as int, lo));
            }
        }
        let ghost rem0 = rem_from;
        rem_from = rem_from ^ (1u64 << i);
        proof {
            assert forall|k: int| 0 <= k < 64 implies #[trigger] bit(rem_from, k) == (bit(own, k) && k >= i + 1) by {
                lemma_bit_xor(rem0, i as u64, k as u64);
            }
            lo_from = i + 1;
        }
    }
    proof {
        assert forall|j: int| 0 <= j < 64 implies !#[trigger] bit(rem_from, j) by {
            lemma_bit_zero(j as u64);
        }
        assert forall|m: Move| #[trigger] moves@.contains(m) <==> is_legal(pos@, m) by {
            if is_legal(pos@, m) {
                lemma_legal_promotion(pos@, m);
                lemma_index_square(m.from);
                assert(bit(own, sq_index(m.from)));
                assert(!bit(rem_from, sq_index(m.from)));
            }
        }
    }
    moves
}

/// All legal moves, each exactly once.
pub fn legal_moves_exec(pos: &Position) -> (moves: Vec<Move>)
    ensures
        forall|m: Move| #[trigger] moves@.contains(m) <==> is_legal(pos@, m),
        moves@.no_duplicates(),
{
    let (own, ki) = scan_exec(pos);
    collect_legal_moves(pos, own, &ki, false)
}

fn has_legal_move_given(pos: &Position, own: u64, ki: &KingInfo) -> (res: bool)
    requires
        own_pieces(pos@, own),
        king_info_ok(pos@, *ki),
    ensures
        res == has_legal_move(pos@),
{
    let moves = collect_legal_moves(pos, own, ki, true);
    if moves.len() > 0 {
        assert(moves@.contains(moves@[0]));
        true
    } else {
        assert forall|m: Move| !is_legal(pos@, m) by {
            if is_legal(pos@, m) {
                assert(moves@.contains(m));
            }
        }
        false
    }
}

pub fn has_legal_move_exec(pos: &Position) -> (res: bool)
    ensures
        res == has_legal_move(pos@),
{
    let (own, ki) = scan_exec(pos);
    has_legal_move_given(pos, own, &ki)
}

/// Whether the side to move is in check, and whether it has a legal move.
pub fn check_status_exec(pos: &Position) -> (res: (bool, bool))
    ensures
        res.0 == in_check(pos@.board, pos.turn),
        res.1 == has_legal_move(pos@),
{
    let (own, ki) = scan_exec(pos);
    (ki.checked, has_legal_move_given(pos, own, &ki))
}

} // verus!
