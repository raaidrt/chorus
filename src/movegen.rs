//! Move legality, making moves, and legal move generation — all proven to match `spec`.
//!
//! Legal move generation tries, for each piece of the side to move, only the target
//! squares it could reach (see "Legal move generation" below), and checks each one with
//! what is known about the own king (see "Legality with a known king square").
use crate::attacks::*;
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
    // The cheap conditions first; the attack tests last.
    if m.to.file == 6 {
        has_kingside_right_exec(pos.castling, c) && opt_piece_eq(get(b, 7, r), Some(rook))
            && is_empty_exec(b, 5, r) && is_empty_exec(b, 6, r) && !in_check_exec(b, c)
            && !is_attacked_exec(b, 5, r, opp) && !is_attacked_exec(b, 6, r, opp)
    } else {
        m.to.file == 2 && has_queenside_right_exec(pos.castling, c) && opt_piece_eq(
            get(b, 0, r),
            Some(rook),
        ) && is_empty_exec(b, 1, r) && is_empty_exec(b, 2, r) && is_empty_exec(b, 3, r)
            && !in_check_exec(b, c) && !is_attacked_exec(b, 3, r, opp) && !is_attacked_exec(
            b,
            2,
            r,
            opp,
        )
    }
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

/// Play a legal move.
pub fn apply_move_exec(pos: &Position, m: Move) -> (np: Position)
    requires
        is_legal(pos@, m),
        pos.halfmove_clock < u32::MAX,
        pos.fullmove_number < u32::MAX,
    ensures
        np@ == apply_move(pos@, m),
{
    let p = get_sq(&pos.board, m.from).unwrap();
    let pawn_move = kind_eq(p.kind, PieceKind::Pawn);
    let capture = get_sq(&pos.board, m.to).is_some() || is_en_passant_exec(pos, m);
    let double_push = pawn_move && abs_exec(m.to.rank as i32 - m.from.rank as i32) == 2;
    let cr = pos.castling;
    let np = Position {
        board: move_board_exec(pos, m),
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
        halfmove_clock: if pawn_move || capture {
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

// ---------------------------------------------------------------------------
// Legal move generation
// ---------------------------------------------------------------------------

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
// Legality with a known king square
// ---------------------------------------------------------------------------

/// `ks`, if known, is the square of the only king of the side to move, and whether
/// that king is in check.
pub open spec fn king_hint(pos: PositionModel, ks: Option<(i32, i32, bool)>) -> bool {
    ks matches Some((f, r, chk)) ==> king_only_at(pos.board, pos.turn, f as int, r as int) && chk
        == in_check(pos.board, pos.turn)
}

/// After a pseudo-legal move, the (only) king is where it was, or where it moved to.
proof fn lemma_move_board_king(pos: PositionModel, m: Move, f: int, r: int)
    requires
        pos.board.len() == 64,
        is_pseudo_legal(pos, m),
        king_only_at(pos.board, pos.turn, f, r),
    ensures
        king_only_at(
            move_board(pos, m),
            pos.turn,
            if m.from.file == f && m.from.rank == r { m.to.file as int } else { f },
            if m.from.file == f && m.from.rank == r { m.to.rank as int } else { r },
        ),
{
    let b = pos.board;
    let c = pos.turn;
    let p = moving_piece(pos, m)->Some_0;
    let (f1, r1, f2, r2) = (m.from.file as int, m.from.rank as int, m.to.file as int, m.to.rank as int);
    let moved = f1 == f && r1 == r;
    let (nf, nr) = if moved { (f2, r2) } else { (f, r) };
    let nb = move_board(pos, m);
    // A king moves iff it is the king on (f, r); a promotion never produces a king.
    assert(p.kind == PieceKind::King <==> moved);
    // The target never holds a king of the mover (it holds no piece of the mover).
    assert(!(f2 == f && r2 == r)) by {
        assert(at(b, f, r) == Some(king_of(c)));
    }
    if is_en_passant(pos, m) {
        assert(at(b, f2, r1) == Some(Piece { color: opponent(c), kind: PieceKind::Pawn }));
    }
    if is_castling(pos, m) && !is_en_passant(pos, m) {
        assert(castle_ok(pos, m));
    }
    assert forall|g: int, h: int| on_board(g, h) implies (#[trigger] at(nb, g, h) == Some(king_of(c)) <==> (g == nf && h == nr)) by {
        if g == nf && h == nr {
        } else {
            if at(b, g, h) == Some(king_of(c)) {
                assert(g == f && h == r);
            }
        }
    }
}

/// If the king was not in check and did not move, a piece attacking it after the move
/// stands on the line from the king through the vacated square (or through the pawn
/// captured en passant): only a vacated square can open a line.
proof fn lemma_discovered(pos: PositionModel, m: Move, f: int, r: int, f1: int, r1: int)
    requires
        pos.board.len() == 64,
        is_pseudo_legal(pos, m),
        king_only_at(pos.board, pos.turn, f, r),
        !(m.from.file == f && m.from.rank == r),
        !is_attacked(pos.board, f, r, opponent(pos.turn)),
        on_board(f1, r1),
        attacker_at(move_board(pos, m), f1, r1, f, r, opponent(pos.turn)),
    ensures
        in_dir(f1 - f, r1 - r, sign(f1 - f), sign(r1 - r)),
        in_dir(m.from.file - f, m.from.rank - r, sign(f1 - f), sign(r1 - r)) || (is_en_passant(
            pos,
            m,
        ) && in_dir(m.to.file - f, m.from.rank - r, sign(f1 - f), sign(r1 - r))),
{
    let b = pos.board;
    let c = pos.turn;
    let opp = opponent(c);
    let nb = move_board(pos, m);
    let p = moving_piece(pos, m)->Some_0;
    let (mf1, mr1, mf2, mr2) = (m.from.file as int, m.from.rank as int, m.to.file as int, m.to.rank as int);
    let ep = is_en_passant(pos, m);
    let q = at(nb, f1, r1)->Some_0;
    assert(at(b, f, r) == Some(king_of(c)));
    // The mover is not the king, so the move is not castling.
    assert(p.kind != PieceKind::King);
    // Squares other than from, to and the en-passant square are unchanged.
    assert forall|g: int, h: int|
        on_board(g, h) && !(g == mf1 && h == mr1) && !(g == mf2 && h == mr2) && !(ep && g == mf2
            && h == mr1) implies #[trigger] at(nb, g, h) == at(b, g, h) by {}
    // The attacker is an enemy piece, so it was already there.
    assert(!(f1 == mf2 && r1 == mr2));
    assert(at(b, f1, r1) == Some(q));
    assert(!attacker_at(b, f1, r1, f, r, opp));
    assert(!attacks(b, q, f1, r1, f, r));
    // So it is a slider whose line was opened by a square that became empty.
    let df = f - f1;
    let dr = r - r1;
    let d = distance(df, dr);
    assert(path_clear(nb, f1, r1, f, r));
    assert(!path_clear(b, f1, r1, f, r));
    let j = choose|j: int| 0 < j < d && !#[trigger] is_empty(b, step(f1, df, j), step(r1, dr, j));
    assert(is_empty(nb, step(f1, df, j), step(r1, dr, j)));
    let (g, h) = (step(f1, df, j), step(r1, dr, j));
    let (sf, sr) = (sign(f1 - f), sign(r1 - r));
    lemma_in_dir(f1 - f, r1 - r, sf, sr);
    assert(g - f == step(0, sf, d - j));
    assert(h - r == step(0, sr, d - j));
    assert(in_dir(g - f, h - r, sf, sr));
    assert((g == mf1 && h == mr1) || (ep && g == mf2 && h == mr1));
}

/// Is (f, r) attacked along the line from it through (g, h), if there is such a line?
fn line_attacked_exec(b: &[Option<Piece>; 64], f: i32, r: i32, g: i32, h: i32, by: Color) -> (res: bool)
    requires
        on_board(f as int, r as int),
        on_board(g as int, h as int),
    ensures
        res ==> is_attacked(b@, f as int, r as int, by),
        !res ==> forall|f1: int, r1: int|
            on_board(f1, r1) && in_dir(f1 - f, r1 - r, sign(f1 - f), sign(r1 - r)) && in_dir(
                g - f,
                h - r,
                sign(f1 - f),
                sign(r1 - r),
            ) ==> !#[trigger] attacker_at(b@, f1, r1, f as int, r as int, by),
{
    let df = g - f;
    let dr = h - r;
    let orth = (df == 0) != (dr == 0);
    let diag = df != 0 && abs_exec(df) == abs_exec(dr);
    if orth || diag {
        let sf: i32 = if df > 0 { 1 } else if df < 0 { -1 } else { 0 };
        let sr: i32 = if dr > 0 { 1 } else if dr < 0 { -1 } else { 0 };
        ray_attacked_exec(b, f, r, sf, sr, by)
    } else {
        false
    }
}

/// Whether a pseudo-legal move leaves the own king safe, using what is known about the king.
fn legal_after_pseudo(pos: &Position, m: Move, ks: Option<(i32, i32, bool)>) -> (res: bool)
    requires
        king_hint(pos@, ks),
        is_pseudo_legal(pos@, m),
    ensures
        res == is_legal(pos@, m),
{
    match ks {
        None => {
            let nb = move_board_exec(pos, m);
            !in_check_exec(&nb, pos.turn)
        },
        Some((f, r, chk)) => {
            let nb = move_board_exec(pos, m);
            let opp = opponent_exec(pos.turn);
            let moved = m.from.file as i32 == f && m.from.rank as i32 == r;
            if moved || chk {
                let (nf, nr) = if moved { (m.to.file as i32, m.to.rank as i32) } else { (f, r) };
                proof {
                    lemma_move_board_king(pos@, m, f as int, r as int);
                    lemma_king_only_in_check(nb@, pos.turn, nf as int, nr as int);
                }
                !is_attacked_exec(&nb, nf, nr, opp)
            } else {
                // Only a line opened by the move can attack the king.
                let a = line_attacked_exec(&nb, f, r, m.from.file as i32, m.from.rank as i32, opp);
                let e = is_en_passant_exec(pos, m) && line_attacked_exec(
                    &nb,
                    f,
                    r,
                    m.to.file as i32,
                    m.from.rank as i32,
                    opp,
                );
                proof {
                    lemma_move_board_king(pos@, m, f as int, r as int);
                    lemma_king_only_in_check(nb@, pos.turn, f as int, r as int);
                    lemma_king_only_in_check(pos@.board, pos.turn, f as int, r as int);
                    if !(a || e) {
                        assert forall|f1: int, r1: int| on_board(f1, r1) implies !#[trigger] attacker_at(
                            nb@,
                            f1,
                            r1,
                            f as int,
                            r as int,
                            opp,
                        ) by {
                            if attacker_at(nb@, f1, r1, f as int, r as int, opp) {
                                lemma_discovered(pos@, m, f as int, r as int, f1, r1);
                            }
                        }
                    }
                }
                !(a || e)
            }
        },
    }
}

/// `is_legal_exec`, using what is known about the king.
fn is_legal_hint(pos: &Position, m: Move, ks: Option<(i32, i32, bool)>) -> (res: bool)
    requires
        king_hint(pos@, ks),
    ensures
        res == is_legal(pos@, m),
{
    is_pseudo_legal_exec(pos, m) && legal_after_pseudo(pos, m, ks)
}

/// A non-pawn piece of the side to move on `from` attacks `to`: moving there is
/// pseudo-legal exactly when `to` does not hold a piece of the side to move.
pub open spec fn geo_ok(pos: PositionModel, from: Square, to: Square) -> bool {
    &&& valid_square(from)
    &&& valid_square(to)
    &&& piece_at(pos.board, from) matches Some(p) && p.color == pos.turn && p.kind != PieceKind::Pawn
        && attacks(pos.board, p, from.file as int, from.rank as int, to.file as int, to.rank as int)
}

/// Append `m` to `moves` if it is legal.
fn try_push(pos: &Position, m: Move, ks: Option<(i32, i32, bool)>, geo: bool, moves: &mut Vec<Move>)
    requires
        king_hint(pos@, ks),
        geo ==> geo_ok(pos@, m.from, m.to) && m.promotion is None,
    ensures
        is_legal(pos@, m) ==> final(moves)@ == old(moves)@.push(m),
        !is_legal(pos@, m) ==> final(moves)@ == old(moves)@,
        forall|x: Move|
            #[trigger] final(moves)@.contains(x) <==> old(moves)@.contains(x) || (x == m
                && is_legal(pos@, m)),
{
    let legal = if geo {
        // The piece moves this way; only the target square remains to be checked.
        !has_color_exec(&pos.board, m.to.file as i32, m.to.rank as i32, pos.turn) && legal_after_pseudo(pos, m, ks)
    } else {
        is_legal_hint(pos, m, ks)
    };
    if legal {
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

// ---------------------------------------------------------------------------
// Legal move generation
//
// For each piece of the side to move, only the target squares it could possibly reach
// are tried: pawn pushes and captures, the knight and king offsets (plus the castling
// squares), and each line of a slider up to and including its first blocker.
// Each candidate is then checked with `is_legal_exec`. The ghost set `tried` records
// the target squares tried so far for the current piece, which gives both completeness
// (every legal target was tried) and the absence of duplicates (no square is tried twice).
// ---------------------------------------------------------------------------

pub open spec fn sq(f: int, r: int) -> Square {
    Square { file: f as u8, rank: r as u8 }
}

pub open spec fn is_pawn_at(b: Board, s: Square) -> bool {
    piece_at(b, s) matches Some(p) && p.kind == PieceKind::Pawn
}

/// No move generated before the current piece starts from its square.
pub open spec fn gen_ctx(from: Square, prior: Seq<Move>) -> bool {
    &&& prior.no_duplicates()
    &&& forall|k: int| 0 <= k < prior.len() ==> (#[trigger] prior[k]).from != from
}

/// `moves` extends `prior` with exactly the legal moves from `from` to a square in `tried`.
pub open spec fn gen_inv(pos: PositionModel, from: Square, prior: Seq<Move>, moves: Seq<Move>, tried: ISet<Square>) -> bool {
    &&& prior.len() <= moves.len()
    &&& forall|k: int| 0 <= k < prior.len() ==> #[trigger] moves[k] == prior[k]
    &&& forall|k: int|
        prior.len() <= k < moves.len() ==> (#[trigger] moves[k]).from == from && tried.contains(
            moves[k].to,
        )
    &&& forall|m: Move| #[trigger]
        moves.contains(m) <==> prior.contains(m) || (m.from == from && tried.contains(m.to)
            && is_legal(pos, m))
    &&& moves.no_duplicates()
}

/// `moves` extends `prior` with exactly the legal moves from `from`.
pub open spec fn gen_done(pos: PositionModel, from: Square, prior: Seq<Move>, moves: Seq<Move>) -> bool {
    &&& prior.len() <= moves.len()
    &&& forall|k: int| 0 <= k < prior.len() ==> #[trigger] moves[k] == prior[k]
    &&& forall|k: int| prior.len() <= k < moves.len() ==> (#[trigger] moves[k]).from == from
    &&& forall|m: Move| #[trigger]
        moves.contains(m) <==> prior.contains(m) || (m.from == from && is_legal(pos, m))
    &&& moves.no_duplicates()
}

proof fn lemma_gen_start(pos: PositionModel, from: Square, prior: Seq<Move>)
    requires
        gen_ctx(from, prior),
    ensures
        gen_inv(pos, from, prior, prior, ISet::empty()),
{
}

proof fn lemma_gen_done(pos: PositionModel, from: Square, prior: Seq<Move>, moves: Seq<Move>, tried: ISet<Square>)
    requires
        gen_inv(pos, from, prior, moves, tried),
        forall|m: Move| m.from == from && is_legal(pos, m) ==> tried.contains(m.to),
    ensures
        gen_done(pos, from, prior, moves),
{
}

/// Try every legal move from `from` to `to` (all four promotions if a pawn promotes).
fn try_to(pos: &Position, from: Square, ks: Option<(i32, i32, bool)>, to: Square, pawn: bool, geo: bool, moves: &mut Vec<Move>, Ghost(prior): Ghost<Seq<Move>>, Ghost(tried): Ghost<ISet<Square>>)
    requires
        king_hint(pos@, ks),
        valid_square(from),
        valid_square(to),
        pawn == is_pawn_at(pos@.board, from),
        geo ==> geo_ok(pos@, from, to),
        gen_ctx(from, prior),
        gen_inv(pos@, from, prior, old(moves)@, tried),
        !tried.contains(to),
    ensures
        gen_inv(pos@, from, prior, final(moves)@, tried.insert(to)),
{
    let ghost start = moves@;
    // `promotion_ok` allows exactly one shape of promotion for a given (from, to):
    // N/B/R/Q for a pawn reaching the last rank, none otherwise. Only try those.
    let promotes = pawn && to.rank as i32 == promotion_rank_exec(pos.turn);
    if promotes {
        try_push(pos, Move { from, to, promotion: Some(PieceKind::Knight) }, ks, false, moves);
        try_push(pos, Move { from, to, promotion: Some(PieceKind::Bishop) }, ks, false, moves);
        try_push(pos, Move { from, to, promotion: Some(PieceKind::Rook) }, ks, false, moves);
        try_push(pos, Move { from, to, promotion: Some(PieceKind::Queen) }, ks, false, moves);
    } else {
        try_push(pos, Move { from, to, promotion: None }, ks, geo, moves);
    }
    proof {
        let t2 = tried.insert(to);
        assert forall|m: Move| #[trigger] moves@.contains(m) <==> prior.contains(m) || (m.from == from
            && t2.contains(m.to) && is_legal(pos@, m)) by {
            if m.from == from && m.to == to && is_legal(pos@, m) {
                lemma_legal_promotion(pos@, m);
                assert(promotion_ok(piece_at(pos@.board, from)->Some_0, m));
                assert(m.promotion is Some <==> promotes);
            }
        }
        assert forall|k: int| start.len() <= k < moves@.len() implies (#[trigger] moves@[k]).from == from
            && moves@[k].to == to by {}
        assert forall|k: int| prior.len() <= k < moves@.len() implies (#[trigger] moves@[k]).from == from
            && t2.contains(moves@[k].to) by {
            if k < start.len() {
                assert(moves@[k] == start[k]);
            }
        }
        assert forall|k: int| 0 <= k < prior.len() implies #[trigger] moves@[k] == prior[k] by {
            assert(moves@[k] == start[k]);
        }
        assert forall|a: int, c: int| 0 <= a < c < moves@.len() implies moves@[a] != moves@[c] by {
            if c >= start.len() && a < start.len() {
                assert(moves@[a] == start[a]);
                if a >= prior.len() {
                    assert(tried.contains(start[a].to));
                } else {
                    assert(prior[a].from != from);
                }
            } else if a < start.len() {
                assert(moves@[a] == start[a]);
                assert(moves@[c] == start[c]);
            }
        }
    }
}

pub open spec fn offset_tried(tried: ISet<Square>, from: Square, df: int, dr: int) -> ISet<Square> {
    if on_board(from.file + df, from.rank + dr) {
        tried.insert(sq(from.file + df, from.rank + dr))
    } else {
        tried
    }
}

/// Try the target square at offset (df, dr) from `from`, if it is on the board.
fn try_offset(pos: &Position, from: Square, ks: Option<(i32, i32, bool)>, pawn: bool, geo: bool, df: i32, dr: i32, moves: &mut Vec<Move>, Ghost(prior): Ghost<Seq<Move>>, Ghost(tried): Ghost<ISet<Square>>)
    requires
        king_hint(pos@, ks),
        valid_square(from),
        -2 <= df <= 2,
        -2 <= dr <= 2,
        pawn == is_pawn_at(pos@.board, from),
        gen_ctx(from, prior),
        gen_inv(pos@, from, prior, old(moves)@, tried),
        on_board(from.file + df, from.rank + dr) ==> !tried.contains(sq(from.file + df, from.rank + dr)),
        geo ==> on_board(from.file + df, from.rank + dr) ==> geo_ok(pos@, from, sq(from.file + df, from.rank + dr)),
    ensures
        gen_inv(pos@, from, prior, final(moves)@, offset_tried(tried, from, df as int, dr as int)),
{
    let f = from.file as i32 + df;
    let r = from.rank as i32 + dr;
    if 0 <= f && f < 8 && 0 <= r && r < 8 {
        try_to(pos, from, ks, Square { file: f as u8, rank: r as u8 }, pawn, geo, moves, Ghost(prior), Ghost(tried));
    }
}

/// A piece of this kind moves along direction (sf, sr).
pub open spec fn slides(k: PieceKind, sf: int, sr: int) -> bool {
    ||| k == PieceKind::Queen
    ||| k == PieceKind::Rook && (sf == 0 || sr == 0)
    ||| k == PieceKind::Bishop && sf != 0 && sr != 0
}

pub open spec fn ray_sq(b: Board, from: Square, sf: int, sr: int, t: Square) -> bool {
    &&& valid_square(t)
    &&& in_dir(t.file - from.file, t.rank - from.rank, sf, sr)
    &&& path_clear(b, from.file as int, from.rank as int, t.file as int, t.rank as int)
}

pub open spec fn ray_tried(tried: ISet<Square>, b: Board, from: Square, sf: int, sr: int) -> ISet<Square> {
    tried.union(ISet::new(|t: Square| ray_sq(b, from, sf, sr, t)))
}

pub open spec fn ray_below(from: Square, sf: int, sr: int, k: int, t: Square) -> bool {
    &&& valid_square(t)
    &&& in_dir(t.file - from.file, t.rank - from.rank, sf, sr)
    &&& distance(t.file - from.file, t.rank - from.rank) < k
}

/// Try every square along the line from `from` in direction (sf, sr), up to and
/// including the first occupied square.
fn walk_ray(pos: &Position, from: Square, ks: Option<(i32, i32, bool)>, sf: i32, sr: i32, moves: &mut Vec<Move>, Ghost(prior): Ghost<Seq<Move>>, Ghost(tried): Ghost<ISet<Square>>)
    requires
        king_hint(pos@, ks),
        valid_square(from),
        unit_dir(sf as int, sr as int),
        !is_pawn_at(pos@.board, from),
        piece_at(pos@.board, from) matches Some(p) && p.color == pos@.turn && slides(p.kind, sf as int, sr as int),
        gen_ctx(from, prior),
        gen_inv(pos@, from, prior, old(moves)@, tried),
        forall|t: Square| #[trigger] tried.contains(t) ==> !in_dir(t.file - from.file, t.rank - from.rank, sf as int, sr as int),
    ensures
        gen_inv(pos@, from, prior, final(moves)@, ray_tried(tried, pos@.board, from, sf as int, sr as int)),
{
    let ghost (ff, fr, sfi, sri) = (from.file as int, from.rank as int, sf as int, sr as int);
    let ghost b = pos@.board;
    let ghost mut k: int = 1;
    let mut f = from.file as i32 + sf;
    let mut r = from.rank as i32 + sr;
    let ghost mut cur = tried;
    assert(cur =~= tried.union(ISet::new(|t: Square| ray_below(from, sfi, sri, 1, t))));
    while 0 <= f && f < 8 && 0 <= r && r < 8
        invariant
            valid_square(from),
            unit_dir(sfi, sri),
            ff == from.file,
            fr == from.rank as int,
            sfi == sf,
            sri == sr,
            b == pos@.board,
            king_hint(pos@, ks),
            !is_pawn_at(b, from),
            piece_at(b, from) matches Some(p) && p.color == pos@.turn && slides(p.kind, sfi, sri),
            gen_ctx(from, prior),
            forall|t: Square| #[trigger] tried.contains(t) ==> !in_dir(t.file - ff, t.rank - fr, sfi, sri),
            1 <= k <= 8,
            f == step(ff, sfi, k),
            r == step(fr, sri, k),
            forall|j: int| 1 <= j < k ==> #[trigger] is_empty(b, step(ff, sfi, j), step(fr, sri, j)),
            cur == tried.union(ISet::new(|t: Square| ray_below(from, sfi, sri, k, t))),
            gen_inv(pos@, from, prior, moves@, cur),
        decreases 8 - k,
    {
        let to = Square { file: f as u8, rank: r as u8 };
        proof {
            assert(distance(to.file - ff, to.rank - fr) == k);
            assert(!ray_below(from, sfi, sri, k, to));
            assert(sign(to.file - ff) == sfi && sign(to.rank - fr) == sri);
            assert forall|j: int| 0 < j < k implies #[trigger] is_empty(b, step(ff, to.file - ff, j), step(fr, to.rank - fr, j)) by {
                assert(step(ff, to.file - ff, j) == step(ff, sfi, j));
                assert(step(fr, to.rank - fr, j) == step(fr, sri, j));
                assert(is_empty(b, step(ff, sfi, j), step(fr, sri, j)));
            }
            assert(path_clear(b, ff, fr, to.file as int, to.rank as int));
            assert(geo_ok(pos@, from, to));
        }
        try_to(pos, from, ks, to, false, true, moves, Ghost(prior), Ghost(cur));
        proof {
            let next = tried.union(ISet::new(|t: Square| ray_below(from, sfi, sri, k + 1, t)));
            assert forall|t: Square| #[trigger] next.contains(t) <==> cur.insert(to).contains(t) by {
                if ray_below(from, sfi, sri, k + 1, t) && !ray_below(from, sfi, sri, k, t) {
                    lemma_in_dir(t.file - ff, t.rank - fr, sfi, sri);
                }
            }
            assert(next =~= cur.insert(to));
            cur = next;
        }
        if get(&pos.board, f, r).is_some() {
            proof {
                assert forall|t: Square| #[trigger] cur.contains(t) <==> ray_tried(tried, b, from, sfi, sri).contains(t) by {
                    if valid_square(t) && in_dir(t.file - ff, t.rank - fr, sfi, sri) {
                        let d = distance(t.file - ff, t.rank - fr);
                        lemma_in_dir(t.file - ff, t.rank - fr, sfi, sri);
                        assert forall|j: int| 0 < j < d implies step(ff, t.file - ff, j) == step(ff, sfi, j) && #[trigger] step(fr, t.rank - fr, j) == step(fr, sri, j) by {}
                        if d > k {
                            assert(step(ff, t.file - ff, k) == step(ff, sfi, k));
                            assert(step(fr, t.rank - fr, k) == step(fr, sri, k));
                            assert(!is_empty(b, step(ff, t.file - ff, k), step(fr, t.rank - fr, k)));
                        } else {
                            assert forall|j: int| 0 < j < d implies #[trigger] is_empty(b, step(ff, t.file - ff, j), step(fr, t.rank - fr, j)) by {
                                assert(is_empty(b, step(ff, sfi, j), step(fr, sri, j)));
                            }
                        }
                    }
                }
                assert(cur =~= ray_tried(tried, b, from, sfi, sri));
            }
            return;
        }
        proof {
            k = k + 1;
        }
        f += sf;
        r += sr;
    }
    proof {
        assert forall|t: Square| #[trigger] cur.contains(t) <==> ray_tried(tried, b, from, sfi, sri).contains(t) by {
            if valid_square(t) && in_dir(t.file - ff, t.rank - fr, sfi, sri) {
                let d = distance(t.file - ff, t.rank - fr);
                lemma_in_dir(t.file - ff, t.rank - fr, sfi, sri);
                assert(d < k);
                assert forall|j: int| 0 < j < d implies #[trigger] is_empty(b, step(ff, t.file - ff, j), step(fr, t.rank - fr, j)) by {
                    assert(step(ff, t.file - ff, j) == step(ff, sfi, j));
                    assert(step(fr, t.rank - fr, j) == step(fr, sri, j));
                    assert(is_empty(b, step(ff, sfi, j), step(fr, sri, j)));
                }
            }
        }
        assert(cur =~= ray_tried(tried, b, from, sfi, sri));
    }
}

fn gen_knight(pos: &Position, from: Square, ks: Option<(i32, i32, bool)>, moves: &mut Vec<Move>, Ghost(prior): Ghost<Seq<Move>>)
    requires
        king_hint(pos@, ks),
        valid_square(from),
        piece_at(pos@.board, from) matches Some(p) && p.kind == PieceKind::Knight && p.color == pos@.turn,
        gen_ctx(from, prior),
        old(moves)@ == prior,
    ensures
        gen_done(pos@, from, prior, final(moves)@),
{
    proof {
        lemma_gen_start(pos@, from, prior);
    }
    let ghost t0 = ISet::<Square>::empty();
    try_offset(pos, from, ks, false, true, 1, 2, moves, Ghost(prior), Ghost(t0));
    let ghost t1 = offset_tried(t0, from, 1, 2);
    try_offset(pos, from, ks, false, true, 2, 1, moves, Ghost(prior), Ghost(t1));
    let ghost t2 = offset_tried(t1, from, 2, 1);
    try_offset(pos, from, ks, false, true, 2, -1, moves, Ghost(prior), Ghost(t2));
    let ghost t3 = offset_tried(t2, from, 2, -1);
    try_offset(pos, from, ks, false, true, 1, -2, moves, Ghost(prior), Ghost(t3));
    let ghost t4 = offset_tried(t3, from, 1, -2);
    try_offset(pos, from, ks, false, true, -1, -2, moves, Ghost(prior), Ghost(t4));
    let ghost t5 = offset_tried(t4, from, -1, -2);
    try_offset(pos, from, ks, false, true, -2, -1, moves, Ghost(prior), Ghost(t5));
    let ghost t6 = offset_tried(t5, from, -2, -1);
    try_offset(pos, from, ks, false, true, -2, 1, moves, Ghost(prior), Ghost(t6));
    let ghost t7 = offset_tried(t6, from, -2, 1);
    try_offset(pos, from, ks, false, true, -1, 2, moves, Ghost(prior), Ghost(t7));
    let ghost t8 = offset_tried(t7, from, -1, 2);
    proof {
        assert forall|m: Move| m.from == from && is_legal(pos@, m) implies t8.contains(m.to) by {
            lemma_legal_promotion(pos@, m);
            assert(m.to == sq(m.to.file as int, m.to.rank as int));
        }
        lemma_gen_done(pos@, from, prior, moves@, t8);
    }
}

fn gen_king(pos: &Position, from: Square, ks: Option<(i32, i32, bool)>, moves: &mut Vec<Move>, Ghost(prior): Ghost<Seq<Move>>)
    requires
        king_hint(pos@, ks),
        valid_square(from),
        piece_at(pos@.board, from) matches Some(p) && p.kind == PieceKind::King && p.color == pos@.turn,
        gen_ctx(from, prior),
        old(moves)@ == prior,
    ensures
        gen_done(pos@, from, prior, final(moves)@),
{
    proof {
        lemma_gen_start(pos@, from, prior);
    }
    let ghost t0 = ISet::<Square>::empty();
    try_offset(pos, from, ks, false, true, 1, 0, moves, Ghost(prior), Ghost(t0));
    let ghost t1 = offset_tried(t0, from, 1, 0);
    try_offset(pos, from, ks, false, true, 1, 1, moves, Ghost(prior), Ghost(t1));
    let ghost t2 = offset_tried(t1, from, 1, 1);
    try_offset(pos, from, ks, false, true, 0, 1, moves, Ghost(prior), Ghost(t2));
    let ghost t3 = offset_tried(t2, from, 0, 1);
    try_offset(pos, from, ks, false, true, -1, 1, moves, Ghost(prior), Ghost(t3));
    let ghost t4 = offset_tried(t3, from, -1, 1);
    try_offset(pos, from, ks, false, true, -1, 0, moves, Ghost(prior), Ghost(t4));
    let ghost t5 = offset_tried(t4, from, -1, 0);
    try_offset(pos, from, ks, false, true, -1, -1, moves, Ghost(prior), Ghost(t5));
    let ghost t6 = offset_tried(t5, from, -1, -1);
    try_offset(pos, from, ks, false, true, 0, -1, moves, Ghost(prior), Ghost(t6));
    let ghost t7 = offset_tried(t6, from, 0, -1);
    try_offset(pos, from, ks, false, true, 1, -1, moves, Ghost(prior), Ghost(t7));
    let ghost t8 = offset_tried(t7, from, 1, -1);
    // Castling: the king moves two files along its rank.
    try_offset(pos, from, ks, false, false, 2, 0, moves, Ghost(prior), Ghost(t8));
    let ghost t9 = offset_tried(t8, from, 2, 0);
    try_offset(pos, from, ks, false, false, -2, 0, moves, Ghost(prior), Ghost(t9));
    let ghost t10 = offset_tried(t9, from, -2, 0);
    proof {
        assert forall|m: Move| m.from == from && is_legal(pos@, m) implies t10.contains(m.to) by {
            lemma_legal_promotion(pos@, m);
            assert(m.to == sq(m.to.file as int, m.to.rank as int));
        }
        lemma_gen_done(pos@, from, prior, moves@, t10);
    }
}

fn gen_pawn(pos: &Position, from: Square, ks: Option<(i32, i32, bool)>, moves: &mut Vec<Move>, Ghost(prior): Ghost<Seq<Move>>)
    requires
        king_hint(pos@, ks),
        valid_square(from),
        piece_at(pos@.board, from) matches Some(p) && p.kind == PieceKind::Pawn && p.color == pos@.turn,
        gen_ctx(from, prior),
        old(moves)@ == prior,
    ensures
        gen_done(pos@, from, prior, final(moves)@),
{
    proof {
        lemma_gen_start(pos@, from, prior);
    }
    let fw = forward_exec(pos.turn);
    let ghost t0 = ISet::<Square>::empty();
    try_offset(pos, from, ks, true, false, 0, fw, moves, Ghost(prior), Ghost(t0));
    let ghost t1 = offset_tried(t0, from, 0, fw as int);
    try_offset(pos, from, ks, true, false, 0, 2 * fw, moves, Ghost(prior), Ghost(t1));
    let ghost t2 = offset_tried(t1, from, 0, 2 * fw);
    try_offset(pos, from, ks, true, false, -1, fw, moves, Ghost(prior), Ghost(t2));
    let ghost t3 = offset_tried(t2, from, -1, fw as int);
    try_offset(pos, from, ks, true, false, 1, fw, moves, Ghost(prior), Ghost(t3));
    let ghost t4 = offset_tried(t3, from, 1, fw as int);
    proof {
        assert forall|m: Move| m.from == from && is_legal(pos@, m) implies t4.contains(m.to) by {
            lemma_legal_promotion(pos@, m);
            assert(m.to == sq(m.to.file as int, m.to.rank as int));
        }
        lemma_gen_done(pos@, from, prior, moves@, t4);
    }
}

/// Bishops, rooks and queens: walk the lines the piece moves along.
fn gen_slider(pos: &Position, from: Square, ks: Option<(i32, i32, bool)>, orth: bool, diag: bool, moves: &mut Vec<Move>, Ghost(prior): Ghost<Seq<Move>>)
    requires
        king_hint(pos@, ks),
        valid_square(from),
        piece_at(pos@.board, from) matches Some(p) && p.color == pos@.turn && (
            (p.kind == PieceKind::Bishop && diag && !orth) || (p.kind == PieceKind::Rook && orth && !diag) || (
            p.kind == PieceKind::Queen && orth && diag)),
        gen_ctx(from, prior),
        old(moves)@ == prior,
    ensures
        gen_done(pos@, from, prior, final(moves)@),
{
    proof {
        lemma_gen_start(pos@, from, prior);
    }
    let ghost b = pos@.board;
    let ghost t0 = ISet::<Square>::empty();
    let ghost mut t = t0;
    if orth {
        walk_ray(pos, from, ks, 1, 0, moves, Ghost(prior), Ghost(t));
        proof { t = ray_tried(t, b, from, 1, 0); }
        walk_ray(pos, from, ks, -1, 0, moves, Ghost(prior), Ghost(t));
        proof { t = ray_tried(t, b, from, -1, 0); }
        walk_ray(pos, from, ks, 0, 1, moves, Ghost(prior), Ghost(t));
        proof { t = ray_tried(t, b, from, 0, 1); }
        walk_ray(pos, from, ks, 0, -1, moves, Ghost(prior), Ghost(t));
        proof { t = ray_tried(t, b, from, 0, -1); }
    }
    let ghost t_orth = t;
    assert(forall|x: Square| #[trigger] t_orth.contains(x) ==> is_orthogonal(x.file - from.file, x.rank - from.rank));
    if diag {
        walk_ray(pos, from, ks, 1, 1, moves, Ghost(prior), Ghost(t));
        proof { t = ray_tried(t, b, from, 1, 1); }
        walk_ray(pos, from, ks, 1, -1, moves, Ghost(prior), Ghost(t));
        proof { t = ray_tried(t, b, from, 1, -1); }
        walk_ray(pos, from, ks, -1, 1, moves, Ghost(prior), Ghost(t));
        proof { t = ray_tried(t, b, from, -1, 1); }
        walk_ray(pos, from, ks, -1, -1, moves, Ghost(prior), Ghost(t));
        proof { t = ray_tried(t, b, from, -1, -1); }
    }
    proof {
        assert forall|m: Move| m.from == from && is_legal(pos@, m) implies t.contains(m.to) by {
            lemma_legal_promotion(pos@, m);
            let df = m.to.file - from.file;
            let dr = m.to.rank - from.rank;
            assert(in_dir(df, dr, sign(df), sign(dr)));
            assert(ray_sq(b, from, sign(df), sign(dr), m.to));
        }
        lemma_gen_done(pos@, from, prior, moves@, t);
    }
}

/// Legal moves, each exactly once: all of them, or with `first_only`, those of the first
/// piece that has any (so the result is empty exactly when there is no legal move).
fn gen_legal_moves(pos: &Position, first_only: bool) -> (moves: Vec<Move>)
    ensures
        forall|m: Move| #[trigger] moves@.contains(m) ==> is_legal(pos@, m),
        !first_only || moves@.len() == 0 ==> forall|m: Move| #[trigger] moves@.contains(m) <== is_legal(pos@, m),
        moves@.no_duplicates(),
{
    let mut moves: Vec<Move> = Vec::with_capacity(64);
    let ks = match find_king(&pos.board, pos.turn) {
        Some((f, r)) => {
            proof {
                lemma_king_only_in_check(pos@.board, pos.turn, f as int, r as int);
            }
            Some((f, r, is_attacked_exec(&pos.board, f, r, opponent_exec(pos.turn))))
        },
        None => None,
    };
    let mut i: u8 = 0;
    while i < 64
        invariant
            0 <= i <= 64,
            king_hint(pos@, ks),
            forall|m: Move| #[trigger] moves@.contains(m) <==> is_legal(pos@, m) && sq_index(m.from) < i,
            forall|k: int| 0 <= k < moves@.len() ==> sq_index(#[trigger] moves@[k].from) < i,
            moves@.no_duplicates(),
        decreases 64 - i,
    {
        let from = Square { file: i % 8, rank: i / 8 };
        proof {
            lemma_square_index(i as int);
        }
        assert(from == square_of_index(i as int));
        let ghost prior = moves@;
        proof {
            assert forall|k: int| 0 <= k < prior.len() implies (#[trigger] prior[k]).from != from by {
                assert(sq_index(prior[k].from) < i);
            }
        }
        match get_sq(&pos.board, from) {
            Some(p) => {
                if color_eq(p.color, pos.turn) {
                    match p.kind {
                        PieceKind::Pawn => gen_pawn(pos, from, ks, &mut moves, Ghost(prior)),
                        PieceKind::Knight => gen_knight(pos, from, ks, &mut moves, Ghost(prior)),
                        PieceKind::Bishop => gen_slider(pos, from, ks, false, true, &mut moves, Ghost(prior)),
                        PieceKind::Rook => gen_slider(pos, from, ks, true, false, &mut moves, Ghost(prior)),
                        PieceKind::Queen => gen_slider(pos, from, ks, true, true, &mut moves, Ghost(prior)),
                        PieceKind::King => gen_king(pos, from, ks, &mut moves, Ghost(prior)),
                    }
                }
            },
            None => {},
        }
        if first_only && moves.len() > 0 {
            proof {
                assert forall|m: Move| #[trigger] moves@.contains(m) implies is_legal(pos@, m) by {}
            }
            return moves;
        }
        proof {
            assert forall|m: Move| #[trigger] moves@.contains(m) <==> is_legal(pos@, m) && sq_index(m.from) < i + 1 by {
                if is_legal(pos@, m) {
                    lemma_index_square(m.from);
                    if sq_index(m.from) == i {
                        assert(m.from == from);
                    }
                }
                if m.from == from {
                    assert(sq_index(m.from) == i);
                }
            }
            assert forall|k: int| 0 <= k < moves@.len() implies sq_index(#[trigger] moves@[k].from) < i + 1 by {
                if k < prior.len() {
                    assert(moves@[k] == prior[k]);
                }
            }
        }
        i += 1;
    }
    proof {
        assert forall|m: Move| #[trigger] moves@.contains(m) <==> is_legal(pos@, m) by {
            if is_legal(pos@, m) {
                lemma_index_square(m.from);
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
    gen_legal_moves(pos, false)
}

pub fn has_legal_move_exec(pos: &Position) -> (res: bool)
    ensures
        res == has_legal_move(pos@),
{
    let moves = gen_legal_moves(pos, true);
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

} // verus!
