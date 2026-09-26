//! Move legality, making moves, and legal move generation — all proven to match `spec`.
//!
//! This is the straightforward "reference" implementation: legal move generation
//! tries every (from, to, promotion) candidate and keeps the legal ones.
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

/// Append `m` to `moves` if it is legal.
fn try_push(pos: &Position, m: Move, moves: &mut Vec<Move>)
    ensures
        is_legal(pos@, m) ==> final(moves)@ == old(moves)@.push(m),
        !is_legal(pos@, m) ==> final(moves)@ == old(moves)@,
        forall|x: Move|
            #[trigger] final(moves)@.contains(x) <==> old(moves)@.contains(x) || (x == m
                && is_legal(pos@, m)),
{
    if is_legal_exec(pos, m) {
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

/// All legal moves, each exactly once.
pub fn legal_moves_exec(pos: &Position) -> (moves: Vec<Move>)
    ensures
        forall|m: Move| #[trigger] moves@.contains(m) <==> is_legal(pos@, m),
        moves@.no_duplicates(),
{
    let mut moves: Vec<Move> = Vec::new();
    let mut i: u8 = 0;
    while i < 64
        invariant
            0 <= i <= 64,
            forall|m: Move| #[trigger] moves@.contains(m) <==> is_legal(pos@, m) && visited(m, i as int, 0),
            forall|k: int| 0 <= k < moves@.len() ==> visited(#[trigger] moves@[k], i as int, 0),
            moves@.no_duplicates(),
        decreases 64 - i,
    {
        let from = Square { file: i % 8, rank: i / 8 };
        proof {
            lemma_square_index(i as int);
        }
        assert(from == square_of_index(i as int));
        let own_piece = match get_sq(&pos.board, from) {
            Some(p) => color_eq(p.color, pos.turn),
            None => false,
        };
        let mut j: u8 = 0;
        // Squares without a piece of the side to move have no legal moves.
        if !own_piece {
            j = 64;
        }
        while j < 64
            invariant
                0 <= i < 64,
                0 <= j <= 64,
                from == square_of_index(i as int),
                sq_index(from) == i,
                valid_square(from),
                !own_piece ==> j == 64,
                own_piece == (moving_piece(pos@, Move { from, to: from, promotion: None }) matches Some(p) && p.color == pos.turn),
                forall|m: Move| #[trigger] moves@.contains(m) <==> is_legal(pos@, m) && visited(m, i as int, j as int),
                forall|k: int| 0 <= k < moves@.len() ==> visited(#[trigger] moves@[k], i as int, j as int),
                moves@.no_duplicates(),
            decreases 64 - j,
        {
            let to = Square { file: j % 8, rank: j / 8 };
            proof {
                lemma_square_index(j as int);
            }
            let ghost old_moves = moves@;
            try_push(pos, Move { from, to, promotion: None }, &mut moves);
            try_push(pos, Move { from, to, promotion: Some(PieceKind::Knight) }, &mut moves);
            try_push(pos, Move { from, to, promotion: Some(PieceKind::Bishop) }, &mut moves);
            try_push(pos, Move { from, to, promotion: Some(PieceKind::Rook) }, &mut moves);
            try_push(pos, Move { from, to, promotion: Some(PieceKind::Queen) }, &mut moves);
            proof {
                assert forall|m: Move| #[trigger] moves@.contains(m) <==> is_legal(pos@, m) && visited(m, i as int, j + 1) by {
                    if is_legal(pos@, m) {
                        lemma_legal_promotion(pos@, m);
                        lemma_index_square(m.from);
                        lemma_index_square(m.to);
                        if sq_index(m.from) == i && sq_index(m.to) == j {
                            assert(m.from == from);
                            assert(m.to == to);
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
                        assert(visited(old_moves[a], i as int, j as int));
                        assert(moves@[c].to == to);
                    }
                }
            }
            j += 1;
        }
        proof {
            assert forall|m: Move| #[trigger] moves@.contains(m) <==> is_legal(pos@, m) && visited(m, i + 1, 0) by {
                if is_legal(pos@, m) {
                    lemma_index_square(m.from);
                    lemma_index_square(m.to);
                    if sq_index(m.from) == i {
                        assert(m.from == from);
                    }
                }
            }
            assert forall|k: int| 0 <= k < moves@.len() implies visited(#[trigger] moves@[k], i + 1, 0) by {
                assert(visited(moves@[k], i as int, j as int));
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

pub fn has_legal_move_exec(pos: &Position) -> (res: bool)
    ensures
        res == has_legal_move(pos@),
{
    let moves = legal_moves_exec(pos);
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
