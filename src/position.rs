//! Executable position representation (a simple 64-square mailbox) and its
//! abstraction to `spec::PositionModel`.
use crate::spec::*;
use crate::types::*;
use vstd::prelude::*;

verus! {

#[derive(Clone, Copy, Debug)]
pub struct Position {
    /// Indexed by `rank * 8 + file`.
    pub board: [Option<Piece>; 64],
    pub turn: Color,
    pub castling: CastlingRights,
    pub ep: Option<Square>,
    pub halfmove_clock: u32,
    pub fullmove_number: u32,
}

impl View for Position {
    type V = PositionModel;

    open spec fn view(&self) -> PositionModel {
        PositionModel {
            board: self.board@,
            turn: self.turn,
            castling: self.castling,
            ep: self.ep,
            halfmove_clock: self.halfmove_clock as nat,
            fullmove_number: self.fullmove_number as nat,
        }
    }
}

/// Spec-level index of a square.
pub open spec fn sq_index(s: Square) -> int {
    index_of(s.file as int, s.rank as int)
}

pub open spec fn square_of_index(i: int) -> Square {
    Square { file: (i % 8) as u8, rank: (i / 8) as u8 }
}

pub proof fn lemma_square_index(i: int)
    requires
        0 <= i < 64,
    ensures
        valid_square(square_of_index(i)),
        sq_index(square_of_index(i)) == i,
        on_board(i % 8, i / 8),
        index_of(i % 8, i / 8) == i,
{
}

pub proof fn lemma_index_square(s: Square)
    requires
        valid_square(s),
    ensures
        0 <= sq_index(s) < 64,
        square_of_index(sq_index(s)) == s,
{
    assert(sq_index(s) % 8 == s.file as int);
    assert(sq_index(s) / 8 == s.rank as int);
}

pub proof fn lemma_index_injective(f1: int, r1: int, f2: int, r2: int)
    requires
        on_board(f1, r1),
        on_board(f2, r2),
    ensures
        0 <= index_of(f1, r1) < 64,
        index_of(f1, r1) == index_of(f2, r2) <==> (f1 == f2 && r1 == r2),
{
}

/// Read the piece on (f, r).
pub fn get(b: &[Option<Piece>; 64], f: i32, r: i32) -> (p: Option<Piece>)
    requires
        on_board(f as int, r as int),
    ensures
        p == at(b@, f as int, r as int),
{
    b[(r * 8 + f) as usize]
}

pub fn get_sq(b: &[Option<Piece>; 64], s: Square) -> (p: Option<Piece>)
    requires
        valid_square(s),
    ensures
        p == piece_at(b@, s),
{
    get(b, s.file as i32, s.rank as i32)
}

pub fn opponent_exec(c: Color) -> (r: Color)
    ensures
        r == opponent(c),
{
    match c {
        Color::White => Color::Black,
        Color::Black => Color::White,
    }
}

pub fn forward_exec(c: Color) -> (r: i32)
    ensures
        r as int == forward(c),
{
    match c {
        Color::White => 1,
        Color::Black => -1,
    }
}

pub fn back_rank_exec(c: Color) -> (r: i32)
    ensures
        r as int == back_rank(c),
{
    match c {
        Color::White => 0,
        Color::Black => 7,
    }
}

pub fn pawn_start_rank_exec(c: Color) -> (r: i32)
    ensures
        r as int == pawn_start_rank(c),
{
    match c {
        Color::White => 1,
        Color::Black => 6,
    }
}

pub fn promotion_rank_exec(c: Color) -> (r: i32)
    ensures
        r as int == promotion_rank(c),
{
    match c {
        Color::White => 7,
        Color::Black => 0,
    }
}

pub fn abs_exec(x: i32) -> (r: i32)
    requires
        -100 <= x <= 100,
    ensures
        r as int == abs(x as int),
{
    if x < 0 {
        -x
    } else {
        x
    }
}

fn back_rank_kind_exec(f: usize) -> (k: PieceKind)
    ensures
        k == back_rank_kind(f as int),
{
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

impl Position {
    /// The standard starting position.
    pub fn initial() -> (pos: Position)
        ensures
            pos@ == initial_position(),
    {
        let mut board: [Option<Piece>; 64] = [None; 64];
        let mut i: usize = 0;
        while i < 64
            invariant
                0 <= i <= 64,
                forall|j: int| 0 <= j < i ==> board@[j] == initial_piece(j % 8, j / 8),
            decreases 64 - i,
        {
            let f = i % 8;
            let r = i / 8;
            let p = if r == 0 {
                Some(Piece { color: Color::White, kind: back_rank_kind_exec(f) })
            } else if r == 1 {
                Some(Piece { color: Color::White, kind: PieceKind::Pawn })
            } else if r == 6 {
                Some(Piece { color: Color::Black, kind: PieceKind::Pawn })
            } else if r == 7 {
                Some(Piece { color: Color::Black, kind: back_rank_kind_exec(f) })
            } else {
                None
            };
            board[i] = p;
            i += 1;
        }
        let pos = Position {
            board,
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
        };
        assert(pos@.board =~= initial_position().board);
        pos
    }
}

} // verus!
