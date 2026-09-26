//! Basic data types shared by the specification and the executable code.
use vstd::prelude::*;

verus! {

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum Color {
    White,
    Black,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum PieceKind {
    Pawn,
    Knight,
    Bishop,
    Rook,
    Queen,
    King,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct Piece {
    pub color: Color,
    pub kind: PieceKind,
}

/// A square given by file (0 = a .. 7 = h) and rank (0 = rank 1 .. 7 = rank 8).
/// Only squares with `file < 8 && rank < 8` are on the board (see `spec::valid_square`).
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct Square {
    pub file: u8,
    pub rank: u8,
}

/// A move in "pure coordinate" form, exactly like UCI notation:
/// castling is encoded as the king moving two files (e1g1, e1c1, ...),
/// en passant as the pawn moving to the en-passant target square,
/// and `promotion` names the piece a pawn promotes to.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct Move {
    pub from: Square,
    pub to: Square,
    pub promotion: Option<PieceKind>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct CastlingRights {
    pub white_kingside: bool,
    pub white_queenside: bool,
    pub black_kingside: bool,
    pub black_queenside: bool,
}

// ---------------------------------------------------------------------------
// Executable equality helpers.
// (Derived `PartialEq` has no spec meaning in Verus, so verified code uses these.)
// ---------------------------------------------------------------------------

pub fn color_eq(a: Color, b: Color) -> (r: bool)
    ensures
        r == (a == b),
{
    match (a, b) {
        (Color::White, Color::White) | (Color::Black, Color::Black) => true,
        _ => false,
    }
}

pub fn kind_eq(a: PieceKind, b: PieceKind) -> (r: bool)
    ensures
        r == (a == b),
{
    match (a, b) {
        (PieceKind::Pawn, PieceKind::Pawn)
        | (PieceKind::Knight, PieceKind::Knight)
        | (PieceKind::Bishop, PieceKind::Bishop)
        | (PieceKind::Rook, PieceKind::Rook)
        | (PieceKind::Queen, PieceKind::Queen)
        | (PieceKind::King, PieceKind::King) => true,
        _ => false,
    }
}

pub fn piece_eq(a: Piece, b: Piece) -> (r: bool)
    ensures
        r == (a == b),
{
    color_eq(a.color, b.color) && kind_eq(a.kind, b.kind)
}

pub fn opt_piece_eq(a: Option<Piece>, b: Option<Piece>) -> (r: bool)
    ensures
        r == (a == b),
{
    match (a, b) {
        (None, None) => true,
        (Some(x), Some(y)) => piece_eq(x, y),
        _ => false,
    }
}

pub fn opt_kind_eq(a: Option<PieceKind>, b: Option<PieceKind>) -> (r: bool)
    ensures
        r == (a == b),
{
    match (a, b) {
        (None, None) => true,
        (Some(x), Some(y)) => kind_eq(x, y),
        _ => false,
    }
}

pub fn square_eq(a: Square, b: Square) -> (r: bool)
    ensures
        r == (a == b),
{
    a.file == b.file && a.rank == b.rank
}

pub fn opt_square_eq(a: Option<Square>, b: Option<Square>) -> (r: bool)
    ensures
        r == (a == b),
{
    match (a, b) {
        (None, None) => true,
        (Some(x), Some(y)) => square_eq(x, y),
        _ => false,
    }
}

pub fn move_eq(a: Move, b: Move) -> (r: bool)
    ensures
        r == (a == b),
{
    square_eq(a.from, b.from) && square_eq(a.to, b.to) && opt_kind_eq(a.promotion, b.promotion)
}

pub fn castling_eq(a: CastlingRights, b: CastlingRights) -> (r: bool)
    ensures
        r == (a == b),
{
    a.white_kingside == b.white_kingside && a.white_queenside == b.white_queenside
        && a.black_kingside == b.black_kingside && a.black_queenside == b.black_queenside
}

} // verus!

verus! {

/// Ways a game can end automatically (without a player's claim or resignation).
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum GameOutcome {
    Checkmate { winner: Color },
    Stalemate,
    InsufficientMaterial,
    SeventyFiveMoveRule,
    FivefoldRepetition,
}

} // verus!
