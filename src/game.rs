//! Game-level rules: game history, repetition, draws and the game outcome,
//! proven to match `spec::game_outcome` and `spec::can_claim_draw`.
use crate::movegen::*;
use crate::position::*;
use crate::spec::*;
use crate::types::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Insufficient material
// ---------------------------------------------------------------------------

/// (f2, r2) comes before (f, r) in the scan order (rank by rank, file by file).
pub open spec fn before(f2: int, r2: int, f: int, r: int) -> bool {
    r2 < r || (r2 == r && f2 < f)
}

/// What the scan of `insufficient_material_exec` has seen of the squares before (f, r):
/// only kings and minor pieces, `minors` minor pieces (counting stops at 2, with the
/// first two at `w1`, `w2`), whether one is a knight (at `wk`), and whether bishops stand
/// on dark (shade 0, at `wd`) or light (shade 1, at `wl`) squares.
pub open spec fn scan_inv(
    b: Board,
    f: int,
    r: int,
    minors: int,
    w1: (int, int),
    w2: (int, int),
    knight: bool,
    wk: (int, int),
    dark: bool,
    wd: (int, int),
    light: bool,
    wl: (int, int),
) -> bool {
    &&& forall|f2: int, r2: int|
        on_board(f2, r2) && before(f2, r2, f, r) ==> #[trigger] king_or_minor_or_empty(b, f2, r2)
    &&& 0 <= minors <= 2
    &&& minors == 0 ==> forall|f2: int, r2: int|
        on_board(f2, r2) && before(f2, r2, f, r) ==> !#[trigger] minor_at(b, f2, r2)
    &&& minors >= 1 ==> on_board(w1.0, w1.1) && before(w1.0, w1.1, f, r) && minor_at(b, w1.0, w1.1)
    &&& minors == 1 ==> forall|f2: int, r2: int|
        on_board(f2, r2) && before(f2, r2, f, r) && #[trigger] minor_at(b, f2, r2) ==> f2 == w1.0
            && r2 == w1.1
    &&& minors == 2 ==> on_board(w2.0, w2.1) && minor_at(b, w2.0, w2.1) && w2 != w1
    &&& knight ==> on_board(wk.0, wk.1) && minor_at(b, wk.0, wk.1) && !bishop_at(b, wk.0, wk.1)
    &&& !knight ==> forall|f2: int, r2: int|
        on_board(f2, r2) && before(f2, r2, f, r) && #[trigger] minor_at(b, f2, r2) ==> bishop_at(
            b,
            f2,
            r2,
        )
    &&& dark ==> on_board(wd.0, wd.1) && bishop_at(b, wd.0, wd.1) && minor_at(b, wd.0, wd.1)
        && square_shade(wd.0, wd.1) == 0
    &&& !dark ==> forall|f2: int, r2: int|
        on_board(f2, r2) && before(f2, r2, f, r) && #[trigger] bishop_at(b, f2, r2) ==> square_shade(
            f2,
            r2,
        ) != 0
    &&& light ==> on_board(wl.0, wl.1) && bishop_at(b, wl.0, wl.1) && minor_at(b, wl.0, wl.1)
        && square_shade(wl.0, wl.1) == 1
    &&& !light ==> forall|f2: int, r2: int|
        on_board(f2, r2) && before(f2, r2, f, r) && #[trigger] bishop_at(b, f2, r2) ==> square_shade(
            f2,
            r2,
        ) != 1
}

/// One pass over the board: counts minor pieces and records knights and bishop shades.
pub fn insufficient_material_exec(b: &[Option<Piece>; 64]) -> (res: bool)
    ensures
        res == insufficient_material(b@),
{
    let mut minors: u8 = 0;
    let mut knight = false;
    let mut dark = false;
    let mut light = false;
    let ghost mut w1: (int, int) = (0, 0);
    let ghost mut w2: (int, int) = (0, 0);
    let ghost mut wk: (int, int) = (0, 0);
    let ghost mut wd: (int, int) = (0, 0);
    let ghost mut wl: (int, int) = (0, 0);
    let mut r: i32 = 0;
    while r < 8
        invariant
            0 <= r <= 8,
            scan_inv(b@, 0, r as int, minors as int, w1, w2, knight, wk, dark, wd, light, wl),
        decreases 8 - r,
    {
        let mut f: i32 = 0;
        while f < 8
            invariant
                0 <= f <= 8,
                0 <= r < 8,
                scan_inv(b@, f as int, r as int, minors as int, w1, w2, knight, wk, dark, wd, light, wl),
            decreases 8 - f,
        {
            let ghost (m0, k0, d0, l0) = (minors, knight, dark, light);
            let ghost (w10, w20, wk0, wd0, wl0) = (w1, w2, wk, wd, wl);
            match get(b, f, r) {
                None => {},
                Some(p) => {
                    let is_knight = kind_eq(p.kind, PieceKind::Knight);
                    let is_bishop = kind_eq(p.kind, PieceKind::Bishop);
                    if !is_knight && !is_bishop {
                        if !kind_eq(p.kind, PieceKind::King) {
                            assert(!king_or_minor_or_empty(b@, f as int, r as int));
                            return false;
                        }
                    } else {
                        if minors == 0 {
                            proof {
                                w1 = (f as int, r as int);
                            }
                            minors = 1;
                        } else if minors == 1 {
                            proof {
                                w2 = (f as int, r as int);
                            }
                            minors = 2;
                        }
                        if is_knight {
                            proof {
                                wk = (f as int, r as int);
                            }
                            knight = true;
                        } else if (f + r) % 2 == 0 {
                            proof {
                                wd = (f as int, r as int);
                            }
                            dark = true;
                        } else {
                            proof {
                                wl = (f as int, r as int);
                            }
                            light = true;
                        }
                    }
                },
            }
            proof {
                assert(scan_inv(b@, f + 1, r as int, minors as int, w1, w2, knight, wk, dark, wd, light, wl)) by {
                    assert forall|f2: int, r2: int| on_board(f2, r2) && #[trigger] before(f2, r2, f + 1, r as int)
                        && !before(f2, r2, f as int, r as int) implies f2 == f && r2 == r by {}
                }
            }
            f += 1;
        }
        proof {
            assert forall|f2: int, r2: int| on_board(f2, r2) implies #[trigger] before(f2, r2, 8, r as int) == before(f2, r2, 0, r + 1) by {}
        }
        r += 1;
    }
    let res = minors <= 1 || (!knight && !(dark && light));
    proof {
        assert forall|f2: int, r2: int| on_board(f2, r2) implies #[trigger] before(f2, r2, 0, 8) by {}
        let b = b@;
        let one = forall|f1: int, r1: int, f2: int, r2: int|
            on_board(f1, r1) && on_board(f2, r2) && #[trigger] minor_at(b, f1, r1)
                && #[trigger] minor_at(b, f2, r2) ==> f1 == f2 && r1 == r2;
        let shade = forall|f1: int, r1: int, f2: int, r2: int|
            on_board(f1, r1) && on_board(f2, r2) && #[trigger] minor_at(b, f1, r1)
                && #[trigger] minor_at(b, f2, r2) ==> bishop_at(b, f1, r1) && bishop_at(b, f2, r2)
                && square_shade(f1, r1) == square_shade(f2, r2);
        assert(one == (minors <= 1)) by {
            if minors == 2 {
                assert(minor_at(b, w1.0, w1.1) && minor_at(b, w2.0, w2.1));
            }
        }
        assert(shade == (!knight && !(dark && light))) by {
            if knight {
                assert(minor_at(b, wk.0, wk.1));
            } else if dark && light {
                assert(minor_at(b, wd.0, wd.1) && minor_at(b, wl.0, wl.1));
            } else {
                assert forall|f1: int, r1: int, f2: int, r2: int|
                    on_board(f1, r1) && on_board(f2, r2) && #[trigger] minor_at(b, f1, r1)
                        && #[trigger] minor_at(b, f2, r2) implies bishop_at(b, f1, r1) && bishop_at(b, f2, r2)
                        && square_shade(f1, r1) == square_shade(f2, r2) by {
                    assert(bishop_at(b, f1, r1) && bishop_at(b, f2, r2));
                    assert(0 <= square_shade(f1, r1) <= 1 && 0 <= square_shade(f2, r2) <= 1);
                }
            }
        }
    }
    res
}

// ---------------------------------------------------------------------------
// Repetition
// ---------------------------------------------------------------------------

/// Whether some move of the pawn on `from` to `to` is a legal en-passant capture.
fn en_passant_from(pos: &Position, from: Square, to: Square) -> (res: bool)
    requires
        valid_square(from),
        valid_square(to),
    ensures
        res == exists|m: Move| #![trigger is_legal(pos@, m)]
            m.from == from && m.to == to && is_legal(pos@, m) && is_en_passant(pos@, m),
{
    let promotes = to.rank as i32 == promotion_rank_exec(pos.turn);
    let n = Move { from, to, promotion: Some(PieceKind::Knight) };
    let b = Move { from, to, promotion: Some(PieceKind::Bishop) };
    let r = Move { from, to, promotion: Some(PieceKind::Rook) };
    let q = Move { from, to, promotion: Some(PieceKind::Queen) };
    let none = Move { from, to, promotion: None };
    let res = if promotes {
        (is_legal_exec(pos, n) && is_en_passant_exec(pos, n)) || (is_legal_exec(pos, b) && is_en_passant_exec(pos, b))
            || (is_legal_exec(pos, r) && is_en_passant_exec(pos, r)) || (is_legal_exec(pos, q) && is_en_passant_exec(pos, q))
    } else {
        is_legal_exec(pos, none) && is_en_passant_exec(pos, none)
    };
    proof {
        assert forall|m: Move| m.from == from && m.to == to && #[trigger] is_legal(pos@, m) && is_en_passant(pos@, m)
            implies res by {
            lemma_legal_promotion(pos@, m);
            if promotes {
                assert(m == n || m == b || m == r || m == q);
            } else {
                assert(m == none);
            }
        }
    }
    res
}

/// Only the (at most two) pawns diagonally behind the en-passant square can capture onto it.
pub fn en_passant_available_exec(pos: &Position) -> (res: bool)
    ensures
        res == en_passant_available(pos@),
{
    let s = match pos.ep {
        None => {
            return false;
        },
        Some(s) => s,
    };
    let r1 = s.rank as i32 - forward_exec(pos.turn);
    if !(s.file < 8 && s.rank < 8 && 0 <= r1 && r1 < 8) {
        proof {
            assert forall|m: Move| !(is_legal(pos@, m) && #[trigger] is_en_passant(pos@, m)) by {
                if is_legal(pos@, m) && is_en_passant(pos@, m) {
                    assert(m.to == s);
                }
            }
        }
        return false;
    }
    let f = s.file as i32;
    let left = f >= 1 && en_passant_from(pos, Square { file: (f - 1) as u8, rank: r1 as u8 }, s);
    let right = f <= 6 && en_passant_from(pos, Square { file: (f + 1) as u8, rank: r1 as u8 }, s);
    proof {
        assert forall|m: Move| is_legal(pos@, m) && #[trigger] is_en_passant(pos@, m) implies left || right by {
            assert(m.to == s);
            if m.from.file as int == f - 1 {
                assert(m.from == Square { file: (f - 1) as u8, rank: r1 as u8 });
            } else {
                assert(m.from == Square { file: (f + 1) as u8, rank: r1 as u8 });
            }
        }
    }
    left || right
}

fn board_eq(a: &[Option<Piece>; 64], b: &[Option<Piece>; 64]) -> (res: bool)
    ensures
        res == (a@ == b@),
{
    // Eight squares at a time.
    let mut i: usize = 0;
    while i < 64
        invariant
            0 <= i <= 64,
            i % 8 == 0,
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases 64 - i,
    {
        let eq = opt_piece_eq(a[i], b[i]) && opt_piece_eq(a[i + 1], b[i + 1]) && opt_piece_eq(
            a[i + 2],
            b[i + 2],
        ) && opt_piece_eq(a[i + 3], b[i + 3]) && opt_piece_eq(a[i + 4], b[i + 4]) && opt_piece_eq(
            a[i + 5],
            b[i + 5],
        ) && opt_piece_eq(a[i + 6], b[i + 6]) && opt_piece_eq(a[i + 7], b[i + 7]);
        if !eq {
            return false;
        }
        i += 8;
    }
    assert(a@ =~= b@);
    true
}

/// The bitboard of the occupied squares of `b`, if it has at most 16 pieces (else 0).
///
/// On a sparse board, a difference from an earlier position almost always shows on an
/// occupied square, while a square-by-square comparison runs through the empty ones.
fn sparse_occupancy(b: &[Option<Piece>; 64]) -> (occ: u64) {
    let mut occ: u64 = 0;
    let mut n: u32 = 0;
    let mut i: u64 = 0;
    while i < 64
        invariant
            n <= i <= 64,
        decreases 64 - i,
    {
        if b[i as usize].is_some() {
            occ = occ | (1u64 << i);
            n += 1;
        }
        i += 1;
    }
    if n <= 16 { occ } else { 0 }
}

/// A quick test that finds most differences between sparse boards: whether they differ on
/// one of the squares of `occ` (in practice, the squares occupied on one of them).
fn differ_on(a: &[Option<Piece>; 64], b: &[Option<Piece>; 64], occ: u64) -> (res: bool)
    ensures
        res ==> a@ != b@,
{
    let mut rem = occ;
    while rem != 0
        decreases rem,
    {
        proof {
            vstd::std_specs::bits::axiom_u64_trailing_zeros(rem);
        }
        let j = rem.trailing_zeros() as usize;
        if !opt_piece_eq(a[j], b[j]) {
            return true;
        }
        assert(rem != 0 ==> rem & sub(rem, 1) < rem) by (bit_vector);
        rem = rem & (rem - 1);
    }
    false
}

/// The key for the repetition rule; `ep` is the *effective* en-passant square.
/// `occ` only speeds up the board comparison.
fn key_matches(p: &Position, board: &[Option<Piece>; 64], occ: u64, turn: Color, castling: CastlingRights, ep: Option<Square>) -> (res: bool)
    ensures
        res == (repetition_key(p@) == PositionKey { board: board@, turn, castling, ep }),
{
    if !(color_eq(p.turn, turn) && castling_eq(p.castling, castling)) || differ_on(&p.board, board, occ)
        || !board_eq(&p.board, board) {
        return false;
    }
    let p_ep = if en_passant_available_exec(p) { p.ep } else { None };
    opt_square_eq(p_ep, ep)
}

// ---------------------------------------------------------------------------
// Games
// ---------------------------------------------------------------------------

/// A game: the list of positions played so far (the last one is the current position).
pub struct Game {
    pub history: Vec<Position>,
}

impl View for Game {
    type V = GameModel;

    open spec fn view(&self) -> GameModel {
        GameModel { history: self.history@.map_values(|p: Position| p@) }
    }
}

impl Game {
    pub open spec fn inv(&self) -> bool {
        self.history@.len() > 0
    }

    pub fn new() -> (g: Game)
        ensures
            g.inv(),
            g@.history == seq![initial_position()],
    {
        Game::from_position(Position::initial())
    }

    pub fn from_position(pos: Position) -> (g: Game)
        ensures
            g.inv(),
            g@.history == seq![pos@],
    {
        let mut history = Vec::new();
        history.push(pos);
        let g = Game { history };
        assert(g@.history =~= seq![pos@]);
        g
    }

    pub fn current(&self) -> (pos: &Position)
        requires
            self.inv(),
        ensures
            pos@ == current(self@),
    {
        let n = self.history.len();
        &self.history[n - 1]
    }

    /// Plays `m` if it is legal; otherwise leaves the game unchanged and returns false.
    /// (A move is also refused if a move counter would overflow a `u32`.)
    pub fn play(&mut self, m: Move) -> (ok: bool)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            ok == (is_legal(current(old(self)@), m) && current(old(self)@).halfmove_clock < u32::MAX
                && current(old(self)@).fullmove_number < u32::MAX),
            ok ==> final(self)@.history == old(self)@.history.push(apply_move(current(old(self)@), m)),
            !ok ==> final(self)@ == old(self)@,
    {
        let pos = self.current();
        if !(pos.halfmove_clock < u32::MAX && pos.fullmove_number < u32::MAX) {
            return false;
        }
        let next = match try_apply_move_exec(pos, m) {
            Some(next) => next,
            None => {
                return false;
            },
        };
        self.history.push(next);
        assert(self@.history =~= old(self)@.history.push(apply_move(current(old(self)@), m)));
        true
    }

    /// How many times the current position has occurred (including now).
    pub fn repetition_count(&self) -> (n: usize)
        requires
            self.inv(),
        ensures
            n as nat == repetition_count(self@),
    {
        let cur = self.current();
        let ghost key = repetition_key(cur@);
        let ep = if en_passant_available_exec(cur) { cur.ep } else { None };
        assert(key == PositionKey { board: cur.board@, turn: cur.turn, castling: cur.castling, ep });
        let n = self.history.len();
        // The pre-check pays off only when there are many positions to compare with.
        let occ = if n > 16 { sparse_occupancy(&cur.board) } else { 0 };
        let mut count: usize = 0;
        let mut i: usize = 0;
        // The current position (the last one) matches itself; it is counted after the loop.
        while i < n - 1
            invariant
                n == self.history@.len(),
                n > 0,
                cur@ == self@.history[n - 1],
                0 <= i <= n - 1,
                count <= i,
                count as nat == occurrences(self@.history, key, i as int),
                key == (PositionKey { board: cur.board@, turn: cur.turn, castling: cur.castling, ep }),
            decreases self.history@.len() - i,
        {
            if key_matches(&self.history[i], &cur.board, occ, cur.turn, cur.castling, ep) {
                count += 1;
            }
            i += 1;
        }
        assert(repetition_key(self@.history[n - 1]) == key);
        count + 1
    }

    /// The automatic result of the game, if it has ended.
    pub fn outcome(&self) -> (o: Option<GameOutcome>)
        requires
            self.inv(),
        ensures
            o == game_outcome(self@),
    {
        let pos = self.current();
        let (check, any_move) = check_status_exec(pos);
        if check && !any_move {
            Some(GameOutcome::Checkmate { winner: opponent_exec(pos.turn) })
        } else if !check && !any_move {
            Some(GameOutcome::Stalemate)
        } else if insufficient_material_exec(&pos.board) {
            Some(GameOutcome::InsufficientMaterial)
        } else if pos.halfmove_clock >= 150 {
            Some(GameOutcome::SeventyFiveMoveRule)
        } else if self.repetition_count() >= 5 {
            Some(GameOutcome::FivefoldRepetition)
        } else {
            None
        }
    }

    /// Whether the player to move may claim a draw (50-move rule or threefold repetition).
    pub fn can_claim_draw(&self) -> (res: bool)
        requires
            self.inv(),
        ensures
            res == can_claim_draw(self@),
    {
        self.outcome().is_none() && (self.current().halfmove_clock >= 100 || self.repetition_count() >= 3)
    }
}

} // verus!
