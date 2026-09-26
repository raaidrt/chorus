//! Game-level rules: game history, repetition, draws and the game outcome,
//! proven to match `spec::game_outcome` and `spec::can_claim_draw`.
use crate::attacks::*;
use crate::movegen::*;
use crate::position::*;
use crate::spec::*;
use crate::types::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Insufficient material
// ---------------------------------------------------------------------------

fn is_minor_exec(k: PieceKind) -> (r: bool)
    ensures
        r == is_minor(k),
{
    kind_eq(k, PieceKind::Knight) || kind_eq(k, PieceKind::Bishop)
}

fn minor_at_exec(b: &[Option<Piece>; 64], f: i32, r: i32) -> (res: bool)
    requires
        on_board(f as int, r as int),
    ensures
        res == minor_at(b@, f as int, r as int),
{
    match get(b, f, r) {
        Some(p) => is_minor_exec(p.kind),
        None => false,
    }
}

fn bishop_at_exec(b: &[Option<Piece>; 64], f: i32, r: i32) -> (res: bool)
    requires
        on_board(f as int, r as int),
    ensures
        res == bishop_at(b@, f as int, r as int),
{
    match get(b, f, r) {
        Some(p) => kind_eq(p.kind, PieceKind::Bishop),
        None => false,
    }
}

/// The pairwise conditions of `insufficient_material`
/// (`shade == false`: "at most one minor"; `shade == true`: "same-shade bishops only").
pub open spec fn pair_ok(b: Board, shade: bool, f1: int, r1: int, f2: int, r2: int) -> bool {
    minor_at(b, f1, r1) && minor_at(b, f2, r2) ==> if shade {
        bishop_at(b, f1, r1) && bishop_at(b, f2, r2) && square_shade(f1, r1) == square_shade(f2, r2)
    } else {
        f1 == f2 && r1 == r2
    }
}

pub open spec fn pair_ok_idx(b: Board, shade: bool, i: int, j: int) -> bool {
    pair_ok(b, shade, i % 8, i / 8, j % 8, j / 8)
}

fn pair_ok_exec(b: &[Option<Piece>; 64], shade: bool, i: i32, j: i32) -> (res: bool)
    requires
        0 <= i < 64,
        0 <= j < 64,
    ensures
        res == pair_ok_idx(b@, shade, i as int, j as int),
{
    let (f1, r1, f2, r2) = (i % 8, i / 8, j % 8, j / 8);
    if !(minor_at_exec(b, f1, r1) && minor_at_exec(b, f2, r2)) {
        return true;
    }
    if shade {
        bishop_at_exec(b, f1, r1) && bishop_at_exec(b, f2, r2) && (f1 + r1) % 2 == (f2 + r2) % 2
    } else {
        f1 == f2 && r1 == r2
    }
}

fn all_pairs_ok(b: &[Option<Piece>; 64], shade: bool) -> (res: bool)
    ensures
        res == (forall|f1: int, r1: int, f2: int, r2: int|
            on_board(f1, r1) && on_board(f2, r2) ==> #[trigger] pair_ok(b@, shade, f1, r1, f2, r2)),
{
    let mut i: i32 = 0;
    while i < 64
        invariant
            0 <= i <= 64,
            forall|i2: int, j2: int| 0 <= i2 < i && 0 <= j2 < 64 ==> #[trigger] pair_ok_idx(b@, shade, i2, j2),
        decreases 64 - i,
    {
        let mut j: i32 = 0;
        while j < 64
            invariant
                0 <= i < 64,
                0 <= j <= 64,
                forall|i2: int, j2: int| 0 <= i2 < i && 0 <= j2 < 64 ==> #[trigger] pair_ok_idx(b@, shade, i2, j2),
                forall|j2: int| 0 <= j2 < j ==> #[trigger] pair_ok_idx(b@, shade, i as int, j2),
            decreases 64 - j,
        {
            if !pair_ok_exec(b, shade, i, j) {
                proof {
                    lemma_square_index(i as int);
                    lemma_square_index(j as int);
                }
                assert(!pair_ok_idx(b@, shade, i as int, j as int));
                return false;
            }
            j += 1;
        }
        i += 1;
    }
    proof {
        assert forall|f1: int, r1: int, f2: int, r2: int|
            on_board(f1, r1) && on_board(f2, r2) implies #[trigger] pair_ok(b@, shade, f1, r1, f2, r2) by {
            let i1 = index_of(f1, r1);
            let j1 = index_of(f2, r2);
            assert(i1 % 8 == f1 && i1 / 8 == r1);
            assert(j1 % 8 == f2 && j1 / 8 == r2);
            assert(pair_ok_idx(b@, shade, i1, j1));
        }
    }
    true
}

fn only_kings_and_minors(b: &[Option<Piece>; 64]) -> (res: bool)
    ensures
        res == (forall|f: int, r: int| on_board(f, r) ==> #[trigger] king_or_minor_or_empty(b@, f, r)),
{
    let mut r: i32 = 0;
    while r < 8
        invariant
            0 <= r <= 8,
            forall|f2: int, r2: int| 0 <= f2 < 8 && 0 <= r2 < r ==> #[trigger] king_or_minor_or_empty(b@, f2, r2),
        decreases 8 - r,
    {
        let mut f: i32 = 0;
        while f < 8
            invariant
                0 <= f <= 8,
                0 <= r < 8,
                forall|f2: int, r2: int| 0 <= f2 < 8 && 0 <= r2 < r ==> #[trigger] king_or_minor_or_empty(b@, f2, r2),
                forall|f2: int| 0 <= f2 < f ==> #[trigger] king_or_minor_or_empty(b@, f2, r as int),
            decreases 8 - f,
        {
            let ok = match get(&b, f, r) {
                Some(p) => kind_eq(p.kind, PieceKind::King) || is_minor_exec(p.kind),
                None => true,
            };
            if !ok {
                assert(!king_or_minor_or_empty(b@, f as int, r as int));
                return false;
            }
            f += 1;
        }
        r += 1;
    }
    true
}

pub fn insufficient_material_exec(b: &[Option<Piece>; 64]) -> (res: bool)
    ensures
        res == insufficient_material(b@),
{
    let res = only_kings_and_minors(b) && (all_pairs_ok(b, false) || all_pairs_ok(b, true));
    proof {
        // Relate the `pair_ok` formulation to the one in the spec.
        let one = forall|f1: int, r1: int, f2: int, r2: int|
            on_board(f1, r1) && on_board(f2, r2) ==> #[trigger] pair_ok(b@, false, f1, r1, f2, r2);
        let spec_one = forall|f1: int, r1: int, f2: int, r2: int|
            on_board(f1, r1) && on_board(f2, r2) && #[trigger] minor_at(b@, f1, r1)
                && #[trigger] minor_at(b@, f2, r2) ==> f1 == f2 && r1 == r2;
        assert(one == spec_one) by {
            if spec_one {
                assert forall|f1: int, r1: int, f2: int, r2: int|
                    on_board(f1, r1) && on_board(f2, r2) implies #[trigger] pair_ok(b@, false, f1, r1, f2, r2) by {
                    if minor_at(b@, f1, r1) && minor_at(b@, f2, r2) {}
                }
            }
            if one {
                assert forall|f1: int, r1: int, f2: int, r2: int|
                    on_board(f1, r1) && on_board(f2, r2) && #[trigger] minor_at(b@, f1, r1)
                        && #[trigger] minor_at(b@, f2, r2) implies f1 == f2 && r1 == r2 by {
                    assert(pair_ok(b@, false, f1, r1, f2, r2));
                }
            }
        }
        let shade = forall|f1: int, r1: int, f2: int, r2: int|
            on_board(f1, r1) && on_board(f2, r2) ==> #[trigger] pair_ok(b@, true, f1, r1, f2, r2);
        let spec_shade = forall|f1: int, r1: int, f2: int, r2: int|
            on_board(f1, r1) && on_board(f2, r2) && #[trigger] minor_at(b@, f1, r1)
                && #[trigger] minor_at(b@, f2, r2) ==> bishop_at(b@, f1, r1) && bishop_at(b@, f2, r2)
                && square_shade(f1, r1) == square_shade(f2, r2);
        assert(shade == spec_shade) by {
            if spec_shade {
                assert forall|f1: int, r1: int, f2: int, r2: int|
                    on_board(f1, r1) && on_board(f2, r2) implies #[trigger] pair_ok(b@, true, f1, r1, f2, r2) by {
                    if minor_at(b@, f1, r1) && minor_at(b@, f2, r2) {}
                }
            }
            if shade {
                assert forall|f1: int, r1: int, f2: int, r2: int|
                    on_board(f1, r1) && on_board(f2, r2) && #[trigger] minor_at(b@, f1, r1)
                        && #[trigger] minor_at(b@, f2, r2) implies bishop_at(b@, f1, r1)
                        && bishop_at(b@, f2, r2) && square_shade(f1, r1) == square_shade(f2, r2) by {
                    assert(pair_ok(b@, true, f1, r1, f2, r2));
                }
            }
        }
    }
    res
}

// ---------------------------------------------------------------------------
// Repetition
// ---------------------------------------------------------------------------

/// Is the en-passant capture from `from` to `to` (with any allowed promotion) legal?
fn ep_capture_legal(pos: &Position, from: Square, to: Square) -> (res: bool)
    requires
        valid_square(from),
        valid_square(to),
    ensures
        res == exists|m: Move| m.from == from && m.to == to && is_legal(pos@, m) && is_en_passant(pos@, m),
{
    let base = Move { from, to, promotion: None };
    if !is_en_passant_exec(pos, base) {
        // Whether a move is en passant does not depend on its promotion.
        assert forall|m: Move| m.from == from && m.to == to implies !is_en_passant(pos@, m) by {}
        return false;
    }
    let promotes = to.rank as i32 == promotion_rank_exec(pos.turn);
    if promotes {
        let res = is_legal_exec(pos, Move { from, to, promotion: Some(PieceKind::Knight) })
            || is_legal_exec(pos, Move { from, to, promotion: Some(PieceKind::Bishop) })
            || is_legal_exec(pos, Move { from, to, promotion: Some(PieceKind::Rook) })
            || is_legal_exec(pos, Move { from, to, promotion: Some(PieceKind::Queen) });
        proof {
            if !res {
                assert forall|m: Move| m.from == from && m.to == to && is_en_passant(pos@, m) implies !is_legal(pos@, m) by {
                    if is_legal(pos@, m) {
                        lemma_legal_promotion(pos@, m);
                    }
                }
            } else {
                if is_legal(pos@, Move { from, to, promotion: Some(PieceKind::Knight) }) {
                    assert(is_en_passant(pos@, Move { from, to, promotion: Some(PieceKind::Knight) }));
                } else if is_legal(pos@, Move { from, to, promotion: Some(PieceKind::Bishop) }) {
                    assert(is_en_passant(pos@, Move { from, to, promotion: Some(PieceKind::Bishop) }));
                } else if is_legal(pos@, Move { from, to, promotion: Some(PieceKind::Rook) }) {
                    assert(is_en_passant(pos@, Move { from, to, promotion: Some(PieceKind::Rook) }));
                } else {
                    assert(is_en_passant(pos@, Move { from, to, promotion: Some(PieceKind::Queen) }));
                }
            }
        }
        res
    } else {
        let res = is_legal_exec(pos, base);
        proof {
            if res {
                assert(is_en_passant(pos@, base));
            } else {
                assert forall|m: Move| m.from == from && m.to == to && is_en_passant(pos@, m) implies !is_legal(pos@, m) by {
                    if is_legal(pos@, m) {
                        lemma_legal_promotion(pos@, m);
                    }
                }
            }
        }
        res
    }
}

/// Only the (at most two) pawns beside the pawn that just double-pushed can capture en passant.
pub fn en_passant_available_exec(pos: &Position) -> (res: bool)
    ensures
        res == en_passant_available(pos@),
{
    let to = match pos.ep {
        None => {
            return false;
        },
        Some(s) => s,
    };
    if !(to.file < 8 && to.rank < 8) {
        return false;
    }
    let r = to.rank as i32 - forward_exec(pos.turn);
    if !(0 <= r && r < 8) {
        assert forall|m: Move| !(is_legal(pos@, m) && is_en_passant(pos@, m)) by {}
        return false;
    }
    let left = to.file > 0 && ep_capture_legal(pos, Square { file: to.file - 1, rank: r as u8 }, to);
    let right = to.file < 7 && ep_capture_legal(pos, Square { file: to.file + 1, rank: r as u8 }, to);
    proof {
        if !(left || right) {
            assert forall|m: Move| !(is_legal(pos@, m) && is_en_passant(pos@, m)) by {
                if is_legal(pos@, m) && is_en_passant(pos@, m) {
                    if m.from.file < to.file {
                        assert(m.from == Square { file: (to.file - 1) as u8, rank: r as u8 });
                    } else {
                        assert(m.from == Square { file: (to.file + 1) as u8, rank: r as u8 });
                    }
                }
            }
        }
    }
    left || right
}

fn board_eq(a: &[Option<Piece>; 64], b: &[Option<Piece>; 64]) -> (res: bool)
    ensures
        res == (a@ == b@),
{
    let mut i: usize = 0;
    while i < 64
        invariant
            0 <= i <= 64,
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases 64 - i,
    {
        if !opt_piece_eq(a[i], b[i]) {
            return false;
        }
        i += 1;
    }
    assert(a@ =~= b@);
    true
}

/// The key for the repetition rule; `ep` is the *effective* en-passant square.
fn key_matches(p: &Position, board: &[Option<Piece>; 64], turn: Color, castling: CastlingRights, ep: Option<Square>) -> (res: bool)
    ensures
        res == (repetition_key(p@) == PositionKey { board: board@, turn, castling, ep }),
{
    if !(color_eq(p.turn, turn) && castling_eq(p.castling, castling) && board_eq(&p.board, board)) {
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
        let pos = *self.current();
        if !(is_legal_exec(&pos, m) && pos.halfmove_clock < u32::MAX && pos.fullmove_number < u32::MAX) {
            return false;
        }
        let next = apply_move_exec(&pos, m);
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
        let mut count: usize = 0;
        let mut i: usize = 0;
        while i < self.history.len()
            invariant
                0 <= i <= self.history@.len(),
                count <= i,
                count as nat == occurrences(self@.history, key, i as int),
                key == (PositionKey { board: cur.board@, turn: cur.turn, castling: cur.castling, ep }),
            decreases self.history@.len() - i,
        {
            if key_matches(&self.history[i], &cur.board, cur.turn, cur.castling, ep) {
                count += 1;
            }
            i += 1;
        }
        count
    }

    /// The automatic result of the game, if it has ended.
    pub fn outcome(&self) -> (o: Option<GameOutcome>)
        requires
            self.inv(),
        ensures
            o == game_outcome(self@),
    {
        let pos = self.current();
        let check = in_check_exec(&pos.board, pos.turn);
        let any_move = has_legal_move_exec(pos);
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
