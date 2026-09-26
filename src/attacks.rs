//! Attack detection, proven equal to `spec::attacks`, `spec::is_attacked` and `spec::in_check`.
use crate::position::*;
#[cfg(verus_only)]
use crate::spec::*;
use crate::types::*;
use vstd::prelude::*;

verus! {

pub fn path_clear_exec(b: &[Option<Piece>; 64], f1: i32, r1: i32, f2: i32, r2: i32) -> (res: bool)
    requires
        on_board(f1 as int, r1 as int),
        on_board(f2 as int, r2 as int),
        is_orthogonal(f2 - f1, r2 - r1) || is_diagonal(f2 - f1, r2 - r1),
    ensures
        res == path_clear(b@, f1 as int, r1 as int, f2 as int, r2 as int),
{
    let df = f2 - f1;
    let dr = r2 - r1;
    let sf: i32 = if df > 0 { 1 } else if df < 0 { -1 } else { 0 };
    let sr: i32 = if dr > 0 { 1 } else if dr < 0 { -1 } else { 0 };
    let adf = abs_exec(df);
    let adr = abs_exec(dr);
    let n = if adf >= adr { adf } else { adr };
    assert(n == distance(df as int, dr as int));
    let mut k: i32 = 1;
    let mut f = f1 + sf;
    let mut r = r1 + sr;
    while k < n
        invariant
            1 <= k <= n <= 7,
            n == distance(df as int, dr as int),
            df == f2 - f1,
            dr == r2 - r1,
            is_orthogonal(df as int, dr as int) || is_diagonal(df as int, dr as int),
            on_board(f1 as int, r1 as int),
            on_board(f2 as int, r2 as int),
            sf == (if df > 0 { 1int } else if df < 0 { -1int } else { 0int }),
            sr == (if dr > 0 { 1int } else if dr < 0 { -1int } else { 0int }),
            f == step(f1 as int, df as int, k as int),
            r == step(r1 as int, dr as int, k as int),
            forall|j: int|
                0 < j < k ==> #[trigger] is_empty(
                    b@,
                    step(f1 as int, df as int, j),
                    step(r1 as int, dr as int, j),
                ),
        decreases n - k,
    {
        if get(b, f, r).is_some() {
            assert(!is_empty(b@, step(f1 as int, df as int, k as int), step(r1 as int, dr as int, k as int)));
            return false;
        }
        k += 1;
        f += sf;
        r += sr;
    }
    true
}

pub fn attacks_exec(b: &[Option<Piece>; 64], p: Piece, f1: i32, r1: i32, f2: i32, r2: i32) -> (res:
    bool)
    requires
        on_board(f1 as int, r1 as int),
        on_board(f2 as int, r2 as int),
    ensures
        res == attacks(b@, p, f1 as int, r1 as int, f2 as int, r2 as int),
{
    let df = f2 - f1;
    let dr = r2 - r1;
    let adf = abs_exec(df);
    let adr = abs_exec(dr);
    let orth = (df == 0) != (dr == 0);
    let diag = df != 0 && adf == adr;
    match p.kind {
        PieceKind::Pawn => dr == forward_exec(p.color) && adf == 1,
        PieceKind::Knight => (adf == 1 && adr == 2) || (adf == 2 && adr == 1),
        PieceKind::Bishop => diag && path_clear_exec(b, f1, r1, f2, r2),
        PieceKind::Rook => orth && path_clear_exec(b, f1, r1, f2, r2),
        PieceKind::Queen => (orth || diag) && path_clear_exec(b, f1, r1, f2, r2),
        PieceKind::King => {
            let d = if adf >= adr { adf } else { adr };
            d == 1
        },
    }
}

pub fn attacker_at_exec(b: &[Option<Piece>; 64], f1: i32, r1: i32, f: i32, r: i32, by: Color) -> (res:
    bool)
    requires
        on_board(f1 as int, r1 as int),
        on_board(f as int, r as int),
    ensures
        res == attacker_at(b@, f1 as int, r1 as int, f as int, r as int, by),
{
    match get(b, f1, r1) {
        Some(p) => color_eq(p.color, by) && attacks_exec(b, p, f1, r1, f, r),
        None => false,
    }
}

/// Is (f, r) attacked by a piece of color `by`?
pub fn is_attacked_exec(b: &[Option<Piece>; 64], f: i32, r: i32, by: Color) -> (res: bool)
    requires
        on_board(f as int, r as int),
    ensures
        res == is_attacked(b@, f as int, r as int, by),
{
    let mut r1: i32 = 0;
    while r1 < 8
        invariant
            0 <= r1 <= 8,
            on_board(f as int, r as int),
            forall|f2: int, r2: int|
                0 <= f2 < 8 && 0 <= r2 < r1 ==> !#[trigger] attacker_at(
                    b@,
                    f2,
                    r2,
                    f as int,
                    r as int,
                    by,
                ),
        decreases 8 - r1,
    {
        let mut f1: i32 = 0;
        while f1 < 8
            invariant
                0 <= f1 <= 8,
                0 <= r1 < 8,
                on_board(f as int, r as int),
                forall|f2: int, r2: int|
                    0 <= f2 < 8 && 0 <= r2 < r1 ==> !#[trigger] attacker_at(
                        b@,
                        f2,
                        r2,
                        f as int,
                        r as int,
                        by,
                    ),
                forall|f2: int|
                    0 <= f2 < f1 ==> !#[trigger] attacker_at(
                        b@,
                        f2,
                        r1 as int,
                        f as int,
                        r as int,
                        by,
                    ),
            decreases 8 - f1,
        {
            if attacker_at_exec(b, f1, r1, f, r, by) {
                assert(on_board(f1 as int, r1 as int));
                return true;
            }
            f1 += 1;
        }
        r1 += 1;
    }
    false
}

/// Is the king of color `c` in check?
pub fn in_check_exec(b: &[Option<Piece>; 64], c: Color) -> (res: bool)
    ensures
        res == in_check(b@, c),
{
    let opp = opponent_exec(c);
    let king = Piece { color: c, kind: PieceKind::King };
    let mut r: i32 = 0;
    while r < 8
        invariant
            0 <= r <= 8,
            opp == opponent(c),
            king == king_of(c),
            forall|f2: int, r2: int|
                0 <= f2 < 8 && 0 <= r2 < r ==> !(#[trigger] at(b@, f2, r2) == Some(king_of(c))
                    && is_attacked(b@, f2, r2, opponent(c))),
        decreases 8 - r,
    {
        let mut f: i32 = 0;
        while f < 8
            invariant
                0 <= f <= 8,
                0 <= r < 8,
                opp == opponent(c),
                king == king_of(c),
                forall|f2: int, r2: int|
                    0 <= f2 < 8 && 0 <= r2 < r ==> !(#[trigger] at(b@, f2, r2) == Some(king_of(c))
                        && is_attacked(b@, f2, r2, opponent(c))),
                forall|f2: int|
                    0 <= f2 < f ==> !(#[trigger] at(b@, f2, r as int) == Some(king_of(c))
                        && is_attacked(b@, f2, r as int, opponent(c))),
            decreases 8 - f,
        {
            if opt_piece_eq(get(b, f, r), Some(king)) && is_attacked_exec(b, f, r, opp) {
                assert(on_board(f as int, r as int));
                return true;
            }
            f += 1;
        }
        r += 1;
    }
    false
}

} // verus!
