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

pub open spec fn sign(x: int) -> int {
    if x > 0 { 1 } else if x < 0 { -1 } else { 0 }
}

/// One of the eight unit directions of a queen.
pub open spec fn unit_dir(sf: int, sr: int) -> bool {
    -1 <= sf <= 1 && -1 <= sr <= 1 && (sf != 0 || sr != 0)
}

/// (df, dr) is a displacement along a rank, file or diagonal, in direction (sf, sr).
pub open spec fn in_dir(df: int, dr: int, sf: int, sr: int) -> bool {
    &&& is_orthogonal(df, dr) || is_diagonal(df, dr)
    &&& sign(df) == sf
    &&& sign(dr) == sr
}

pub open spec fn knight_shape(df: int, dr: int) -> bool {
    (abs(df) == 1 && abs(dr) == 2) || (abs(df) == 2 && abs(dr) == 1)
}

/// Whether piece `p` standing `k` steps from the target in direction (sf, sr), with
/// the squares in between empty, attacks the target.
pub open spec fn ray_hit(p: Piece, sf: int, sr: int, k: int) -> bool {
    match p.kind {
        PieceKind::Queen => true,
        PieceKind::Rook => sf == 0 || sr == 0,
        PieceKind::Bishop => sf != 0 && sr != 0,
        PieceKind::King => k == 1,
        PieceKind::Pawn => k == 1 && sf != 0 && sr == -forward(p.color),
        PieceKind::Knight => false,
    }
}

pub proof fn lemma_in_dir(df: int, dr: int, sf: int, sr: int)
    requires
        in_dir(df, dr, sf, sr),
    ensures
        unit_dir(sf, sr),
        distance(df, dr) >= 1,
        df == step(0, sf, distance(df, dr)),
        dr == step(0, sr, distance(df, dr)),
{
}

/// The squares strictly between (f, r) and the square `k` steps away in direction (sf, sr)
/// are exactly the ray squares `1 .. k`.
pub proof fn lemma_ray_path(b: Board, f: int, r: int, sf: int, sr: int, k: int)
    requires
        unit_dir(sf, sr),
        k >= 1,
    ensures
        distance(f - step(f, sf, k), r - step(r, sr, k)) == k,
        path_clear(b, step(f, sf, k), step(r, sr, k), f, r) <==> (forall|j: int|
            1 <= j < k ==> #[trigger] is_empty(b, step(f, sf, j), step(r, sr, j))),
{
    let f1 = step(f, sf, k);
    let r1 = step(r, sr, k);
    assert forall|j: int| 0 < j < k implies #[trigger] step(f1, f - f1, j) == step(f, sf, k - j) && step(
        r1,
        r - r1,
        j,
    ) == step(r, sr, k - j) by {}
    if path_clear(b, f1, r1, f, r) {
        assert forall|j: int| 1 <= j < k implies #[trigger] is_empty(b, step(f, sf, j), step(r, sr, j)) by {
            assert(step(f1, f - f1, k - j) == step(f, sf, j));
            assert(step(r1, r - r1, k - j) == step(r, sr, j));
            assert(is_empty(b, step(f1, f - f1, k - j), step(r1, r - r1, k - j)));
        }
    }
    if forall|j: int| 1 <= j < k ==> #[trigger] is_empty(b, step(f, sf, j), step(r, sr, j)) {
        assert forall|j: int| 0 < j < distance(f - f1, r - r1) implies #[trigger] is_empty(
            b,
            step(f1, f - f1, j),
            step(r1, r - r1, j),
        ) by {
            assert(is_empty(b, step(f, sf, k - j), step(r, sr, k - j)));
        }
    }
}

/// A piece `k` steps away along a clear ray attacks the target iff `ray_hit`.
pub proof fn lemma_ray_attacks(b: Board, p: Piece, f: int, r: int, sf: int, sr: int, k: int)
    requires
        unit_dir(sf, sr),
        k >= 1,
        forall|j: int| 1 <= j < k ==> #[trigger] is_empty(b, step(f, sf, j), step(r, sr, j)),
    ensures
        attacks(b, p, step(f, sf, k), step(r, sr, k), f, r) == ray_hit(p, sf, sr, k),
{
    lemma_ray_path(b, f, r, sf, sr, k);
}

/// Nothing standing behind an occupied ray square attacks the target.
pub proof fn lemma_ray_blocked(b: Board, p: Piece, f: int, r: int, sf: int, sr: int, k: int, k2: int)
    requires
        unit_dir(sf, sr),
        1 <= k < k2,
        !is_empty(b, step(f, sf, k), step(r, sr, k)),
    ensures
        !attacks(b, p, step(f, sf, k2), step(r, sr, k2), f, r),
{
    lemma_ray_path(b, f, r, sf, sr, k2);
}

/// The first piece on the ray from (f, r) in direction (sf, sr), and whether it is an
/// attacker of color `by`. Pieces further along the ray are blocked by it.
pub fn ray_attacked_exec(b: &[Option<Piece>; 64], f: i32, r: i32, sf: i32, sr: i32, by: Color) -> (res: bool)
    requires
        on_board(f as int, r as int),
        unit_dir(sf as int, sr as int),
    ensures
        res ==> is_attacked(b@, f as int, r as int, by),
        !res ==> forall|f1: int, r1: int|
            on_board(f1, r1) && in_dir(f1 - f, r1 - r, sf as int, sr as int) ==> !#[trigger] attacker_at(
                b@,
                f1,
                r1,
                f as int,
                r as int,
                by,
            ),
{
    let ghost (fi, ri, sfi, sri) = (f as int, r as int, sf as int, sr as int);
    let mut k: i32 = 1;
    let mut f1 = f + sf;
    let mut r1 = r + sr;
    while 0 <= f1 && f1 < 8 && 0 <= r1 && r1 < 8
        invariant
            on_board(fi, ri),
            unit_dir(sfi, sri),
            fi == f,
            ri == r,
            sfi == sf,
            sri == sr,
            1 <= k <= 8,
            f1 == step(fi, sfi, k as int),
            r1 == step(ri, sri, k as int),
            forall|j: int| 1 <= j < k ==> #[trigger] is_empty(b@, step(fi, sfi, j), step(ri, sri, j)),
        decreases 8 - k,
    {
        match get(b, f1, r1) {
            None => {
                k += 1;
                f1 += sf;
                r1 += sr;
            },
            Some(p) => {
                let hit = color_eq(p.color, by) && match p.kind {
                    PieceKind::Queen => true,
                    PieceKind::Rook => sf == 0 || sr == 0,
                    PieceKind::Bishop => sf != 0 && sr != 0,
                    PieceKind::King => k == 1,
                    PieceKind::Pawn => k == 1 && sf != 0 && sr == -forward_exec(by),
                    PieceKind::Knight => false,
                };
                proof {
                    lemma_ray_attacks(b@, p, fi, ri, sfi, sri, k as int);
                    if hit {
                        assert(attacker_at(b@, f1 as int, r1 as int, fi, ri, by));
                    }
                    assert forall|g1: int, h1: int|
                        on_board(g1, h1) && in_dir(g1 - f, h1 - r, sfi, sri) && !hit implies !#[trigger] attacker_at(
                            b@,
                            g1,
                            h1,
                            fi,
                            ri,
                            by,
                        ) by {
                        let k2 = distance(g1 - f, h1 - r);
                        lemma_in_dir(g1 - f, h1 - r, sfi, sri);
                        assert(g1 == step(fi, sfi, k2));
                        assert(h1 == step(ri, sri, k2));
                        if k2 < k {
                            assert(is_empty(b@, step(fi, sfi, k2), step(ri, sri, k2)));
                        } else if k2 > k {
                            if let Some(q) = at(b@, g1, h1) {
                                lemma_ray_blocked(b@, q, fi, ri, sfi, sri, k as int, k2);
                            }
                        }
                    }
                }
                return hit;
            },
        }
    }
    proof {
        assert forall|g1: int, h1: int|
            on_board(g1, h1) && in_dir(g1 - f, h1 - r, sfi, sri) implies !#[trigger] attacker_at(
                b@,
                g1,
                h1,
                fi,
                ri,
                by,
            ) by {
            let k2 = distance(g1 - f, h1 - r);
            lemma_in_dir(g1 - f, h1 - r, sfi, sri);
            assert(g1 == step(fi, sfi, k2));
            assert(h1 == step(ri, sri, k2));
            assert(k2 < k);
            assert(is_empty(b@, step(fi, sfi, k2), step(ri, sri, k2)));
        }
    }
    false
}

/// Is there a knight of color `by` on (f, r)? (False off the board.)
fn knight_on_exec(b: &[Option<Piece>; 64], f: i32, r: i32, by: Color) -> (res: bool)
    requires
        -2 <= f < 10,
        -2 <= r < 10,
    ensures
        res == (on_board(f as int, r as int) && at(b@, f as int, r as int) == Some(
            Piece { color: by, kind: PieceKind::Knight },
        )),
{
    if 0 <= f && f < 8 && 0 <= r && r < 8 {
        match get(b, f, r) {
            Some(p) => color_eq(p.color, by) && kind_eq(p.kind, PieceKind::Knight),
            None => false,
        }
    } else {
        false
    }
}

/// Is (f, r) attacked by a knight of color `by`?
fn knight_attacked_exec(b: &[Option<Piece>; 64], f: i32, r: i32, by: Color) -> (res: bool)
    requires
        on_board(f as int, r as int),
    ensures
        res ==> is_attacked(b@, f as int, r as int, by),
        !res ==> forall|f1: int, r1: int|
            on_board(f1, r1) && knight_shape(f1 - f, r1 - r) ==> !#[trigger] attacker_at(
                b@,
                f1,
                r1,
                f as int,
                r as int,
                by,
            ),
{
    let res = knight_on_exec(b, f + 1, r + 2, by) || knight_on_exec(b, f + 2, r + 1, by)
        || knight_on_exec(b, f + 2, r - 1, by) || knight_on_exec(b, f + 1, r - 2, by)
        || knight_on_exec(b, f - 1, r - 2, by) || knight_on_exec(b, f - 2, r - 1, by)
        || knight_on_exec(b, f - 2, r + 1, by) || knight_on_exec(b, f - 1, r + 2, by);
    proof {
        if res {
            if knight_on(b@, f + 1, r + 2, by) {
                assert(attacker_at(b@, f + 1, r + 2, f as int, r as int, by));
            } else if knight_on(b@, f + 2, r + 1, by) {
                assert(attacker_at(b@, f + 2, r + 1, f as int, r as int, by));
            } else if knight_on(b@, f + 2, r - 1, by) {
                assert(attacker_at(b@, f + 2, r - 1, f as int, r as int, by));
            } else if knight_on(b@, f + 1, r - 2, by) {
                assert(attacker_at(b@, f + 1, r - 2, f as int, r as int, by));
            } else if knight_on(b@, f - 1, r - 2, by) {
                assert(attacker_at(b@, f - 1, r - 2, f as int, r as int, by));
            } else if knight_on(b@, f - 2, r - 1, by) {
                assert(attacker_at(b@, f - 2, r - 1, f as int, r as int, by));
            } else if knight_on(b@, f - 2, r + 1, by) {
                assert(attacker_at(b@, f - 2, r + 1, f as int, r as int, by));
            } else {
                assert(attacker_at(b@, f - 1, r + 2, f as int, r as int, by));
            }
        } else {
            assert forall|f1: int, r1: int|
                on_board(f1, r1) && knight_shape(f1 - f, r1 - r) implies !#[trigger] attacker_at(
                    b@,
                    f1,
                    r1,
                    f as int,
                    r as int,
                    by,
                ) by {
                assert(!knight_on(b@, f1, r1, by));
            }
        }
    }
    res
}

pub open spec fn knight_on(b: Board, f: int, r: int, by: Color) -> bool {
    on_board(f, r) && at(b, f, r) == Some(Piece { color: by, kind: PieceKind::Knight })
}

/// Is (f, r) attacked by a piece of color `by`?
///
/// Rather than trying every square, this looks outwards from (f, r): the eight knight
/// squares, and the first piece along each of the eight lines (which covers pawns and
/// the king, whose attacks are one step along a line).
pub fn is_attacked_exec(b: &[Option<Piece>; 64], f: i32, r: i32, by: Color) -> (res: bool)
    requires
        on_board(f as int, r as int),
    ensures
        res == is_attacked(b@, f as int, r as int, by),
{
    let res = knight_attacked_exec(b, f, r, by) || ray_attacked_exec(b, f, r, 1, 0, by)
        || ray_attacked_exec(b, f, r, -1, 0, by) || ray_attacked_exec(b, f, r, 0, 1, by)
        || ray_attacked_exec(b, f, r, 0, -1, by) || ray_attacked_exec(b, f, r, 1, 1, by)
        || ray_attacked_exec(b, f, r, 1, -1, by) || ray_attacked_exec(b, f, r, -1, 1, by)
        || ray_attacked_exec(b, f, r, -1, -1, by);
    proof {
        if !res {
            assert forall|f1: int, r1: int| on_board(f1, r1) implies !#[trigger] attacker_at(
                b@,
                f1,
                r1,
                f as int,
                r as int,
                by,
            ) by {
                let df = f1 - f;
                let dr = r1 - r;
                if is_orthogonal(df, dr) || is_diagonal(df, dr) {
                    assert(in_dir(df, dr, sign(df), sign(dr)));
                } else if knight_shape(df, dr) {
                } else {
                    if let Some(p) = at(b@, f1, r1) {
                        assert(!attacks(b@, p, f1, r1, f as int, r as int));
                    }
                }
            }
        }
    }
    res
}

/// The king of color `c` stands on (f, r), and nowhere else.
pub open spec fn king_only_at(b: Board, c: Color, f: int, r: int) -> bool {
    &&& on_board(f, r)
    &&& forall|f2: int, r2: int|
        on_board(f2, r2) ==> (#[trigger] at(b, f2, r2) == Some(king_of(c)) <==> (f2 == f && r2 == r))
}

pub proof fn lemma_king_only_in_check(b: Board, c: Color, f: int, r: int)
    requires
        king_only_at(b, c, f, r),
    ensures
        in_check(b, c) == is_attacked(b, f, r, opponent(c)),
{
    assert(at(b, f, r) == Some(king_of(c)));
}

/// The square of the only king of color `c`, if there is exactly one.
pub fn find_king(b: &[Option<Piece>; 64], c: Color) -> (ks: Option<(i32, i32)>)
    ensures
        ks matches Some((f, r)) ==> king_only_at(b@, c, f as int, r as int),
{
    let king = Some(Piece { color: c, kind: PieceKind::King });
    let mut found: Option<usize> = None;
    let mut i: usize = 0;
    while i < 64
        invariant
            0 <= i <= 64,
            king == Some(king_of(c)),
            found matches Some(j) ==> j < i && b@[j as int] == Some(king_of(c)),
            forall|j: int| 0 <= j < i && b@[j] == Some(king_of(c)) ==> (found matches Some(k) && k == j),
        decreases 64 - i,
    {
        if opt_piece_eq(b[i], king) {
            if found.is_some() {
                return None;
            }
            found = Some(i);
        }
        i += 1;
    }
    match found {
        None => None,
        Some(j) => {
            let (f, r) = ((j % 8) as i32, (j / 8) as i32);
            proof {
                lemma_square_index(j as int);
                assert forall|f2: int, r2: int| on_board(f2, r2) implies (#[trigger] at(b@, f2, r2) == Some(king_of(c)) <==> (f2 == f && r2 == r)) by {
                    lemma_index_injective(f2, r2, f as int, r as int);
                }
            }
            Some((f, r))
        },
    }
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
