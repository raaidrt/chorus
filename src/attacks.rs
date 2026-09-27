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

/// A bishop, rook or queen of color `by` on (f1, r1) attacks (f, r).
pub open spec fn slider_attacker_at(b: Board, f1: int, r1: int, f: int, r: int, by: Color) -> bool {
    &&& attacker_at(b, f1, r1, f, r, by)
    &&& at(b, f1, r1) matches Some(p) && (p.kind == PieceKind::Bishop || p.kind == PieceKind::Rook
        || p.kind == PieceKind::Queen)
}

/// A unit direction: one of the eight king steps.
pub open spec fn unit_dir(df: int, dr: int) -> bool {
    -1 <= df <= 1 && -1 <= dr <= 1 && (df != 0 || dr != 0)
}

/// The squares strictly between the `k`-th square of a ray and its origin are the
/// first `k - 1` squares of the ray, so they are clear if those are empty.
pub proof fn lemma_ray_path_clear(b: Board, f: int, r: int, df: int, dr: int, k: int)
    requires
        unit_dir(df, dr),
        k >= 1,
        forall|j: int| 1 <= j < k ==> #[trigger] is_empty(b, step(f, df, j), step(r, dr, j)),
    ensures
        path_clear(b, step(f, df, k), step(r, dr, k), f, r),
        distance(f - step(f, df, k), r - step(r, dr, k)) == k,
        is_orthogonal(f - step(f, df, k), r - step(r, dr, k)) == (df == 0 || dr == 0),
        is_diagonal(f - step(f, df, k), r - step(r, dr, k)) == (df != 0 && dr != 0),
{
    let g = step(f, df, k);
    let h = step(r, dr, k);
    assert forall|j: int| 0 < j < distance(f - g, r - h) implies #[trigger] is_empty(
        b,
        step(g, f - g, j),
        step(h, r - h, j),
    ) by {
        assert(step(g, f - g, j) == step(f, df, k - j));
        assert(step(h, r - h, j) == step(r, dr, k - j));
        assert(is_empty(b, step(f, df, k - j), step(r, dr, k - j)));
    }
}

/// An occupied `m`-th square of a ray blocks every later square of the ray from its origin.
pub proof fn lemma_ray_blocked(b: Board, f: int, r: int, df: int, dr: int, m: int, k: int)
    requires
        unit_dir(df, dr),
        1 <= m < k,
        !is_empty(b, step(f, df, m), step(r, dr, m)),
    ensures
        !path_clear(b, step(f, df, k), step(r, dr, k), f, r),
{
    let g = step(f, df, k);
    let h = step(r, dr, k);
    assert(distance(f - g, r - h) == k);
    assert(step(g, f - g, k - m) == step(f, df, m));
    assert(step(h, r - h, k - m) == step(r, dr, m));
    assert(!is_empty(b, step(g, f - g, k - m), step(h, r - h, k - m)));
}

/// The number of squares on the ray from (f, r) in direction (df, dr).
pub fn ray_len(f: i32, r: i32, df: i32, dr: i32) -> (n: i32)
    requires
        on_board(f as int, r as int),
        unit_dir(df as int, dr as int),
    ensures
        0 <= n <= 7,
        forall|k: int| k >= 1 ==> (#[trigger] on_board(step(f as int, df as int, k), step(r as int, dr as int, k)) <==> k <= n),
{
    let nf = if df > 0 { 7 - f } else if df < 0 { f } else { 7 };
    let nr = if dr > 0 { 7 - r } else if dr < 0 { r } else { 7 };
    if nf < nr { nf } else { nr }
}

/// A pawn of color `by` one step from its target in direction (df, dr) attacks it.
pub open spec fn pawn_dir(df: int, dr: int, by: Color) -> bool {
    df != 0 && dr == -forward(by)
}

/// Is (f, r) attacked along the ray in direction (df, dr) by a bishop, rook or queen of
/// color `by`? Walks to the first occupied square of the ray. With `near`, the king (and,
/// in a pawn's capture direction, the pawn) of color `by` next to (f, r) counts too.
pub fn ray_attacked_exec(b: &[Option<Piece>; 64], f: i32, r: i32, df: i32, dr: i32, by: Color, near: bool) -> (res:
    bool)
    requires
        on_board(f as int, r as int),
        unit_dir(df as int, dr as int),
    ensures
        res ==> is_attacked(b@, f as int, r as int, by),
        !res && near && on_board(f + df, r + dr) ==> at(b@, f + df, r + dr) != Some(
            Piece { color: by, kind: PieceKind::King },
        ) && (pawn_dir(df as int, dr as int, by) ==> at(b@, f + df, r + dr) != Some(
            Piece { color: by, kind: PieceKind::Pawn },
        )),
        !res ==> forall|k: int|
            k >= 1 && on_board(step(f as int, df as int, k), step(r as int, dr as int, k))
                ==> !#[trigger] slider_attacker_at(
                b@,
                step(f as int, df as int, k),
                step(r as int, dr as int, k),
                f as int,
                r as int,
                by,
            ),
{
    let diag = df != 0 && dr != 0;
    let pawn_near = near && df != 0 && dr == -forward_exec(by);
    // Step one board index along the ray, for as many squares as it has.
    let n = ray_len(f, r, df, dr);
    let d = dr * 8 + df;
    let mut k: i32 = 1;
    let mut idx = r * 8 + f + d;
    let ghost mut g: int = f + df;
    let ghost mut h: int = r + dr;
    while k <= n
        invariant
            1 <= k <= n + 1,
            0 <= n <= 7,
            forall|k2: int| k2 >= 1 ==> (#[trigger] on_board(step(f as int, df as int, k2), step(r as int, dr as int, k2)) <==> k2 <= n),
            d == dr * 8 + df,
            idx == index_of(g, h),
            on_board(f as int, r as int),
            unit_dir(df as int, dr as int),
            diag == (df != 0 && dr != 0),
            pawn_near == (near && pawn_dir(df as int, dr as int, by)),
            g == step(f as int, df as int, k as int),
            h == step(r as int, dr as int, k as int),
            forall|j: int|
                1 <= j < k ==> #[trigger] is_empty(
                    b@,
                    step(f as int, df as int, j),
                    step(r as int, dr as int, j),
                ),
        decreases 8 - k,
    {
        assert(on_board(g, h));
        match b[idx as usize] {
            None => {
                assert(is_empty(b@, g, h));
                k += 1;
                idx += d;
                proof {
                    g = g + df;
                    h = h + dr;
                }
            },
            Some(p) => {
                let hit = color_eq(p.color, by) && match p.kind {
                    PieceKind::Queen => true,
                    PieceKind::Bishop => diag,
                    PieceKind::Rook => !diag,
                    PieceKind::King => near && k == 1,
                    PieceKind::Pawn => pawn_near && k == 1,
                    _ => false,
                };
                proof {
                    assert(step(f as int, df as int, 1) == f + df && step(r as int, dr as int, 1) == r + dr);
                    if k > 1 {
                        assert(is_empty(b@, step(f as int, df as int, 1), step(r as int, dr as int, 1)));
                    }
                    lemma_ray_path_clear(b@, f as int, r as int, df as int, dr as int, k as int);
                    if hit {
                        assert(attacker_at(b@, g, h, f as int, r as int, by));
                    }
                    assert forall|k2: int|
                        k2 >= 1 && on_board(
                            step(f as int, df as int, k2),
                            step(r as int, dr as int, k2),
                        ) && !hit implies !#[trigger] slider_attacker_at(
                        b@,
                        step(f as int, df as int, k2),
                        step(r as int, dr as int, k2),
                        f as int,
                        r as int,
                        by,
                    ) by {
                        if k2 < k {
                            assert(is_empty(
                                b@,
                                step(f as int, df as int, k2),
                                step(r as int, dr as int, k2),
                            ));
                        } else if k2 > k {
                            lemma_ray_blocked(
                                b@,
                                f as int,
                                r as int,
                                df as int,
                                dr as int,
                                k as int,
                                k2,
                            );
                        }
                    }
                }
                return hit;
            },
        }
    }
    proof {
        assert(step(f as int, df as int, 1) == f + df && step(r as int, dr as int, 1) == r + dr);
        if k > 1 {
            assert(is_empty(b@, step(f as int, df as int, 1), step(r as int, dr as int, 1)));
        }
        assert forall|k2: int|
            k2 >= 1 && on_board(
                step(f as int, df as int, k2),
                step(r as int, dr as int, k2),
            ) implies !#[trigger] slider_attacker_at(
            b@,
            step(f as int, df as int, k2),
            step(r as int, dr as int, k2),
            f as int,
            r as int,
            by,
        ) by {
            assert(k2 <= n);
            assert(k2 < k);
            assert(is_empty(b@, step(f as int, df as int, k2), step(r as int, dr as int, k2)));
        }
    }
    false
}

/// A pawn, knight or king of color `by` standing at offset (df, dr) from (f, r), placed so
/// that it attacks (f, r).
fn offset_attacker_exec(
    b: &[Option<Piece>; 64],
    f: i32,
    r: i32,
    df: i32,
    dr: i32,
    by: Color,
    kind: PieceKind,
) -> (res: bool)
    requires
        on_board(f as int, r as int),
        -2 <= df <= 2,
        -2 <= dr <= 2,
        kind == PieceKind::Pawn ==> -dr == forward(by) && abs(df as int) == 1,
        kind == PieceKind::Knight ==> (abs(df as int) == 1 && abs(dr as int) == 2) || (abs(
            df as int,
        ) == 2 && abs(dr as int) == 1),
        kind == PieceKind::King ==> distance(df as int, dr as int) == 1,
        kind == PieceKind::Pawn || kind == PieceKind::Knight || kind == PieceKind::King,
    ensures
        res == (on_board(f + df, r + dr) && at(b@, f + df, r + dr) == Some(
            Piece { color: by, kind },
        )),
        res ==> is_attacked(b@, f as int, r as int, by),
{
    let g = f + df;
    let h = r + dr;
    let res = 0 <= g && g < 8 && 0 <= h && h < 8 && opt_piece_eq(
        get(b, g, h),
        Some(Piece { color: by, kind }),
    );
    if res {
        assert(attacker_at(b@, g as int, h as int, f as int, r as int, by));
    }
    res
}

/// Is (f, r) attacked by a piece of color `by`?
///
/// Looks outward from (f, r): the eight knight squares, and the first piece along each of
/// the eight rays (which may be an adjacent king or pawn).
pub fn is_attacked_exec(b: &[Option<Piece>; 64], f: i32, r: i32, by: Color) -> (res: bool)
    requires
        on_board(f as int, r as int),
    ensures
        res == is_attacked(b@, f as int, r as int, by),
{
    let knight = PieceKind::Knight;
    // The king and pawn squares are the first squares of the rays, so the ray walks check them.
    if offset_attacker_exec(b, f, r, 1, 2, by, knight) || offset_attacker_exec(b, f, r, 2, 1, by, knight)
        || offset_attacker_exec(b, f, r, 2, -1, by, knight) || offset_attacker_exec(b, f, r, 1, -2, by, knight)
        || offset_attacker_exec(b, f, r, -1, -2, by, knight) || offset_attacker_exec(b, f, r, -2, -1, by, knight)
        || offset_attacker_exec(b, f, r, -2, 1, by, knight) || offset_attacker_exec(b, f, r, -1, 2, by, knight)
        || ray_attacked_exec(b, f, r, 1, 0, by, true) || ray_attacked_exec(b, f, r, -1, 0, by, true)
        || ray_attacked_exec(b, f, r, 0, 1, by, true) || ray_attacked_exec(b, f, r, 0, -1, by, true)
        || ray_attacked_exec(b, f, r, 1, 1, by, true) || ray_attacked_exec(b, f, r, 1, -1, by, true)
        || ray_attacked_exec(b, f, r, -1, 1, by, true) || ray_attacked_exec(b, f, r, -1, -1, by, true) {
        return true;
    }
    proof {
        lemma_no_attacker(b@, f as int, r as int, by);
    }
    false
}

/// Completeness of `is_attacked_exec`: every attacker is found by one of its probes.
proof fn lemma_no_attacker(b: Board, f: int, r: int, by: Color)
    requires
        on_board(f, r),
        !(on_board(f - 1, r - forward(by)) && at(b, f - 1, r - forward(by)) == Some(
            Piece { color: by, kind: PieceKind::Pawn },
        )),
        !(on_board(f + 1, r - forward(by)) && at(b, f + 1, r - forward(by)) == Some(
            Piece { color: by, kind: PieceKind::Pawn },
        )),
        forall|df: int, dr: int|
            #![trigger at(b, f + df, r + dr)]
            ((abs(df) == 1 && abs(dr) == 2) || (abs(df) == 2 && abs(dr) == 1)) ==> !(on_board(
                f + df,
                r + dr,
            ) && at(b, f + df, r + dr) == Some(Piece { color: by, kind: PieceKind::Knight })),
        forall|df: int, dr: int|
            #![trigger at(b, f + df, r + dr)]
            distance(df, dr) == 1 ==> !(on_board(f + df, r + dr) && at(b, f + df, r + dr) == Some(
                Piece { color: by, kind: PieceKind::King },
            )),
        forall|df: int, dr: int, k: int|
            #![trigger slider_attacker_at(b, step(f, df, k), step(r, dr, k), f, r, by)]
            unit_dir(df, dr) && k >= 1 && on_board(step(f, df, k), step(r, dr, k))
                ==> !slider_attacker_at(b, step(f, df, k), step(r, dr, k), f, r, by),
    ensures
        !is_attacked(b, f, r, by),
{
    assert forall|f1: int, r1: int| on_board(f1, r1) implies !#[trigger] attacker_at(
        b,
        f1,
        r1,
        f,
        r,
        by,
    ) by {
        if attacker_at(b, f1, r1, f, r, by) {
            let p = at(b, f1, r1)->Some_0;
            let (df, dr) = (f1 - f, r1 - r);
            assert(at(b, f + df, r + dr) == at(b, f1, r1));
            match p.kind {
                PieceKind::Pawn => {
                    assert(p == Piece { color: by, kind: PieceKind::Pawn });
                },
                PieceKind::Knight => {
                    assert(p == Piece { color: by, kind: PieceKind::Knight });
                },
                PieceKind::King => {
                    assert(p == Piece { color: by, kind: PieceKind::King });
                },
                _ => {
                    let sf: int = if df > 0 { 1 } else if df < 0 { -1 } else { 0 };
                    let sr: int = if dr > 0 { 1 } else if dr < 0 { -1 } else { 0 };
                    let k = distance(df, dr);
                    assert(step(f, sf, k) == f1 && step(r, sr, k) == r1);
                    assert(slider_attacker_at(b, step(f, sf, k), step(r, sr, k), f, r, by));
                },
            }
        }
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
