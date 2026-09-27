//! Bitboards: sets of squares as a `u64`, with bit `rank * 8 + file` for each square.
#[cfg(verus_only)]
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// Bit `j` of `x`.
pub open spec fn bit(x: u64, j: int) -> bool {
    (x >> (j as u64)) & 1u64 == 1u64
}

pub proof fn lemma_bit_zero(j: u64)
    requires
        j < 64,
    ensures
        !bit(0u64, j as int),
{
    assert((0u64 >> j) & 1u64 == 0u64) by (bit_vector);
}

pub proof fn lemma_bit_or(x: u64, i: u64, j: u64)
    requires
        i < 64,
        j < 64,
    ensures
        bit(x | (1u64 << i), j as int) == (bit(x, j as int) || i == j),
{
    assert(((x | (1u64 << i)) >> j) & 1u64 == 1u64 <==> ((x >> j) & 1u64 == 1u64 || i == j))
        by (bit_vector)
        requires
            i < 64,
            j < 64,
    ;
}

pub proof fn lemma_bit_xor(x: u64, i: u64, j: u64)
    requires
        i < 64,
        j < 64,
    ensures
        bit(x ^ (1u64 << i), j as int) == (bit(x, j as int) != (i == j)),
{
    assert(((x ^ (1u64 << i)) >> j) & 1u64 == 1u64 <==> (((x >> j) & 1u64 == 1u64) != (i == j)))
        by (bit_vector)
        requires
            i < 64,
            j < 64,
    ;
}

/// `x` with bit `i` set.
pub fn with_index(x: u64, i: i32) -> (y: u64)
    requires
        0 <= i < 64,
    ensures
        forall|j: int| 0 <= j < 64 ==> #[trigger] bit(y, j) == (bit(x, j) || j == i),
{
    let i = i as u64;
    proof {
        assert forall|j: int| 0 <= j < 64 implies #[trigger] bit(x | (1u64 << i), j) == (bit(x, j) || j == i) by {
            lemma_bit_or(x, i, j as u64);
        }
    }
    x | (1u64 << i)
}

/// `x` with the bit of (f, r) set.
pub fn with_bit(x: u64, f: i32, r: i32) -> (y: u64)
    requires
        on_board(f as int, r as int),
    ensures
        forall|j: int| 0 <= j < 64 ==> #[trigger] bit(y, j) == (bit(x, j) || j == index_of(f as int, r as int)),
{
    let i = (r * 8 + f) as u64;
    proof {
        assert forall|j: int| 0 <= j < 64 implies #[trigger] bit(x | (1u64 << i), j) == (bit(x, j) || j
            == index_of(f as int, r as int)) by {
            lemma_bit_or(x, i, j as u64);
        }
    }
    x | (1u64 << i)
}

} // verus!
