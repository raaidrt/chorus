//! A chess engine verified with Verus.
//!
//! * [`spec`] — the formal rules of chess (trusted; review this).
//! * [`position`], [`attacks`], [`movegen`], [`game`] — executable code proven to match [`spec`].
//! * [`fen`] — unverified text I/O (FEN / UCI move notation).
pub mod types;
pub mod spec;
pub mod position;
pub mod attacks;
pub mod movegen;
pub mod game;
pub mod fen;
