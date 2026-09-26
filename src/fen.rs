//! FEN / UCI text conversion. Plain (unverified) Rust: this is I/O glue only.
use crate::position::Position;
use crate::types::*;

pub fn parse_square(s: &str) -> Option<Square> {
    let b = s.as_bytes();
    if b.len() != 2 || !(b'a'..=b'h').contains(&b[0]) || !(b'1'..=b'8').contains(&b[1]) {
        return None;
    }
    Some(Square { file: b[0] - b'a', rank: b[1] - b'1' })
}

pub fn square_to_string(s: Square) -> String {
    format!("{}{}", (b'a' + s.file) as char, (b'1' + s.rank) as char)
}

pub fn move_to_uci(m: Move) -> String {
    let promo = match m.promotion {
        None => "",
        Some(PieceKind::Knight) => "n",
        Some(PieceKind::Bishop) => "b",
        Some(PieceKind::Rook) => "r",
        Some(PieceKind::Queen) => "q",
        Some(PieceKind::Pawn) => "p",
        Some(PieceKind::King) => "k",
    };
    format!("{}{}{}", square_to_string(m.from), square_to_string(m.to), promo)
}

pub fn parse_uci_move(s: &str) -> Option<Move> {
    if s.len() != 4 && s.len() != 5 {
        return None;
    }
    let from = parse_square(s.get(0..2)?)?;
    let to = parse_square(s.get(2..4)?)?;
    let promotion = match s.get(4..5) {
        None => None,
        Some("n") => Some(PieceKind::Knight),
        Some("b") => Some(PieceKind::Bishop),
        Some("r") => Some(PieceKind::Rook),
        Some("q") => Some(PieceKind::Queen),
        Some(_) => return None,
    };
    Some(Move { from, to, promotion })
}

fn piece_from_char(c: char) -> Option<Piece> {
    let color = if c.is_ascii_uppercase() { Color::White } else { Color::Black };
    let kind = match c.to_ascii_lowercase() {
        'p' => PieceKind::Pawn,
        'n' => PieceKind::Knight,
        'b' => PieceKind::Bishop,
        'r' => PieceKind::Rook,
        'q' => PieceKind::Queen,
        'k' => PieceKind::King,
        _ => return None,
    };
    Some(Piece { color, kind })
}

fn piece_to_char(p: Piece) -> char {
    let c = match p.kind {
        PieceKind::Pawn => 'p',
        PieceKind::Knight => 'n',
        PieceKind::Bishop => 'b',
        PieceKind::Rook => 'r',
        PieceKind::Queen => 'q',
        PieceKind::King => 'k',
    };
    if p.color == Color::White { c.to_ascii_uppercase() } else { c }
}

/// Parse a FEN string. Only syntax is checked, not that the position is well formed.
pub fn parse_fen(fen: &str) -> Result<Position, String> {
    let fields: Vec<&str> = fen.split_whitespace().collect();
    if fields.len() < 4 {
        return Err(format!("FEN needs at least 4 fields: {fen}"));
    }
    let mut board = [None; 64];
    let ranks: Vec<&str> = fields[0].split('/').collect();
    if ranks.len() != 8 {
        return Err("FEN board must have 8 ranks".into());
    }
    for (i, row) in ranks.iter().enumerate() {
        let rank = 7 - i;
        let mut file = 0usize;
        for c in row.chars() {
            if let Some(d) = c.to_digit(10) {
                file += d as usize;
            } else {
                let p = piece_from_char(c).ok_or(format!("bad piece '{c}'"))?;
                if file >= 8 {
                    return Err("rank too long".into());
                }
                board[rank * 8 + file] = Some(p);
                file += 1;
            }
        }
        if file != 8 {
            return Err(format!("rank {} has {} files", rank + 1, file));
        }
    }
    let turn = match fields[1] {
        "w" => Color::White,
        "b" => Color::Black,
        t => return Err(format!("bad side to move '{t}'")),
    };
    let c = fields[2];
    if c != "-" && !c.chars().all(|x| "KQkq".contains(x)) {
        return Err(format!("bad castling field '{c}'"));
    }
    let castling = CastlingRights {
        white_kingside: c.contains('K'),
        white_queenside: c.contains('Q'),
        black_kingside: c.contains('k'),
        black_queenside: c.contains('q'),
    };
    let ep = match fields[3] {
        "-" => None,
        s => Some(parse_square(s).ok_or(format!("bad ep square '{s}'"))?),
    };
    let halfmove_clock = fields.get(4).map_or(Ok(0), |s| s.parse()).map_err(|e| format!("{e}"))?;
    let fullmove_number = fields.get(5).map_or(Ok(1), |s| s.parse()).map_err(|e| format!("{e}"))?;
    Ok(Position { board, turn, castling, ep, halfmove_clock, fullmove_number })
}

pub fn to_fen(pos: &Position) -> String {
    let mut s = String::new();
    for rank in (0..8).rev() {
        let mut empty = 0;
        for file in 0..8 {
            match pos.board[rank * 8 + file] {
                None => empty += 1,
                Some(p) => {
                    if empty > 0 {
                        s.push_str(&empty.to_string());
                        empty = 0;
                    }
                    s.push(piece_to_char(p));
                }
            }
        }
        if empty > 0 {
            s.push_str(&empty.to_string());
        }
        if rank > 0 {
            s.push('/');
        }
    }
    s.push(' ');
    s.push(if pos.turn == Color::White { 'w' } else { 'b' });
    s.push(' ');
    let cr = pos.castling;
    let mut c = String::new();
    if cr.white_kingside {
        c.push('K');
    }
    if cr.white_queenside {
        c.push('Q');
    }
    if cr.black_kingside {
        c.push('k');
    }
    if cr.black_queenside {
        c.push('q');
    }
    s.push_str(if c.is_empty() { "-" } else { &c });
    s.push(' ');
    s.push_str(&pos.ep.map_or("-".to_string(), square_to_string));
    s.push_str(&format!(" {} {}", pos.halfmove_clock, pos.fullmove_number));
    s
}
