// Copyright (C) 2025 Nicolas Dumitru
// SPDX-License-Identifier: GPL-3.0-or-later

use crate::{bitboard::Bitboard, types::Square};

pub struct Board {
    ours: Bitboard,        // All of our pieces
    theirs: Bitboard,      // All of the opponent's pieces
    orthogonals: Bitboard, // All orthogonal sliding pieces (queens and rooks)
    diagonals: Bitboard,   // All diagonal sliding pieces (queens and bishops)
    pawns: Bitboard,       // All pawns
    our_king: Square,
    their_king: Square,
}

impl Board {
    #[inline]
    pub fn ours(&self) -> Bitboard {
        self.ours
    }
    #[inline]
    pub fn theirs(&self) -> Bitboard {
        self.theirs
    }
    #[inline]
    pub fn pawns(&self) -> Bitboard {
        self.pawns
    }
    #[inline]
    pub fn queens(&self) -> Bitboard {
        self.orthogonals & self.diagonals
    }
    #[inline]
    pub fn kings(&self) -> Bitboard {
        Bitboard::from(self.our_king) | Bitboard::from(self.their_king)
    }
}
