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
    pub fn kings(&self) -> Bitboard {
        Bitboard::from(self.our_king) | Bitboard::from(self.their_king)
    }
    #[inline]
    pub fn queens(&self) -> Bitboard {
        self.orthogonals & self.diagonals
    }
    #[inline]
    pub fn rooks(&self) -> Bitboard {
        self.orthogonals - self.diagonals
    }
    #[inline]
    pub fn bishops(&self) -> Bitboard {
        self.diagonals - self.orthogonals
    }
    #[inline]
    pub fn knights(&self) -> Bitboard {
        self.ours
            | self.theirs
                - self.orthogonals
                - self.diagonals
                - self.pawns
                - self.our_king
                - self.their_king
    }
    #[inline]
    pub fn pawns(&self) -> Bitboard {
        self.pawns
    }
}
