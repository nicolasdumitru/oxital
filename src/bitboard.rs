// Copyright (C) 2025 Nicolas Dumitru
// SPDX-License-Identifier: GPL-3.0-or-later

use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not};

#[derive(Clone, Copy)]
pub struct Bitboard {
    bits: u64,
}

impl Bitboard {
    #[inline]
    pub fn new(bits: u64) -> Self {
        Self { bits }
    }

    // Little-Endian Rank-File Mapping (LERF)
    #[inline]
    fn square_to_index(rank: u8, file: u8) -> u8 {
        (rank << 3) + file
    }

    // Contract: This function expects an index in the [0, 63] range and returns the
    // value of the indexed bit as a boolean value.
    #[inline]
    pub fn test(&self, index: u8) -> bool {
        debug_assert!(index < 64);
        (self.bits & (1 << index)) != 0
    }

    // Contract: This function expects a valid rank and a valid file. Ranks ranging
    // from a to h map to integers from 0 to 7 respectively. Thus, both the
    // rank and the file are expected to be in the range [0, 7].
    #[inline]
    pub fn test_square(&self, rank: u8, file: u8) -> bool {
        self.test(Self::square_to_index(rank, file))
    }
}

impl BitAnd for Bitboard {
    type Output = Bitboard;

    #[inline]
    fn bitand(self, rhs: Self) -> Self::Output {
        Self::new(self.bits & rhs.bits)
    }
}

impl BitAndAssign for Bitboard {
    #[inline]
    fn bitand_assign(&mut self, rhs: Self) {
        self.bits &= rhs.bits;
    }
}

impl BitOr for Bitboard {
    type Output = Bitboard;

    #[inline]
    fn bitor(self, rhs: Self) -> Self::Output {
        Self::new(self.bits | rhs.bits)
    }
}

impl BitOrAssign for Bitboard {
    #[inline]
    fn bitor_assign(&mut self, rhs: Self) {
        self.bits |= rhs.bits;
    }
}

impl BitXor for Bitboard {
    type Output = Bitboard;

    #[inline]
    fn bitxor(self, rhs: Self) -> Self::Output {
        Self::new(self.bits ^ rhs.bits)
    }
}

impl BitXorAssign for Bitboard {
    #[inline]
    fn bitxor_assign(&mut self, rhs: Self) {
        self.bits ^= rhs.bits
    }
}

impl Not for Bitboard {
    type Output = Bitboard;

    #[inline]
    fn not(self) -> Self::Output {
        Self::new(!self.bits)
    }
}
