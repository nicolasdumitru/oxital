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

    // Converts a (rank, file) coordinate pair to a square index using
    // Little-Endian Rank-File (LERF) mapping.
    // Returns index in range [0, 63] via 8 * rank + file.
    // Expects rank and file in the range [0, 7], where rank is the row (0 =
    // rank 1) and file is the column (0 = file a).
    // Panics in debug mode if rank or file is out of bounds.
    #[inline]
    fn square_to_index(rank: u8, file: u8) -> u8 {
        debug_assert!(rank < 8 && file < 8);
        (rank << 3) | file // <=> 8 * rank + file for rank, file in [0, 7]
    }

    // Returns true if the bit at the given square's index is
    // set.
    // Expects index in range [0, 63].
    // Panics in debug mode if index is out of bounds.
    #[inline]
    pub fn test(&self, index: u8) -> bool {
        debug_assert!(index < 64);
        (self.bits & (1 << index)) != 0
    }

    // Returns true if the bit at the given (rank, file) coordinates is set.
    // Expects rank and file in range [0, 7], where rank is the row and file is
    // the column. Internally maps the square to its index using.
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_bitboard() {
        let bb = Bitboard::new(0);
        assert_eq!(bb.bits, 0);

        let bb = Bitboard::new(u64::MAX);
        assert_eq!(bb.bits, u64::MAX);

        let bb = Bitboard::new(0x123456789ABCDEF0);
        assert_eq!(bb.bits, 0x123456789ABCDEF0);
    }

    #[test]
    fn test_square_to_index() {
        // Test corner squares
        assert_eq!(Bitboard::square_to_index(0, 0), 0); // a1
        assert_eq!(Bitboard::square_to_index(0, 7), 7); // h1
        assert_eq!(Bitboard::square_to_index(7, 0), 56); // a8
        assert_eq!(Bitboard::square_to_index(7, 7), 63); // h8

        // Test some middle squares
        assert_eq!(Bitboard::square_to_index(3, 4), 28); // e4
        assert_eq!(Bitboard::square_to_index(4, 3), 35); // d5

        // Test first rank
        for file in 0..8 {
            assert_eq!(Bitboard::square_to_index(0, file), file);
        }

        // Test first file
        for rank in 0..8 {
            assert_eq!(Bitboard::square_to_index(rank, 0), rank * 8);
        }
    }

    #[test]
    fn test_bit_testing() {
        // Test empty bitboard
        let empty = Bitboard::new(0);
        for i in 0..64 {
            assert!(!empty.test(i));
        }

        // Test full bitboard
        let full = Bitboard::new(u64::MAX);
        for i in 0..64 {
            assert!(full.test(i));
        }

        // Test single bit
        let single = Bitboard::new(1);
        assert!(single.test(0));
        for i in 1..64 {
            assert!(!single.test(i));
        }

        // Test highest bit
        let high = Bitboard::new(1u64 << 63);
        assert!(high.test(63));
        for i in 0..63 {
            assert!(!high.test(i));
        }

        // Test alternating pattern
        let alternating = Bitboard::new(0xAAAAAAAAAAAAAAAA);
        for i in 0..64 {
            if i % 2 == 1 {
                assert!(alternating.test(i));
            } else {
                assert!(!alternating.test(i));
            }
        }
    }

    #[test]
    fn test_square_testing() {
        // Test empty bitboard
        let empty = Bitboard::new(0);
        for rank in 0..8 {
            for file in 0..8 {
                assert!(!empty.test_square(rank, file));
            }
        }

        // Test single square
        let single = Bitboard::new(1u64 << 28); // e4
        assert!(single.test_square(3, 4));

        // Test that other squares are empty
        for rank in 0..8 {
            for file in 0..8 {
                if rank != 3 || file != 4 {
                    assert!(!single.test_square(rank, file));
                }
            }
        }

        // Test corner squares
        let corners = Bitboard::new((1u64 << 0) | (1u64 << 7) | (1u64 << 56) | (1u64 << 63));
        assert!(corners.test_square(0, 0)); // a1
        assert!(corners.test_square(0, 7)); // h1
        assert!(corners.test_square(7, 0)); // a8
        assert!(corners.test_square(7, 7)); // h8

        // Test that middle squares are empty
        assert!(!corners.test_square(3, 3));
        assert!(!corners.test_square(4, 4));
    }

    #[test]
    fn test_bitwise_and() {
        let bb1 = Bitboard::new(0xFF00FF00FF00FF00);
        let bb2 = Bitboard::new(0xF0F0F0F0F0F0F0F0);
        let result = bb1 & bb2;
        assert_eq!(result.bits, 0xF000F000F000F000);

        // Test with zero
        let zero = Bitboard::new(0);
        let result = bb1 & zero;
        assert_eq!(result.bits, 0);

        // Test with self
        let result = bb1 & bb1;
        assert_eq!(result.bits, bb1.bits);
    }

    #[test]
    fn test_bitwise_and_assign() {
        let mut bb1 = Bitboard::new(0xFF00FF00FF00FF00);
        let bb2 = Bitboard::new(0xF0F0F0F0F0F0F0F0);
        bb1 &= bb2;
        assert_eq!(bb1.bits, 0xF000F000F000F000);

        // Test with zero
        let mut bb = Bitboard::new(0xFF00FF00FF00FF00);
        bb &= Bitboard::new(0);
        assert_eq!(bb.bits, 0);
    }

    #[test]
    fn test_bitwise_or() {
        let bb1 = Bitboard::new(0xFF00FF00FF00FF00);
        let bb2 = Bitboard::new(0x00FF00FF00FF00FF);
        let result = bb1 | bb2;
        assert_eq!(result.bits, u64::MAX);

        // Test with zero
        let zero = Bitboard::new(0);
        let result = bb1 | zero;
        assert_eq!(result.bits, bb1.bits);

        // Test with self
        let result = bb1 | bb1;
        assert_eq!(result.bits, bb1.bits);
    }

    #[test]
    fn test_bitwise_or_assign() {
        let mut bb1 = Bitboard::new(0xFF00FF00FF00FF00);
        let bb2 = Bitboard::new(0x00FF00FF00FF00FF);
        bb1 |= bb2;
        assert_eq!(bb1.bits, u64::MAX);

        // Test with zero
        let mut bb = Bitboard::new(0xFF00FF00FF00FF00);
        let original = bb.bits;
        bb |= Bitboard::new(0);
        assert_eq!(bb.bits, original);
    }

    #[test]
    fn test_bitwise_xor() {
        let bb1 = Bitboard::new(0xFF00FF00FF00FF00);
        let bb2 = Bitboard::new(0xF0F0F0F0F0F0F0F0);
        let result = bb1 ^ bb2;
        assert_eq!(result.bits, 0x0FF00FF00FF00FF0);

        // Test with zero
        let zero = Bitboard::new(0);
        let result = bb1 ^ zero;
        assert_eq!(result.bits, bb1.bits);

        // Test with self (should be zero)
        let result = bb1 ^ bb1;
        assert_eq!(result.bits, 0);
    }

    #[test]
    fn test_bitwise_xor_assign() {
        let mut bb1 = Bitboard::new(0xFF00FF00FF00FF00);
        let bb2 = Bitboard::new(0xF0F0F0F0F0F0F0F0);
        bb1 ^= bb2;
        assert_eq!(bb1.bits, 0x0FF00FF00FF00FF0);

        // Test XOR with self (should result in zero)
        let mut bb = Bitboard::new(0xFF00FF00FF00FF00);
        let original = bb;
        bb ^= original;
        assert_eq!(bb.bits, 0);
    }

    #[test]
    fn test_bitwise_not() {
        let bb = Bitboard::new(0);
        let result = !bb;
        assert_eq!(result.bits, u64::MAX);

        let bb = Bitboard::new(u64::MAX);
        let result = !bb;
        assert_eq!(result.bits, 0);

        let bb = Bitboard::new(0xFF00FF00FF00FF00);
        let result = !bb;
        assert_eq!(result.bits, 0x00FF00FF00FF00FF);

        // Test double negation
        let bb = Bitboard::new(0x123456789ABCDEF0);
        let result = !!bb;
        assert_eq!(result.bits, bb.bits);
    }

    #[test]
    fn test_copy_and_clone() {
        let bb1 = Bitboard::new(0x123456789ABCDEF0);
        let bb2 = bb1; // Copy
        let bb3 = bb1.clone(); // Clone

        assert_eq!(bb1.bits, bb2.bits);
        assert_eq!(bb1.bits, bb3.bits);
        assert_eq!(bb2.bits, bb3.bits);
    }

    #[test]
    fn test_chess_squares() {
        // Test some well-known chess squares
        let mut board = Bitboard::new(0);

        // Set e4 (rank 3, file 4)
        board |= Bitboard::new(1u64 << Bitboard::square_to_index(3, 4));
        assert!(board.test_square(3, 4));

        // Set d5 (rank 4, file 3)
        board |= Bitboard::new(1u64 << Bitboard::square_to_index(4, 3));
        assert!(board.test_square(4, 3));

        // Verify both squares are set
        assert!(board.test_square(3, 4));
        assert!(board.test_square(4, 3));

        // Verify other squares are not set
        assert!(!board.test_square(0, 0));
        assert!(!board.test_square(7, 7));
    }

    #[test]
    fn test_bitboard_operations_chain() {
        let bb1 = Bitboard::new(0xF0F0F0F0F0F0F0F0);
        let bb2 = Bitboard::new(0xFF00FF00FF00FF00);
        let bb3 = Bitboard::new(0x0F0F0F0F0F0F0F0F);

        // Chain operations
        let result = (bb1 | bb2) & !bb3;
        let expected = (bb1.bits | bb2.bits) & !bb3.bits;
        assert_eq!(result.bits, expected);

        // More complex chain
        let result = (bb1 ^ bb2) | (bb2 & bb3);
        let expected = (bb1.bits ^ bb2.bits) | (bb2.bits & bb3.bits);
        assert_eq!(result.bits, expected);
    }

    #[test]
    fn test_edge_cases() {
        // Test boundary conditions for test() method
        let bb = Bitboard::new(0x8000000000000001);
        assert!(bb.test(0)); // First bit
        assert!(bb.test(63)); // Last bit
        for i in 1..63 {
            assert!(!bb.test(i));
        }

        // Test boundary conditions for test_square() method
        let bb = Bitboard::new(0x8100000000000081);
        assert!(bb.test_square(0, 0)); // a1
        assert!(bb.test_square(0, 7)); // h1
        assert!(bb.test_square(7, 0)); // a8
        assert!(bb.test_square(7, 7)); // h8
    }
}
