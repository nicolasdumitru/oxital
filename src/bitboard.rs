// Copyright (C) 2025 Nicolas Dumitru
// SPDX-License-Identifier: GPL-3.0-or-later

use core::convert::From;
use std::cmp::PartialEq;
use std::ops::Not;
use std::ops::{BitAnd, BitAndAssign};
use std::ops::{BitOr, BitOrAssign};
use std::ops::{BitXor, BitXorAssign};
use std::ops::{Shl, ShlAssign};
use std::ops::{Shr, ShrAssign};

#[derive(Clone, Copy, Debug)]
pub struct Bitboard {
    bits: u64,
}

impl Bitboard {
    /// Converts a (rank, file) coordinate pair to a square index using
    /// Little-Endian Rank-File (LERF) mapping.
    /// Returns index in range [0, 63] via 8 * rank + file.
    /// Expects rank and file in the range [0, 7], where rank is the row (0 =
    /// rank 1) and file is the column (0 = file a).
    /// Panics in debug mode if rank or file is out of bounds.
    #[inline]
    fn square_to_index(rank: u8, file: u8) -> u8 {
        debug_assert!(rank < 8 && file < 8);
        (rank << 3) | file // <=> 8 * rank + file for rank, file in [0, 7]
    }

    /// Returns true if the bit at the given square's index is
    /// set.
    /// Expects index in range [0, 63].
    /// Panics in debug mode if index is out of bounds.
    #[inline]
    pub fn test(&self, index: u8) -> bool {
        debug_assert!(index < 64);
        (self.bits & (1 << index)) != 0
    }

    /// Returns true if the bit at the given (rank, file) coordinates is set.
    /// Expects rank and file in range [0, 7], where rank is the row and file is
    /// the column. Internally maps the square to its index using.
    #[inline]
    pub fn test_square(&self, rank: u8, file: u8) -> bool {
        self.test(Self::square_to_index(rank, file))
    }
}

impl From<u64> for Bitboard {
    /// Creates a Bitboard from a u64.
    #[inline]
    fn from(bits: u64) -> Self {
        Self { bits }
    }
}

impl From<&str> for Bitboard {
    /// Creates a Bitboard from a pattern string.
    ///
    /// This constructor provides a flexible way to create bitboards from string literals
    /// for better visualization of constants. The encoding is:
    /// - '0' or '.' represents an empty square (unset bit)
    /// - '1' or 'X' represents an occupied square (set bit)
    /// - Newlines are ignored and only used for visual delimitation of ranks
    /// - Any other characters will cause a panic at runtime
    ///
    /// The pattern should represent exactly 64 squares, read from rank 8 to rank 1
    /// (top to bottom), and from file a to file h (left to right).
    ///
    /// # Panics
    ///
    /// Panics if the pattern contains invalid characters or doesn't represent exactly 64 squares.
    ///
    /// # Example
    /// ```
    /// # use oxital::bitboard::Bitboard;
    /// let board = Bitboard::from("
    ///     ........
    ///     ........
    ///     ........
    ///     ...1....
    ///     ........
    ///     ........
    ///     ......X.
    ///     ........
    /// ");
    ///
    /// // Or more compactly:
    /// let board = Bitboard::from("0000000000000000000000000001000000000000000000000000000000000000");
    /// ```
    fn from(pattern: &str) -> Self {
        // Filter out newlines and whitespace for processing
        let cleaned: String = pattern.chars().filter(|&ch| !ch.is_whitespace()).collect();

        if cleaned.len() != 64 {
            panic!("Pattern must contain exactly 64 squares, got {}", cleaned.len());
        }

        let mut bits: u64 = 0;

        for (i, ch) in cleaned.chars().enumerate() {
            match ch {
                '0' | '.' => {} // Empty square - bit remains unset
                '1' | 'X' => {
                    // Occupied square - set the bit
                    // i = 0 corresponds to rank 7, file 0 (a8)
                    // i = 63 corresponds to rank 0, file 7 (h1)
                    let rank = 7 - (i / 8) as u8;
                    let file = (i % 8) as u8;
                    let square_index = Self::square_to_index(rank, file);
                    bits |= 1u64 << square_index;
                }
                _ => panic!(
                    "Invalid character '{}' in pattern. Only '0', '.', '1', and 'X' are allowed.",
                    ch
                ),
            }
        }

        Self { bits }
    }
}

impl PartialEq for Bitboard {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.bits == other.bits
    }

    #[inline]
    fn ne(&self, other: &Self) -> bool {
        self.bits != other.bits
    }
}

impl Not for Bitboard {
    type Output = Bitboard;

    #[inline]
    fn not(self) -> Self::Output {
        Self::from(!self.bits)
    }
}

impl BitAnd for Bitboard {
    type Output = Bitboard;

    #[inline]
    fn bitand(self, rhs: Self) -> Self::Output {
        Self::from(self.bits & rhs.bits)
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
        Self::from(self.bits | rhs.bits)
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
        Self::from(self.bits ^ rhs.bits)
    }
}

impl BitXorAssign for Bitboard {
    #[inline]
    fn bitxor_assign(&mut self, rhs: Self) {
        self.bits ^= rhs.bits
    }
}

impl<T> Shl<T> for Bitboard
where
    T: Into<u8>,
{
    type Output = Bitboard;

    #[inline]
    fn shl(self, rhs: T) -> Self::Output {
        Self::from(self.bits << rhs.into())
    }
}

impl<T> ShlAssign<T> for Bitboard
where
    T: Into<u8>,
{
    #[inline]
    fn shl_assign(&mut self, rhs: T) {
        self.bits <<= rhs.into()
    }
}

impl<T> Shr<T> for Bitboard
where
    T: Into<u8>,
{
    type Output = Bitboard;

    #[inline]
    fn shr(self, rhs: T) -> Self::Output {
        Self::from(self.bits >> rhs.into())
    }
}

impl<T> ShrAssign<T> for Bitboard
where
    T: Into<u8>,
{
    #[inline]
    fn shr_assign(&mut self, rhs: T) {
        self.bits >>= rhs.into()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_bitboard() {
        let bb = Bitboard::from(0);
        assert!(bb == Bitboard::from(0));

        let bb = Bitboard::from(u64::MAX);
        assert!(bb == Bitboard::from(u64::MAX));

        let bb = Bitboard::from(0x123456789ABCDEF0);
        assert!(bb == Bitboard::from(0x123456789ABCDEF0));
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
        let empty = Bitboard::from(0);
        for i in 0..64 {
            assert!(!empty.test(i));
        }

        // Test full bitboard
        let full = Bitboard::from(u64::MAX);
        for i in 0..64 {
            assert!(full.test(i));
        }

        // Test single bit
        let single = Bitboard::from(1);
        assert!(single.test(0));
        for i in 1..64 {
            assert!(!single.test(i));
        }

        // Test highest bit
        let high = Bitboard::from(1u64 << 63);
        assert!(high.test(63));
        for i in 0..63 {
            assert!(!high.test(i));
        }

        // Test alternating pattern
        let alternating = Bitboard::from(0xAAAAAAAAAAAAAAAA);
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
        let empty = Bitboard::from(0);
        for rank in 0..8 {
            for file in 0..8 {
                assert!(!empty.test_square(rank, file));
            }
        }

        // Test single square
        let single = Bitboard::from(1u64 << 28); // e4
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
        let corners = Bitboard::from((1u64 << 0) | (1u64 << 7) | (1u64 << 56) | (1u64 << 63));
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
        let bb1 = Bitboard::from(0xFF00FF00FF00FF00);
        let bb2 = Bitboard::from(0xF0F0F0F0F0F0F0F0);
        let result = bb1 & bb2;
        assert_eq!(result, Bitboard::from(0xF000F000F000F000));

        // Test with zero
        let zero = Bitboard::from(0);
        let result = bb1 & zero;
        assert_eq!(result, Bitboard::from(0));

        // Test with self
        let result = bb1 & bb1;
        assert_eq!(result, bb1);
    }

    #[test]
    fn test_bitwise_and_assign() {
        let mut bb1 = Bitboard::from(0xFF00FF00FF00FF00);
        let bb2 = Bitboard::from(0xF0F0F0F0F0F0F0F0);
        bb1 &= bb2;
        assert_eq!(bb1, Bitboard::from(0xF000F000F000F000));

        // Test with zero
        let mut bb = Bitboard::from(0xFF00FF00FF00FF00);
        bb &= Bitboard::from(0);
        assert_eq!(bb, Bitboard::from(0));
    }

    #[test]
    fn test_bitwise_or() {
        let bb1 = Bitboard::from(0xFF00FF00FF00FF00);
        let bb2 = Bitboard::from(0x00FF00FF00FF00FF);
        let result = bb1 | bb2;
        assert_eq!(result, Bitboard::from(u64::MAX));

        // Test with zero
        let zero = Bitboard::from(0);
        let result = bb1 | zero;
        assert_eq!(result, bb1);

        // Test with self
        let result = bb1 | bb1;
        assert_eq!(result, bb1);
    }

    #[test]
    fn test_bitwise_or_assign() {
        let mut bb1 = Bitboard::from(0xFF00FF00FF00FF00);
        let bb2 = Bitboard::from(0x00FF00FF00FF00FF);
        bb1 |= bb2;
        assert_eq!(bb1, Bitboard::from(u64::MAX));

        // Test with zero
        let mut bb = Bitboard::from(0xFF00FF00FF00FF00);
        let original = bb;
        bb |= Bitboard::from(0);
        assert_eq!(bb, original);
    }

    #[test]
    fn test_bitwise_xor() {
        let bb1 = Bitboard::from(0xFF00FF00FF00FF00);
        let bb2 = Bitboard::from(0xF0F0F0F0F0F0F0F0);
        let result = bb1 ^ bb2;
        assert_eq!(result, Bitboard::from(0x0FF00FF00FF00FF0));

        // Test with zero
        let zero = Bitboard::from(0);
        let result = bb1 ^ zero;
        assert_eq!(result.bits, bb1.bits);

        // Test with self (should be zero)
        let result = bb1 ^ bb1;
        assert_eq!(result.bits, 0);
    }

    #[test]
    fn test_bitwise_xor_assign() {
        let mut bb1 = Bitboard::from(0xFF00FF00FF00FF00);
        let bb2 = Bitboard::from(0xF0F0F0F0F0F0F0F0);
        bb1 ^= bb2;
        assert_eq!(bb1.bits, 0x0FF00FF00FF00FF0);

        // Test XOR with self (should result in zero)
        let mut bb = Bitboard::from(0xFF00FF00FF00FF00);
        let original = bb;
        bb ^= original;
        assert_eq!(bb.bits, 0);
    }

    #[test]
    fn test_bitwise_not() {
        let bb = Bitboard::from(0);
        let result = !bb;
        assert_eq!(result.bits, u64::MAX);

        let bb = Bitboard::from(u64::MAX);
        let result = !bb;
        assert_eq!(result.bits, 0);

        let bb = Bitboard::from(0xFF00FF00FF00FF00);
        let result = !bb;
        assert_eq!(result.bits, 0x00FF00FF00FF00FF);

        // Test double negation
        let bb = Bitboard::from(0x123456789ABCDEF0);
        let result = !!bb;
        assert_eq!(result.bits, bb.bits);
    }

    #[test]
    fn test_copy_and_clone() {
        let bb1 = Bitboard::from(0x123456789ABCDEF0);
        let bb2 = bb1; // Copy
        let bb3 = bb1.clone(); // Clone

        assert_eq!(bb1.bits, bb2.bits);
        assert_eq!(bb1.bits, bb3.bits);
        assert_eq!(bb2.bits, bb3.bits);
    }

    #[test]
    fn test_chess_squares() {
        // Test some well-known chess squares
        let mut board = Bitboard::from(0);

        // Set e4 (rank 3, file 4)
        board |= Bitboard::from(1u64 << Bitboard::square_to_index(3, 4));
        assert!(board.test_square(3, 4));

        // Set d5 (rank 4, file 3)
        board |= Bitboard::from(1u64 << Bitboard::square_to_index(4, 3));
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
        let bb1 = Bitboard::from(0xF0F0F0F0F0F0F0F0);
        let bb2 = Bitboard::from(0xFF00FF00FF00FF00);
        let bb3 = Bitboard::from(0x0F0F0F0F0F0F0F0F);

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
        let bb = Bitboard::from(0x8000000000000001);
        assert!(bb.test(0)); // First bit
        assert!(bb.test(63)); // Last bit
        for i in 1..63 {
            assert!(!bb.test(i));
        }

        // Test boundary conditions for test_square() method
        let bb = Bitboard::from(0x8100000000000081);
        assert!(bb.test_square(0, 0)); // a1
        assert!(bb.test_square(0, 7)); // h1
        assert!(bb.test_square(7, 0)); // a8
        assert!(bb.test_square(7, 7)); // h8
    }

    #[test]
    fn test_partial_eq() {
        let bb1 = Bitboard::from(0x123456789ABCDEF0);
        let bb2 = Bitboard::from(0x123456789ABCDEF0);
        let bb3 = Bitboard::from(0xFEDCBA9876543210);

        // Test equality
        assert_eq!(bb1, bb2);
        assert!(bb1 == bb2);

        // Test inequality
        assert_ne!(bb1, bb3);
        assert!(bb1 != bb3);

        // Test with zero
        let zero1 = Bitboard::from(0);
        let zero2 = Bitboard::from(0);
        assert_eq!(zero1, zero2);

        // Test with max
        let max1 = Bitboard::from(u64::MAX);
        let max2 = Bitboard::from(u64::MAX);
        assert_eq!(max1, max2);

        // Test reflexivity
        assert_eq!(bb1, bb1);
        assert!(!(bb1 != bb1));
    }

    #[test]
    fn test_left_shift() {
        let bb = Bitboard::from(0x0F0F0F0F0F0F0F0F);

        // Test shifting by different amounts
        let result1 = bb << 1u8;
        assert_eq!(result1.bits, 0x1E1E1E1E1E1E1E1E);

        let result4 = bb << 4u8;
        assert_eq!(result4.bits, 0xF0F0F0F0F0F0F0F0);

        let result8 = bb << 8u8;
        assert_eq!(result8.bits, 0x0F0F0F0F0F0F0F00);

        // Test with different integer types that can convert to u8
        let result_u8 = bb << 2u8;
        let result_bool = bb << true; // bool converts to u8 (true = 1)
        assert_eq!(result_u8.bits, (bb.bits << 2));
        assert_eq!(result_bool.bits, (bb.bits << 1));

        // Test shifting by zero
        let result0 = bb << 0u8;
        assert_eq!(result0.bits, bb.bits);

        // Test overflow behavior
        let high_bit = Bitboard::from(0x8000000000000000);
        let overflow = high_bit << 1u8;
        assert_eq!(overflow.bits, 0);

        // Test shifting with pattern
        let pattern = Bitboard::from(0x0000000000000001);
        let shifted = pattern << 63u8;
        assert_eq!(shifted.bits, 0x8000000000000000);
    }

    #[test]
    fn test_left_shift_assign() {
        let mut bb = Bitboard::from(0x0F0F0F0F0F0F0F0F);
        let original = bb.bits;

        // Test shifting by 1
        bb <<= 1u8;
        assert_eq!(bb.bits, 0x1E1E1E1E1E1E1E1E);

        // Reset and test shifting by 4
        bb = Bitboard::from(original);
        bb <<= 4u8;
        assert_eq!(bb.bits, 0xF0F0F0F0F0F0F0F0);

        // Test with different integer types that can convert to u8
        let mut bb1 = Bitboard::from(0x0F0F0F0F0F0F0F0F);
        let mut bb2 = Bitboard::from(0x0F0F0F0F0F0F0F0F);
        bb1 <<= 3u8;
        bb2 <<= false; // false converts to u8 (false = 0)
        assert_eq!(bb1.bits, 0x7878787878787878);
        assert_eq!(bb2.bits, 0x0F0F0F0F0F0F0F0F); // shifted by 0

        // Test shifting by zero
        let mut bb = Bitboard::from(0x123456789ABCDEF0);
        let original = bb.bits;
        bb <<= 0u8;
        assert_eq!(bb.bits, original);

        // Test chained assignment
        let mut bb = Bitboard::from(0x0000000000000001);
        bb <<= 1u8;
        bb <<= 1u8;
        bb <<= 1u8;
        assert_eq!(bb.bits, 0x0000000000000008);
    }

    #[test]
    fn test_right_shift() {
        let bb = Bitboard::from(0xF0F0F0F0F0F0F0F0);

        // Test shifting by different amounts
        let result1 = bb >> 1u8;
        assert_eq!(result1.bits, 0x7878787878787878);

        let result4 = bb >> 4u8;
        assert_eq!(result4.bits, 0x0F0F0F0F0F0F0F0F);

        let result8 = bb >> 8u8;
        assert_eq!(result8.bits, 0x00F0F0F0F0F0F0F0);

        // Test with different integer types that can convert to u8
        let result_u8 = bb >> 2u8;
        let result_bool = bb >> true; // bool converts to u8 (true = 1)
        assert_eq!(result_u8.bits, (bb.bits >> 2));
        assert_eq!(result_bool.bits, (bb.bits >> 1));

        // Test shifting by zero
        let result0 = bb >> 0u8;
        assert_eq!(result0.bits, bb.bits);

        // Test underflow behavior
        let low_bit = Bitboard::from(0x0000000000000001);
        let underflow = low_bit >> 1u8;
        assert_eq!(underflow.bits, 0);

        // Test shifting with pattern
        let pattern = Bitboard::from(0x8000000000000000);
        let shifted = pattern >> 63u8;
        assert_eq!(shifted.bits, 0x0000000000000001);

        // Test large shift (close to complete but not overflow)
        let large_shift = bb >> 63u8;
        assert_eq!(large_shift.bits, bb.bits >> 63);
    }

    #[test]
    fn test_right_shift_assign() {
        let mut bb = Bitboard::from(0xF0F0F0F0F0F0F0F0);
        let original = bb.bits;

        // Test shifting by 1
        bb >>= 1u8;
        assert_eq!(bb.bits, 0x7878787878787878);

        // Reset and test shifting by 4
        bb = Bitboard::from(original);
        bb >>= 4u8;
        assert_eq!(bb.bits, 0x0F0F0F0F0F0F0F0F);

        // Test with different integer types that can convert to u8
        let mut bb1 = Bitboard::from(0xF0F0F0F0F0F0F0F0);
        let mut bb2 = Bitboard::from(0xF0F0F0F0F0F0F0F0);
        bb1 >>= 3u8;
        bb2 >>= false; // false converts to u8 (false = 0)
        assert_eq!(bb1.bits, 0x1E1E1E1E1E1E1E1E);
        assert_eq!(bb2.bits, 0xF0F0F0F0F0F0F0F0); // shifted by 0

        // Test shifting by zero
        let mut bb = Bitboard::from(0x123456789ABCDEF0);
        let original = bb.bits;
        bb >>= 0u8;
        assert_eq!(bb.bits, original);

        // Test chained assignment
        let mut bb = Bitboard::from(0x8000000000000000);
        bb >>= 1u8;
        bb >>= 1u8;
        bb >>= 1u8;
        assert_eq!(bb.bits, 0x1000000000000000);

        // Test shifting to zero
        let mut bb = Bitboard::from(0x0000000000000001);
        bb >>= 1u8;
        assert_eq!(bb.bits, 0);
    }

    #[test]
    fn test_shift_symmetry() {
        let original = Bitboard::from(0x0000FF0000FF0000);

        // Test that left shift followed by right shift returns to original
        // (when no bits are lost)
        let shifted_left = original << 8u8;
        let back_to_original = shifted_left >> 8u8;
        assert_eq!(back_to_original.bits, original.bits);

        // Test the reverse
        let shifted_right = original >> 8u8;
        let back_to_original = shifted_right << 8u8;
        assert_eq!(back_to_original.bits, original.bits);

        // Test with assign operations
        let mut bb = original;
        bb <<= 4u8;
        bb >>= 4u8;
        assert_eq!(bb.bits, original.bits);
    }

    #[test]
    fn test_from_pattern_basic() {
        // Test empty board
        let empty = Bitboard::from(
            "
            ........
            ........
            ........
            ........
            ........
            ........
            ........
            ........
        ",
        );
        assert_eq!(empty.bits, 0);

        // Test single bit at a8 (rank 7, file 0)
        let a8 = Bitboard::from(
            "
            1.......
            ........
            ........
            ........
            ........
            ........
            ........
            ........
        ",
        );
        assert_eq!(a8.bits, 1u64 << 56);

        // Test single bit at h1 (rank 0, file 7)
        let h1 = Bitboard::from(
            "
            ........
            ........
            ........
            ........
            ........
            ........
            ........
            .......1
        ",
        );
        assert_eq!(h1.bits, 1u64 << 7);
    }

    #[test]
    fn test_from_pattern_characters() {
        // Test all valid empty characters
        let empty_dots =
            Bitboard::from("................................................................");
        let empty_zeros =
            Bitboard::from("0000000000000000000000000000000000000000000000000000000000000000");
        assert_eq!(empty_dots.bits, 0);
        assert_eq!(empty_zeros.bits, 0);

        // Test all valid occupied characters
        let pattern_ones = Bitboard::from(
            "
            1.......
            ........
            ........
            ........
            ........
            ........
            ........
            ........
        ",
        );
        let pattern_x = Bitboard::from(
            "
            X.......
            ........
            ........
            ........
            ........
            ........
            ........
            ........
        ",
        );
        assert_eq!(pattern_ones.bits, pattern_x.bits);
        assert_eq!(pattern_ones.bits, 1u64 << 56);
    }

    #[test]
    fn test_from_pattern_compact() {
        // Test without newlines - compact format
        let compact =
            Bitboard::from("1000000000000000000000000000000000000000000000000000000000000001");
        // Should have bits set at a8 (index 56) and h1 (index 7)
        assert_eq!(compact.bits, (1u64 << 56) | (1u64 << 7));
    }

    #[test]
    fn test_from_pattern_whitespace_ignored() {
        // Test that various whitespace is ignored
        let with_spaces = Bitboard::from(
            "
            1 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 1
        ",
        );
        let expected = (1u64 << 56) | (1u64 << 7);
        assert_eq!(with_spaces.bits, expected);
    }

    #[test]
    fn test_from_pattern_chess_positions() {
        // Test a more complex pattern - initial pawn structure
        let pawns = Bitboard::from(
            "
            ........
            11111111
            ........
            ........
            ........
            ........
            11111111
            ........
        ",
        );
        // Rank 6 (index 48-55) and rank 1 (index 8-15) should be set
        let expected = 0x00FF_0000_0000_FF00u64;
        assert_eq!(pawns.bits, expected);
    }

    #[test]
    #[should_panic(expected = "Pattern must contain exactly 64 squares")]
    fn test_from_pattern_too_few_squares() {
        let _ = Bitboard::from("1010101");
    }

    #[test]
    #[should_panic(expected = "Pattern must contain exactly 64 squares")]
    fn test_from_pattern_too_many_squares() {
        let _ = Bitboard::from("10101010101010101010101010101010101010101010101010101010101010101");
    }

    #[test]
    #[should_panic(expected = "Invalid character 'Z' in pattern")]
    fn test_from_pattern_invalid_character() {
        let _ = Bitboard::from(
            "
            1.......
            ........
            ........
            ...Z....
            ........
            ........
            ........
            ........
        ",
        );
    }

    #[test]
    #[should_panic(expected = "Invalid character '2' in pattern")]
    fn test_from_pattern_invalid_number() {
        let _ = Bitboard::from("2000000000000000000000000000000000000000000000000000000000000000");
    }
}
