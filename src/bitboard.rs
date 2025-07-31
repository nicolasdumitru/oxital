// Copyright (C) 2025 Nicolas Dumitru
// SPDX-License-Identifier: GPL-3.0-or-later

use std::cmp::PartialEq;
use std::ops::Not;
use std::ops::{BitAnd, BitAndAssign};
use std::ops::{BitOr, BitOrAssign};
use std::ops::{BitXor, BitXorAssign};
use std::ops::{Shl, ShlAssign};
use std::ops::{Shr, ShrAssign};
use std::ops::{Sub, SubAssign};

use crate::types::{File, Rank, Square};

/// `Bitboard` is a thin wrapper around `u64` bit masks representing finite sets
/// of up to 64 elements. `Bitboard` provides fast, type-safe and, convenient
/// set operations by implementing them as bitwise operations on 64-bit masks.
/// In the context of chess, `Bitboard`s are used to represent all of the 64
/// squares of a chessboard, one bit per square in each `Bitboard`.
///
/// By design, `Bitboard` depends directly on `Square` for the mapping between
/// square and bits. As an implementation detail, it follows that `Bitboard`'s
/// internal mask representation is compatible with `Square::mask()`.
#[derive(Clone, Copy, Debug)]
pub struct Bitboard {
    bits: u64,
}

impl Bitboard {
    /// Returns true if the bit of the given square is set.
    #[inline]
    pub fn test(self, square: Square) -> bool {
        (self.bits & square.mask()) != 0
    }

    /// Returns the number of ones in the binary representation of `self`.
    #[inline]
    pub fn count_ones(self) -> u32 {
        self.bits.count_ones()
    }

    /// Returns the number of zeros in the binary representation of `self`.
    #[inline]
    pub fn count_zeros(self) -> u32 {
        self.bits.count_zeros()
    }

    /// Returns the bitboard with one bit set.
    #[inline]
    pub fn set(self, square: Square) -> Self {
        Self {
            bits: self.bits | square.mask(),
        }
    }

    /// Sets a bit of the bitboard.
    #[inline]
    pub fn set_mut(&mut self, square: Square) {
        self.bits |= square.mask()
    }

    /// Returns the bitboard with one bit unset.
    #[inline]
    pub fn unset(self, square: Square) -> Self {
        Self {
            bits: self.bits & !square.mask(),
        }
    }

    /// Unsets a bit of the bitboard.
    #[inline]
    pub fn unset_mut(&mut self, square: Square) {
        self.bits &= !square.mask()
    }
}

impl From<Square> for Bitboard {
    /// Creates a Bitboard from a `Square` by setting only that square's bit.
    ///
    /// This creates a bitboard with exactly one bit set - the bit corresponding
    /// to the given square. This is useful for creating single-square bitboards
    /// for operations like checking if a piece is on a specific square, or for
    /// building up more complex bitboards by combining single squares.
    ///
    /// # Examples
    /// ```
    /// # use oxital::bitboard::Bitboard;
    /// # use oxital::types::{Square, File, Rank};
    /// // Create a bitboard with only the e4 square set
    /// let e4 = Square::from((File::E, Rank::Fourth));
    /// let bitboard = Bitboard::from(e4);
    /// assert!(bitboard.test(e4));
    ///
    /// // Create a bitboard for the a1 square
    /// let a1 = Square::from((File::A, Rank::First));
    /// let bitboard = Bitboard::from(a1);
    /// assert!(bitboard.test(a1));
    /// ```
    #[inline]
    fn from(square: Square) -> Self {
        Self {
            bits: square.mask(),
        }
    }
}

impl From<u64> for Bitboard {
    /// Creates a `Bitboard` from a `u64` bit mask.
    #[inline]
    fn from(bits: u64) -> Self {
        Self { bits }
    }
}

impl From<&str> for Bitboard {
    /// Creates a Bitboard from a pattern string.
    ///
    /// This constructor provides a flexible way to create bitboards from string
    /// literals for better visualization of constants. The encoding is:
    /// - '0' or '.' represents an empty square (unset bit)
    /// - '1' or 'X' represents an occupied square (set bit)
    /// - Newlines are ignored and only used for visual delimitation of ranks
    /// - Any other characters will cause a panic at runtime
    ///
    /// The pattern should represent exactly 64 squares, read from rank 8 to
    /// rank 1 (top to bottom), and from file a to file h (left to right).
    ///
    /// # Panics
    ///
    /// Panics if the pattern contains invalid characters or doesn't represent
    /// exactly 64 squares.
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
    /// ```
    fn from(pattern: &str) -> Self {
        // Filter out newlines and whitespace for processing
        let cleaned: String = pattern.chars().filter(|&ch| !ch.is_whitespace()).collect();

        if cleaned.len() != 64 {
            panic!(
                "Pattern must contain exactly 64 squares, got {}",
                cleaned.len()
            );
        }

        let mut bits: u64 = 0;

        for (i, ch) in cleaned.chars().enumerate() {
            match ch {
                '0' | '.' => {} // Empty square - bit remains unset
                '1' | 'X' => {
                    // Occupied square - set the bit
                    // i = 0 corresponds to rank 7, file 0 (a8)
                    // i = 63 corresponds to rank 0, file 7 (h1)
                    let rank = Rank::from(7 ^ (i >> 3) as u8); // 7 - i / 8
                    let file = File::from((i & 7) as u8); // i % 8
                    let square = Square::from((file, rank));
                    bits |= square.mask();
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
    type Output = Self;
    #[inline]
    fn not(self) -> Self::Output {
        Self::Output { bits: !self.bits }
    }
}

impl BitAnd for Bitboard {
    type Output = Self;
    #[inline]
    fn bitand(self, rhs: Self) -> Self::Output {
        Self::Output {
            bits: self.bits & rhs.bits,
        }
    }
}

impl BitAndAssign for Bitboard {
    #[inline]
    fn bitand_assign(&mut self, rhs: Self) {
        self.bits &= rhs.bits;
    }
}

impl BitOr<Self> for Bitboard {
    type Output = Self;
    #[inline]
    fn bitor(self, rhs: Self) -> Self::Output {
        Self::Output {
            bits: self.bits | rhs.bits,
        }
    }
}

impl BitOr<Square> for Bitboard {
    type Output = Self;
    /// Performs the bit setting operation.
    #[inline]
    fn bitor(self, rhs: Square) -> Self::Output {
        Self::Output {
            bits: self.bits | rhs.mask(),
        }
    }
}

impl BitOrAssign<Self> for Bitboard {
    #[inline]
    fn bitor_assign(&mut self, rhs: Self) {
        self.bits |= rhs.bits;
    }
}

impl BitOrAssign<Square> for Bitboard {
    /// Set bit assignment operator.
    #[inline]
    fn bitor_assign(&mut self, rhs: Square) {
        self.bits |= rhs.mask();
    }
}

impl BitXor for Bitboard {
    type Output = Self;
    #[inline]
    fn bitxor(self, rhs: Self) -> Self::Output {
        Self::Output {
            bits: self.bits ^ rhs.bits,
        }
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
    type Output = Self;
    #[inline]
    fn shl(self, rhs: T) -> Self::Output {
        Self::Output {
            bits: self.bits << rhs.into(),
        }
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
    type Output = Self;
    #[inline]
    fn shr(self, rhs: T) -> Self::Output {
        Self::Output {
            bits: self.bits >> rhs.into(),
        }
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

impl Sub<Self> for Bitboard {
    type Output = Self;
    /// Performs the set difference operation.
    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        Self::Output {
            bits: self.bits & !rhs.bits,
        }
    }
}

impl Sub<Square> for Bitboard {
    type Output = Self;
    /// Performs the bit unsetting operation.
    #[inline]
    fn sub(self, rhs: Square) -> Self::Output {
        Self::Output {
            bits: self.bits & !rhs.mask(),
        }
    }
}

impl SubAssign<Self> for Bitboard {
    /// Set difference assignment operator.
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        self.bits &= !rhs.bits
    }
}

impl SubAssign<Square> for Bitboard {
    /// Unset bit assignment operator.
    #[inline]
    fn sub_assign(&mut self, rhs: Square) {
        self.bits &= !rhs.mask()
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
    fn test_from_square() {
        // Test corner squares
        let a1 = Square::from((File::A, Rank::First));
        let bb_a1 = Bitboard::from(a1);
        assert!(bb_a1.test(a1));
        assert_eq!(bb_a1, Bitboard::from(1u64 << 0)); // a1 is index 0

        let h1 = Square::from((File::H, Rank::First));
        let bb_h1 = Bitboard::from(h1);
        assert!(bb_h1.test(h1));
        assert_eq!(bb_h1, Bitboard::from(1u64 << 7)); // h1 is index 7

        let a8 = Square::from((File::A, Rank::Eighth));
        let bb_a8 = Bitboard::from(a8);
        assert!(bb_a8.test(a8));
        assert_eq!(bb_a8, Bitboard::from(1u64 << 56)); // a8 is index 56

        let h8 = Square::from((File::H, Rank::Eighth));
        let bb_h8 = Bitboard::from(h8);
        assert!(bb_h8.test(h8));
        assert_eq!(bb_h8, Bitboard::from(1u64 << 63)); // h8 is index 63

        // Test center squares
        let e4 = Square::from((File::E, Rank::Fourth));
        let bb_e4 = Bitboard::from(e4);
        assert!(bb_e4.test(e4));
        assert_eq!(bb_e4, Bitboard::from(1u64 << 28)); // e4 is index 28

        let d5 = Square::from((File::D, Rank::Fifth));
        let bb_d5 = Bitboard::from(d5);
        assert!(bb_d5.test(d5));
        assert_eq!(bb_d5, Bitboard::from(1u64 << 35)); // d5 is index 35

        // Test that only the target square is set
        for i in 0..64 {
            let square = Square::from(i);
            let bitboard = Bitboard::from(square);

            // The target square should be set
            assert!(bitboard.test(square));

            // All other squares should be empty
            for j in 0..64 {
                if j != i {
                    let other_square = Square::from(j);
                    assert!(!bitboard.test(other_square));
                }
            }
        }

        // Test bitboard operations with single squares
        let e1 = Square::from((File::E, Rank::First));
        let e8 = Square::from((File::E, Rank::Eighth));
        let bb_e1 = Bitboard::from(e1);
        let bb_e8 = Bitboard::from(e8);

        // Combining two single-square bitboards should set both squares
        let combined = bb_e1 | bb_e8;
        assert!(combined.test(e1));
        assert!(combined.test(e8));

        // XOR with itself should result in empty bitboard
        let empty = bb_e1 ^ bb_e1;
        assert!(!empty.test(e1));
        assert_eq!(empty, Bitboard::from(0));
    }

    #[test]
    fn test_bit_testing() {
        // Test empty bitboard
        let empty = Bitboard::from(0);
        for i in 0..64 {
            assert!(!empty.test(Square::from(i)));
        }

        // Test full bitboard
        let full = Bitboard::from(u64::MAX);
        for i in 0..64 {
            assert!(full.test(Square::from(i)));
        }

        // Test single bit
        let single = Bitboard::from(1);
        assert!(single.test(Square::from(0)));
        for i in 1..64 {
            assert!(!single.test(Square::from(i)));
        }

        // Test highest bit
        let high = Bitboard::from(1u64 << 63);
        assert!(high.test(Square::from(63)));
        for i in 0..63 {
            assert!(!high.test(Square::from(i)));
        }

        // Test alternating pattern
        let alternating = Bitboard::from(0xAAAAAAAAAAAAAAAA);
        for i in 0..64 {
            if i % 2 == 1 {
                assert!(alternating.test(Square::from(i)));
            } else {
                assert!(!alternating.test(Square::from(i)));
            }
        }
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
        assert_eq!(result, bb1);

        // Test with self (should be zero)
        let result = bb1 ^ bb1;
        assert_eq!(result, Bitboard::from(0));
    }

    #[test]
    fn test_bitwise_xor_assign() {
        let mut bb1 = Bitboard::from(0xFF00FF00FF00FF00);
        let bb2 = Bitboard::from(0xF0F0F0F0F0F0F0F0);
        bb1 ^= bb2;
        assert_eq!(bb1, Bitboard::from(0x0FF00FF00FF00FF0));

        // Test XOR with self (should result in zero)
        let mut bb = Bitboard::from(0xFF00FF00FF00FF00);
        let original = bb;
        bb ^= original;
        assert_eq!(bb, Bitboard::from(0));
    }

    #[test]
    fn test_bitwise_not() {
        let bb = Bitboard::from(0);
        let result = !bb;
        assert_eq!(result, Bitboard::from(u64::MAX));

        let bb = Bitboard::from(u64::MAX);
        let result = !bb;
        assert_eq!(result, Bitboard::from(0));

        let bb = Bitboard::from(0xFF00FF00FF00FF00);
        let result = !bb;
        assert_eq!(result, Bitboard::from(0x00FF00FF00FF00FF));

        // Test double negation
        let bb = Bitboard::from(0x123456789ABCDEF0);
        let result = !!bb;
        assert_eq!(result, bb);
    }

    #[test]
    fn test_copy_and_clone() {
        let bb1 = Bitboard::from(0x123456789ABCDEF0);
        let bb2 = bb1; // Copy
        let bb3 = bb1.clone(); // Clone

        assert_eq!(bb1, bb2);
        assert_eq!(bb1, bb3);
        assert_eq!(bb2, bb3);
    }

    #[test]
    fn test_chess_squares() {
        // Test some well-known chess squares
        let mut board = Bitboard::from(0);

        // Set e4 (rank 3, file 4)
        let e4 = Square::from((File::E, Rank::Fourth));
        board |= Bitboard::from(1u64 << e4.index());
        assert!(board.test(e4));

        // Set d5 (rank 4, file 3)
        let d5 = Square::from((File::D, Rank::Fifth));
        board |= Bitboard::from(1u64 << d5.index());
        assert!(board.test(d5));

        // Verify both squares are set
        assert!(board.test(e4));
        assert!(board.test(d5));

        // Verify other squares are not set
        let a1 = Square::from((File::A, Rank::First));
        let h8 = Square::from((File::H, Rank::Eighth));
        assert!(!board.test(a1));
        assert!(!board.test(h8));
    }

    #[test]
    fn test_bitboard_operations_chain() {
        let bb1 = Bitboard::from(0xF0F0F0F0F0F0F0F0);
        let bb2 = Bitboard::from(0xFF00FF00FF00FF00);
        let bb3 = Bitboard::from(0x0F0F0F0F0F0F0F0F);

        // Chain operations
        let result = (bb1 | bb2) & !bb3;
        let expected = Bitboard::from(
            (0xF0F0F0F0F0F0F0F0u64 | 0xFF00FF00FF00FF00u64) & !0x0F0F0F0F0F0F0F0Fu64,
        );
        assert_eq!(result, expected);

        // More complex chain
        let result = (bb1 ^ bb2) | (bb2 & bb3);
        let expected = Bitboard::from(
            (0xF0F0F0F0F0F0F0F0u64 ^ 0xFF00FF00FF00FF00u64)
                | (0xFF00FF00FF00FF00u64 & 0x0F0F0F0F0F0F0F0Fu64),
        );
        assert_eq!(result, expected);
    }

    #[test]
    fn test_edge_cases() {
        // Test boundary conditions for test() method
        let bb = Bitboard::from(0x8000000000000001);
        assert!(bb.test(Square::from(0))); // First bit
        assert!(bb.test(Square::from(63))); // Last bit
        for i in 1..63 {
            assert!(!bb.test(Square::from(i)));
        }

        // Test corner squares
        let bb = Bitboard::from(0x8100000000000081);
        assert!(bb.test(Square::from((File::A, Rank::First)))); // a1
        assert!(bb.test(Square::from((File::H, Rank::First)))); // h1
        assert!(bb.test(Square::from((File::A, Rank::Eighth)))); // a8
        assert!(bb.test(Square::from((File::H, Rank::Eighth)))); // h8
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
        assert_eq!(result1, Bitboard::from(0x1E1E1E1E1E1E1E1E));

        let result4 = bb << 4u8;
        assert_eq!(result4, Bitboard::from(0xF0F0F0F0F0F0F0F0));

        let result8 = bb << 8u8;
        assert_eq!(result8, Bitboard::from(0x0F0F0F0F0F0F0F00));

        // Test with different integer types that can convert to u8
        let result_u8 = bb << 2u8;
        let result_bool = bb << true; // bool converts to u8 (true = 1)
        assert_eq!(result_u8, Bitboard::from(0x0F0F0F0F0F0F0F0Fu64 << 2));
        assert_eq!(result_bool, Bitboard::from(0x0F0F0F0F0F0F0F0Fu64 << 1));

        // Test shifting by zero
        let result0 = bb << 0u8;
        assert_eq!(result0, bb);

        // Test overflow behavior
        let high_bit = Bitboard::from(0x8000000000000000);
        let overflow = high_bit << 1u8;
        assert_eq!(overflow, Bitboard::from(0));

        // Test shifting with pattern
        let pattern = Bitboard::from(0x0000000000000001);
        let shifted = pattern << 63u8;
        assert_eq!(shifted, Bitboard::from(0x8000000000000000));
    }

    #[test]
    fn test_left_shift_assign() {
        let mut bb = Bitboard::from(0x0F0F0F0F0F0F0F0F);
        let original = Bitboard::from(0x0F0F0F0F0F0F0F0F);

        // Test shifting by 1
        bb <<= 1u8;
        assert_eq!(bb, Bitboard::from(0x1E1E1E1E1E1E1E1E));

        // Reset and test shifting by 4
        bb = original;
        bb <<= 4u8;
        assert_eq!(bb, Bitboard::from(0xF0F0F0F0F0F0F0F0));

        // Test with different integer types that can convert to u8
        let mut bb1 = Bitboard::from(0x0F0F0F0F0F0F0F0F);
        let mut bb2 = Bitboard::from(0x0F0F0F0F0F0F0F0F);
        bb1 <<= 3u8;
        bb2 <<= false; // false converts to u8 (false = 0)
        assert_eq!(bb1, Bitboard::from(0x7878787878787878));
        assert_eq!(bb2, Bitboard::from(0x0F0F0F0F0F0F0F0F)); // shifted by 0

        // Test shifting by zero
        let mut bb = Bitboard::from(0x123456789ABCDEF0);
        let original = bb;
        bb <<= 0u8;
        assert_eq!(bb, original);

        // Test chained assignment
        let mut bb = Bitboard::from(0x0000000000000001);
        bb <<= 1u8;
        bb <<= 1u8;
        bb <<= 1u8;
        assert_eq!(bb, Bitboard::from(0x0000000000000008));
    }

    #[test]
    fn test_right_shift() {
        let bb = Bitboard::from(0xF0F0F0F0F0F0F0F0);

        // Test shifting by different amounts
        let result1 = bb >> 1u8;
        assert_eq!(result1, Bitboard::from(0x7878787878787878));

        let result4 = bb >> 4u8;
        assert_eq!(result4, Bitboard::from(0x0F0F0F0F0F0F0F0F));

        let result8 = bb >> 8u8;
        assert_eq!(result8, Bitboard::from(0x00F0F0F0F0F0F0F0));

        // Test with different integer types that can convert to u8
        let result_u8 = bb >> 2u8;
        let result_bool = bb >> true; // bool converts to u8 (true = 1)
        assert_eq!(result_u8, Bitboard::from(0xF0F0F0F0F0F0F0F0u64 >> 2));
        assert_eq!(result_bool, Bitboard::from(0xF0F0F0F0F0F0F0F0u64 >> 1));

        // Test shifting by zero
        let result0 = bb >> 0u8;
        assert_eq!(result0, bb);

        // Test underflow behavior
        let low_bit = Bitboard::from(0x0000000000000001);
        let underflow = low_bit >> 1u8;
        assert_eq!(underflow, Bitboard::from(0));

        // Test shifting with pattern
        let pattern = Bitboard::from(0x8000000000000000);
        let shifted = pattern >> 63u8;
        assert_eq!(shifted, Bitboard::from(0x0000000000000001));

        // Test large shift (close to complete but not overflow)
        let large_shift = bb >> 63u8;
        assert_eq!(large_shift, Bitboard::from(0xF0F0F0F0F0F0F0F0u64 >> 63));
    }

    #[test]
    fn test_right_shift_assign() {
        let mut bb = Bitboard::from(0xF0F0F0F0F0F0F0F0);
        let original = Bitboard::from(0xF0F0F0F0F0F0F0F0);

        // Test shifting by 1
        bb >>= 1u8;
        assert_eq!(bb, Bitboard::from(0x7878787878787878));

        // Reset and test shifting by 4
        bb = original;
        bb >>= 4u8;
        assert_eq!(bb, Bitboard::from(0x0F0F0F0F0F0F0F0F));

        // Test with different integer types that can convert to u8
        let mut bb1 = Bitboard::from(0xF0F0F0F0F0F0F0F0);
        let mut bb2 = Bitboard::from(0xF0F0F0F0F0F0F0F0);
        bb1 >>= 3u8;
        bb2 >>= false; // false converts to u8 (false = 0)
        assert_eq!(bb1, Bitboard::from(0x1E1E1E1E1E1E1E1E));
        assert_eq!(bb2, Bitboard::from(0xF0F0F0F0F0F0F0F0)); // shifted by 0

        // Test shifting by zero
        let mut bb = Bitboard::from(0x123456789ABCDEF0);
        let original = bb;
        bb >>= 0u8;
        assert_eq!(bb, original);

        // Test chained assignment
        let mut bb = Bitboard::from(0x8000000000000000);
        bb >>= 1u8;
        bb >>= 1u8;
        bb >>= 1u8;
        assert_eq!(bb, Bitboard::from(0x1000000000000000));

        // Test shifting to zero
        let mut bb = Bitboard::from(0x0000000000000001);
        bb >>= 1u8;
        assert_eq!(bb, Bitboard::from(0));
    }

    #[test]
    fn test_shift_symmetry() {
        let original = Bitboard::from(0x0000FF0000FF0000);

        // Test that left shift followed by right shift returns to original
        // (when no bits are lost)
        let shifted_left = original << 8u8;
        let back_to_original = shifted_left >> 8u8;
        assert_eq!(back_to_original, original);

        // Test the reverse
        let shifted_right = original >> 8u8;
        let back_to_original = shifted_right << 8u8;
        assert_eq!(back_to_original, original);

        // Test with assign operations
        let mut bb = original;
        bb <<= 4u8;
        bb >>= 4u8;
        assert_eq!(bb, original);
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
        assert_eq!(empty, Bitboard::from(0));

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
        assert_eq!(a8, Bitboard::from(1u64 << 56));

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
        assert_eq!(h1, Bitboard::from(1u64 << 7));
    }

    #[test]
    fn test_from_pattern_characters() {
        // Test all valid empty characters
        let empty_dots =
            Bitboard::from("................................................................");
        let empty_zeros =
            Bitboard::from("0000000000000000000000000000000000000000000000000000000000000000");
        assert_eq!(empty_dots, Bitboard::from(0));
        assert_eq!(empty_zeros, Bitboard::from(0));

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
        assert_eq!(pattern_ones, pattern_x);
        assert_eq!(pattern_ones, Bitboard::from(1u64 << 56));
    }

    #[test]
    fn test_from_pattern_compact() {
        // Test without newlines - compact format
        let compact =
            Bitboard::from("1000000000000000000000000000000000000000000000000000000000000001");
        // Should have bits set at a8 (index 56) and h1 (index 7)
        assert_eq!(compact, Bitboard::from((1u64 << 56) | (1u64 << 7)));
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
        assert_eq!(with_spaces, Bitboard::from(expected));
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
        assert_eq!(pawns, Bitboard::from(expected));
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
