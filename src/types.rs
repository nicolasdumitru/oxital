// Copyright (C) 2025 Nicolas Dumitru
// SPDX-License-Identifier: GPL-3.0-or-later

use std::fmt;

#[derive(Clone, Copy, Debug)]
#[repr(u8)]
pub enum File {
    A = 0,
    B = 1,
    C = 2,
    D = 3,
    E = 4,
    F = 5,
    G = 6,
    H = 7,
}

impl From<u8> for File {
    #[inline]
    fn from(value: u8) -> Self {
        match value {
            0 => File::A,
            1 => File::B,
            2 => File::C,
            3 => File::D,
            4 => File::E,
            5 => File::F,
            6 => File::G,
            7 => File::H,
            _ => panic!("Invalid file value: {}", value),
        }
    }
}

impl fmt::Display for File {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let c = match self {
            File::A => 'a',
            File::B => 'b',
            File::C => 'c',
            File::D => 'd',
            File::E => 'e',
            File::F => 'f',
            File::G => 'g',
            File::H => 'h',
        };
        write!(f, "{}", c)
    }
}

#[derive(Clone, Copy, Debug)]
#[repr(u8)]
pub enum Rank {
    First = 0,
    Second = 1,
    Third = 2,
    Fourth = 3,
    Fifth = 4,
    Sixth = 5,
    Seventh = 6,
    Eighth = 7,
}

impl From<u8> for Rank {
    #[inline]
    fn from(value: u8) -> Self {
        match value {
            0 => Rank::First,
            1 => Rank::Second,
            2 => Rank::Third,
            3 => Rank::Fourth,
            4 => Rank::Fifth,
            5 => Rank::Sixth,
            6 => Rank::Seventh,
            7 => Rank::Eighth,
            _ => panic!("Invalid rank value: {}", value),
        }
    }
}

impl fmt::Display for Rank {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let n = match self {
            Rank::First => '1',
            Rank::Second => '2',
            Rank::Third => '3',
            Rank::Fourth => '4',
            Rank::Fifth => '5',
            Rank::Sixth => '6',
            Rank::Seventh => '7',
            Rank::Eighth => '8',
        };
        write!(f, "{}", n)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Square {
    idx: u8,
}

impl Square {
    #[inline]
    pub fn index(&self) -> u8 {
        self.idx
    }

    #[inline]
    pub fn mask(&self) -> u64 {
        1u64 << self.idx
    }

    #[inline]
    pub fn file(&self) -> File {
        File::from(self.idx & 7)
    }

    #[inline]
    pub fn rank(&self) -> Rank {
        Rank::from(self.idx >> 3)
    }
}

impl From<u8> for Square {
    #[inline]
    fn from(index: u8) -> Self {
        if index >= 64 {
            panic!("Square index must be less than 64")
        }
        Self { idx: index }
    }
}

impl From<(File, Rank)> for Square {
    #[inline]
    fn from((file, rank): (File, Rank)) -> Self {
        Self {
            idx: ((rank as u8) << 3) | file as u8, // <=> 8 * rank + file
        }
    }
}

impl fmt::Display for Square {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", self.file(), self.rank())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_file_from_u8() {
        assert!(matches!(File::from(0), File::A));
        assert!(matches!(File::from(1), File::B));
        assert!(matches!(File::from(2), File::C));
        assert!(matches!(File::from(3), File::D));
        assert!(matches!(File::from(4), File::E));
        assert!(matches!(File::from(5), File::F));
        assert!(matches!(File::from(6), File::G));
        assert!(matches!(File::from(7), File::H));
    }

    #[test]
    #[should_panic(expected = "Invalid file value: 8")]
    fn test_file_from_u8_invalid() {
        let _ = File::from(8);
    }

    #[test]
    fn test_file_display() {
        assert_eq!(format!("{}", File::A), "a");
        assert_eq!(format!("{}", File::B), "b");
        assert_eq!(format!("{}", File::C), "c");
        assert_eq!(format!("{}", File::D), "d");
        assert_eq!(format!("{}", File::E), "e");
        assert_eq!(format!("{}", File::F), "f");
        assert_eq!(format!("{}", File::G), "g");
        assert_eq!(format!("{}", File::H), "h");
    }

    #[test]
    fn test_file_enum_values() {
        assert_eq!(File::A as u8, 0);
        assert_eq!(File::B as u8, 1);
        assert_eq!(File::C as u8, 2);
        assert_eq!(File::D as u8, 3);
        assert_eq!(File::E as u8, 4);
        assert_eq!(File::F as u8, 5);
        assert_eq!(File::G as u8, 6);
        assert_eq!(File::H as u8, 7);
    }

    #[test]
    fn test_rank_from_u8() {
        assert!(matches!(Rank::from(0), Rank::First));
        assert!(matches!(Rank::from(1), Rank::Second));
        assert!(matches!(Rank::from(2), Rank::Third));
        assert!(matches!(Rank::from(3), Rank::Fourth));
        assert!(matches!(Rank::from(4), Rank::Fifth));
        assert!(matches!(Rank::from(5), Rank::Sixth));
        assert!(matches!(Rank::from(6), Rank::Seventh));
        assert!(matches!(Rank::from(7), Rank::Eighth));
    }

    #[test]
    #[should_panic(expected = "Invalid rank value: 8")]
    fn test_rank_from_u8_invalid() {
        let _ = Rank::from(8);
    }

    #[test]
    fn test_rank_display() {
        assert_eq!(format!("{}", Rank::First), "1");
        assert_eq!(format!("{}", Rank::Second), "2");
        assert_eq!(format!("{}", Rank::Third), "3");
        assert_eq!(format!("{}", Rank::Fourth), "4");
        assert_eq!(format!("{}", Rank::Fifth), "5");
        assert_eq!(format!("{}", Rank::Sixth), "6");
        assert_eq!(format!("{}", Rank::Seventh), "7");
        assert_eq!(format!("{}", Rank::Eighth), "8");
    }

    #[test]
    fn test_rank_enum_values() {
        assert_eq!(Rank::First as u8, 0);
        assert_eq!(Rank::Second as u8, 1);
        assert_eq!(Rank::Third as u8, 2);
        assert_eq!(Rank::Fourth as u8, 3);
        assert_eq!(Rank::Fifth as u8, 4);
        assert_eq!(Rank::Sixth as u8, 5);
        assert_eq!(Rank::Seventh as u8, 6);
        assert_eq!(Rank::Eighth as u8, 7);
    }

    #[test]
    fn test_square_from_u8() {
        let square = Square::from(0);
        assert_eq!(square.index(), 0);

        let square = Square::from(63);
        assert_eq!(square.index(), 63);
    }

    #[test]
    #[should_panic(expected = "Square index must be less than 64")]
    fn test_square_from_u8_invalid() {
        let _ = Square::from(64);
    }

    #[test]
    fn test_square_from_file_rank() {
        let square = Square::from((File::A, Rank::First));
        assert_eq!(square.index(), 0);
        assert!(matches!(square.file(), File::A));
        assert!(matches!(square.rank(), Rank::First));

        let square = Square::from((File::H, Rank::Eighth));
        assert_eq!(square.index(), 63);
        assert!(matches!(square.file(), File::H));
        assert!(matches!(square.rank(), Rank::Eighth));

        let square = Square::from((File::E, Rank::Fourth));
        assert_eq!(square.index(), 28); // (3 << 3) | 4 = 24 + 4 = 28
        assert!(matches!(square.file(), File::E));
        assert!(matches!(square.rank(), Rank::Fourth));
    }

    #[test]
    fn test_square_file_and_rank_extraction() {
        // Test all combinations
        for rank_val in 0..8 {
            for file_val in 0..8 {
                let expected_index = (rank_val << 3) | file_val;
                let square = Square::from(expected_index);

                assert_eq!(square.file() as u8, file_val);
                assert_eq!(square.rank() as u8, rank_val);
                assert_eq!(square.index(), expected_index);
            }
        }
    }

    #[test]
    fn test_square_display() {
        let square = Square::from((File::A, Rank::First));
        assert_eq!(format!("{}", square), "a1");

        let square = Square::from((File::H, Rank::Eighth));
        assert_eq!(format!("{}", square), "h8");

        let square = Square::from((File::E, Rank::Fourth));
        assert_eq!(format!("{}", square), "e4");

        let square = Square::from((File::D, Rank::Second));
        assert_eq!(format!("{}", square), "d2");
    }

    #[test]
    fn test_square_round_trip_conversions() {
        // Test that converting from (File, Rank) to Square and back works correctly
        for rank_val in 0..8 {
            for file_val in 0..8 {
                let file = File::from(file_val);
                let rank = Rank::from(rank_val);
                let square = Square::from((file, rank));

                assert_eq!(square.file() as u8, file_val);
                assert_eq!(square.rank() as u8, rank_val);
            }
        }

        // Test that converting from u8 to Square and extracting components works
        for index in 0..64 {
            let square = Square::from(index);
            let expected_file = index & 7;
            let expected_rank = index >> 3;

            assert_eq!(square.file() as u8, expected_file);
            assert_eq!(square.rank() as u8, expected_rank);
            assert_eq!(square.index(), index);
        }
    }
}
