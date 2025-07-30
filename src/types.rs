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
            idx: ((rank as u8) << 3) | file as u8,
        }
    }
}

impl fmt::Display for Square {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", self.file(), self.rank())
    }
}
