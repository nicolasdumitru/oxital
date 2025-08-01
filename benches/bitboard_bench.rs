// Copyright (C) 2025 Nicolas Dumitru
// SPDX-License-Identifier: GPL-3.0-or-later

use criterion::{Criterion, black_box, criterion_group, criterion_main};

// Import from your library - replace 'your_crate_name' with actual name
use oxital::bitboard::Bitboard;
use oxital::types::{File, Rank, Square};

// Compare get method vs index operator for single bit access
fn bench_comparison_single_access(c: &mut Criterion) {
    let board = Bitboard::from(0xAA55AA55AA55AA55);

    let mut group = c.benchmark_group("single_bit_access");

    group.bench_function("`test` method", |b| {
        b.iter(|| {
            let mut sum = 0u32;
            for i in 0..64 {
                if board.test(black_box(Square::from(i))) {
                    sum += 1;
                }
            }
            black_box(sum)
        })
    });

    group.finish();
}

// Compare for rank/file access
fn bench_comparison_rank_file_access(c: &mut Criterion) {
    let board = Bitboard::from(0xAA55AA55AA55AA55);

    let mut group = c.benchmark_group("rank_file_access");

    group.bench_function("`test_square` method", |b| {
        b.iter(|| {
            let mut sum = 0u32;
            for rank_idx in 0..8 {
                for file_idx in 0..8 {
                    let square = Square::from((File::from(file_idx), Rank::from(rank_idx)));
                    if board.test(black_box(square)) {
                        sum += 1;
                    }
                }
            }
            black_box(sum)
        })
    });

    group.finish();
}

// Realistic chess pattern: checking attacks
fn bench_chess_pattern(c: &mut Criterion) {
    // Rook on a1, checking if it attacks along first rank
    // let rook_board = Bitboard::new(0x0000000000000001);
    let occupied = Bitboard::from(0x00000000000000FF); // First rank occupied

    let mut group = c.benchmark_group("chess_attack_pattern");

    group.bench_function("`test_square` method", |b| {
        b.iter(|| {
            let mut attacks = 0u64;
            // Check east from a1
            for file_idx in 1..8 {
                let square = Square::from((File::from(file_idx), Rank::from(0)));
                if occupied.test(square) {
                    break; // Hit a piece
                }
                attacks |= 1 << (file_idx as u64);
            }
            black_box(attacks)
        })
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_comparison_single_access,
    bench_comparison_rank_file_access,
    bench_chess_pattern,
);

criterion_main!(benches);
