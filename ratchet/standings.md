# Standings

Faun at `686541e` beside each program's C twin, from the report of
2026-11-18; `just standings` writes this file and
[RATCHET.md](../RATCHET.md) says what is measured. Speed is counted in
instructions on x86-64, fuel on wasm32 and cycles on the 6502; memory
and sizes are bytes. K, M and G are thousands, millions and billions.
`vs C` is Faun's measure over the C twin's: below one, Faun is ahead.

## x86_64-linux, stock

| Program        | Speed | vs C | Memory | vs C | Size    | vs C | Small  |
| -------------- | ----- | ---- | ------ | ---- | ------- | ---- | ------ |
| binary-trees   | 758M  | 1.15 | 2.08M  | 0.46 | 31,120  | 2.17 | 23,488 |
| checksum       | 111M  | 1.05 | 9.75M  | 4.33 | 9,620   | 0.67 | 6,755  |
| collatz        | 279M  | 31.4 | 377K   | 0.17 | 22,048  | 1.54 | 16,016 |
| crc32          | 430K  | 1.24 | 45.1K  | 0.02 | 11,743  | 0.82 | 8,663  |
| fannkuch-redux | 645M  | 55.1 | 123K   | 0.05 | 42,760  | 2.98 | 29,120 |
| fasta          | 213M  | 1.76 | 98.3K  | 0.05 | 17,520  | 1.22 | 13,744 |
| inflate        | 1.21G | 64.1 | 4.26M  | 1.46 | 104,976 | 7.27 | 65,608 |
| k-nucleotide   | 661M  | 73.8 | 8.41M  | 3.34 | 102,184 | 5.54 | 70,696 |
| mandelbrot     | 123M  | 1.94 | 119K   | 0.05 | 38,208  | 2.66 | 24,864 |
| md5            | 142M  | 4.61 | 238K   | 0.12 | 19,832  | 1.38 | 16,904 |
| n-body         | 287M  | 2.11 | 49.2K  | 0.02 | 29,376  | 2.01 | 22,984 |
| pidigits       | 272M  | 20.8 | 160K   | 0.06 | 78,272  | 5.45 | 43,424 |
| queens         | 80.6M | 31   | 111K   | 0.05 | 30,248  | 1.64 | 20,056 |
| sieve          | 350M  | 29.3 | 2.38M  | 0.72 | 20,288  | 1.41 | 14,384 |
| sort           | 319M  | 5.97 | 1.98M  | 0.71 | 25,648  | 1.79 | 20,368 |
| spectral-norm  | 159M  | 1.76 | 131K   | 0.06 | 50,152  | 3.49 | 32,776 |
| geometric mean |       | 7.40 |        | 0.18 |         | 2.11 |        |

## x86_64-linux, lab

| Program        | Speed | vs C | Memory | vs C | Size   | vs C | Small  |
| -------------- | ----- | ---- | ------ | ---- | ------ | ---- | ------ |
| binary-trees   | 326M  | 0.50 | 1.02M  | 0.22 | 24,899 | 1.73 | 20,227 |
| checksum       | 94.1M | 0.89 | 9.74M  | 4.32 | 6,795  | 0.47 | 5,481  |
| collatz        | 279M  | 31.4 | 373K   | 0.16 | 18,563 | 1.29 | 14,291 |
| crc32          | 426K  | 1.23 | 41K    | 0.02 | 8,030  | 0.56 | 6,723  |
| fannkuch-redux | 643M  | 54.9 | 119K   | 0.05 | 37,411 | 2.61 | 26,595 |
| fasta          | 210M  | 1.73 | 94.2K  | 0.04 | 15,691 | 1.09 | 12,483 |
| inflate        | 1.21G | 64.3 | 4.25M  | 1.46 | 93,867 | 6.50 | 58,971 |
| k-nucleotide   | 507M  | 56.7 | 8.46M  | 3.36 | 88,315 | 4.79 | 63,835 |
| mandelbrot     | 82.6M | 1.31 | 115K   | 0.05 | 33,907 | 2.36 | 23,123 |
| md5            | 128M  | 4.15 | 98.3K  | 0.05 | 16,123 | 1.12 | 14,251 |
| n-body         | 287M  | 2.11 | 45.1K  | 0.02 | 24,851 | 1.70 | 20,659 |
| pidigits       | 272M  | 20.7 | 176K   | 0.06 | 71,691 | 5.00 | 40,915 |
| queens         | 80.3M | 30.9 | 106K   | 0.05 | 26,587 | 1.44 | 18,339 |
| sieve          | 345M  | 28.9 | 2.12M  | 0.65 | 17,195 | 1.20 | 12,931 |
| sort           | 292M  | 5.47 | 1.97M  | 0.71 | 19,619 | 1.37 | 16,659 |
| spectral-norm  | 159M  | 1.76 | 123K   | 0.05 | 44,347 | 3.09 | 29,947 |
| geometric mean |       | 6.57 |        | 0.15 |        | 1.76 |        |

## wasm32-wasi, stock

| Program        | Speed | vs C | Memory | vs C | Size    | vs C | Small   |
| -------------- | ----- | ---- | ------ | ---- | ------- | ---- | ------- |
| binary-trees   | 208M  | 0.88 | 467K   | 1.68 | 21,879  | 0.76 | 16,250  |
| checksum       | 60.7M | 1.80 | 2.12M  | 173  | 7,554   | 0.43 | 5,658   |
| collatz        | 464M  | 26.8 | 205K   | 12.5 | 16,505  | 0.64 | 11,692  |
| crc32          | 268K  | 2.80 | 16.4K  | 1.33 | 9,186   | 0.52 | 7,172   |
| fannkuch-redux | 788M  | 37.1 | 73.7K  | 3.60 | 30,134  | 1.14 | 19,564  |
| fasta          | 289M  | 2.75 | 73.7K  | 6.00 | 13,308  | 1.02 | 10,530  |
| inflate        | 566M  | 48.1 | 467K   | 2.19 | 78,330  | 2.40 | 43,277  |
| k-nucleotide   | 772M  | 78.3 | 2.06M  | 10.9 | 325,268 | 9.13 | 153,791 |
| mandelbrot     | 852M  | 6.1k | 73.7K  | 4.50 | 279,316 | 10.7 | 120,373 |
| md5            | 78.5M | 3.17 | 209K   | 2.83 | 17,190  | 4.18 | 15,059  |
| n-body         | 1.64G | 18k  | 73.7K  | 4.50 | 305,914 | 10.8 | 133,513 |
| pidigits       | 281M  | -    | 73.7K  | -    | 55,175  | -    | 26,876  |
| queens         | 17.5M | 12.6 | 73.7K  | 4.50 | 20,528  | 0.80 | 13,516  |
| sieve          | 217M  | 12.8 | 1.19M  | 2.31 | 15,809  | 0.61 | 11,290  |
| sort           | 128M  | 1.65 | 467K   | 3.35 | 18,005  | 0.63 | 14,956  |
| spectral-norm  | 1.34G | 23k  | 73.7K  | 3.60 | 307,302 | 11.5 | 134,243 |
| geometric mean |       | 34.1 |        | 4.83 |         | 1.76 |         |

## wasm32-wasi, lab

| Program        | Speed | vs C | Memory | vs C | Size    | vs C | Small   |
| -------------- | ----- | ---- | ------ | ---- | ------- | ---- | ------- |
| binary-trees   | 182M  | 0.77 | 467K   | 1.68 | 19,321  | 0.67 | 14,630  |
| checksum       | 60.7M | 1.80 | 2.12M  | 173  | 5,940   | 0.34 | 4,959   |
| collatz        | 464M  | 26.8 | 205K   | 12.5 | 15,246  | 0.59 | 11,044  |
| crc32          | 267K  | 2.78 | 16.4K  | 1.33 | 7,172   | 0.40 | 6,143   |
| fannkuch-redux | 784M  | 36.9 | 73.7K  | 3.60 | 28,347  | 1.07 | 18,584  |
| fasta          | 289M  | 2.75 | 73.7K  | 6.00 | 12,687  | 0.97 | 10,076  |
| inflate        | 560M  | 47.6 | 467K   | 2.19 | 75,965  | 2.33 | 41,922  |
| k-nucleotide   | 697M  | 70.6 | 2.06M  | 10.9 | 332,737 | 9.34 | 155,190 |
| mandelbrot     | 857M  | 6.2k | 73.7K  | 4.50 | 289,679 | 11.1 | 123,582 |
| md5            | 78.3M | 3.16 | 209K   | 2.83 | 15,496  | 3.77 | 13,812  |
| n-body         | 1.65G | 18k  | 73.7K  | 4.50 | 318,031 | 11.3 | 137,427 |
| pidigits       | 281M  | -    | 73.7K  | -    | 53,616  | -    | 26,036  |
| queens         | 17.4M | 12.5 | 73.7K  | 4.50 | 19,488  | 0.76 | 12,985  |
| sieve          | 217M  | 12.8 | 1.19M  | 2.31 | 14,764  | 0.57 | 10,760  |
| sort           | 125M  | 1.62 | 467K   | 3.35 | 15,112  | 0.53 | 12,974  |
| spectral-norm  | 1.35G | 23k  | 73.7K  | 3.60 | 318,646 | 12   | 137,686 |
| geometric mean |       | 33.5 |        | 4.83 |         | 1.63 |         |

## mos6502-sim65, stock

| Program        | Speed | vs C | Memory | vs C | Size   | vs C | Small  |
| -------------- | ----- | ---- | ------ | ---- | ------ | ---- | ------ |
| checksum       | 3.91M | 5.53 | 7.33K  | 61   | 21,375 | 8.25 | 21,375 |
| collatz        | 55.3M | 12.7 | 1.27K  | 7.03 | 46,670 | 15.1 | 46,670 |
| crc32          | 10.6M | 9.50 | 6.35K  | 5.47 | 29,647 | 9.90 | 29,647 |
| fasta          | 64.5M | -    | 1.31K  | -    | 57,321 | -    | 57,321 |
| queens         | 46.6M | 33   | 1.51K  | 5.89 | 60,606 | 20.3 | 60,606 |
| sieve          | 22.7M | 41.7 | 3.32K  | 2.84 | 45,426 | 14.1 | 45,426 |
| geometric mean |       | 15.6 |        | 8.29 |        | 12.9 |        |

Not running:

- binary-trees: too large
- fannkuch-redux: too large
- inflate: too large
- k-nucleotide: too large
- mandelbrot: too large
- md5: build: error: after natural legalization: main! instruction follows control flow that does not come back
- n-body: too large
- pidigits: too large
- sort: too large
- spectral-norm: too large

## mos6502-sim65, lab

| Program        | Speed | vs C | Memory | vs C | Size   | vs C | Small  |
| -------------- | ----- | ---- | ------ | ---- | ------ | ---- | ------ |
| checksum       | 3.92M | 5.54 | 7.31K  | 60.9 | 20,394 | 7.87 | 20,394 |
| collatz        | 55M   | 12.6 | 1.27K  | 7.04 | 44,665 | 14.5 | 44,665 |
| crc32          | 10.6M | 9.51 | 6.33K  | 5.45 | 27,229 | 9.09 | 27,229 |
| fasta          | 64.6M | -    | 1.3K   | -    | 55,744 | -    | 55,744 |
| queens         | 46.6M | 32.9 | 1.51K  | 5.90 | 58,871 | 19.8 | 58,871 |
| sieve          | 22.7M | 41.7 | 3.33K  | 2.84 | 43,742 | 13.6 | 43,742 |
| sort           | 4.96M | 12.1 | 804    | 3.03 | 63,166 | 13.8 | 63,166 |
| geometric mean |       | 14.9 |        | 7.01 |        | 12.5 |        |

Not running:

- binary-trees: size image at 1: exit 3: stack overflow
- fannkuch-redux: too large
- inflate: too large
- k-nucleotide: too large
- mandelbrot: too large
- md5: too large
- n-body: too large
- pidigits: too large
- spectral-norm: too large
