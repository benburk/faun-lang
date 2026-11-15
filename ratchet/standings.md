# Standings

Faun at `c3cded9` beside each program's C twin, from the report of
2026-11-15; `just standings` writes this file and
[RATCHET.md](../RATCHET.md) says what is measured. Speed is counted in
instructions on x86-64, fuel on wasm32 and cycles on the 6502; memory
and sizes are bytes. K, M and G are thousands, millions and billions.
`vs C` is Faun's measure over the C twin's: below one, Faun is ahead.

## x86_64-linux, stock

| Program        | Speed | vs C | Memory | vs C | Size    | vs C | Small  |
| -------------- | ----- | ---- | ------ | ---- | ------- | ---- | ------ |
| binary-trees   | 844M  | 1.28 | 2.08M  | 0.46 | 32,928  | 2.29 | 24,696 |
| checksum       | 111M  | 1.05 | 9.75M  | 4.34 | 10,621  | 0.74 | 7,342  |
| collatz        | 389M  | 43.7 | 377K   | 0.17 | 23,712  | 1.65 | 16,600 |
| fannkuch-redux | 664M  | 56.7 | 127K   | 0.06 | 45,600  | 3.18 | 29,696 |
| fasta          | 258M  | 2.12 | 98.3K  | 0.05 | 19,768  | 1.38 | 14,576 |
| k-nucleotide   | 673M  | 75.2 | 8.42M  | 3.35 | 107,208 | 5.81 | 72,424 |
| mandelbrot     | 143M  | 2.27 | 123K   | 0.05 | 41,640  | 2.90 | 25,880 |
| md5            | 142M  | 4.62 | 242K   | 0.12 | 21,808  | 1.52 | 18,704 |
| n-body         | 287M  | 2.11 | 49.2K  | 0.02 | 30,864  | 2.11 | 23,920 |
| pidigits       | 273M  | 20.8 | 172K   | 0.06 | 88,400  | 6.16 | 43,768 |
| queens         | 92.5M | 35.6 | 111K   | 0.05 | 32,024  | 1.74 | 20,776 |
| sieve          | 429M  | 35.9 | 2.38M  | 0.73 | 21,976  | 1.53 | 15,264 |
| sort           | 323M  | 6.05 | 1.98M  | 0.71 | 27,816  | 1.94 | 21,832 |
| spectral-norm  | 159M  | 1.76 | 135K   | 0.06 | 54,536  | 3.80 | 34,248 |
| geometric mean |       | 7.85 |        | 0.18 |         | 2.24 |        |

## x86_64-linux, lab

| Program        | Speed | vs C | Memory | vs C | Size   | vs C | Small  |
| -------------- | ----- | ---- | ------ | ---- | ------ | ---- | ------ |
| binary-trees   | 409M  | 0.62 | 1.02M  | 0.23 | 25,715 | 1.79 | 20,587 |
| checksum       | 94.1M | 0.89 | 9.74M  | 4.33 | 6,823  | 0.48 | 5,497  |
| collatz        | 388M  | 43.7 | 373K   | 0.16 | 19,235 | 1.34 | 14,323 |
| fannkuch-redux | 662M  | 56.6 | 119K   | 0.05 | 39,179 | 2.73 | 26,611 |
| fasta          | 255M  | 2.10 | 98.3K  | 0.05 | 17,211 | 1.20 | 12,763 |
| k-nucleotide   | 518M  | 57.9 | 8.46M  | 3.36 | 91,675 | 4.97 | 64,403 |
| mandelbrot     | 90.1M | 1.43 | 115K   | 0.05 | 36,083 | 2.51 | 23,507 |
| md5            | 128M  | 4.15 | 98.3K  | 0.05 | 16,499 | 1.15 | 14,619 |
| n-body         | 287M  | 2.11 | 45.1K  | 0.02 | 25,051 | 1.71 | 20,747 |
| pidigits       | 272M  | 20.8 | 188K   | 0.07 | 80,411 | 5.60 | 40,699 |
| queens         | 92.2M | 35.5 | 106K   | 0.05 | 27,363 | 1.48 | 18,507 |
| sieve          | 424M  | 35.5 | 2.12M  | 0.65 | 17,603 | 1.23 | 12,995 |
| sort           | 295M  | 5.52 | 1.97M  | 0.71 | 19,835 | 1.38 | 16,771 |
| spectral-norm  | 159M  | 1.76 | 127K   | 0.06 | 46,739 | 3.26 | 30,211 |
| geometric mean |       | 6.88 |        | 0.16 |        | 1.81 |        |

## wasm32-wasi, stock

| Program        | Speed | vs C | Memory | vs C | Size    | vs C | Small   |
| -------------- | ----- | ---- | ------ | ---- | ------- | ---- | ------- |
| binary-trees   | 233M  | 0.99 | 467K   | 1.68 | 23,186  | 0.81 | 16,601  |
| checksum       | 60.7M | 1.80 | 2.12M  | 173  | 8,130   | 0.46 | 5,980   |
| collatz        | 540M  | 31.2 | 205K   | 12.5 | 17,757  | 0.69 | 12,014  |
| fannkuch-redux | 819M  | 38.6 | 73.7K  | 3.60 | 32,835  | 1.24 | 19,891  |
| fasta          | 365M  | 3.48 | 73.7K  | 6.00 | 15,229  | 1.16 | 10,887  |
| k-nucleotide   | 816M  | 82.7 | 2.06M  | 10.9 | 351,085 | 9.86 | 160,770 |
| mandelbrot     | 910M  | 6.6k | 73.7K  | 4.50 | 302,914 | 11.6 | 127,382 |
| md5            | 84.3M | 3.40 | 209K   | 2.83 | 18,402  | 4.47 | 16,105  |
| n-body         | 1.75G | 20k  | 73.7K  | 4.50 | 329,978 | 11.7 | 139,959 |
| pidigits       | 281M  | -    | 73.7K  | -    | 64,403  | -    | 27,210  |
| queens         | 20.5M | 14.7 | 73.7K  | 4.50 | 21,828  | 0.85 | 13,838  |
| sieve          | 290M  | 17.1 | 1.19M  | 2.31 | 17,053  | 0.66 | 11,778  |
| sort           | 129M  | 1.67 | 467K   | 3.35 | 19,383  | 0.68 | 15,831  |
| spectral-norm  | 1.44G | 24k  | 73.7K  | 3.60 | 331,773 | 12.4 | 140,983 |
| geometric mean |       | 44.6 |        | 5.66 |         | 2.04 |         |

## wasm32-wasi, lab

| Program        | Speed | vs C | Memory | vs C | Size    | vs C | Small   |
| -------------- | ----- | ---- | ------ | ---- | ------- | ---- | ------- |
| binary-trees   | 206M  | 0.88 | 467K   | 1.68 | 20,056  | 0.70 | 15,003  |
| checksum       | 60.7M | 1.80 | 2.12M  | 173  | 5,940   | 0.34 | 4,959   |
| collatz        | 540M  | 31.2 | 205K   | 12.5 | 15,925  | 0.62 | 11,044  |
| fannkuch-redux | 815M  | 38.4 | 73.7K  | 3.60 | 30,476  | 1.15 | 18,589  |
| fasta          | 365M  | 3.48 | 73.7K  | 6.00 | 14,224  | 1.09 | 10,111  |
| k-nucleotide   | 741M  | 75.1 | 2.06M  | 10.9 | 354,101 | 9.94 | 161,266 |
| mandelbrot     | 913M  | 6.6k | 73.7K  | 4.50 | 309,233 | 11.8 | 130,170 |
| md5            | 84.1M | 3.39 | 209K   | 2.83 | 15,731  | 3.82 | 14,037  |
| n-body         | 1.76G | 20k  | 73.7K  | 4.50 | 337,526 | 12   | 143,133 |
| pidigits       | 281M  | -    | 73.7K  | -    | 62,266  | -    | 26,048  |
| queens         | 20.4M | 14.6 | 73.7K  | 4.50 | 20,212  | 0.78 | 12,985  |
| sieve          | 290M  | 17.1 | 1.19M  | 2.31 | 15,240  | 0.59 | 10,765  |
| sort           | 127M  | 1.64 | 467K   | 3.35 | 15,317  | 0.54 | 13,112  |
| spectral-norm  | 1.44G | 24k  | 73.7K  | 3.60 | 338,376 | 12.7 | 143,463 |
| geometric mean |       | 43.8 |        | 5.66 |         | 1.86 |         |

## mos6502-sim65, stock

| Program        | Speed | vs C | Memory | vs C | Size   | vs C | Small  |
| -------------- | ----- | ---- | ------ | ---- | ------ | ---- | ------ |
| checksum       | 11M   | 15.6 | 7.34K  | 61.1 | 23,310 | 9.00 | 23,310 |
| collatz        | 55.3M | 12.7 | 1.27K  | 7.03 | 47,894 | 15.5 | 47,894 |
| fasta          | 65.5M | -    | 1.31K  | -    | 59,192 | -    | 59,192 |
| queens         | 46.6M | 32.9 | 1.51K  | 5.89 | 61,830 | 20.7 | 61,830 |
| sieve          | 22.9M | 42.2 | 3.32K  | 2.84 | 47,276 | 14.7 | 47,276 |
| geometric mean |       | 22.9 |        | 9.21 |        | 14.4 |        |

Not running:

- binary-trees: too large
- fannkuch-redux: too large
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
| checksum       | 11.1M | 15.6 | 7.32K  | 61   | 21,089 | 8.14 | 21,089 |
| collatz        | 55M   | 12.6 | 1.27K  | 7.04 | 44,665 | 14.5 | 44,665 |
| fasta          | 65.5M | -    | 1.3K   | -    | 56,391 | -    | 56,391 |
| queens         | 46.6M | 32.9 | 1.51K  | 5.90 | 58,871 | 19.8 | 58,871 |
| sieve          | 22.9M | 42.2 | 3.32K  | 2.84 | 43,756 | 13.6 | 43,756 |
| sort           | 4.98M | 12.1 | 804    | 3.03 | 63,311 | 13.9 | 63,311 |
| geometric mean |       | 20.1 |        | 7.38 |        | 13.4 |        |

Not running:

- binary-trees: size image at 1: exit 3: stack overflow
- fannkuch-redux: too large
- k-nucleotide: too large
- mandelbrot: too large
- md5: too large
- n-body: too large
- pidigits: too large
- spectral-norm: too large
