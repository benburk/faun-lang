# Standings

Faun at `16405ac` beside each program's C twin, from the report of
2026-11-18; `just standings` writes this file and
[RATCHET.md](../RATCHET.md) says what is measured. Speed is counted in
instructions on x86-64, fuel on wasm32 and cycles on the 6502; memory
and sizes are bytes. K, M and G are thousands, millions and billions.
`vs C` is Faun's measure over the C twin's: below one, Faun is ahead.

## x86_64-linux, stock

| Program        | Speed | vs C | Memory | vs C | Size    | vs C | Small  |
| -------------- | ----- | ---- | ------ | ---- | ------- | ---- | ------ |
| binary-trees   | 802M  | 1.22 | 2.08M  | 0.45 | 32,688  | 2.28 | 24,472 |
| checksum       | 111M  | 1.05 | 9.75M  | 4.33 | 10,621  | 0.74 | 7,342  |
| collatz        | 340M  | 38.2 | 377K   | 0.17 | 23,560  | 1.64 | 16,600 |
| crc32          | 430K  | 1.24 | 49.2K  | 0.02 | 13,086  | 0.91 | 9,558  |
| fannkuch-redux | 650M  | 55.5 | 127K   | 0.06 | 45,128  | 3.14 | 29,696 |
| fasta          | 209M  | 1.72 | 98.3K  | 0.05 | 18,216  | 1.27 | 14,328 |
| inflate        | 1.25G | 66.1 | 4.26M  | 1.46 | 106,400 | 7.37 | 65,512 |
| k-nucleotide   | 669M  | 74.8 | 8.41M  | 3.34 | 105,704 | 5.73 | 72,352 |
| mandelbrot     | 137M  | 2.17 | 119K   | 0.05 | 40,728  | 2.84 | 25,832 |
| md5            | 142M  | 4.62 | 242K   | 0.12 | 21,808  | 1.52 | 18,704 |
| n-body         | 287M  | 2.11 | 49.2K  | 0.02 | 30,752  | 2.10 | 23,920 |
| pidigits       | 273M  | 20.8 | 172K   | 0.06 | 87,144  | 6.07 | 43,768 |
| queens         | 84.6M | 32.6 | 111K   | 0.05 | 31,792  | 1.72 | 20,776 |
| sieve          | 367M  | 30.7 | 2.38M  | 0.73 | 21,824  | 1.52 | 15,264 |
| sort           | 322M  | 6.03 | 1.98M  | 0.71 | 27,768  | 1.93 | 21,832 |
| spectral-norm  | 159M  | 1.76 | 131K   | 0.06 | 53,088  | 3.70 | 34,032 |
| geometric mean |       | 7.64 |        | 0.18 |         | 2.25 |        |

## x86_64-linux, lab

| Program        | Speed | vs C | Memory | vs C | Size   | vs C | Small  |
| -------------- | ----- | ---- | ------ | ---- | ------ | ---- | ------ |
| binary-trees   | 367M  | 0.56 | 1.02M  | 0.22 | 25,467 | 1.77 | 20,363 |
| checksum       | 94.1M | 0.89 | 9.74M  | 4.32 | 6,823  | 0.48 | 5,497  |
| collatz        | 340M  | 38.2 | 373K   | 0.16 | 19,083 | 1.33 | 14,323 |
| crc32          | 426K  | 1.23 | 41K    | 0.02 | 8,064  | 0.56 | 6,748  |
| fannkuch-redux | 648M  | 55.3 | 119K   | 0.05 | 38,707 | 2.70 | 26,611 |
| fasta          | 206M  | 1.70 | 98.3K  | 0.05 | 15,755 | 1.10 | 12,507 |
| inflate        | 1.25G | 66.3 | 4.25M  | 1.46 | 93,787 | 6.50 | 57,987 |
| k-nucleotide   | 515M  | 57.5 | 8.46M  | 3.36 | 90,547 | 4.91 | 64,403 |
| mandelbrot     | 88.2M | 1.40 | 115K   | 0.05 | 35,387 | 2.47 | 23,507 |
| md5            | 128M  | 4.15 | 98.3K  | 0.05 | 16,499 | 1.15 | 14,619 |
| n-body         | 287M  | 2.11 | 45.1K  | 0.02 | 24,947 | 1.70 | 20,747 |
| pidigits       | 272M  | 20.8 | 188K   | 0.07 | 79,139 | 5.51 | 40,699 |
| queens         | 84.4M | 32.5 | 106K   | 0.05 | 27,139 | 1.47 | 18,507 |
| sieve          | 362M  | 30.3 | 2.12M  | 0.65 | 17,459 | 1.22 | 12,995 |
| sort           | 294M  | 5.50 | 1.97M  | 0.71 | 19,787 | 1.38 | 16,723 |
| spectral-norm  | 159M  | 1.76 | 127K   | 0.06 | 45,627 | 3.18 | 30,059 |
| geometric mean |       | 6.79 |        | 0.16 |        | 1.80 |        |

## wasm32-wasi, stock

| Program        | Speed | vs C | Memory | vs C | Size    | vs C | Small   |
| -------------- | ----- | ---- | ------ | ---- | ------- | ---- | ------- |
| binary-trees   | 219M  | 0.93 | 467K   | 1.68 | 22,884  | 0.80 | 16,601  |
| checksum       | 60.7M | 1.80 | 2.12M  | 173  | 8,130   | 0.46 | 5,980   |
| collatz        | 505M  | 29.2 | 205K   | 12.5 | 17,528  | 0.68 | 12,014  |
| crc32          | 268K  | 2.80 | 16.4K  | 1.33 | 9,961   | 0.56 | 7,662   |
| fannkuch-redux | 796M  | 37.5 | 73.7K  | 3.60 | 32,149  | 1.21 | 19,891  |
| fasta          | 289M  | 2.75 | 73.7K  | 6.00 | 13,869  | 1.06 | 10,852  |
| inflate        | 575M  | 48.9 | 467K   | 2.19 | 79,447  | 2.44 | 43,204  |
| k-nucleotide   | 815M  | 82.6 | 2.06M  | 10.9 | 338,354 | 9.50 | 160,373 |
| mandelbrot     | 877M  | 6.3k | 73.7K  | 4.50 | 290,285 | 11.1 | 126,978 |
| md5            | 84.3M | 3.40 | 209K   | 2.83 | 18,402  | 4.47 | 16,105  |
| n-body         | 1.69G | 19k  | 73.7K  | 4.50 | 316,499 | 11.2 | 139,548 |
| pidigits       | 281M  | -    | 73.7K  | -    | 62,686  | -    | 27,210  |
| queens         | 18.1M | 13   | 73.7K  | 4.50 | 21,521  | 0.84 | 13,838  |
| sieve          | 240M  | 14.2 | 1.19M  | 2.31 | 16,813  | 0.65 | 11,778  |
| sort           | 129M  | 1.67 | 467K   | 3.35 | 19,305  | 0.68 | 15,831  |
| spectral-norm  | 1.39G | 23k  | 73.7K  | 3.60 | 318,352 | 11.9 | 140,531 |
| geometric mean |       | 35.3 |        | 4.83 |         | 1.85 |         |

## wasm32-wasi, lab

| Program        | Speed | vs C | Memory | vs C | Size    | vs C | Small   |
| -------------- | ----- | ---- | ------ | ---- | ------- | ---- | ------- |
| binary-trees   | 193M  | 0.82 | 467K   | 1.68 | 19,750  | 0.69 | 14,778  |
| checksum       | 60.7M | 1.80 | 2.12M  | 173  | 5,940   | 0.34 | 4,959   |
| collatz        | 505M  | 29.2 | 205K   | 12.5 | 15,692  | 0.61 | 11,044  |
| crc32          | 267K  | 2.78 | 16.4K  | 1.33 | 7,172   | 0.40 | 6,143   |
| fannkuch-redux | 792M  | 37.3 | 73.7K  | 3.60 | 29,786  | 1.12 | 18,589  |
| fasta          | 289M  | 2.75 | 73.7K  | 6.00 | 12,864  | 0.98 | 10,076  |
| inflate        | 568M  | 48.3 | 467K   | 2.19 | 76,313  | 2.34 | 41,365  |
| k-nucleotide   | 739M  | 75   | 2.06M  | 10.9 | 343,604 | 9.65 | 159,973 |
| mandelbrot     | 882M  | 6.4k | 73.7K  | 4.50 | 298,915 | 11.4 | 128,894 |
| md5            | 84.1M | 3.39 | 209K   | 2.83 | 15,731  | 3.82 | 14,037  |
| n-body         | 1.7G  | 19k  | 73.7K  | 4.50 | 326,517 | 11.6 | 141,840 |
| pidigits       | 281M  | -    | 73.7K  | -    | 60,545  | -    | 26,048  |
| queens         | 18M   | 12.9 | 73.7K  | 4.50 | 19,905  | 0.77 | 12,985  |
| sieve          | 240M  | 14.2 | 1.19M  | 2.31 | 15,000  | 0.58 | 10,765  |
| sort           | 126M  | 1.63 | 467K   | 3.35 | 15,239  | 0.53 | 13,039  |
| spectral-norm  | 1.39G | 23k  | 73.7K  | 3.60 | 327,195 | 12.3 | 142,012 |
| geometric mean |       | 34.7 |        | 4.83 |         | 1.67 |         |

## mos6502-sim65, stock

| Program        | Speed | vs C | Memory | vs C | Size   | vs C | Small  |
| -------------- | ----- | ---- | ------ | ---- | ------ | ---- | ------ |
| checksum       | 11M   | 15.6 | 7.34K  | 61.1 | 23,310 | 9.00 | 23,310 |
| collatz        | 55.3M | 12.7 | 1.27K  | 7.03 | 47,894 | 15.5 | 47,894 |
| crc32          | 10.9M | 9.83 | 6.35K  | 5.47 | 31,753 | 10.6 | 31,753 |
| fasta          | 64.9M | -    | 1.31K  | -    | 58,828 | -    | 58,828 |
| queens         | 46.6M | 32.9 | 1.51K  | 5.89 | 61,830 | 20.7 | 61,830 |
| sieve          | 22.9M | 42.2 | 3.32K  | 2.84 | 47,276 | 14.7 | 47,276 |
| geometric mean |       | 19.3 |        | 8.30 |        | 13.5 |        |

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
| checksum       | 11.1M | 15.6 | 7.32K  | 61   | 21,089 | 8.14 | 21,089 |
| collatz        | 55M   | 12.6 | 1.27K  | 7.04 | 44,665 | 14.5 | 44,665 |
| crc32          | 10.9M | 9.83 | 6.33K  | 5.45 | 27,485 | 9.18 | 27,485 |
| fasta          | 64.9M | -    | 1.3K   | -    | 56,027 | -    | 56,027 |
| queens         | 46.6M | 32.9 | 1.51K  | 5.90 | 58,871 | 19.8 | 58,871 |
| sieve          | 22.9M | 42.2 | 3.32K  | 2.84 | 43,756 | 13.6 | 43,756 |
| sort           | 4.98M | 12.1 | 804    | 3.03 | 63,311 | 13.9 | 63,311 |
| geometric mean |       | 17.9 |        | 7.01 |        | 12.6 |        |

Not running:

- binary-trees: size image at 2: exit 3: stack overflow
- fannkuch-redux: too large
- inflate: too large
- k-nucleotide: too large
- mandelbrot: too large
- md5: too large
- n-body: too large
- pidigits: too large
- spectral-norm: too large
