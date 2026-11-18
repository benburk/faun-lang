/* Compress a text with DEFLATE and read it back: the text is words drawn
   from a small generator, compressed as one block under the fixed Huffman
   code, its matches found by LZ77 through short hash chains, and then
   inflated. Prints the compressed length, the length read back and its
   CRC-32. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define CHAIN_LIMIT 8
#define HASHES 1024

static const char *const words[16] = {"the", "quick", "brown", "fox", "jumps", "over",
                                      "lazy", "dog", "and", "runs", "far", "away",
                                      "from", "a", "big", "cat"};

static const unsigned length_bases[29] = {3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27,
                                          31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195,
                                          227, 258};
static const unsigned length_extras[29] = {0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2,
                                           2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0};
static const unsigned distance_bases[30] = {1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97,
                                            129, 193, 257, 385, 513, 769, 1025, 1537, 2049,
                                            3073, 4097, 6145, 8193, 12289, 16385, 24577};
static const unsigned distance_extras[30] = {0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6,
                                             6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13};

/* The bits written so far: whole bytes in out, and count more in bits, the
   first written the least significant. */
static unsigned char *out;
static unsigned written, count;
static unsigned long bits;

static void put(unsigned value, unsigned width) {
    bits |= (unsigned long)value << count;
    count += width;
    while (count >= 8) {
        out[written++] = (unsigned char)(bits & 0xFF);
        bits >>= 8;
        count -= 8;
    }
}

/* A Huffman code is written from its most significant bit. */
static unsigned reversed(unsigned code, unsigned length) {
    unsigned done = 0;
    while (length--) {
        done = done * 2 + code % 2;
        code /= 2;
    }
    return done;
}

static void put_symbol(unsigned symbol) {
    if (symbol < 144) put(reversed(0x30 + symbol, 8), 8);
    else if (symbol < 256) put(reversed(0x190 + symbol - 144, 9), 9);
    else if (symbol < 280) put(reversed(symbol - 256, 7), 7);
    else put(reversed(0xC0 + symbol - 280, 8), 8);
}

static unsigned symbol_of(const unsigned *bases, unsigned n, unsigned value) {
    unsigned symbol = 0;
    while (symbol + 1 < n && bases[symbol + 1] <= value) symbol++;
    return symbol;
}

static void put_match(unsigned length, unsigned distance) {
    unsigned l = symbol_of(length_bases, 29, length);
    unsigned d = symbol_of(distance_bases, 30, distance);
    put_symbol(257 + l);
    put(length - length_bases[l], length_extras[l]);
    put(reversed(d, 5), 5);
    put(distance - distance_bases[d], distance_extras[d]);
}

static const unsigned char *input;
static unsigned n;
/* For each hash, the latest position that had it, plus one, and for each
   position, the one before it with the same hash, plus one. */
static unsigned head[HASHES], *prev;

static unsigned hash(unsigned at) {
    return ((unsigned)input[at] * 64 ^ (unsigned)input[at + 1] * 8 ^ input[at + 2]) % HASHES;
}

static void insert(unsigned at) {
    unsigned key;
    if (at + 3 > n) return;
    key = hash(at);
    prev[at] = head[key];
    head[key] = at + 1;
}

static unsigned compress(void) {
    unsigned at = 0, i;
    written = count = 0;
    bits = 0;
    memset(head, 0, sizeof head);
    put(3, 3);
    while (at < n) {
        unsigned candidate = at + 3 <= n ? head[hash(at)] : 0;
        unsigned length = 0, distance = 0, limit = CHAIN_LIMIT;
        unsigned most = n - at < 258 ? n - at : 258;
        while (candidate && limit) {
            unsigned from = candidate - 1, found = 0;
            if (at - from > 32768U) break;
            while (found < most && input[from + found] == input[at + found]) found++;
            if (found > length) {
                length = found;
                distance = at - from;
            }
            candidate = prev[from];
            limit--;
        }
        insert(at);
        if (length < 3) {
            put_symbol(input[at]);
            at++;
        } else {
            for (i = at + 1; i < at + length; i++) insert(i);
            put_match(length, distance);
            at += length;
        }
    }
    put_symbol(256);
    if (count > 0) out[written++] = (unsigned char)bits;
    return written;
}

static const unsigned char *stream;

static unsigned bit(unsigned long at) { return (stream[at / 8] >> (at % 8)) & 1; }

static unsigned long at;

/* count bits, the first the least significant. */
static unsigned extra(unsigned count) {
    unsigned value = 0, i;
    for (i = 0; i < count; i++) value |= bit(at++) << i;
    return value;
}

/* count more bits of a Huffman code, the first the most significant. */
static unsigned code_bits(unsigned count, unsigned code) {
    while (count--) code = code * 2 + bit(at++);
    return code;
}

static unsigned literal_symbol(void) {
    unsigned code = code_bits(7, 0);
    if (code < 0x18) return 256 + code;
    code = code_bits(1, code);
    if (code < 0xC0) return code - 0x30;
    if (code < 0xC8) return 280 + code - 0xC0;
    return 144 + code_bits(1, code) - 0x190;
}

/* The bytes of a stream of one fixed block, or -1 where it is corrupt. */
static long inflate(unsigned char *into) {
    unsigned length = 0;
    at = 0;
    if (bit(0) != 1 || (bit(1) | bit(2) << 1) != 1) return -1;
    at = 3;
    for (;;) {
        unsigned symbol = literal_symbol(), l, d, distance, run;
        if (symbol < 256) {
            into[length++] = (unsigned char)symbol;
            continue;
        }
        if (symbol == 256) return length;
        if (symbol > 285) return -1;
        l = symbol - 257;
        run = length_bases[l] + extra(length_extras[l]);
        d = code_bits(5, 0);
        if (d >= 30) return -1;
        distance = distance_bases[d] + extra(distance_extras[d]);
        if (distance > length) return -1;
        while (run--) {
            into[length] = into[length - distance];
            length++;
        }
    }
}

static unsigned long table[256];

static unsigned long crc32(const unsigned char *bytes, unsigned length) {
    unsigned long reg = 0xFFFFFFFFUL;
    unsigned i, b;
    for (i = 0; i < 256; i++) {
        unsigned long entry = i;
        for (b = 0; b < 8; b++) entry = entry & 1 ? 0xEDB88320UL ^ (entry >> 1) : entry >> 1;
        table[i] = entry;
    }
    for (i = 0; i < length; i++) reg = table[(reg ^ bytes[i]) & 0xFF] ^ (reg >> 8);
    return (reg ^ 0xFFFFFFFFUL) & 0xFFFFFFFFUL;
}

int main(int argc, char **argv) {
    unsigned size = argc > 1 ? (unsigned)atol(argv[1]) : 1000;
    unsigned char *text = malloc(size + 8), *back = malloc(size + 1);
    unsigned length = 0, seed = 42, packed;
    long read;
    out = malloc(size + size / 8 + 8);
    prev = malloc((size + 1) * sizeof *prev);
    if (!text || !back || !out || !prev) return 1;
    while (length < size) {
        const char *word = words[seed / 256 % 16];
        while (*word) text[length++] = (unsigned char)*word++;
        text[length++] = ' ';
        seed = (unsigned)((seed * 25173UL + 13849) % 65536);
    }
    input = text;
    n = size;
    packed = compress();
    stream = out;
    read = inflate(back);
    if (read < 0) printf("corrupt\n");
    else printf("%u %ld %lu\n", packed, read, crc32(back, (unsigned)read));
    return 0;
}
