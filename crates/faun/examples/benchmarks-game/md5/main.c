/* Streaming MD5. A partial block stays in tail between reads. */
#include <errno.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>

struct md5 {
    uint32_t h[4];
    uint64_t bytes;
    unsigned char tail[64];
};

static const uint32_t constants[64] = {
    0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee,
    0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
    0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be,
    0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
    0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa,
    0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
    0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed,
    0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
    0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c,
    0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
    0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05,
    0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
    0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039,
    0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
    0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1,
    0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391
};
static const unsigned rotations[4][4] = {
    {7, 12, 17, 22}, {5, 9, 14, 20}, {4, 11, 16, 23}, {6, 10, 15, 21}
};

static void compress(struct md5 *ctx, const unsigned char block[64]) {
    uint32_t x[16];
    for (unsigned j = 0; j < 16; ++j) {
        const unsigned char *p = block + 4 * j;
        x[j] = p[0] | (uint32_t)p[1] << 8 | (uint32_t)p[2] << 16 | (uint32_t)p[3] << 24;
    }
    uint32_t a = ctx->h[0], b = ctx->h[1], c = ctx->h[2], d = ctx->h[3];
    for (unsigned i = 0; i < 64; ++i) {
        uint32_t f;
        unsigned g;
        if (i < 16) {
            f = (b & c) | (~b & d);
            g = i;
        } else if (i < 32) {
            f = (d & b) | (~d & c);
            g = (5 * i + 1) % 16;
        } else if (i < 48) {
            f = b ^ c ^ d;
            g = (3 * i + 5) % 16;
        } else {
            f = c ^ (b | ~d);
            g = (7 * i) % 16;
        }
        uint32_t sum = a + f + constants[i] + x[g];
        unsigned s = rotations[i / 16][i % 4];
        a = d;
        d = c;
        c = b;
        b += (sum << s) | (sum >> (32 - s));
    }
    ctx->h[0] += a;
    ctx->h[1] += b;
    ctx->h[2] += c;
    ctx->h[3] += d;
}

static void update(struct md5 *ctx, const unsigned char *p, size_t n) {
    size_t used = ctx->bytes % 64;
    ctx->bytes += n;
    if (used) {
        size_t take = n < 64 - used ? n : 64 - used;
        memcpy(ctx->tail + used, p, take);
        if (used + take < 64) return;
        compress(ctx, ctx->tail);
        p += take;
        n -= take;
    }
    while (n >= 64) {
        compress(ctx, p);
        p += 64;
        n -= 64;
    }
    memcpy(ctx->tail, p, n);
}

static void finish(struct md5 *ctx, char line[33]) {
    size_t used = ctx->bytes % 64;
    ctx->tail[used++] = 0x80;
    if (used > 56) {
        memset(ctx->tail + used, 0, 64 - used);
        compress(ctx, ctx->tail);
        used = 0;
    }
    memset(ctx->tail + used, 0, 56 - used);
    uint64_t bits = ctx->bytes * 8;
    for (unsigned i = 0; i < 8; ++i) {
        ctx->tail[56 + i] = (unsigned char)(bits >> (8 * i));
    }
    compress(ctx, ctx->tail);
    static const char hex[] = "0123456789abcdef";
    for (unsigned i = 0; i < 16; ++i) {
        unsigned byte = (ctx->h[i / 4] >> (8 * (i % 4))) & 255;
        line[2 * i] = hex[byte / 16];
        line[2 * i + 1] = hex[byte % 16];
    }
    line[32] = '\n';
}

int main(void) {
    struct md5 ctx = {.h = {0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476}};
    unsigned char input[65536];
    for (;;) {
        ssize_t n = read(STDIN_FILENO, input, sizeof input);
        if (n < 0 && errno == EINTR) continue;
        if (n < 0) return 1;
        if (n == 0) break;
        update(&ctx, input, (size_t)n);
    }
    char line[33];
    finish(&ctx, line);
    for (size_t sent = 0; sent < sizeof line;) {
        ssize_t n = write(STDOUT_FILENO, line + sent, sizeof line - sent);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) return 1;
        sent += (size_t)n;
    }
    return 0;
}
