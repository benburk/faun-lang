/* Scalar reference for main.fn, using arrays instead of immutable lists.
 * Keep the order of operations, including each row's sum and the two final
 * sums, the same as Faun. Compile without reassociation or FMA contraction.
 * See notes/spectralnorm-performance.md for build and comparison commands.
 */
#include <errno.h>
#include <inttypes.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

/* The indices are doubles, as in Faun: whole and below 2^53, so exact. */
static double entry(double i, double j) {
    double diagonal = i + j;
    return 1.0 / (diagonal * (diagonal + 1.0) * 0.5 + i + 1.0);
}

static void times_a(size_t n, const double *u, double *out) {
    for (size_t i = 0; i < n; ++i) {
        double row = (double)i;
        double column = 0.0;
        double sum = 0.0;
        for (size_t j = 0; j < n; ++j) {
            sum = sum + entry(row, column) * u[j];
            column = column + 1.0;
        }
        out[i] = sum;
    }
}

static void times_at(size_t n, const double *u, double *out) {
    for (size_t i = 0; i < n; ++i) {
        double row = (double)i;
        double column = 0.0;
        double sum = 0.0;
        for (size_t j = 0; j < n; ++j) {
            sum = sum + entry(column, row) * u[j];
            column = column + 1.0;
        }
        out[i] = sum;
    }
}

static void times_ata(size_t n, const double *u, double *out, double *scratch) {
    times_a(n, u, scratch);
    times_at(n, scratch, out);
}

int main(int argc, char **argv) {
    if (argc != 2 || argv[1][0] == '\0') {
        fprintf(stderr, "usage: %s N (unsigned decimal)\n", argv[0]);
        return EXIT_FAILURE;
    }
    for (const char *p = argv[1]; *p; ++p) {
        if (*p < '0' || *p > '9') {
            fprintf(stderr, "invalid size\n");
            return EXIT_FAILURE;
        }
    }
    errno = 0;
    char *end;
    uintmax_t parsed = strtoumax(argv[1], &end, 10);
    if (errno == ERANGE || *end != '\0' || parsed > 1000000) {
        fprintf(stderr, "size exceeds 1000000\n");
        return EXIT_FAILURE;
    }
    size_t n = (size_t)parsed;
    double *u = malloc((n + 1) * sizeof *u);
    double *v = malloc((n + 1) * sizeof *v);
    double *scratch = malloc((n + 1) * sizeof *scratch);
    if (!u || !v || !scratch) {
        fprintf(stderr, "out of memory\n");
        return EXIT_FAILURE;
    }
    for (size_t i = 0; i < n; ++i) {
        u[i] = 1.0;
    }
    for (int round = 0; round < 10; ++round) {
        times_ata(n, u, v, scratch);
        times_ata(n, v, u, scratch);
    }
    double vbv = 0.0;
    double vv = 0.0;
    for (size_t i = 0; i < n; ++i) {
        vbv = vbv + u[i] * v[i];
        vv = vv + v[i] * v[i];
    }
    printf("%.9f\n", sqrt(vbv / vv));
    free(u);
    free(v);
    free(scratch);
    return EXIT_SUCCESS;
}
