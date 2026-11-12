/* Scalar reference for main.fn, using a fixed array instead of immutable
 * lists. Keep the order of operations, including momentum and energy sums,
 * the same as Faun. Compile without reassociation or FMA contraction.
 * See notes/nbody-performance.md for build and comparison commands.
 */
#include <errno.h>
#include <inttypes.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#define SOLAR_MASS (4.0 * 3.141592653589793 * 3.141592653589793)
#define DAYS_PER_YEAR 365.24
#define COUNT 5

typedef struct {
    double x, y, z;
} Vec3;

typedef struct {
    Vec3 pos, vel;
    double mass;
} Body;

static void advance(Body bodies[COUNT], double dt) {
    for (int i = 0; i < COUNT; ++i) {
        for (int j = i + 1; j < COUNT; ++j) {
            Body *b = &bodies[i];
            Body *other = &bodies[j];
            double dx = b->pos.x - other->pos.x;
            double dy = b->pos.y - other->pos.y;
            double dz = b->pos.z - other->pos.z;
            double d2 = dx * dx + dy * dy + dz * dz;
            double mag = dt / (d2 * sqrt(d2));
            double other_factor = other->mass * mag;
            double factor = b->mass * mag;
            b->vel.x -= dx * other_factor;
            b->vel.y -= dy * other_factor;
            b->vel.z -= dz * other_factor;
            other->vel.x += dx * factor;
            other->vel.y += dy * factor;
            other->vel.z += dz * factor;
        }
    }
    for (int i = 0; i < COUNT; ++i) {
        bodies[i].pos.x += bodies[i].vel.x * dt;
        bodies[i].pos.y += bodies[i].vel.y * dt;
        bodies[i].pos.z += bodies[i].vel.z * dt;
    }
}

static double energy(const Body bodies[COUNT]) {
    double answer = 0.0;
    /* Faun's recursive energy sums each head with the answer for its tail. */
    for (int i = COUNT - 1; i >= 0; --i) {
        const Body *b = &bodies[i];
        double kinetic = 0.5 * b->mass *
            (b->vel.x * b->vel.x + b->vel.y * b->vel.y + b->vel.z * b->vel.z);
        double potential = 0.0;
        for (int j = i + 1; j < COUNT; ++j) {
            double dx = b->pos.x - bodies[j].pos.x;
            double dy = b->pos.y - bodies[j].pos.y;
            double dz = b->pos.z - bodies[j].pos.z;
            potential -= b->mass * bodies[j].mass / sqrt(dx * dx + dy * dy + dz * dz);
        }
        answer = kinetic + potential + answer;
    }
    return answer;
}

int main(int argc, char **argv) {
    if (argc != 2 || argv[1][0] == '\0') {
        fprintf(stderr, "usage: %s STEPS (unsigned decimal)\n", argv[0]);
        return EXIT_FAILURE;
    }
    for (const char *p = argv[1]; *p; ++p) {
        if (*p < '0' || *p > '9') {
            fprintf(stderr, "invalid step count\n");
            return EXIT_FAILURE;
        }
    }
    errno = 0;
    char *end;
    uintmax_t parsed = strtoumax(argv[1], &end, 10);
    if (errno == ERANGE || *end != '\0' || parsed > UINT64_MAX) {
        fprintf(stderr, "step count exceeds uint64_t\n");
        return EXIT_FAILURE;
    }
    uint64_t steps = (uint64_t)parsed;
    Body bodies[COUNT] = {
        {{0.0, 0.0, 0.0}, {0.0, 0.0, 0.0}, SOLAR_MASS},
        {{4.84143144246472090e+00, -1.16032004402742839e+00, -1.03622044471123109e-01},
         {1.66007664274403694e-03 * DAYS_PER_YEAR,
          7.69901118419740425e-03 * DAYS_PER_YEAR,
          -6.90460016972063023e-05 * DAYS_PER_YEAR},
         9.54791938424326609e-04 * SOLAR_MASS},
        {{8.34336671824457987e+00, 4.12479856412430479e+00, -4.03523417114321381e-01},
         {-2.76742510726862411e-03 * DAYS_PER_YEAR,
          4.99852801234917238e-03 * DAYS_PER_YEAR,
          2.30417297573763929e-05 * DAYS_PER_YEAR},
         2.85885980666130812e-04 * SOLAR_MASS},
        {{1.28943695621391310e+01, -1.51111514016986312e+01, -2.23307578892655734e-01},
         {2.96460137564761618e-03 * DAYS_PER_YEAR,
          2.37847173959480950e-03 * DAYS_PER_YEAR,
          -2.96589568540237556e-05 * DAYS_PER_YEAR},
         4.36624404335156298e-05 * SOLAR_MASS},
        {{1.53796971148509165e+01, -2.59193146099879641e+01, 1.79258772950371181e-01},
         {2.68067772490389322e-03 * DAYS_PER_YEAR,
          1.62824170038242295e-03 * DAYS_PER_YEAR,
          -9.51592254519715870e-05 * DAYS_PER_YEAR},
         5.15138902046611451e-05 * SOLAR_MASS}
    };
    for (int i = 1; i < COUNT; ++i) {
        double ratio = bodies[i].mass / bodies[0].mass;
        bodies[0].vel.x -= bodies[i].vel.x * ratio;
        bodies[0].vel.y -= bodies[i].vel.y * ratio;
        bodies[0].vel.z -= bodies[i].vel.z * ratio;
    }
    printf("%.9f\n", energy(bodies));
    for (uint64_t i = 0; i < steps; ++i) {
        advance(bodies, 0.01);
    }
    printf("%.9f\n", energy(bodies));
    return EXIT_SUCCESS;
}
