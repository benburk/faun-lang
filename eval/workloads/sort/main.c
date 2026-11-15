/* Sort numbers drawn from a small generator, and print the least, the
   middle and the greatest with a sum that depends on every place. */
#include <stdio.h>
#include <stdlib.h>

static int ascending(const void *a, const void *b) {
    unsigned x = *(const unsigned *)a, y = *(const unsigned *)b;
    return (x > y) - (x < y);
}

int main(int argc, char **argv) {
    unsigned count = argc > 1 ? (unsigned)atol(argv[1]) : 1000;
    unsigned *numbers = malloc((count ? count : 1) * sizeof *numbers);
    unsigned long seed = 42, sum = 0;
    unsigned place;
    if (!numbers) return 1;
    for (place = 0; place < count; place++) {
        numbers[place] = (unsigned)seed;
        seed = (seed * 25173 + 13849) % 65536;
    }
    qsort(numbers, count, sizeof *numbers, ascending);
    for (place = 0; place < count; place++) sum = (sum + (unsigned long)(place + 1) * numbers[place]) % 65521;
    printf("%u %u %u %lu\n", count ? numbers[0] : 0, count ? numbers[count / 2] : 0,
           count ? numbers[count - 1] : 0, sum);
    return 0;
}
