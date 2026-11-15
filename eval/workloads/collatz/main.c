/* Find the start below a limit whose Collatz chain is the longest: halve an
   even number, triple an odd one and add one, until it is 1. A chain from
   below 100,000 stays below 2^32, which a long holds everywhere. */
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv) {
    unsigned long limit = argc > 1 ? (unsigned long)atol(argv[1]) : 1000;
    unsigned long start, n, best = 1;
    unsigned count, most = 0;
    for (start = 1; start < limit; start++) {
        count = 0;
        for (n = start; n != 1; count++) n = n % 2 == 0 ? n / 2 : 3 * n + 1;
        if (count > most) {
            best = start;
            most = count;
        }
    }
    printf("%lu %u\n", best, most);
    return 0;
}
