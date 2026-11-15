/* Count the primes below a limit with the sieve of Eratosthenes. */
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv) {
    unsigned limit = argc > 1 ? (unsigned)atol(argv[1]) : 1000;
    unsigned n, multiple, count = 0;
    char *composite = calloc(limit ? limit : 1, 1);
    if (!composite) return 1;
    for (n = 2; n * n < limit; n++) {
        if (composite[n]) continue;
        for (multiple = n * n; multiple < limit; multiple += n) composite[multiple] = 1;
    }
    for (n = 2; n < limit; n++) count += !composite[n];
    printf("%u\n", count);
    return 0;
}
