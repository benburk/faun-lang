/* A 16-bit checksum of standard input: for each byte, the sum so far turned
   left one bit and the byte mixed in. */
#include <stdio.h>

int main(void) {
    unsigned sum = 0;
    int byte;
    while ((byte = getchar()) != EOF) {
        sum = ((sum << 1) | (sum >> 15)) & 0xFFFF;
        sum ^= (unsigned)byte;
    }
    printf("%u\n", sum);
    return 0;
}
