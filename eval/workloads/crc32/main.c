/* The CRC-32 of standard input, as zlib, gzip and PNG compute it: the
   polynomial 0xEDB88320 reflected, the register starting and ending
   inverted, and the bytes taken one at a time through a table of 256. */
#include <stdio.h>

static unsigned long table[256];

int main(void) {
    unsigned long reg = 0xFFFFFFFFUL;
    unsigned n, bit;
    int byte;
    for (n = 0; n < 256; n++) {
        unsigned long entry = n;
        for (bit = 0; bit < 8; bit++)
            entry = entry & 1 ? 0xEDB88320UL ^ (entry >> 1) : entry >> 1;
        table[n] = entry;
    }
    while ((byte = getchar()) != EOF)
        reg = table[(reg ^ (unsigned)byte) & 0xFF] ^ (reg >> 8);
    printf("%lu\n", (reg ^ 0xFFFFFFFFUL) & 0xFFFFFFFFUL);
    return 0;
}
