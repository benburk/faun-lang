/* Count the ways to put a queen in each row of a board so that no two share
   a column or a diagonal. */
#include <stdio.h>
#include <stdlib.h>

static int size;
static int queens[32];

/* Whether a queen at `row` and `column` is clear of those in the rows before. */
static int clear(int row, int column) {
    int before;
    for (before = 0; before < row; before++) {
        int other = queens[before];
        if (other == column || abs(other - column) == row - before) return 0;
    }
    return 1;
}

static unsigned long ways(int row) {
    unsigned long count = 0;
    int column;
    if (row == size) return 1;
    for (column = 0; column < size; column++) {
        if (clear(row, column)) {
            queens[row] = column;
            count += ways(row + 1);
        }
    }
    return count;
}

int main(int argc, char **argv) {
    size = argc > 1 ? atoi(argv[1]) : 6;
    if (size < 0 || size > 32) return 1;
    printf("%lu\n", ways(0));
    return 0;
}
