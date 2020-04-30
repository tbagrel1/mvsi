#include <stdio.h>
void floyd_triangle(unsigned int n) {
    int i, c, a;
    a = 1;
    for (i = 1; i <= n; i++) {
        for (c = 1; c <= i; c++) {
            printf("%d ", a);
            a++;
        }
        printf("\n");
    }
}
