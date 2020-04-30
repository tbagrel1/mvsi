/*@ requires \valid(tab + (0..n - 1));
  @ ensures \forall int k; 0 <= k <= n - 2 ==> *(tab + k) <= *(tab + k + 1);
*/
void bubble_sort(int *tab, unsigned int n) {
    int c, d, swap;
    c = 0;
    while (c < (n - 1)) {
        d = 0;
        while (d < (n - c - 1)) {
            if (tab[d] > tab[d + 1]) {
                swap = tab[d];
                tab[d] = tab[d + 1];
                tab[d + 1] = swap;
            }
            d++;
        }
        c++;
    }
}
