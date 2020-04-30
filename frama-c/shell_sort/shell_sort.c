/*@ requires \valid(tab + (0..n - 1));
  @ ensures \forall int k; 0 <= k <= n - 2 ==> *(tab + k) <= *(tab + k + 1);
*/
void shell_sort(int *tab, unsigned int n) {
    int i, j, inc, tmp;
    // --------------------
    inc = 3;
    while (inc > 0) {
        for (i = 0; i < n; i++) {
            j = i;
            tmp = tab[i];
            while ((j >= inc) && (tab[j - inc] > tmp)) {
                tab[j] = tab[j - inc];
                j = j - inc;
            }
            tab[j] = tmp;
        }
        if (inc / 2 != 0) {
            inc = inc / 2;
        } else if (inc == 1) {
            inc = 0;
        } else {
            inc = 1;
        }
    }
}