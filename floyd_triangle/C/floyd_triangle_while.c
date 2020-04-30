void floyd_triangle(int n) {
    int c, i = 1, a = 1;
    int display[n][n];
    while( i <= n)
    {
        c = 1;
        while(c <= i)
        {
            display[i-1, c-1] = a;
            a++;
            c++;
        }
        i++;
    }
    return 0 ;
}