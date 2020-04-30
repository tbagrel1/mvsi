void floyd_triangle (int n)

{
    int i, c, a = 1;
    for ( i = 1 ; i <= n ; i ++)
    {
        for ( c = 1 ; c <= i ; c ++)
        {
            printf("%d ", a);
            a++;
        }
        printf("\n") ;
    }
}
