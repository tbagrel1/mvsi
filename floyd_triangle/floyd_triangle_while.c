#include <stdio.h>
int main ()
{
    int n, c, i = 1, a = 1;
    printf("Enter the number of rows of Floyd’s triangle to print \n");
    scanf("%d", &n);
    while( i <= n)
    {
        c = 1;
        while(c <= i)
        {
            printf("%d ", a);
            a++;
            c++;
        }
        printf("\n") ;
        i++;
    }
    return 0 ;
}