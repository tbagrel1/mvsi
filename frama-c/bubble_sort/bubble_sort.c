//Bubble sort code
#include <stdio.h>
int main()
{
    int array[100], n, c, d, swap;
    
    printf("Enter number of elements\n");
    scanf("%d", &n);
    
    printf("Enter %d integers\n", n);
    
    c = 0;
    while(c < n)
    {
        scanf ("%d", &array[c]);
        c++;
    }
     
    c = 0;
    while(c < (n - 1))
    {
        d = 0;
        while(d < (n - c - 1))
        {
            if(array[d] > array[d + 1]) //For decreasing order use <
            {
                swap = array[d];
                array[d] = array[d + 1];
                array[d + 1] = swap;
            }
            d++;
        }
        c++;
    }
    printf("Sorted list in ascending order : \n");
    c = 0;
        while(c < n)
    {
        printf("%d\n", array[c]);
        c++;
    }
    
    return 0 ;
}
